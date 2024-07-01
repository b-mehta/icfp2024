import Mathlib.Data.Nat.Digits
import Batteries
import Lean.Data.Parsec

inductive Literal : Type
  | bool : Bool → Literal
  | int : Int → Literal
  | str : String → Literal
  deriving Repr, BEq, DecidableEq

inductive Unary : Type
  | neg | not | toInt | toStr
  deriving Repr, DecidableEq

inductive Binary : Type
  | add | sub | mul | quot | rem
  | lt | gt | eq
  | or | and
  | conc | take | drop
  | app
  deriving Repr, DecidableEq

inductive Program : Type
  | lit : Literal → Program
  | unary : Unary → Program → Program
  | binary : Binary → Program → Program → Program
  | ite : Program → Program → Program → Program
  | abs : ℕ → Program → Program
  | var : ℕ → Program
  deriving Inhabited, Repr

@[simp] def Program.size : Program → ℕ
  | .lit _ => 1
  | .var _ => 1
  | .unary _ x => 1 + size x
  | .binary _ x y => 1 + size x + size y
  | .ite x y z => 1 + size x + size y + size z
  | .abs _ f => 1 + size f

section tokenise

inductive Token : Type
  | lit : Literal → Token
  | unary : Unary → Token
  | binary : Binary → Token
  | ite : Token
  | abs : ℕ → Token
  | var : ℕ → Token
  deriving Repr, DecidableEq

def tokeniseAux (s : String) : List String := s.splitOn

def getBinary : String → Except String Token
  | "+" => .ok <| .binary .add
  | "-" => .ok <| .binary .sub
  | "*" => .ok <| .binary .mul
  | "/" => .ok <| .binary .quot
  | "%" => .ok <| .binary .rem
  | "<" => .ok <| .binary .lt
  | ">" => .ok <| .binary .gt
  | "=" => .ok <| .binary .eq
  | "|" => .ok <| .binary .or
  | "&" => .ok <| .binary .and
  | "." => .ok <| .binary .conc
  | "T" => .ok <| .binary .take
  | "D" => .ok <| .binary .drop
  | "$" => .ok <| .binary .app
  | s => .error s!"unknown binary body {s}"

def getUnary : String → Except String Token
  | "-" => .ok <| .unary .neg
  | "!" => .ok <| .unary .not
  | "#" => .ok <| .unary .toInt
  | "$" => .ok <| .unary .toStr
  | s => .error s!"unknown unary body {s}"

def fullAlphabet : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!\"#$%&'()*+,-./:;<=>?@[\\]^_`|~ \n"

def getVal (c : Char) : Except String ℕ :=
  if c.toNat < 33 || c.toNat > 126 then .error s!"invalid character {c}"
  else .ok <| c.toNat - 33

def getNum (s : String) : Except String ℕ := do
  let i ← s.toList.traverse getVal
  match i with
  | [] => .error "empty literal string"
  | l => .ok <| l.foldl (· * 94 + ·) 0

def getChar (c : Char) : Except String Char := do
  let i ← getVal c
  return fullAlphabet.get ⟨i⟩

def getString : String → Except String Token
  | s => do
      let i ← s.toList.traverse getChar
      return .lit <| .str <| i.foldl String.push ""

def unreadableString (c : String) : String :=
  c.map fun i => Char.ofNat ((fullAlphabet.posOf i).1 + 33)

def numToString (n : ℕ) : String :=
  let x := if n = 0 then [0] else Nat.digits 94 n
  (x.map fun i => Char.ofNat (i + 33)).reverse.foldl (fun i j => i.push j) ""

def tokeniseOne (s : String) : Except String Token :=
  match s.head with
  | '?' => .ok .ite
  | 'B' => getBinary <| s.extract ⟨1⟩ s.endPos
  | 'U' => getUnary <| s.extract ⟨1⟩ s.endPos
  | 'S' => getString <| s.extract ⟨1⟩ s.endPos
  | 'L' => do
      let i ← getNum <| s.extract ⟨1⟩ s.endPos
      return .abs i
  | 'v' => do
      let i ← getNum <| s.extract ⟨1⟩ s.endPos
      return .var i
  | 'I' => do
      let i ← getNum <| s.extract ⟨1⟩ s.endPos
      return .lit (.int i)
  | 'T' => .ok <| .lit <| .bool <| true
  | 'F' => .ok <| .lit <| .bool <| false
  | s => .error s!"unknown indicator {s}"

def tokenise (s : String) : Except String (List Token) := traverse tokeniseOne (tokeniseAux s)

end tokenise

section parse

def parseOne : (t : List Token) → Except String (Program × {u : List Token // u.length < t.length})
  | [] => .error "unexpected end of input"
  | .lit l :: p => .ok ⟨.lit l, p, by simp⟩
  | .var x :: xs => .ok ⟨.var x, xs, by simp⟩
  | .unary l :: p =>  do
      let ⟨i, r, hr⟩ ← parseOne p
      return ⟨.unary l i, r, hr.trans (by simp)⟩
  | .binary l :: p => do
      let ⟨i₁, r₁, hr₁⟩ ← parseOne p
      let ⟨i₂, r₂, hr₂⟩ ← parseOne r₁
      return ⟨.binary l i₁ i₂, r₂, (hr₂.trans hr₁).trans (by simp)⟩
  | .ite :: p => do
      let ⟨i₁, r₁, hr₁⟩ ← parseOne p
      let ⟨i₂, r₂, hr₂⟩ ← parseOne r₁
      let ⟨i₃, r₃, hr₃⟩ ← parseOne r₂
      return ⟨.ite i₁ i₂ i₃, r₃, ((hr₃.trans hr₂).trans hr₁).trans (by simp)⟩
  | .abs n :: p => do
      let ⟨i, r, hr⟩ ← parseOne p
      return ⟨.abs n i, r, hr.trans (by simp)⟩
  termination_by t => t.length

end parse

def prettyUn : Unary → String
  | .neg => "-"
  | .not => "!"
  | .toInt => "#"
  | .toStr => "$"

def prettyBin : Binary → String
  | .add => "+"
  | .sub => "-"
  | .mul => "*"
  | .quot => "/"
  | .rem => "%"
  | .lt => "<"
  | .gt => ">"
  | .eq => "="
  | .or => "|"
  | .and => "&"
  | .conc => "."
  | .take => "T"
  | .drop => "D"
  | .app => "$"

def pretty : Program → String
  | .var n => s!"x{n}"
  | .unary b x => s!"({repr b} {pretty x})"
  | .binary .app x y => s!"({pretty x} {pretty y})"
  | .binary b x y => s!"({pretty x} {prettyBin b} {pretty y})"
  | .ite x y z => s!"(?{pretty x} {pretty y} {pretty z})"
  | .lit (.bool b) => s!"{repr b}"
  | .lit (.int b) => s!"{repr b}"
  | .lit (.str b) => s!"{repr b}"
  | .abs n f => s!"(λx{n} => {pretty f})"

def unpretty : Program → String
  | .var n => s!"v{numToString n}"
  | .unary b x => s!"U{prettyUn b} {unpretty x}"
  | .binary b x y => s!"B{prettyBin b} {unpretty x} {unpretty y}"
  | .ite x y z => s!"? {unpretty x} {unpretty y} {unpretty z}"
  | .lit (.bool b) => if b then "T" else "F"
  | .lit (.int b) => s!"I{numToString b.toNat}"
  | .lit (.str b) => s!"S{unreadableString b}"
  | .abs n f => s!"L{numToString n} {unpretty f}"

def parse (s : String) : Except String Program := do
  let t ← tokenise s
  let ⟨f, [], _⟩ ← parseOne t | .error "unparsed tokens"
  return f

def quot (m n : ℤ) : ℤ :=
  if m < 0 ∧ m % n ≠ 0
    then (m / n) + 1
    else m / n

def cfold : Program → Program
  | .var e => .var e
  | .abs n f => .abs n (cfold f)
  | .lit x => .lit x
  | .unary b x =>
      match b, cfold x with
      | .neg, .lit (.int x) => .lit (.int (-x))
      | .not, .lit (.bool b) => .lit (.bool (!b))
      | .toInt, .lit (.str s) => .lit <| .int <|
          Nat.ofDigits 94 <| List.reverse <| s.toList.map fun c => (fullAlphabet.posOf c).1
      | .toStr, .lit (.int s) => .lit <| .str <|
          let x := if s.toNat = 0 then [0] else Nat.digits 94 s.toNat
          (x.map fun i => fullAlphabet.get ⟨i⟩).reverse.foldl (fun i j => i.push j) ""
      | b', x' => .unary b' x'
  | .binary b x y =>
      match b, cfold x, cfold y with
      | .add, .lit (.int m), .lit (.int n) => .lit (.int (m + n))
      | .sub, .lit (.int m), .lit (.int n) => .lit (.int (m - n))
      | .mul, .lit (.int m), .lit (.int n) => .lit (.int (m * n))
      | .quot, .lit (.int m), .lit (.int n) => .lit <| .int <| quot m n
      | .rem , .lit (.int m), .lit (.int n) => .lit (.int (m - quot m n * n))
      | .lt, .lit (.int m), .lit (.int n) => .lit (.bool (m < n))
      | .gt, .lit (.int m), .lit (.int n) => .lit (.bool (m > n))
      | .eq, .lit m, .lit n => .lit (.bool (m == n))
      | .or, .lit (.bool b1), .lit (.bool b2) => .lit (.bool (b1 || b2))
      | .and, .lit (.bool b1), .lit (.bool b2) => .lit (.bool (b1 && b2))
      | .conc, .lit (.str m), .lit (.str n) => .lit (.str (m ++ n))
      | .take, .lit (.int n), .lit (.str m) => .lit (.str (m.take n.toNat))
      | .drop, .lit (.int n), .lit (.str m) => .lit (.str (m.drop n.toNat))
      | b, x', y' => .binary b x' y'
  | .ite x y z =>
      match cfold x with
      | .lit (.bool true) => cfold y
      | .lit (.bool false) => cfold z
      | x' => .ite x' y z

def freeVars : Program → Finset ℕ
  | .var n => {n}
  | .binary _ x y => freeVars x ∪ freeVars y
  | .unary _ x => freeVars x
  | .lit _ => ∅
  | .abs n f => insert n (freeVars f)
  | .ite x y z => freeVars x ∪ freeVars y ∪ freeVars z

def smallestMissing (X : Finset ℕ) : ℕ := Nat.find X.exists_not_mem
lemma smallestMissing_spec (X : Finset ℕ) : smallestMissing X ∉ X := Nat.find_spec X.exists_not_mem
lemma smallestMissing_min' (X : Finset ℕ) {x : ℕ} (hx : x ∉ X) : smallestMissing X ≤ x :=
  Nat.find_min' X.exists_not_mem hx
lemma smallestMissing_min (X : Finset ℕ) {x : ℕ} (hx : x < smallestMissing X) : x ∈ X := by
  simpa using Nat.find_min X.exists_not_mem hx

lemma smallestMissing_le_card {X : Finset ℕ} : smallestMissing X ≤ X.card := by
  by_contra!
  have hX : ∀ i ≤ X.card, i ∈ X := fun i hi => smallestMissing_min _ (by omega)
  have : Finset.range (X.card + 1) ⊆ X := fun i hi => hX _ (Finset.mem_range_succ_iff.1 hi)
  simpa using Finset.card_le_card this

lemma smallestMissing_eq_iff {X : Finset ℕ} {x : ℕ} :
    smallestMissing X = x ↔ x ∉ X ∧ ∀ y < x, y ∈ X := by
  simp [smallestMissing, Nat.find_eq_iff]

-- change `n`s to `m`s
@[simp]
def rename (n m : ℕ) : Program → Program
  | .var x => if x = n then .var m else .var x
  | .binary b x y => .binary b (rename n m x) (rename n m y)
  | .unary b x => .unary b (rename n m x)
  | .lit l => .lit l
  | .ite x y z => .ite (rename n m x) (rename n m y) (rename n m z)
  | .abs x f => if x = n then .abs m (rename n m f) else .abs x (rename n m f)

@[simp] lemma rename_size {n m : ℕ} (f : Program) : (rename n m f).size = f.size := by
  induction f with aesop | _ => _

def subst (n : ℕ) : Finset ℕ → Program → Program → Program
  | _, .var m, p => if n = m then p else .var m
  | s, .binary b x y, p => .binary b (subst n s x p) (subst n s y p)
  | s, .unary b x, p => .unary b (subst n s x p)
  | _, .lit l, _ => .lit l
  | s, .ite x y z, p => .ite (subst n s x p) (subst n s y p) (subst n s z p)
  | s, .abs m f, p =>
      if m ∈ insert n (freeVars p)
        -- if m is in s, something else has gone wrong...
        then let m' := smallestMissing (insert n (freeVars p) ∪ s ∪ freeVars f)
             .abs m' (subst n (insert m' s) (rename m m' f) p)
        else .abs m (subst n (insert m s) f p)
  termination_by _ x2 => x2.size

def betaOnce : Program → (_ : Finset ℕ := ∅) → Program × Bool
  | .binary .app (.abs n f) g, s => (subst n s f g, true)
  | .var e, _ => (.var e, false)
  | .lit x, _ => (.lit x, false)
  | .abs n f, s =>
      match betaOnce f (insert n s) with
      | (f', b) => (.abs n f', b)
  | .unary o f, s =>
      match betaOnce f s with
      | (f', b) => (.unary o f', b)
  | .binary b f g, s =>
      match betaOnce f s with
      | (f', true) => (.binary b f' g, true)
      | (f', false) =>
          match betaOnce g s with
          | (g', true) => (.binary b f g', true)
          | (g', false) => (.binary b f' g', false)
  | .ite x y z, s =>
      match betaOnce x s with
      | (x', true) => (.ite x' y z, true)
      | (x', false) =>
          match betaOnce y s with
          | (y', true) => (.ite x y' z, true)
          | (y', false) =>
              match betaOnce z s with
              | (z', true) => (.ite x y z', true)
              | (z', false) => (.ite x' y' z', false)

lemma betaOnce_false_noOp (p : Program) (s : Finset ℕ) (h : (betaOnce p s).2 = false) :
    (betaOnce p s).1 = p := by
  induction p, s using betaOnce.induct with aesop (add simp betaOnce) | _ => _

def beta? (p : Program) : Except String Program :=
  match betaOnce p with
  | (p', true) => .ok p'
  | (_, false) => .error "no beta redex"

def reductions (p : Program) (acc : ℕ) : ℕ → Except String (ℕ × Program)
  | 0 => .error s!"out of gas {pretty p}"
  | n + 1 =>
      match beta? p with
      | Except.ok p' => reductions (cfold p') (acc + 1) n
      | Except.error _ => .ok (acc, p)

def run (s : String) (gas : ℕ := 100000) : Except String (ℕ × Program) := do
  let p ← parse s
  reductions (cfold p) 0 gas

def runIO [Repr α] (x : Except String α) : IO Unit := do
  match x with
  | Except.ok p => IO.println (repr p)
  | Except.error e => IO.println e

def unfoldN : ℕ → (p : Program) → String × List Program
| 0, p => ("out of time", [p])
| n + 1, p =>
    match beta? p with
    | Except.ok p' =>
        let (s, l) := unfoldN n (cfold p')
        (s, p :: l)
    | Except.error e => (e, [p])

def testOutputStringLit (p : String) (s : String) : IO Unit :=
  match run p with
  | Except.ok (_, p') =>
      match p' with
      | .lit (.str s') =>
          if s' == s
            then IO.println "program output matches"
            else do
              IO.println "program output does not match"
              IO.println s!"got {s'}"
              IO.println s!"expected {s}"
      | _ => IO.println "not a string"
  | Except.error _ => IO.println "program errored"

-- lambdaman6
def test1 : String :=
  "B. SF B$ B$ L\" B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L$ L# ? B= v# I\" v\" B. v\" B$ v$ B- v# I\" Sl I#,"

-- short reduction example
def test2 : String := "B$ L# B$ L\" B+ v\" v\" B* I$ I# v8"

-- long beta reduction example
def test3 : String := "B$ B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L\" L# ? B= v# I! I\" B$ L$ B+ B$ v\" v$ B$ v\" v$ B- v# I\" I%"

-- abstraction example
def test4 : String := "B$ B$ L# L$ v# B. SB%,,/ S}Q/2,$_ IK"

def test5 : String :=
  "B. S3/,6%},!-\"$!-!.[} B$ B$ L\" B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L$ L# ? B= v# I\" v\" B. v\" B$ v$ B- v# I\" SL I#-"

def test7 : Program :=
  .binary .app
    (.abs 0
      (.binary .conc (.var 0)
        (.binary .conc (.var 0)
          (.binary .conc (.var 0) (.var 0)))))
    (.lit (.str (String.replicate 50 'R')))

def test8 : Program :=
  (.binary .app
    (.abs 0
      (.binary .app (.var 0)
        (.binary .app (.var 0)
          (.lit (.str (String.replicate 13 'R'))))))
    (.abs 0
      (.binary .conc
        (.binary .conc (.var 0) (.var 0))
        (.binary .conc (.var 0) (.var 0)))))

def test9 : Program :=
  .binary .app
    (.binary .app
      (.abs 0
        (.binary .app
          (.var 0)
          (.binary .app
            (.var 0)
            (.binary .app
              (.var 0)
              (.abs 1 (.binary .conc (.var 1) (.var 1)))))
        ))
      (.abs 0 (.abs 1 (.binary .app (.var 0) (.binary .app (.var 0) (.var 1))))))
    (.lit (.str "R"))

def flipDir : Program :=
  .abs 0 <| .unary .toStr <|
  .binary .app
    (.abs 1
    (.binary .sub
      (.ite
        (.binary .gt (.binary .rem (.var 1) (.lit (.int 6))) (.lit (.int 1)))
        (.lit (.int 75))
        (.lit (.int 80)))
    (.var 1)))
  <| .unary .toInt (.var 0)

def flipDir' : Program :=
  .abs 0 <|
    .ite
      (.binary .eq (.var 0) (.lit (.str "L")))
      (.lit (.str "R")) <|
    .ite
      (.binary .eq (.var 0) (.lit (.str "R")))
      (.lit (.str "L")) <|
    .ite
      (.binary .eq (.var 0) (.lit (.str "U")))
      (.lit (.str "D"))
      (.lit (.str "U"))

def test10 : String := "B$ L' B$ L( B$ B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L$ L% ? B& B> v% I\"41= B& B$ v' v% B$ v( B+ v% I\" v% B$ v$ B+ v% I\" I# B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L$ L% ? B= v% I\" T ? B= B% v% I# I\" F B$ v$ B/ v% I# L& B$ B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L$ L% ? B= v% v& T ? B= B% v& v% I! F B$ v$ B+ v% I\" I#"

def YComb : Program :=
  .abs 1
  (.binary .app
    (.abs 2
      (.binary .app (.var 1)
        (.binary .app (.var 2) (.var 2))))
    (.abs 2
      (.binary .app (.var 1)
        (.binary .app (.var 2) (.var 2)))))

#eval parse "B. S3/,6%},!-\"$!-!.[} B$ L# B$ v# B$ v# B$ v# SLLLLLLLL L$ B. B. v$ v$ v$"

#eval match parse "B. S3/,6%},!-\"$!-!.[} B$ L# B$ v# B$ v# B$ v# SLLLLLLLL L$ B. B. v$ v$ v$" with
  | .ok e => IO.println <| pretty e
  | .error e => IO.println e

-- (λx6 => (λx7 => ((Y (λx3 => λx4 => ?((x4 > 1000000) & ((x6 x4) & (x7 (x4 + 1)))) x4 (x3 (x4 + 1)))) 2)) (Y (λx3 => λx4 => (?(x4 = 1) true (?((x4 % 2) = 1) false (x3 (x4 / 2)))))))
--    (λx5 => Y (λx3 => λx4 => ?(x4 = x5) true (?((x5 % x4) = 0) false (x3 (x4 + 1)))) 2)

-- Y (λx3 => λx4 => ?((x4 > 1000000) & ((isPrime x4) & (isPowTwo (x4 + 1)))) x4 (x3 (x4 + 1))) 2

-- axiom isPrime : ℕ → Bool
-- axiom isPowTwo : ℕ → Bool

-- def f1 (x4 : ℕ) : ℕ :=
--   if x4 > 1000000 ∧ isPrime x4 ∧ isPowTwo (x4 + 1)
--     then x4
--     else f1 (x4 + 1)

  -- if x4 = 1
  --   then true
  --   else if x4 % 2 = 1
  --     then false
  --     else f2 (x4 / 2)
  -- if x4 = x5
  --   then true
  --   else if x5 % x4 = 0
  --           then false
  --           else f3 x5 (x4 + 1)


-- 2, 3, 5, 7, 11

-- #eval fib 40
-- #eval 9345873499 + 1 + 2134

#exit



-- List.foldl f a [] = a
-- List.foldl f a (x :: xs) = List.foldl f (f a x) xs

-- foldl f a x = if x = [] then a else foldl f (f a (head x)) (tail x)
-- Foldl g f a x = if x = [] then a else g (f a (head x)) (tail x)

-- def repeatProgram : Program := .abs 0 <|
--   _

-- #eval reductions (.binary .app repeatProgram (.lit (.str "R"))) 0 5

def test : List α → List α := List.foldl (fun x y => x ++ [y, y]) []

def Foldl : Program :=
  .abs 0
    (.abs 1
      (.abs 2
        (.abs 3
          (.ite
            (.binary .eq (.var 3) (.lit (.str "")))
            (.var 2)
            (.binary .app
              (.binary .app (.var 0)
                (.binary .app (.binary .app (.var 1) (.var 2))
                  (.binary .take (.lit (.int 1)) (.var 3))))
              (.binary .drop (.lit (.int 1)) (.var 3)))))))

def test1'' : Program :=
  (.binary .conc (.lit (.str "L"))
    (.binary .app
      (.binary .app
        (.abs 1
          (.binary .app
            YComb
            (Program.abs
            3
            (Program.abs
              2
              (Program.ite
                (Program.binary (Binary.eq) (Program.var 2) (Program.lit (Literal.int 1)))
                (Program.var 1)
                (Program.binary
                  (Binary.conc)
                  (Program.var 1)
                  (Program.binary
                    (Binary.app)
                    (Program.var 3)
                    (Program.binary (Binary.sub) (Program.var 2) (Program.lit (Literal.int 1))))))))))
        (.lit (.str ".")))
      (.lit (.int 199))))

#eval test1''

-- example : parse test1 = .ok
--     (.binary .conc (.lit (.str "L"))
--       (.binary .app (.binary .app sorry (.lit (.str "."))) (.lit (.int 199)))) := by
--   rw [parse, tokenise_test1']
--   simp?

-- f x = if x = [] then [] else [head x] ++ [head x] ++ f (tail x)
-- F f x = if x = [] then [] else [head x] ++ [head x] ++ f (tail x)

#print Foldl
def doubleEach : Program :=
  .binary .app
    (.binary .app
      (.binary .app YComb Foldl)
      (.abs 0
        (.abs 1
          (.binary .conc (.var 0) (.binary .conc (.var 1) (.var 1))))))
  (.lit (.str ""))

def doubleEach' : Program :=
  .binary .app YComb
    (.abs 0
      (.abs 1
        (.ite
          (.binary .eq (.var 1) (.lit (.str "")))
          (.lit (.str "solve lambdaman4 "))
          (.binary .conc
            (.binary .app (.var 0)
              (.binary .drop
                (.lit (.int 1))
                (.var 1)))
            (.binary .conc
              (.binary .take (.lit (.int 1)) (.var 1))
              (.binary .take (.lit (.int 1)) (.var 1)))
                ))))

def myProg : Program := .binary .app doubleEach' (.lit (.str "RULRRDDRRLLDRDRLDULLDRLLUUURLDRLDDDRDLRRRULRRURUUURDRDRDDULRURDDDUUUUDLLUUURRDLDURUUDLLURLDDDLUUUDDLULLUDRUDRUDDDLRDRDULDLDRLDDRRDLLLULLLRDLRURRDLRRRRUUURLDRRDRDLRULULDDUULLR"))

#eval (unpretty myProg)

#eval reductions (.binary .app doubleEach' (.lit (.str "LR"))) 0 13

#eval run (unpretty <| .binary .conc (.lit (.str "")) myProg)

#eval testOutputStringLit
  "B$ B$ L# B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L! L\" ? B= v\" I! S3/,6%},!-\"$!-!.Y} B. B$ v! B/ v\" I% B$ v# B% v\" I% L! ? B= v! I! SOO ? B= v! I\" S>> ? B= v! I# SFF SLL I\"Dj*QZ0tu&~S>0,\\>6G8N[7xP|>Ea.$:X^tJQd(G!Cy_#T~UpPVw]<"
  "solve lambdaman4 RRLLLLUUUUDDDDLLUULLUURRLLDDRRDDRRRRDDLLRRUUUUUURRRRRRRRLLDDRRRRUURRLLDDRRLLLLLLUULLLLLLDDRRRRDDDDLLRRDDLLDDLLUUDDRRDDRRLLDDDDDDUURRDDUURRDDUULLLLUULLDDDDUUUUUULLDDDDDDLLRRUULLLLDDUUUURRUUDDLLDDRRRRUUUUUULLLLDDUUUUUUUUDDDDDDRRUURRLLUUDDDDRRDDRRDDRRUUUUUURRUURRRRLLUURRRRRRLLDDRRDDDDDDLLRRDDLLRRUUUUUULLLLRRDDLLLLUUDDLLRRDDRRDDLLLLRRRRDDDDRRRRLLUURR"

#eval run "U# S!"
#eval numToString 4

#eval cfold (.unary .toInt (.lit (.str "D")))

def toDir : Program :=
  .abs 0
    (.ite
      (.binary .eq (.var 0) (.lit (.int 0))) (.lit (.str "R"))
    (.ite
      (.binary .eq (.var 0) (.lit (.int 1))) (.lit (.str "L"))
    (.ite
      (.binary .eq (.var 0) (.lit (.int 2))) (.lit (.str "U"))
    (.lit (.str "D")))))

#eval (unpretty toDir).length

#eval cfold (.unary .toStr (.lit (.int 0)))
#eval cfold (.unary .toStr (.lit (.int 1)))
#eval cfold (.unary .toStr (.lit (.int 2)))
#eval cfold (.unary .toStr (.lit (.int 3)))

def unwrap : Program :=
  .binary .app
    (.abs 2
      (.binary .app YComb
        (.abs 0
          (.abs 1
            (.ite
              (.binary .eq (.var 1) (.lit (.int 0)))
              (.lit (.str "solve lambdaman5 "))
              (.binary .conc
                (.binary .app (.var 0)
                  (.binary .quot (.var 1) (.lit (.int 4))))
                (.binary .app (.var 2)
                  (.binary .rem (.var 1) (.lit (.int 4))))))))))
  (.abs 0 <|
    (.ite
      (.binary .eq (.var 0) (.lit (.int 0))) (.lit (.str "U"))
    (.ite
      (.binary .eq (.var 0) (.lit (.int 1))) (.lit (.str "D"))
    (.ite
      (.binary .eq (.var 0) (.lit (.int 2))) (.lit (.str "L"))
    (.lit (.str "R"))))))

#exit

#eval run (unpretty (.binary .app unwrap (.lit (.int 6633436648709275211376181446523774298163658356295194901953262301057714015649683288179)))) 1000
#eval unpretty (.binary .app unwrap (.lit (.int 6633436648709275211376181446523774298163658356295194901953262301057714015649683288179)))
#eval (unpretty (.binary .app unwrap (.lit (.int 6633436648709275211376181446523774298163658356295194901953262301057714015649683288179)))).length

#eval Nat.ofDigits 4 [3, 0, 2, 3, 3, 1, 1, 3, 3, 2, 2, 1, 3, 1, 3, 2, 1, 0, 2, 2, 1, 3, 2, 2, 0, 0, 0, 3, 2, 1, 3, 2, 1, 1, 1, 3, 1, 2, 3, 3,
 3, 0, 2, 3, 3, 0, 3, 0, 0, 0, 3, 1, 3, 1, 3, 1, 1, 0, 2, 3, 0, 3, 1, 1, 1, 0, 0, 0, 0, 1, 2, 2, 0, 0, 0, 3, 3, 1, 2, 1,
 0, 3, 0, 0, 1, 2, 2, 0, 3, 2, 1, 1, 1, 2, 0, 0, 0, 1, 1, 2, 0, 2, 2, 0, 1, 3, 0, 1, 3, 0, 1, 1, 1, 2, 3, 1, 3, 1, 0, 2,
 1, 2, 1, 3, 2, 1, 1, 3, 3, 1, 2, 2, 2, 0, 2, 2, 2, 3, 1, 2, 3, 0, 3, 3, 1, 2, 3, 3, 3, 3, 0, 0, 0, 3, 2, 1, 3, 3, 1, 3,
 1, 2, 3, 0, 2, 0, 2, 1, 1, 0, 0, 2, 2, 3]

def ans : String := "RDLLLULURURDURRRRDLRRDLRRDLLDRLDULDLLLLLULDULURLLURULRURURURRRRRRRDRUURRDLDRDLLRDRDDDLDRLLDRRDLLLUDLLLLLLLLLLLLURRRLULLURLUUUUUUURDDDURUUDRUR"

#eval unpretty (.lit (.int 519814475489821910163330564047912094965750940516350360421308049078642394899611190126055241711994333288419))
#eval (unpretty (.lit (.int 519814475489821910163330564047912094965750940516350360421308049078642394899611190126055241711994333288419))).length

#eval
  ans.toList.reverse.map
  (fun
    | 'U' => 0
    | 'D' => 1
    | 'L' => 2
    | 'R' => 3
    | _ => 4) |> Nat.ofDigits 4

-- 0123
-- 1023 ok
-- 0132
-- 0213
-- 0312
-- 0321 ok
-- 1203
-- 1302 ok
-- 1230

import Mathlib.Data.Nat.Digits
import Batteries

def hello : String := "world"

def postString (s : String) : IO.Process.SpawnArgs :=
  { cmd := "curl",
    args := #["-X", "POST", "https://boundvariable.space/communicate",
              "-H", "Authorization: Bearer 936b9b2a-02ec-4fba-a92c-a2235171195c",
              "-d", s] }

def validChar (c : Char) : Option ℕ :=
    if c.toNat < 33 then none
    else if c.toNat > 126 then none
    else some c.toNat

def fullAlphabet : String :=
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789!\"#$%&'()*+,-./:;<=>?@[\\]^_`|~ \n"

def readableString (c : String) : String := c.map fun i => fullAlphabet.get ⟨i.toNat - 33⟩

def unreadableString (c : String) : String :=
  c.map fun i => Char.ofNat ((fullAlphabet.posOf i).1 + 33)

def sendString (s : String) : IO Unit := do
  let time ← IO.Process.run { cmd := "date", args := #["+%Y-%m-%dT%H:%M:%S"] }
  let time' := time.trim
  IO.println time'
  let out ← IO.Process.run <| postString <| s
  let parsedOutput := readableString <| out.extract ⟨1⟩ out.endPos
  let result := s!"Input:\n{s}\nParsed output:\n{parsedOutput}\nOutput:\n{out}"
  IO.FS.writeFile s!"responses/{time'}.txt" result
  IO.println result

def readSaved (s : System.FilePath) : IO String := do
  let r ← IO.FS.lines s
  let r : String := (r.toList.drop 3).foldl (· ++ ·) ""
  return readableString <| r.extract ⟨1⟩ r.endPos

-- #eval sendString <| "S" ++ unreadableString "get efficiency5"
-- #eval sendString <| "S" ++ unreadableString "solve efficiency5 1257787"
-- #eval sendString <| "S" ++ unreadableString "solve lambdaman5 RDLLLULURURDURRRRDLRRDLRRDLLDRLDULDLLLLLULDULURLLURULRURURURRRRRRRDRUURRDLDRDLLRDRDDDLDRLLDRRDLLLUDLLLLLLLLLLLLURRRLULLURLUUUUUUURDDDURUUDRUR"
-- #eval sendString <| "B. S%#(/} B. SF B$ B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L\" L# ? B= v# I;Y S B. ? B= B% v# IS I! S~ S B. ? B= B% v# I, I! Sa Sl B$ v\" B+ v# I\" I\""
-- #eval sendString <| "B. S%#(/} B$ B$ B$ B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L! L\" L# L$ ? B= v$ S v# B$ B$ v! B$ B$ v\" v# BT I\" v$ BD I\" v$ L! L\" B. v! B. v\" v\" S SL"

-- #eval sendString <| "S" ++ unreadableString "solve spaceship6 95662749147426858765183425341899656247512989845952549997233125757222144826644442764959379556377532462562855772222245386797366"
-- #eval sendString <| "S" ++ unreadableString "get spaceship6"

-- #eval (unreadableString "solve lambdaman4 DDLLRRUURRLLLLLLUULLUURRLLDDRRDDRRUUUUDDDDRRUUUURRRRRRRRLLDDRRRRUURRLLDDRRLLLLLLUULLLLLLDDRRRRDDDDLLRRDDLLDDLLUUDDRRDDRRLLDDDDDDUURRDDUURRDDUULLLLUULLDDDDUUUUUULLDDDDDDLLRRUULLLLDDUUUURRUUDDLLDDRRRRUUUUUULLUUUUDDRRLLDDLLDDUUUUUUUUDDDDDDRRRRDDRRDDRRUUUUUURRUURRRRLLUURRRRRRLLDDRRDDDDDDLLRRDDLLRRUUUUUULLLLRRDDLLLLUUDDLLRRDDRRDDLLLLRRRRDDDDRRRRLLUURR").length
-- #eval sendString <| "B$ B$ L# B$ L\" B$ L# B$ v\" B$ v# v# L# B$ v\" B$ v# v# L! L\" ? B= v\" I! S3/,6%},!-\"$!-!.Z} B. B$ v! B/ v\" I% B$ v# B% v\" I% L! ? B= v! I! SO ? B= v! I\" S> ? B= v! I# SF SL Iz3s7h5Aa=|[9#4:&e|9N|{0(2{I9fKzQp{03]8lrCm\\"

def main : IO Unit := do
  IO.println "hi"
--   let out ← IO.Process.run <| postString "S'%4}.$%8"
--   IO.FS.writeFile "ICFP2024/result.txt" out
--   IO.println out

-- B$ L+ B. B. SF B$ B$ v+ Sl IR B$ B$ v+ B. S~ B$ B$ v+ Sl IS IR L" B$ L" B$ L# B$ v" B$ v# v# L# B$ v" B$ v# v# L$ L# ? B= v# I" v" B. v" B$ v$ B- v# I"
-- B. SF B$ B$ L" B$ L# B$ v" B$ v# v# L# B$ v" B$ v# v# L" L# ? B= v# I;Y S B. ? B= B% v# IS I! S~ S B. ? B= B% v# I, I! Sa Sl B$ v" B+ v# I" I"

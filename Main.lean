/-
  Command line front end, used by the tests.

  Reads one request per line and prints one answer per line. A
  request is an operation and its input as comma-separated decimal
  character codes.

    parse 91,34,97,34,93   prints  ok:91,34,97,34,93
    parse 91,93            prints  ok:91,93
    parse 120               prints  none
    num 49,46,53,48        prints  ok:49,46,53
    num 48,49               prints  none

  The operations are `parse` and `num`. The input of `parse` is
  the character codes of a JSON text. Its answer is `ok:` and the
  character codes of the canonical print of the parsed value, or
  `none` when the text is rejected.

  The input of `num` is the character codes of a number text.
  Its answer is `ok:` and the character codes of the canonical
  text of the number's value (slice 2: the exact decimal value,
  printed in plain notation), or `none` when the text is not a
  number by the grammar of RFC 8259.

  A request is an operation, then optionally one space and its
  numbers; with no numbers after the space, the input is empty. A
  malformed request prints `error`: any other line, an unknown
  operation, a number that is not plain decimal digits, or a
  character code that is not a Unicode scalar value. A line may end
  in LF or CR LF; nothing else around a request is ignored.

  The parsing and printing here call `Json.parse` and `Json.print`
  directly. The line handling is covered by the tests, not by a
  proof.
-/

import Json

open Json

/-- A number in plain decimal digits. Longer numbers than any
    character code are refused before they are converted, since
    that takes time quadratic in their length. -/
def number (t : String) : Option Nat :=
  let ds := t.toList
  if ds.isEmpty || !ds.all Char.isDigit || (ds.dropWhile (· = '0')).length > 7 then none
  else t.toNat?

/-- The comma-separated numbers in `s`. -/
def numbers (s : String) : Option (List Nat) :=
  if s.isEmpty then some [] else (s.splitOn ",").mapM number

def toChars (ns : List Nat) : Option (List Char) :=
  ns.mapM fun n => if n.isValidChar then some (Char.ofNat n) else none

def showCodes (cs : List Char) : String :=
  ",".intercalate (cs.map fun c => toString c.toNat)

/-- The answer to one request, or `none` when the request is
    malformed. -/
def answer (op : String) (ns : List Nat) : Option String :=
  match op with
  | "parse" =>
    match toChars ns with
    | none => none
    | some cs =>
      match parse cs with
      | some v => some ("ok:" ++ showCodes (print v))
      | none => some "none"
  | "num" =>
    match toChars ns with
    | none => none
    | some cs =>
      match readNumber cs with
      | some v => some ("ok:" ++ showCodes (printVal v))
      | none => some "none"
  | _ => none

/-- The answer to one line: an operation, then optionally one space
    and its numbers. -/
def request (line : String) : Option String :=
  match line.splitOn " " with
  | [op] => answer op []
  | [op, arg] => numbers arg >>= answer op
  | _ => none

/-- The line without its line ending: LF, or CR LF. -/
def chomp (line : String) : String :=
  let cs := line.toList
  if cs.getLast? = some '\n' then
    let cs := cs.dropLast
    String.ofList (if cs.getLast? = some '\r' then cs.dropLast else cs)
  else line

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let line := chomp line
    stdout.putStrLn ((request line).getD "error")

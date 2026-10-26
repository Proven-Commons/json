/-
  Slice 2: a number value layer for JSON numbers.

  Slice 1 holds a number as its source text and makes no claim
  about its value. This file adds the value: an exact decimal,
  held as a sign, a significand (a natural number), and an
  exponent (an integer, a power of ten). The value is

    (if neg then -1 else 1) * sig * 10 ^ exp

  A value is held in one canonical shape:

  - zero is held as `neg = false`, `sig = 0`, `exp = 0`. Every
    spelling of zero, `-0` and `0.0e5` included, reads to this
    one value.
  - a nonzero value is held normalized: its significand has no
    trailing zero (`sig % 10 != 0`). Trailing zeros are divided
    out of the significand and added into the exponent, so the
    held form is unique per value.

  The reader in this file reads a number text on its own, by the
  number grammar of RFC 8259. It reuses the part readers of
  `Json.Parse` (`parseIntPart`, `parseFracOpt`, `parseExpOpt`),
  which together accept exactly that grammar, and it does not
  touch the document parser. The whole text must be the number:
  anything after the number part makes the read fail.

  The printer writes the canonical text of a value, always in
  plain decimal notation, with no exponent part: the point is
  placed by the exponent, a `0` is written before the point when
  the value is below one, and zeros pad the text when the
  exponent pushes the point past the digits.
-/

import Json.Parse

namespace Json

/-- An exact decimal value: a sign, a significand, and an
    exponent (a power of ten). -/
structure DecVal where
  neg : Bool
  sig : Nat
  exp : Int
deriving DecidableEq, Repr

/-- The canonical zero value. -/
def decZero : DecVal := ⟨false, 0, 0⟩

/-- Well formed, for the value layer: the value is held in its
    canonical shape. Either it is the canonical zero, or its
    significand is nonzero with no trailing zero. -/
def WFVal (v : DecVal) : Prop :=
  (v.sig = 0 ∧ v.neg = false ∧ v.exp = 0) ∨
  (v.sig ≠ 0 ∧ v.sig % 10 ≠ 0)

/-- One decimal digit step of the fold that turns a list of
    digits into a natural number. -/
def digitStep (acc d : Nat) : Nat := acc * 10 + d

/-- The fold of a digit list, starting from a given value. -/
def foldDigits (a : Nat) (ds : List Nat) : Nat :=
  ds.foldl digitStep a

/-- The natural number a list of digits (most significant first)
    stands for. -/
def natOfDigits (ds : List Nat) : Nat :=
  foldDigits 0 ds

/-- The value of a digit character. Only meaningful on characters
    the digit test accepts; there it is the digit itself. -/
def digitVal (c : Char) : Nat := c.toNat - 48

/-- The text of a list of digits: each digit below 16 prints by
    the hex digit table of `Json.Value`, whose first ten entries
    are the decimal digits. -/
def digitChars (ds : List Nat) : List Char :=
  ds.map hexDigit

/-- Strip the trailing zeros of a natural number, with fuel.
    Returns the stripped significand and the count stripped.
    The fuel bounds the count of divisions; called with
    `n + 1` it always suffices, since each division shrinks
    a positive number. -/
def stripAux (n : Nat) : Nat → Nat × Nat
  | 0 => (n, 0)
  | fuel + 1 =>
    if n = 0 then (0, 0)
    else if n % 10 = 0 then
      let (m, k) := stripAux (n / 10) fuel
      (m, k + 1)
    else (n, 0)

/-- The value held for a sign, an integer digit list, a fraction
    digit list, and a written exponent. The digits fold into one
    significand, the exponent drops by the fraction length, and
    the result is normalized: trailing zeros of the significand
    move into the exponent, and zero collapses to the canonical
    zero. -/
def valueOfDigits (neg : Bool) (intDs fracDs : List Nat) (expW : Int) : DecVal :=
  let d := intDs ++ fracDs
  let n := natOfDigits d
  let (m, k) := stripAux n (n + 1)
  if m = 0 then decZero
  else ⟨neg, m, expW - (fracDs.length : Int) + (k : Int)⟩

/-- The written exponent of an exponent part, as read by
    `parseExpOpt`: empty when there is no part, else the letter,
    an optional sign, and digits. -/
def expValOfChars : List Char → Int
  | [] => 0
  | _ :: rest =>
    match rest with
    | '+' :: ds => (natOfDigits (ds.map digitVal) : Int)
    | '-' :: ds => -(natOfDigits (ds.map digitVal) : Int)
    | ds => (natOfDigits (ds.map digitVal) : Int)

/-- Read a number body (the text after the sign) to its value,
    for a given sign. The whole of the text must be the number:
    anything after the number part makes the read fail. -/
def readNumberFrom (neg : Bool) (rest0 : List Char) : Option DecVal :=
  match parseIntPart rest0 with
  | none => none
  | some (ichars, r1) =>
    match parseFracOpt r1 with
    | none => none
    | some (fchars, r2) =>
      match parseExpOpt r2 with
      | none => none
      | some (echars, r3) =>
        if r3 = [] then
          some (valueOfDigits neg (ichars.map digitVal)
            ((fchars.drop 1).map digitVal) (expValOfChars echars))
        else none

/-- Read a whole number text to its value. The text must be one
    number by the grammar of RFC 8259, with nothing before it
    (beyond the sign the grammar allows) and nothing after it. -/
def readNumber (cs : List Char) : Option DecVal :=
  if cs.head? = some '-' then readNumberFrom true cs.tail
  else readNumberFrom false cs

/-- The digits of a natural number, least significant first,
    with fuel. Called with `n + 1` the fuel always suffices.
    The digits of 0 are the empty list here; `digitsOf` adds
    the canonical single zero. -/
def digsRevAux (n : Nat) : Nat → List Nat
  | 0 => []
  | fuel + 1 =>
    if n = 0 then [] else (n % 10) :: digsRevAux (n / 10) fuel

/-- The digits of a natural number, most significant first.
    The digits of 0 are `[0]`. -/
def digitsOf (n : Nat) : List Nat :=
  if n = 0 then [0] else (digsRevAux n (n + 1)).reverse

/-- The value of a digit list read least significant first:
    the head counts once, the next ten times, and so on. -/
def powVal : List Nat → Nat
  | [] => 0
  | d :: ds => d + 10 * powVal ds

/-- The canonical text of a value: plain decimal notation,
    always. Zero prints as `0`. A negative nonzero value takes
    a leading minus. The point is placed by the exponent, with
    a `0` before it when the value is below one, and zero
    padding when the exponent pushes the point past the
    digits. -/
def printVal (v : DecVal) : List Char :=
  if v.sig = 0 then ['0']
  else
    let ds := digitsOf v.sig
    let body : List Char :=
      if v.exp ≥ 0 then
        digitChars ds ++ List.replicate v.exp.toNat '0'
      else
        let p : Int := (ds.length : Int) + v.exp
        if p > 0 then
          digitChars (ds.take p.toNat) ++ '.' :: digitChars (ds.drop p.toNat)
        else
          ['0', '.'] ++ List.replicate (-p).toNat '0' ++ digitChars ds
    if v.neg then '-' :: body else body

/-- The canonical text of the value of a text, when the text
    reads as a number. -/
def canonicalText (cs : List Char) : Option (List Char) :=
  (readNumber cs).map printVal

end Json

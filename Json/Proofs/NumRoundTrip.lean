/-
  The round trip proof for the number value layer of slice 2:
  for every well formed value, reading its printed form gives
  the value back.

  The statement proved here is `read_print`. A matching statement
  in a spec file still has to be added by a reviewer, so this
  file builds on its own, in the same shape as the slice 1 proofs.

  Plan of the proof. A printed value is a sign, then digits with
  the point placed by the exponent. Three shapes occur: the
  exponent is not negative (digits, then zero padding, no
  point), the point falls inside the digits, and the point
  falls before the digits (a `0`, a point, zero padding, then
  the digits). In each shape the part readers of slice 1 read
  the parts whole (the lemmas of `Json.Proofs` cover the
  integer and fraction parts), the digit fold gives back the
  significand times a power of ten, and the trailing zero
  strip is pinned down by a uniqueness lemma: a positive
  integer with a last digit other than zero factors as itself
  times a power of ten in only one way.
-/

import Json
import Json.Proofs.RoundTrip

namespace Json.NumProofs

open Json

/-! ## Digit characters -/

/-- The character for a digit below 10 is a digit character. -/
theorem isDigit_hexDigit : ∀ d : Fin 10, IsDigit (hexDigit d.val) := by
  have h : ∀ d : Fin 10, ('0' ≤ hexDigit d.val ∧ hexDigit d.val ≤ '9') := by
    decide
  exact h

/-- The character for a digit below 10 passes the digit test. -/
theorem isDigit_test_hexDigit (d : Nat) (h : d < 10) : isDigit (hexDigit d) = true :=
  Json.Proofs.isDigit_of_isDigit (isDigit_hexDigit ⟨d, h⟩)

/-- The value of the character for a digit below 10 is the
    digit. -/
theorem digitVal_hexDigit : ∀ d : Fin 10, digitVal (hexDigit d.val) = d.val := by
  decide

/-- The character for a digit from 1 to 9 lies between `1` and
    `9`. -/
theorem hexDigit_range : ∀ d : Fin 10, 1 ≤ d.val →
    '1' ≤ hexDigit d.val ∧ hexDigit d.val ≤ '9' := by
  decide

/-- The character for a digit below 10 is not a minus sign. -/
theorem hexDigit_ne_minus : ∀ d : Fin 10, hexDigit d.val ≠ '-' := by
  decide

/-- The character for 0 is `0`. -/
theorem hexDigit_zero : hexDigit 0 = '0' := by
  decide

/-! ## The digit fold -/

/-- One step of the fold, on a cons. -/
theorem foldDigits_cons (a d : Nat) (ds : List Nat) :
    foldDigits a (d :: ds) = foldDigits (a * 10 + d) ds :=
  rfl

/-- The fold from any starting value: the starting value counts
    shifted by the length of the list, plus the fold of the
    list itself. -/
theorem foldDigits_spec : ∀ (a : Nat) (ds : List Nat),
    foldDigits a ds = a * 10 ^ ds.length + natOfDigits ds := by
  intro a ds
  induction ds generalizing a with
  | nil => simp [foldDigits, natOfDigits]
  | cons d ds ih =>
    rw [foldDigits_cons, ih]
    have ih' := ih d
    have hnd : natOfDigits (d :: ds) = d * 10 ^ ds.length + natOfDigits ds := by
      show foldDigits 0 (d :: ds) = _
      rw [foldDigits_cons]
      simpa using ih'
    rw [hnd]
    have hpow : (10 : Nat) ^ (ds.length + 1) = 10 ^ ds.length * 10 :=
      Nat.pow_succ 10 ds.length
    simp only [List.length_cons]
    rw [hpow, Nat.add_mul]
    have e : (a * 10) * 10 ^ ds.length = a * (10 ^ ds.length * 10) := by ac_rfl
    rw [e, Nat.add_assoc]

/-- The fold over a joined list is the fold of the second
    part, started from the fold of the first. -/
theorem foldDigits_append (a : Nat) (as bs : List Nat) :
    foldDigits a (as ++ bs) = foldDigits (foldDigits a as) bs :=
  List.foldl_append

/-- The number of a joined digit list: the first part counts
    shifted by the length of the second. -/
theorem natOfDigits_append (as bs : List Nat) :
    natOfDigits (as ++ bs) =
      natOfDigits as * 10 ^ bs.length + natOfDigits bs := by
  show foldDigits 0 (as ++ bs) = _
  rw [foldDigits_append]
  exact foldDigits_spec _ _

/-- A list of zeros stands for zero. -/
theorem natOfDigits_replicate_zero : ∀ k : Nat,
    natOfDigits (List.replicate k 0) = 0 := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ]
    show natOfDigits (0 :: List.replicate k 0) = 0
    rw [show natOfDigits (0 :: List.replicate k 0) =
      natOfDigits (List.replicate k 0) from rfl]
    exact ih

/-- A single digit stands for itself. -/
theorem natOfDigits_singleton (d : Nat) : natOfDigits [d] = d := by
  simp [natOfDigits, foldDigits, digitStep]

/-! ## The trailing zero strip -/

/-- The strip, specified: the stripped significand times ten
    to the stripped count is the number; zero strips to
    `(0, 0)`; a nonzero stripped significand does not end in
    zero. The fuel bound `n ≤ fuel` is what the induction
    spends: each step divides by ten. -/
theorem stripAux_spec : ∀ (fuel n : Nat), n ≤ fuel →
    (stripAux n fuel).1 * 10 ^ (stripAux n fuel).2 = n ∧
    (n = 0 → stripAux n fuel = (0, 0)) ∧
    ((stripAux n fuel).1 ≠ 0 → (stripAux n fuel).1 % 10 ≠ 0) := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    exact ⟨by simp [stripAux], fun _ => rfl,
      fun h => absurd (show (stripAux 0 0).fst = 0 from rfl) h⟩
  | succ fuel ih =>
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      refine ⟨by simp [stripAux], fun _ => rfl, fun h => ?_⟩
      simp [stripAux] at h
    · by_cases hmod : n % 10 = 0
      · have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
        have hle : n / 10 ≤ fuel := by omega
        obtain ⟨ih1, -, ih3⟩ := ih (n / 10) hle
        obtain ⟨m, k, hmk⟩ : ∃ m k, stripAux (n / 10) fuel = (m, k) :=
          ⟨_, _, rfl⟩
        have hstrip : stripAux n (fuel + 1) = (m, k + 1) := by
          simp [stripAux, hn0, hmod, hmk]
        have h10 : m * 10 ^ k = n / 10 := by
          have h := ih1
          rw [hmk] at h
          exact h
        have ih3' : m ≠ 0 → m % 10 ≠ 0 := by
          have h := ih3
          rw [hmk] at h
          exact h
        refine ⟨?_, fun h => absurd h hn0, ?_⟩
        · rw [hstrip]
          show m * 10 ^ (k + 1) = n
          have hps : (10 : Nat) ^ (k + 1) = 10 ^ k * 10 := Nat.pow_succ 10 k
          rw [hps]
          have hmul : m * (10 ^ k * 10) = (n / 10) * 10 := by
            rw [← h10]
            ac_rfl
          rw [hmul]
          omega
        · rw [hstrip]
          exact ih3'
      · have hstrip : stripAux n (fuel + 1) = (n, 0) := by
          simp [stripAux, hn0, hmod]
        refine ⟨?_, fun h => absurd h hn0, ?_⟩
        · rw [hstrip]
          show n * 10 ^ 0 = n
          simp
        · rw [hstrip]
          exact fun _ => hmod

/-- Uniqueness of the strip: if `a * 10 ^ i = b * 10 ^ j` and
    neither `a` nor `b` ends in zero, then `a = b` and
    `i = j`. A factor of ten on one side would force a
    trailing zero on the other. -/
theorem strip_unique {a b i j : Nat} (ha : a % 10 ≠ 0) (hb : b % 10 ≠ 0)
    (h : a * 10 ^ i = b * 10 ^ j) : a = b ∧ i = j := by
  rcases Nat.lt_trichotomy i j with hij | rfl | hij
  · exfalso
    have hji : j = i + (j - i) := by omega
    rw [hji, Nat.pow_add] at h
    have h10 : 0 < 10 ^ i := Nat.pow_pos (by decide)
    have h' : a * 10 ^ i = (b * 10 ^ (j - i)) * 10 ^ i := by
      rw [h]
      ac_rfl
    have ha' : a = b * 10 ^ (j - i) := Nat.mul_right_cancel h10 h'
    have hpos : 0 < j - i := by omega
    obtain ⟨t, ht⟩ : ∃ t, j - i = t + 1 := ⟨j - i - 1, by omega⟩
    have hps : (10 : Nat) ^ (t + 1) = 10 ^ t * 10 := Nat.pow_succ 10 t
    rw [ht, hps] at ha'
    have hdvd : a % 10 = 0 := by
      rw [ha']
      have e : b * (10 ^ t * 10) = 10 * (b * 10 ^ t) := by ac_rfl
      rw [e]
      exact Nat.mul_mod_right 10 _
    exact ha hdvd
  · exact ⟨Nat.mul_right_cancel (Nat.pow_pos (by decide)) h, rfl⟩
  · exfalso
    have hji : i = j + (i - j) := by omega
    rw [hji, Nat.pow_add] at h
    have h10 : 0 < 10 ^ j := Nat.pow_pos (by decide)
    have h' : (a * 10 ^ (i - j)) * 10 ^ j = b * 10 ^ j := by
      rw [← h]
      ac_rfl
    have hb' : a * 10 ^ (i - j) = b := Nat.mul_right_cancel h10 h'
    have hpos : 0 < i - j := by omega
    obtain ⟨t, ht⟩ : ∃ t, i - j = t + 1 := ⟨i - j - 1, by omega⟩
    have hps : (10 : Nat) ^ (t + 1) = 10 ^ t * 10 := Nat.pow_succ 10 t
    rw [ht, hps] at hb'
    have hdvd : b % 10 = 0 := by
      rw [← hb']
      have e : a * (10 ^ t * 10) = 10 * (a * 10 ^ t) := by ac_rfl
      rw [e]
      exact Nat.mul_mod_right 10 _
    exact hb hdvd

/-! ## Digits of a number -/

/-- The reversed digits of 0 are empty, at any fuel. -/
theorem digsRevAux_zero : ∀ fuel : Nat, digsRevAux 0 fuel = [] := by
  intro fuel
  cases fuel with
  | zero => rfl
  | succ fuel => rfl

/-- The reversed digit list of a number, specified: read least
    significant first it gives the number back, and every
    digit is below ten. -/
theorem digsRevAux_spec : ∀ (fuel n : Nat), n ≤ fuel →
    powVal (digsRevAux n fuel) = n ∧
    ∀ d ∈ digsRevAux n fuel, d < 10 := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn
    have hn0 : n = 0 := Nat.eq_zero_of_le_zero hn
    subst hn0
    exact ⟨rfl, fun d hd => by simp [digsRevAux] at hd⟩
  | succ fuel ih =>
    intro n hn
    by_cases hn0 : n = 0
    · subst hn0
      exact ⟨by simp [digsRevAux, powVal], fun d hd => by
        simp [digsRevAux] at hd⟩
    · have hlt : n / 10 < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn0) (by decide)
      have hle : n / 10 ≤ fuel := by omega
      obtain ⟨ih1, ih2⟩ := ih (n / 10) hle
      have hdigs : digsRevAux n (fuel + 1) =
          (n % 10) :: digsRevAux (n / 10) fuel := by
        simp [digsRevAux, hn0]
      refine ⟨?_, ?_⟩
      · rw [hdigs]
        show n % 10 + 10 * powVal (digsRevAux (n / 10) fuel) = n
        rw [ih1]
        omega
      · intro d hd
        rw [hdigs] at hd
        cases List.mem_cons.mp hd with
        | inl h => rw [h]; exact Nat.mod_lt n (by decide)
        | inr h => exact ih2 d h

/-- The last reversed digit of a positive number (its most
    significant digit) is not zero, and the list is not
    empty. -/
theorem digsRevAux_getLast : ∀ (fuel n : Nat), n ≤ fuel → 0 < n →
    (digsRevAux n fuel).getLast? ≠ some 0 ∧
    digsRevAux n fuel ≠ [] := by
  intro fuel
  induction fuel with
  | zero =>
    intro n hn hpos
    omega
  | succ fuel ih =>
    intro n hn hpos
    have hn0 : n ≠ 0 := Nat.pos_iff_ne_zero.mp hpos
    have hdigs : digsRevAux n (fuel + 1) =
        (n % 10) :: digsRevAux (n / 10) fuel := by
      simp [digsRevAux, hn0]
    by_cases hdiv : n / 10 = 0
    · have hlt10 : n < 10 := by omega
      have hmod : n % 10 = n := Nat.mod_eq_of_lt hlt10
      refine ⟨?_, by rw [hdigs]; simp⟩
      rw [hdigs, hdiv]
      simp [digsRevAux_zero, hmod, hn0]
    · have hpos' : 0 < n / 10 := Nat.pos_of_ne_zero hdiv
      have hle : n / 10 ≤ fuel := by
        have hlt : n / 10 < n := Nat.div_lt_self hpos (by decide)
        omega
      obtain ⟨ih1, ih2⟩ := ih (n / 10) hle hpos'
      refine ⟨?_, by rw [hdigs]; simp⟩
      obtain ⟨a, as, htail⟩ : ∃ a as, digsRevAux (n / 10) fuel = a :: as :=
        List.exists_cons_of_ne_nil ih2
      rw [hdigs, htail]
      simp only [List.getLast?_cons_cons]
      rw [← htail]
      exact ih1

/-- Reading a reversed digit list back: the fold of the
    reversal is the least significant first value. -/
theorem natOfDigits_reverse (l : List Nat) :
    natOfDigits l.reverse = powVal l := by
  induction l with
  | nil => rfl
  | cons d ds ih =>
    rw [List.reverse_cons, natOfDigits_append, ih, natOfDigits_singleton]
    show powVal ds * 10 ^ ([d] : List Nat).length + d = d + 10 * powVal ds
    simp
    omega

/-- The digits of a number fold back to the number. -/
theorem natOfDigits_digitsOf (n : Nat) : natOfDigits (digitsOf n) = n := by
  by_cases hn : n = 0
  · subst hn
    simp [digitsOf, natOfDigits_singleton]
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have hdigs : digitsOf n = (digsRevAux n (n + 1)).reverse := by
      simp [digitsOf, hn]
    rw [hdigs, natOfDigits_reverse]
    exact (digsRevAux_spec (n + 1) n (Nat.le_succ n)).1

/-- Every digit of a number is below ten. -/
theorem digitsOf_lt (n : Nat) : ∀ d ∈ digitsOf n, d < 10 := by
  by_cases hn : n = 0
  · subst hn
    intro d hd
    simp [digitsOf] at hd
    omega
  · intro d hd
    have hdigs : digitsOf n = (digsRevAux n (n + 1)).reverse := by
      simp [digitsOf, hn]
    rw [hdigs] at hd
    exact (digsRevAux_spec (n + 1) n (Nat.le_succ n)).2 d
      (List.mem_reverse.mp hd)

/-- The first digit of a positive number: there is one, it is
    below ten, and it is not zero. The head of the digit list
    is the last of the reversed list, which the reversed
    list lemma pins away from zero. -/
theorem digitsOf_cons {n : Nat} (hn : 0 < n) :
    ∃ d ds, digitsOf n = d :: ds ∧ d ≠ 0 ∧ d < 10 := by
  have hne : n ≠ 0 := Nat.pos_iff_ne_zero.mp hn
  have hdigs : digitsOf n = (digsRevAux n (n + 1)).reverse := by
    simp [digitsOf, hne]
  obtain ⟨hgl, hnil⟩ := digsRevAux_getLast (n + 1) n (Nat.le_succ n) hn
  have hrev : digitsOf n ≠ [] := by
    rw [hdigs]
    intro h
    exact hnil (List.reverse_eq_nil_iff.mp h)
  obtain ⟨d, ds, hds⟩ : ∃ d ds, digitsOf n = d :: ds :=
    List.exists_cons_of_ne_nil hrev
  refine ⟨d, ds, hds, ?_, digitsOf_lt n d (by rw [hds]; exact List.mem_cons_self)⟩
  intro hd0
  have hhead : (digitsOf n).head? = some d := by
    rw [hds]
    rfl
  rw [hdigs, List.head?_reverse] at hhead
  exact hgl (by rw [hhead, hd0])

/-! ## Digit text -/

/-- Reading the digit characters of a digit list back gives
    the digits, when every digit is below ten. -/
theorem map_digitVal_digitChars : ∀ {ds : List Nat},
    (∀ d ∈ ds, d < 10) → (digitChars ds).map digitVal = ds := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons d ds ih =>
    intro h
    have hd : d < 10 := h d (List.mem_cons_self)
    have hds : ∀ x ∈ ds, x < 10 := fun x hx => h x (List.mem_cons_of_mem d hx)
    show digitVal (hexDigit d) :: (digitChars ds).map digitVal = d :: ds
    rw [digitVal_hexDigit ⟨d, hd⟩, ih hds]

/-- The digit characters of a joined list are the join of the
    digit characters. -/
theorem digitChars_append (as bs : List Nat) :
    digitChars (as ++ bs) = digitChars as ++ digitChars bs :=
  List.map_append

/-- The digit characters of a list of zeros are zero
    characters. -/
theorem digitChars_replicate_zero (k : Nat) :
    digitChars (List.replicate k 0) = List.replicate k '0' := by
  simp [digitChars, List.map_replicate, hexDigit_zero]

/-! ## Reading the printed shapes -/

/-- The integer part reader reads a digit text whole, when the
    first digit is not zero and what follows cannot be a
    digit. -/
theorem parseIntPart_digitChars {ds : List Nat} {tail : List Char}
    (hds : ∃ d ds', ds = d :: ds' ∧ d ≠ 0)
    (hb : ∀ x ∈ ds, x < 10)
    (ht : ∀ c, tail.head? = some c → isDigit c = false) :
    parseIntPart (digitChars ds ++ tail) = some (digitChars ds, tail) := by
  obtain ⟨d, ds', rfl, hd0⟩ := hds
  have hd10 : d < 10 := hb d (List.mem_cons_self)
  have hr : '1' ≤ hexDigit d ∧ hexDigit d ≤ '9' :=
    hexDigit_range ⟨d, hd10⟩ (Nat.pos_of_ne_zero hd0)
  have hne : hexDigit d ≠ '0' := by
    intro hcon
    have h1 : digitVal (hexDigit d) = digitVal '0' := by rw [hcon]
    rw [digitVal_hexDigit ⟨d, hd10⟩] at h1
    have h2 : digitVal '0' = 0 := by decide
    rw [h2] at h1
    exact hd0 h1
  have htk : takeDigits (digitChars ds' ++ tail) = (digitChars ds', tail) :=
    Json.Proofs.takeDigits_append
      (fun x hx => by
        obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
        exact isDigit_test_hexDigit y (hb y (List.mem_cons_of_mem d hy)))
      ht
  show parseIntPart (hexDigit d :: (digitChars ds' ++ tail)) =
    some (digitChars (d :: ds'), tail)
  unfold parseIntPart
  dsimp only
  rw [if_neg hne, if_pos hr, htk]
  dsimp only
  rfl

/-- A fraction text over digit characters is a well formed
    fraction part. -/
theorem fracOk_digitChars {fds : List Nat} (hb : ∀ x ∈ fds, x < 10)
    {d : Nat} {ds : List Nat} (h : fds = d :: ds) :
    FracOk ('.' :: digitChars fds) := by
  refine Or.inr ⟨hexDigit d, digitChars ds, ?_, ?_, ?_⟩
  · rw [h]
    rfl
  · exact isDigit_hexDigit ⟨d, hb d (by rw [h]; exact List.mem_cons_self)⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
    exact isDigit_hexDigit ⟨y, hb y (by
      rw [h]
      exact List.mem_cons_of_mem d hy)⟩

/-- The fraction part reader reads a fraction text over digit
    characters whole, at the end of a text. -/
theorem parseFracOpt_digitChars {fds : List Nat} (hb : ∀ x ∈ fds, x < 10)
    {d : Nat} {ds : List Nat} (h : fds = d :: ds) :
    parseFracOpt ('.' :: digitChars fds) = some ('.' :: digitChars fds, []) := by
  have h' := Json.Proofs.parseFracOpt_append (frac := '.' :: digitChars fds)
    (tail := []) (fracOk_digitChars hb h) (fun c hc => by simp at hc)
  simpa using h'

/-- The reader, assembled: when the three part readers read
    their parts whole and nothing is left, the read is the
    value of the parts. -/
theorem readNumberFrom_eq {neg : Bool} {rest0 ichars r1 fchars r2 echars : List Char}
    (hInt : parseIntPart rest0 = some (ichars, r1))
    (hFrac : parseFracOpt r1 = some (fchars, r2))
    (hExp : parseExpOpt r2 = some (echars, [])) :
    readNumberFrom neg rest0 =
      some (valueOfDigits neg (ichars.map digitVal)
        ((fchars.drop 1).map digitVal) (expValOfChars echars)) := by
  unfold readNumberFrom
  rw [hInt]
  dsimp only
  rw [hFrac]
  dsimp only
  rw [hExp]
  dsimp only
  exact if_pos rfl

/-- The value of digits, when the folded digits are a stripped
    significand times a power of ten: normalization is forced
    by the uniqueness of the strip. -/
theorem valueOfDigits_strip {neg : Bool} {intDs fracDs : List Nat} {expW : Int}
    {s e : Nat} (hs : s % 10 ≠ 0)
    (hN : natOfDigits (intDs ++ fracDs) = s * 10 ^ e) :
    valueOfDigits neg intDs fracDs expW =
      ⟨neg, s, expW - (fracDs.length : Int) + (e : Int)⟩ := by
  obtain ⟨m, k, hmk⟩ : ∃ m k,
      stripAux (natOfDigits (intDs ++ fracDs))
        (natOfDigits (intDs ++ fracDs) + 1) = (m, k) :=
    ⟨_, _, rfl⟩
  have hval : valueOfDigits neg intDs fracDs expW =
      if m = 0 then decZero
      else ⟨neg, m, expW - (fracDs.length : Int) + (k : Int)⟩ := by
    simp only [valueOfDigits, hmk]
  obtain ⟨h1, -, h3⟩ := stripAux_spec
    (natOfDigits (intDs ++ fracDs) + 1) (natOfDigits (intDs ++ fracDs))
    (Nat.le_succ _)
  rw [hmk] at h1 h3
  simp only at h1 h3
  rw [hN] at h1
  have hpos : 0 < s * 10 ^ e := by
    have hspos : 0 < s := by
      rcases Nat.eq_zero_or_pos s with hs0 | hspos
      · rw [hs0] at hs
        exact absurd (by decide : (0 : Nat) % 10 = 0) hs
      · exact hspos
    exact Nat.mul_pos hspos (Nat.pow_pos (by decide))
  have hmne : m ≠ 0 := by
    intro hm
    rw [hm] at h1
    simp at h1
    omega
  obtain ⟨rfl, rfl⟩ : m = s ∧ k = e := strip_unique (h3 hmne) hs h1
  rw [hval, if_neg hmne]

/-- Every value the digit reader builds is well formed: the
    strip leaves a significand that is zero (and the value
    collapses to the canonical zero) or does not end in
    zero. -/
theorem valueOfDigits_wf (neg : Bool) (intDs fracDs : List Nat) (expW : Int) :
    WFVal (valueOfDigits neg intDs fracDs expW) := by
  obtain ⟨m, k, hmk⟩ : ∃ m k,
      stripAux (natOfDigits (intDs ++ fracDs))
        (natOfDigits (intDs ++ fracDs) + 1) = (m, k) :=
    ⟨_, _, rfl⟩
  have hval : valueOfDigits neg intDs fracDs expW =
      if m = 0 then decZero
      else ⟨neg, m, expW - (fracDs.length : Int) + (k : Int)⟩ := by
    simp only [valueOfDigits, hmk]
  obtain ⟨-, -, h3⟩ := stripAux_spec
    (natOfDigits (intDs ++ fracDs) + 1) (natOfDigits (intDs ++ fracDs))
    (Nat.le_succ _)
  rw [hmk] at h3
  simp only at h3
  by_cases hm : m = 0
  · rw [hval, if_pos hm]
    exact Or.inl ⟨rfl, rfl, rfl⟩
  · rw [hval, if_neg hm]
    exact Or.inr ⟨hm, h3 hm⟩

/-- A value read by the body reader is the value of some
    digit parts. -/
theorem readNumberFrom_eq_valueOfDigits {neg : Bool} {rest0 : List Char}
    {v : DecVal} (h : readNumberFrom neg rest0 = some v) :
    ∃ (intDs fracDs : List Nat) (expW : Int),
      v = valueOfDigits neg intDs fracDs expW := by
  unfold readNumberFrom at h
  cases hInt : parseIntPart rest0 with
  | none => rw [hInt] at h; simp at h
  | some p1 =>
    obtain ⟨ichars, r1⟩ := p1
    rw [hInt] at h
    dsimp only at h
    cases hFrac : parseFracOpt r1 with
    | none => rw [hFrac] at h; simp at h
    | some p2 =>
      obtain ⟨fchars, r2⟩ := p2
      rw [hFrac] at h
      dsimp only at h
      cases hExp : parseExpOpt r2 with
      | none => rw [hExp] at h; simp at h
      | some p3 =>
        obtain ⟨echars, r3⟩ := p3
        rw [hExp] at h
        dsimp only at h
        by_cases hr : r3 = []
        · rw [if_pos hr] at h
          refine ⟨ichars.map digitVal, (fchars.drop 1).map digitVal,
            expValOfChars echars, ?_⟩
          exact (Option.some.inj h).symm
        · rw [if_neg hr] at h
          simp at h

/-- Every value the number reader returns is well formed. -/
theorem readNumber_wf {cs : List Char} {v : DecVal}
    (h : readNumber cs = some v) : WFVal v := by
  unfold readNumber at h
  by_cases hsign : cs.head? = some '-'
  · rw [if_pos hsign] at h
    obtain ⟨intDs, fracDs, expW, hv⟩ := readNumberFrom_eq_valueOfDigits h
    rw [hv]
    exact valueOfDigits_wf _ _ _ _
  · rw [if_neg hsign] at h
    obtain ⟨intDs, fracDs, expW, hv⟩ := readNumberFrom_eq_valueOfDigits h
    rw [hv]
    exact valueOfDigits_wf _ _ _ _

/-! ## The three printed shapes -/

/-- Shape one: the exponent is not negative. The text is the
    digits, then zero padding, with no point. Reading it folds
    the padding into the significand, and the strip moves it
    back into the exponent. -/
theorem readFrom_padded {neg : Bool} {dsAll : List Nat} {sig k : Nat} {expT : Int}
    (hb : ∀ x ∈ dsAll, x < 10)
    (hdsig : natOfDigits dsAll = sig) (hsmod : sig % 10 ≠ 0)
    (hhead : ∃ d ds', dsAll = d :: ds' ∧ d ≠ 0)
    (hkey : ((k : Nat) : Int) = expT) :
    readNumberFrom neg (digitChars dsAll ++ List.replicate k '0') =
      some ⟨neg, sig, expT⟩ := by
  have hbnds : ∀ x ∈ dsAll ++ List.replicate k 0, x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact hb x hx
    · have hx0 : x = 0 := (List.mem_replicate.mp hx).2
      omega
  obtain ⟨d, ds', hds, hd0⟩ := hhead
  have hhead' : ∃ d0 ds0, dsAll ++ List.replicate k 0 = d0 :: ds0 ∧ d0 ≠ 0 :=
    ⟨d, ds' ++ List.replicate k 0, by rw [hds, List.cons_append], hd0⟩
  have hInt : parseIntPart (digitChars (dsAll ++ List.replicate k 0) ++ []) =
      some (digitChars (dsAll ++ List.replicate k 0), []) :=
    parseIntPart_digitChars hhead' hbnds (fun c hc => by simp at hc)
  have hbody : digitChars dsAll ++ List.replicate k '0' =
      digitChars (dsAll ++ List.replicate k 0) := by
    rw [digitChars_append, digitChars_replicate_zero]
  rw [hbody, ← List.append_nil (digitChars (dsAll ++ List.replicate k 0))]
  have hFrom : readNumberFrom neg (digitChars (dsAll ++ List.replicate k 0) ++ []) =
      some (valueOfDigits neg
        ((digitChars (dsAll ++ List.replicate k 0)).map digitVal) [] 0) :=
    readNumberFrom_eq hInt (rfl : parseFracOpt [] = some ([], []))
      (rfl : parseExpOpt [] = some ([], []))
  rw [map_digitVal_digitChars hbnds] at hFrom
  have hN : natOfDigits ((dsAll ++ List.replicate k 0) ++ []) = sig * 10 ^ k := by
    rw [List.append_nil, natOfDigits_append, hdsig,
      natOfDigits_replicate_zero, List.length_replicate]
    simp
  have hval : valueOfDigits neg (dsAll ++ List.replicate k 0) [] 0 =
      ⟨neg, sig, expT⟩ := by
    rw [valueOfDigits_strip hsmod hN]
    congr 1
    have hlen : ((List.length ([] : List Nat) : Nat) : Int) = 0 := rfl
    omega
  exact hFrom.trans (congrArg some hval)

/-- Shape two: the point falls inside the digits. The text is
    some digits, a point, and the rest of the digits. Reading
    it joins the two runs back into the significand, and the
    fraction length restores the exponent. -/
theorem readFrom_pointInside {neg : Bool} {dsAll : List Nat} {sig pN : Nat}
    {expT : Int}
    (hb : ∀ x ∈ dsAll, x < 10)
    (hdsig : natOfDigits dsAll = sig) (hsmod : sig % 10 ≠ 0)
    (hhead : ∃ d ds', dsAll = d :: ds' ∧ d ≠ 0)
    (hpNpos : 0 < pN) (hpNlt : pN < dsAll.length)
    (hkey : ((pN : Nat) : Int) = (dsAll.length : Int) + expT) :
    readNumberFrom neg
      (digitChars (List.take pN dsAll) ++ '.' :: digitChars (List.drop pN dsAll)) =
      some ⟨neg, sig, expT⟩ := by
  have hbT : ∀ x ∈ List.take pN dsAll, x < 10 :=
    fun x hx => hb x (List.mem_of_mem_take hx)
  have hbD : ∀ x ∈ List.drop pN dsAll, x < 10 :=
    fun x hx => hb x (List.mem_of_mem_drop hx)
  obtain ⟨d, ds', hds, hd0⟩ := hhead
  obtain ⟨q, hq⟩ : ∃ q, pN = q + 1 := ⟨pN - 1, by omega⟩
  have htake : List.take pN dsAll = d :: List.take q ds' := by
    simp [hq, hds]
  have hhead' : ∃ d0 ds0, List.take pN dsAll = d0 :: ds0 ∧ d0 ≠ 0 :=
    ⟨d, List.take q ds', htake, hd0⟩
  have hInt : parseIntPart
      (digitChars (List.take pN dsAll) ++ '.' :: digitChars (List.drop pN dsAll)) =
      some (digitChars (List.take pN dsAll),
        '.' :: digitChars (List.drop pN dsAll)) :=
    parseIntPart_digitChars hhead' hbT (fun c hc => by
      have hcc : ('.' : Char) = c := Option.some.inj hc
      rw [← hcc]
      decide)
  have hdropne : List.drop pN dsAll ≠ [] := by
    intro hcon
    have hlen : (List.drop pN dsAll).length = 0 := by rw [hcon]; rfl
    rw [List.length_drop] at hlen
    omega
  obtain ⟨d', ds'', hdrop⟩ : ∃ d' ds'', List.drop pN dsAll = d' :: ds'' :=
    List.exists_cons_of_ne_nil hdropne
  have hFrac : parseFracOpt ('.' :: digitChars (List.drop pN dsAll)) =
      some ('.' :: digitChars (List.drop pN dsAll), []) :=
    parseFracOpt_digitChars hbD hdrop
  have hFrom : readNumberFrom neg
      (digitChars (List.take pN dsAll) ++ '.' :: digitChars (List.drop pN dsAll)) =
      some (valueOfDigits neg ((digitChars (List.take pN dsAll)).map digitVal)
        ((digitChars (List.drop pN dsAll)).map digitVal) 0) :=
    readNumberFrom_eq hInt hFrac (rfl : parseExpOpt [] = some ([], []))
  rw [map_digitVal_digitChars hbT, map_digitVal_digitChars hbD] at hFrom
  have hN : natOfDigits (List.take pN dsAll ++ List.drop pN dsAll) =
      sig * 10 ^ 0 := by
    rw [List.take_append_drop, hdsig]
    simp
  have hval : valueOfDigits neg (List.take pN dsAll) (List.drop pN dsAll) 0 =
      ⟨neg, sig, expT⟩ := by
    rw [valueOfDigits_strip hsmod hN]
    congr 1
    have hlen : (List.drop pN dsAll).length = dsAll.length - pN :=
      List.length_drop
    omega
  exact hFrom.trans (congrArg some hval)

/-- Shape three: the point falls before the digits. The text
    is a `0`, a point, zero padding, and the digits. Reading
    it folds the leading zeros away, and the fraction length
    restores the exponent. -/
theorem readFrom_pointBefore {neg : Bool} {dsAll : List Nat} {sig k : Nat}
    {expT : Int}
    (hb : ∀ x ∈ dsAll, x < 10)
    (hdsig : natOfDigits dsAll = sig) (hsmod : sig % 10 ≠ 0)
    (hhead : ∃ d ds', dsAll = d :: ds' ∧ d ≠ 0)
    (hkey : ((k : Nat) : Int) + (dsAll.length : Int) = -expT) :
    readNumberFrom neg
      (['0', '.'] ++ List.replicate k '0' ++ digitChars dsAll) =
      some ⟨neg, sig, expT⟩ := by
  have hbF : ∀ x ∈ List.replicate k 0 ++ dsAll, x < 10 := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · have hx0 : x = 0 := (List.mem_replicate.mp hx).2
      omega
    · exact hb x hx
  have hInt : parseIntPart
      (['0', '.'] ++ List.replicate k '0' ++ digitChars dsAll) =
      some (['0'], '.' :: (List.replicate k '0' ++ digitChars dsAll)) := by
    show parseIntPart ('0' :: '.' :: (List.replicate k '0' ++ digitChars dsAll)) = _
    unfold parseIntPart
    dsimp only
    rw [if_pos rfl]
  have hform : '.' :: (List.replicate k '0' ++ digitChars dsAll) =
      '.' :: digitChars (List.replicate k 0 ++ dsAll) := by
    rw [← digitChars_replicate_zero, ← digitChars_append]
  obtain ⟨d0, ds0, hcons⟩ :
      ∃ d0 ds0, List.replicate k 0 ++ dsAll = d0 :: ds0 := by
    cases k with
    | zero =>
      obtain ⟨d, ds', hds, -⟩ := hhead
      exact ⟨d, ds', hds⟩
    | succ k =>
      exact ⟨0, List.replicate k 0 ++ dsAll, by
        rw [List.replicate_succ, List.cons_append]⟩
  have hFrac : parseFracOpt ('.' :: (List.replicate k '0' ++ digitChars dsAll)) =
      some ('.' :: digitChars (List.replicate k 0 ++ dsAll), []) := by
    rw [hform]
    exact parseFracOpt_digitChars hbF hcons
  have hFrom : readNumberFrom neg
      (['0', '.'] ++ List.replicate k '0' ++ digitChars dsAll) =
      some (valueOfDigits neg ([0] : List Nat)
        ((digitChars (List.replicate k 0 ++ dsAll)).map digitVal) 0) :=
    readNumberFrom_eq hInt hFrac (rfl : parseExpOpt [] = some ([], []))
  rw [map_digitVal_digitChars hbF] at hFrom
  have hN : natOfDigits ([0] ++ (List.replicate k 0 ++ dsAll)) = sig * 10 ^ 0 := by
    rw [natOfDigits_append, natOfDigits_singleton, natOfDigits_append,
      natOfDigits_replicate_zero, hdsig]
    simp
  have hval : valueOfDigits neg [0] (List.replicate k 0 ++ dsAll) 0 =
      ⟨neg, sig, expT⟩ := by
    rw [valueOfDigits_strip hsmod hN]
    congr 1
    have hlen : (List.replicate k 0 ++ dsAll).length = k + dsAll.length := by
      rw [List.length_append, List.length_replicate]
    omega
  exact hFrom.trans (congrArg some hval)

/-! ## The round trip -/

/-- The round trip for the value layer: reading the printed
    form of a well formed value gives the value back. The
    printed form has one of the three shapes above, or is
    the single `0` of the canonical zero. No bound on the
    value is needed: the digits and the padding are finite
    for every held value, so the printed text is finite and
    the reader takes it whole. -/
theorem read_print {v : DecVal} (hv : WFVal v) :
    readNumber (printVal v) = some v := by
  obtain ⟨neg, sig, exp⟩ := v
  have hv' : (sig = 0 ∧ neg = false ∧ exp = 0) ∨
      (sig ≠ 0 ∧ sig % 10 ≠ 0) := hv
  rcases hv' with ⟨hsig, hneg, hexp⟩ | ⟨hsig, hsmod⟩
  · subst hsig
    subst hneg
    subst hexp
    have hprint : printVal ⟨false, 0, 0⟩ = ['0'] := rfl
    rw [hprint]
    decide
  · have hsigpos : 0 < sig := Nat.pos_of_ne_zero hsig
    obtain ⟨d, ds', hds, hd0, hd10⟩ := digitsOf_cons hsigpos
    have hb : ∀ x ∈ digitsOf sig, x < 10 := digitsOf_lt sig
    have hdsig : natOfDigits (digitsOf sig) = sig := natOfDigits_digitsOf sig
    have hhead : ∃ d0 ds0, digitsOf sig = d0 :: ds0 ∧ d0 ≠ 0 :=
      ⟨d, ds', hds, hd0⟩
    by_cases hexpA : exp ≥ 0
    · have hkey : readNumberFrom neg
          (digitChars (digitsOf sig) ++ List.replicate exp.toNat '0') =
          some ⟨neg, sig, exp⟩ :=
        readFrom_padded hb hdsig hsmod hhead (Int.toNat_of_nonneg hexpA)
      have hprint : printVal ⟨neg, sig, exp⟩ =
          if neg then '-' :: (digitChars (digitsOf sig) ++
              List.replicate exp.toNat '0')
          else digitChars (digitsOf sig) ++ List.replicate exp.toNat '0' := by
        unfold printVal
        dsimp only
        rw [if_neg hsig, if_pos hexpA]
      rw [hprint]
      have hBhead : (digitChars (digitsOf sig) ++
          List.replicate exp.toNat '0').head? = some (hexDigit d) := by
        rw [hds]
        rfl
      cases neg with
      | true =>
        rw [if_pos rfl]
        exact hkey
      | false =>
        rw [if_neg (by decide : ¬ ((false : Bool) = true))]
        have hheadne : ¬ ((digitChars (digitsOf sig) ++
            List.replicate exp.toNat '0').head? = some '-') := by
          rw [hBhead]
          intro hcon
          exact hexDigit_ne_minus ⟨d, hd10⟩ (Option.some.inj hcon)
        have hread : readNumber (digitChars (digitsOf sig) ++
            List.replicate exp.toNat '0') =
            readNumberFrom false (digitChars (digitsOf sig) ++
              List.replicate exp.toNat '0') := by
          unfold readNumber
          rw [if_neg hheadne]
        rw [hread]
        exact hkey
    · have hexp : exp < 0 := by omega
      by_cases hp : (digitsOf sig).length + exp > 0
      · have hpNcast : ((((digitsOf sig).length + exp).toNat : Nat) : Int) =
            (digitsOf sig).length + exp :=
          Int.toNat_of_nonneg (by omega)
        have hpNpos : 0 < ((digitsOf sig).length + exp).toNat := by omega
        have hpNlt : ((digitsOf sig).length + exp).toNat <
            (digitsOf sig).length := by omega
        have hkey : readNumberFrom neg
            (digitChars (List.take ((digitsOf sig).length + exp).toNat
                (digitsOf sig)) ++ '.' ::
              digitChars (List.drop ((digitsOf sig).length + exp).toNat
                (digitsOf sig))) =
            some ⟨neg, sig, exp⟩ :=
          readFrom_pointInside hb hdsig hsmod hhead hpNpos hpNlt hpNcast
        have hprint : printVal ⟨neg, sig, exp⟩ =
            if neg then '-' :: (digitChars
                (List.take ((digitsOf sig).length + exp).toNat (digitsOf sig)) ++
                '.' :: digitChars
                  (List.drop ((digitsOf sig).length + exp).toNat (digitsOf sig)))
            else digitChars
                (List.take ((digitsOf sig).length + exp).toNat (digitsOf sig)) ++
                '.' :: digitChars
                  (List.drop ((digitsOf sig).length + exp).toNat
                    (digitsOf sig)) := by
          unfold printVal
          dsimp only
          rw [if_neg hsig, if_neg hexpA, if_pos hp]
        rw [hprint]
        have htake : List.take ((digitsOf sig).length + exp).toNat
            (digitsOf sig) = d :: List.take
              (((digitsOf sig).length + exp).toNat - 1) ds' := by
          cases hpp : ((digitsOf sig).length + exp).toNat with
          | zero => exact absurd hpp (Nat.pos_iff_ne_zero.mp hpNpos)
          | succ q => simp [hds]
        have hBhead : (digitChars
            (List.take ((digitsOf sig).length + exp).toNat (digitsOf sig)) ++
            '.' :: digitChars
              (List.drop ((digitsOf sig).length + exp).toNat
                (digitsOf sig))).head? = some (hexDigit d) := by
          rw [htake]
          rfl
        cases neg with
        | true =>
          rw [if_pos rfl]
          exact hkey
        | false =>
          rw [if_neg (by decide : ¬ ((false : Bool) = true))]
          have hheadne : ¬ ((digitChars
              (List.take ((digitsOf sig).length + exp).toNat (digitsOf sig)) ++
              '.' :: digitChars
                (List.drop ((digitsOf sig).length + exp).toNat
                  (digitsOf sig))).head? = some '-') := by
            rw [hBhead]
            intro hcon
            exact hexDigit_ne_minus ⟨d, hd10⟩ (Option.some.inj hcon)
          have hread : readNumber (digitChars
              (List.take ((digitsOf sig).length + exp).toNat (digitsOf sig)) ++
              '.' :: digitChars
                (List.drop ((digitsOf sig).length + exp).toNat
                  (digitsOf sig))) =
              readNumberFrom false (digitChars
                (List.take ((digitsOf sig).length + exp).toNat (digitsOf sig)) ++
                '.' :: digitChars
                  (List.drop ((digitsOf sig).length + exp).toNat
                    (digitsOf sig))) := by
            unfold readNumber
            rw [if_neg hheadne]
          rw [hread]
          exact hkey
      · have hkcast : (((-((digitsOf sig).length + exp)).toNat : Nat) : Int) =
            -((digitsOf sig).length + exp) :=
          Int.toNat_of_nonneg (by omega)
        have hkey : readNumberFrom neg
            (['0', '.'] ++
              List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
              digitChars (digitsOf sig)) =
            some ⟨neg, sig, exp⟩ :=
          readFrom_pointBefore hb hdsig hsmod hhead (by omega)
        have hprint : printVal ⟨neg, sig, exp⟩ =
            if neg then '-' :: (['0', '.'] ++
                List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
                digitChars (digitsOf sig))
            else ['0', '.'] ++
              List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
              digitChars (digitsOf sig) := by
          unfold printVal
          dsimp only
          rw [if_neg hsig, if_neg hexpA, if_neg hp]
        rw [hprint]
        cases neg with
        | true =>
          rw [if_pos rfl]
          exact hkey
        | false =>
          rw [if_neg (by decide : ¬ ((false : Bool) = true))]
          have hhead0 : ((['0', '.'] ++
              List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
              digitChars (digitsOf sig)).head? = some '0') := rfl
          have hheadne : ¬ ((['0', '.'] ++
              List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
              digitChars (digitsOf sig)).head? = some '-') := by
            rw [hhead0]
            decide
          have hread : readNumber (['0', '.'] ++
              List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
              digitChars (digitsOf sig)) =
              readNumberFrom false (['0', '.'] ++
                List.replicate (-((digitsOf sig).length + exp)).toNat '0' ++
                digitChars (digitsOf sig)) := by
            unfold readNumber
            rw [if_neg hheadne]
          rw [hread]
          exact hkey

/-- The canonical text of a text's value re-reads to that
    value: the value the reader returns is well formed, so
    the round trip applies to it. -/
theorem read_print_of_read {cs : List Char} {v : DecVal}
    (h : readNumber cs = some v) : readNumber (printVal v) = some v :=
  read_print (readNumber_wf h)

/-- Two texts with the same value have the same canonical
    text: the canonical text is built from the value alone. -/
theorem canonical_eq_of_value_eq {t1 t2 : List Char} {v : DecVal}
    (h1 : readNumber t1 = some v) (h2 : readNumber t2 = some v) :
    canonicalText t1 = canonicalText t2 := by
  unfold canonicalText
  rw [h1, h2]

end Json.NumProofs

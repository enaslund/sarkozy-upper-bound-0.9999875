module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Prime.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Tactic.NormNum

@[expose] public section

/-!
# The parameters and prime ranges of the construction (`def:record:parameters`)

`paper/sections/18_design.tex`, `def:record:parameters` (c)–(f), `def:construction` (a), with the
piece endpoints of `def:record:exact-blocks` (a) (`paper/sections/20_middle_reference.tex`) and
the bands of `def:record:upper-bands` (a) (`paper/sections/25_upper_reference.tex`).

What is fixed here, as exact natural numbers or rationals:
* the thresholds `Q₃ = 19 951 586`, `P₃ = 167·2⁴⁰`, `P₄ = 2⁵¹²`, `P₅ = 2⁶⁵⁵³⁶`, the number of
  digit pairs `𝔪 = 8192` (prefix exponent `e_p = 2𝔪`), `m_ext = 64`, the middle budget
  `L = 570`, the local cap `L_loc = 585`, the integer budget `𝔲_* = 2⁴⁰ L`, the
  Chebyshev threshold `X_Ch = 4 800 162 890`;
* the five prime ranges (prefix, small modulus, middle, upper, tail) as predicates; every prime
  lies in exactly one of them (`prime_range_cover`, `prime_range_disjoint`);
* the small modulus `M₀ = 2^{2m_ext+1} ∏_{3 ≤ p < Q₃, p ≡ 3 (4)} p^{2m_ext}`; it is coprime to
  every prime of the other four ranges (`coprime_M0`);
* the 34 endpoints of the 33 middle pieces (strictly increasing, from `Q₃` to `P₃`), and which
  root (`def:positive-root`) each piece uses (`pieceRoot`), with the seven tilt parameters of
  `def:record:parameters` (f);
* the 310 upper bands (consecutive, from `P₃` to `P₄`).

Interpretation choices.
* The exponents `a` and `θ` of `def:record:parameters` (a) are not fixed here: the project's
  formal exponent is set in `Sarkozy.Parameters`, and nothing in this file depends on it
  (the worker guide forbids hard-coding the old exponent).
* The number of intervals `K` of (b) is likewise not repeated (it is `Sarkozy.blockScale`).
* Prime ranges are stated for all natural numbers; the predicates include primality.
-/

namespace Sarkozy.PartV

open Finset

/-! ## Thresholds (`def:record:parameters`(c),(d)) -/

/-- `Q₃ = 19 951 586`, the start of the middle range (`def:record:parameters`(c)). -/
def Q3 : ℕ := 19951586

/-- `P₃ = 167·2⁴⁰`, the end of the middle range and start of the upper range. -/
def P3 : ℕ := 167 * 2 ^ 40

/-- `P₄ = 2⁵¹²`, the end of the prefix and of the upper range, the start of the tail. -/
def P4 : ℕ := 2 ^ 512

/-- `P₅ = 2⁶⁵⁵³⁶`, the threshold of the mixing condition (R4) (`lem:record:tail-mixing`). -/
def P5 : ℕ := 2 ^ 65536

/-- `m_ext = 64`: the exponent of the small modulus is `2 m_ext`. -/
def mExt : ℕ := 64

/-- The number of digit pairs of the prefix, `𝔪 = 8192`. -/
def digitPairs : ℕ := 8192

/-- The prefix exponent `e_p = 2𝔪 = 16384` (`def:record:parameters`(c), prefix). -/
def prefixExponent : ℕ := 2 * digitPairs

/-- The middle block budget `L = 570` (`def:record:parameters`(d)). -/
def middleBudget : ℕ := 570

/-- The local cap `L_loc = 585` at which the middle local laws are evaluated. -/
def localCap : ℕ := 585

/-- The integer budget `𝔲_* = 2⁴⁰ L = 626 721 627 832 320` (`def:record:exact-blocks`). -/
def integerBudget : ℕ := 2 ^ 40 * middleBudget

theorem integerBudget_eq : integerBudget = 626721627832320 := by decide

/-- The Chebyshev threshold `X_Ch = 4 800 162 890` (`subsec:record:middle_blocks`). -/
def chebyshevThreshold : ℕ := 4800162890

/-- The upper block length `L_u = 50000/27` (`def:record:parameters`(d)). -/
def upperLength : ℚ := 50000 / 27

theorem Q3_lt_P3 : Q3 < P3 := by norm_num [Q3, P3]

theorem P3_lt_P4 : P3 < P4 := by decide +kernel

/-! ## The prime ranges (`def:record:parameters`(c), `tab:ranges`) -/

/-- Prefix: the primes `p ≡ 1 (mod 4)` below `P₄`. -/
def IsPrefixPrime (p : ℕ) : Prop := p.Prime ∧ p % 4 = 1 ∧ p < P4

/-- Small modulus: `2` and the primes `p ≡ 3 (mod 4)` below `Q₃`; they divide `M₀` and are not
coordinates of the label group. -/
def IsSmallModulusPrime (p : ℕ) : Prop := p.Prime ∧ (p = 2 ∨ (p % 4 = 3 ∧ p < Q3))

/-- Middle: the primes `p ≡ 3 (mod 4)` in `[Q₃, P₃)`. -/
def IsMiddlePrime (p : ℕ) : Prop := p.Prime ∧ p % 4 = 3 ∧ Q3 ≤ p ∧ p < P3

/-- Upper: the primes `p ≡ 3 (mod 4)` in `[P₃, P₄)`. -/
def IsUpperPrime (p : ℕ) : Prop := p.Prime ∧ p % 4 = 3 ∧ P3 ≤ p ∧ p < P4

/-- Tail: every prime `p ≥ P₄`, of either class. -/
def IsTailPrime (p : ℕ) : Prop := p.Prime ∧ P4 ≤ p

theorem prime_mod_four {p : ℕ} (hp : p.Prime) : p = 2 ∨ p % 4 = 1 ∨ p % 4 = 3 := by
  rcases hp.eq_two_or_odd with h | h
  · exact Or.inl h
  · omega

/-- **Every prime lies in one of the five ranges** (`def:record:parameters`(c), last sentence:
every other prime divides `M₀`). -/
theorem prime_range_cover {p : ℕ} (hp : p.Prime) :
    IsSmallModulusPrime p ∨ IsPrefixPrime p ∨ IsMiddlePrime p ∨ IsUpperPrime p ∨
      IsTailPrime p := by
  unfold IsSmallModulusPrime IsPrefixPrime IsMiddlePrime IsUpperPrime IsTailPrime
  have h4 := prime_mod_four hp
  have hQP : Q3 < P3 := Q3_lt_P3
  have hPP : P3 < P4 := P3_lt_P4
  by_cases ht : P4 ≤ p
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨hp, ht⟩)))
  · rcases h4 with h | h | h
    · exact Or.inl ⟨hp, Or.inl h⟩
    · exact Or.inr (Or.inl ⟨hp, h, by omega⟩)
    · by_cases hq : p < Q3
      · exact Or.inl ⟨hp, Or.inr ⟨h, hq⟩⟩
      · by_cases hm : p < P3
        · exact Or.inr (Or.inr (Or.inl ⟨hp, h, by omega, hm⟩))
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hp, h, by omega, by omega⟩)))

/-- **The five ranges are pairwise disjoint.** -/
theorem prime_range_disjoint (p : ℕ) :
    (IsSmallModulusPrime p → ¬ IsPrefixPrime p ∧ ¬ IsMiddlePrime p ∧ ¬ IsUpperPrime p ∧
      ¬ IsTailPrime p) ∧
    (IsPrefixPrime p → ¬ IsMiddlePrime p ∧ ¬ IsUpperPrime p ∧ ¬ IsTailPrime p) ∧
    (IsMiddlePrime p → ¬ IsUpperPrime p ∧ ¬ IsTailPrime p) ∧
    (IsUpperPrime p → ¬ IsTailPrime p) := by
  unfold IsSmallModulusPrime IsPrefixPrime IsMiddlePrime IsUpperPrime IsTailPrime
  have hQP : Q3 < P3 := Q3_lt_P3
  have hPP : P3 < P4 := P3_lt_P4
  have hQ : 2 < Q3 := by norm_num [Q3]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨-, h⟩
    refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro ⟨-, h'⟩ <;> omega
  · rintro ⟨-, h, h'⟩
    refine ⟨?_, ?_, ?_⟩ <;> rintro ⟨-, h''⟩ <;> omega
  · rintro ⟨-, h, h'⟩
    refine ⟨?_, ?_⟩ <;> rintro ⟨-, h''⟩ <;> omega
  · rintro ⟨-, h, h'⟩ ⟨-, h''⟩
    omega

/-! ## The small modulus `M₀` (`def:record:parameters`(c), `def:hyb:coupled`) -/

/-- The odd primes of the small modulus: `3 ≤ p < Q₃`, `p ≡ 3 (mod 4)`. -/
def smallModulusOddPrimes : Finset ℕ := (range Q3).filter fun p => p.Prime ∧ p % 4 = 3

/-- `2^{2m_ext+1} ∏_{q ∈ s} q^{2m_ext}` for a finite set `s` of odd primes. -/
def smallModulusOf (s : Finset ℕ) : ℕ := 2 ^ (2 * mExt + 1) * ∏ q ∈ s, q ^ (2 * mExt)

/-- **The small modulus** `M₀ = 2^{2m_ext+1} ∏_{3 ≤ p < Q₃, p ≡ 3 (4)} p^{2m_ext}`. -/
def M0 : ℕ := smallModulusOf smallModulusOddPrimes

theorem mem_smallModulusOddPrimes {p : ℕ} :
    p ∈ smallModulusOddPrimes ↔ p.Prime ∧ p % 4 = 3 ∧ p < Q3 := by
  unfold smallModulusOddPrimes
  rw [mem_filter, mem_range]
  tauto

theorem coprime_smallModulusOf {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) {s : Finset ℕ}
    (hs : ∀ q ∈ s, q.Prime) (hps : p ∉ s) : Nat.Coprime p (smallModulusOf s) := by
  unfold smallModulusOf
  exact Nat.Coprime.mul_right
    (Nat.Coprime.pow_right _ ((Nat.coprime_primes hp Nat.prime_two).mpr h2))
    (Nat.Coprime.prod_right fun q hq => Nat.Coprime.pow_right _
      ((Nat.coprime_primes hp (hs q hq)).mpr fun h => hps (h ▸ hq)))

theorem smallModulusOf_pos {s : Finset ℕ} (hs : ∀ q ∈ s, q.Prime) : 0 < smallModulusOf s := by
  unfold smallModulusOf
  exact Nat.mul_pos (Nat.pos_of_ne_zero (pow_ne_zero _ two_ne_zero))
    (prod_pos fun q hq => pow_pos (hs q hq).pos _)

theorem coprime_M0 {p : ℕ} (hp : p.Prime) (hs : ¬ IsSmallModulusPrime p) : Nat.Coprime p M0 :=
  coprime_smallModulusOf hp (fun h => hs ⟨hp, Or.inl h⟩)
    (fun _ hq => (mem_smallModulusOddPrimes.mp hq).1)
    (fun hq => hs ⟨hp, Or.inr ⟨(mem_smallModulusOddPrimes.mp hq).2.1,
      (mem_smallModulusOddPrimes.mp hq).2.2⟩⟩)

theorem M0_pos : 0 < M0 := smallModulusOf_pos fun _ hq => (mem_smallModulusOddPrimes.mp hq).1

/-! ## The middle pieces (`def:record:exact-blocks`(a), `tab:record:middle-pieces`) -/

/-- The 34 endpoints `X₁ < X₂ < ⋯ < X₃₄` of the middle pieces. -/
def pieceEnds : List ℕ :=
  [19951586, 21757358, 23726568, 25429506, 25874006, 28215802,
    2 ^ 25, 39903170, 47453134, 56431604, 2 ^ 26, 79806340, 94906266,
    112863208, 2 ^ 27, 159612678, 189812532, 225726414, 2 ^ 28,
    319225356, 379625064, 451452826, 2 ^ 29, 638450710, 759250126,
    902905652, 2 ^ 30, 2 ^ 31, 2 ^ 32, 2 ^ 34, 2 ^ 36, 2 ^ 40, 2 ^ 45, 167 * 2 ^ 40]

/-- The 33 middle pieces `[X_i, X_{i+1})`. -/
def pieces : List (ℕ × ℕ) := pieceEnds.zip pieceEnds.tail

theorem pieceEnds_length : pieceEnds.length = 34 := by decide

theorem pieces_length : pieces.length = 33 := by decide

/-- The pieces are nonempty intervals: `X_i < X_{i+1}`. -/
theorem pieces_lt : pieces.all (fun xy => decide (xy.1 < xy.2)) = true := by decide +kernel

/-- The pieces start at `Q₃` and end at `P₃`. -/
theorem pieceEnds_head_last :
    pieceEnds.head? = some Q3 ∧ pieceEnds.getLast? = some P3 := by decide +kernel

/-- The start `X_i` of the piece `i` (`0 ≤ i < 33`, numbered from `0`). -/
def pieceStart (i : Fin 33) : ℕ := pieceEnds.getD i.val 0

/-- The end `X_{i+1}` of the piece `i`. -/
def pieceStop (i : Fin 33) : ℕ := pieceEnds.getD (i.val + 1) 0

theorem pieceStart_lt_pieceStop : ∀ i : Fin 33, pieceStart i < pieceStop i := by
  unfold pieceStart pieceStop pieceEnds
  decide +kernel

theorem pieceStop_eq_pieceStart : ∀ i : Fin 32, pieceStop i.castSucc = pieceStart i.succ := by
  intro i
  rfl

/-- The kind of two-layer root a middle piece uses (`def:record:parameters`(f),
`def:positive-root`): the uniform law, the individual-square positive root with parameter
`u`, or the coherent root with parameter `u` and floor `η` (dictionary `𝒟₃₉`). -/
inductive RootKind where
  | uniform
  | individualSquare (u : ℚ)
  | coherent (u η : ℚ)
  deriving DecidableEq

/-- **The root of each middle piece** (`def:record:parameters`(f)): uniform below `2³⁰`; on the
pieces from `2³⁰`, `2³¹`, `2³²`, `2³⁴`, `2³⁶`, `2⁴⁰` the individual-square root with
`u = 711/4096, 1021/4096, 1455/4096, 833/1024, 3851/4096, 4049/4096`; on `[2⁴⁵, P₃)` the
coherent root with `u = 67/40` and floor `1/100`. Pieces are numbered from `0`. -/
def pieceRoot (i : Fin 33) : RootKind :=
  if i.val < 26 then .uniform
  else if i.val = 26 then .individualSquare (711 / 4096)
  else if i.val = 27 then .individualSquare (1021 / 4096)
  else if i.val = 28 then .individualSquare (1455 / 4096)
  else if i.val = 29 then .individualSquare (833 / 1024)
  else if i.val = 30 then .individualSquare (3851 / 4096)
  else if i.val = 31 then .individualSquare (4049 / 4096)
  else .coherent (67 / 40) (1 / 100)

/-- The seven tilted pieces start at `2³⁰, 2³¹, 2³², 2³⁴, 2³⁶, 2⁴⁰, 2⁴⁵`, and every piece below
`2³⁰` uses the uniform root. -/
theorem pieceRoot_tilted_starts :
    pieceStart 26 = 2 ^ 30 ∧ pieceStart 27 = 2 ^ 31 ∧ pieceStart 28 = 2 ^ 32 ∧
      pieceStart 29 = 2 ^ 34 ∧ pieceStart 30 = 2 ^ 36 ∧ pieceStart 31 = 2 ^ 40 ∧
      pieceStart 32 = 2 ^ 45 := by
  unfold pieceStart pieceEnds
  decide +kernel

theorem pieceRoot_uniform_iff (i : Fin 33) : pieceRoot i = .uniform ↔ pieceStart i < 2 ^ 30 := by
  revert i
  unfold pieceRoot pieceStart pieceEnds
  decide +kernel

/-! ## The upper bands (`def:record:upper-bands`(a)) -/

/-- The first band `[167·2⁴⁰, 168·2⁴⁰)`. -/
def bandsA : List (ℕ × ℕ) := [(167 * 2 ^ 40, 168 * 2 ^ 40)]

/-- The 44 bands `[j 2⁴¹, (j+1) 2⁴¹)`, `84 ≤ j < 128`. -/
def bandsB : List (ℕ × ℕ) := (List.range 44).map fun i => ((84 + i) * 2 ^ 41, (85 + i) * 2 ^ 41)

/-- The `4 · 64` bands `[2^b(1 + j/64), 2^b(1 + (j+1)/64))`, `48 ≤ b ≤ 51`, `0 ≤ j < 64`, written
as `[2^{b-6}(64 + j), 2^{b-6}(65 + j))`. -/
def bandsC : List (ℕ × ℕ) :=
  (List.range 4).flatMap fun c => (List.range 64).map fun j =>
    (2 ^ (42 + c) * (64 + j), 2 ^ (42 + c) * (65 + j))

/-- The exponents `52, 53, …, 58, 60, 64, 512` of the last nine bands. -/
def bandsDExponents : List ℕ := [52, 53, 54, 55, 56, 57, 58, 60, 64, 512]

/-- The nine bands `[2^b, 2^{b'})` for consecutive `b < b'` in `{52, …, 58, 60, 64, 512}`. -/
def bandsD : List (ℕ × ℕ) :=
  (bandsDExponents.zip bandsDExponents.tail).map fun bb => (2 ^ bb.1, 2 ^ bb.2)

/-- **The 310 upper bands** in increasing order. -/
def upperBands : List (ℕ × ℕ) := bandsA ++ bandsB ++ bandsC ++ bandsD

theorem upperBands_length : upperBands.length = 310 := by decide +kernel

/-- **The bands partition `[P₃, P₄)`**: they are nonempty, consecutive (each ends where the next
starts), the first starts at `P₃` and the last ends at `P₄`. -/
theorem upperBands_tile :
    upperBands.all (fun xy => decide (xy.1 < xy.2)) = true ∧
      (upperBands.map Prod.snd).dropLast = (upperBands.map Prod.fst).tail ∧
      (upperBands.map Prod.fst).head? = some P3 ∧ (upperBands.map Prod.snd).getLast? = some P4 := by
  decide +kernel

end Sarkozy.PartV

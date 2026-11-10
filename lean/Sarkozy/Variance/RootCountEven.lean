module

public import Sarkozy.Labellings.SignedNbhd

/-!
# The even component of the root completion count (`eq:record:root-count`, part)

`paper/sections/22_variance.tex`, proof of `lem:record:root-marginal`, "Even component". Given a
half configuration `y`, the pair `(y_{4,0}, y_{4,1})` is an ordered distinct pair in the signed
neighbourhood of `(y_{0,0}, y_{0,1}, y_{2,0}, y_{2,1})` with the signs `(-1,-1,1,1)`, avoiding
`y_{1,0}, y_{1,1}`. By `lem:record:signed-nbhd` (`Labellings.signed_nbhd_bounds`, from H1) the
number of such pairs lies between `(p/16)²(1 - υ×)(1 - υ× - 16q)` and `(p/16)²(1 + υ₊)²`, with
`υ₊ = 11r + 6q`, `υ× = 11r + 102q`, `q = 1/p`, `r = p^{-1/2}` (`even_pairs_bounds`).

This is one step of `eq:record:root-count`. The odd component (the count `𝒵` and its
independence of `(y_{1,0}, y_{1,1})`), the probability bound `𝔞_p` and the union bound over the
six even labels are not formalized; `RootMarginal.lean` takes the full count as the hypothesis
`hcount`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.Labellings

namespace Sarkozy.Variance

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The even component of `eq:record:root-count`**: for four distinct labels `x`, signs `s`,
and at most two further excluded labels `K`, the ordered distinct pairs in the signed
neighbourhood outside `K` number at most `(p/16)²(1 + υ₊)²`, and at least
`(p/16)²(1 - υ×)(1 - υ× - 16q)` when the lower factor `1 - υ× - 16q` is nonnegative. -/
theorem even_pairs_bounds (hW : WeilBound F) (x : Fin 4 → F) (hx : Function.Injective x)
    (s : Fin 4 → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (K : Finset F) (hK : K.card ≤ 2) :
    let p : ℝ := Fintype.card F
    let r : ℝ := 1 / Real.sqrt p
    let T := (admissible x s (univ.image x)) \ K
    (T.offDiag.card : ℝ) ≤ (p / 16) ^ 2 * (1 + (11 * r + 6 / p)) ^ 2 ∧
      (0 ≤ 1 - (11 * r + 102 / p) - 16 / p →
        (p / 16) ^ 2 * ((1 - (11 * r + 102 / p)) * (1 - (11 * r + 102 / p) - 16 / p)) ≤
          T.offDiag.card) := by
  intro p r T
  obtain ⟨hup, -, hlow⟩ := signed_nbhd_bounds hW x hx s hs K
  have hp : (0 : ℝ) < p := by
    show (0 : ℝ) < (Fintype.card F : ℝ)
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card F)
  have hT : (T.card : ℝ) ≤ ((admissible x s (univ.image x)).card : ℝ) := by
    exact_mod_cast card_le_card sdiff_subset
  have hoff : (T.offDiag.card : ℝ) = (T.card : ℝ) * T.card - T.card := by
    rw [offDiag_card]
    have : T.card ≤ T.card * T.card := Nat.le_mul_self _
    push_cast [Nat.cast_sub this]
    ring
  have hn0 : (0 : ℝ) ≤ T.card := Nat.cast_nonneg _
  constructor
  · rw [hoff]
    have hup' : (T.card : ℝ) ≤ p / 16 * (1 + (11 * r + 6 / p)) := hT.trans hup
    have h0 : 0 ≤ p / 16 * (1 + (11 * r + 6 / p)) := hn0.trans hup'
    have : (T.card : ℝ) * T.card ≤ (p / 16 * (1 + (11 * r + 6 / p))) ^ 2 := by
      rw [sq]
      exact mul_le_mul hup' hup' hn0 h0
    nlinarith
  · intro hfac
    rw [hoff]
    have hK' : (16 * (K.card : ℝ)) / p ≤ 32 / p := by
      apply div_le_div_of_nonneg_right _ hp.le
      have : (K.card : ℝ) ≤ 2 := by exact_mod_cast hK
      linarith
    -- `n ≥ p/16 (1 - υ×)`
    have hA : p / 16 * (1 - (11 * r + 102 / p)) ≤ (T.card : ℝ) := by
      have h1 := hlow
      have e : p / 16 * (1 - (11 * r + 102 / p)) =
          p / 16 * (1 - (11 * r + 70 / p) - 32 / p) := by
        field_simp
        ring
      rw [e]
      refine le_trans ?_ h1
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith
    -- `n - 1 ≥ p/16 (1 - υ× - 16q)`
    have hB : p / 16 * (1 - (11 * r + 102 / p) - 16 / p) ≤ (T.card : ℝ) - 1 := by
      have e : p / 16 * (1 - (11 * r + 102 / p) - 16 / p) =
          p / 16 * (1 - (11 * r + 102 / p)) - 1 := by
        field_simp
      rw [e]
      linarith
    have hB0 : 0 ≤ p / 16 * (1 - (11 * r + 102 / p) - 16 / p) :=
      mul_nonneg (by positivity) hfac
    have hA0 : 0 ≤ p / 16 * (1 - (11 * r + 102 / p)) := by
      have : 0 ≤ 1 - (11 * r + 102 / p) := by
        have : 0 ≤ 16 / p := by positivity
        linarith
      exact mul_nonneg (by positivity) this
    have hprod := mul_le_mul hA hB hB0 hn0
    have e2 : (p / 16) ^ 2 * ((1 - (11 * r + 102 / p)) * (1 - (11 * r + 102 / p) - 16 / p)) =
        p / 16 * (1 - (11 * r + 102 / p)) * (p / 16 * (1 - (11 * r + 102 / p) - 16 / p)) := by
      ring
    rw [e2]
    nlinarith

end Sarkozy.Variance

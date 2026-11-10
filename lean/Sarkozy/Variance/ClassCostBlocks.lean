module

public import Sarkozy.Variance.BackgroundBlocks
public import Sarkozy.Variance.VarianceInterface

/-!
# The class cost with each block its own factor (`prop:background-variance`(a))

`paper/sections/22_variance.tex`, the last step of the proof of `prop:background-variance`(a)
(and of `lem:var-gain`(b)), with the selected set `X` as a set of factors.

* `class_cost_scalar`: the class-cost step for real numbers. For each selection `s` of a class
  `R`, let `I_s` be its term, `DN_s, JN_s` the energies of `Diag_X` and `J_X` with the bracket
  `Ñ` outside, and `JO_s` the energy of `J_X` with `O' = Ñ₀` outside. Suppose
  `|I_s| ≤ γ (DN_s - JN_s)`, `JN_s ≥ 0`, `DN_s ≤ (B + z₃) C_X Y`,
  `JN_s ≥ JO_s - (R_err + z₄) C_X Y`, and `avg_s JO_s ≥ (C_m b̃ - z_b) Y`. Then
  `∑_s |I_s| ≤ (B - [b̃ - R_*]_+ + z₃ + z₄ + z_b) ∑_s γ C_X Y`.
* `background_variance_class_cost_blocks`: the class of the two aligned matching assignments,
  `X` as factors. Here `|I_s| ≤ ∏γ_𝔅 (DN_s - JN_s)` is `abs_energy_le_variance_blocks`
  (`lem:record:variance-interface`(i) for products), `JN_s ≥ 0` is (E2), and the displayed bound
  is `background_variance_a_blocks`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

/-- **The class-cost step for real numbers.** -/
theorem class_cost_scalar {ι : Type*} (R : Finset ι) (hR : R.Nonempty) (I DN JN JO : ι → ℝ)
    {γ Yμ CX Cm bt zb z₃ z₄ Bf Rerr Rstar : ℝ} (hγ : 0 ≤ γ) (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX)
    (hCm : CX ≤ Cm) (hzb : 0 ≤ zb) (hz₄ : 0 ≤ z₄) (hR0 : 0 ≤ Rerr) (hRs : Rerr ≤ Rstar)
    (hI : ∀ s ∈ R, |I s| ≤ γ * (DN s - JN s)) (hJN0 : ∀ s ∈ R, 0 ≤ JN s)
    (hbound : (Cm * bt - zb) * Yμ ≤ (∑ s ∈ R, JO s) / R.card)
    (hDiagN : ∀ s ∈ R, DN s ≤ (Bf + z₃) * CX * Yμ)
    (hJN : ∀ s ∈ R, JO s - (Rerr + z₄) * CX * Yμ ≤ JN s) :
    ∑ s ∈ R, |I s| ≤ (Bf - max 0 (bt - Rstar) + (z₃ + z₄ + zb)) * (∑ _s ∈ R, γ * CX) * Yμ := by
  have hn : (0 : ℝ) < R.card := by exact_mod_cast hR.card_pos
  have hsumγ : ∑ _s ∈ R, γ * CX = R.card * (γ * CX) := by rw [sum_const, nsmul_eq_mul]
  rw [hsumγ]
  have h4 : 0 ≤ (R.card : ℝ) * (γ * CX) * Yμ :=
    mul_nonneg (mul_nonneg hn.le (mul_nonneg hγ (by linarith))) hY
  by_cases hg : 0 ≤ bt - Rstar
  · rw [max_eq_right hg]
    have hbt : 0 ≤ bt := by linarith
    have hb' : R.card * ((bt - zb) * CX * Yμ) ≤ ∑ s ∈ R, JO s := by
      have h1 := (le_div_iff₀ hn).mp hbound
      have h2 : (bt - zb) * CX * Yμ ≤ (Cm * bt - zb) * Yμ := by
        have e1 : CX * bt ≤ Cm * bt := mul_le_mul_of_nonneg_right hCm hbt
        have e2 : zb * Yμ ≤ zb * CX * Yμ := by
          have := mul_nonneg (mul_nonneg hzb hY) (sub_nonneg.mpr hCX)
          nlinarith
        nlinarith
      nlinarith
    have hle : ∀ s ∈ R, |I s| ≤
        γ * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ - JO s) := by
      intro s hs
      refine (hI s hs).trans ?_
      apply mul_le_mul_of_nonneg_left _ hγ
      linarith [hDiagN s hs, hJN s hs]
    have hsum := sum_le_sum hle
    rw [← mul_sum, sum_sub_distrib, sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    have h3 : γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) - ∑ s ∈ R, JO s) ≤
        γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
          R.card * ((bt - zb) * CX * Yμ)) :=
      mul_le_mul_of_nonneg_left (by linarith) hγ
    refine h3.trans ?_
    have h5 : γ * (R.card * ((Bf + z₃) * CX * Yμ + (Rerr + z₄) * CX * Yμ) -
          R.card * ((bt - zb) * CX * Yμ)) =
        (Bf - (bt - Rerr) + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ) := by ring
    rw [h5]
    calc (Bf - (bt - Rerr) + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ)
        ≤ (Bf - (bt - Rstar) + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ = (Bf - (bt - Rstar) + (z₃ + z₄ + zb)) * (R.card * (γ * CX)) * Yμ := by ring
  · push Not at hg
    rw [max_eq_left hg.le]
    have hle : ∀ s ∈ R, |I s| ≤ γ * ((Bf + z₃) * CX * Yμ) := by
      intro s hs
      refine (hI s hs).trans ?_
      apply mul_le_mul_of_nonneg_left _ hγ
      linarith [hDiagN s hs, hJN0 s hs]
    have hsum := sum_le_sum hle
    rw [sum_const, nsmul_eq_mul] at hsum
    refine hsum.trans ?_
    calc (R.card : ℝ) * (γ * ((Bf + z₃) * CX * Yμ)) = (Bf + z₃) * (R.card * (γ * CX) * Yμ) := by
          ring
      _ ≤ (Bf - 0 + (z₃ + z₄ + zb)) * (R.card * (γ * CX) * Yμ) :=
          mul_le_mul_of_nonneg_right (by linarith) h4
      _ = (Bf - 0 + (z₃ + z₄ + zb)) * (R.card * (γ * CX)) * Yμ := by ring

section Blocks

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`prop:background-variance`(a), the class cost, blocks as factors**: from the displayed
bound `½ ∑_s Y^{Ñ₀}[J_{X,s}] ≥ (C_m b̃ - z_b) Y` (`background_variance_a_blocks`, with `Ñ₀` the
exterior `O'`), `lem:record:variance-interface`(i) for products and its part (ii) (hypotheses
`hDiagN`, `hJN`), the two aligned matching selections, with block differences `ζ_{s,𝔅}` of
bilinear bounds `γ_𝔅`, satisfy
`|I_0| + |I_1| ≤ (B - [b̃ - R_*]_+ + z₃ + z₄ + z_b) · 2 (∏ γ_𝔅) C_X Y`. -/
theorem background_variance_class_cost_blocks (ι : ReflectionCut V)
    (N lam O' : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hXs : Xs.Nonempty)
    (hN : ∀ j, j ∉ Xs → ι.Bracket (N j) (lam j) (N j)) (F : (∀ b, X b) → ℝ)
    (m0 m1 : ∀ j, (ι.Half → X j) → ℝ) (hm0 : ∀ j ∈ Xs, ∀ x, 0 ≤ m0 j x)
    (hm1 : ∀ j ∈ Xs, ∀ x, 0 ≤ m1 j x) (γ : J → ℝ) (hγ : ∀ j ∈ Xs, 0 ≤ γ j)
    (ζ0 ζ1 : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ)
    (hζ0 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ, |ι.form (ζ0 j) G H| ≤
      γ j * Real.sqrt (ι.form (ι.diagonalLaw (m0 j) - indepLaw ι (m0 j)) G G) *
        Real.sqrt (ι.form (ι.diagonalLaw (m0 j) - indepLaw ι (m0 j)) H H))
    (hζ1 : ∀ j ∈ Xs, ∀ G H : (ι.Half → X j) → ℝ, |ι.form (ζ1 j) G H| ≤
      γ j * Real.sqrt (ι.form (ι.diagonalLaw (m1 j) - indepLaw ι (m1 j)) G G) *
        Real.sqrt (ι.form (ι.diagonalLaw (m1 j) - indepLaw ι (m1 j)) H H))
    {Yμ CX Cm bt zb z₃ z₄ Bf Rerr Rstar : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hCm : CX ≤ Cm)
    (hzb : 0 ≤ zb) (hz₄ : 0 ≤ z₄) (hR0 : 0 ≤ Rerr) (hRs : Rerr ≤ Rstar)
    (hbound : (Cm * bt - zb) * Yμ ≤
      (diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m0 b) else O' b) F +
        diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m1 b) else O' b) F) / 2)
    (hDiagN0 : diagonalIntegral (tensorLaw fun b => if b ∈ Xs then ι.diagonalLaw (m0 b) else N b)
      F ≤ (Bf + z₃) * CX * Yμ)
    (hDiagN1 : diagonalIntegral (tensorLaw fun b => if b ∈ Xs then ι.diagonalLaw (m1 b) else N b)
      F ≤ (Bf + z₃) * CX * Yμ)
    (hJN0 : diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m0 b) else O' b) F -
        (Rerr + z₄) * CX * Yμ ≤
      diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m0 b) else N b) F)
    (hJN1 : diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m1 b) else O' b) F -
        (Rerr + z₄) * CX * Yμ ≤
      diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m1 b) else N b) F) :
    |diagonalIntegral (tensorLaw fun b => if b ∈ Xs then ζ0 b else lam b) F| +
        |diagonalIntegral (tensorLaw fun b => if b ∈ Xs then ζ1 b else lam b) F| ≤
      (Bf - max 0 (bt - Rstar) + (z₃ + z₄ + zb)) *
        ((∏ j ∈ Xs, γ j) * CX + (∏ j ∈ Xs, γ j) * CX) * Yμ := by
  have hNpos : ∀ j, j ∉ Xs → ι.Positive (N j) := fun j hj => (hN j hj).left_positive
  let m : Bool → ∀ j, (ι.Half → X j) → ℝ := fun s => if s then m1 else m0
  let ζ : Bool → ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ := fun s => if s then ζ1 else ζ0
  have hm : ∀ s : Bool, ∀ j ∈ Xs, ∀ x, 0 ≤ m s j x := by
    intro s
    cases s
    · exact hm0
    · exact hm1
  have hJpos : ∀ s : Bool, 0 ≤ diagonalIntegral
      (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m s b) else N b) F := by
    intro s
    apply energy_nonneg_of_positive ι
    intro j
    by_cases hj : j ∈ Xs
    · simp only [hj, ↓reduceIte]
      exact positive_indepLaw ι (hm s j hj)
    · simp only [hj, ↓reduceIte]
      exact hNpos j hj
  have h := class_cost_scalar (univ : Finset Bool) univ_nonempty
    (fun s => diagonalIntegral (tensorLaw fun b => if b ∈ Xs then ζ s b else lam b) F)
    (fun s => diagonalIntegral
      (tensorLaw fun b => if b ∈ Xs then ι.diagonalLaw (m s b) else N b) F)
    (fun s => diagonalIntegral (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m s b) else N b) F)
    (fun s => diagonalIntegral
      (tensorLaw fun b => if b ∈ Xs then indepLaw ι (m s b) else O' b) F)
    (prod_nonneg hγ) hY hCX hCm hzb hz₄ hR0 hRs
    (fun s _ => by
      cases s
      · exact abs_energy_le_variance_blocks ι N lam Xs hXs hN m0 hm0 γ hγ ζ0 hζ0 F
      · exact abs_energy_le_variance_blocks ι N lam Xs hXs hN m1 hm1 γ hγ ζ1 hζ1 F)
    (fun s _ => hJpos s)
    (by simpa [m, add_comm] using hbound)
    (fun s _ => by cases s <;> [exact hDiagN0; exact hDiagN1])
    (fun s _ => by cases s <;> [exact hJN0; exact hJN1])
  simp only [Fintype.sum_bool, ζ, ↓reduceIte, Bool.false_eq_true] at h
  linarith

end Blocks

end Sarkozy.Variance

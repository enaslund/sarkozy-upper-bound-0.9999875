module

public import Sarkozy.Reflection.Seminorm
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.Analysis.Convex.Jensen

/-!
# The pointwise fibre argument

The core of `prop:record:density-structured` (`paper/sections/08_scale_comparison.tex`),
which the improved stage reuses verbatim "up to its final Jensen step"
(`prop:density:production`, `31_density_induction_upgrade.tex`). At a changed slot the
square-step model of a fibre input (`lem:record:fibre-scale`(b)) is
`g̃ = λ · (D/R) ∑_{j ∈ J} hⱼ ∘ Tⱼ` with `|J| = R/D` progressions, maps `Tⱼ` preserving the
reference law, and children `hⱼ` whose energies are controlled by restoration and the
induction hypothesis: `Z(hⱼ) ≤ B αⱼ^θ` (`lem:record:fibre-scale`(c) and the hypothesis on
smaller scales, with `B = C₀ ℓ^(-a)`). Then

`Z(g̃) ≤ λ^d B ((D/R) ∑ⱼ αⱼ)^θ = λ^(d-θ) B α_f^θ`,

using the triangle inequality and invariance of the seminorm `Z^(1/d)`
(`Sarkozy.SignedHolder`), and concavity of `x ↦ x^(θ/d)`. This holds for every
`0 ≤ θ ≤ d`; only the paper's later averaging over the fibre labels needs `θ ≤ 1`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X : Type*} [Fintype V] [DecidableEq V] [Nonempty V]
  {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}

/-- **The fibre energy bound.** -/
theorem SignedHolder.fibre_energy_le (hL : SignedHolder L) {ι : Type*} (J : Finset ι)
    (hJ : J.Nonempty) (h : ι → X → ℝ) (T : ι → X → X)
    (hinv : ∀ j ∈ J, diagonalIntegral L (h j ∘ T j) = diagonalIntegral L (h j))
    {lam B θ : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθd : θ ≤ Fintype.card V) (α : ι → ℝ) (hα : ∀ j ∈ J, 0 ≤ α j)
    (hZ : ∀ j ∈ J, diagonalIntegral L (h j) ≤ B * α j ^ θ) :
    diagonalIntegral L (lam • ∑ j ∈ J, ((J.card : ℝ)⁻¹) • (h j ∘ T j)) ≤
      lam ^ Fintype.card V * B * ((J.card : ℝ)⁻¹ * ∑ j ∈ J, α j) ^ θ := by
  classical
  set d : ℕ := Fintype.card V
  have hd : (0 : ℝ) < d := by exact_mod_cast Fintype.card_pos
  have hcard : (0 : ℝ) < J.card := by exact_mod_cast hJ.card_pos
  set w : ℝ := (J.card : ℝ)⁻¹
  have hw : 0 ≤ w := inv_nonneg.mpr hcard.le
  have hwsum : ∑ _j ∈ J, w = 1 := by
    rw [Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  -- Root energies.
  set q : ℝ := θ / d
  have hq0 : 0 ≤ q := div_nonneg hθ0 hd.le
  have hq1 : q ≤ 1 := (div_le_one hd).mpr hθd
  have hroot_child (j : ι) (hj : j ∈ J) :
      rootEnergy L (h j ∘ T j) ≤ B ^ ((1 : ℝ) / d) * α j ^ q := by
    unfold rootEnergy
    rw [hinv j hj]
    have hle := Real.rpow_le_rpow (hL.1 _) (hZ j hj) (by positivity : (0 : ℝ) ≤ 1 / d)
    refine hle.trans_eq ?_
    rw [Real.mul_rpow hB (Real.rpow_nonneg (hα j hj) _), ← Real.rpow_mul (hα j hj)]
    congr 2
    simp only [q]
    field_simp
  -- Minkowski for the combination.
  have hmink : rootEnergy L (lam • ∑ j ∈ J, w • (h j ∘ T j)) ≤
      lam * (B ^ ((1 : ℝ) / d) * ∑ j ∈ J, w * α j ^ q) := by
    rw [hL.rootEnergy_smul, abs_of_nonneg hlam]
    apply mul_le_mul_of_nonneg_left _ hlam
    refine (hL.rootEnergy_sum_le J (fun _ => w) (fun j => h j ∘ T j)).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [abs_of_nonneg hw]
    calc w * rootEnergy L (h j ∘ T j) ≤ w * (B ^ ((1 : ℝ) / d) * α j ^ q) :=
          mul_le_mul_of_nonneg_left (hroot_child j hj) hw
      _ = B ^ ((1 : ℝ) / d) * (w * α j ^ q) := by ring
  -- Concavity of `x ↦ x^q`.
  have hjensen : ∑ j ∈ J, w * α j ^ q ≤ (∑ j ∈ J, w * α j) ^ q := by
    have hc := (Real.concaveOn_rpow hq0 hq1).le_map_sum (t := J) (w := fun _ => w)
      (p := α) (fun _ _ => hw) hwsum (fun j hj => Set.mem_Ici.mpr (hα j hj))
    simpa only [smul_eq_mul] using hc
  have hmean0 : 0 ≤ ∑ j ∈ J, w * α j := Finset.sum_nonneg fun j hj => mul_nonneg hw (hα j hj)
  have hroot : rootEnergy L (lam • ∑ j ∈ J, w • (h j ∘ T j)) ≤
      lam * (B ^ ((1 : ℝ) / d) * (∑ j ∈ J, w * α j) ^ q) :=
    hmink.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hjensen (Real.rpow_nonneg hB _)) hlam)
  -- Raise to the `d`-th power.
  have hpow := pow_le_pow_left₀ (hL.rootEnergy_nonneg _) hroot d
  rw [hL.rootEnergy_pow] at hpow
  refine hpow.trans_eq ?_
  rw [mul_pow, mul_pow, ← Real.rpow_natCast (B ^ ((1 : ℝ) / d)), ← Real.rpow_mul hB,
    ← Real.rpow_natCast ((∑ j ∈ J, w * α j) ^ q), ← Real.rpow_mul hmean0, ← Finset.mul_sum]
  have h1 : (1 : ℝ) / d * d = 1 := by field_simp
  have h2 : q * d = θ := by
    change θ / d * d = θ
    field_simp
  rw [h1, h2, Real.rpow_one]
  ring

end Sarkozy

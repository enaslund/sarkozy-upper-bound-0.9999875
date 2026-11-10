module

public import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Sarkozy.DensityUpgrade.Coupled

@[expose] public section

/-!
# The fibre moment with a model replacement (`prop:density:production`, the fibre step at `θ > 1`)

The fibre-moment input of `lem:density:coupled` asks a bound on
`(E_q Z(q)^{1/θ})^θ`. Here `Z(q) = Z_{μ_𝒮}(F_A(q, ·))` is the outside energy of the **actual**
fibre of the lift at the selected labels `q`.

The paper does not bound `Z(q)` pointwise. It bounds the energy `Z̃(q)` of the square-step model
of `lem:record:fibre-scale`(b):
* `Z̃(q) ≤ K α_f(q)^θ`, by restoration (`lem:record:fibre-scale`(c)), the scales (d) and the
  induction hypothesis;
* the difference `Z − Z̃` is controlled on average by `lem:record:density-dc`, first display:
  `E_q |Z(q) − Z̃(q)| ≤ C_dc N^{-γβ/2+72δ} α`.

This file contains the real-analysis step that combines the two at `θ ≥ 1`. It is new: B5's
`coupledFibreMoment_of_fibres` needs a pointwise bound on the actual fibres.

* `rpow_add_le_split`: for `θ ≥ 1`, `η > 0`, `s, t ≥ 0`, convexity of `x ↦ x^θ` gives
  `(s + t)^θ ≤ (1 + η)^{θ-1} s^θ + (1 + 1/η)^{θ-1} t^θ`.
* `coupledMean_rpow_le`: Jensen for the concave power, `E f^p ≤ (E f)^p` for `0 < p ≤ 1`.
* **`fibre_moment_le_of_model`**: if `Z ≥ 0`, `α ≥ 0` and `Z̃ ≤ K α^θ` pointwise, then
  `(E Z^{1/θ})^θ ≤ (1 + η)^{θ-1} K (E α)^θ + (1 + 1/η)^{θ-1} E|Z − Z̃|`.

  The main term has the factor `(1 + η)^{θ-1} → 1` as `η → 0`. The remainder is the averaged
  dc difference times `(1 + 1/η)^{θ-1}`. This factor grows only like `η^{-(θ-1)}`, with
  `θ - 1 = 0.014587` at the paper's endpoint. So any power saving of the dc lemma beyond `σ`
  absorbs it, e.g. `η = L^{-1}` with the slack `γβ/2 - 72δ - σ > θ - 1`.
-/

open Finset Set
open scoped BigOperators

namespace Sarkozy.DensityFibre

open Sarkozy.DensityUpgrade

/-- **The convexity split** (`θ ≥ 1`, `η > 0`):
`(s + t)^θ ≤ (1 + η)^{θ-1} s^θ + (1 + 1/η)^{θ-1} t^θ`. -/
theorem rpow_add_le_split {θ η s t : ℝ} (hθ : 1 ≤ θ) (hη : 0 < η) (hs : 0 ≤ s) (ht : 0 ≤ t) :
    (s + t) ^ θ ≤ (1 + η) ^ (θ - 1) * s ^ θ + (1 + 1 / η) ^ (θ - 1) * t ^ θ := by
  have h1η : 0 < 1 + η := by linarith
  have hc : 0 < (1 + η) / η := div_pos h1η hη
  set x := (1 + η) * s with hx
  set y := (1 + η) / η * t with hy
  have hx0 : x ∈ Ici (0 : ℝ) := mem_Ici.mpr (mul_nonneg h1η.le hs)
  have hy0 : y ∈ Ici (0 : ℝ) := mem_Ici.mpr (mul_nonneg hc.le ht)
  have ha : (0 : ℝ) ≤ 1 / (1 + η) := by positivity
  have hb : (0 : ℝ) ≤ η / (1 + η) := by positivity
  have hab : 1 / (1 + η) + η / (1 + η) = 1 := by field_simp
  have hconv := (convexOn_rpow hθ).2 hx0 hy0 ha hb hab
  simp only [smul_eq_mul] at hconv
  have hsum : 1 / (1 + η) * x + η / (1 + η) * y = s + t := by
    rw [hx, hy]
    field_simp
  rw [hsum] at hconv
  refine hconv.trans (le_of_eq ?_)
  rw [hx, hy, Real.mul_rpow h1η.le hs, Real.mul_rpow hc.le ht]
  have e1 : 1 / (1 + η) * ((1 + η) ^ θ * s ^ θ) = (1 + η) ^ (θ - 1) * s ^ θ := by
    rw [Real.rpow_sub_one h1η.ne']
    field_simp
  have e2 : η / (1 + η) * (((1 + η) / η) ^ θ * t ^ θ) = (1 + 1 / η) ^ (θ - 1) * t ^ θ := by
    have e : 1 + 1 / η = (1 + η) / η := by field_simp; ring
    rw [e, Real.rpow_sub_one hc.ne']
    field_simp
  rw [e1, e2]

section Mean

variable {Q : Type*} [Fintype Q]

theorem coupledMean_mono {f g : Q → ℝ} (h : ∀ q, f q ≤ g q) : coupledMean f ≤ coupledMean g := by
  unfold coupledMean
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun q _ => h q) (Nat.cast_nonneg _)

theorem coupledMean_add (f g : Q → ℝ) :
    coupledMean (fun q => f q + g q) = coupledMean f + coupledMean g := by
  unfold coupledMean
  rw [Finset.sum_add_distrib, add_div]

theorem coupledMean_const_mul (c : ℝ) (f : Q → ℝ) :
    coupledMean (fun q => c * f q) = c * coupledMean f := by
  unfold coupledMean
  rw [← Finset.mul_sum, mul_div_assoc]

/-- **Jensen for the concave power**: `E f^p ≤ (E f)^p` for `f ≥ 0`, `0 < p ≤ 1`. -/
theorem coupledMean_rpow_le {f : Q → ℝ} (hf : ∀ q, 0 ≤ f q) {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) :
    coupledMean (fun q => f q ^ p) ≤ coupledMean f ^ p := by
  rcases isEmpty_or_nonempty Q with hQ | hQ
  · unfold coupledMean
    simp only [Finset.univ_eq_empty, Finset.sum_empty, zero_div]
    rw [Real.zero_rpow hp.ne']
  · have hcard : (0 : ℝ) < Fintype.card Q := by exact_mod_cast Fintype.card_pos
    set w : Q → ℝ := fun _ => 1 / (Fintype.card Q : ℝ)
    have hw : ∀ q ∈ (univ : Finset Q), 0 ≤ w q := fun _ _ => by positivity
    have hw' : ∑ q ∈ (univ : Finset Q), w q = 1 := by
      simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      field_simp
    have hz : ∀ q ∈ (univ : Finset Q), 0 ≤ f q ^ p := fun q _ => Real.rpow_nonneg (hf q) _
    have h1p : 1 ≤ 1 / p := by rw [le_div_iff₀ hp]; linarith
    have hJ := Real.rpow_arith_mean_le_arith_mean_rpow (s := univ) w (fun q => f q ^ p) hw hw' hz
      h1p
    have hpp : ∀ q, (f q ^ p) ^ (1 / p) = f q := fun q => by
      rw [← Real.rpow_mul (hf q), mul_one_div_cancel hp.ne', Real.rpow_one]
    simp only [hpp] at hJ
    have hmean : ∀ g : Q → ℝ, ∑ q, w q * g q = coupledMean g := fun g => by
      unfold coupledMean
      simp only [w]
      rw [← Finset.mul_sum]
      field_simp
    rw [hmean, hmean] at hJ
    have h0 : 0 ≤ coupledMean (fun q => f q ^ p) :=
      coupledMean_nonneg fun q => Real.rpow_nonneg (hf q) _
    have h2 := Real.rpow_le_rpow (Real.rpow_nonneg h0 _) hJ hp.le
    rwa [← Real.rpow_mul h0, one_div_mul_cancel hp.ne', Real.rpow_one] at h2

/-- **The fibre moment of the actual fibres from a model with a pointwise bound and an averaged
difference** (`prop:density:production`, fibre step at `θ ≥ 1`; `lem:record:density-dc`, first
display, for the difference). If `Z ≥ 0`, `α ≥ 0`, `K ≥ 0` and `Z̃(q) ≤ K α(q)^θ` for every `q`,
then for every `η > 0`
`(E Z^{1/θ})^θ ≤ (1 + η)^{θ-1} K (E α)^θ + (1 + 1/η)^{θ-1} E|Z − Z̃|`. -/
theorem fibre_moment_le_of_model {Z Zt α : Q → ℝ} (hZ : ∀ q, 0 ≤ Z q) (hα : ∀ q, 0 ≤ α q)
    {K θ η : ℝ} (hK : 0 ≤ K) (hθ : 1 ≤ θ) (hη : 0 < η) (hmod : ∀ q, Zt q ≤ K * α q ^ θ) :
    coupledMean (fun q => Z q ^ (1 / θ)) ^ θ ≤
      (1 + η) ^ (θ - 1) * (K * coupledMean α ^ θ) +
        (1 + 1 / η) ^ (θ - 1) * coupledMean (fun q => |Z q - Zt q|) := by
  have hθ0 : 0 < θ := by linarith
  have hp : 0 < 1 / θ := by positivity
  have hp1 : 1 / θ ≤ 1 := by rw [div_le_one hθ0]; exact hθ
  set e : Q → ℝ := fun q => |Z q - Zt q| with he
  have he0 : ∀ q, 0 ≤ e q := fun q => abs_nonneg _
  have hKα : ∀ q, 0 ≤ K * α q ^ θ := fun q => mul_nonneg hK (Real.rpow_nonneg (hα q) _)
  -- pointwise: `Z^{1/θ} ≤ K^{1/θ} α + e^{1/θ}`
  have hpt : ∀ q, Z q ^ (1 / θ) ≤ K ^ (1 / θ) * α q + e q ^ (1 / θ) := by
    intro q
    have hle : Z q ≤ K * α q ^ θ + e q := by
      have := le_abs_self (Z q - Zt q)
      have := hmod q
      simp only [he]
      linarith
    have h1 := Real.rpow_le_rpow (hZ q) hle hp.le
    have h2 := Real.rpow_add_le_add_rpow (hKα q) (he0 q) hp.le hp1
    have h3 : (K * α q ^ θ) ^ (1 / θ) = K ^ (1 / θ) * α q := by
      rw [Real.mul_rpow hK (Real.rpow_nonneg (hα q) _), ← Real.rpow_mul (hα q),
        mul_one_div_cancel hθ0.ne', Real.rpow_one]
    rw [h3] at h2
    exact h1.trans h2
  -- the mean
  set s := K ^ (1 / θ) * coupledMean α with hs
  set t := coupledMean e ^ (1 / θ) with ht
  have hs0 : 0 ≤ s := mul_nonneg (Real.rpow_nonneg hK _) (coupledMean_nonneg hα)
  have he0m : 0 ≤ coupledMean e := coupledMean_nonneg he0
  have ht0 : 0 ≤ t := Real.rpow_nonneg he0m _
  have hmean : coupledMean (fun q => Z q ^ (1 / θ)) ≤ s + t := by
    calc coupledMean (fun q => Z q ^ (1 / θ))
        ≤ coupledMean (fun q => K ^ (1 / θ) * α q + e q ^ (1 / θ)) := coupledMean_mono hpt
      _ = K ^ (1 / θ) * coupledMean α + coupledMean (fun q => e q ^ (1 / θ)) := by
          rw [coupledMean_add, coupledMean_const_mul]
      _ ≤ s + t := by
          have := coupledMean_rpow_le he0 hp hp1
          rw [hs, ht]
          linarith
  have hZm : 0 ≤ coupledMean (fun q => Z q ^ (1 / θ)) :=
    coupledMean_nonneg fun q => Real.rpow_nonneg (hZ q) _
  have hpow := Real.rpow_le_rpow hZm hmean hθ0.le
  have hsplit := rpow_add_le_split hθ hη hs0 ht0
  have hsθ : s ^ θ = K * coupledMean α ^ θ := by
    rw [hs, Real.mul_rpow (Real.rpow_nonneg hK _) (coupledMean_nonneg hα), ← Real.rpow_mul hK,
      one_div_mul_cancel hθ0.ne', Real.rpow_one]
  have htθ : t ^ θ = coupledMean e := by
    rw [ht, ← Real.rpow_mul he0m, one_div_mul_cancel hθ0.ne', Real.rpow_one]
  rw [hsθ, htθ] at hsplit
  exact hpow.trans hsplit

end Mean

end Sarkozy.DensityFibre

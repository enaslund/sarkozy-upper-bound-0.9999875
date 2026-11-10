module

public import Sarkozy.OpsFeature.UnitLift
public import Sarkozy.Envelopes.PurePair

@[expose] public section

/-!
# The fold label `3`: the pure-pair arms under the substitute `Q₁₂` (`lem:oct24:mask-schur`(a))

`paper/sections/23_envelopes.tex`, proof of `lem:oct24:mask-schur`(a) (move 4, the scalar unit
`e₃₃ ↦ Q₁₂`) with `eq:signed-star` (`Ξ_p` has the label-`3` component `A_3°/r_p`, "a map of norm at
most `r_p` into the sector `{p}` of `𝒦₁₂`", `lem:actual-features`(c), (e)) and
`lem:oct24:pure-pair-substitute` (`Π_{𝒦₁₂} ⪯ Q₁₂`).

**`pureArms_form_le`** (W2's abstract setting `E`, `Cst ≤ S₁, S₂ ≤ S₁₂`, `|⟪H₁, H₂⟫| ≤ ρ`): if the
columns `Y_{p,z}` of the maps `Y_p` lie in the pure-pair space `𝒦₁₂`, the maps of different `p`
have orthogonal ranges (the singleton sectors) and every `Y_p` is a contraction, then
`∑_p ‖Y_p^* x‖² = ∑_{p,z} ⟪x, Y_{p,z}⟫² ≤ ⟪Q₁₂ x, x⟫`. The proof: with `v = ∑ ⟪x, Y_{p,z}⟫ Y_{p,z}`,
`S = ⟪x, v⟫ = ⟪Π_𝒦 x, v⟫ ≤ ‖Π_𝒦 x‖ ‖v‖`, `‖v‖² ≤ S` (orthogonality, contraction), so
`S ≤ ‖Π_𝒦 x‖² ≤ ⟪Q₁₂ x, x⟫` (W2's `pureSubstitute_form_bounds`).

**`unit_ge_gram_of_form`** turns such a form inequality into the kernel inequality `hUa` of
`hdom_of_units`; **`label3_le_substitute`**: the label-`3` inequality `hUa` (a kernel
inequality in `L²(m)`), for a realization `emb` of `L²(m)` in `E` under which the unit lift
`U(3, 3)` is `Q₁₂` (`hQ`) and the sector maps `Ξ_{p,3}` are the `Y_p` (`hΞ`);
**`singleton_le_proj`**: the labels `0, 1, 2`, with `U(a, a)` the projection onto `H_a`
(`arms_form_le_proj`, Bessel for the singleton sectors).
-/

open Finset Matrix
open scoped BigOperators RealInnerProductSpace

namespace Sarkozy.OpsFeature

open Sarkozy.Envelopes Sarkozy.EnvelopeSteps

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **Arms into orthogonal sectors of a subspace `K`** (Bessel): if the columns `Y_{p,z}` lie in
`K`, the maps of different `p` have orthogonal ranges and every `Y_p` is a contraction, then
`∑_{p,z} ⟪x, Y_{p,z}⟫² ≤ ⟪Π_K x, x⟫`. -/
theorem arms_form_le_proj (K : Submodule ℝ E)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (Y : ∀ p, Z p → E) (hK : ∀ p z, Y p z ∈ K)
    (horth : ∀ p q, p ≠ q → ∀ z z', ⟪Y p z, Y q z'⟫ = 0)
    (hcon : ∀ p (a : Z p → ℝ), ‖∑ z, a z • Y p z‖ ^ 2 ≤ ∑ z, a z ^ 2) (x : E) :
    ∑ p, ∑ z, ⟪x, Y p z⟫ ^ 2 ≤ ⟪K.starProjection x, x⟫ := by
  set w : ∀ p, Z p → ℝ := fun p z => ⟪x, Y p z⟫ with hw
  set S := ∑ p, ∑ z, w p z ^ 2 with hS
  set vp : ι → E := fun p => ∑ z, w p z • Y p z with hvp
  set v := ∑ p, vp p with hv
  have hS0 : 0 ≤ S := sum_nonneg fun p _ => sum_nonneg fun z _ => sq_nonneg _
  -- `S = ⟪x, v⟫`
  have hSv : S = ⟪x, v⟫ := by
    simp only [hv, hvp, inner_sum, inner_smul_right, hS, hw, sq]
  -- `v ∈ K`
  have hvK : v ∈ K := Submodule.sum_mem _ fun p _ =>
    Submodule.sum_mem _ fun z _ => Submodule.smul_mem _ _ (hK p z)
  -- `‖v‖² ≤ S`
  have hvp_orth : ∀ p q, p ≠ q → ⟪vp p, vp q⟫ = 0 := by
    intro p q hpq
    simp only [hvp, sum_inner, inner_sum, inner_smul_left, inner_smul_right, horth p q hpq,
      mul_zero, sum_const_zero]
  have hvn : ‖v‖ ^ 2 ≤ S := by
    have e : ‖v‖ ^ 2 = ∑ p, ‖vp p‖ ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hv, sum_inner]
      refine sum_congr rfl fun p _ => ?_
      rw [inner_sum, sum_eq_single p (fun q _ hq => hvp_orth p q (Ne.symm hq)) (by simp),
        real_inner_self_eq_norm_sq]
    rw [e, hS]
    exact sum_le_sum fun p _ => hcon p (w p)
  -- `S ≤ ‖Π_K x‖ ‖v‖`
  have hPx : ⟪x, v⟫ = ⟪K.starProjection x, v⟫ := by
    have h0 : ⟪x - K.starProjection x, v⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hvK (K.sub_starProjection_mem_orthogonal x)
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have hCS : S ≤ ‖K.starProjection x‖ * ‖v‖ := by
    rw [hSv, hPx]
    exact real_inner_le_norm _ _
  -- `S ≤ ‖Π_K x‖²`
  have hSP : S ≤ ‖K.starProjection x‖ ^ 2 := by
    set P := ‖K.starProjection x‖
    have hP0 : 0 ≤ P := norm_nonneg _
    have hvS : ‖v‖ ≤ Real.sqrt S := Real.le_sqrt_of_sq_le hvn
    have h1 : S ≤ P * Real.sqrt S := hCS.trans (mul_le_mul_of_nonneg_left hvS hP0)
    have hsS : Real.sqrt S * Real.sqrt S = S := Real.mul_self_sqrt hS0
    have hs0 : 0 ≤ Real.sqrt S := Real.sqrt_nonneg S
    have h2 : Real.sqrt S ≤ P := by
      rcases hs0.eq_or_lt with h | h
      · rw [← h]; exact hP0
      · nlinarith
    nlinarith
  -- `‖Π_K x‖² = ⟪Π_K x, x⟫`
  have hnorm : ‖K.starProjection x‖ ^ 2 = ⟪K.starProjection x, x⟫ := by
    rw [← real_inner_self_eq_norm_sq]
    have h0 : ⟪K.starProjection x, x - K.starProjection x⟫ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (K.starProjection_apply_mem x)
        (K.sub_starProjection_mem_orthogonal x)
    rw [inner_sub_right, sub_eq_zero] at h0
    exact h0.symm
  linarith

/-- **The pure-pair arms are dominated by the substitute `Q₁₂`** (form version). -/
theorem pureArms_form_le {Cst Si Sj Sij : Submodule ℝ E} (hi : Cst ≤ Si) (hj : Cst ≤ Sj)
    (hii : Si ≤ Sij) (hjj : Sj ≤ Sij) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcor : ∀ f ∈ featureSpace Cst Si, ∀ h ∈ featureSpace Cst Sj, |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (Y : ∀ p, Z p → E) (hK : ∀ p z, Y p z ∈ pureSpace Cst Si Sj Sij)
    (horth : ∀ p q, p ≠ q → ∀ z z', ⟪Y p z, Y q z'⟫ = 0)
    (hcon : ∀ p (a : Z p → ℝ), ‖∑ z, a z • Y p z‖ ^ 2 ≤ ∑ z, a z ^ 2) (x : E) :
    ∑ p, ∑ z, ⟪x, Y p z⟫ ^ 2 ≤ ⟪pureSubstitute Cst Si Sj Sij ρ x, x⟫ := by
  have hPQ := (pureSubstitute_form_bounds hi hj hii hjj hρ hρ1 hcor x).1
  rw [_root_.sub_apply, inner_sub_left, sub_nonneg] at hPQ
  exact (arms_form_le_proj _ Y hK horth hcon x).trans hPQ

end Abstract

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {O : Type*} [Fintype O] [DecidableEq O]

omit [FiniteDimensional ℝ E] in
/-- **A unit lift dominates the Gram table of the sector maps** (the label inequality `hUa` of
`hdom_of_units`, as kernels in `L²(m)`), from the form inequality
`∑_{p,z} ⟪emb f, Y_{p,z}⟫² ≤ ⟨f, U f⟩_m` in a realization `emb` of `L²(m)` with
`∑_x f(x) Ξ_p(x, z) = ⟪emb f, Y_{p,z}⟫` (`hΞ`) and `U` symmetric in `L²(m)` (`hUs`). -/
theorem unit_ge_gram_of_form {ι : Type*} [Fintype ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (Y : ∀ p, Z p → E) (m : O → ℝ) (emb : (O → ℝ) →ₗ[ℝ] E) (Uop : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hform : ∀ f, ∑ p, ∑ z, ⟪emb f, Y p z⟫ ^ 2 ≤ ip m f (Uop f))
    (hQs : ∀ f g, ip m f (Uop g) = ip m g (Uop f))
    (Ξ : ∀ p, Matrix O (Z p) ℝ) (hΞ : ∀ p z f, ∑ x, f x * Ξ p x z = ⟪emb f, Y p z⟫) :
    (Matrix.of fun x y : O => kern m Uop x y - ∑ p, ∑ z, Ξ p x z * Ξ p y z).PosSemidef := by
  have hk : ∀ x y, kern m Uop x y = ip m (delta x) (Uop (delta y)) := by
    intro x y
    simp only [kern, ip, delta, ite_mul, one_mul, zero_mul, mul_ite, mul_zero,
      sum_ite_eq', mem_univ, ↓reduceIte]
  refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun ξ => ?_
  · ext x y
    simp only [conjTranspose_apply, star_trivial, Matrix.of_apply, hk]
    rw [hQs (delta y) (delta x)]
    congr 1
    exact sum_congr rfl fun p _ => sum_congr rfl fun z _ => mul_comm _ _
  · set G : O → O → ι → ℝ := fun x y p => ∑ z, ξ x * Ξ p x z * (ξ y * Ξ p y z) with hG
    have e2 : ∀ p, ∑ z, (∑ x, ξ x * Ξ p x z) ^ 2 = ∑ x, ∑ y, G x y p := by
      intro p
      simp only [hG, sq, sum_mul_sum]
      rw [sum_comm]
      exact sum_congr rfl fun x _ => sum_comm
    have e : star ξ ⬝ᵥ ((Matrix.of fun x y : O => kern m Uop x y -
        ∑ p, ∑ z, Ξ p x z * Ξ p y z) *ᵥ ξ) =
        ip m ξ (Uop ξ) - ∑ p, ∑ z, (∑ x, ξ x * Ξ p x z) ^ 2 := by
      rw [ip_eq_kern]
      simp only [e2]
      have e3 : ∑ p, ∑ x, ∑ y, G x y p = ∑ x, ∑ y, ∑ p, G x y p := by
        rw [sum_comm]
        exact sum_congr rfl fun x _ => sum_comm
      rw [e3, ← sum_sub_distrib]
      simp only [dotProduct, mulVec, star_trivial, Matrix.of_apply, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun y _ => ?_
      simp only [hG, mul_sub, sub_mul, sum_mul, mul_sum]
      congr 1
      · ring
      · exact sum_congr rfl fun p _ => sum_congr rfl fun z _ => by ring
    rw [e]
    simp only [hΞ]
    linarith [hform ξ]


/-- **The label-`3` inequality `hUa` of `hdom_of_units`** (`U(3, 3) = Q₁₂ ⪰ ∑_p Ξ_{p,3} Ξ_{p,3}ᵀ`
as kernels in `L²(m)`): for a realization `emb` of `L²(m)` in W2's `E` under which the unit lift
`Qop = U(3, 3)` has the form of `Q₁₂` (`hQ`, `hQs`) and the label-`3` columns of the sector maps
are the pure-pair arms `Y_p` (`hΞ`), with ranges in `𝒦₁₂` (`hK`), orthogonal across the singleton
sectors (`horth`), contractions (`hcon`: `A_3°/r_p`, `lem:actual-features`(c), (e)). -/
theorem label3_le_substitute {Cst Si Sj Sij : Submodule ℝ E} (hi : Cst ≤ Si) (hj : Cst ≤ Sj)
    (hii : Si ≤ Sij) (hjj : Sj ≤ Sij) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hcor : ∀ f ∈ featureSpace Cst Si, ∀ h ∈ featureSpace Cst Sj, |⟪f, h⟫| ≤ ρ * ‖f‖ * ‖h‖)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (Y : ∀ p, Z p → E) (hK : ∀ p z, Y p z ∈ pureSpace Cst Si Sj Sij)
    (horth : ∀ p q, p ≠ q → ∀ z z', ⟪Y p z, Y q z'⟫ = 0)
    (hcon : ∀ p (a : Z p → ℝ), ‖∑ z, a z • Y p z‖ ^ 2 ≤ ∑ z, a z ^ 2)
    (m : O → ℝ) (emb : (O → ℝ) →ₗ[ℝ] E) (Qop : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hQ : ∀ f, ip m f (Qop f) = ⟪pureSubstitute Cst Si Sj Sij ρ (emb f), emb f⟫)
    (hQs : ∀ f g, ip m f (Qop g) = ip m g (Qop f))
    (Ξ : ∀ p, Matrix O (Z p) ℝ) (hΞ : ∀ p z f, ∑ x, f x * Ξ p x z = ⟪emb f, Y p z⟫) :
    (Matrix.of fun x y : O => kern m Qop x y - ∑ p, ∑ z, Ξ p x z * Ξ p y z).PosSemidef :=
  unit_ge_gram_of_form Y m emb Qop (fun f => by
    rw [hQ]; exact pureArms_form_le hi hj hii hjj hρ hρ1 hcor Y hK horth hcon (emb f)) hQs Ξ hΞ

/-- **The singleton labels `a = 0, 1, 2`** (`U(a, a) = V_a V_a^* = M_aa − 𝒥 ⪰ ∑_p Ξ_{p,a} Ξ_{p,a}ᵀ`
as kernels): `U(a, a)` realizes the projection onto `H_a = featureSpace Cst S_a` (`hU`), the
label-`a` columns of the sector maps are `V_a` on the singleton sectors (`hK`: in `H_a`; `horth`:
orthogonal across the sectors; `hcon`: contractions). -/
theorem singleton_le_proj (H : Submodule ℝ E)
    {ι : Type*} [Fintype ι] [DecidableEq ι] {Z : ι → Type*} [∀ p, Fintype (Z p)]
    (Y : ∀ p, Z p → E) (hK : ∀ p z, Y p z ∈ H)
    (horth : ∀ p q, p ≠ q → ∀ z z', ⟪Y p z, Y q z'⟫ = 0)
    (hcon : ∀ p (a : Z p → ℝ), ‖∑ z, a z • Y p z‖ ^ 2 ≤ ∑ z, a z ^ 2)
    (m : O → ℝ) (emb : (O → ℝ) →ₗ[ℝ] E) (Uop : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hU : ∀ f, ip m f (Uop f) = ⟪H.starProjection (emb f), emb f⟫)
    (hUs : ∀ f g, ip m f (Uop g) = ip m g (Uop f))
    (Ξ : ∀ p, Matrix O (Z p) ℝ) (hΞ : ∀ p z f, ∑ x, f x * Ξ p x z = ⟪emb f, Y p z⟫) :
    (Matrix.of fun x y : O => kern m Uop x y - ∑ p, ∑ z, Ξ p x z * Ξ p y z).PosSemidef :=
  unit_ge_gram_of_form Y m emb Uop (fun f => by
    rw [hU]; exact arms_form_le_proj H Y hK horth hcon (emb f)) hUs Ξ hΞ

end Bridge

end Sarkozy.OpsFeature

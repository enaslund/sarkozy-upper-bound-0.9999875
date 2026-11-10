module

public import Sarkozy.Angles.Friedrichs

/-!
# Duality of the Friedrichs angle

Kassabov, *Subspace arrangements and property T*, Lemma 3.9: in finite dimension
`cos∠(Vᗮ, Wᗮ) = cos∠(V, W)` (`friedrichsCos_orthogonal`).

The proof of `≤` (`friedrichsCos_orthogonal_le`) is elementary. Put `c = cos∠(V, W)` and let
`a ∈ Vᗮ` be orthogonal to `Vᗮ ⊓ Wᗮ = (V ⊔ W)ᗮ`, so `a ∈ V ⊔ W`.
* Then `a = P_{Vᗮ} w'` for some `w' ∈ W` orthogonal to `V ⊓ W`. Put `x = P_V w'`, so
  `a = w' - x`.
* For every `b ∈ Wᗮ`, `⟪a, b⟫ = -⟪x, b⟫ = -⟪P_{Wᗮ} x, b⟫`.
* `‖P_W x‖ ‖w'‖ ≥ ⟪P_W x, w'⟫ = ⟪x, w'⟫ = ‖x‖²`. Hence
  `‖P_{Wᗮ} x‖² ‖w'‖² = (‖x‖² - ‖P_W x‖²) ‖w'‖² ≤ ‖x‖² (‖w'‖² - ‖x‖²) = ‖x‖² ‖a‖²`.
* With `‖x‖ ≤ c ‖w'‖` this gives `‖P_{Wᗮ} x‖ ≤ c ‖a‖`, so `|⟪a, b⟫| ≤ c ‖a‖ ‖b‖`.

Only `b ∈ Wᗮ` is used, not `b ⊥ Vᗮ ⊓ Wᗮ` (`abs_inner_le_friedrichsCos_of_orthogonal`). The
reverse inequality follows by applying `≤` to `Vᗮ`, `Wᗮ`, since `Vᗮᗮ = V`.

Also `orthogonal_inf_eq_sup`: `(V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ` in finite dimension.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- In finite dimension, `(V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ`. -/
theorem orthogonal_inf_eq_sup (V W : Submodule ℝ E) : (V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ := by
  have h : (Vᗮ ⊔ Wᗮ)ᗮ = V ⊓ W := by
    rw [← Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal,
      Submodule.orthogonal_orthogonal]
  rw [← h, Submodule.orthogonal_orthogonal]

/-- The real-number step of the duality: from `‖x‖² = ‖P_W x‖² + q²`, `‖w'‖² = ‖x‖² + ‖a‖²`,
`‖x‖² ≤ ‖P_W x‖ ‖w'‖` and `‖x‖ ≤ c ‖w'‖`, conclude `q ≤ c ‖a‖`. -/
theorem duality_real_step {s t p q α c : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hq : 0 ≤ q)
    (hα : 0 ≤ α) (hc : 0 ≤ c) (h1 : s ^ 2 = p ^ 2 + q ^ 2) (h2 : t ^ 2 = s ^ 2 + α ^ 2)
    (h3 : s ^ 2 ≤ p * t) (h4 : s ≤ c * t) : q ≤ c * α := by
  have h5 : (s ^ 2) ^ 2 ≤ (p * t) ^ 2 := pow_le_pow_left₀ (sq_nonneg s) h3 2
  have h6 : q ^ 2 * t ^ 2 ≤ s ^ 2 * α ^ 2 := by
    have e1 : q ^ 2 = s ^ 2 - p ^ 2 := by linarith
    have e2 : α ^ 2 = t ^ 2 - s ^ 2 := by linarith
    rw [e1, e2]
    nlinarith [h5]
  have h7 : s ^ 2 ≤ (c * t) ^ 2 := pow_le_pow_left₀ hs h4 2
  have h8 : q ^ 2 * t ^ 2 ≤ (c * α) ^ 2 * t ^ 2 := by
    have : s ^ 2 * α ^ 2 ≤ (c * t) ^ 2 * α ^ 2 := mul_le_mul_of_nonneg_right h7 (sq_nonneg α)
    nlinarith [h6, this]
  rcases ht.eq_or_lt with h0 | htpos
  · -- `t = 0` forces `s = 0`, hence `q = 0`.
    have hs0 : s = 0 := by
      rw [← h0, mul_zero] at h4
      exact le_antisymm h4 hs
    have hq0 : q = 0 := by
      rw [hs0] at h1
      nlinarith [sq_nonneg p, sq_nonneg q]
    rw [hq0]
    exact mul_nonneg hc hα
  · have ht2 : 0 < t ^ 2 := by positivity
    have h9 : q ^ 2 ≤ (c * α) ^ 2 := le_of_mul_le_mul_right h8 ht2
    exact (pow_le_pow_iff_left₀ hq (mul_nonneg hc hα) two_ne_zero).mp h9

/-- **The key step of the duality.** For `a ∈ Vᗮ` orthogonal to `Vᗮ ⊓ Wᗮ` and for **every**
`b ∈ Wᗮ`, `|⟪a, b⟫| ≤ cos∠(V, W) ‖a‖ ‖b‖`. -/
theorem abs_inner_le_friedrichsCos_of_orthogonal {V W : Submodule ℝ E} {a b : E}
    (ha : a ∈ Vᗮ) (ha' : a ∈ (Vᗮ ⊓ Wᗮ)ᗮ) (hb : b ∈ Wᗮ) :
    |⟪a, b⟫_ℝ| ≤ friedrichsCos V W * ‖a‖ * ‖b‖ := by
  have hc0 : 0 ≤ friedrichsCos V W := friedrichsCos_nonneg V W
  -- `a ∈ V ⊔ W`, so `a = y + z` with `y ∈ V`, `z ∈ W`.
  have haVW : a ∈ V ⊔ W := by
    rwa [Submodule.inf_orthogonal, Submodule.orthogonal_orthogonal] at ha'
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp haVW
  -- `w' = z - P_{V ⊓ W} z ∈ W ⊓ (V ⊓ W)ᗮ`.
  have hQz : (V ⊓ W).starProjection z ∈ V ⊓ W := Submodule.starProjection_apply_mem _ _
  set w' := z - (V ⊓ W).starProjection z with hw'def
  have hw'W : w' ∈ W := W.sub_mem hz (Submodule.mem_inf.mp hQz).2
  have hw'o : w' ∈ (V ⊓ W)ᗮ := Submodule.sub_starProjection_mem_orthogonal z
  set x := V.starProjection w' with hxdef
  -- `a = P_{Vᗮ} w' = w' - x`.
  have hPa : Vᗮ.starProjection w' = a := by
    have h1 : Vᗮ.starProjection a = a := Submodule.starProjection_eq_self_iff.mpr ha
    have h2 : Vᗮ.starProjection y = 0 := Submodule.starProjection_orthogonal_apply_eq_zero hy
    have h3 : Vᗮ.starProjection ((V ⊓ W).starProjection z) = 0 :=
      Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_inf.mp hQz).1
    have h4 : Vᗮ.starProjection w' = Vᗮ.starProjection z := by
      rw [hw'def, map_sub, h3, sub_zero]
    rw [h4, ← h1, ← hyz, map_add, h2, zero_add]
  have hax : a = w' - x := by
    rw [← hPa, hxdef, Submodule.starProjection_orthogonal_val]
  -- `⟪a, b⟫ = -⟪P_{Wᗮ} x, b⟫`.
  have hab : ⟪a, b⟫_ℝ = -⟪Wᗮ.starProjection x, b⟫_ℝ := by
    have hw'b : ⟪w', b⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hw'W hb
    have hPb : Wᗮ.starProjection b = b := Submodule.starProjection_eq_self_iff.mpr hb
    rw [Submodule.inner_starProjection_left_eq_right, hPb, hax, inner_sub_left, hw'b,
      zero_sub]
  -- The four norm relations.
  have h1 : ‖x‖ ^ 2 = ‖W.starProjection x‖ ^ 2 + ‖Wᗮ.starProjection x‖ ^ 2 :=
    Submodule.norm_sq_eq_add_norm_sq_starProjection x W
  have h2 : ‖w'‖ ^ 2 = ‖x‖ ^ 2 + ‖a‖ ^ 2 := by
    rw [← hPa]
    exact Submodule.norm_sq_eq_add_norm_sq_starProjection w' V
  have h3 : ‖x‖ ^ 2 ≤ ‖W.starProjection x‖ * ‖w'‖ := by
    have hPw : W.starProjection w' = w' := Submodule.starProjection_eq_self_iff.mpr hw'W
    have e : ‖x‖ ^ 2 = ⟪W.starProjection x, w'⟫_ℝ := by
      rw [Submodule.inner_starProjection_left_eq_right, hPw, hxdef, inner_starProjection_self]
    rw [e]
    exact real_inner_le_norm _ _
  have h4 : ‖x‖ ≤ friedrichsCos V W * ‖w'‖ := norm_starProjection_le_friedrichsCos hw'W hw'o
  have hq : ‖Wᗮ.starProjection x‖ ≤ friedrichsCos V W * ‖a‖ :=
    duality_real_step (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) (norm_nonneg _) hc0 h1 h2
      h3 h4
  calc |⟪a, b⟫_ℝ| = |⟪Wᗮ.starProjection x, b⟫_ℝ| := by rw [hab, abs_neg]
    _ ≤ ‖Wᗮ.starProjection x‖ * ‖b‖ := abs_real_inner_le_norm _ _
    _ ≤ friedrichsCos V W * ‖a‖ * ‖b‖ := by gcongr

/-- `cos∠(Vᗮ, Wᗮ) ≤ cos∠(V, W)`. -/
theorem friedrichsCos_orthogonal_le (V W : Submodule ℝ E) :
    friedrichsCos Vᗮ Wᗮ ≤ friedrichsCos V W :=
  friedrichsCos_le_of_forall (friedrichsCos_nonneg V W) fun _ ha _ hb ha' _ =>
    abs_inner_le_friedrichsCos_of_orthogonal ha ha' hb

/-- **Duality** (Kassabov, Lemma 3.9): in finite dimension `cos∠(Vᗮ, Wᗮ) = cos∠(V, W)`. -/
theorem friedrichsCos_orthogonal (V W : Submodule ℝ E) :
    friedrichsCos Vᗮ Wᗮ = friedrichsCos V W := by
  refine le_antisymm (friedrichsCos_orthogonal_le V W) ?_
  have h := friedrichsCos_orthogonal_le Vᗮ Wᗮ
  rwa [Submodule.orthogonal_orthogonal, Submodule.orthogonal_orthogonal] at h

end Sarkozy.Angles

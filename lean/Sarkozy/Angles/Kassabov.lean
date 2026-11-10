module

public import Sarkozy.Angles.Duality

/-!
# Kassabov's angle inequality

`thm:kassabov` (`paper/sections/04_notation.tex`), which the paper cites as Kassabov,
*Subspace arrangements and property T* (arXiv:0911.1983), Lemma 4.2(b): for subspaces
`V₁, V₂, V₃` of a finite-dimensional real inner product space with `εᵢⱼ = cos∠(Vᵢ, Vⱼ)`,
`ε₁₃ < 1` and `ε₂₃ < 1`,
`cos∠(V₁ ⊓ V₃, V₂ ⊓ V₃) ≤ (ε₁₂ + ε₁₃ ε₂₃) / √((1 - ε₁₃²)(1 - ε₂₃²))`
(`kassabov_angle_inequality`). Lemma 4.2(a), the same bound for `cos∠(V₁ ⊔ V₃, V₂ ⊔ V₃)`,
is `kassabov_angle_inequality_sup`. Both are also proved in Kassabov's own form, with upper
bounds `eᵢⱼ` for the cosines in place of the cosines themselves (`kassabov_sup`,
`kassabov_inf`). No case distinction is needed when one space contains another.

## The proof, and the gap in the printed one

Kassabov's proof of (a): take `uᵢ ∈ Wᵢ ⊔ W₃` orthogonal to `(W₁ ⊔ W₃) ⊓ (W₂ ⊔ W₃)`. Then
`uᵢ ⊥ W₃`, so `uᵢ = vᵢ - P_{W₃} vᵢ` with `vᵢ ∈ Wᵢ`, and `vᵢ` may be taken orthogonal to
`Wᵢ ⊓ W₃`, which gives `‖P_{W₃} vᵢ‖ ≤ εᵢ₃ ‖vᵢ‖`. Then
`⟪u₁, u₂⟫ = ⟪v₁, v₂⟫ - ⟪P_{W₃} v₁, P_{W₃} v₂⟫`. The printed proof also asserts that the `vᵢ`
can be taken orthogonal to `W₁ ⊓ W₂`, to get `|⟪v₁, v₂⟫| ≤ ε₁₂ ‖v₁‖ ‖v₂‖`. This is false in
general: the condition `vᵢ ⊥ Wᵢ ⊓ W₃` already determines `vᵢ`, and that `vᵢ` need not be
orthogonal to `W₁ ⊓ W₂`.

Example: in `ℝ⁴` take `W₁ = span(e₁, e₂)`, `W₂ = span(e₁, e₃)` and `W₃ = span(1, 1, 1, 2)`.
Then `(W₁ ⊔ W₃) ⊓ (W₂ ⊔ W₃) = span(e₁, W₃)`, whose orthogonal complement in `Wᵢ ⊔ W₃` is the
line through `u₁ = (0, 5, -1, -2)`, resp. `u₂ = (0, -1, 5, -2)`. Since `Wᵢ ⊓ W₃ = 0`, the only
choices (up to scale) are `v₁ = (1/6, 1, 0, 0)` and `v₂ = (1/6, 0, 1, 0)`. Neither is orthogonal
to `W₁ ⊓ W₂ = span(e₁)`, and `⟪v₁, v₂⟫ = 1/36 > 0 = ε₁₂ ‖v₁‖ ‖v₂‖`. The lemma itself holds
there: the cosine is `1/5` and the bound is `2/5`.

The argument is complete when `W₁ ⊓ W₂ ≤ W₃`: then `W₁ ⊓ W₂ ≤ W₂ ⊓ W₃`, so `v₂ ⊥ W₁ ⊓ W₂`,
and the one-sided bound `abs_inner_le_friedrichsCos_of_right` needs only that
(`kassabov_sup_of_inf_le`).

The general case reduces to this one. Replace `W₃` by `W₃' = W₃ ⊔ (W₁ ⊓ W₂)`. This does not
change `Wᵢ ⊔ W₃`, and it does not increase `cos∠(Wᵢ, W₃)`
(`friedrichsCos_sup_le_of_le`, proved by duality). Part (b) follows from (a) applied to
`Vᵢᗮ`, by duality (`friedrichsCos_orthogonal`) and `(V ⊓ W)ᗮ = Vᗮ ⊔ Wᗮ`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Enlarging one space by a subspace of the other does not increase the cosine: if `Z ≤ W`,
then `cos∠(W, T ⊔ Z) ≤ cos∠(W, T)`. By duality this is
`cos∠(Wᗮ, Tᗮ ⊓ Zᗮ) ≤ cos∠(Wᗮ, Tᗮ)`, which is `friedrichsCos_mono` since `Wᗮ ≤ Zᗮ`. -/
theorem friedrichsCos_sup_le_of_le {W T Z : Submodule ℝ E} (hZ : Z ≤ W) :
    friedrichsCos W (T ⊔ Z) ≤ friedrichsCos W T := by
  rw [← friedrichsCos_orthogonal W (T ⊔ Z), ← friedrichsCos_orthogonal W T,
    ← Submodule.inf_orthogonal]
  refine friedrichsCos_mono le_rfl inf_le_left fun x hx => ?_
  obtain ⟨hxW, hxT⟩ := Submodule.mem_inf.mp hx
  exact Submodule.mem_inf.mpr
    ⟨hxW, Submodule.mem_inf.mpr ⟨hxT, Submodule.orthogonal_le hZ hxW⟩⟩

/-- A vector of `W ⊔ T` orthogonal to `T` is `P_{Tᗮ} v` for some `v ∈ W` orthogonal to
`W ⊓ T`. -/
theorem exists_mem_eq_starProjection_orthogonal {W T : Submodule ℝ E} {u : E}
    (hu : u ∈ W ⊔ T) (hu' : u ∈ Tᗮ) :
    ∃ v ∈ W, v ∈ (W ⊓ T)ᗮ ∧ Tᗮ.starProjection v = u := by
  obtain ⟨w, hw, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
  have hQ : (W ⊓ T).starProjection w ∈ W ⊓ T := Submodule.starProjection_apply_mem _ _
  refine ⟨w - (W ⊓ T).starProjection w, W.sub_mem hw (Submodule.mem_inf.mp hQ).1,
    Submodule.sub_starProjection_mem_orthogonal w, ?_⟩
  have h1 : Tᗮ.starProjection (w + t) = w + t := Submodule.starProjection_eq_self_iff.mpr hu'
  have h2 : Tᗮ.starProjection t = 0 := Submodule.starProjection_orthogonal_apply_eq_zero ht
  have h3 : Tᗮ.starProjection ((W ⊓ T).starProjection w) = 0 :=
    Submodule.starProjection_orthogonal_apply_eq_zero (Submodule.mem_inf.mp hQ).2
  rw [map_sub, h3, sub_zero, ← h1, map_add, h2, add_zero]

/-- `⟪P_{Tᗮ} v₁, P_{Tᗮ} v₂⟫ = ⟪v₁, v₂⟫ - ⟪P_T v₁, P_T v₂⟫`. -/
theorem inner_starProjection_orthogonal (T : Submodule ℝ E) (v₁ v₂ : E) :
    ⟪Tᗮ.starProjection v₁, Tᗮ.starProjection v₂⟫_ℝ =
      ⟪v₁, v₂⟫_ℝ - ⟪T.starProjection v₁, T.starProjection v₂⟫_ℝ := by
  have h1 := Submodule.starProjection_add_starProjection_orthogonal (K := T) v₁
  have h2 := Submodule.starProjection_add_starProjection_orthogonal (K := T) v₂
  have c1 : ⟪T.starProjection v₁, Tᗮ.starProjection v₂⟫_ℝ = 0 :=
    Submodule.inner_right_of_mem_orthogonal (T.starProjection_apply_mem _)
      (Tᗮ.starProjection_apply_mem _)
  have c2 : ⟪Tᗮ.starProjection v₁, T.starProjection v₂⟫_ℝ = 0 :=
    Submodule.inner_left_of_mem_orthogonal (T.starProjection_apply_mem _)
      (Tᗮ.starProjection_apply_mem _)
  have e : ⟪v₁, v₂⟫_ℝ = ⟪T.starProjection v₁ + Tᗮ.starProjection v₁,
      T.starProjection v₂ + Tᗮ.starProjection v₂⟫_ℝ := by rw [h1, h2]
  rw [e, inner_add_left, inner_add_right, inner_add_right, c1, c2]
  ring

/-- **Lemma 4.2(a) when `W₁ ⊓ W₂ ≤ W₃`.** Here Kassabov's argument is complete: the vector
`v₂ ∈ W₂` orthogonal to `W₂ ⊓ W₃` is orthogonal to `W₁ ⊓ W₂`, and the one-sided bound
`abs_inner_le_friedrichsCos_of_right` needs nothing about `v₁`. -/
theorem kassabov_sup_of_inf_le {W₁ W₂ W₃ : Submodule ℝ E} (hZ : W₁ ⊓ W₂ ≤ W₃)
    {e₁₂ e₁₃ e₂₃ : ℝ} (h₁₂ : friedrichsCos W₁ W₂ ≤ e₁₂) (h₁₃ : friedrichsCos W₁ W₃ ≤ e₁₃)
    (h₂₃ : friedrichsCos W₂ W₃ ≤ e₂₃) (h₁₃' : e₁₃ < 1) (h₂₃' : e₂₃ < 1) :
    friedrichsCos (W₁ ⊔ W₃) (W₂ ⊔ W₃) ≤
      (e₁₂ + e₁₃ * e₂₃) / √((1 - e₁₃ ^ 2) * (1 - e₂₃ ^ 2)) := by
  have he₁₂ : 0 ≤ e₁₂ := (friedrichsCos_nonneg _ _).trans h₁₂
  have he₁₃ : 0 ≤ e₁₃ := (friedrichsCos_nonneg _ _).trans h₁₃
  have he₂₃ : 0 ≤ e₂₃ := (friedrichsCos_nonneg _ _).trans h₂₃
  have hd₁ : 0 < 1 - e₁₃ ^ 2 := by nlinarith
  have hd₂ : 0 < 1 - e₂₃ ^ 2 := by nlinarith
  set D := √((1 - e₁₃ ^ 2) * (1 - e₂₃ ^ 2)) with hD
  have hDpos : 0 < D := Real.sqrt_pos.mpr (mul_pos hd₁ hd₂)
  have hDsq : D ^ 2 = (1 - e₁₃ ^ 2) * (1 - e₂₃ ^ 2) := Real.sq_sqrt (mul_pos hd₁ hd₂).le
  have hK : 0 ≤ (e₁₂ + e₁₃ * e₂₃) / D := div_nonneg (by positivity) hDpos.le
  refine friedrichsCos_le_of_forall hK fun u₁ hu₁ u₂ hu₂ hu₁' hu₂' => ?_
  -- Both vectors are orthogonal to `W₃`.
  have hW₃ : W₃ ≤ (W₁ ⊔ W₃) ⊓ (W₂ ⊔ W₃) := le_inf le_sup_right le_sup_right
  obtain ⟨v₁, hv₁, hv₁', rfl⟩ :=
    exists_mem_eq_starProjection_orthogonal hu₁ (Submodule.orthogonal_le hW₃ hu₁')
  obtain ⟨v₂, hv₂, hv₂', rfl⟩ :=
    exists_mem_eq_starProjection_orthogonal hu₂ (Submodule.orthogonal_le hW₃ hu₂')
  -- Projection bounds `‖P_{W₃} vᵢ‖ ≤ eᵢ₃ ‖vᵢ‖`.
  have hp₁ : ‖W₃.starProjection v₁‖ ≤ e₁₃ * ‖v₁‖ :=
    (norm_starProjection_le_friedrichsCos' hv₁ hv₁').trans
      (mul_le_mul_of_nonneg_right h₁₃ (norm_nonneg _))
  have hp₂ : ‖W₃.starProjection v₂‖ ≤ e₂₃ * ‖v₂‖ :=
    (norm_starProjection_le_friedrichsCos' hv₂ hv₂').trans
      (mul_le_mul_of_nonneg_right h₂₃ (norm_nonneg _))
  -- `v₂ ⊥ W₁ ⊓ W₂`, so `|⟪v₁, v₂⟫| ≤ e₁₂ ‖v₁‖ ‖v₂‖`.
  have hv₂Z : v₂ ∈ (W₁ ⊓ W₂)ᗮ := Submodule.orthogonal_le (le_inf inf_le_right hZ) hv₂'
  have h12 : |⟪v₁, v₂⟫_ℝ| ≤ e₁₂ * ‖v₁‖ * ‖v₂‖ := by
    refine (abs_inner_le_friedrichsCos_of_right hv₁ hv₂ hv₂Z).trans ?_
    gcongr
  have h33 : |⟪W₃.starProjection v₁, W₃.starProjection v₂⟫_ℝ| ≤
      e₁₃ * e₂₃ * (‖v₁‖ * ‖v₂‖) := by
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖W₃.starProjection v₁‖ * ‖W₃.starProjection v₂‖
        ≤ (e₁₃ * ‖v₁‖) * (e₂₃ * ‖v₂‖) :=
          mul_le_mul hp₁ hp₂ (norm_nonneg _) (mul_nonneg he₁₃ (norm_nonneg _))
      _ = e₁₃ * e₂₃ * (‖v₁‖ * ‖v₂‖) := by ring
  have hinner : |⟪W₃ᗮ.starProjection v₁, W₃ᗮ.starProjection v₂⟫_ℝ| ≤
      (e₁₂ + e₁₃ * e₂₃) * (‖v₁‖ * ‖v₂‖) := by
    rw [inner_starProjection_orthogonal]
    calc |⟪v₁, v₂⟫_ℝ - ⟪W₃.starProjection v₁, W₃.starProjection v₂⟫_ℝ|
        ≤ |⟪v₁, v₂⟫_ℝ| + |⟪W₃.starProjection v₁, W₃.starProjection v₂⟫_ℝ| := abs_sub _ _
      _ ≤ e₁₂ * ‖v₁‖ * ‖v₂‖ + e₁₃ * e₂₃ * (‖v₁‖ * ‖v₂‖) := add_le_add h12 h33
      _ = (e₁₂ + e₁₃ * e₂₃) * (‖v₁‖ * ‖v₂‖) := by ring
  -- `‖uᵢ‖² ≥ (1 - eᵢ₃²) ‖vᵢ‖²`, hence `D ‖v₁‖ ‖v₂‖ ≤ ‖u₁‖ ‖u₂‖`.
  have hsq₁ : (1 - e₁₃ ^ 2) * ‖v₁‖ ^ 2 ≤ ‖W₃ᗮ.starProjection v₁‖ ^ 2 := by
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection v₁ W₃
    have := pow_le_pow_left₀ (norm_nonneg _) hp₁ 2
    nlinarith
  have hsq₂ : (1 - e₂₃ ^ 2) * ‖v₂‖ ^ 2 ≤ ‖W₃ᗮ.starProjection v₂‖ ^ 2 := by
    have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection v₂ W₃
    have := pow_le_pow_left₀ (norm_nonneg _) hp₂ 2
    nlinarith
  have hnorm : D * (‖v₁‖ * ‖v₂‖) ≤
      ‖W₃ᗮ.starProjection v₁‖ * ‖W₃ᗮ.starProjection v₂‖ := by
    have hsq : (D * (‖v₁‖ * ‖v₂‖)) ^ 2 ≤
        (‖W₃ᗮ.starProjection v₁‖ * ‖W₃ᗮ.starProjection v₂‖) ^ 2 := by
      calc (D * (‖v₁‖ * ‖v₂‖)) ^ 2
          = ((1 - e₁₃ ^ 2) * ‖v₁‖ ^ 2) * ((1 - e₂₃ ^ 2) * ‖v₂‖ ^ 2) := by
            rw [mul_pow, hDsq]; ring
        _ ≤ ‖W₃ᗮ.starProjection v₁‖ ^ 2 * ‖W₃ᗮ.starProjection v₂‖ ^ 2 :=
            mul_le_mul hsq₁ hsq₂ (by positivity) (by positivity)
        _ = (‖W₃ᗮ.starProjection v₁‖ * ‖W₃ᗮ.starProjection v₂‖) ^ 2 := by ring
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  calc |⟪W₃ᗮ.starProjection v₁, W₃ᗮ.starProjection v₂⟫_ℝ|
      ≤ (e₁₂ + e₁₃ * e₂₃) * (‖v₁‖ * ‖v₂‖) := hinner
    _ = (e₁₂ + e₁₃ * e₂₃) / D * (D * (‖v₁‖ * ‖v₂‖)) := by
      field_simp
    _ ≤ (e₁₂ + e₁₃ * e₂₃) / D * (‖W₃ᗮ.starProjection v₁‖ * ‖W₃ᗮ.starProjection v₂‖) := by
      gcongr
    _ = (e₁₂ + e₁₃ * e₂₃) / D * ‖W₃ᗮ.starProjection v₁‖ * ‖W₃ᗮ.starProjection v₂‖ := by
      ring

/-- **Kassabov's Lemma 4.2(a)**, in his form with upper bounds `eᵢⱼ` for the cosines:
`cos∠(W₁ ⊔ W₃, W₂ ⊔ W₃) ≤ (e₁₂ + e₁₃ e₂₃) / √((1 - e₁₃²)(1 - e₂₃²))`. -/
theorem kassabov_sup {W₁ W₂ W₃ : Submodule ℝ E} {e₁₂ e₁₃ e₂₃ : ℝ}
    (h₁₂ : friedrichsCos W₁ W₂ ≤ e₁₂) (h₁₃ : friedrichsCos W₁ W₃ ≤ e₁₃)
    (h₂₃ : friedrichsCos W₂ W₃ ≤ e₂₃) (h₁₃' : e₁₃ < 1) (h₂₃' : e₂₃ < 1) :
    friedrichsCos (W₁ ⊔ W₃) (W₂ ⊔ W₃) ≤
      (e₁₂ + e₁₃ * e₂₃) / √((1 - e₁₃ ^ 2) * (1 - e₂₃ ^ 2)) := by
  have hs₁ : W₁ ⊔ (W₃ ⊔ W₁ ⊓ W₂) = W₁ ⊔ W₃ := by
    rw [sup_comm W₃, ← sup_assoc, sup_eq_left.mpr (inf_le_left : W₁ ⊓ W₂ ≤ W₁)]
  have hs₂ : W₂ ⊔ (W₃ ⊔ W₁ ⊓ W₂) = W₂ ⊔ W₃ := by
    rw [sup_comm W₃, ← sup_assoc, sup_eq_left.mpr (inf_le_right : W₁ ⊓ W₂ ≤ W₂)]
  have h := kassabov_sup_of_inf_le (W₃ := W₃ ⊔ W₁ ⊓ W₂) le_sup_right h₁₂
    ((friedrichsCos_sup_le_of_le inf_le_left).trans h₁₃)
    ((friedrichsCos_sup_le_of_le inf_le_right).trans h₂₃) h₁₃' h₂₃'
  rwa [hs₁, hs₂] at h

/-- **Kassabov's Lemma 4.2(b)**, in his form with upper bounds `eᵢⱼ` for the cosines:
`cos∠(V₁ ⊓ V₃, V₂ ⊓ V₃) ≤ (e₁₂ + e₁₃ e₂₃) / √((1 - e₁₃²)(1 - e₂₃²))`. -/
theorem kassabov_inf {V₁ V₂ V₃ : Submodule ℝ E} {e₁₂ e₁₃ e₂₃ : ℝ}
    (h₁₂ : friedrichsCos V₁ V₂ ≤ e₁₂) (h₁₃ : friedrichsCos V₁ V₃ ≤ e₁₃)
    (h₂₃ : friedrichsCos V₂ V₃ ≤ e₂₃) (h₁₃' : e₁₃ < 1) (h₂₃' : e₂₃ < 1) :
    friedrichsCos (V₁ ⊓ V₃) (V₂ ⊓ V₃) ≤
      (e₁₂ + e₁₃ * e₂₃) / √((1 - e₁₃ ^ 2) * (1 - e₂₃ ^ 2)) := by
  have h := kassabov_sup (W₁ := V₁ᗮ) (W₂ := V₂ᗮ) (W₃ := V₃ᗮ) (e₁₂ := e₁₂) (e₁₃ := e₁₃)
    (e₂₃ := e₂₃) (by rwa [friedrichsCos_orthogonal]) (by rwa [friedrichsCos_orthogonal])
    (by rwa [friedrichsCos_orthogonal]) h₁₃' h₂₃'
  rwa [← orthogonal_inf_eq_sup, ← orthogonal_inf_eq_sup, friedrichsCos_orthogonal] at h

/-- **Kassabov's angle inequality** (`thm:kassabov`), exactly as stated in the paper: with
`εᵢⱼ = cos∠(Vᵢ, Vⱼ)`, if `ε₁₃ < 1` and `ε₂₃ < 1` then
`cos∠(V₁ ⊓ V₃, V₂ ⊓ V₃) ≤ (ε₁₂ + ε₁₃ ε₂₃) / √((1 - ε₁₃²)(1 - ε₂₃²))`. -/
theorem kassabov_angle_inequality (V₁ V₂ V₃ : Submodule ℝ E)
    (h₁₃ : friedrichsCos V₁ V₃ < 1) (h₂₃ : friedrichsCos V₂ V₃ < 1) :
    friedrichsCos (V₁ ⊓ V₃) (V₂ ⊓ V₃) ≤
      (friedrichsCos V₁ V₂ + friedrichsCos V₁ V₃ * friedrichsCos V₂ V₃) /
        √((1 - friedrichsCos V₁ V₃ ^ 2) * (1 - friedrichsCos V₂ V₃ ^ 2)) :=
  kassabov_inf le_rfl le_rfl le_rfl h₁₃ h₂₃

/-- **Kassabov's Lemma 4.2(a)** with the cosines themselves:
`cos∠(V₁ ⊔ V₃, V₂ ⊔ V₃) ≤ (ε₁₂ + ε₁₃ ε₂₃) / √((1 - ε₁₃²)(1 - ε₂₃²))`. -/
theorem kassabov_angle_inequality_sup (V₁ V₂ V₃ : Submodule ℝ E)
    (h₁₃ : friedrichsCos V₁ V₃ < 1) (h₂₃ : friedrichsCos V₂ V₃ < 1) :
    friedrichsCos (V₁ ⊔ V₃) (V₂ ⊔ V₃) ≤
      (friedrichsCos V₁ V₂ + friedrichsCos V₁ V₃ * friedrichsCos V₂ V₃) /
        √((1 - friedrichsCos V₁ V₃ ^ 2) * (1 - friedrichsCos V₂ V₃ ^ 2)) :=
  kassabov_sup le_rfl le_rfl le_rfl h₁₃ h₂₃

end Sarkozy.Angles

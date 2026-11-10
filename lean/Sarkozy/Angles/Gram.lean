module

public import Sarkozy.Angles.Elimination

/-!
# Gaussian elimination as Gram–Schmidt: the numbers `e_𝒴` of `lem:mid:allpin`

Let `m : P → F` be linearly independent vectors with Gram matrix `M = (⟪m x, m y⟫)`. For a
finite set `𝒴` of indices let `gramRes m 𝒴 x` be the residual of `m x` after projecting out
`span {m γ : γ ∈ 𝒴}`, and let
`gramE m 𝒴 x y = -⟪res x, res y⟫ / (‖res x‖ ‖res y‖)`.
These are the numbers `e_𝒴` of `lem:mid:allpin`. (The Gram matrix of the residuals is the Schur
complement of `M_{𝒴𝒴}` in `M`, so `gramE m 𝒴` is minus the normalized Schur complement; this
standard fact is a remark only and is not used. The formal proofs use the residuals
directly, which makes the independence of the elimination order automatic.)

* `gramE_empty`: `e_∅(x, y) = -M_{xy} / √(M_{xx} M_{yy})`.
* `gramE_lt_one`: `e_𝒴(x, y) < 1` for distinct `x, y ∉ 𝒴` (strict Cauchy–Schwarz).
* `gramE_insert`: eliminating one more index `γ` is Kassabov's recursion,
  `e_{𝒴 ∪ {γ}}(x, y) = F(e_𝒴(x, y), e_𝒴(x, γ), e_𝒴(y, γ))` (`gram_step`, the spherical-geometry
  identity behind Kassabov's §4.2).
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {P : Type*}

/-- The span of the vectors `m γ`, `γ ∈ 𝒴`. -/
def gramSpan (m : P → F) (𝒴 : Finset P) : Submodule ℝ F := Submodule.span ℝ (m '' ↑𝒴)

theorem mem_gramSpan {m : P → F} {𝒴 : Finset P} {x : P} (hx : x ∈ 𝒴) : m x ∈ gramSpan m 𝒴 :=
  Submodule.subset_span ⟨x, hx, rfl⟩

/-- `⟪g, r - (⟪r, g⟫ / ‖g‖²) • g⟫ = 0`. -/
theorem inner_sub_proj_eq_zero (r g : F) :
    ⟪g, r - (⟪r, g⟫_ℝ / ‖g‖ ^ 2) • g⟫_ℝ = 0 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, real_inner_comm g r]
  rcases eq_or_ne ‖g‖ 0 with h0 | h0
  · rw [norm_eq_zero.mp h0]
    simp
  · field_simp
    ring

variable [FiniteDimensional ℝ F]

/-- The residual of `m x` after projecting out the `m γ`, `γ ∈ 𝒴`. -/
noncomputable def gramRes (m : P → F) (𝒴 : Finset P) (x : P) : F :=
  (gramSpan m 𝒴)ᗮ.starProjection (m x)

/-- The elimination numbers: `e_𝒴(x, y) = -⟪res x, res y⟫ / (‖res x‖ ‖res y‖)`. -/
noncomputable def gramE (m : P → F) (𝒴 : Finset P) (x y : P) : ℝ :=
  -(⟪gramRes m 𝒴 x, gramRes m 𝒴 y⟫_ℝ / (‖gramRes m 𝒴 x‖ * ‖gramRes m 𝒴 y‖))

theorem gramRes_mem (m : P → F) (𝒴 : Finset P) (x : P) : gramRes m 𝒴 x ∈ (gramSpan m 𝒴)ᗮ :=
  Submodule.starProjection_apply_mem _ _

theorem sub_gramRes_mem (m : P → F) (𝒴 : Finset P) (x : P) :
    m x - gramRes m 𝒴 x ∈ gramSpan m 𝒴 := by
  rw [gramRes, Submodule.starProjection_orthogonal_val, sub_sub_cancel]
  exact Submodule.starProjection_apply_mem _ _

/-- A residual vanishes only if `m x` lies in the span. -/
theorem gramRes_eq_zero_iff (m : P → F) (𝒴 : Finset P) (v : F) :
    (gramSpan m 𝒴)ᗮ.starProjection v = 0 ↔ v ∈ gramSpan m 𝒴 := by
  rw [Submodule.starProjection_apply_eq_zero_iff, Submodule.orthogonal_orthogonal]

theorem gramRes_ne_zero {m : P → F} (hm : LinearIndependent ℝ m) {𝒴 : Finset P} {x : P}
    (hx : x ∉ 𝒴) : gramRes m 𝒴 x ≠ 0 := by
  intro h
  rw [gramRes, gramRes_eq_zero_iff] at h
  exact hm.notMem_span_image (s := (↑𝒴 : Set P)) (by simpa using hx) h

variable [DecidableEq P]

/-- **Strict Cauchy–Schwarz for residuals** of distinct indices outside `𝒴`. -/
theorem abs_inner_gramRes_lt {m : P → F} (hm : LinearIndependent ℝ m) {𝒴 : Finset P}
    {x y : P} (hx : x ∉ 𝒴) (hy : y ∉ 𝒴) (hxy : x ≠ y) :
    |⟪gramRes m 𝒴 x, gramRes m 𝒴 y⟫_ℝ| < ‖gramRes m 𝒴 x‖ * ‖gramRes m 𝒴 y‖ := by
  refine lt_of_le_of_ne (abs_real_inner_le_norm _ _) fun heq => ?_
  have h := (norm_inner_eq_norm_iff (𝕜 := ℝ) (gramRes_ne_zero hm hx)
    (gramRes_ne_zero hm hy)).mp (by rw [Real.norm_eq_abs]; exact heq)
  obtain ⟨r, -, hr⟩ := h
  -- `m y - r • m x` lies in the span of `m '' 𝒴`
  have h0 : (gramSpan m 𝒴)ᗮ.starProjection (m y - r • m x) = 0 := by
    rw [map_sub, map_smul]
    change gramRes m 𝒴 y - r • gramRes m 𝒴 x = 0
    rw [hr, sub_self]
  rw [gramRes_eq_zero_iff] at h0
  have hsub : gramSpan m 𝒴 ≤ Submodule.span ℝ (m '' ↑(insert x 𝒴)) :=
    Submodule.span_mono (Set.image_mono (by simp))
  have hmem : m y ∈ Submodule.span ℝ (m '' ↑(insert x 𝒴)) := by
    have : m y = (m y - r • m x) + r • m x := by abel
    rw [this]
    exact Submodule.add_mem _ (hsub h0)
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨x, by simp, rfl⟩))
  exact hm.notMem_span_image (s := (↑(insert x 𝒴) : Set P)) (by simp [hxy.symm, hy]) hmem

theorem gramE_lt_one {m : P → F} (hm : LinearIndependent ℝ m) {𝒴 : Finset P} {x y : P}
    (hx : x ∉ 𝒴) (hy : y ∉ 𝒴) (hxy : x ≠ y) : gramE m 𝒴 x y < 1 := by
  have hlt := abs_inner_gramRes_lt hm hx hy hxy
  have hpos : 0 < ‖gramRes m 𝒴 x‖ * ‖gramRes m 𝒴 y‖ :=
    mul_pos (norm_pos_iff.mpr (gramRes_ne_zero hm hx)) (norm_pos_iff.mpr (gramRes_ne_zero hm hy))
  rw [gramE, neg_div', div_lt_one hpos]
  exact (neg_le_abs _).trans_lt hlt

omit [DecidableEq P] in
theorem gramE_empty (m : P → F) (x y : P) :
    gramE m ∅ x y = -(⟪m x, m y⟫_ℝ / (‖m x‖ * ‖m y‖)) := by
  have hbot : gramSpan m ∅ = ⊥ := by
    rw [gramSpan, Finset.coe_empty, Set.image_empty, Submodule.span_empty]
  have h : ∀ z, gramRes m ∅ z = m z := fun z =>
    Submodule.starProjection_eq_self_iff.mpr (by
      rw [hbot, Submodule.bot_orthogonal_eq_top]
      exact Submodule.mem_top)
  rw [gramE, h, h]

/-- Adding `γ` to `𝒴` adds the residual of `m γ` to the span. -/
theorem gramSpan_insert (m : P → F) (𝒴 : Finset P) (γ : P) :
    gramSpan m (insert γ 𝒴) = gramSpan m 𝒴 ⊔ ℝ ∙ gramRes m 𝒴 γ := by
  have hins : gramSpan m (insert γ 𝒴) = ℝ ∙ m γ ⊔ gramSpan m 𝒴 := by
    rw [gramSpan, Finset.coe_insert, Set.image_insert_eq, Submodule.span_insert, gramSpan]
  rw [hins]
  apply le_antisymm
  · refine sup_le ?_ le_sup_left
    rw [Submodule.span_singleton_le_iff_mem]
    have : m γ = (m γ - gramRes m 𝒴 γ) + gramRes m 𝒴 γ := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (sub_gramRes_mem m 𝒴 γ))
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
  · refine sup_le le_sup_right ?_
    rw [Submodule.span_singleton_le_iff_mem]
    have : gramRes m 𝒴 γ = m γ - (m γ - gramRes m 𝒴 γ) := by abel
    rw [this]
    exact Submodule.sub_mem _ (Submodule.mem_sup_left (Submodule.mem_span_singleton_self _))
      (Submodule.mem_sup_right (sub_gramRes_mem m 𝒴 γ))

/-- **One Gram–Schmidt step**: the residual after eliminating `γ` as well is
`res x - (⟪res x, res γ⟫ / ‖res γ‖²) • res γ`. -/
theorem gramRes_insert (m : P → F) (𝒴 : Finset P) (γ x : P) :
    gramRes m (insert γ 𝒴) x = gramRes m 𝒴 x -
      (⟪gramRes m 𝒴 x, gramRes m 𝒴 γ⟫_ℝ / ‖gramRes m 𝒴 γ‖ ^ 2) • gramRes m 𝒴 γ := by
  refine Submodule.eq_starProjection_of_mem_orthogonal ?_ ?_
  · -- `r - c • g ∈ (A ⊔ ℝ ∙ g)ᗮ = Aᗮ ⊓ (ℝ ∙ g)ᗮ`
    rw [gramSpan_insert, ← Submodule.inf_orthogonal]
    refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem _ (gramRes_mem m 𝒴 x)
      (Submodule.smul_mem _ _ (gramRes_mem m 𝒴 γ)), ?_⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
    exact inner_sub_proj_eq_zero _ _
  · refine Submodule.le_orthogonal_orthogonal _ ?_
    rw [gramSpan_insert]
    have : m x - (gramRes m 𝒴 x - (⟪gramRes m 𝒴 x, gramRes m 𝒴 γ⟫_ℝ / ‖gramRes m 𝒴 γ‖ ^ 2) •
        gramRes m 𝒴 γ) = (m x - gramRes m 𝒴 x) +
        (⟪gramRes m 𝒴 x, gramRes m 𝒴 γ⟫_ℝ / ‖gramRes m 𝒴 γ‖ ^ 2) • gramRes m 𝒴 γ := by abel
    rw [this]
    exact Submodule.add_mem _ (Submodule.mem_sup_left (sub_gramRes_mem m 𝒴 x))
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))

omit [FiniteDimensional ℝ F] in
/-- **The spherical-geometry step** (Kassabov, §4.2): projecting `a` and `b` orthogonally to
`g` turns the negated cosines into Kassabov's recursion `F`. -/
theorem gram_step {a b g : F} (ha : a ≠ 0) (hb : b ≠ 0) (hg : g ≠ 0)
    (ha' : a - (⟪a, g⟫_ℝ / ‖g‖ ^ 2) • g ≠ 0) (hb' : b - (⟪b, g⟫_ℝ / ‖g‖ ^ 2) • g ≠ 0) :
    -(⟪a - (⟪a, g⟫_ℝ / ‖g‖ ^ 2) • g, b - (⟪b, g⟫_ℝ / ‖g‖ ^ 2) • g⟫_ℝ /
        (‖a - (⟪a, g⟫_ℝ / ‖g‖ ^ 2) • g‖ * ‖b - (⟪b, g⟫_ℝ / ‖g‖ ^ 2) • g‖)) =
      kassabovBound (-(⟪a, b⟫_ℝ / (‖a‖ * ‖b‖))) (-(⟪a, g⟫_ℝ / (‖a‖ * ‖g‖)))
        (-(⟪b, g⟫_ℝ / (‖b‖ * ‖g‖))) := by
  have hna : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnb : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hng : 0 < ‖g‖ := norm_pos_iff.mpr hg
  have hG : 0 < ‖g‖ ^ 2 := by positivity
  set a' := a - (⟪a, g⟫_ℝ / ‖g‖ ^ 2) • g with ha'def
  set b' := b - (⟪b, g⟫_ℝ / ‖g‖ ^ 2) • g with hb'def
  have hgg : ⟪g, g⟫_ℝ = ‖g‖ ^ 2 := real_inner_self_eq_norm_sq g
  -- inner products and norms after the projection
  have hi : ⟪a', b'⟫_ℝ = ⟪a, b⟫_ℝ - ⟪a, g⟫_ℝ * ⟪b, g⟫_ℝ / ‖g‖ ^ 2 := by
    rw [ha'def, hb'def, inner_sub_left, inner_sub_right, inner_sub_right, real_inner_smul_left,
      real_inner_smul_left, real_inner_smul_right, real_inner_smul_right, hgg,
      real_inner_comm b g]
    field_simp
    ring
  have hna' : ‖a'‖ ^ 2 = ‖a‖ ^ 2 - ⟪a, g⟫_ℝ * ⟪a, g⟫_ℝ / ‖g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq a, ha'def, inner_sub_left,
      inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, hgg, real_inner_comm a g]
    field_simp
    ring
  have hnb' : ‖b'‖ ^ 2 = ‖b‖ ^ 2 - ⟪b, g⟫_ℝ * ⟪b, g⟫_ℝ / ‖g‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq b, hb'def, inner_sub_left,
      inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, hgg, real_inner_comm b g]
    field_simp
    ring
  have hpa' : 0 < ‖a'‖ ^ 2 := by have := norm_pos_iff.mpr ha'; positivity
  have hpb' : 0 < ‖b'‖ ^ 2 := by have := norm_pos_iff.mpr hb'; positivity
  -- the hypotheses of `schur_normalize_aux`
  have hsa : √(‖a‖ ^ 2 * ‖g‖ ^ 2) = ‖a‖ * ‖g‖ := by
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have hsb : √(‖b‖ ^ 2 * ‖g‖ ^ 2) = ‖b‖ * ‖g‖ := by
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have hsab : √(‖a‖ ^ 2 * ‖b‖ ^ 2) = ‖a‖ * ‖b‖ := by
    rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have hca : (⟪a, g⟫_ℝ / √(‖a‖ ^ 2 * ‖g‖ ^ 2)) ^ 2 < 1 := by
    rw [hsa, div_pow, div_lt_one (by positivity)]
    have : ⟪a, g⟫_ℝ * ⟪a, g⟫_ℝ / ‖g‖ ^ 2 < ‖a‖ ^ 2 := by linarith
    rw [div_lt_iff₀ hG] at this
    nlinarith
  have hcb : (⟪b, g⟫_ℝ / √(‖b‖ ^ 2 * ‖g‖ ^ 2)) ^ 2 < 1 := by
    rw [hsb, div_pow, div_lt_one (by positivity)]
    have : ⟪b, g⟫_ℝ * ⟪b, g⟫_ℝ / ‖g‖ ^ 2 < ‖b‖ ^ 2 := by linarith
    rw [div_lt_iff₀ hG] at this
    nlinarith
  have key := schur_normalize_aux (a := ⟪a, b⟫_ℝ) (pow_pos hna 2) (pow_pos hnb 2) hG hca hcb
  rw [hsa, hsb, hsab] at key
  have hnn : ‖a'‖ * ‖b'‖ =
      √((‖a‖ ^ 2 - ⟪a, g⟫_ℝ * ⟪a, g⟫_ℝ / ‖g‖ ^ 2) * (‖b‖ ^ 2 - ⟪b, g⟫_ℝ * ⟪b, g⟫_ℝ / ‖g‖ ^ 2)) := by
    rw [← hna', ← hnb', ← mul_pow, Real.sqrt_sq (by positivity)]
  rw [hi, hnn, key, neg_neg]

/-- **Kassabov's recursion for the elimination numbers.** -/
theorem gramE_insert {m : P → F} (hm : LinearIndependent ℝ m) {𝒴 : Finset P} {γ x y : P}
    (hγ : γ ∉ 𝒴) (hx : x ∉ insert γ 𝒴) (hy : y ∉ insert γ 𝒴) :
    gramE m (insert γ 𝒴) x y =
      kassabovBound (gramE m 𝒴 x y) (gramE m 𝒴 x γ) (gramE m 𝒴 y γ) := by
  have hx𝒴 : x ∉ 𝒴 := fun h => hx (Finset.mem_insert_of_mem h)
  have hy𝒴 : y ∉ 𝒴 := fun h => hy (Finset.mem_insert_of_mem h)
  have hx' := gramRes_ne_zero hm hx
  have hy' := gramRes_ne_zero hm hy
  rw [gramRes_insert] at hx' hy'
  rw [gramE, gramRes_insert, gramRes_insert]
  exact gram_step (gramRes_ne_zero hm hx𝒴) (gramRes_ne_zero hm hy𝒴) (gramRes_ne_zero hm hγ)
    hx' hy'

end Sarkozy.Angles

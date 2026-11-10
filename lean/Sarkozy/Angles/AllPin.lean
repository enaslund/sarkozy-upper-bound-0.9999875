module

public import Sarkozy.Angles.Gram

/-!
# All partial pinnings: the abstract linear algebra of `lem:mid:allpin`

`lem:mid:allpin` (`paper/sections/13_cuts_correlations.tex`), for an abstract family of
subspaces `V[𝒴]` of a finite-dimensional real inner product space `E`, indexed by finite
sets `𝒴` of parts, with `V[𝒴] ⊓ V[𝒴'] = V[𝒴 ∪ 𝒴']`.

Let `Ē` be a symmetric matrix with zero diagonal such that `M = I - Ē` is the Gram matrix of
linearly independent vectors `m x` (equivalently, `M` is positive definite), and let
`Q = M⁻¹`. If `cos∠(V[{β}], V[{β'}]) ≤ Ē_{ββ'}` for distinct `β, β'`, then
`cos∠(V[𝒫 ∖ {β'}], V[𝒫 ∖ {β}]) ≤ Q_{ββ'} / √(Q_{ββ} Q_{β'β'})` (`allpin_gram`,
`allpin_matrix`), and so `≤ Q_{ββ'}` when `Q_{ββ'} ≥ 0` and `Q_{ββ}, Q_{β'β'} ≥ 1`
(`allpin_matrix_le`), which the paper gets from the Neumann series of `Q`.

The proof: the Claim (`allpin_claim_pair`) with `e = gramE m` (`Sarkozy.Angles.Gram`), and the
identification `gramE_pair`: after eliminating all of `𝒫 ∖ {β, β'}`, the residuals of `m β`
and `m β'` are the dual basis of the dual vectors `q x = ∑ z, Q x z • m z`, so
`e_{𝒫∖{β,β'}}(β, β') = Q_{ββ'} / √(Q_{ββ} Q_{β'β'})`. (In the paper's language: the Schur
complement of `M_{𝒴𝒴}` is the inverse of the `{β, β'}` block of `Q`.) The hypotheses on `m`
and `Q` are derived from `‖Ē‖ < 1` in `Sarkozy.Angles.AllPinNorm`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {P : Type*}

theorem mem_orthogonal_gramSpan {m : P → F} {𝒴 : Finset P} {v : F}
    (h : ∀ z ∈ 𝒴, ⟪m z, v⟫_ℝ = 0) : v ∈ (gramSpan m 𝒴)ᗮ := by
  have hle : gramSpan m 𝒴 ≤ (ℝ ∙ v)ᗮ := by
    rw [gramSpan, Submodule.span_le]
    rintro _ ⟨z, hz, rfl⟩
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.mpr (h z hz)
  rw [Submodule.mem_orthogonal]
  intro u hu
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp (hle hu)

variable [Fintype P] [DecidableEq P]

theorem sum_smul_mem_gramSpan (m : P → F) {β β' : P} (c : P → ℝ) (hβ : c β = 0)
    (hβ' : c β' = 0) : ∑ w, c w • m w ∈ gramSpan m (Finset.univ \ {β, β'}) := by
  refine Submodule.sum_mem _ fun w _ => ?_
  by_cases hw : w = β ∨ w = β'
  · rcases hw with rfl | rfl
    · rw [hβ, zero_smul]
      exact Submodule.zero_mem _
    · rw [hβ', zero_smul]
      exact Submodule.zero_mem _
  · obtain ⟨h1, h2⟩ := not_or.mp hw
    exact Submodule.smul_mem _ _ (mem_gramSpan (by simp [h1, h2]))

/-- The dual vectors `q x = ∑ z, Q x z • m z`. -/
noncomputable def dualVec (Q : Matrix P P ℝ) (m : P → F) (x : P) : F := ∑ z, Q x z • m z

theorem inner_dualVec_left {m : P → F} {Q : Matrix P P ℝ}
    (hQ : ∀ x y, ∑ z, Q x z * ⟪m z, m y⟫_ℝ = if x = y then 1 else 0) (x y : P) :
    ⟪dualVec Q m x, m y⟫_ℝ = if x = y then 1 else 0 := by
  rw [dualVec, sum_inner]
  simp_rw [real_inner_smul_left]
  exact hQ x y

theorem inner_dualVec_dualVec {m : P → F} {Q : Matrix P P ℝ}
    (hQ : ∀ x y, ∑ z, Q x z * ⟪m z, m y⟫_ℝ = if x = y then 1 else 0) (x y : P) :
    ⟪dualVec Q m x, dualVec Q m y⟫_ℝ = Q y x := by
  conv_lhs => rw [show dualVec Q m y = ∑ z, Q y z • m z from rfl, inner_sum]
  simp_rw [real_inner_smul_right, inner_dualVec_left hQ, mul_ite, mul_one, mul_zero]
  simp

/-- `m x - (s • q β + t • q β')` in coordinates. -/
theorem sub_dualVec_eq_sum (m : P → F) (Q : Matrix P P ℝ) (x β β' : P) (s t : ℝ) :
    m x - (s • dualVec Q m β + t • dualVec Q m β') =
      ∑ w, ((if w = x then 1 else 0) - (s * Q β w + t * Q β' w)) • m w := by
  have h1 : ∑ w, (if w = x then (1 : ℝ) else 0) • m w = m x := by
    simp only [ite_smul, one_smul, zero_smul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  have h2 : ∑ w, ((if w = x then (1 : ℝ) else 0) - (s * Q β w + t * Q β' w)) • m w =
      ∑ w, (if w = x then (1 : ℝ) else 0) • m w -
        (s • ∑ w, Q β w • m w + t • ∑ w, Q β' w • m w) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [sub_smul, add_smul, mul_smul, mul_smul]
  rw [h2, h1]
  rfl

variable [FiniteDimensional ℝ F]

omit [Fintype P] [DecidableEq P] in
theorem gramRes_eq_of_mem {m : P → F} {𝒴 : Finset P} {x : P} {r : F}
    (hr : r ∈ (gramSpan m 𝒴)ᗮ) (h : m x - r ∈ gramSpan m 𝒴) : gramRes m 𝒴 x = r :=
  Submodule.eq_starProjection_of_mem_orthogonal hr (Submodule.le_orthogonal_orthogonal _ h)

/-- **The last elimination number.** After eliminating `𝒫 ∖ {β, β'}`,
`e(β, β') = Q_{ββ'} / √(Q_{ββ} Q_{β'β'})`, where `Q` is the inverse of the Gram matrix. -/
theorem gramE_pair {m : P → F} {Q : Matrix P P ℝ}
    (hQ : ∀ x y, ∑ z, Q x z * ⟪m z, m y⟫_ℝ = if x = y then 1 else 0)
    (hQs : ∀ x y, Q x y = Q y x) {β β' : P} (hne : β ≠ β') :
    gramE m (Finset.univ \ {β, β'}) β β' = Q β β' / √(Q β β * Q β' β') := by
  set 𝒴 : Finset P := Finset.univ \ {β, β'} with h𝒴
  set q := dualVec Q m with hqdef
  have hqq : ∀ x y, ⟪q x, q y⟫_ℝ = Q y x := inner_dualVec_dualVec hQ
  have hqm : ∀ x y, ⟪q x, m y⟫_ℝ = if x = y then 1 else 0 := inner_dualVec_left hQ
  -- `q β, q β' ⊥ m z` for `z ∈ 𝒴`
  have hq𝒴 : ∀ x, x = β ∨ x = β' → q x ∈ (gramSpan m 𝒴)ᗮ := by
    intro x hx
    refine mem_orthogonal_gramSpan fun z hz => ?_
    rw [real_inner_comm, hqm]
    have hxz : x ≠ z := by
      rintro rfl
      simp only [h𝒴, Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton] at hz
      exact hz hx
    simp [hxz]
  -- `q β` and `q β'` are not parallel, so `Δ = Q_ββ Q_β'β' - Q_ββ'² > 0`.
  have hqβ0 : q β ≠ 0 := by
    intro h0
    have := hqm β β
    rw [h0, inner_zero_left] at this
    simp at this
  have hqβ'0 : q β' ≠ 0 := by
    intro h0
    have := hqm β' β'
    rw [h0, inner_zero_left] at this
    simp at this
  have hstrict : |⟪q β, q β'⟫_ℝ| < ‖q β‖ * ‖q β'‖ := by
    refine lt_of_le_of_ne (abs_real_inner_le_norm _ _) fun heq => ?_
    obtain ⟨r, -, hr⟩ := (norm_inner_eq_norm_iff (𝕜 := ℝ) hqβ0 hqβ'0).mp
      (by rw [Real.norm_eq_abs]; exact heq)
    have h1 := hqm β' β'
    rw [hr, real_inner_smul_left, hqm β β', ite_eq_right hne] at h1
    simp at h1
  have ha : ‖q β‖ ^ 2 = Q β β := by rw [← real_inner_self_eq_norm_sq, hqq]
  have hd : ‖q β'‖ ^ 2 = Q β' β' := by rw [← real_inner_self_eq_norm_sq, hqq]
  have hb : ⟪q β, q β'⟫_ℝ = Q β β' := by rw [hqq, hQs]
  have hapos : 0 < Q β β := by rw [← ha]; exact pow_pos (norm_pos_iff.mpr hqβ0) 2
  have hdpos : 0 < Q β' β' := by rw [← hd]; exact pow_pos (norm_pos_iff.mpr hqβ'0) 2
  have hΔ : 0 < Q β β * Q β' β' - Q β β' ^ 2 := by
    have h2 : |⟪q β, q β'⟫_ℝ| ^ 2 < (‖q β‖ * ‖q β'‖) ^ 2 :=
      pow_lt_pow_left₀ hstrict (abs_nonneg _) two_ne_zero
    rw [sq_abs, hb, mul_pow, ha, hd] at h2
    linarith
  set a := Q β β with hadef
  set b := Q β β' with hbdef
  set d := Q β' β' with hddef
  set Δ := a * d - b ^ 2 with hΔdef
  have hba : Q β' β = b := hQs β' β
  -- the residuals are explicit combinations of `q β` and `q β'`
  have hrβ : gramRes m 𝒴 β = (d / Δ) • q β + (-b / Δ) • q β' := by
    refine gramRes_eq_of_mem (Submodule.add_mem _
      (Submodule.smul_mem _ _ (hq𝒴 β (Or.inl rfl)))
      (Submodule.smul_mem _ _ (hq𝒴 β' (Or.inr rfl)))) ?_
    rw [hqdef, sub_dualVec_eq_sum]
    refine sum_smul_mem_gramSpan m _ ?_ ?_
    · rw [ite_eq_left rfl, ← hadef, hba]
      field_simp
      ring
    · rw [ite_eq_right hne.symm, ← hbdef, ← hddef]
      field_simp
      ring
  have hrβ' : gramRes m 𝒴 β' = (-b / Δ) • q β + (a / Δ) • q β' := by
    refine gramRes_eq_of_mem (Submodule.add_mem _
      (Submodule.smul_mem _ _ (hq𝒴 β (Or.inl rfl)))
      (Submodule.smul_mem _ _ (hq𝒴 β' (Or.inr rfl)))) ?_
    rw [hqdef, sub_dualVec_eq_sum]
    refine sum_smul_mem_gramSpan m _ ?_ ?_
    · rw [ite_eq_right hne, ← hadef, hba]
      field_simp
      ring
    · rw [ite_eq_left rfl, ← hbdef, ← hddef]
      field_simp
      ring
  -- their Gram matrix
  have hip : ∀ s t s' t' : ℝ, ⟪s • q β + t • q β', s' • q β + t' • q β'⟫_ℝ =
      s * s' * a + s * t' * b + t * s' * b + t * t' * d := by
    intro s t s' t'
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right,
      hqq, hba]
    ring
  have h12 : ⟪gramRes m 𝒴 β, gramRes m 𝒴 β'⟫_ℝ = -b / Δ := by
    rw [hrβ, hrβ', hip]
    field_simp
    ring
  have h11 : ‖gramRes m 𝒴 β‖ ^ 2 = d / Δ := by
    rw [← real_inner_self_eq_norm_sq, hrβ, hip]
    field_simp
    ring
  have h22 : ‖gramRes m 𝒴 β'‖ ^ 2 = a / Δ := by
    rw [← real_inner_self_eq_norm_sq, hrβ', hip]
    field_simp
    ring
  set N := ‖gramRes m 𝒴 β‖ * ‖gramRes m 𝒴 β'‖ with hNdef
  have hN0 : 0 ≤ N := by positivity
  have hN2 : N ^ 2 = a * d / Δ ^ 2 := by
    rw [hNdef, mul_pow, h11, h22]
    field_simp
  have hsq : √(a * d) = Δ * N := by
    have : a * d = (Δ * N) ^ 2 := by
      rw [mul_pow, hN2]
      field_simp
    rw [this, Real.sqrt_sq (by positivity)]
  have hNpos : 0 < N := by
    rcases hN0.eq_or_lt with h | h
    · exfalso
      rw [← h] at hN2
      have h3 : 0 < a * d / Δ ^ 2 := div_pos (mul_pos hapos hdpos) (pow_pos hΔ 2)
      rw [← hN2] at h3
      simp at h3
    · exact h
  rw [gramE, h12, ← hNdef, hsq]
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- **`lem:mid:allpin`, abstract form with Gram vectors.** Let `V[𝒴]` satisfy
`V[𝒴] ⊓ V[𝒴'] = V[𝒴 ∪ 𝒴']`; let `m` be linearly independent unit vectors with
`⟪m x, m y⟫ = -Ē_{xy}` for `x ≠ y` (so `I - Ē` is their Gram matrix), `Q` its inverse, and
`cos∠(V[{β}], V[{β'}]) ≤ Ē_{ββ'}`. Then
`cos∠(V[𝒫 ∖ {β'}], V[𝒫 ∖ {β}]) ≤ Q_{ββ'} / √(Q_{ββ} Q_{β'β'})`. -/
theorem allpin_gram (V : Finset P → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset P, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    {m : P → F} (hm : LinearIndependent ℝ m) (Ebar : Matrix P P ℝ)
    (hunit : ∀ x, ‖m x‖ = 1) (hgram : ∀ x y, x ≠ y → ⟪m x, m y⟫_ℝ = -Ebar x y)
    (hcos : ∀ β β', β ≠ β' → friedrichsCos (V {β}) (V {β'}) ≤ Ebar β β')
    {Q : Matrix P P ℝ} (hQ : ∀ x y, ∑ z, Q x z * ⟪m z, m y⟫_ℝ = if x = y then 1 else 0)
    (hQs : ∀ x y, Q x y = Q y x) {β β' : P} (hne : β ≠ β') :
    friedrichsCos (V (Finset.univ \ {β'})) (V (Finset.univ \ {β})) ≤
      Q β β' / √(Q β β * Q β' β') := by
  have h := allpin_claim_pair V hV (gramE m)
    (fun x y hxy => by
      rw [gramE_empty, hgram x y hxy, hunit, hunit, mul_one, div_one, neg_neg]
      exact hcos x y hxy)
    (fun _ _ _ hx hy hxy => gramE_lt_one hm hx hy hxy)
    (fun _ _ _ _ hγ hx hy _ => (gramE_insert hm hγ hx hy).ge) hne
  rwa [gramE_pair hQ hQs hne] at h

/-- **`lem:mid:allpin`, matrix form.** As `allpin_gram`, with the hypotheses on `m` and `Q`
stated as matrix identities: `gram m = 1 - Ē`, `Ē` with zero diagonal, `Q (1 - Ē) = 1` and
`Q` symmetric. -/
theorem allpin_matrix (V : Finset P → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset P, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    {m : P → F} (hm : LinearIndependent ℝ m) (Ebar : Matrix P P ℝ)
    (hgram : ∀ x y, ⟪m x, m y⟫_ℝ = (1 - Ebar) x y) (hdiag : ∀ x, Ebar x x = 0)
    (hcos : ∀ β β', β ≠ β' → friedrichsCos (V {β}) (V {β'}) ≤ Ebar β β')
    {Q : Matrix P P ℝ} (hQ : Q * (1 - Ebar) = 1) (hQs : Q.IsSymm) {β β' : P} (hne : β ≠ β') :
    friedrichsCos (V (Finset.univ \ {β'})) (V (Finset.univ \ {β})) ≤
      Q β β' / √(Q β β * Q β' β') := by
  have hunit : ∀ x, ‖m x‖ = 1 := fun x => by
    have h := hgram x x
    rw [real_inner_self_eq_norm_sq, Matrix.sub_apply, Matrix.one_apply_eq, hdiag, sub_zero] at h
    have h0 := norm_nonneg (m x)
    nlinarith
  have hoff : ∀ x y, x ≠ y → ⟪m x, m y⟫_ℝ = -Ebar x y := fun x y hxy => by
    rw [hgram, Matrix.sub_apply, Matrix.one_apply_ne hxy, zero_sub]
  have hQ' : ∀ x y, ∑ z, Q x z * ⟪m z, m y⟫_ℝ = if x = y then 1 else 0 := fun x y => by
    simp_rw [hgram]
    rw [← Matrix.mul_apply, hQ, Matrix.one_apply]
  have hQs' : ∀ x y, Q x y = Q y x := fun x y => by
    rw [← Matrix.transpose_apply Q y x, hQs.eq]
  exact allpin_gram V hV hm Ebar hunit hoff hcos hQ' hQs' hne

/-- **`lem:mid:allpin`, final bound.** If moreover `Q_{ββ'} ≥ 0` and `Q_{ββ}, Q_{β'β'} ≥ 1`
(which the paper reads off the Neumann series `Q = ∑ Ēᵏ` of a nonnegative `Ē`), then
`cos∠(V[𝒫 ∖ {β'}], V[𝒫 ∖ {β}]) ≤ Q_{ββ'}`. -/
theorem allpin_matrix_le (V : Finset P → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset P, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    {m : P → F} (hm : LinearIndependent ℝ m) (Ebar : Matrix P P ℝ)
    (hgram : ∀ x y, ⟪m x, m y⟫_ℝ = (1 - Ebar) x y) (hdiag : ∀ x, Ebar x x = 0)
    (hcos : ∀ β β', β ≠ β' → friedrichsCos (V {β}) (V {β'}) ≤ Ebar β β')
    {Q : Matrix P P ℝ} (hQ : Q * (1 - Ebar) = 1) (hQs : Q.IsSymm) {β β' : P} (hne : β ≠ β')
    (hQ0 : 0 ≤ Q β β') (hQ1 : 1 ≤ Q β β) (hQ1' : 1 ≤ Q β' β') :
    friedrichsCos (V (Finset.univ \ {β'})) (V (Finset.univ \ {β})) ≤ Q β β' := by
  refine (allpin_matrix V hV hm Ebar hgram hdiag hcos hQ hQs hne).trans ?_
  have h1 : 1 ≤ √(Q β β * Q β' β') := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by nlinarith)
  exact div_le_self hQ0 h1

end Sarkozy.Angles

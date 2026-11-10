module

public import Sarkozy.EnvelopeSteps.WitnessBridge
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# The domination `±L_ω ⪯ D_ω` for the checked diagonal envelopes, without move 1
(`lem:oct24:mask-schur`(a), (c), `cert:envelopes`(b); Step 2 of `thm:envelopes`(i))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`. B11's `hdom_of_mask` derives the input
`hdom` of `DegreeOps` (`±L_ω ⪯ D_ω` in `L²(m_ω)`) from move 1 (`hspec`, the joint spectral
decomposition), move 4 (`hLift`) and the identification of the kernels. For a **diagonal** envelope
move 1 is not needed: part (c) of the lemma (the mask Schur test) bounds the tensor of the stars on
every sector directly. **`hdom_of_table`** is `hdom_of_mask` with `hspec` replaced by W2's checked
table (`tablePos`, `maskCheck`; for the five witnesses F6E0, F5E1, F4E2, F3E3, F2E4 W2's
`*_tablePos`, `*_maskCheck`) and the sector structure of the tensor of the stars on each singleton
sector `s`:

* `hsec`: `T_s((w, ·), (v, ·)) = 0` unless the masks of `v` and `w` are complementary (a star maps
  its centre to its arms and back);
* `hnorm`: the block `T_s((w, ·), (v, ·))` has norm at most `α(v) α(w)` (the products of the arm
  norm bounds);
* `hTs`: `T_s` is symmetric (an even tensor of skew stars).

The other hypotheses are B11's: `0 ≤ c_s ≤ 1`; `hLift` (move 4, e.g. `hLift_of_blocks`) for the
diagonal matrix `D = diag(d_v)` of the table's weights on the tensor features `Feat n k` (the
features outside the stars carry the weight `0`, the paper's "extended by any nonnegative
weights"); and the kernels of `L_ω` and `D_ω` relative to `m_ω`.

The proof: for every `ξ`, with `y_s = Ξ_sᵀ ξ`, `ξᵀ L ξ = ∑_s c_s y_sᵀ T_s y_s` and
`|y_sᵀ T_s y_s| ≤ ∑_v d_v ‖y_s(v, ·)‖² = y_sᵀ (D ⊗ I) y_s` (W2's `checked_table_envelope` in
`EuclideanSpace ℝ (Z s)`), so `|ξᵀ L ξ| ≤ ξᵀ (∑_s Ξ_s (D ⊗ I) Ξ_sᵀ) ξ ≤ ξᵀ Lift ξ`; B11's
`opLE_of_mask` concludes.
-/

open Finset Matrix
open scoped BigOperators Kronecker RealInnerProductSpace

namespace Sarkozy.OpsFeature

open Sarkozy.EnvelopeSteps Sarkozy.Envelopes

/-- A matrix as a linear map of `EuclideanSpace`. -/
noncomputable def eucLin {Z : Type*} [Fintype Z] (M : Matrix Z Z ℝ) :
    EuclideanSpace ℝ Z →ₗ[ℝ] EuclideanSpace ℝ Z where
  toFun y := WithLp.toLp 2 (M *ᵥ WithLp.ofLp y)
  map_add' a b := by
    rw [WithLp.ofLp_add, Matrix.mulVec_add, WithLp.toLp_add]
  map_smul' c a := by
    rw [WithLp.ofLp_smul, Matrix.mulVec_smul, WithLp.toLp_smul, RingHom.id_apply]

theorem inner_eucLin {Z : Type*} [Fintype Z] (M : Matrix Z Z ℝ) (a b : Z → ℝ) :
    ⟪WithLp.toLp 2 a, eucLin M (WithLp.toLp 2 b)⟫ = ∑ z, a z * ∑ z', M z z' * b z' := by
  change ⟪WithLp.toLp 2 a, WithLp.toLp 2 (M *ᵥ b)⟫ = _
  rw [EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, star_trivial, mulVec]
  exact sum_congr rfl fun z _ => by ring

theorem norm_toLp_sq {Z : Type*} [Fintype Z] (a : Z → ℝ) :
    ‖(WithLp.toLp 2 a : EuclideanSpace ℝ Z)‖ ^ 2 = ∑ z, a z ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_toLp_toLp]
  simp only [dotProduct, star_trivial]
  exact sum_congr rfl fun z _ => by ring

/-- The quadratic form of a congruence: `ξᵀ (A B Aᵀ) ξ = (Aᵀξ)ᵀ B (Aᵀξ)`. -/
theorem form_congr {O W : Type*} [Fintype O] [Fintype W] (A : Matrix O W ℝ) (B : Matrix W W ℝ)
    (ξ : O → ℝ) :
    star ξ ⬝ᵥ ((A * B * Aᴴ) *ᵥ ξ) = star (Aᴴ *ᵥ ξ) ⬝ᵥ (B *ᵥ (Aᴴ *ᵥ ξ)) := by
  rw [← mulVec_mulVec, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec, conjTranspose_conjTranspose]

section Table

variable {Tb : EnvTable} {n k : ℕ} {Z : Type*} [Fintype Z] [DecidableEq Z]

omit [Fintype Z] in
/-- The form of `D ⊗ I` for the diagonal `D = diag(d)`: `∑_v d_v ∑_z y(v, z)²`. -/
theorem form_diag_kron {W : Type*} [Fintype W] [DecidableEq W] [Fintype Z] (d : W → ℝ)
    (y : W × Z → ℝ) :
    star y ⬝ᵥ ((diagonal d ⊗ₖ (1 : Matrix Z Z ℝ)) *ᵥ y) = ∑ v, d v * ∑ z, y (v, z) ^ 2 := by
  simp only [dotProduct, mulVec, star_trivial, kroneckerMap_apply, diagonal_apply, one_apply,
    Fintype.sum_prod_type]
  refine sum_congr rfl fun v _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun z _ => ?_
  simp only [ite_mul, zero_mul, mul_ite, mul_one, mul_zero]
  rw [sum_eq_single v]
  · rw [sum_eq_single z]
    · simp; ring
    · intro z' _ hz; simp [Ne.symm hz]
    · simp
  · intro v' _ hv
    refine sum_eq_zero fun z' _ => ?_
    simp [Ne.symm hv]
  · simp

omit [DecidableEq Z] in
/-- The form of a block matrix on `W × Z`, block by block. -/
theorem form_blocks {W : Type*} [Fintype W] (T : Matrix (W × Z) (W × Z) ℝ) (y : W × Z → ℝ) :
    star y ⬝ᵥ (T *ᵥ y) = ∑ v, ∑ w, ∑ z, y (w, z) * ∑ z', T (w, z) (v, z') * y (v, z') := by
  simp only [dotProduct, mulVec, star_trivial, Fintype.sum_prod_type, mul_sum]
  simp only [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv
    { toFun := fun t : W × Z × W × Z => (t.2.2.1, t.1, t.2.1, t.2.2.2)
      invFun := fun u : W × W × Z × Z => (u.2.1, u.2.2.1, u.1, u.2.2.2)
      left_inv := fun t => rfl
      right_inv := fun u => rfl } _ _ (fun t => rfl)

omit [DecidableEq Z] in
/-- **The mask Schur test on one sector, in matrix form**: for a checked table and a sector matrix
`T` with the star's sector structure and block norms, `|yᵀ T y| ≤ ∑_v d_v ‖y(v, ·)‖²`. -/
theorem form_table_le (hT : tablePos Tb n k = true) (hC : maskCheck Tb n k = true)
    (T : Matrix (Feat n k × Z) (Feat n k × Z) ℝ)
    (hsec : ∀ v w z z', featMask w ≠ maskCompl (featMask v) → T (w, z) (v, z') = 0)
    (hnorm : ∀ v w (y : Z → ℝ), ∑ z, (∑ z', T (w, z) (v, z') * y z') ^ 2 ≤
      ((featAlpha v : ℝ) * featAlpha w) ^ 2 * ∑ z, y z ^ 2)
    (y : Feat n k × Z → ℝ) :
    |star y ⬝ᵥ (T *ᵥ y)| ≤ ∑ v, (featWeight Tb v : ℝ) * ∑ z, y (v, z) ^ 2 := by
  set Top : Feat n k → Feat n k → EuclideanSpace ℝ Z →ₗ[ℝ] EuclideanSpace ℝ Z :=
    fun w v => eucLin (Matrix.of fun z z' => T (w, z) (v, z')) with hTop
  set x : Feat n k → EuclideanSpace ℝ Z := fun v => WithLp.toLp 2 (fun z => y (v, z)) with hx
  have hsec' : ∀ v w, featMask w ≠ maskCompl (featMask v) → Top w v = 0 := by
    intro v w h
    apply LinearMap.ext
    intro a
    simp only [hTop, LinearMap.zero_apply]
    change WithLp.toLp 2 _ = 0
    have : (Matrix.of fun z z' => T (w, z) (v, z')) *ᵥ WithLp.ofLp a = 0 := by
      funext z
      simp only [mulVec, dotProduct, Matrix.of_apply, hsec v w z _ h, zero_mul, sum_const_zero,
        Pi.zero_apply]
    rw [this]
    rfl
  have hα : ∀ v : Feat n k, (0 : ℝ) ≤ featAlpha v := fun v => by
    exact_mod_cast featAlpha_nonneg v
  have hnorm' : ∀ v w a, ‖Top w v a‖ ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖a‖ := by
    intro v w a
    have h1 : ‖Top w v a‖ ^ 2 = ∑ z, (∑ z', T (w, z) (v, z') * WithLp.ofLp a z') ^ 2 := by
      change ‖(WithLp.toLp 2 _ : EuclideanSpace ℝ Z)‖ ^ 2 = _
      rw [norm_toLp_sq]
      rfl
    have h2 : ‖a‖ ^ 2 = ∑ z, WithLp.ofLp a z ^ 2 := by
      rw [← norm_toLp_sq]
    have h3 := hnorm v w (WithLp.ofLp a)
    rw [← h1, ← h2] at h3
    have hc : 0 ≤ (featAlpha v : ℝ) * (featAlpha w : ℝ) * ‖a‖ :=
      mul_nonneg (mul_nonneg (hα v) (hα w)) (norm_nonneg _)
    rw [← abs_of_nonneg (norm_nonneg (Top w v a)), ← abs_of_nonneg hc]
    exact sq_le_sq.mp (by rw [mul_pow]; exact h3)
  have hb := checked_table_envelope hT hC Top hsec' hnorm' x
  have hform : star y ⬝ᵥ (T *ᵥ y) = ∑ v, ∑ w, ⟪x w, Top w v (x v)⟫ := by
    simp only [hx, hTop, inner_eucLin, Matrix.of_apply]
    exact form_blocks T y
  have hnx : ∀ v, ‖x v‖ ^ 2 = ∑ z, y (v, z) ^ 2 := fun v => norm_toLp_sq _
  rw [hform]
  simpa only [hnx] using hb

end Table

/-- **`hdom` for a checked diagonal envelope, without move 1** (`lem:oct24:mask-schur`(a), (c),
`cert:envelopes`(b)): B11's `hdom_of_mask` with the joint spectral hypothesis `hspec` replaced by
the checked table and the sector structure of the tensor of the stars. The conclusion is the input
`hdom` of `EnvelopeSteps.DegreeOps` (`±L_ω ⪯ D_ω` in `L²(m_ω)`). -/
theorem hdom_of_table {O : Type*} [Fintype O] [DecidableEq O] {Tb : EnvTable} {n k : ℕ}
    (hT : tablePos Tb n k = true) (hC : maskCheck Tb n k = true)
    {S : Type*} [Fintype S] {Z : S → Type*} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
    (T : ∀ s, Matrix (Feat n k × Z s) (Feat n k × Z s) ℝ) (cs : S → ℝ)
    (hc0 : ∀ s, 0 ≤ cs s) (hc1 : ∀ s, cs s ≤ 1) (hTs : ∀ s, (T s).IsHermitian)
    (hsec : ∀ s v w z z', featMask w ≠ maskCompl (featMask v) → T s (w, z) (v, z') = 0)
    (hnorm : ∀ s v w (y : Z s → ℝ), ∑ z, (∑ z', T s (w, z) (v, z') * y z') ^ 2 ≤
      ((featAlpha v : ℝ) * featAlpha w) ^ 2 * ∑ z, y z ^ 2)
    (Ξ : ∀ s, Matrix O (Feat n k × Z s) ℝ) (Lift : Matrix O O ℝ)
    (hLift : (Lift - ∑ s, Ξ s * (diagonal (fun v => (featWeight Tb v : ℝ)) ⊗ₖ
      (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ).PosSemidef)
    {m : O → ℝ} {Lead Lop : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (hL : ∀ x y, kern m Lead x y = (∑ s, cs s • (Ξ s * T s * (Ξ s)ᴴ)) x y)
    (hLop : ∀ x y, kern m Lop x y = Lift x y) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop := by
  set d : Feat n k → ℝ := fun v => (featWeight Tb v : ℝ) with hd
  set Sg : Matrix O O ℝ := ∑ s, Ξ s * (diagonal d ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ
    with hSg
  set Lm : Matrix O O ℝ := ∑ s, cs s • (Ξ s * T s * (Ξ s)ᴴ) with hLm
  have hd0 : ∀ v, 0 ≤ d v := fun v => by
    simp only [hd]; exact_mod_cast (featWeight_pos hT v).le
  -- the quadratic forms
  have hQS : ∀ ξ : O → ℝ, star ξ ⬝ᵥ (Sg *ᵥ ξ) =
      ∑ s, ∑ v, d v * ∑ z, ((Ξ s)ᴴ *ᵥ ξ) (v, z) ^ 2 := by
    intro ξ
    simp only [hSg, Matrix.sum_mulVec, dotProduct_sum, form_congr, form_diag_kron]
  have hQL : ∀ ξ : O → ℝ, |star ξ ⬝ᵥ (Lm *ᵥ ξ)| ≤ star ξ ⬝ᵥ (Sg *ᵥ ξ) := by
    intro ξ
    rw [hQS]
    simp only [hLm, Matrix.sum_mulVec, dotProduct_sum, Matrix.smul_mulVec, dotProduct_smul,
      form_congr]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun s _ => ?_)
    have h := form_table_le hT hC (T s) (hsec s) (hnorm s) ((Ξ s)ᴴ *ᵥ ξ)
    have hQ0 : 0 ≤ ∑ v, d v * ∑ z, ((Ξ s)ᴴ *ᵥ ξ) (v, z) ^ 2 :=
      sum_nonneg fun v _ => mul_nonneg (hd0 v) (sum_nonneg fun z _ => sq_nonneg _)
    rw [smul_eq_mul, abs_mul, abs_of_nonneg (hc0 s)]
    calc cs s * |star ((Ξ s)ᴴ *ᵥ ξ) ⬝ᵥ (T s *ᵥ ((Ξ s)ᴴ *ᵥ ξ))|
        ≤ cs s * ∑ v, d v * ∑ z, ((Ξ s)ᴴ *ᵥ ξ) (v, z) ^ 2 :=
          mul_le_mul_of_nonneg_left h (hc0 s)
      _ ≤ 1 * ∑ v, d v * ∑ z, ((Ξ s)ᴴ *ᵥ ξ) (v, z) ^ 2 :=
          mul_le_mul_of_nonneg_right (hc1 s) hQ0
      _ = _ := one_mul _
  -- the Hermitian parts
  have hSgh : Sg.IsHermitian := by
    rw [IsHermitian, hSg, conjTranspose_sum]
    refine sum_congr rfl fun s _ => (isHermitian_mul_mul_conjTranspose (Ξ s) ?_).eq
    rw [IsHermitian, conjTranspose_kronecker, diagonal_conjTranspose, conjTranspose_one]
    congr 2
  have hLmh : Lm.IsHermitian := by
    rw [IsHermitian, hLm, conjTranspose_sum]
    refine sum_congr rfl fun s _ => ?_
    rw [conjTranspose_smul, star_trivial,
      (isHermitian_mul_mul_conjTranspose (Ξ s) (hTs s)).eq]
  have hLifth : Lift.IsHermitian := by
    have := hLift.1.add hSgh
    rwa [sub_add_cancel] at this
  have hsplit : ∀ (M : Matrix O O ℝ) (ξ : O → ℝ),
      star ξ ⬝ᵥ (Lift *ᵥ ξ) + star ξ ⬝ᵥ (M *ᵥ ξ) =
        star ξ ⬝ᵥ ((Lift - Sg) *ᵥ ξ) + star ξ ⬝ᵥ (Sg *ᵥ ξ) + star ξ ⬝ᵥ (M *ᵥ ξ) := by
    intro M ξ
    rw [sub_mulVec, dotProduct_sub]
    ring
  refine opLE_of_mask hL hLop ?_ ?_
  · refine PosSemidef.of_dotProduct_mulVec_nonneg (hLifth.add hLmh) fun ξ => ?_
    rw [add_mulVec, dotProduct_add, hsplit]
    have h1 := hLift.dotProduct_mulVec_nonneg ξ
    have h2 := (abs_le.mp (hQL ξ)).1
    linarith
  · refine PosSemidef.of_dotProduct_mulVec_nonneg (hLifth.sub hLmh) fun ξ => ?_
    rw [sub_mulVec, dotProduct_sub]
    have h1 := hLift.dotProduct_mulVec_nonneg ξ
    have h2 := (abs_le.mp (hQL ξ)).2
    have e := hsplit 0 ξ
    simp only [zero_mulVec, dotProduct_zero, add_zero] at e
    linarith

end Sarkozy.OpsFeature

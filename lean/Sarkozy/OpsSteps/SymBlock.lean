module

public import Sarkozy.FirstStagePaper.BlockBound
public import Sarkozy.PartVRecords.OneStageSym

@[expose] public section

/-!
# `lem:record:one-stage-folded-e`(d), second bound: the symmetric part of `Δ_c` (OPS-S)

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(c), (d). V3 proved (c) at one
prime as a quadratic-form bound (`PartVRecords.abs_form_Dop_le`: `|⟨f, Δ f⟩| ≤ ‖f‖²/(p - 2)` on
the mean-zero functions); BlockBound proved the first bound of (d). Here:

* `normSq_le_of_form`: for a symmetric matrix and an invariant subspace, the quadratic-form bound
  gives the norm bound (polarization);
* `symD`, **`symD_norm_sq_le`**: at one prime, `‖Sym(𝒦₊ - 𝒦₀) f‖ ≤ ‖f‖/(p - 2)` on the mean-zero
  functions of `V_c`;
* **`tensor_sym_norm_le`** (abstract, after `TensorDiff.tensor_diff_norm_le`): the symmetric part of
  `⊗ Kp - ⊗ K0` preserves the sectors `H_S`, vanishes on `H_∅`, is the factor `Sym(Kp_e - K0_e)` on
  `H_{{e}}`, and has norm at most `α_e α_{e'} + β_e β_{e'}` on `H_S` with `|S| ≥ 2` (bounding
  `‖Sym T‖ ≤ ‖T‖` there);
* **`block_sym_norm_le`**: for a block of class-three primes `p ≥ b ≥ X ≥ 2^{24}` and every shared
  label, `‖Sym Δ_c‖ ≤ s_crude(b) = ((√b + 3)/(b - 3))² + 1/(b - 2)²`.

**Constant.** `b · s_crude(b) = 1 + 6 b^{-1/2} + O(1/b)`, against the paper's
`s_fold(X) = 1 + 2 r_X + O(q_X)`. The paper reaches its constant on the two-prime sectors by
splitting `𝒦₊^∘` into symmetric and skew parts; the cruder `‖Sym T‖ ≤ ‖T‖` there loses a factor
`1 + O(b^{-1/2})` (at most `1 + 2^{-9}` for `b ≥ 2^{24}`). Both are `O(1/b)`, which is what the
improvement of `lem:orbit-coupon`(i) needs.
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.OpsSteps

open Sarkozy.FirstStagePaper Sarkozy.IndexSupport Sarkozy.PartVRecords Sarkozy.PartV

/-! ## Polarization -/

section Polar

variable {Ω : Type*} [Fintype Ω]

/-- **A symmetric matrix whose quadratic form is at most `σ ‖f‖²` on an invariant subspace has norm
at most `σ` there.** -/
theorem normSq_le_of_form {S : Matrix Ω Ω ℝ} (hS : Sᵀ = S) (V : (Ω → ℝ) → Prop)
    (hVadd : ∀ f g, V f → V g → V (f + g)) (hVsmul : ∀ (t : ℝ) f, V f → V (t • f))
    (hinv : ∀ f, V f → V (S *ᵥ f)) {σ : ℝ} (hσ : 0 ≤ σ)
    (hform : ∀ f, V f → |f ⬝ᵥ (S *ᵥ f)| ≤ σ * (f ⬝ᵥ f)) (f : Ω → ℝ) (hf : V f) :
    (S *ᵥ f) ⬝ᵥ (S *ᵥ f) ≤ σ ^ 2 * (f ⬝ᵥ f) := by
  set y := S *ᵥ f with hy
  have hyV : V y := hinv f hf
  have hsym : ∀ u v : Ω → ℝ, u ⬝ᵥ (S *ᵥ v) = v ⬝ᵥ (S *ᵥ u) := by
    intro u v
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hS, dotProduct_comm]
  have hfy : f ⬝ᵥ (S *ᵥ y) = y ⬝ᵥ y := by rw [hsym, ← hy]
  have hyf : y ⬝ᵥ (S *ᵥ f) = y ⬝ᵥ y := by rw [← hy]
  have key : ∀ t : ℝ, 4 * t * (y ⬝ᵥ y) ≤ σ * (2 * (f ⬝ᵥ f) + 2 * t ^ 2 * (y ⬝ᵥ y)) := by
    intro t
    have h1 := hform (f + t • y) (hVadd _ _ hf (hVsmul t y hyV))
    have h2 := hform (f + (-t) • y) (hVadd _ _ hf (hVsmul (-t) y hyV))
    have e : ∀ s : ℝ, (f + s • y) ⬝ᵥ (S *ᵥ (f + s • y)) =
        f ⬝ᵥ (S *ᵥ f) + 2 * s * (y ⬝ᵥ y) + s ^ 2 * (y ⬝ᵥ (S *ᵥ y)) := by
      intro s
      simp only [Matrix.mulVec_add, Matrix.mulVec_smul, dotProduct_add, add_dotProduct,
        dotProduct_smul, smul_dotProduct, smul_eq_mul, hfy, hyf]
      ring
    have en : ∀ s : ℝ, (f + s • y) ⬝ᵥ (f + s • y) =
        f ⬝ᵥ f + 2 * s * (f ⬝ᵥ y) + s ^ 2 * (y ⬝ᵥ y) := by
      intro s
      simp only [dotProduct_add, add_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul,
        dotProduct_comm y f]
      ring
    rw [e, en] at h1 h2
    have h1' := (abs_le.mp h1).2
    have h2' := (abs_le.mp h2).1
    nlinarith
  have hyy := dotProduct_self_nonneg y
  have hff := dotProduct_self_nonneg f
  rcases hσ.lt_or_eq with hσ0 | hσ0
  · have k := key σ⁻¹
    have hinv0 : 0 < σ⁻¹ := inv_pos.mpr hσ0
    have e1 : σ * (4 * σ⁻¹ * (y ⬝ᵥ y)) = 4 * (y ⬝ᵥ y) := by field_simp
    have e2 : σ * (σ * (2 * (f ⬝ᵥ f) + 2 * σ⁻¹ ^ 2 * (y ⬝ᵥ y))) =
        2 * σ ^ 2 * (f ⬝ᵥ f) + 2 * (y ⬝ᵥ y) := by field_simp
    have k' := mul_le_mul_of_nonneg_left k hσ0.le
    rw [e1, e2] at k'
    linarith
  · subst hσ0
    have k := key 1
    simp only [zero_mul] at k
    nlinarith

end Polar

/-! ## One prime -/

section OnePrime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (hk : 0 < kP F)
include hF h3 hk

omit hF h3 hk in
/-- The symmetric part `Sym(𝒦₊ - 𝒦₀)` on `V_c`. -/
noncomputable def symD (c : F) : Matrix (Vc c) (Vc c) ℝ :=
  (1 / 2 : ℝ) • ((KpMat c - K0Mat c) + (KpMat c - K0Mat c)ᵀ)

omit hF h3 hk in
theorem symD_transpose (c : F) : (symD c)ᵀ = symD c := by
  unfold symD
  rw [Matrix.transpose_smul, Matrix.transpose_add, Matrix.transpose_transpose, add_comm]

omit hF h3 hk in
theorem form_transpose {Ω : Type*} [Fintype Ω] (A : Matrix Ω Ω ℝ) (f : Ω → ℝ) :
    f ⬝ᵥ (Aᵀ *ᵥ f) = f ⬝ᵥ (A *ᵥ f) := by
  rw [Matrix.mulVec_transpose, Matrix.dotProduct_mulVec, dotProduct_comm]

omit hF h3 hk in
theorem form_symD (c : F) (f : Vc c → ℝ) :
    f ⬝ᵥ (symD c *ᵥ f) = f ⬝ᵥ ((KpMat c - K0Mat c) *ᵥ f) := by
  unfold symD
  rw [Matrix.smul_mulVec, Matrix.add_mulVec, dotProduct_smul, dotProduct_add, form_transpose,
    smul_eq_mul]
  ring

/-- The mean matrix annihilates `Sym(𝒦₊ - 𝒦₀)` on the left. -/
theorem mean_mul_symD (c : F) (hq : (3 : ℝ) ≤ Fintype.card F) :
    meanMatrix (Vc c) * symD c = 0 := by
  have hJt : (meanMatrix (Vc c))ᵀ = meanMatrix (Vc c) := by
    ext x y
    simp [meanMatrix_apply]
  have h1 : meanMatrix (Vc c) * (KpMat c - K0Mat c) = 0 := by
    rw [Matrix.mul_sub, mean_mul_KpMat hF h3 hk c, mean_mul_K0Mat c hq, sub_self]
  have h2 : meanMatrix (Vc c) * (KpMat c - K0Mat c)ᵀ = 0 := by
    have : ((KpMat c - K0Mat c) * meanMatrix (Vc c))ᵀ = 0 := by
      rw [Matrix.sub_mul, KpMat_mul_mean hF h3 hk c, K0Mat_mul_mean c hq, sub_self,
        Matrix.transpose_zero]
    rw [Matrix.transpose_mul, hJt] at this
    exact this
  unfold symD
  rw [Matrix.mul_smul, Matrix.mul_add, h1, h2, add_zero, smul_zero]

/-- **`lem:record:one-stage-folded-e`(c), symmetric part, as a norm bound**:
`‖Sym(𝒦₊ - 𝒦₀) f‖ ≤ ‖f‖/(p - 2)` on the mean-zero functions of `V_c` (`p ≥ 11`). -/
theorem symD_norm_sq_le (h11 : 11 ≤ Fintype.card F) (c : F) (f : Vc c → ℝ)
    (hf : ∑ y, f y = 0) :
    (symD c *ᵥ f) ⬝ᵥ (symD c *ᵥ f) ≤ (1 / ((Fintype.card F : ℝ) - 2)) ^ 2 * (f ⬝ᵥ f) := by
  have hq : (3 : ℝ) ≤ Fintype.card F := by exact_mod_cast (by omega : 3 ≤ Fintype.card F)
  have hq2 : 0 < (Fintype.card F : ℝ) - 2 := by
    have : (11 : ℝ) ≤ Fintype.card F := by exact_mod_cast h11
    linarith
  refine normSq_le_of_form (symD_transpose c) (fun g => ∑ y, g y = 0)
    (fun g g' hg hg' => by simp [Finset.sum_add_distrib, hg, hg'])
    (fun t g hg => by simp [← Finset.mul_sum, hg])
    (fun g hg => sum_eq_zero_of_meanMatrix (by
      rw [Matrix.mulVec_mulVec, mean_mul_symD hF h3 hk c hq, Matrix.zero_mulVec]))
    (by positivity) (fun g hg => ?_) f hf
  rw [form_symD]
  have h := abs_form_Dop_le hF h3 hk h11 c (f := extV c g) (extV_c c g) (by rw [sum_extV, hg])
  rw [sum_extV_sq] at h
  rw [sum_Vc c (fun a => extV c g a * Dop c (extV c g) a) (by simp only [extV_c]; norm_num)] at h
  have e : g ⬝ᵥ ((KpMat c - K0Mat c) *ᵥ g) = ∑ y : Vc c, extV c g y.1 * Dop c (extV c g) y.1 := by
    unfold dotProduct
    refine sum_congr rfl fun y _ => ?_
    rw [extV_val, Matrix.sub_mulVec, Pi.sub_apply, KpMat_mulVec, K0Mat_mulVec]
    rfl
  rw [e, dotProduct_self_eq]
  calc _ ≤ (∑ y, g y ^ 2) / ((Fintype.card F : ℝ) - 2) := h
    _ = 1 / ((Fintype.card F : ℝ) - 2) * ∑ y, g y ^ 2 := by ring

end OnePrime

/-! ## The tensor difference -/

section Tensor

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]
  [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)]

omit [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)] [∀ e, Fintype (Ω e)] in
/-- The average of two products that differ in one coordinate. -/
theorem piKron_ite_avg (X Y C : ∀ e, Matrix (Ω e) (Ω e) ℝ) (e₀ : E) :
    (1 / 2 : ℝ) • (piKron (fun e => if e = e₀ then X e else C e) +
      piKron (fun e => if e = e₀ then Y e else C e)) =
      piKron (fun e => if e = e₀ then (1 / 2 : ℝ) • (X e + Y e) else C e) := by
  ext x y
  simp only [Matrix.smul_apply, Matrix.add_apply, piKron_apply, smul_eq_mul]
  rw [Fintype.prod_eq_mul_prod_compl e₀, Fintype.prod_eq_mul_prod_compl e₀,
    Fintype.prod_eq_mul_prod_compl e₀]
  have hc : ∀ F : ∀ e, Matrix (Ω e) (Ω e) ℝ,
      ∏ e ∈ ({e₀}ᶜ : Finset E), (if e = e₀ then F e else C e) (x e) (y e) =
        ∏ e ∈ ({e₀}ᶜ : Finset E), C e (x e) (y e) := by
    intro F
    refine prod_congr rfl fun e he => ?_
    rw [mem_compl, mem_singleton] at he
    simp only [he, ↓reduceIte]
  rw [hc X, hc Y, hc (fun e => (1 / 2 : ℝ) • (X e + Y e))]
  simp only [↓reduceIte, Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
  ring

omit [∀ e, Nonempty (Ω e)] in
/-- On a one-coordinate sector the tensor difference is its factor at that coordinate (the
argument of `TensorDiff.tensor_diff_norm_le`). -/
theorem single_sector_mulVec (Kp K0 : ∀ e, Matrix (Ω e) (Ω e) ℝ)
    (hrowp : ∀ e, Kp e * meanMatrix (Ω e) = meanMatrix (Ω e))
    (hrow0 : ∀ e, K0 e * meanMatrix (Ω e) = meanMatrix (Ω e))
    (l : E → Bool) (e₀ : E) (hsingle : ∀ e, e ≠ e₀ → l e = false) (g : (∀ e, Ω e) → ℝ)
    (hg : piKron (fun e => twoProj (Ω e) (l e)) *ᵥ g = g) :
    (piKron Kp - piKron K0) *ᵥ g =
      piKron (fun e => if e = e₀ then Kp e - K0 e else 1) *ᵥ g := by
  set P : ∀ e, Matrix (Ω e) (Ω e) ℝ := fun e => twoProj (Ω e) (l e) with hPdef
  have hKP : ∀ K : ∀ e, Matrix (Ω e) (Ω e) ℝ,
      (∀ e, K e * meanMatrix (Ω e) = meanMatrix (Ω e)) →
      piKron (fun e => K e * P e) = piKron (fun e => if e = e₀ then K e * P e else P e) := by
    intro K hK
    congr 1
    funext e
    by_cases he : e = e₀
    · simp only [he, ↓reduceIte]
    · simp only [he, ↓reduceIte, hPdef, hsingle e he, twoProj, Bool.false_eq_true, hK e]
  have hdiff : (piKron Kp - piKron K0) * piKron P =
      piKron (fun e => if e = e₀ then Kp e - K0 e else 1) * piKron P := by
    rw [Matrix.sub_mul, piKron_mul, piKron_mul, piKron_mul, hKP Kp hrowp, hKP K0 hrow0,
      piKron_ite_sub]
    congr 1
    funext e
    by_cases he : e = e₀
    · simp only [he, ↓reduceIte, Matrix.sub_mul]
    · simp only [he, ↓reduceIte, Matrix.one_mul]
  rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdiff]

omit [Fintype E] [DecidableEq E] [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)] in
theorem meanMatrix_transpose' (e : E) : (meanMatrix (Ω e))ᵀ = meanMatrix (Ω e) := by
  ext x y
  simp [meanMatrix_apply]

/-- **`lem:record:one-stage-folded-e`(d), the symmetric part, abstract form.** With the hypotheses
of `TensorDiff.tensor_diff_norm_le` and `‖Sym(Kp_e - K0_e) f‖ ≤ σ_e ‖f‖` on the mean-zero
functions, `‖Sym(⊗ Kp - ⊗ K0) f‖ ≤ D ‖f‖` as soon as `σ_e ≤ D` and `α_e α_{e'} + β_e β_{e'} ≤ D`
for `e ≠ e'`. -/
theorem tensor_sym_norm_le (Kp K0 : ∀ e, Matrix (Ω e) (Ω e) ℝ)
    (hrowp : ∀ e, Kp e * meanMatrix (Ω e) = meanMatrix (Ω e))
    (hcolp : ∀ e, meanMatrix (Ω e) * Kp e = meanMatrix (Ω e))
    (hrow0 : ∀ e, K0 e * meanMatrix (Ω e) = meanMatrix (Ω e))
    (hcol0 : ∀ e, meanMatrix (Ω e) * K0 e = meanMatrix (Ω e))
    {α β σ : E → ℝ} (hα0 : ∀ e, 0 ≤ α e) (hα1 : ∀ e, α e ≤ 1) (hβ0 : ∀ e, 0 ≤ β e)
    (hβ1 : ∀ e, β e ≤ 1) (hσ0 : ∀ e, 0 ≤ σ e)
    (hKp : ∀ e (f : Ω e → ℝ), ∑ x, f x = 0 → (Kp e *ᵥ f) ⬝ᵥ (Kp e *ᵥ f) ≤ α e ^ 2 * (f ⬝ᵥ f))
    (hK0 : ∀ e (f : Ω e → ℝ), ∑ x, f x = 0 → (K0 e *ᵥ f) ⬝ᵥ (K0 e *ᵥ f) ≤ β e ^ 2 * (f ⬝ᵥ f))
    (hS : ∀ e (f : Ω e → ℝ), ∑ x, f x = 0 →
      (((1 / 2 : ℝ) • ((Kp e - K0 e) + (Kp e - K0 e)ᵀ)) *ᵥ f) ⬝ᵥ
        (((1 / 2 : ℝ) • ((Kp e - K0 e) + (Kp e - K0 e)ᵀ)) *ᵥ f) ≤ σ e ^ 2 * (f ⬝ᵥ f))
    {D : ℝ} (hDσ : ∀ e, σ e ≤ D) (hD2 : ∀ e e', e ≠ e' → α e * α e' + β e * β e' ≤ D)
    (f : (∀ e, Ω e) → ℝ) :
    (((1 / 2 : ℝ) • ((piKron Kp - piKron K0) + (piKron Kp - piKron K0)ᵀ)) *ᵥ f) ⬝ᵥ
      (((1 / 2 : ℝ) • ((piKron Kp - piKron K0) + (piKron Kp - piKron K0)ᵀ)) *ᵥ f) ≤
      D ^ 2 * (f ⬝ᵥ f) := by
  set H : SectorSystem (∀ e, Ω e) (E → Bool) := SectorSystem.pi (fun e => twoSectors (Ω e))
    with hH
  have hp : SectorOperator H (piKron Kp)
      (fun l => ∏ e, (fun s : Bool => if s then α e else 1) (l e)) :=
    SectorOperator.pi (fun e => sectorOperator_of_stochastic (hrowp e) (hcolp e) (hKp e))
  have h0 : SectorOperator H (piKron K0)
      (fun l => ∏ e, (fun s : Bool => if s then β e else 1) (l e)) :=
    SectorOperator.pi (fun e => sectorOperator_of_stochastic (hrow0 e) (hcol0 e) (hK0 e))
  have hpT := hp.transpose
  have h0T := h0.transpose
  have hSg : ∀ g : (∀ e, Ω e) → ℝ,
      ((1 / 2 : ℝ) • ((piKron Kp - piKron K0) + (piKron Kp - piKron K0)ᵀ)) *ᵥ g =
        (1 / 2 : ℝ) • ((piKron Kp *ᵥ g - piKron K0 *ᵥ g) +
          ((piKron Kp)ᵀ *ᵥ g - (piKron K0)ᵀ *ᵥ g)) := by
    intro g
    rw [Matrix.transpose_sub, Matrix.smul_mulVec, Matrix.add_mulVec, Matrix.sub_mulVec,
      Matrix.sub_mulVec]
  apply norm_le_of_sectors H
  · intro l g hg
    rw [hSg, Matrix.mulVec_smul, Matrix.mulVec_add, Matrix.mulVec_sub, Matrix.mulVec_sub,
      hp.maps l g hg, h0.maps l g hg, hpT.maps l g hg, h0T.maps l g hg]
  · intro l g hg
    have hgg := dotProduct_self_nonneg g
    by_cases hz : ∀ e, l e = false
    · have hl : l = H.zero := funext hz
      rw [hl] at hg
      rw [hSg, hp.id_zero g hg, h0.id_zero g hg, hpT.id_zero g hg, h0T.id_zero g hg, sub_self,
        add_zero, smul_zero, zero_dotProduct]
      exact mul_nonneg (sq_nonneg D) hgg
    · push Not at hz
      obtain ⟨e₀, he₀⟩ := hz
      have he₀' : l e₀ = true := by simpa using he₀
      by_cases hsingle : ∀ e, e ≠ e₀ → l e = false
      · -- one coordinate: the factor `Sym(Kp e₀ - K0 e₀)`
        have hg' : piKron (fun e => twoProj (Ω e) (l e)) *ᵥ g = g := hg
        have hJt := meanMatrix_transpose' (Ω := Ω)
        have hrowpT : ∀ e, (Kp e)ᵀ * meanMatrix (Ω e) = meanMatrix (Ω e) := fun e => by
          have := congrArg Matrix.transpose (hcolp e)
          rwa [Matrix.transpose_mul, hJt e] at this
        have hrow0T : ∀ e, (K0 e)ᵀ * meanMatrix (Ω e) = meanMatrix (Ω e) := fun e => by
          have := congrArg Matrix.transpose (hcol0 e)
          rwa [Matrix.transpose_mul, hJt e] at this
        have e1 := single_sector_mulVec Kp K0 hrowp hrow0 l e₀ hsingle g hg'
        have e2 := single_sector_mulVec (fun e => (Kp e)ᵀ) (fun e => (K0 e)ᵀ) hrowpT hrow0T l e₀
          hsingle g hg'
        rw [← piKron_transpose, ← piKron_transpose] at e2
        have hval : ((1 / 2 : ℝ) • ((piKron Kp - piKron K0) + (piKron Kp - piKron K0)ᵀ)) *ᵥ g =
            piKron (fun e => if e = e₀ then
              (1 / 2 : ℝ) • ((Kp e - K0 e) + (Kp e - K0 e)ᵀ) else 1) *ᵥ g := by
          rw [Matrix.transpose_sub, Matrix.smul_mulVec, Matrix.add_mulVec, e1, e2,
            ← Matrix.add_mulVec, ← Matrix.smul_mulVec, piKron_ite_avg]
          simp only [Matrix.transpose_sub]
        have hRB : RangeBound (piKron (fun e => twoProj (Ω e) (l e)))
            (piKron (fun e => if e = e₀ then
              (1 / 2 : ℝ) • ((Kp e - K0 e) + (Kp e - K0 e)ᵀ) else 1))
            (∏ e, if e = e₀ then σ e else 1) := by
          refine RangeBound.piKron (fun e => (twoSectors (Ω e)).transpose_proj (l e)) ?_
          intro e
          by_cases he : e = e₀
          · subst he
            simp only [↓reduceIte, he₀']
            refine RangeBound.of_vec ((twoSectors (Ω e)).transpose_proj true)
              ((twoSectors (Ω e)).proj_mul_self true) ?_ ?_
            · intro v _
              have hJM : meanMatrix (Ω e) *
                  ((1 / 2 : ℝ) • ((Kp e - K0 e) + (Kp e - K0 e)ᵀ)) = 0 := by
                have a1 : meanMatrix (Ω e) * (Kp e - K0 e) = 0 := by
                  rw [Matrix.mul_sub, hcolp e, hcol0 e, sub_self]
                have a2 : meanMatrix (Ω e) * (Kp e - K0 e)ᵀ = 0 := by
                  have : ((Kp e - K0 e) * meanMatrix (Ω e))ᵀ = 0 := by
                    rw [Matrix.sub_mul, hrowp e, hrow0 e, sub_self, Matrix.transpose_zero]
                  rwa [Matrix.transpose_mul, hJt e] at this
                rw [Matrix.mul_smul, Matrix.mul_add, a1, a2, add_zero, smul_zero]
              change twoProj (Ω e) true *ᵥ _ = _
              simp only [twoProj, ↓reduceIte]
              rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hJM,
                Matrix.zero_mulVec, sub_zero]
            · intro v hv
              exact hS e v (sum_eq_zero_of_meanMatrix (mean_of_proj_true hv))
          · simp only [he, ↓reduceIte, hsingle e he]
            exact rangeBound_one_false
        have hnorm := hRB.norm_le (H.transpose_proj l) (f := g) hg
        rw [Finset.prod_ite_eq' univ e₀ σ, ite_eq_left (mem_univ e₀)] at hnorm
        rw [hval]
        refine le_trans hnorm (mul_le_mul_of_nonneg_right ?_ hgg)
        exact pow_le_pow_left₀ (hσ0 e₀) (hDσ e₀) 2
      · -- two coordinates or more: `‖Sym T‖ ≤ ‖T‖`
        push Not at hsingle
        obtain ⟨e₁, he₁, hle₁⟩ := hsingle
        have hle₁' : l e₁ = true := by simpa using hle₁
        have hwα : ∏ e, (fun s : Bool => if s then α e else 1) (l e) ≤ α e₀ * α e₁ := by
          have h := prod_le_two_of_le_one
            (w := fun e => (fun s : Bool => if s then α e else 1) (l e))
            (fun e => by cases l e <;> simp [hα0 e]) (fun e => by cases l e <;> simp [hα1 e])
            (Ne.symm he₁)
          simpa only [he₀', hle₁', ↓reduceIte] using h
        have hwβ : ∏ e, (fun s : Bool => if s then β e else 1) (l e) ≤ β e₀ * β e₁ := by
          have h := prod_le_two_of_le_one
            (w := fun e => (fun s : Bool => if s then β e else 1) (l e))
            (fun e => by cases l e <;> simp [hβ0 e]) (fun e => by cases l e <;> simp [hβ1 e])
            (Ne.symm he₁)
          simpa only [he₀', hle₁', ↓reduceIte] using h
        have hwα0 : 0 ≤ ∏ e, (fun s : Bool => if s then α e else 1) (l e) :=
          prod_nonneg fun e _ => by cases l e <;> simp [hα0 e]
        have hwβ0 : 0 ≤ ∏ e, (fun s : Bool => if s then β e else 1) (l e) :=
          prod_nonneg fun e _ => by cases l e <;> simp [hβ0 e]
        have hab0 : 0 ≤ α e₀ * α e₁ := mul_nonneg (hα0 e₀) (hα0 e₁)
        have hbb0 : 0 ≤ β e₀ * β e₁ := mul_nonneg (hβ0 e₀) (hβ0 e₁)
        have hu : (piKron Kp *ᵥ g) ⬝ᵥ (piKron Kp *ᵥ g) ≤ (α e₀ * α e₁) ^ 2 * (g ⬝ᵥ g) :=
          le_trans (hp.norm_le l g hg)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwα0 hwα 2) hgg)
        have hv : (piKron K0 *ᵥ g) ⬝ᵥ (piKron K0 *ᵥ g) ≤ (β e₀ * β e₁) ^ 2 * (g ⬝ᵥ g) :=
          le_trans (h0.norm_le l g hg)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwβ0 hwβ 2) hgg)
        have huT : ((piKron Kp)ᵀ *ᵥ g) ⬝ᵥ ((piKron Kp)ᵀ *ᵥ g) ≤ (α e₀ * α e₁) ^ 2 * (g ⬝ᵥ g) :=
          le_trans (hpT.norm_le l g hg)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwα0 hwα 2) hgg)
        have hvT : ((piKron K0)ᵀ *ᵥ g) ⬝ᵥ ((piKron K0)ᵀ *ᵥ g) ≤ (β e₀ * β e₁) ^ 2 * (g ⬝ᵥ g) :=
          le_trans (h0T.norm_le l g hg)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwβ0 hwβ 2) hgg)
        set D' := α e₀ * α e₁ + β e₀ * β e₁ with hD'
        have hD'0 : 0 ≤ D' := add_nonneg hab0 hbb0
        have h1 := sub_dotProduct_le hab0 hbb0 hgg hu hv
        have h2 := sub_dotProduct_le hab0 hbb0 hgg huT hvT
        set u := piKron Kp *ᵥ g - piKron K0 *ᵥ g
        set w := (piKron Kp)ᵀ *ᵥ g - (piKron K0)ᵀ *ᵥ g
        have hw' : (-w) ⬝ᵥ (-w) ≤ D' ^ 2 * (g ⬝ᵥ g) := by
          rw [neg_dotProduct, dotProduct_neg, neg_neg]
          exact h2
        have h3 := sub_dotProduct_le hD'0 hD'0 hgg h1 hw'
        rw [sub_neg_eq_add] at h3
        rw [hSg]
        rw [smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
        have hDD : D' ^ 2 * (g ⬝ᵥ g) ≤ D ^ 2 * (g ⬝ᵥ g) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hD'0 (hD2 e₀ e₁ (Ne.symm he₁)) 2) hgg
        nlinarith

end Tensor

/-! ## The block -/

/-- The constant `s_crude(b) = ((√b + 3)/(b - 3))² + 1/(b - 2)²` of the symmetric block bound. -/
noncomputable def sCrude (b : ℝ) : ℝ := ((Real.sqrt b + 3) / (b - 3)) ^ 2 + (1 / (b - 2)) ^ 2

section Constants

variable {X b p : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) (hbp : b ≤ p)
include hX hXb hbp

/-- `κ^{fold}_p = (√p + 3)/(p - 3)` is nonincreasing in `p`. -/
theorem kfold_mono : (Real.sqrt p + 3) / (p - 3) ≤ (Real.sqrt b + 3) / (b - 3) := by
  obtain ⟨hsb, hsbp⟩ := sqrt_ge_of_block hX hXb hbp
  have hb0 : 0 ≤ b := by linarith
  have hp0 : 0 ≤ p := by linarith
  have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  have hsp2 : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0
  have hb3 : 0 < b - 3 := by linarith
  have hp3 : 0 < p - 3 := by linarith
  rw [div_le_div_iff₀ hp3 hb3]
  have e : (Real.sqrt p + 3) * (b - 3) - (Real.sqrt b + 3) * (p - 3) =
      (Real.sqrt b - Real.sqrt p) *
        (Real.sqrt p * Real.sqrt b + 3 * Real.sqrt p + 3 * Real.sqrt b + 3) := by
    linear_combination (Real.sqrt b + 3) * hsp2 - (Real.sqrt p + 3) * hsb2
  have h1 : (Real.sqrt b - Real.sqrt p) *
      (Real.sqrt p * Real.sqrt b + 3 * Real.sqrt p + 3 * Real.sqrt b + 3) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by positivity)
  linarith

/-- `1/(p - 2) ≤ s_crude(b)`. -/
theorem sigma_le_sCrude : 1 / (p - 2) ≤ sCrude b := by
  obtain ⟨hsb, -⟩ := sqrt_ge_of_block hX hXb hbp
  have hb0 : 0 ≤ b := by linarith
  have hsb2 : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb0
  have hb2 : 0 < b - 2 := by linarith
  have hb3 : 0 < b - 3 := by linarith
  have h1 : 1 / (p - 2) ≤ 1 / (b - 2) := one_div_le_one_div_of_le hb2 (by linarith)
  have h2 : 1 / (b - 2) ≤ ((Real.sqrt b + 3) / (b - 3)) ^ 2 := by
    rw [div_pow, div_le_div_iff₀ hb2 (by positivity)]
    have a1 : (b - 3) ^ 2 ≤ b * (b - 2) := by nlinarith
    have a2 : b ≤ (Real.sqrt b + 3) ^ 2 := by nlinarith [Real.sqrt_nonneg b]
    nlinarith
  have h3 : 0 ≤ (1 / (b - 2)) ^ 2 := sq_nonneg _
  unfold sCrude
  linarith

end Constants

/-- **The symmetric constant is below the sharp one**: `s_crude(b) ≤ k_new(X) b^{-1/2}` for
`b ≥ X ≥ 2^{24}` (so the symmetric prices satisfy `0 ≤ s ≤ d`, the condition of
`hcat_of_terms`). -/
theorem sCrude_le_blockConst {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) :
    sCrude b ≤ blockConst X b := by
  obtain ⟨ha0, -, ha⟩ := kfold_bounds hX hXb (le_refl b)
  obtain ⟨hb0, -, hb⟩ := k0_bounds hX hXb (le_refl b)
  refine le_trans ?_ (pair_le_blockConst hX hXb)
  unfold sCrude
  exact add_le_add (pow_le_pow_left₀ ha0 ha 2) (pow_le_pow_left₀ hb0 hb 2)

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- `Sym Δ_c = ½(Δ_c + Δ_c^T)` for the shared label `c` of a block. -/
noncomputable def blockSymD (c : BlockLabel pr) :
    Matrix (∀ i, Vc (c i)) (∀ i, Vc (c i)) ℝ :=
  (1 / 2 : ℝ) • ((blockKp pr c - blockK0 pr c) + (blockKp pr c - blockK0 pr c)ᵀ)

/-- **`lem:record:one-stage-folded-e`(d), second bound** (with the constant `s_crude(b)`; see the
module docstring): for a block of class-three primes `p ≥ b ≥ X ≥ 2^{24}` and every shared label
`c`, `‖Sym Δ_c f‖ ≤ s_crude(b) ‖f‖` on all of `ℝ^{∏_p V_{c_p}}`. -/
theorem block_sym_norm_le (h : ClassThreeBlock pr) {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (c : BlockLabel pr) (f : (∀ i, Vc (c i)) → ℝ) :
    (blockSymD pr c *ᵥ f) ⬝ᵥ (blockSymD pr c *ᵥ f) ≤ sCrude b ^ 2 * (f ⬝ᵥ f) := by
  have hcard : ∀ i, (Fintype.card (ZMod (pr i)) : ℝ) = pr i := fun i => by rw [ZMod.card]
  have hq3 : ∀ i, (3 : ℝ) ≤ Fintype.card (ZMod (pr i)) := fun i => card_three_le (h.card_mod i)
  have hbp' : ∀ i, b ≤ (Fintype.card (ZMod (pr i)) : ℝ) := fun i => by rw [hcard]; exact hbp i
  have h11 : ∀ i, 11 ≤ Fintype.card (ZMod (pr i)) := fun i => by
    have : (11 : ℝ) ≤ Fintype.card (ZMod (pr i)) := by linarith [hbp' i]
    exact_mod_cast this
  have hαb := kfold_bounds hX hXb (le_refl b)
  have hβb := k0_bounds hX hXb (le_refl b)
  exact tensor_sym_norm_le (fun i => KpMat (c i)) (fun i => K0Mat (c i))
    (fun i => KpMat_mul_mean (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i))
    (fun i => mean_mul_KpMat (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i))
    (fun i => K0Mat_mul_mean (c i) (hq3 i)) (fun i => mean_mul_K0Mat (c i) (hq3 i))
    (α := fun i => (Real.sqrt (Fintype.card (ZMod (pr i)) : ℝ) + 3) /
      ((Fintype.card (ZMod (pr i)) : ℝ) - 3))
    (β := fun i => 1 / ((Fintype.card (ZMod (pr i)) : ℝ) - 2))
    (σ := fun i => 1 / ((Fintype.card (ZMod (pr i)) : ℝ) - 2))
    (fun i => (kfold_bounds hX hXb (hbp' i)).1) (fun i => (kfold_bounds hX hXb (hbp' i)).2.1)
    (fun i => (k0_bounds hX hXb (hbp' i)).1) (fun i => (k0_bounds hX hXb (hbp' i)).2.1)
    (fun i => (k0_bounds hX hXb (hbp' i)).1)
    (fun i f hf => KpMat_norm_sq_le (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (c i) f hf)
    (fun i f hf => K0Mat_norm_sq_le (c i) f hf)
    (fun i f hf => symD_norm_sq_le (h.ringChar_ne i) (h.card_mod i) (h.kP_pos' i) (h11 i) (c i)
      f hf)
    (fun i => sigma_le_sCrude hX hXb (hbp' i))
    (fun i j _ => by
      have ha := kfold_mono hX hXb (hbp' i)
      have ha' := kfold_mono hX hXb (hbp' j)
      have ha0 := (kfold_bounds hX hXb (hbp' i)).1
      have ha0' := (kfold_bounds hX hXb (hbp' j)).1
      have hb := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < b - 2)
        (by linarith [hbp' i] : b - 2 ≤ (Fintype.card (ZMod (pr i)) : ℝ) - 2)
      have hb' := one_div_le_one_div_of_le (by linarith : (0 : ℝ) < b - 2)
        (by linarith [hbp' j] : b - 2 ≤ (Fintype.card (ZMod (pr j)) : ℝ) - 2)
      have hb0 := (k0_bounds hX hXb (hbp' i)).1
      have hb0' := (k0_bounds hX hXb (hbp' j)).1
      unfold sCrude
      rw [sq, sq]
      exact add_le_add (mul_le_mul ha ha' ha0' hαb.1) (mul_le_mul hb hb' hb0' hβb.1))
    f

/-- The same bound for the bilinear form: `|⟨g, Sym Δ_c f⟩| ≤ s_crude(b) ‖g‖ ‖f‖`. -/
theorem block_sym_form_le (h : ClassThreeBlock pr) {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) (c : BlockLabel pr) (g f : (∀ i, Vc (c i)) → ℝ) :
    |g ⬝ᵥ (blockSymD pr c *ᵥ f)| ≤ sCrude b * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f) := by
  have hcs := dotProduct_sq_le g (blockSymD pr c *ᵥ f)
  have hgg := dotProduct_self_nonneg g
  have hff := dotProduct_self_nonneg f
  have hS0 : 0 ≤ sCrude b := by unfold sCrude; positivity
  have h2 : (g ⬝ᵥ (blockSymD pr c *ᵥ f)) ^ 2 ≤
      (sCrude b * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f)) ^ 2 := by
    have e : (sCrude b * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f)) ^ 2 =
        (g ⬝ᵥ g) * (sCrude b ^ 2 * (f ⬝ᵥ f)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hgg, Real.sq_sqrt hff]
      ring
    rw [e]
    exact le_trans hcs (mul_le_mul_of_nonneg_left (block_sym_norm_le pr h hX hXb hbp c f) hgg)
  exact abs_le_of_sq_le_sq h2 (by positivity)

end Block

end Sarkozy.OpsSteps

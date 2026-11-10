module

public import Sarkozy.UpperReference.ObservedGates
public import Sarkozy.SpectralC.MatrixNorms

/-!
# `prop:observed-caps`: the operator-norm form of the two Schur tests

`rem:realified-gates`, last step: from `-kI ⪯ M(±i) ⪯ kI` (`ObservedGates.lean`) to
`‖M(±i)‖ ≤ k` in the bilinear form `SpectralC.NormLe` used by S1's `cor:star-matrix`
(`SpectralD.StarMatrix.starPart_norm_le`, hypothesis `‖M(i)‖ ≤ λ`).

* `normLe_of_gates`: the general step, for Hermitian `M` (`sq_le_of_forall_pos` is the
  discriminant argument).
* **`full_normLe`**: `‖M(σ)‖ ≤ 6` for the full complete star matrix of EL22, `σ = ±i`.
* **`merge_normLe`**: `‖M_vv(σ)‖ ≤ 2.188902` for the merge's principal star matrix.
-/

@[expose] public section

open Matrix ComplexConjugate
open scoped ComplexOrder

namespace Sarkozy.UpperReference.Observed

variable {n : Type*} [Fintype n]

/-- `SpectralC.bform` is the `dotProduct` form `w^* M z`. -/
theorem bform_eq (M : Matrix n n ℂ) (w z : n → ℂ) :
    SpectralC.bform (fun i j => M i j) w z = star w ⬝ᵥ (M *ᵥ z) := by
  unfold SpectralC.bform
  simp only [dotProduct, mulVec, Finset.mul_sum, Pi.star_apply, RCLike.star_def]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- The quadratic form of a positive semidefinite matrix has nonnegative real part. -/
theorem re_form_nonneg {A : Matrix n n ℂ} (hA : A.PosSemidef) (x : n → ℂ) :
    0 ≤ (star x ⬝ᵥ (A *ᵥ x)).re := by
  have h := hA.dotProduct_mulVec_nonneg x
  exact (Complex.nonneg_iff.mp h).1

/-- `re(x^*x) = |x|²`. -/
theorem re_self (x : n → ℂ) : (star x ⬝ᵥ x).re = SpectralC.vnorm x ^ 2 := by
  rw [SpectralC.vnorm_sq]
  simp only [dotProduct, Pi.star_apply, RCLike.star_def, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]

/-- If `2ta ≤ b + t²d` for every `t > 0` (`a, b, d ≥ 0`), then `a² ≤ bd`. -/
theorem sq_le_of_forall_pos {a b d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d)
    (h : ∀ t : ℝ, 0 < t → 2 * t * a ≤ b + t ^ 2 * d) : a ^ 2 ≤ b * d := by
  rcases ha.lt_or_eq with ha' | ha'
  · rcases hd.lt_or_eq with hd' | hd'
    · have h1 := h (a / d) (div_pos ha' hd')
      have e : (a / d) ^ 2 * d = a ^ 2 / d := by field_simp
      have e2 : 2 * (a / d) * a = 2 * (a ^ 2 / d) := by ring
      rw [e, e2] at h1
      have h3 : a ^ 2 / d ≤ b := by linarith
      rwa [div_le_iff₀ hd'] at h3
    · have h1 := h ((b + 1) / (2 * a)) (by positivity)
      rw [← hd'] at h1
      have e : 2 * ((b + 1) / (2 * a)) * a = b + 1 := by field_simp
      rw [e] at h1
      linarith
  · rw [← ha']
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact mul_nonneg hb hd

/-- **`‖M‖ ≤ k` from `-kI ⪯ M ⪯ kI`** (`rem:realified-gates`, the last step): for Hermitian
`M`, `kI ∓ M ⪰ 0` gives `2 re(x^*My) ≤ k(|x|² + |y|²)` (parallelogram), hence
`|w^*Mz| ≤ k|w||z|`, i.e. `SpectralC.NormLe M k` (the norm hypothesis of S1's
`SpectralD.StarMatrix.starPart_norm_le`). -/
theorem normLe_of_gates [DecidableEq n] (M : Matrix n n ℂ) (hM : M.IsHermitian) {k : ℝ} (hk : 0 ≤ k)
    (hm : ((k : ℂ) • (1 : Matrix n n ℂ) - M).PosSemidef)
    (hp : ((k : ℂ) • (1 : Matrix n n ℂ) + M).PosSemidef) :
    SpectralC.NormLe (fun i j => M i j) k := by
  intro w z
  rw [bform_eq]
  -- `2 re(x^* M y) ≤ k(|x|² + |y|²)` for all `x, y`
  have key : ∀ x y : n → ℂ, 2 * (star x ⬝ᵥ (M *ᵥ y)).re ≤
      k * (SpectralC.vnorm x ^ 2 + SpectralC.vnorm y ^ 2) := by
    intro x y
    have h1 := re_form_nonneg hm (x + y)
    have h2 := re_form_nonneg hp (x - y)
    have hsym : (star y ⬝ᵥ (M *ᵥ x)).re = (star x ⬝ᵥ (M *ᵥ y)).re := by
      rw [← hM.star_dotProduct_mulVec_comm x y, RCLike.star_def, Complex.conj_re]
    simp only [star_add, star_sub, Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec,
      Matrix.one_mulVec, Matrix.mulVec_add, Matrix.mulVec_sub, dotProduct_add, add_dotProduct,
      dotProduct_sub, sub_dotProduct, dotProduct_smul, Complex.add_re, Complex.sub_re,
      smul_eq_mul, Complex.re_ofReal_mul] at h1 h2
    rw [← re_self x, ← re_self y]
    linarith
  set c := star w ⬝ᵥ (M *ᵥ z) with hc
  by_cases hc0 : c = 0
  · rw [hc0, norm_zero]
    exact mul_nonneg (mul_nonneg hk (SpectralC.vnorm_nonneg w)) (SpectralC.vnorm_nonneg z)
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc0
  set θ : ℂ := conj c / (‖c‖ : ℂ) with hθ
  have hθc : θ * c = (‖c‖ : ℂ) := by
    rw [hθ, div_mul_eq_mul_div, Complex.conj_mul', sq]
    field_simp
  have hθn : ‖θ‖ = 1 := by
    rw [hθ, norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
      div_self hcn.ne']
  have hquad : ∀ t : ℝ, 0 < t → 2 * t * ‖c‖ ≤
      k * SpectralC.vnorm w ^ 2 + t ^ 2 * (k * SpectralC.vnorm z ^ 2) := by
    intro t ht
    have h := key w (((t : ℂ) * θ) • z)
    rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, mul_assoc, ← hc, hθc] at h
    have hre : (((t : ℂ) * (‖c‖ : ℂ))).re = t * ‖c‖ := by
      rw [← Complex.ofReal_mul, Complex.ofReal_re]
    have hv : SpectralC.vnorm (((t : ℂ) * θ) • z) ^ 2 = t ^ 2 * SpectralC.vnorm z ^ 2 := by
      rw [SpectralC.vnorm_sq, SpectralC.vnorm_sq, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Pi.smul_apply, smul_eq_mul, norm_mul, norm_mul, hθn, Complex.norm_real,
        Real.norm_of_nonneg ht.le]
      ring
    rw [hre, hv] at h
    nlinarith
  have hsq := sq_le_of_forall_pos (norm_nonneg c)
    (mul_nonneg hk (sq_nonneg _)) (mul_nonneg hk (sq_nonneg _)) hquad
  have hrhs : k * SpectralC.vnorm w ^ 2 * (k * SpectralC.vnorm z ^ 2) =
      (k * SpectralC.vnorm w * SpectralC.vnorm z) ^ 2 := by ring
  rw [hrhs] at hsq
  exact abs_le_of_sq_le_sq' hsq (mul_nonneg (mul_nonneg hk (SpectralC.vnorm_nonneg w))
    (SpectralC.vnorm_nonneg z)) |>.2

/-- `σD` is Hermitian for the real antisymmetric `D` of EL22 and `σ = ±i`. -/
theorem sigmaD_hermitian (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    (σ • toC Dfull).IsHermitian := by
  have hσc : -(star σ) = σ := by
    rcases hσ with h | h <;> rw [h]
    · rw [Complex.star_def, Complex.conj_I, neg_neg]
    · rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]
  show (σ • toC Dfull)ᴴ = σ • toC Dfull
  rw [conjTranspose_smul, Dfull_conjTranspose, smul_neg, ← neg_smul, hσc]

/-- `σD_v` is Hermitian for the merge's principal block and `σ = ±i`. -/
theorem sigmaDc_hermitian (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    (σ • Dc).IsHermitian := by
  have hσc : -(star σ) = σ := by
    rcases hσ with h | h <;> rw [h]
    · rw [Complex.star_def, Complex.conj_I, neg_neg]
    · rw [Complex.star_def, map_neg, Complex.conj_I, neg_neg]
  show (σ • Dc)ᴴ = σ • Dc
  rw [conjTranspose_smul, Dc_conjTranspose, smul_neg, ← neg_smul, hσc]

/-- **`‖M(±i)‖ ≤ 6` for the full complete star matrix of EL22** (`prop:observed-caps`). -/
theorem full_normLe (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    SpectralC.NormLe (fun i j => fromBlocks (σ • toC Dfull) starBfull starBfullᴴ 0 i j) 6 := by
  have hH : (fromBlocks (σ • toC Dfull) starBfull starBfullᴴ 0).IsHermitian :=
    IsHermitian.fromBlocks (sigmaD_hermitian σ hσ) (by simp) isHermitian_zero
  obtain ⟨hm, hp⟩ := full_gates σ hσ
  exact normLe_of_gates _ hH (by norm_num) hm hp

/-- **`‖M_vv(±i)‖ ≤ 2.188902` for the merge's principal star matrix** (`prop:observed-caps`). -/
theorem merge_normLe (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    SpectralC.NormLe (fun i j => fromBlocks (σ • Dc) starBmerge starBmergeᴴ 0 i j)
      (2188902 / 1000000) := by
  have hH : (fromBlocks (σ • Dc) starBmerge starBmergeᴴ 0).IsHermitian :=
    IsHermitian.fromBlocks (sigmaDc_hermitian σ hσ) (by simp) isHermitian_zero
  obtain ⟨hm, hp⟩ := merge_gates σ hσ
  exact normLe_of_gates _ hH (by norm_num) hm hp

end Sarkozy.UpperReference.Observed

module

public import Sarkozy.DLK.Basic
public import Mathlib.Analysis.Matrix.PosDef

/-!
# The transcription of `thm:dl:K` is its literal spectral statement

`paper/sections/15_second_order.tex`, `thm:dl:K`: *for every odd prime `p`, every eigenvalue of
the real symmetric matrix `M` of `eq:dl:M` lies in `[-2p, 2p]`.* The hypothesis
`Target.FourCycle` (`Sarkozy/TargetDLK.lean`) states this as a quadratic-form bound. This file
proves, with Mathlib's spectrum of a matrix, that the two statements are equivalent, so that the
transcription does not rest on the Rayleigh–Ritz step:

* `fourCycleMat p`: `M` as a Mathlib matrix indexed by `𝒳` (the subtype of `distinctPairs p`),
  `fourCycleMat_isHermitian`: it is real symmetric;
* `quadForm_iff_spectrum`: for a real symmetric matrix `A`,
  `(∀ v, |vᵀ A v| ≤ c vᵀ v) ↔ ∀ μ ∈ spectrum ℝ A, |μ| ≤ c` (through `posSemidef_iff_eigenvalues_nonneg`
  for `c·1 ∓ A`, and `spectrum ℝ (c·1 ∓ A) = c ∓ spectrum ℝ A`);
* `FourCycleSpectral`: the literal statement, `∀ μ ∈ spectrum ℝ (fourCycleMat p), |μ| ≤ 2p` for
  every odd prime `p` (`spectrum ℝ M` is the set of eigenvalues of `M`, real since `M` is real
  symmetric; `Matrix.IsHermitian.spectrum_real_eq_range_eigenvalues`);
* `fourCycle_iff_spectral`: `Target.FourCycle ↔ FourCycleSpectral`; `abs_eigenvalues_le`: the
  same with Mathlib's `Matrix.IsHermitian.eigenvalues`.
-/

@[expose] public section

open scoped BigOperators Pointwise
open Finset Matrix

namespace Sarkozy.DLK

open Sarkozy Sarkozy.Target

/-- For a real symmetric matrix `A` and `c ∈ ℝ`: `|vᵀ A v| ≤ c vᵀ v` for all `v` if and only if
every eigenvalue of `A` (every element of `spectrum ℝ A`) lies in `[-c, c]`. -/
theorem quadForm_iff_spectrum {ι : Type*} [Fintype ι] [DecidableEq ι] {A : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (c : ℝ) :
    (∀ v : ι → ℝ, |v ⬝ᵥ (A *ᵥ v)| ≤ c * (v ⬝ᵥ v)) ↔ ∀ μ ∈ spectrum ℝ A, |μ| ≤ c := by
  have hC : (algebraMap ℝ (Matrix ι ι ℝ) c).IsHermitian := by
    rw [Matrix.algebraMap_eq_diagonal]
    exact isHermitian_diagonal_of_self_adjoint _ (by
      ext i
      simp)
  have hN₁ : (algebraMap ℝ (Matrix ι ι ℝ) c - A).IsHermitian := hC.sub hA
  have hN₂ : (algebraMap ℝ (Matrix ι ι ℝ) c + A).IsHermitian := hC.add hA
  -- positive semidefiniteness of a real symmetric matrix through its spectrum
  have psd_iff : ∀ {N : Matrix ι ι ℝ}, N.IsHermitian →
      ((∀ v : ι → ℝ, 0 ≤ v ⬝ᵥ (N *ᵥ v)) ↔ ∀ μ ∈ spectrum ℝ N, 0 ≤ μ) := by
    intro N hN
    rw [hN.spectrum_real_eq_range_eigenvalues]
    have h := hN.posSemidef_iff_eigenvalues_nonneg
    rw [Matrix.posSemidef_iff_dotProduct_mulVec] at h
    simp only [star_trivial] at h
    constructor
    · rintro hv μ ⟨i, rfl⟩
      exact (h.mp ⟨hN, hv⟩) i
    · intro hμ
      exact (h.mpr fun i => hμ _ ⟨i, rfl⟩).2
  have hmul : ∀ v : ι → ℝ, algebraMap ℝ (Matrix ι ι ℝ) c *ᵥ v = c • v := by
    intro v
    rw [Algebra.algebraMap_eq_smul_one, Matrix.smul_mulVec, one_mulVec]
  have e₁ : ∀ v : ι → ℝ, v ⬝ᵥ ((algebraMap ℝ (Matrix ι ι ℝ) c - A) *ᵥ v) =
      c * (v ⬝ᵥ v) - v ⬝ᵥ (A *ᵥ v) := by
    intro v
    rw [sub_mulVec, dotProduct_sub, hmul, dotProduct_smul, smul_eq_mul]
  have e₂ : ∀ v : ι → ℝ, v ⬝ᵥ ((algebraMap ℝ (Matrix ι ι ℝ) c + A) *ᵥ v) =
      c * (v ⬝ᵥ v) + v ⬝ᵥ (A *ᵥ v) := by
    intro v
    rw [add_mulVec, dotProduct_add, hmul, dotProduct_smul, smul_eq_mul]
  have s₁ : spectrum ℝ (algebraMap ℝ (Matrix ι ι ℝ) c - A) = {c} - spectrum ℝ A :=
    (spectrum.singleton_sub_eq A c).symm
  have s₂ : spectrum ℝ (algebraMap ℝ (Matrix ι ι ℝ) c + A) = {c} + spectrum ℝ A :=
    (spectrum.singleton_add_eq A c).symm
  have p₁ := psd_iff hN₁
  have p₂ := psd_iff hN₂
  simp only [e₁, e₂, s₁, s₂, Set.singleton_sub, Set.singleton_add, Set.forall_mem_image,
    sub_nonneg] at p₁ p₂
  constructor
  · intro hv μ hμ
    have h1 := p₁.mp (fun v => by linarith [le_abs_self (v ⬝ᵥ (A *ᵥ v)), hv v]) hμ
    have h2 := p₂.mp (fun v => by linarith [neg_abs_le (v ⬝ᵥ (A *ᵥ v)), hv v]) hμ
    exact abs_le.mpr ⟨by linarith, h1⟩
  · intro hμ v
    have h1 := p₁.mpr (fun μ hμ' => (abs_le.mp (hμ μ hμ')).2) v
    have h2 := p₂.mpr (fun μ hμ' => by linarith [(abs_le.mp (hμ μ hμ')).1]) v
    exact abs_le.mpr ⟨by linarith, h1⟩

variable {p : ℕ} [Fact p.Prime]

/-- The four-cycle matrix `M` of `eq:dl:M` as a Mathlib matrix, indexed by
`𝒳 = {(x₁, x₂) ∈ ℙ¹ × ℙ¹ : x₁ ≠ x₂}` (the subtype of `distinctPairs p`). -/
noncomputable def fourCycleMat (p : ℕ) [Fact p.Prime] :
    Matrix (distinctPairs p) (distinctPairs p) ℝ :=
  fun x z => (fourCycleMatrix p x.1 z.1 : ℝ)

/-- `M` is real symmetric. -/
theorem fourCycleMat_isHermitian : (fourCycleMat p).IsHermitian := by
  ext x z
  simp only [conjTranspose_apply, star_trivial, fourCycleMat]
  rw [fourCycleMatrix_symm]

/-- **`thm:dl:K` as stated in the paper**: for every odd prime `p`, every eigenvalue of the real
symmetric matrix `M` (every element of `spectrum ℝ M`) lies in `[-2p, 2p]`. -/
def FourCycleSpectral : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ μ ∈ spectrum ℝ (fourCycleMat p), |μ| ≤ 2 * (p : ℝ)

/-- The quadratic form of `FourCycle` at `p` is the quadratic form of the matrix `fourCycleMat p`. -/
theorem quadForm_fourCycle_iff (p : ℕ) [Fact p.Prime] :
    (∀ v : Option (ZMod p) × Option (ZMod p) → ℝ,
      |∑ x ∈ distinctPairs p, ∑ z ∈ distinctPairs p, v x * (fourCycleMatrix p x z : ℝ) * v z| ≤
        2 * (p : ℝ) * ∑ x ∈ distinctPairs p, v x ^ 2) ↔
    ∀ w : distinctPairs p → ℝ,
      |w ⬝ᵥ (fourCycleMat p *ᵥ w)| ≤ 2 * (p : ℝ) * (w ⬝ᵥ w) := by
  have key : ∀ v : Option (ZMod p) × Option (ZMod p) → ℝ,
      (∑ x ∈ distinctPairs p, ∑ z ∈ distinctPairs p, v x * (fourCycleMatrix p x z : ℝ) * v z =
        (fun x : distinctPairs p => v x.1) ⬝ᵥ
          (fourCycleMat p *ᵥ fun x : distinctPairs p => v x.1)) ∧
      ∑ x ∈ distinctPairs p, v x ^ 2 =
        (fun x : distinctPairs p => v x.1) ⬝ᵥ (fun x : distinctPairs p => v x.1) := by
    intro v
    constructor
    · simp only [dotProduct, mulVec, fourCycleMat]
      rw [← sum_coe_sort (distinctPairs p)]
      refine sum_congr rfl fun x _ => ?_
      rw [← sum_coe_sort (distinctPairs p), mul_sum]
      exact sum_congr rfl fun z _ => by ring
    · simp only [dotProduct]
      rw [← sum_coe_sort (distinctPairs p)]
      exact sum_congr rfl fun x _ => by ring
  constructor
  · intro h w
    classical
    set v : Option (ZMod p) × Option (ZMod p) → ℝ :=
      fun x => if hx : x ∈ distinctPairs p then w ⟨x, hx⟩ else 0 with hv
    have hw : (fun x : distinctPairs p => v x.1) = w := by
      funext x
      simp only [hv, x.2, ↓reduceDIte]
    have := h v
    rw [(key v).1, (key v).2, hw] at this
    exact this
  · intro h v
    rw [(key v).1, (key v).2]
    exact h _

/-- **The transcription is faithful**: `Target.FourCycle` (the quadratic-form statement) is
equivalent to the literal statement of `thm:dl:K`, that every eigenvalue of the real symmetric
matrix `M` lies in `[-2p, 2p]` for every odd prime `p`. -/
theorem fourCycle_iff_spectral : Target.FourCycle ↔ FourCycleSpectral := by
  constructor
  · intro h p _ hp2
    exact (quadForm_iff_spectrum fourCycleMat_isHermitian _).mp
      ((quadForm_fourCycle_iff p).mp (h p hp2))
  · intro h p _ hp2
    exact (quadForm_fourCycle_iff p).mpr
      ((quadForm_iff_spectrum fourCycleMat_isHermitian _).mpr (h p hp2))

/-- `thm:dl:K` in terms of Mathlib's eigenvalues of the Hermitian matrix `M`: every eigenvalue
`λ_i` of `M` satisfies `|λ_i| ≤ 2p`. -/
theorem abs_eigenvalues_le (h : Target.FourCycle) (hp2 : p ≠ 2) (i : distinctPairs p) :
    |fourCycleMat_isHermitian.eigenvalues i| ≤ 2 * (p : ℝ) :=
  (fourCycle_iff_spectral.mp h) p hp2 _ (fourCycleMat_isHermitian.eigenvalues_mem_spectrum_real i)

end Sarkozy.DLK

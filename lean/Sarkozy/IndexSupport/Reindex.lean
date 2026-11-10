module

public import Sarkozy.IndexSupport.Operators

/-!
# Transport along a relabelling of the index space

For an equivalence `σ : Ω' ≃ Ω` of finite index spaces, sector systems, revelations and
sector operators on `Ω` transport to `Ω'` (matrices `M ↦ M.submatrix σ σ`, functions
`Z ↦ Z ∘ σ`), and the forms, means and energies of the index-support inequality are
invariant (`pairing_comp_equiv`, `vmean_comp_equiv`, `act_submatrix_comp`,
`Revelation.energy_reindex`).

This is the interface for a relabelling such as the Chinese remainder isomorphism
between the product coordinates `ℤ/Kℤ × ∏_p ℤ/p^{h_p}ℤ` used in
`Sarkozy/IndexSupport/CoupledIndex.lean` and the unsplit index `ℤ/Kℤ × ℤ/M_0ℤ` of
`def:hyb:coupled`(a): all results of this package hold for the transported data with the
same weights.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

variable {Ω Ω' : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω']

section Matrices

omit [Fintype Ω] [DecidableEq Ω] [Fintype Ω'] [DecidableEq Ω'] in
theorem submatrix_sum_equiv {S : Type*} (F : Finset S) (A : S → Matrix Ω Ω ℝ) (σ : Ω' ≃ Ω) :
    (∑ s ∈ F, A s).submatrix σ σ = ∑ s ∈ F, (A s).submatrix σ σ := by
  ext x y
  simp only [Matrix.submatrix_apply, Matrix.sum_apply]

omit [DecidableEq Ω] [DecidableEq Ω'] in
theorem meanMatrix_submatrix (σ : Ω' ≃ Ω) : (meanMatrix Ω).submatrix σ σ = meanMatrix Ω' := by
  ext x y
  simp only [Matrix.submatrix_apply, meanMatrix_apply, Fintype.card_congr σ]

omit [DecidableEq Ω] [DecidableEq Ω'] in
theorem RangeBound.submatrix {P A : Matrix Ω Ω ℝ} {c : ℝ} (h : RangeBound P A c)
    (σ : Ω' ≃ Ω) : RangeBound (P.submatrix σ σ) (A.submatrix σ σ) c := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
      h.maps]
  · have h2 := h.norm.submatrix σ
    have he : (c ^ 2 • P - P * Aᵀ * A * P).submatrix σ σ =
        c ^ 2 • P.submatrix σ σ - P.submatrix σ σ * (A.submatrix σ σ)ᵀ * A.submatrix σ σ *
          P.submatrix σ σ := by
      rw [Matrix.transpose_submatrix, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv,
        Matrix.submatrix_mul_equiv]
      ext x y
      rfl
    rwa [he] at h2

end Matrices

section Transport

variable {S : Type*} [Fintype S] [DecidableEq S]

/-- Transport of a sector system along `σ : Ω' ≃ Ω`. -/
def SectorSystem.reindex (H : SectorSystem Ω S) (σ : Ω' ≃ Ω) : SectorSystem Ω' S where
  proj s := (H.proj s).submatrix σ σ
  zero := H.zero
  transpose_proj s := by rw [Matrix.transpose_submatrix, H.transpose_proj]
  proj_mul_proj s t := by
    rw [Matrix.submatrix_mul_equiv, H.proj_mul_proj]
    split_ifs
    · rfl
    · ext x y
      rfl
  sum_proj := by
    rw [← submatrix_sum_equiv, H.sum_proj, Matrix.submatrix_one_equiv]
  proj_zero := by rw [H.proj_zero, meanMatrix_submatrix]

theorem SectorSystem.reindex_proj (H : SectorSystem Ω S) (σ : Ω' ≃ Ω) (s : S) :
    (H.reindex σ).proj s = (H.proj s).submatrix σ σ := rfl

/-- Transport of a sector operator: same weights. -/
theorem SectorOperator.reindex {H : SectorSystem Ω S} {T : Matrix Ω Ω ℝ} {δ : S → ℝ}
    (hT : SectorOperator H T δ) (σ : Ω' ≃ Ω) :
    SectorOperator (H.reindex σ) (T.submatrix σ σ) δ := by
  apply SectorOperator.of_rangeBound
  · intro s
    exact (hT.toRangeBound s).submatrix σ
  · change T.submatrix σ σ * (H.proj H.zero).submatrix σ σ = (H.proj H.zero).submatrix σ σ
    rw [Matrix.submatrix_mul_equiv, hT.mul_proj_zero]

/-- Transport of a revelation: same law and retained sets. -/
def Revelation.reindex {H : SectorSystem Ω S} {R : Type*} [Fintype R] (V : Revelation H R)
    (σ : Ω' ≃ Ω) : Revelation (H.reindex σ) R where
  law := V.law
  retained := V.retained
  zero_mem := V.zero_mem

theorem Revelation.reindex_prob {H : SectorSystem Ω S} {R : Type*} [Fintype R]
    (V : Revelation H R) (σ : Ω' ≃ Ω) (s : S) : (V.reindex σ).prob s = V.prob s := rfl

end Transport

section Invariance

variable {ι : Type*}

omit [DecidableEq Ω] [DecidableEq Ω'] in
theorem act_submatrix_comp (A : Matrix Ω Ω ℝ) (σ : Ω' ≃ Ω) (Z : Ω → ι → ℝ) :
    act (A.submatrix σ σ) (Z ∘ σ) = (act A Z) ∘ σ := by
  funext ω a
  simp only [act, Matrix.submatrix_apply, Function.comp_apply]
  exact Fintype.sum_equiv σ _ _ (fun η => rfl)

omit [DecidableEq Ω] [DecidableEq Ω'] in
theorem pairing_comp_equiv [Fintype ι] (M : Matrix ι ι ℝ) (σ : Ω' ≃ Ω) (X Y : Ω → ι → ℝ) :
    pairing M (X ∘ σ) (Y ∘ σ) = pairing M X Y := by
  simp only [pairing, Function.comp_apply, Fintype.card_congr σ]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun ω => rfl)

omit [DecidableEq Ω] [DecidableEq Ω'] in
theorem vmean_comp_equiv [Nonempty Ω] [Nonempty Ω'] (σ : Ω' ≃ Ω) (Z : Ω → ι → ℝ) :
    vmean (Z ∘ σ) = vmean Z := by
  funext a
  simp only [vmean, FiniteLaw.expect_uniform, Function.comp_apply, Fintype.card_congr σ]
  congr 1
  exact Fintype.sum_equiv σ _ _ (fun ω => rfl)

theorem Revelation.reveal_reindex {S : Type*} [Fintype S] [DecidableEq S]
    {H : SectorSystem Ω S} {R : Type*} [Fintype R] (V : Revelation H R) (σ : Ω' ≃ Ω) (r : R)
    (Z : Ω → ι → ℝ) : (V.reindex σ).reveal r (Z ∘ σ) = (V.reveal r Z) ∘ σ := by
  unfold Revelation.reveal
  change act (∑ s ∈ V.retained r, (H.proj s).submatrix σ σ) (Z ∘ σ) = _
  rw [← submatrix_sum_equiv, act_submatrix_comp]

theorem Revelation.energy_reindex [Fintype ι] {S : Type*} [Fintype S] [DecidableEq S]
    {H : SectorSystem Ω S} {R : Type*} [Fintype R] (V : Revelation H R) (σ : Ω' ≃ Ω)
    (M : Matrix ι ι ℝ) (Z : Ω → ι → ℝ) :
    (V.reindex σ).energy M (Z ∘ σ) = V.energy M Z := by
  unfold Revelation.energy
  simp only [Revelation.reveal_reindex, pairing_comp_equiv]
  rfl

end Invariance

end Sarkozy.IndexSupport

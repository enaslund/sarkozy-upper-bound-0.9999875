module

public import Sarkozy.UpperReference.ObservedSchurTest

/-!
# `prop:observed-caps`: from the Schur tests to `-kI ⪯ M(±i) ⪯ kI` (`rem:realified-gates`)

`paper/sections/25_upper_reference.tex`, `prop:observed-caps`, "Schur tests": "`‖M(±i)‖ ≤ k`
follows from the rational tests `k²I - B_⋆B_⋆ᵀ ± ikD ⪰ 0`". On a mode of `Φ̂` with eigenvalue
`σ = ±i`, the complete star matrix is the Hermitian block matrix
`M(σ) = [[σD, B_⋆], [B_⋆ᴴ, 0]]`. By the Schur complement (`Matrix.PosDef.fromBlocks₂₂`, with the
lower right block `kI ≻ 0`),
`kI - M(σ) ⪰ 0 ⟺ k²I - B_⋆B_⋆ᴴ - kσD ⪰ 0` and `kI + M(σ) ⪰ 0 ⟺ k²I - B_⋆B_⋆ᴴ + kσD ⪰ 0`,
so the tests for both signs give `-kI ⪯ M(σ) ⪯ kI` for both `σ`.

* `gates_of_tests`: the general step, for any `D`, `B`, `k > 0`.
* `starB_full`, `full_gram`: the matrix `B_⋆` of the full star matrix (rows the eighteen labels,
  columns the `162` supports) and `B_⋆B_⋆ᴴ = (gram)`; **`full_gates`**: `-6I ⪯ M(±i) ⪯ 6I`.
* `starB_merge`, `merge_gram`: the principal block of the merge (rows its twelve observed labels,
  columns its sixty visible supports) and `B_vB_vᴴ = I`; **`merge_gates`**:
  `-kI ⪯ M_vv(±i) ⪯ kI`, `k = 2.188902`.

`ObservedNorm.lean` turns these into `‖M(±i)‖ ≤ k` (`SpectralC.NormLe`). The passage from the
modes `M(±i)` to the operator `M(Φ̂)` on `L²` is S1's `SpectralD.StarMatrix.norm_blockForm_le`; the
identification of S1's `starM0`, `starM1` for EL22 with the matrices here is not done.
-/

@[expose] public section

open scoped Matrix ComplexOrder ComplexConjugate
open Matrix

namespace Sarkozy.UpperReference.Observed

/-- **`rem:realified-gates`, the Schur complement step.** For a Hermitian block matrix
`M(σ) = [[σD, B], [Bᴴ, 0]]` with `(σD)ᴴ = σD` and `k > 0`: if `k²I - BBᴴ - kσD ⪰ 0` and
`k²I - BBᴴ + kσD ⪰ 0`, then `kI - M(σ) ⪰ 0` and `kI + M(σ) ⪰ 0`. -/
theorem gates_of_tests {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (Y : Matrix m m ℂ) (B : Matrix m n ℂ) {k : ℝ} (hk : 0 < k)
    (hminus : ((((k ^ 2 : ℝ) : ℂ) • (1 : Matrix m m ℂ)) - B * Bᴴ - (k : ℂ) • Y).PosSemidef)
    (hplus : ((((k ^ 2 : ℝ) : ℂ) • (1 : Matrix m m ℂ)) - B * Bᴴ + (k : ℂ) • Y).PosSemidef) :
    ((k : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks Y B Bᴴ 0).PosSemidef ∧
      ((k : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) + fromBlocks Y B Bᴴ 0).PosSemidef := by
  have hk0 : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  have hDpd : ((k : ℂ) • (1 : Matrix n n ℂ)).PosDef :=
    Matrix.PosDef.one.smul (RCLike.ofReal_pos.mpr hk)
  let _ : Invertible ((k : ℂ) • (1 : Matrix n n ℂ)) :=
    ⟨((k : ℂ)⁻¹) • (1 : Matrix n n ℂ), by rw [smul_mul_smul_comm, inv_mul_cancel₀ hk0, one_mul,
      one_smul], by rw [smul_mul_smul_comm, mul_inv_cancel₀ hk0, one_mul, one_smul]⟩
  have hinv : ((k : ℂ) • (1 : Matrix n n ℂ))⁻¹ = ((k : ℂ)⁻¹) • (1 : Matrix n n ℂ) :=
    Matrix.inv_eq_left_inv (by rw [smul_mul_smul_comm, inv_mul_cancel₀ hk0, one_mul, one_smul])
  have hscale : ∀ X : Matrix m m ℂ, X.PosSemidef → ((k : ℂ)⁻¹ • X).PosSemidef := fun X hX =>
    hX.smul (by
      rw [← Complex.ofReal_inv]
      exact RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr hk.le))
  have h1 : (k : ℂ)⁻¹ * ((k ^ 2 : ℝ) : ℂ) = k := by
    push_cast
    field_simp
  have h2 : (k : ℂ)⁻¹ * (k : ℂ) = 1 := inv_mul_cancel₀ hk0
  constructor
  · have e : (k : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) - fromBlocks Y B Bᴴ 0 =
        fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) - Y) (-B) (-B)ᴴ
          ((k : ℂ) • (1 : Matrix n n ℂ)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [one_apply]
    rw [e, Matrix.PosDef.fromBlocks₂₂ _ _ hDpd, hinv]
    have h := hscale _ hminus
    convert h using 1
    simp only [conjTranspose_neg, Matrix.neg_mul, Matrix.mul_neg, Matrix.mul_smul,
      Matrix.mul_one, Matrix.smul_mul]
    rw [smul_sub, smul_sub, smul_smul, smul_smul, h1, h2, one_smul]
    module
  · have e : (k : ℂ) • (1 : Matrix (m ⊕ n) (m ⊕ n) ℂ) + fromBlocks Y B Bᴴ 0 =
        fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Y) B Bᴴ ((k : ℂ) • (1 : Matrix n n ℂ)) := by
      ext i j
      rcases i with i | i <;> rcases j with j | j <;> simp [one_apply]
    rw [e, Matrix.PosDef.fromBlocks₂₂ _ _ hDpd, hinv]
    have h := hscale _ hplus
    convert h using 1
    simp only [Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
    rw [smul_add, smul_sub, smul_smul, smul_smul, h1, h2, one_smul]
    module

/-- The star coefficients `B_⋆` of the full star matrix of EL22: rows the eighteen labels, columns
the `162` supports. -/
noncomputable def starBfull : Matrix Half {S // S ∈ supports} ℂ := fun j S => (starB j S.1 : ℂ)

/-- `B_⋆B_⋆ᴴ` is the Gram matrix `gram` over the supports. -/
theorem full_gram : starBfull * starBfullᴴ = Matrix.of (fun j j' => (gram j j' : ℂ)) := by
  ext j j'
  simp only [mul_apply, conjTranspose_apply, starBfull, star_intCast, of_apply, gram]
  push_cast
  exact Finset.sum_coe_sort supports (fun S => (starB j S : ℂ) * (starB j' S : ℂ))

/-- **`‖M(±i)‖ ≤ 6` for the full star matrix of EL22** (`prop:observed-caps`), as
`-6I ⪯ M(σ) ⪯ 6I` for `σ = ±i`, `M(σ) = [[σD, B_⋆], [B_⋆ᴴ, 0]]`. -/
theorem full_gates (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    (((6 : ℝ) : ℂ) • (1 : Matrix (Half ⊕ {S // S ∈ supports}) (Half ⊕ {S // S ∈ supports}) ℂ) -
        fromBlocks (σ • toC Dfull) starBfull starBfullᴴ 0).PosSemidef ∧
      (((6 : ℝ) : ℂ) • (1 : Matrix (Half ⊕ {S // S ∈ supports}) (Half ⊕ {S // S ∈ supports}) ℂ) +
        fromBlocks (σ • toC Dfull) starBfull starBfullᴴ 0).PosSemidef := by
  have hσ' : -σ = Complex.I ∨ -σ = -Complex.I := by
    rcases hσ with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  refine gates_of_tests (σ • toC Dfull) starBfull (k := 6) (by norm_num) ?_ ?_
  · convert full_schur_test (-σ) hσ' using 1
    rw [full_gram]
    push_cast
    module
  · convert full_schur_test σ hσ using 1
    rw [full_gram]
    push_cast
    module

/-- The merge's observed labels are the images of the embedding, which is injective. -/
theorem mergeEmb_mem : ∀ a, mergeEmb a ∈ mergeObs := by
  decide +kernel

theorem mergeEmb_inj : ∀ a a', mergeEmb a = mergeEmb a' → a = a' := by
  decide +kernel

/-- The principal block `B_v` of the merge: rows its twelve observed labels, columns its sixty
visible supports. -/
noncomputable def starBmerge :
    Matrix MHalf {S // S ∈ supports.filter (fun S => S ⊆ mergeObs)} ℂ :=
  fun a S => (starB (mergeEmb a) S.1 : ℂ)

/-- **`B_vB_vᴴ = I`** on the merge's singleton rows (`merge_singleton_gram`). -/
theorem merge_gram : starBmerge * starBmergeᴴ = 1 := by
  ext a a'
  simp only [mul_apply, conjTranspose_apply, starBmerge, star_intCast, one_apply]
  have h := merge_singleton_gram (mergeEmb a) (mergeEmb_mem a) (mergeEmb a') (mergeEmb_mem a')
  have h' := congrArg (fun z : ℤ => (z : ℂ)) h
  simp only [Int.cast_sum, Int.cast_mul] at h'
  rw [Finset.sum_coe_sort (supports.filter (fun S => S ⊆ mergeObs))
    (fun S => (starB (mergeEmb a) S : ℂ) * (starB (mergeEmb a') S : ℂ)), h']
  by_cases haa : a = a'
  · subst haa
    simp
  · have hne : mergeEmb a ≠ mergeEmb a' := fun he => haa (mergeEmb_inj a a' he)
    simp [hne, haa]

/-- **`‖M_vv(±i)‖ ≤ 2.188902` for the merge's principal star matrix** (`prop:observed-caps`), as
`-kI ⪯ M_vv(σ) ⪯ kI`, `k = 2188902/10⁶`, `M_vv(σ) = [[σD_v, B_v], [B_vᴴ, 0]]`. -/
theorem merge_gates (σ : ℂ) (hσ : σ = Complex.I ∨ σ = -Complex.I) :
    ((((2188902 / 1000000 : ℝ)) : ℂ) • (1 : Matrix (MHalf ⊕
        {S // S ∈ supports.filter (fun S => S ⊆ mergeObs)})
        (MHalf ⊕ {S // S ∈ supports.filter (fun S => S ⊆ mergeObs)}) ℂ) -
        fromBlocks (σ • Dc) starBmerge starBmergeᴴ 0).PosSemidef ∧
      ((((2188902 / 1000000 : ℝ)) : ℂ) • (1 : Matrix (MHalf ⊕
        {S // S ∈ supports.filter (fun S => S ⊆ mergeObs)})
        (MHalf ⊕ {S // S ∈ supports.filter (fun S => S ⊆ mergeObs)}) ℂ) +
        fromBlocks (σ • Dc) starBmerge starBmergeᴴ 0).PosSemidef := by
  have hσ' : -σ = Complex.I ∨ -σ = -Complex.I := by
    rcases hσ with h | h <;> rw [h]
    · exact Or.inr rfl
    · exact Or.inl (neg_neg _)
  refine gates_of_tests (σ • Dc) starBmerge (k := 2188902 / 1000000) (by norm_num) ?_ ?_
  · convert merge_schur_test (-σ) hσ' using 1
    rw [merge_gram]
    push_cast
    module
  · convert merge_schur_test σ hσ using 1
    rw [merge_gram]
    push_cast
    module

end Sarkozy.UpperReference.Observed

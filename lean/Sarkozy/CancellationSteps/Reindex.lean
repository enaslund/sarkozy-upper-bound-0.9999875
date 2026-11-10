module

public import Sarkozy.Functional.FibreScale

/-!
# Reindexing the coordinates of a residue space

For an equivalence `e : ι ≃ ι'` of coordinate sets and moduli `m` on `ι'`, the residue spaces
`∏_{i ∈ ι} ℤ/m_{e(i)}` and `∏_{c ∈ ι'} ℤ/m_c` are identified by `reindexLabel e m`. The Fourier
coefficients, characters, support denominators and integer residues correspond:
`groupCoeff_reindex`, `prodChar_reindex`, `supportDenominator_reindex`,
`integerResidue_reindex`. Used to read the fibre formula of `lem:record:fibre-scale`(a) (stated
on the free coordinates `{c // c ∉ E}` of the joined group) on the free tail primes
`{k // U k = false}` of `lem:record:density-can`, Step 3.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

variable {ι ι' : Type*} [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] (e : ι ≃ ι')
  (m : ι' → ℕ) [∀ c, NeZero (m c)]

/-- The identification `∏_{i} ℤ/m_{e(i)} ≃ ∏_{c} ℤ/m_c`. -/
def reindexLabel : ResidueSpace (fun i => m (e i)) ≃ ResidueSpace m :=
  Equiv.piCongrLeft (fun c => ZMod (m c)) e

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] [∀ c, NeZero (m c)] in
@[simp] lemma reindexLabel_apply (y : ResidueSpace (fun i => m (e i))) (i : ι) :
    reindexLabel e m y (e i) = y i :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

omit [DecidableEq ι] [DecidableEq ι'] in
lemma prodChar_reindex (a y : ResidueSpace (fun i => m (e i))) :
    prodChar m (reindexLabel e m a) (reindexLabel e m y) = prodChar (fun i => m (e i)) a y := by
  unfold prodChar
  rw [← e.prod_comp]
  simp only [reindexLabel_apply]

omit [Fintype ι] [Fintype ι'] [DecidableEq ι] [DecidableEq ι'] [∀ c, NeZero (m c)] in
lemma integerResidue_reindex (n : ℤ) :
    reindexLabel e m (integerResidue (fun i => m (e i)) n) = integerResidue m n := by
  funext c
  obtain ⟨i, rfl⟩ := e.surjective c
  rw [reindexLabel_apply]
  rfl

omit [DecidableEq ι] [DecidableEq ι'] [∀ c, NeZero (m c)] in
lemma supportDenominator_reindex (a : ResidueSpace (fun i => m (e i))) :
    supportDenominator (fun i => m (e i)) a = supportDenominator m (reindexLabel e m a) := by
  classical
  unfold supportDenominator primeSupport
  rw [prod_filter, prod_filter, ← e.prod_comp]
  simp only [reindexLabel_apply]

/-- The Fourier coefficient is invariant under reindexing. -/
lemma groupCoeff_reindex (f : ResidueSpace (fun i => m (e i)) → ℂ)
    (a : ResidueSpace (fun i => m (e i))) :
    groupCoeff (fun i => m (e i)) f a =
      groupCoeff m (fun y => f ((reindexLabel e m).symm y)) (reindexLabel e m a) := by
  unfold groupCoeff
  refine (Fintype.expect_equiv (reindexLabel e m) _ _ fun y => ?_)
  simp only [Equiv.symm_apply_apply, prodChar_reindex]

end Sarkozy.CancellationSteps

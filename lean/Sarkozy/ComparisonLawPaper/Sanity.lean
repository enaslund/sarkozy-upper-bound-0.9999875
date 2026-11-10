module

public import Sarkozy.ComparisonLawPaper.Deletion
public import Sarkozy.MainAnchor.PaperQueries

@[expose] public section



open Finset
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.RecordExpansion

/-- The uniform law on labellings by one letter. -/
noncomputable def toyLaw : FiniteLaw (Slot → Unit) := FiniteLaw.uniform (Slot → Unit)

theorem toyLaw_symmetric : IsSymmetricAt reservedCut (signedIntegral toyLaw.weight) := by
  unfold IsSymmetricAt
  apply LinearMap.ext
  intro f
  rw [reflect_apply]
  congr 1

theorem toyLaw_uniform : HasUniformMarginals toyLaw := by
  intro v f
  have h : (fun z : Slot → Unit => f (z v)) = fun _ => f () := funext fun _ => rfl
  rw [FiniteLaw.expect_uniform, h, FiniteLaw.expect_const]
  simp

/-- **A toy deletion** of mass `1/2`: `μ = κ̄ = ν̄` the uniform law,
`(1 - 1/2) ν̄ = μ - (1/2) κ̄`. -/
noncomputable def toyDeletion :
    DeletionInputs toyLaw (fun _ _ => True) MainAnchor.paperQueries where
  κ := toyLaw
  ω := 1 / 2
  ω_nonneg := by norm_num
  ω_lt_one := by norm_num
  ν := toyLaw
  decomp z := by ring
  κ_sym := toyLaw_symmetric
  κ_unif := toyLaw_uniform
  accept _ _ _ := trivial

/-- The toy deletion is priced `ω q^{2a} = q^{2a}/2` in the symmetric total and `0` in the skew
one. -/
theorem toyDeletion_prices (sel : ℝ) :
    (toyDeletion.toAtom toyLaw_uniform).sprice sel = 1 / 2 * sel ∧
      (toyDeletion.toAtom toyLaw_uniform).aprice sel = 0 :=
  ⟨toyDeletion.toAtom_sprice toyLaw_uniform sel, toyDeletion.toAtom_aprice toyLaw_uniform sel⟩

end Sarkozy.ComparisonLawPaper

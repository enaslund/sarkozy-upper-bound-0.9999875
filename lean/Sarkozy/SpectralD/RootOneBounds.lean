module

public import Sarkozy.SpectralD.RootOneChecks
public import Sarkozy.SpectralD.MatrixCertificate

/-!
# Class-one upper bounds for the root model matrices

Exact absolute row sums of the graph-verified tables give the quadratic
form bounds needed by the coupling estimate.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset Sarkozy.SpectralC

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem LL20_gramOne_rows : ∀ i : LL20.cut.Half,
    ∑ j, |gramOne LL20.cut i j| ≤ 8928 := by
  have h : ∀ i : LL20.cut.Half,
      ∑ j : LL20.cut.Half,
        |oneEntry LL20_HOneTable (slotCode i.1) (slotCode j.1)| ≤ 8928 := by
    decide +kernel
  simpa only [LL20_gramOne_table] using h

theorem LL20_plusOne_rows : ∀ i : LL20.cut.Half,
    ∑ j, |plusOne LL20.cut i j| ≤ 12384 := by
  have h : ∀ i : LL20.cut.Half,
      ∑ j : LL20.cut.Half,
        |oneEntry LL20_HplusOneTable (slotCode i.1) (slotCode j.1)| ≤ 12384 := by
    decide +kernel
  simpa only [LL20_plusOne_table] using h

theorem LL22_gramOne_rows : ∀ i : LL22.cut.Half,
    ∑ j, |gramOne LL22.cut i j| ≤ 1492 := by
  have h : ∀ i : LL22.cut.Half,
      ∑ j : LL22.cut.Half,
        |oneEntry LL22_HOneTable (slotCode i.1 / 2) (slotCode j.1 / 2)| ≤ 1492 := by
    decide +kernel
  simpa only [LL22_gramOne_table] using h

theorem LL22_plusOne_rows : ∀ i : LL22.cut.Half,
    ∑ j, |plusOne LL22.cut i j| ≤ 1592 := by
  have h : ∀ i : LL22.cut.Half,
      ∑ j : LL22.cut.Half,
        |oneEntry LL22_HplusOneTable (slotCode i.1 / 2) (slotCode j.1 / 2)| ≤ 1592 := by
    decide +kernel
  simpa only [LL22_plusOne_table] using h

variable {p : ℕ} [Fact p.Prime]

theorem LL20_lamH_one (hp1 : p % 4 = 1) (x : LL20.cut.Half → ℂ) :
    (qform (PaleyB.modelHC LL20.Nset (Cx.sgnZ (p := p) LL20)) x).re ≤
      8928 * ∑ j, ‖x j‖ ^ 2 := by
  have hM : PaleyB.modelHC LL20.Nset (Cx.sgnZ (p := p) LL20) =
      (fun i j => (gramOne LL20.cut i j : ℂ)) := by
    funext i j
    exact modelHC_one_eq LL20 rfl hp1 i j
  rw [hM]
  exact qform_le_of_integer_rows _ (gramOne_symm LL20.cut) 8928 LL20_gramOne_rows x

theorem LL20_plus_one (hp1 : p % 4 = 1) (x : LL20.cut.Half → ℂ) :
    (qform (PaleyB.hplusM halfAdjB LL20.Nset (Cx.sgnZ (p := p) LL20)) x).re ≤
      12384 * ∑ j, ‖x j‖ ^ 2 := by
  have hM : PaleyB.hplusM halfAdjB LL20.Nset (Cx.sgnZ (p := p) LL20) =
      (fun i j => (plusOne LL20.cut i j : ℂ)) := by
    funext i j
    exact hplusM_one_eq LL20 rfl hp1 i j
  rw [hM]
  exact qform_le_of_integer_rows _ (plusOne_symm LL20.cut) 12384 LL20_plusOne_rows x

theorem LL22_lamH_one (hp1 : p % 4 = 1) (x : LL22.cut.Half → ℂ) :
    (qform (PaleyB.modelHC LL22.Nset (Cx.sgnZ (p := p) LL22)) x).re ≤
      1492 * ∑ j, ‖x j‖ ^ 2 := by
  have hM : PaleyB.modelHC LL22.Nset (Cx.sgnZ (p := p) LL22) =
      (fun i j => (gramOne LL22.cut i j : ℂ)) := by
    funext i j
    exact modelHC_one_eq LL22 rfl hp1 i j
  rw [hM]
  exact qform_le_of_integer_rows _ (gramOne_symm LL22.cut) 1492 LL22_gramOne_rows x

theorem LL22_plus_one (hp1 : p % 4 = 1) (x : LL22.cut.Half → ℂ) :
    (qform (PaleyB.hplusM halfAdjB LL22.Nset (Cx.sgnZ (p := p) LL22)) x).re ≤
      1592 * ∑ j, ‖x j‖ ^ 2 := by
  have hM : PaleyB.hplusM halfAdjB LL22.Nset (Cx.sgnZ (p := p) LL22) =
      (fun i j => (plusOne LL22.cut i j : ℂ)) := by
    funext i j
    exact hplusM_one_eq LL22 rfl hp1 i j
  rw [hM]
  exact qform_le_of_integer_rows _ (plusOne_symm LL22.cut) 1592 LL22_plusOne_rows x

end Sarkozy.SpectralD.Root

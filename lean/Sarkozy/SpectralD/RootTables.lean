module

public import Sarkozy.SpectralD.RootCriterion
public import Sarkozy.SpectralD.RootModelH
public import Sarkozy.SpectralD.RootTableData






@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SpectralD.Root

open Sarkozy

theorem LL20_sgn_table : ∀ j k : LL20.cut.Half,
    LL20.sgn j k = tableEntry LL20_sigTable (slotCode j.1) (slotCode k.1) := by
  intro j k
  rw [sgn_eq LL20 LL20_G]
  revert j k
  decide +kernel

theorem LL22_sgn_table : ∀ j k : LL22.cut.Half,
    LL22.sgn j k = tableEntry LL22_sigTable (slotCode j.1 / 2) (slotCode k.1 / 2) := by
  intro j k
  rw [sgn_eq LL22 LL22_G]
  revert j k
  decide +kernel

/-- **`𝐇` of LL20 at `p ≡ 3 (mod 4)` is the explicit table `LL20_Htable`.** -/
theorem LL20_hMat_table : ∀ k l : LL20.cut.Half,
    hMat LL20 k l = tableEntryShift LL20_Htable (slotCode k.1) (slotCode l.1) := by
  intro k l
  rw [hMat_eq_hB LL20 LL20_G]
  revert k l
  decide +kernel

/-- **`𝐇` of LL22 at `p ≡ 3 (mod 4)` is the explicit table `LL22_Htable`.** -/
theorem LL22_hMat_table : ∀ k l : LL22.cut.Half,
    hMat LL22 k l = tableEntryShift LL22_Htable (slotCode k.1 / 2) (slotCode l.1 / 2) := by
  intro k l
  rw [hMat_eq_hB LL22 LL22_G]
  revert k l
  decide +kernel

/-! ### Edge counts -/

theorem halfGraph_card_eq (D : Cuts.SpecData Slot) (hG : D.G = Labellings.rootGraph) :
    D.halfGraph.E.card =
      (univ.filter (fun e : D.cut.Half × D.cut.Half => edgeB e.1.1 e.2.1 = true)).card := by
  congr 1
  ext e
  simp only [Cuts.SpecData.mem_halfGraph, mem_filter, mem_univ, true_and, mem_E D hG]

theorem mcross_eq_bool (D : Cuts.SpecData Slot) (hG : D.G = Labellings.rootGraph) :
    D.mcross =
      (univ.filter (fun q : D.cut.Half × D.cut.Half => sgnB D.cut.flip q.1.1 q.2.1 ≠ 0)).card := by
  unfold Cuts.SpecData.mcross Cuts.SpecData.crossPairs
  congr 1
  ext q
  simp only [mem_filter, mem_univ, true_and, sgn_eq D hG]

/-- The LL20 half graph `G_{FL,2}` has `168` edges (`subsec:record:upper_root`). -/
theorem LL20_halfGraph_card : LL20.halfGraph.E.card = 168 := by
  rw [halfGraph_card_eq LL20 LL20_G]
  decide +kernel

/-- The LL22 half graph `G_{LL,1}` has `180` edges (`subsec:record:upper_root`). -/
theorem LL22_halfGraph_card : LL22.halfGraph.E.card = 180 := by
  rw [halfGraph_card_eq LL22 LL22_G]
  decide +kernel

/-- `m_× = 384` for LL20 (`lem:spec:elementary`: the number of cross edges). -/
theorem LL20_mcross : LL20.mcross = 384 := by
  rw [mcross_eq_bool LL20 LL20_G]
  decide +kernel

/-- `m_× = 360` for LL22 (`lem:spec:elementary`: the number of cross edges). -/
theorem LL22_mcross : LL22.mcross = 360 := by
  rw [mcross_eq_bool LL22 LL22_G]
  decide +kernel

end Sarkozy.SpectralD.Root

module

public import Sarkozy.SpectralD.RootOneFast.LL20
public import Sarkozy.SpectralD.RootOneFast.LL22

/-!
# Kernel checks for the class-one root model tables

Every table entry is checked against the graph definition, including the
coverable-subset count in Hplus. The source JSON is not trusted. The checks
run on codes of the half (`RootOneFast.LL20`, `RootOneFast.LL22`): the
neighbourhoods and the adjacency are tabulated against the graph, and the
coverable subsets are enumerated as bit masks, which keeps the kernel work
and memory small.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

theorem LL20_code_lt : ∀ i : LL20.cut.Half, slotCode i.1 < 36 := by
  decide +kernel

theorem LL20_gramOne_table : ∀ i j : LL20.cut.Half,
    gramOne LL20.cut i j = oneEntry LL20_HOneTable (slotCode i.1) (slotCode j.1) := by
  intro i j
  rw [gramOne, LL20_card_common]
  exact LL20_gram_codes _ (LL20_code_lt i) _ (LL20_code_lt j)

theorem LL20_plusOne_table : ∀ i j : LL20.cut.Half,
    plusOne LL20.cut i j = oneEntry LL20_HplusOneTable (slotCode i.1) (slotCode j.1) := by
  intro i j
  rw [plusOne, LL20_gramOne_table, coverOne, LL20_coverCount_common,
    LL20_cover_codes _ (LL20_code_lt i) _ (LL20_code_lt j)]
  ring

theorem LL22_code_lt : ∀ i : LL22.cut.Half, slotCode i.1 < 72 := by
  decide +kernel

theorem LL22_gramOne_table : ∀ i j : LL22.cut.Half,
    gramOne LL22.cut i j = oneEntry LL22_HOneTable (slotCode i.1 / 2) (slotCode j.1 / 2) := by
  intro i j
  have hi := LL22_code_lt i
  have hj := LL22_code_lt j
  rw [gramOne, LL22_card_common]
  exact LL22_gram_codes _ (by omega) _ (by omega)

theorem LL22_plusOne_table : ∀ i j : LL22.cut.Half,
    plusOne LL22.cut i j = oneEntry LL22_HplusOneTable (slotCode i.1 / 2) (slotCode j.1 / 2) := by
  intro i j
  have hi := LL22_code_lt i
  have hj := LL22_code_lt j
  rw [plusOne, LL22_gramOne_table, coverOne, LL22_coverCount_common,
    LL22_cover_codes _ (by omega) _ (by omega)]
  ring

end Sarkozy.SpectralD.Root

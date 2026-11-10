module

public import Sarkozy.BlockAdapter.E21

@[expose] public section

/-!
# Sanity checks of the block adapter's spectral data

* The cuts have the paper's sizes: `|U⁺| = 6` for L20 and L21 (`G_{L,2}`), `3` for L10
  (`G_{L,1}`) and E21 (`G_{E,2}`); the half graph of L20 has the `4` edges of `G_{F,2}`
  (`(0, ℓ) → (2, ℓ')`) and that of L10 the single edge of `G_{F,1}`.
* `LayerCutCap` is satisfiable: for E21 it is proved at the recorded constants
  (`middleE21Caps_proved`), here restated at every prime `p ≥ 2²⁴` with `g = 1/100`, `B = 0`.
-/

open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.Cuts

theorem recordData_two_n : (recordData (Fin 2)).n = 6 := by
  unfold SpecData.n
  rw [← Fintype.card_coe, Fintype.card_congr (recordHalfEquiv (Fin 2))]
  simp

theorem recordData_one_n : (recordData (Fin 1)).n = 3 := by
  unfold SpecData.n
  rw [← Fintype.card_coe, Fintype.card_congr (recordHalfEquiv (Fin 1))]
  simp

theorem recordLayer_n : recordLayer.n = 6 := by
  unfold SpecData.n
  rw [← Fintype.card_coe,
    Fintype.card_congr (layerHalfEquiv (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap)]
  simp

theorem matchLayer_n : matchLayer.n = 3 := by
  unfold SpecData.n
  rw [← Fintype.card_coe]
  exact card_matchHalf

theorem foldGraph_two_card : (foldGraph (Fin 2)).E.card = 4 := by
  unfold foldGraph
  decide

theorem foldGraph_one_card : (foldGraph (Fin 1)).E.card = 1 := by
  unfold foldGraph
  decide

/-- `LayerCutCap` is satisfiable (E21 at `g = 1/100`, `B = 0`, every prime `p ≥ 2²⁴`). -/
theorem e21_layerCutCap_example (p : ℕ) [Fact p.Prime] (hp : 2 ^ 24 ≤ p) :
    LayerCutCap (Fin 3) (matchGraph (Fin 2)) matchGraph_swap (1 / 100) 0 p := by
  have hp' : ((2 : ℝ) ^ 12) ^ 2 ≤ p := by
    have : ((2 ^ 24 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
    norm_num at this ⊢
    linarith
  have hp9 : (9 : ℝ) < p := by nlinarith
  exact e21_layerCutCap le_rfl hp9
    (e21_gate (by norm_num) (by norm_num) (by norm_num) hp' hp9)

end Sarkozy.BlockAdapter

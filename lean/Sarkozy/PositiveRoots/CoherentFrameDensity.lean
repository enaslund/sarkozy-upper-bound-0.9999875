module

public import Sarkozy.SpectralD.GraphLawBridge
public import Sarkozy.L20Cap.RectGraph

/-! Pivot density on the six-label, degree-two half laws used by the coherent kernel. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.Labellings Sarkozy.SpectralC Sarkozy.SpectralD

theorem degree_two_price {q : ℝ} (hq : 64 ≤ q) {d : ℕ} (hd : d ≤ 2) :
    0 < q - softError q d - 2 ^ d * 5 ∧
      2 ^ d / (q - softError q d - 2 ^ d * 5) ≤ 8 / q := by
  have hden : 0 < q - softError q d - 2 ^ d * 5 := by
    interval_cases d <;> norm_num [softError, gradedA, gradedB] <;> linarith
  refine ⟨hden, ?_⟩
  rw [div_le_div_iff₀ hden (by linarith : 0 < q)]
  interval_cases d <;> norm_num [softError, gradedA, gradedB] <;> linarith

variable {p : ℕ} [Fact p.Prime]

theorem graph_pivot_density (hW : WeilBound (ZMod p)) (hp : 64 ≤ p)
    (G : OrientedGraph (Fin 6)) (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2) (j : Fin 6)
    (x : Fin 6 → ZMod p) (t : ZMod p) (hx : graphWeight G hne x ≠ 0) :
    condLaw (graphWeight G hne) j x t ≤ 8 / (p : ℝ) := by
  have he : (Fintype.card (Fin 6) : ℝ) - 1 = 5 := by norm_num
  obtain ⟨hden, hprice⟩ := degree_two_price (q := p) (by exact_mod_cast hp) (hdeg j)
  have hden' : 0 < (p : ℝ) - softError p (nbrCount G (univ.erase j) j) -
      2 ^ nbrCount G (univ.erase j) j * ((Fintype.card (Fin 6) : ℝ) - 1) := by
    rw [he]
    exact hden
  have h := graphWeight_condLaw_le hW G hne j hden' x t hx
  rw [he] at h
  exact h.trans hprice

omit [Fact p.Prime] in
theorem g6_degree : ∀ j : Fin 6, nbrCount Sarkozy.L20Cap.G6 (univ.erase j) j ≤ 2 := by
  decide +kernel

end Sarkozy.PositiveRoots.CoherentFrame

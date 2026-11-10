module

public import Sarkozy.JointRows.StarDictionaryAllPrimes

/-! Star kernels commute with bijective changes of row coordinates. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset

variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

omit [DecidableEq X] [DecidableEq Y] in
theorem sum_sets2_product (e : X ≃ Y) (a : Y → ℝ) :
    (∑ T ∈ sets2 Y, ∏ j ∈ T, a j) = ∑ S ∈ sets2 X, ∏ i ∈ S, a (e i) := by
  simp only [sets2, sum_filter]
  rw [← e.finsetCongr.sum_comp]
  simp only [Equiv.finsetCongr_apply, card_map, prod_map, Equiv.coe_toEmbedding]

variable {p : ℕ} [Fact p.Prime]

omit [DecidableEq X] [DecidableEq Y] in
theorem starKernel_equiv (e : X ≃ Y) (D : Y → Y → ℝ) (x y : Y → ZMod p) :
    starKernel D (sets2 Y) x y =
      starKernel (fun i j => D (e i) (e j)) (sets2 X) (x ∘ e) (y ∘ e) := by
  have h1 : (∑ i, ∑ j, D i j * PaleyGauss.chiR p (y j - x i)) =
      ∑ i, ∑ j, D (e i) (e j) * PaleyGauss.chiR p (y (e j) - x (e i)) := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun i _ => (e.sum_comp _).symm
  have h2 : (∑ i, ∑ T ∈ sets2 Y, ∏ j ∈ T, D i j * PaleyGauss.chiR p (y j - x i)) =
      ∑ i, ∑ T ∈ sets2 X, ∏ j ∈ T,
        D (e i) (e j) * PaleyGauss.chiR p (y (e j) - x (e i)) := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun i _ => sum_sets2_product e _
  have h3 : (∑ j, ∑ S ∈ sets2 Y, ∏ i ∈ S, D i j * PaleyGauss.chiR p (y j - x i)) =
      ∑ j, ∑ S ∈ sets2 X, ∏ i ∈ S,
        D (e i) (e j) * PaleyGauss.chiR p (y (e j) - x (e i)) := by
    rw [← e.sum_comp]
    exact sum_congr rfl fun j _ => sum_sets2_product e _
  unfold starKernel
  rw [h1, h2, h3]
  rfl

end Sarkozy.JointRows.StarOps

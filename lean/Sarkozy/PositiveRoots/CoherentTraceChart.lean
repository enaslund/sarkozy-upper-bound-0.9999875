module

public import Sarkozy.PartV.CoherentChamberOperator
public import Sarkozy.PositiveRoots.CoherentMatrixModel
public import Sarkozy.SpectralD.StarPairFactorization

/-! Exact trace-pair coordinates for the physical chamber score. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators

def chamberSupport (side : Bool) (S : Support) : Finset (Fin 6) :=
  univ.filter fun i => chamberVertices side i ∈ S

theorem chamber_vertex_injective (side : Bool) : Function.Injective (chamberVertices side) := by
  cases side <;> decide +kernel

theorem chamber_vertex_disjoint : ∀ i j, chamberVertices true i ≠ chamberVertices false j := by
  decide +kernel

theorem chamber_support_partition (S : Support) :
    S = (chamberSupport true S).image (chamberVertices true) ∪
      (chamberSupport false S).image (chamberVertices false) := by
  ext v
  constructor
  · intro hv
    rcases chamberVertices_cover v with ⟨i, rfl⟩ | ⟨i, rfl⟩
    · exact mem_union_left _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hv⟩))
    · exact mem_union_right _ (mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hv⟩))
  · intro hv
    rcases mem_union.mp hv with hv | hv <;> obtain ⟨i, hi, rfl⟩ := mem_image.mp hv
    all_goals exact (mem_filter.mp hi).2

theorem chamber_support_disjoint (S : Support) :
    Disjoint ((chamberSupport true S).image (chamberVertices true))
      ((chamberSupport false S).image (chamberVertices false)) := by
  apply disjoint_left.mpr
  intro v hv hw
  obtain ⟨i, _, hi⟩ := mem_image.mp hv
  obtain ⟨j, _, hj⟩ := mem_image.mp hw
  exact chamber_vertex_disjoint i j (hi.trans hj.symm)

theorem chamber_support_sizes : ∀ sc ∈ dictionary39,
    3 ≤ (chamberSupport true sc.1).card ∧ 3 ≤ (chamberSupport false sc.1).card := by
  decide +kernel

def chamberCodeIndex (side : Bool) (S : Support) : Fin 64 :=
  if side then ⟨CoherentMatrix.leftCode S % 64, Nat.mod_lt _ (by decide)⟩
  else ⟨CoherentMatrix.rightCode S % 64, Nat.mod_lt _ (by decide)⟩

theorem chamber_codes : ∀ sc ∈ dictionary39,
    CoherentMatrix.leftCode sc.1 < 64 ∧ CoherentMatrix.rightCode sc.1 < 64 ∧
      CoherentMatrix.support (chamberCodeIndex true sc.1) = chamberSupport true sc.1 ∧
      CoherentMatrix.support (chamberCodeIndex false sc.1) = chamberSupport false sc.1 := by
  decide +kernel

variable {p : ℕ} [Fact p.Prime]

theorem trace_in_chamber (S : Support) (x y : Fin 6 → ZMod p) :
    trace S (chamberConfiguration x y) =
      ∑ z, StarMatrix.psi (chamberSupport true S) z x *
        StarMatrix.psi (chamberSupport false S) z y := by
  unfold trace
  apply sum_congr rfl
  intro z _
  conv_lhs => rw [chamber_support_partition S]
  rw [prod_union (chamber_support_disjoint S),
    prod_image (chamber_vertex_injective true).injOn,
    prod_image (chamber_vertex_injective false).injOn]
  simp only [chamberConfiguration, join_chamber_left, join_chamber_right]
  rfl

theorem tracePair_chamber (S : Support) (x y : Fin 6 → ZMod p) :
    trace S (chamberConfiguration x y) / p =
      StarMatrix.tracePair (chamberSupport true S) (chamberSupport false S) x y := by
  rw [trace_in_chamber]
  unfold StarMatrix.tracePair
  ring

/-- The original physical score, exactly as a sum of scaled star-pair kernels. -/
theorem score_chamber (x y : Fin 6 → ZMod p) :
    coherentScore p dictionary39 (chamberConfiguration x y) =
      (dictionary39.map fun sc => (sc.2 : ℝ) * (rp p)⁻¹ *
        StarMatrix.tracePair (chamberSupport true sc.1) (chamberSupport false sc.1) x y).sum := by
  change Real.sqrt p * (dictionary39.map fun sc => (sc.2 : ℝ) *
    (trace sc.1 (chamberConfiguration x y) / p)).sum = _
  simp_rw [tracePair_chamber]
  rw [← List.sum_map_mul_left]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc _
  unfold rp
  rw [inv_inv]
  ring

end Sarkozy.PositiveRoots.CoherentFrame

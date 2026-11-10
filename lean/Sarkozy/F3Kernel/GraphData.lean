module

public import Sarkozy.F3Kernel.Split
public import Sarkozy.F3Kernel.FixedPoint
public import Sarkozy.SpectralD.RootCuts

/-!
# The certificate graphs are the paper's LL20 and LL22 cuts

The refiner permutes the 36 vertices before producing its certificates. The explicit
equivalences below account for that permutation. Both layouts of the cross-edge masks and
the entire packed adjacency vectors agree with the actual root cuts. The integer square-root
constant also bounds `sqrt 2` after fixed-point decoding.

All finite comparisons are kernel reductions; no external graph generator is trusted.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset

namespace GraphData

open Sarkozy.SpectralD.Root

/-- The refiner's order, expressed as slot codes in the chamber half. -/
def codes20 : List ℕ :=
  [4, 0, 1, 8, 5, 10, 11, 9, 19, 15, 12, 14, 7, 13, 2, 22, 3, 32,
    18, 6, 27, 21, 25, 33, 26, 16, 28, 23, 29, 17, 35, 30, 34, 20, 24, 31]

/-- The refiner's order, expressed as half-slot codes in the layer half. -/
def codes22 : List ℕ :=
  [35, 1, 3, 18, 27, 7, 26, 31, 14, 17, 21, 15, 30, 28, 4, 25, 6, 11,
    19, 34, 8, 5, 23, 13, 16, 0, 2, 10, 29, 33, 20, 12, 32, 22, 24, 9]

def slot20 (i : Fin 36) : Slot := slotOfCode (codes20.getD i 0)
def slot22 (i : Fin 36) : Slot := slotOfCode (2 * codes22.getD i 0)

theorem slot20_mem : ∀ i, slot20 i ∈ SpectralD.Root.LL20.cut.half := by decide +kernel
theorem slot22_mem : ∀ i, slot22 i ∈ SpectralD.Root.LL22.cut.half := by decide +kernel

def half20 (i : Fin 36) : SpectralD.Root.LL20.cut.Half := ⟨slot20 i, slot20_mem i⟩
def half22 (i : Fin 36) : SpectralD.Root.LL22.cut.Half := ⟨slot22 i, slot22_mem i⟩

theorem half20_bijective : Function.Bijective half20 := by decide +kernel
theorem half22_bijective : Function.Bijective half22 := by decide +kernel

/-- The certificate's vertex labels are all and only the chamber-half vertices. -/
noncomputable def equiv20 : Fin 36 ≃ SpectralD.Root.LL20.cut.Half :=
  Equiv.ofBijective half20 half20_bijective

/-- The certificate's vertex labels are all and only the layer-half vertices. -/
noncomputable def equiv22 : Fin 36 ≃ SpectralD.Root.LL22.cut.Half :=
  Equiv.ofBijective half22 half22_bijective

theorem cross20_bool : ∀ i j : Fin 36,
    bit F3Kernel.LL20.EM (64 * i.val + j.val) =
      decide (sgnB SpectralD.Root.LL20.cut.flip (slot20 i) (slot20 j) ≠ 0) := by
  decide +kernel

theorem cross22_bool : ∀ i j : Fin 36,
    bit F3Kernel.LL22.EM (64 * i.val + j.val) =
      decide (sgnB SpectralD.Root.LL22.cut.flip (slot22 i) (slot22 j) ≠ 0) := by
  decide +kernel

theorem layouts20 : ∀ i j : Fin 36,
    bit F3Kernel.LL20.ET (64 * j.val + i.val) = bit F3Kernel.LL20.EM (64 * i.val + j.val) := by
  decide +kernel

theorem layouts22 : ∀ i j : Fin 36,
    bit F3Kernel.LL22.ET (64 * j.val + i.val) = bit F3Kernel.LL22.EM (64 * i.val + j.val) := by
  decide +kernel

/-- The decoded cross pairs in the `T` layout are exactly those of LL20. -/
theorem mem_cross20 (i j : Fin 36) :
    (i, j) ∈ decT F3Kernel.LL20.ET ↔
      (equiv20 i, equiv20 j) ∈ SpectralD.Root.LL20.crossPairs := by
  simp only [decT, mem_filter, mem_univ, true_and, Cuts.SpecData.crossPairs]
  rw [← bit_eq_testBit, layouts20, cross20_bool, decide_eq_true_eq,
    sgn_eq SpectralD.Root.LL20 LL20_G]
  rfl

/-- The decoded cross pairs in the `T` layout are exactly those of LL22. -/
theorem mem_cross22 (i j : Fin 36) :
    (i, j) ∈ decT F3Kernel.LL22.ET ↔
      (equiv22 i, equiv22 j) ∈ SpectralD.Root.LL22.crossPairs := by
  simp only [decT, mem_filter, mem_univ, true_and, Cuts.SpecData.crossPairs]
  rw [← bit_eq_testBit, layouts22, cross22_bool, decide_eq_true_eq,
    sgn_eq SpectralD.Root.LL22 LL22_G]
  rfl

/-- Every lane of the packed adjacency vector, including its unused bits, is correct. -/
theorem adj20_bool : ∀ u : Fin 36,
    adj64 F3Kernel.LL20 u = ∑ w : Fin 36,
      if edgeB (slot20 u) (slot20 w) || edgeB (slot20 w) (slot20 u)
      then 2 ^ (64 * w.val) else 0 := by
  decide +kernel

theorem adj22_bool : ∀ u : Fin 36,
    adj64 F3Kernel.LL22 u = ∑ w : Fin 36,
      if edgeB (slot22 u) (slot22 w) || edgeB (slot22 w) (slot22 u)
      then 2 ^ (64 * w.val) else 0 := by
  decide +kernel

theorem adj20 (u : Fin 36) :
    adj64 F3Kernel.LL20 u = ∑ w : Fin 36,
      if SpectralD.Root.LL20.Adj (equiv20 u).val (equiv20 w).val
      then 2 ^ (64 * w.val) else 0 := by
  rw [adj20_bool]
  apply sum_congr rfl
  intro w _
  simp only [Cuts.SpecData.Adj, mem_E SpectralD.Root.LL20 LL20_G, Bool.or_eq_true]
  rfl

theorem adj22 (u : Fin 36) :
    adj64 F3Kernel.LL22 u = ∑ w : Fin 36,
      if SpectralD.Root.LL22.Adj (equiv22 u).val (equiv22 w).val
      then 2 ^ (64 * w.val) else 0 := by
  rw [adj22_bool]
  apply sum_congr rfl
  intro w _
  simp only [Cuts.SpecData.Adj, mem_E SpectralD.Root.LL22 LL22_G, Bool.or_eq_true]
  rfl

end GraphData

theorem LL20_sqrtTwo : Real.sqrt 2 ≤ value64 LL20.SQ2 := by
  apply sqrt_le_value64
  norm_num [LL20]

theorem LL22_sqrtTwo : Real.sqrt 2 ≤ value64 LL22.SQ2 := by
  apply sqrt_le_value64
  norm_num [LL22]

end Sarkozy.F3Kernel

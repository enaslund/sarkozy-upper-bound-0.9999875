module

public import Sarkozy.F3Kernel.WeightBounds

/-!
# Certified finite weight sums of LL20 and LL22
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

namespace GraphData

def internal20 (i j : Fin 36) : Bool :=
  SpectralD.Root.edgeB (slot20 i) (slot20 j) || SpectralD.Root.edgeB (slot20 j) (slot20 i)

def internal22 (i j : Fin 36) : Bool :=
  SpectralD.Root.edgeB (slot22 i) (slot22 j) || SpectralD.Root.edgeB (slot22 j) (slot22 i)

def cross20 (i j : Fin 36) : Bool := bit LL20.EM (64 * i.val + j.val)
def cross22 (i j : Fin 36) : Bool := bit LL22.EM (64 * i.val + j.val)

theorem internal20_eq (i j : Fin 36) : internal20 i j = true ↔ graphAdj graph20 i j := by
  rw [graph20_adj]
  simp only [internal20, Cuts.SpecData.Adj,
    SpectralD.Root.mem_E _ SpectralD.Root.LL20_G, Bool.or_eq_true]
  rfl

theorem internal22_eq (i j : Fin 36) : internal22 i j = true ↔ graphAdj graph22 i j := by
  rw [graph22_adj]
  simp only [internal22, Cuts.SpecData.Adj,
    SpectralD.Root.mem_E _ SpectralD.Root.LL22_G, Bool.or_eq_true]
  rfl

theorem cross20_eq (i j : Fin 36) : cross20 i j = true ↔ sign20 i j ≠ 0 := by
  rw [cross20, cross20_bool, decide_eq_true_eq, sign20,
    SpectralD.Root.sgn_eq _ SpectralD.Root.LL20_G]
  rfl

theorem cross22_eq (i j : Fin 36) : cross22 i j = true ↔ sign22 i j ≠ 0 := by
  rw [cross22, cross22_bool, decide_eq_true_eq, sign22,
    SpectralD.Root.sgn_eq _ SpectralD.Root.LL22_G]
  rfl

set_option maxRecDepth 100000 in
theorem weightM20_sum : ∀ i, ∑ j, finiteM internal20 cross20 i j ≤ 810 := by decide +kernel

set_option maxRecDepth 100000 in
theorem weightM22_sum : ∀ i, ∑ j, finiteM internal22 cross22 i j ≤ 1528 := by decide +kernel

set_option maxRecDepth 100000 in
theorem weightRho20_sum : ∀ i, ∑ j, finiteRho internal20 cross20 i j ≤ 134112 := by decide +kernel

set_option maxRecDepth 100000 in
theorem weightRho22_sum : ∀ i, ∑ j, finiteRho internal22 cross22 i j ≤ 1117056 := by decide +kernel

theorem leafS_m20 (s : ℕ) : leafS graph20 sign20 (weightM graph20 sign20) s ≤ 810 :=
  leafS_m_le_finite graph20 sign20 internal20_eq cross20_eq weightM20_sum s

theorem leafS_m22 (s : ℕ) : leafS graph22 sign22 (weightM graph22 sign22) s ≤ 1528 :=
  leafS_m_le_finite graph22 sign22 internal22_eq cross22_eq weightM22_sum s

theorem leafS_rho20 (s : ℕ) : leafS graph20 sign20 (weightRho graph20 sign20) s ≤ 134112 :=
  leafS_rho_le_finite graph20 sign20 internal20_eq cross20_eq weightRho20_sum s

theorem leafS_rho22 (s : ℕ) : leafS graph22 sign22 (weightRho graph22 sign22) s ≤ 1117056 :=
  leafS_rho_le_finite graph22 sign22 internal22_eq cross22_eq weightRho22_sum s

theorem degree20_bound : ∀ i, #(univ.filter (fun j => internal20 i j = true)) ≤ 10 := by
  decide +kernel

theorem degree22_bound : ∀ i, #(univ.filter (fun j => internal22 i j = true)) ≤ 10 := by
  decide +kernel

theorem rowsDeg0_le_finite (H : OrientedGraph (Fin 36))
    {a : Fin 36 → Fin 36 → Bool} (ha : ∀ i j, a i j = true ↔ graphAdj H i j)
    {d : ℕ} (hd : ∀ i, #(univ.filter (fun j => a i j = true)) ≤ d) (i : Fin 36) :
    rowsDeg0 H i ≤ d := by
  simpa only [rowsDeg0, rowsAdj, ha, graphAdj, or_comm] using hd i

theorem degree20_sup : univ.sup (rowsDeg0 graph20) ≤ 10 :=
  Finset.sup_le fun i _ => rowsDeg0_le_finite graph20 internal20_eq degree20_bound i

theorem degree22_sup : univ.sup (rowsDeg0 graph22) ≤ 10 :=
  Finset.sup_le fun i _ => rowsDeg0_le_finite graph22 internal22_eq degree22_bound i

end GraphData

end Sarkozy.F3Kernel

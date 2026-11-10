module

public import Sarkozy.PositiveRoots.CoherentDiagonalRectangle

/-! A core/private singleton trace is exactly minus q on the accepting rectangle. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.L20Cap
open Sarkozy.PartV.CoherentDictionary

variable {p : ℕ} [Fact p.Prime]

theorem chamberTrace_singletons (hp2 : p ≠ 2) (S : Support) (i j : Fin 6)
    (hL : chamberSupport true S = {i}) (hR : chamberSupport false S = {j})
    (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    chamberTrace S x y =
      ((if emb x.1.val x.2.val i = emb y.1.val y.2.val j then (p : ℝ) else 0) - 1) / p := by
  unfold chamberTrace
  rw [trace_in_chamber, hL, hR]
  simp only [StarMatrix.psi, prod_singleton]
  rw [sum_chiRe_mul hp2]

theorem Rk_zero_core_private (hp3 : p % 4 = 3)
    (c : CoreT (ZMod p)) (b : PairT (ZMod p)) (i : Fin 4) (j : Fin 2)
    (h : c.val i = ![b.val.1, b.val.2] j) : Rk c b = 0 := by
  have hm1 := JointRows.PaleyGauss.chi_neg_one hp3
  fin_cases j
  · change c.val i = b.val.1 at h
    unfold Rk
    rw [← h, Kz_core hm1 c.property i, zero_mul]
  · change c.val i = b.val.2 at h
    unfold Rk
    rw [← h, Kz_core hm1 c.property i, mul_zero]

theorem chamberTrace_core_private (hp3 : p % 4 = 3) (S : Support) (i : Fin 4) (j : Fin 2)
    (hL : chamberSupport true S = {coreVertex i})
    (hR : chamberSupport false S = {privateVertex j})
    (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    Rk x.1 y.2 * Rk y.1 x.2 * chamberTrace S x y =
      -(p : ℝ)⁻¹ * (Rk x.1 y.2 * Rk y.1 x.2) := by
  rw [chamberTrace_singletons (by omega) S _ _ hL hR]
  have hx := emb_core x.1.val ![x.2.val.1, x.2.val.2] i
  have hy := emb_private y.1.val ![y.2.val.1, y.2.val.2] j
  change emb x.1.val x.2.val (coreVertex i) = x.1.val i at hx
  change emb y.1.val y.2.val (privateVertex j) = ![y.2.val.1, y.2.val.2] j at hy
  rw [hx, hy]
  by_cases he : x.1.val i = ![y.2.val.1, y.2.val.2] j
  · rw [Rk_zero_core_private hp3 x.1 y.2 i j he]
    ring
  · rw [ite_eq_right he]
    ring

theorem chamberTrace_private_core (hp3 : p % 4 = 3) (S : Support) (i : Fin 4) (j : Fin 2)
    (hL : chamberSupport true S = {privateVertex j})
    (hR : chamberSupport false S = {coreVertex i})
    (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    Rk x.1 y.2 * Rk y.1 x.2 * chamberTrace S x y =
      -(p : ℝ)⁻¹ * (Rk x.1 y.2 * Rk y.1 x.2) := by
  rw [chamberTrace_singletons (by omega) S _ _ hL hR]
  have hx := emb_private x.1.val ![x.2.val.1, x.2.val.2] j
  have hy := emb_core y.1.val ![y.2.val.1, y.2.val.2] i
  change emb x.1.val x.2.val (privateVertex j) = ![x.2.val.1, x.2.val.2] j at hx
  change emb y.1.val y.2.val (coreVertex i) = y.1.val i at hy
  rw [hx, hy]
  by_cases he : ![x.2.val.1, x.2.val.2] j = y.1.val i
  · rw [Rk_zero_core_private hp3 y.1 x.2 i j he.symm]
    ring
  · rw [ite_eq_right he]
    ring

end Sarkozy.PositiveRoots.CoherentFrame

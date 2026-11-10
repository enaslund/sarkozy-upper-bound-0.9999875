module

public import Sarkozy.PositiveRoots.CoherentProductGeometry
public import Sarkozy.PositiveRoots.CoherentRectangle
public import Sarkozy.PartV.CoherentDiagonalProduct

/-! Physical off-diagonal trace products in the fixed core/private rectangle. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def rawPairFeature {ι : Type*} (S T : Finset ι)
    (x : ι → ZMod p) (z : ZMod p × ZMod p) : ℝ :=
  StarMatrix.psi S z.1 x * StarMatrix.psi T z.2 x

theorem rawPairFeature_abs {ι : Type*} (S T : Finset ι)
    (x : ι → ZMod p) (z : ZMod p × ZMod p) : |rawPairFeature S T x z| ≤ 1 := by
  unfold rawPairFeature StarMatrix.psi
  rw [abs_mul]
  exact (mul_le_mul (abs_prod_chiRe_le S x z.1) (abs_prod_chiRe_le T x z.2)
    (abs_nonneg _) (by norm_num)).trans (by norm_num)

theorem offdiag_half_core (side : Bool) (S T : Support)
    (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) (z : ZMod p × ZMod p) :
    offdiagFeature (chamberSupport side S) (chamberSupport side T) (emb c (b 0, b 1)) z =
      offdiagFeature (coreSupport side S) (coreSupport side T) c z *
        rawPairFeature (privateSupport side S) (privateSupport side T) b z := by
  unfold offdiagFeature
  by_cases hz : z.1 = z.2
  · simp only [hz, ite_true, zero_mul]
  · rw [ite_eq_right hz, ite_eq_right hz]
    change StarMatrix.psi (chamberSupport side S) z.1 (emb c (b 0, b 1)) *
      StarMatrix.psi (chamberSupport side T) z.2 (emb c (b 0, b 1)) = _
    rw [psi_emb, psi_emb]
    unfold rawPairFeature coreSupport privateSupport StarMatrix.psi
    ring

theorem offdiag_half_private (side : Bool) (S T : Support)
    (c : Fin 4 → ZMod p) (b : Fin 2 → ZMod p) (z : ZMod p × ZMod p) :
    offdiagFeature (chamberSupport side S) (chamberSupport side T) (emb c (b 0, b 1)) z =
      offdiagFeature (privateSupport side S) (privateSupport side T) b z *
        rawPairFeature (coreSupport side S) (coreSupport side T) c z := by
  unfold offdiagFeature
  by_cases hz : z.1 = z.2
  · simp only [hz, ite_true, zero_mul]
  · rw [ite_eq_right hz, ite_eq_right hz]
    change StarMatrix.psi (chamberSupport side S) z.1 (emb c (b 0, b 1)) *
      StarMatrix.psi (chamberSupport side T) z.2 (emb c (b 0, b 1)) = _
    rw [psi_emb, psi_emb]
    unfold rawPairFeature coreSupport privateSupport StarMatrix.psi
    ring

noncomputable def chamberPairOffdiag (S T : Support)
    (x y : CoreT (ZMod p) × PairT (ZMod p)) : ℝ :=
  (p : ℝ) * ip ((fieldLaw p).product (fieldLaw p))
    (offdiagFeature (chamberSupport true S) (chamberSupport true T) (emb x.1.val x.2.val))
    (offdiagFeature (chamberSupport false S) (chamberSupport false T) (emb y.1.val y.2.val))

theorem chamberPairOffdiag_core (S T : Support) (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    chamberPairOffdiag S T x y = (p : ℝ) * ip ((fieldLaw p).product (fieldLaw p))
      (fun z => offdiagFeature (coreSupport true S) (coreSupport true T) x.1.val z *
        rawPairFeature (privateSupport true S) (privateSupport true T) ![x.2.val.1, x.2.val.2] z)
      (fun z => offdiagFeature (coreSupport false S) (coreSupport false T) y.1.val z *
        rawPairFeature (privateSupport false S) (privateSupport false T) ![y.2.val.1, y.2.val.2] z) := by
  unfold chamberPairOffdiag
  congr 2 <;> funext z
  · exact offdiag_half_core true S T x.1.val ![x.2.val.1, x.2.val.2] z
  · exact offdiag_half_core false S T y.1.val ![y.2.val.1, y.2.val.2] z

theorem chamberPairOffdiag_private (S T : Support) (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    chamberPairOffdiag S T x y = (p : ℝ) * ip ((fieldLaw p).product (fieldLaw p))
      (fun z => offdiagFeature (privateSupport true S) (privateSupport true T) ![x.2.val.1, x.2.val.2] z *
        rawPairFeature (coreSupport true S) (coreSupport true T) x.1.val z)
      (fun z => offdiagFeature (privateSupport false S) (privateSupport false T) ![y.2.val.1, y.2.val.2] z *
        rawPairFeature (coreSupport false S) (coreSupport false T) y.1.val z) := by
  unfold chamberPairOffdiag
  congr 2 <;> funext z
  · exact offdiag_half_private true S T x.1.val ![x.2.val.1, x.2.val.2] z
  · exact offdiag_half_private false S T y.1.val ![y.2.val.1, y.2.val.2] z

end Sarkozy.PositiveRoots.CoherentFrame

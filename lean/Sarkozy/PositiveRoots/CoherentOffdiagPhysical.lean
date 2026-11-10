module

public import Sarkozy.PositiveRoots.CoherentOffdiagBound
public import Sarkozy.PartV.CoherentSquareSplit

/-! The proved off-diagonal operator is exactly the off-diagonal part of the physical score square. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralC.TwoLabel Sarkozy.SpectralD
open Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

theorem evaluation_in_chamber (S : Support) (x y : Fin 6 → ZMod p) (z : ZMod p) :
    evaluation S (chamberConfiguration x y) z =
      StarMatrix.psi (chamberSupport true S) z x *
        StarMatrix.psi (chamberSupport false S) z y := by
  unfold evaluation
  conv_lhs => rw [chamber_support_partition S]
  rw [prod_union (chamber_support_disjoint S),
    prod_image (chamber_vertex_injective true).injOn,
    prod_image (chamber_vertex_injective false).injOn]
  simp only [chamberConfiguration, join_chamber_left, join_chamber_right]
  rfl

theorem chamberPairOffdiag_physical (S T : Support)
    (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    chamberPairOffdiag S T x y = offdiagTraceProduct S T
      (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have he (u v : ZMod p) :
      offdiagFeature (chamberSupport true S) (chamberSupport true T) (emb x.1.val x.2.val) (u, v) *
        offdiagFeature (chamberSupport false S) (chamberSupport false T) (emb y.1.val y.2.val) (u, v) =
      if u = v then 0 else
        evaluation S (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) u *
          evaluation T (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) v := by
    rw [evaluation_in_chamber, evaluation_in_chamber]
    unfold offdiagFeature StarMatrix.psi
    dsimp only
    split_ifs <;> ring
  unfold chamberPairOffdiag Recentering.ip
  rw [FiniteLaw.expect_product]
  simp_rw [he]
  simp only [fieldLaw, FiniteLaw.expect_uniform, ZMod.card, ← sum_div]
  unfold offdiagTraceProduct
  field_simp

theorem coherent_square_physical (x y : CoreT (ZMod p) × PairT (ZMod p)) :
    coherentScore p dictionary39
        (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) ^ 2 =
      (∑ z, (dictionaryEval dictionary39 (fun S => evaluation S
        (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) z)) ^ 2) / p +
          coherentOffdiagKernel x y := by
  rw [score_square_split]
  unfold coherentOffdiagKernel
  simp_rw [chamberPairOffdiag_physical]

end Sarkozy.PositiveRoots.CoherentFrame

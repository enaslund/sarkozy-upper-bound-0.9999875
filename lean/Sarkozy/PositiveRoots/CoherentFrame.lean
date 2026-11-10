module

public import Sarkozy.PositiveRoots.CoherentFrameEntries

/-!
The paper's actual-feature frame bound `Γ = 1 + 434r`. The graph-law hypotheses are
discharged for every six-vertex graph of maximum degree two, including the chamber half.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.Labellings Sarkozy.SpectralC Sarkozy.SpectralD
open scoped BigOperators ComplexConjugate

local notation "𝒮₆" => StarMatrix.supports (Fin 6)

theorem offdiag_row (r : ℝ) (a : Feature) :
    (∑ b : Feature, if a = b then 0 else 7 * r) = 434 * r := by
  calc
    _ = ∑ b : Feature, (7 * r - if a = b then 7 * r else 0) := by
      apply sum_congr rfl
      intro b _
      split_ifs <;> ring
    _ = (63 : ℝ) * (7 * r) - 7 * r := by
      rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, feature_card]
      simp
    _ = _ := by ring

variable {p : ℕ} [Fact p.Prime]

theorem graph_synthesis (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (G : OrientedGraph (Fin 6))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2)
    (h : Feature → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ x, graphWeight G hne x * ‖∑ a, kerMap (featKer 𝒮₆ a) (h a) x‖ ^ 2 ≤
      (1 + 434 * rp p) * ∑ a, l2sq (h a) := by
  obtain ⟨h0, h1, hi, hj⟩ := graphWeight_hyps G hne
  exact synthesis_bound (graphWeight G hne) (featKer 𝒮₆) (fun _ _ => 7 * rp p)
    (fun _ _ => mul_nonneg (by norm_num) rp_nonneg) (fun _ _ => rfl)
    (fun a => (offdiag_row (rp p) a).le)
    (feat_diag (by omega) hp3 (graphWeight G hne) h0 h1 hi hj 𝒮₆
      (fun S hS => support_nonempty ⟨S, hS⟩))
    (graph_feature_entry hW hp hp3 G hne hdeg) h hh

theorem graph_analysis (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (G : OrientedGraph (Fin 6))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2) (g : (Fin 6 → ZMod p) → ℂ) :
    ∑ a, l2sq (StarMatrix.featAdj (graphWeight G hne) 𝒮₆ g a) ≤
      (1 + 434 * rp p) * ∑ x, graphWeight G hne x * ‖g x‖ ^ 2 := by
  refine StarMatrix.sum_l2sq_adj_le (graphWeight G hne) (graphWeight_nonneg G hne)
    (StarMatrix.featKer 𝒮₆) (StarMatrix.featAdj (graphWeight G hne) 𝒮₆ g) g
    (by have := rp_nonneg (p := p); positivity)
    (StarMatrix.meanC_featAdj _ _ _) (StarMatrix.featKer_adjoint _ _ _) ?_
  intro h hh
  simp only [StarMatrix.featKer_eq_features]
  exact graph_synthesis hW hp hp3 G hne hdeg h hh

/-- Transfer any certified star-matrix norm bound to the actual graph law. -/
theorem graph_starPart_norm (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (G : OrientedGraph (Fin 6))
    (hne : (injLabellings (ZMod p) G).Nonempty)
    (hdeg : ∀ j, nbrCount G (univ.erase j) j ≤ 2)
    (d : Fin 6 → Fin 6 → ℝ) (L : Fin 6 → Finset (Fin 6) → ℝ)
    (R : Finset (Fin 6) → Fin 6 → ℝ) {lam : ℝ} (hlam : 0 ≤ lam)
    (hM : NormLe
      (StarMatrix.matI (StarMatrix.starM0 L R 𝒮₆) (StarMatrix.starM1 d 𝒮₆)) lam)
    (g f : (Fin 6 → ZMod p) → ℂ) :
    ‖StarMatrix.bil (graphWeight G hne) (StarMatrix.cent (graphWeight G hne) g)
      (StarMatrix.starPart d L R 𝒮₆) (StarMatrix.cent (graphWeight G hne) f)‖ ≤
      rp p * lam * (1 + 434 * rp p) *
        Real.sqrt (∑ x, graphWeight G hne x * ‖g x‖ ^ 2) *
        Real.sqrt (∑ x, graphWeight G hne x * ‖f x‖ ^ 2) := by
  obtain ⟨h0, h1, hi, _⟩ := graphWeight_hyps G hne
  refine StarMatrix.starPart_norm_le (by omega) hp3 (graphWeight G hne) h0 h1 hi
    d L R 𝒮₆ hlam (by have := rp_nonneg (p := p); positivity) hM ?_ g f
  intro h hh
  simp only [StarMatrix.featKer_eq_features]
  exact graph_synthesis hW hp hp3 G hne hdeg h hh

theorem chamber_synthesis (hW : WeilBound (ZMod p)) (hp : 4096 ≤ p)
    (hp3 : p % 4 = 3) (hne : (injLabellings (ZMod p) Sarkozy.L20Cap.G6).Nonempty)
    (h : Feature → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ x, graphWeight Sarkozy.L20Cap.G6 hne x *
      ‖∑ a, kerMap (featKer 𝒮₆ a) (h a) x‖ ^ 2 ≤
        (1 + 434 * rp p) * ∑ a, l2sq (h a) :=
  graph_synthesis hW hp hp3 _ hne g6_degree h hh

end Sarkozy.PositiveRoots.CoherentFrame

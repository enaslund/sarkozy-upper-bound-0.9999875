module

public import Sarkozy.MiddleCertificates.GraphFacts
public import Sarkozy.Cuts.CutMass
public import Sarkozy.MiddlePrimeInputs.EpsV

/-!
# The input `hL` of the `R₊` chain for the middle cuts

`paper/sections/14_spectral.tex`, `prop:spec2:mucentre`(c2): the lower one-step counts
`𝔩(t⁰_j) = max(0, (q - 𝔈_{t⁰_j} - 2^{t⁰_j} n)/2^{t⁰_j})` along the deletion order are positive.
For the middle cuts `t⁰_j ≤ Δ = 4` and `q = p ≥ 2²⁴`, `n ≤ 12`, so every factor is positive
(`hL_mid`), which is the input `hL` of `routeALower_midRplus` and `routeAUpper_midRplus`.

`hehat_mid`, `hehat1_mid`: X1's hypotheses on `ê` in `N_ns` (`cor:extraction-compressed`) with
the half-graph error `ê = e_{max d⁰}(p, |U⁺|)`, `max d⁰ = 1` (L10), `2` (L21).
-/

@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.MiddleCertificates

/-- The spectral data of the cut `c` with the deletion order replaced by `o`. Only the bounds of
the chain (`R_cut`, `R₊`, `t_i`, `t⁰_i`) see the order; the cut law and the cut operator do not
(`cutOp` of `withOrder c o` is `cutOp` of `c.data` by `rfl`). -/
@[reducible] noncomputable def withOrder (c : MidCut) (o : Fin c.data.cut.half.card ≃ c.data.cut.Half) :
    Cuts.SpecData c.Vertex :=
  { c.data with order := o }

/-- `t⁰_j ≤ 4`, for any deletion order: the later half-neighbours of `v_j` are `G`-neighbours. -/
theorem t0deg_le (c : MidCut) (o : Fin c.data.cut.half.card ≃ c.data.cut.Half)
    (j : Fin c.data.cut.half.card) : (withOrder c o).t0deg j ≤ 4 := by
  unfold Cuts.SpecData.t0deg
  refine le_trans (Finset.card_le_card_of_injOn (fun k => (withOrder c o).vtx k)
    (t := univ.filter (fun w => ((withOrder c o).vtx j, w) ∈ c.data.G.E ∨
      (w, (withOrder c o).vtx j) ∈ c.data.G.E))
    ?_ ?_) (mid_hdeg c _)
  · intro k hk
    simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hk ⊢
    exact hk.2
  · intro a _ b _ h
    exact (withOrder c o).vtx_inj h

/-- `𝔩(t) > 0` for `q ≥ 2²⁴`, `n ≤ 12`, `t ≤ 4`. -/
theorem stepLower_pos {q : ℝ} (hq : 2 ^ 24 ≤ q) {nn t : ℕ} (hnn : nn ≤ 12) (ht : t ≤ 4) :
    0 < Labellings.stepLower q nn t := by
  unfold Labellings.stepLower Labellings.softError
  have hs : (4096 : ℝ) ≤ Real.sqrt q := by
    rw [show (4096 : ℝ) = Real.sqrt (2 ^ 24) by
      rw [show (2 : ℝ) ^ 24 = 4096 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hq
  have hss : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by linarith)
  have hnn' : (nn : ℝ) ≤ 12 := by exact_mod_cast hnn
  apply lt_max_of_lt_right
  apply div_pos _ (by positivity)
  interval_cases t <;> norm_num [Labellings.gradedA, Labellings.gradedB] <;> nlinarith

/-- **`hL` for the middle cuts**, for any deletion order: `∏_j 𝔩(t⁰_j) > 0` at every
`p ≥ 2²⁴` and `n ≤ 12`. -/
theorem hL_mid (c : MidCut) (o : Fin c.data.cut.half.card ≃ c.data.cut.Half) {p : ℕ}
    [Fact p.Prime] (hp : 2 ^ 24 ≤ p) {nn : ℕ} (hnn : nn ≤ 12) :
    0 < ∏ j, Labellings.stepLower (Fintype.card (ZMod p)) nn ((withOrder c o).t0deg j) := by
  have hq : (2 : ℝ) ^ 24 ≤ (Fintype.card (ZMod p) : ℝ) := by
    rw [ZMod.card]
    exact_mod_cast hp
  exact Finset.prod_pos fun j _ => stepLower_pos hq hnn (t0deg_le c o j)

/-- The largest half-graph degree `max d⁰`: `1` (L10), `2` (L21). -/
def vD0 : MidCut → ℕ
  | .l10 => 1
  | .l21 => 2

theorem rowsDeg0_le (c : MidCut) (i : c.data.cut.Half) :
    Extraction.rowsDeg0 c.data.halfGraph i ≤ vD0 c := by
  unfold Extraction.rowsDeg0 Extraction.rowsAdj
  have h : (univ.filter fun j => (j, i) ∈ c.data.halfGraph.E ∨ (i, j) ∈ c.data.halfGraph.E) =
      univ.filter fun j => hAdj c j i = true := by
    refine Finset.filter_congr fun j _ => ?_
    exact hAdj_iff c j i
  rw [h]
  revert i
  cases c <;> decide

/-- **X1's hypothesis `hehat` with the half-graph error** `ê = e_{max d⁰}(p, |U⁺|)` (the
evaluator's `ehalf` in `raw_bound`). -/
theorem hehat_mid (c : MidCut) {p : ℕ} [Fact p.Prime] (i : c.data.cut.Half) :
    Extraction.coarseError (Extraction.rowsDeg0 c.data.halfGraph i) (Fintype.card (ZMod p) : ℕ)
      (Fintype.card c.data.cut.Half : ℕ) ≤ TraceMixing.coarseErr p (vD0 c) (vN c) := by
  have hqp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hce : ∀ t m : ℕ, Extraction.coarseError t (Fintype.card (ZMod p) : ℕ) (m : ℝ) =
      TraceMixing.coarseErr p t m := by
    intro t m
    rw [ZMod.card]
    unfold Extraction.coarseError Extraction.coarseH TraceMixing.coarseErr
    simp only [inv_pow, Real.sq_sqrt hqp.le, one_div]
    ring
  rw [hce, card_half]
  exact TraceMixing.coarseErr_mono hqp (rowsDeg0_le c i) le_rfl

/-- `ê = e_{max d⁰}(p, |U⁺|) < 1` for `p ≥ 2²⁴`. -/
theorem hehat1_mid (c : MidCut) {p : ℕ} (hp : 2 ^ 24 ≤ p) :
    TraceMixing.coarseErr p (vD0 c) (vN c) < 1 := by
  have hp' : (2 : ℝ) ^ 24 ≤ (p : ℝ) := by exact_mod_cast hp
  have h := SpectralD.Root.coarseErr_antitone (q := (2 : ℝ) ^ 24) (by norm_num) hp' (vD0 c) (vN c)
  refine lt_of_le_of_lt h ?_
  have hs : Real.sqrt ((2 : ℝ) ^ 24) = 2 ^ 12 := by
    rw [show (2 : ℝ) ^ 24 = (2 ^ 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold TraceMixing.coarseErr
  rw [hs]
  cases c <;> norm_num [vD0, vN]

end Sarkozy.MiddlePrimeInputs

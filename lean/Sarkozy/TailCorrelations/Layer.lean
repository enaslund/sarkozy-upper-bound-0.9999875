module

public import Sarkozy.InfluenceGlue.Weil
public import Sarkozy.F7Repair.Counts

@[expose] public section






open scoped BigOperators

namespace Sarkozy.TailCorrelations

open Sarkozy Sarkozy.Peyre Sarkozy.Influence Sarkozy.InfluenceGlue

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- A vertex has fewer neighbours than there are vertices. -/
theorem deg_lt_card (G : OrientedGraph U) (i : U) : G.deg i < Fintype.card U := by
  classical
  unfold OrientedGraph.deg
  calc (Finset.univ.filter (fun v => G.Adj i v)).card ≤ (Finset.univ.erase i).card := by
        apply Finset.card_le_card
        intro v hv
        rw [Finset.mem_filter] at hv
        rw [Finset.mem_erase]
        refine ⟨fun h => ?_, Finset.mem_univ _⟩
        subst h
        exact G.not_adj_self _ hv.2
    _ < Fintype.card U := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
        exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨i⟩) one_pos

/-- The largest free degree is at most `n - 1`. -/
theorem maxDeg_le (G : OrientedGraph U) (F : Finset U) : maxDeg G F ≤ Fintype.card U - 1 :=
  Finset.sup_le fun i _ => Nat.le_sub_one_of_lt (deg_lt_card G i)

/-- `p^{-1/2} ≤ 2⁻²⁵⁶` at `p ≥ 2⁵¹²`. -/
theorem rp_le {p : ℕ} (hp : (2 : ℝ) ^ 512 ≤ p) : rp p ≤ 1 / 2 ^ 256 := by
  unfold rp
  exact one_div_le_one_div_of_le (by positivity) (F7Repair.sqrt_ge_of_large hp)

/-- **The graded count errors at a large prime**: for `t ≤ 72` and `m ≤ 144`,
`(𝔄_t √p + 𝔅_t + 2^t m)/p ≤ 2⁸¹ p^{-1/2}` (`eq:graphs:graded`). -/
theorem graded_le {p : ℕ} (hp : (2 : ℝ) ^ 512 ≤ p) {t m : ℕ} (ht : t ≤ 72) (hm : m ≤ 144) :
    (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t + 2 ^ t * (m : ℝ)) / p ≤
      2 ^ 81 * rp p := by
  have hs := F7Repair.sqrt_ge_of_large hp
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  have hss : √(p : ℝ) * √(p : ℝ) = p := Real.mul_self_sqrt hp0.le
  set s := √(p : ℝ) with hs_def
  have hs1 : (1 : ℝ) ≤ s := le_trans (one_le_pow₀ (by norm_num)) hs
  have hA := F7Repair.gradedA_le ht
  have hB := F7Repair.gradedB_le ht
  have h2t : (2 : ℝ) ^ t ≤ 2 ^ 72 := pow_le_pow_right₀ (by norm_num) ht
  have hm' : (m : ℝ) ≤ 144 := by exact_mod_cast hm
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have h1 : Labellings.gradedA t * s ≤ 2 ^ 80 * s :=
    mul_le_mul_of_nonneg_right hA (by linarith)
  have h3 : (2 : ℝ) ^ t * (m : ℝ) ≤ 2 ^ 72 * 144 :=
    mul_le_mul h2t hm' hm0 (by positivity)
  have hnum : Labellings.gradedA t * s + Labellings.gradedB t + 2 ^ t * (m : ℝ) ≤ 2 ^ 81 * s := by
    have : (2 : ℝ) ^ 72 + 2 ^ 72 * 144 ≤ 2 ^ 80 * s := by
      have e : (2 : ℝ) ^ 72 + 2 ^ 72 * 144 ≤ 2 ^ 80 := by norm_num
      nlinarith
    nlinarith
  rw [div_le_iff₀ hp0]
  have e : 2 ^ 81 * rp p * p = 2 ^ 81 * s := by
    unfold rp
    rw [← hs_def, ← hss]
    have : s ≠ 0 := by positivity
    field_simp
  rw [e]
  exact hnum

/-- `H_w ≤ 2` for `0 ≤ w ≤ 1/5`. -/
theorem Hw_le_two {w : ℝ} (h0 : 0 ≤ w) (h1 : w ≤ 1 / 5) : Hw w ≤ 2 := by
  unfold Hw
  have h : 0 < (1 - w) ^ 2 := by
    have : 0 < 1 - w := by linarith
    positivity
  rw [div_le_iff₀ h]
  nlinarith

/-- **A uniform bound for the influence entries** on a graph with at most `72` vertices:
`ε_ij ≤ 2⁷³ r` when `0 ≤ w ≤ 1/5` and `r ≤ 1` (`eq:mid:epsij`). -/
theorem influence_le_crude (G : OrientedGraph U) (hU : Fintype.card U ≤ 72) (p : ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 5) (hr : rp p ≤ 1) (i j : U) :
    influence G p w i j ≤ 2 ^ 73 * rp p := by
  have h := influence_le G p (by linarith : (-1 : ℝ) ≤ w) i j
  have hH := Hw_le_two hw0 hw1
  have hH0 := Hw_nonneg (by linarith : (-1 : ℝ) ≤ w)
  have hr0 := rp_nonneg p
  have hdi := deg_lt_card G i
  have hdj := deg_lt_card G j
  have h2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hpow : √2 ^ (G.deg i + G.deg j) ≤ 2 ^ 71 := by
    have e : (√2 : ℝ) ^ 142 = 2 ^ 71 := by
      rw [show (142 : ℕ) = 2 * 71 from rfl, pow_mul, Real.sq_sqrt (by norm_num)]
    rw [← e]
    exact pow_le_pow_right₀ h2 (by omega)
  have hrr : rp p + rp p ^ 2 ≤ 2 * rp p := by
    have : rp p ^ 2 ≤ rp p := by
      rw [sq]
      exact mul_le_of_le_one_left hr0 hr
    linarith
  calc influence G p w i j ≤ Hw w * √2 ^ (G.deg i + G.deg j) * (rp p + rp p ^ 2) := h
    _ ≤ 2 * 2 ^ 71 * (2 * rp p) := by
        apply mul_le_mul (mul_le_mul hH hpow (by positivity) (by norm_num)) hrr
          (add_nonneg hr0 (sq_nonneg _)) (by positivity)
    _ = 2 ^ 73 * rp p := by ring

/-- **Row sums of the influence matrix**: `∑_{j ∈ F} ε_ij ≤ 2⁸⁰ r`. -/
theorem influence_row_le (G : OrientedGraph U) (hU : Fintype.card U ≤ 72) (p : ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 5) (hr : rp p ≤ 1) (F : Finset U) (i : U) :
    ∑ j ∈ F, influence G p w i j ≤ 2 ^ 80 * rp p := by
  have h := Finset.sum_le_card_nsmul F (fun j => influence G p w i j) (2 ^ 73 * rp p)
    (fun j _ => influence_le_crude G hU p hw0 hw1 hr i j)
  rw [nsmul_eq_mul] at h
  have hF : (F.card : ℝ) ≤ 72 := by
    have := Finset.card_le_univ F
    exact_mod_cast this.trans hU
  have hr0 := rp_nonneg p
  calc ∑ j ∈ F, influence G p w i j ≤ (F.card : ℝ) * (2 ^ 73 * rp p) := h
    _ ≤ 72 * (2 ^ 73 * rp p) := mul_le_mul_of_nonneg_right hF (by positivity)
    _ ≤ 2 ^ 80 * rp p := by nlinarith

/-- **The Schur test for the influence matrix**: `‖𝓔_{FF}‖ ≤ 2⁸⁰ r`. -/
theorem influence_opBound (G : OrientedGraph U) (hU : Fintype.card U ≤ 72) (p : ℕ) {w : ℝ}
    (hw0 : 0 ≤ w) (hw1 : w ≤ 1 / 5) (hr : rp p ≤ 1) (F : Finset U) :
    OpBound F F (influence G p w) (2 ^ 80 * rp p) := by
  have hρ : (0 : ℝ) ≤ 2 ^ 80 * rp p := mul_nonneg (by positivity) (rp_nonneg p)
  have h := opBound_schur (R := F) (C := F) (influence_nonneg G p (by linarith)) hρ hρ
    (fun i _ => influence_row_le G hU p hw0 hw1 hr F i)
    (fun j _ => by
      rw [Finset.sum_congr rfl (fun i _ => influence_symm G p w i j)]
      exact influence_row_le G hU p hw0 hw1 hr F j)
  rwa [Real.sqrt_mul_self hρ] at h

/-- `e + e²/(1 - e) ≤ 2⁸¹ r` for `e = 2⁸⁰ r`, `r ≤ 2⁻²⁵⁶`. -/
theorem schur_tail_le {r : ℝ} (hr0 : 0 ≤ r) (hr : r ≤ 1 / 2 ^ 256) :
    2 ^ 80 * r + (2 ^ 80 * r) ^ 2 / (1 - 2 ^ 80 * r) ≤ 2 ^ 81 * r := by
  have he : 2 ^ 80 * r ≤ 1 / 2 ^ 176 := by
    calc 2 ^ 80 * r ≤ 2 ^ 80 * (1 / 2 ^ 256) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = 1 / 2 ^ 176 := by norm_num
  have he0 : 0 ≤ 2 ^ 80 * r := mul_nonneg (by positivity) hr0
  have hd : (1 / 2 : ℝ) ≤ 1 - 2 ^ 80 * r := by
    have : (1 / 2 ^ 176 : ℝ) ≤ 1 / 2 := by norm_num
    linarith
  have hq : (2 ^ 80 * r) ^ 2 / (1 - 2 ^ 80 * r) ≤ 2 ^ 80 * r := by
    rw [div_le_iff₀ (by linarith)]
    have : (2 ^ 80 * r) * (2 ^ 80 * r) ≤ (2 ^ 80 * r) * (1 / 2) :=
      mul_le_mul_of_nonneg_left (by
        have : (1 / 2 ^ 176 : ℝ) ≤ 1 / 2 := by norm_num
        linarith) he0
    have h2 : (2 ^ 80 * r) * (1 / 2) ≤ (2 ^ 80 * r) * (1 - 2 ^ 80 * r) :=
      mul_le_mul_of_nonneg_left hd he0
    nlinarith
  linarith

theorem condLaw_pinEvent_empty {p : ℕ} [NeZero p] (μ : FiniteLaw (U → ZMod p)) (s : U → ZMod p)
    (h : 0 < prob μ (pinEvent (∅ : Finset U) s)) : condLaw μ (pinEvent (∅ : Finset U) s) h = μ := by
  have h1 : 0 < prob μ (fun _ : U → ZMod p => True) := by
    rw [← pinEvent_empty s]; exact h
  rw [cond_congr μ (pinEvent_empty s) h h1, condLaw_true]

theorem prob_pinEvent_empty_pos {p : ℕ} [NeZero p] (μ : FiniteLaw (U → ZMod p)) (s : U → ZMod p) :
    0 < prob μ (pinEvent (∅ : Finset U) s) := by
  rw [pinEvent_empty]
  unfold prob
  rw [show ind (fun _ : U → ZMod p => True) = fun _ => 1 from funext fun ω => ind_of_pos trivial,
    FiniteLaw.expect_const]
  exact one_pos

/-- **(F2) at a large prime, crude form**: for an odd prime `p ≥ 2⁵¹²` with Weil's bound, a graph
`G` on at most `72` vertices with `Inj_p(G) ≠ ∅` and disjoint vertex sets `X, Y`,
`ρ(y_X; y_Y) ≤ 2⁸¹ p^{-1/2}` under `λ_p(G)` (`it:record:upper-F2`, `cor:influence-schur`,
`prop:middle-negative`(b) with the empty pinning). -/
theorem graphLaw_maxCorr_le {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : Labellings.WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 512 ≤ p) (G : OrientedGraph U)
    (hU : Fintype.card U ≤ 72) (hInj : (injLabellings G p).Nonempty) (X Y : Finset U)
    (hXY : Disjoint X Y) :
    maxCorr (graphLaw G p hInj) (fun ω (v : X) => ω v) (fun ω (v : Y) => ω v) ≤
      2 ^ 81 * rp p := by
  have hr := rp_le hp
  have hr0 := rp_nonneg p
  have hr1 : rp p ≤ 1 := hr.trans (by norm_num)
  set w : ℝ := 2 ^ 81 * rp p with hw_def
  have hw0 : 0 ≤ w := mul_nonneg (by positivity) hr0
  have hw5 : w ≤ 1 / 5 := by
    calc w ≤ 2 ^ 81 * (1 / 2 ^ 256) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ ≤ 1 / 5 := by norm_num
  have hw1 : w < 1 := by linarith
  have hΔ := maxDeg_le G (free (∅ : Finset U))
  have hw : ∀ t ≤ maxDeg G (free (∅ : Finset U)), (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * (Fintype.card U : ℝ)) / p ≤ w :=
    fun t ht => graded_le hp (by omega) (by omega)
  have hwc : ∀ t ≤ maxDeg G (free (∅ : Finset U)) + 1, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * ((2 * Fintype.card U : ℕ) : ℝ)) / p ≤ w :=
    fun t ht => graded_le hp (by omega) (by omega)
  set e : ℝ := 2 ^ 80 * rp p with he_def
  have he0 : 0 ≤ e := mul_nonneg (by positivity) hr0
  have he1 : e < 1 := by
    calc e ≤ 2 ^ 80 * (1 / 2 ^ 256) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ < 1 := by norm_num
  have hE : OpBound (free (∅ : Finset U)) (free ∅) (influence G p w) e :=
    influence_opBound G hU p hw0 hw5 hr1 _
  obtain ⟨Q, hQ⟩ := exists_inverse (free (∅ : Finset U)) (influence G p w) he0 he1 hE
  set s : U → ZMod p := fun _ => 0 with hs
  have hprob := prob_pinEvent_empty_pos (graphLaw G p hInj) s
  have hsub : ∀ Z : Finset U, Z ⊆ free (∅ : Finset U) := fun Z v _ => by simp [free]
  have hb := middle_negative_b_weil hp2 hW G hInj ∅ s hw0 hw1 hw0 hw1 hw hwc he0 he1 hE Q hQ
    ∅ s ⟨Finset.Subset.refl _, fun v hv => absurd hv (Finset.notMem_empty v)⟩ hprob X Y
    (hsub X) (hsub Y) hXY he0 (hE.subset (hsub X) (hsub Y))
  rw [condLaw_pinEvent_empty] at hb
  exact (hb.trans (min_le_right _ _)).trans (schur_tail_le hr0 hr)

end Sarkozy.TailCorrelations

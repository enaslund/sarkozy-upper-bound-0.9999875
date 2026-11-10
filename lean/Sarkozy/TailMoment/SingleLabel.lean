module

public import Sarkozy.TailMoment.GraphUnit
public import Sarkozy.InfluenceGlue.SingleLabel

/-!
# The single-label bound from Weil's bound, and the tail hypothesis without it

`31_density_induction_upgrade.tex`, first paragraph of the proof of `lem:density:global-moment`,
with the single-label correlation bound now proved rather than assumed. The chain is:

* `Target.Weil` gives `WeilBound (ZMod p)` (`Sarkozy.Labellings.weilBound_of_target`);
* this gives the count errors (`Sarkozy.Influence.countErrors_of_weil`, `lem:mid:standing`);
* with them, `prop:middle-negative` (b) for the empty pinning is
  `Sarkozy.InfluenceGlue.single_label_maxCorr_le_rowSum_weil` (WP-A's glue over WP-P's pinned
  influence). It gives `ρ(y_v; y_{U ∖ v}) ≤ q/(1 - q)` once the influence row sums are `≤ q < 1`.

For a fixed graph, the count errors `w` and the influence row sums `q` are both `O(p^{-1/2})`
(`graded_le_div_sqrt`, `influence_le_two_pow`). This gives:

* `single_label_of_weil`: `ρ(y_v; y_{U ∖ v}) ≤ C/√p` for all primes `p ≥ p₁`, with explicit `C`
  and `p₁` depending only on the graph;
* `graphLaw_unit_mixed_L36_of_weil`: the `hunit` hypothesis of
  `Sarkozy.Comparison.paperMain_powerSavingBound` for `λ_p(G)`, from `Target.Weil` alone;
* `labellings_unit_mixed_L36_of_weil`: the same for the Labellings law `Labellings.graphLaw G'`;
* `tailFamily`, `tailFamily_unit`, `tailFamily_hasUniformMarginals`: a total family of laws
  (the graph law when `Inj_q(G) ≠ ∅`, the uniform law otherwise) with the types of `μp`,
  `hunit` and `hmp` in `paperMain_powerSavingBound`.

There are no graph conditions: any fixed oriented graph on a nonempty vertex type works.

Caveat: `tailFamily G` is the law of one fixed graph. The paper's tail law `μ_p`
(`def:tail-law`) is a normalized mixture of the upper-reference components `π_{t,j}`, with root
`π_{LL,2}`; for the root graph, `tailFamily G` is the root's law, not `μ_p`. So
`tailFamily_unit` does not discharge `hunit` for the paper's `μ_p`: that still needs the mixture
step and the Part V definitions.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.TailMoment

open Sarkozy Sarkozy.Peyre Sarkozy.Influence

variable {W : Type} [Fintype W] [DecidableEq W]

/-- The graded count errors are `O(p^{-1/2})`:
`(a_t √p + b_t + 2^t n)/p ≤ (a_t + b_t + 2^t n)/√p` for `p ≥ 1`. -/
theorem graded_le_div_sqrt (t n : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    (Labellings.gradedA t * √p + Labellings.gradedB t + 2 ^ t * (n : ℝ)) / p ≤
      (Labellings.gradedA t + Labellings.gradedB t + 2 ^ t * (n : ℝ)) / √p := by
  have hs1 : 1 ≤ √p := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hp
  have hs0 : 0 < √p := by linarith
  have hsq : √p * √p = p := Real.mul_self_sqrt (by linarith)
  have hle : √p ≤ p := by nlinarith
  have hA := Labellings.gradedA_nonneg t
  have hB := Labellings.gradedB_nonneg t
  have hN : 0 ≤ 2 ^ t * (n : ℝ) := by positivity
  rw [div_le_div_iff₀ (by linarith) hs0]
  have e1 : Labellings.gradedA t * √p * √p = Labellings.gradedA t * p := by
    rw [mul_assoc, hsq]
  nlinarith [mul_le_mul_of_nonneg_left hle hB, mul_le_mul_of_nonneg_left hle hN]

/-- Each influence entry is at most `H_w 2^Δ (r + r²)` when both degrees are at most `Δ`. -/
theorem influence_le_two_pow (G : OrientedGraph W) (p : ℕ) {w : ℝ} (hw : -1 ≤ w) (i j : W) :
    influence G p w i j ≤ Hw w * 2 ^ maxDeg G Finset.univ * (rp p + rp p ^ 2) := by
  have h := influence_le G p hw i j
  have h2 : (1 : ℝ) ≤ √2 := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hdi : G.deg i ≤ maxDeg G Finset.univ := Finset.le_sup (f := G.deg) (Finset.mem_univ i)
  have hdj : G.deg j ≤ maxDeg G Finset.univ := Finset.le_sup (f := G.deg) (Finset.mem_univ j)
  have hpow : √2 ^ (G.deg i + G.deg j) ≤ 2 ^ maxDeg G Finset.univ := by
    calc √2 ^ (G.deg i + G.deg j) ≤ √2 ^ (2 * maxDeg G Finset.univ) :=
          pow_le_pow_right₀ h2 (by omega)
      _ = 2 ^ maxDeg G Finset.univ := by
          rw [pow_mul, Real.sq_sqrt (by norm_num)]
  have hH := Hw_nonneg hw
  have hr : 0 ≤ rp p + rp p ^ 2 := add_nonneg (rp_nonneg p) (sq_nonneg _)
  calc influence G p w i j ≤ Hw w * √2 ^ (G.deg i + G.deg j) * (rp p + rp p ^ 2) := h
    _ ≤ Hw w * 2 ^ maxDeg G Finset.univ * (rp p + rp p ^ 2) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH) hr

/-- **The single-label correlation bound from Weil's bound.** For a fixed oriented graph `G'`,
`ρ(y_v; y_{W ∖ v}) ≤ C/√p` under `λ_p(G)` for every prime `p ≥ p₁`. The constants are
explicit: `C = 24 |W| 2^Δ` and `p₁ = ⌈(2K + 24 |W| 2^Δ)²⌉ + 3`, where
`K = ∑_{t ≤ Δ+1} (a_t + b_t + 2^{t+1}|W|)` and `Δ` is the maximum degree. -/
theorem single_label_of_weil (G' : Labellings.OrientedGraph W) (hW : Target.Weil) :
    ∃ C : ℝ, ∃ p₁ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₁ ≤ p →
      ∀ (hInj : (injLabellings (ofLabellings G') p).Nonempty) (v : W),
        maxCorr (graphLaw (ofLabellings G') p hInj) (fun z => z v)
          (fun z (u : {u // u ≠ v}) => z u) ≤ C / √(p : ℝ) := by
  set G := ofLabellings G'
  set n := Fintype.card W
  set Δ := maxDeg G Finset.univ
  set K : ℝ := ∑ t ∈ Finset.range (Δ + 2),
    (Labellings.gradedA t + Labellings.gradedB t + 2 ^ t * ((2 * n : ℕ) : ℝ)) with hK
  set C₀ : ℝ := 12 * n * 2 ^ Δ with hC₀
  have hK0 : 0 ≤ K := Finset.sum_nonneg (fun t _ => by
    have := Labellings.gradedA_nonneg t
    have := Labellings.gradedB_nonneg t
    positivity)
  have hC0 : 0 ≤ C₀ := by positivity
  refine ⟨2 * C₀, ⌈(2 * K + 2 * C₀) ^ 2⌉₊ + 3, fun p _ hp hInj v => ?_⟩
  have hp2 : p ≠ 2 := by omega
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
  have hs : 2 * K + 2 * C₀ ≤ √(p : ℝ) := by
    have h1 : (2 * K + 2 * C₀) ^ 2 ≤ (p : ℝ) := by
      have hc := Nat.le_ceil ((2 * K + 2 * C₀) ^ 2)
      have h2 : ((⌈(2 * K + 2 * C₀) ^ 2⌉₊ : ℕ) : ℝ) ≤ p := by
        exact_mod_cast (by omega : ⌈(2 * K + 2 * C₀) ^ 2⌉₊ ≤ p)
      linarith
    calc 2 * K + 2 * C₀ = √((2 * K + 2 * C₀) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ √(p : ℝ) := Real.sqrt_le_sqrt h1
  have hs0 : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hrp : rp p = (√(p : ℝ))⁻¹ := by unfold rp; rw [one_div]
  -- the count errors
  set w : ℝ := K / √(p : ℝ) with hw_def
  have hw0 : 0 ≤ w := div_nonneg hK0 hs0.le
  have hw_half : w ≤ 1 / 2 := by
    rw [hw_def, div_le_iff₀ hs0]
    linarith
  have hw1 : w < 1 := by linarith
  have hterm : ∀ t ∈ Finset.range (Δ + 2), ∀ m : ℕ, m ≤ 2 * n →
      (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t + 2 ^ t * (m : ℝ)) / p ≤ w := by
    intro t ht m hm
    refine (graded_le_div_sqrt t m hpR).trans ?_
    rw [hw_def]
    apply div_le_div_of_nonneg_right _ hs0.le
    have hmR : (m : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by exact_mod_cast hm
    have h2t : (0 : ℝ) ≤ 2 ^ t := by positivity
    calc Labellings.gradedA t + Labellings.gradedB t + 2 ^ t * (m : ℝ)
        ≤ Labellings.gradedA t + Labellings.gradedB t + 2 ^ t * ((2 * n : ℕ) : ℝ) := by
          nlinarith [mul_le_mul_of_nonneg_left hmR h2t]
      _ ≤ K := by
          rw [hK]
          exact Finset.single_le_sum (f := fun t => Labellings.gradedA t + Labellings.gradedB t +
            2 ^ t * ((2 * n : ℕ) : ℝ)) (fun t _ => by
              have := Labellings.gradedA_nonneg t
              have := Labellings.gradedB_nonneg t
              positivity) ht
  have hgw : ∀ t ≤ maxDeg G Finset.univ, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * (Fintype.card W : ℝ)) / p ≤ w := fun t ht =>
    hterm t (Finset.mem_range.mpr (by omega)) n (by omega)
  have hgwc : ∀ t ≤ maxDeg G Finset.univ + 1, (Labellings.gradedA t * √(p : ℝ) +
      Labellings.gradedB t + 2 ^ t * ((2 * Fintype.card W : ℕ) : ℝ)) / p ≤ w := fun t ht =>
    hterm t (Finset.mem_range.mpr (by omega)) (2 * n) le_rfl
  -- the influence row sums
  set q : ℝ := C₀ / √(p : ℝ) with hq_def
  have hq0 : 0 ≤ q := div_nonneg hC0 hs0.le
  have hq_half : q ≤ 1 / 2 := by
    rw [hq_def, div_le_iff₀ hs0]
    linarith
  have hq1 : q < 1 := by linarith
  have hr1 : rp p ≤ 1 := by
    rw [hrp]
    refine inv_le_one_of_one_le₀ ?_
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hpR
  have hHw : Hw w ≤ 6 := by
    have := Hw_mono hw0 hw_half (by norm_num)
    have e : Hw (1 / 2) = 6 := by unfold Hw; norm_num
    linarith
  have hrow : ∀ i, ∑ j, influence G p w i j ≤ q := by
    intro i
    have hentry : ∀ j, influence G p w i j ≤ 12 * 2 ^ Δ * rp p := by
      intro j
      refine (influence_le_two_pow G p (by linarith) i j).trans ?_
      have hr0 := rp_nonneg p
      have hsq : rp p ^ 2 ≤ rp p := by nlinarith
      have h2Δ : (0 : ℝ) ≤ 2 ^ Δ := by positivity
      calc Hw w * 2 ^ Δ * (rp p + rp p ^ 2) ≤ 6 * 2 ^ Δ * (rp p + rp p) := by
            apply mul_le_mul (mul_le_mul_of_nonneg_right hHw h2Δ) (by linarith)
              (by positivity) (by positivity)
        _ = 12 * 2 ^ Δ * rp p := by ring
    calc ∑ j, influence G p w i j ≤ ∑ _j : W, 12 * 2 ^ Δ * rp p :=
          Finset.sum_le_sum (fun j _ => hentry j)
      _ = q := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hq_def, hC₀, hrp, div_eq_mul_inv]
          ring
  have h := InfluenceGlue.single_label_maxCorr_le_rowSum_weil hp2
    (Labellings.weilBound_of_target hW p hp2)
    G hInj hw0 hw1 hw0 hw1 hgw hgwc hq0 hq1 hrow v
  refine h.trans ?_
  -- `q/(1 - q) ≤ 2q = 2C₀/√p`
  have h1q : 1 / 2 ≤ 1 - q := by linarith
  have : q / (1 - q) ≤ 2 * q := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  calc q / (1 - q) ≤ 2 * q := this
    _ = 2 * C₀ / √(p : ℝ) := by rw [hq_def]; ring

/-- **The tail hypothesis from Weil's bound alone** (`hunit` of
`Sarkozy.Comparison.paperMain_powerSavingBound`): for a fixed oriented graph `G'` on a nonempty
vertex type, `λ_q(G)` has unit mixed `L³⁶` for every prime `q` above a threshold. -/
theorem graphLaw_unit_mixed_L36_of_weil [Nonempty W] (G' : Labellings.OrientedGraph W)
    (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q →
      ∃ hInj : (injLabellings (ofLabellings G') q).Nonempty,
        MixedLpBound (graphLaw (ofLabellings G') q hInj) 36 1 := by
  obtain ⟨C, p₁, hcorr⟩ := single_label_of_weil G' hW
  exact graphLaw_unit_mixed_L36 G' hW hcorr

/-- The same tail statement for the Labellings law `Labellings.graphLaw G'` (equal to the law above
by `graphLaw_ofLabellings`), for every prime `q` above a threshold. -/
theorem labellings_unit_mixed_L36_of_weil [Nonempty W] (G' : Labellings.OrientedGraph W)
    (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      ∃ hne : (Labellings.injLabellings (ZMod q) G').Nonempty,
        MixedLpBound (Labellings.graphLaw G' hne) 36 1 := by
  obtain ⟨C, p₁, hcorr⟩ := single_label_of_weil G' hW
  exact graphLaw_eventually_unit G' hW hcorr (r := 36) (by norm_num)

/-- Unit mixed `Lʳ` for every `r > 1`, from Weil's bound alone. -/
theorem labellings_unit_mixed_of_weil [Nonempty W] (G' : Labellings.OrientedGraph W)
    (hW : Target.Weil) {r : ℝ} (hr : 1 < r) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [Fact q.Prime], p₀ ≤ q →
      ∃ hne : (Labellings.injLabellings (ZMod q) G').Nonempty,
        MixedLpBound (Labellings.graphLaw G' hne) r 1 := by
  obtain ⟨C, p₁, hcorr⟩ := single_label_of_weil G' hW
  exact graphLaw_eventually_unit G' hW hcorr hr

/-! ### A total family of laws for `paperMain_powerSavingBound` -/

/-- The uniform law on `V → X` has uniform marginals. -/
theorem uniform_hasUniformMarginals {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Nonempty X] : HasUniformMarginals (FiniteLaw.uniform (V → X)) := by
  intro v f
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  set R := ({j // j ≠ v} → X)
  have hsum : ∑ z : V → X, f (z v) = (Fintype.card R : ℝ) * ∑ a : X, f a := by
    rw [Fintype.sum_equiv (Equiv.piSplitAt v (fun _ => X)) (fun z => f (z v))
      (fun q => f q.1) (fun z => rfl), Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.mul_sum]
  have hcard : (Fintype.card (V → X) : ℝ) = Fintype.card X * Fintype.card R := by
    rw [Fintype.card_congr (Equiv.piSplitAt v (fun _ => X)), Fintype.card_prod]
    push_cast
    ring
  have hR : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  rw [hsum, hcard]
  field_simp

open Classical in
/-- The graph law `λ_q(G)` when `Inj_q(G)` is nonempty, and the uniform law otherwise. This is a
total family `∀ q [NeZero q], FiniteLaw (W → ZMod q)`, the type of `μp` in
`Sarkozy.Comparison.paperMain_powerSavingBound`. It is the law of a single graph, not the
paper's tail law `μ_p` (`def:tail-law`), which mixes the upper-reference components. -/
noncomputable def tailFamily (G' : Labellings.OrientedGraph W) (q : ℕ) [NeZero q] :
    FiniteLaw (W → ZMod q) :=
  if h : (injLabellings (ofLabellings G') q).Nonempty then graphLaw (ofLabellings G') q h
  else FiniteLaw.uniform (W → ZMod q)

theorem tailFamily_eq (G' : Labellings.OrientedGraph W) (q : ℕ) [NeZero q]
    (h : (injLabellings (ofLabellings G') q).Nonempty) :
    tailFamily G' q = graphLaw (ofLabellings G') q h := by
  unfold tailFamily
  rw [dite_eq_left h]

/-- **`hunit` for `μp = tailFamily G'`, from `Target.Weil` alone.** This is `hunit` for the law
of the single graph `G'`; it is not `hunit` for the paper's tail law `μ_p` (see the module
docstring). -/
theorem tailFamily_unit [Nonempty W] (G' : Labellings.OrientedGraph W) (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (tailFamily G' q) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := graphLaw_unit_mixed_L36_of_weil G' hW
  refine ⟨p₀, fun q _ hq hle => ?_⟩
  obtain ⟨hInj, hmix⟩ := hp₀ q hq hle
  rw [tailFamily_eq G' q hInj]
  exact hmix

/-- `hmp` for `μp = tailFamily G'`: every member has uniform marginals. -/
theorem tailFamily_hasUniformMarginals (G' : Labellings.OrientedGraph W) (q : ℕ) [NeZero q] :
    HasUniformMarginals (tailFamily G' q) := by
  unfold tailFamily
  split_ifs with h
  · exact graphLaw_hasUniformMarginals (ofLabellings G') h
  · exact uniform_hasUniformMarginals

end Sarkozy.TailMoment

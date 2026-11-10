module

public import Sarkozy.Influence.UnitConstant
public import Sarkozy.Influence.Marginals
public import Sarkozy.Influence.Bridge
public import Sarkozy.Labellings.GraphLaw
public import Sarkozy.Target
public import Sarkozy.Labellings.TargetBridge
public import Sarkozy.Moments.Mixed





@[expose] public section

open scoped BigOperators
open Filter

namespace Sarkozy.TailMoment

open Sarkozy Sarkozy.Peyre Sarkozy.Influence

variable {W : Type} [Fintype W] [DecidableEq W]

/-- **Unit mixed `Lʳ` norm of a fixed graph law, for large primes, for one exponent
`r ∈ (1, 2]`.** -/
theorem graphLaw_eventually_unit_le_two [Nonempty W] (G' : Labellings.OrientedGraph W)
    (hW : Target.Weil) {C : ℝ} {p₁ : ℕ}
    (hcorr : ∀ (p : ℕ) [Fact p.Prime], p₁ ≤ p →
      ∀ (hInj : (injLabellings (ofLabellings G') p).Nonempty) (v : W),
        maxCorr (graphLaw (ofLabellings G') p hInj) (fun z => z v)
          (fun z (u : {u // u ≠ v}) => z u) ≤ C / √(p : ℝ))
    {r : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) :
    ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      ∃ hne : (Labellings.injLabellings (ZMod p) G').Nonempty,
        MixedLpBound (Labellings.graphLaw G' hne) r 1 := by
  classical
  obtain ⟨D, hD0, q₀, hdens⟩ := Labellings.graphLaw_uniform_density G'
  set n := Fintype.card W
  set τ := centeredTolerance W r with hτ
  have hτ0 : 0 < τ := centeredTolerance_pos hr1
  -- a truncation scale `t ≥ 1` with `4^n D t^{1-r} ≤ τ/2`
  set M : ℝ := 4 ^ n * D with hM
  have hM0 : 0 ≤ M := by positivity
  have hlim : Tendsto (fun t : ℝ => M * t ^ (1 - r)) atTop (nhds 0) := by
    have h := (tendsto_rpow_neg_atTop (by linarith : 0 < r - 1)).const_mul M
    simpa only [neg_sub, mul_zero] using h
  obtain ⟨t₀, ht₀⟩ := eventually_atTop.mp
    (hlim.eventually (gt_mem_nhds (by linarith : (0 : ℝ) < τ / 2)))
  set t : ℝ := max 1 t₀ with ht_def
  have ht : 1 ≤ t := le_max_left _ _
  have hMt : M * t ^ (1 - r) < τ / 2 := ht₀ t (le_max_right _ _)
  -- the prime threshold
  set K : ℝ := max C 0 * √D * t ^ ((n : ℝ) * (1 - r / 2)) with hK
  have hK0 : 0 ≤ K := by positivity
  set p₀ : ℕ := ⌈(2 * K / τ) ^ 2⌉₊ + ⌈q₀⌉₊ + p₁ + 3 with hp₀
  refine ⟨p₀, fun p _ hp => ?_⟩
  have hpprime : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by omega
  have hp2 : p ≠ 2 := by omega
  have hpR : (3 : ℝ) ≤ p := by exact_mod_cast hp3
  have hWp := Labellings.weilBound_of_target hW p hp2
  have hq : q₀ ≤ Fintype.card (ZMod p) := by
    rw [ZMod.card]
    have h1 : q₀ ≤ (⌈q₀⌉₊ : ℝ) := Nat.le_ceil q₀
    have h2 : (⌈q₀⌉₊ : ℝ) ≤ p := by exact_mod_cast (by omega : ⌈q₀⌉₊ ≤ p)
    linarith
  obtain ⟨hne, hdensp⟩ := hdens (ZMod p) hWp hq
  refine ⟨hne, ?_⟩
  have hInj : (injLabellings (ofLabellings G') p).Nonempty := by
    rw [injLabellings_ofLabellings]
    exact hne
  rw [← graphLaw_ofLabellings G' hInj hne]
  set μ := graphLaw (ofLabellings G') p hInj with hμ
  have hm : HasUniformMarginals μ := graphLaw_hasUniformMarginals _ hInj
  have hdensμ : ∀ S : Finset W, ∀ g : W → ZMod p → ℝ,
      |slotForm μ S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform (ZMod p)).expect (fun x => |g v x|) := by
    intro S g
    have h := hdensp S g
    rw [← graphLaw_ofLabellings G' hInj hne] at h
    exact h
  -- the correlation constant `ρ = max (C/√p) 0`
  set ρ : ℝ := max (C / √(p : ℝ)) 0 with hρ
  have hρ0 : 0 ≤ ρ := le_max_right _ _
  have hcorrμ : ∀ v : W, maxCorr μ (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤ ρ :=
    fun v => (hcorr p (by omega) hInj v).trans (le_max_left _ _)
  have hsp : 0 < √(p : ℝ) := Real.sqrt_pos.mpr (by linarith)
  -- `ρ √D t^{n(1-r/2)} ≤ τ/2`
  have hρK : ρ * √D * t ^ ((n : ℝ) * (1 - r / 2)) ≤ K / √(p : ℝ) := by
    have h1 : ρ ≤ max C 0 / √(p : ℝ) := by
      rw [hρ]
      refine max_le ?_ (div_nonneg (le_max_right _ _) hsp.le)
      exact div_le_div_of_nonneg_right (le_max_left _ _) hsp.le
    have h2 : 0 ≤ √D * t ^ ((n : ℝ) * (1 - r / 2)) := by positivity
    calc ρ * √D * t ^ ((n : ℝ) * (1 - r / 2)) = ρ * (√D * t ^ ((n : ℝ) * (1 - r / 2))) := by
          ring
      _ ≤ max C 0 / √(p : ℝ) * (√D * t ^ ((n : ℝ) * (1 - r / 2))) :=
          mul_le_mul_of_nonneg_right h1 h2
      _ = K / √(p : ℝ) := by rw [hK]; ring
  have hKp : K / √(p : ℝ) ≤ τ / 2 := by
    rw [div_le_iff₀ hsp]
    have hceil : (2 * K / τ) ^ 2 ≤ (p : ℝ) := by
      have h1 : (2 * K / τ) ^ 2 ≤ (⌈(2 * K / τ) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h2 : (⌈(2 * K / τ) ^ 2⌉₊ : ℝ) ≤ p := by
        exact_mod_cast (by omega : ⌈(2 * K / τ) ^ 2⌉₊ ≤ p)
      linarith
    have hsq : 2 * K / τ ≤ √(p : ℝ) := by
      rw [← Real.sqrt_sq (by positivity : 0 ≤ 2 * K / τ)]
      exact Real.sqrt_le_sqrt hceil
    have : 2 * K ≤ τ * √(p : ℝ) := by
      rw [div_le_iff₀ hτ0] at hsq
      linarith
    linarith
  have hsmall : ρ * √D * t ^ ((n : ℝ) * (1 - r / 2)) + 4 ^ n * D * t ^ (1 - r) ≤
      centeredTolerance W r := by
    have : 4 ^ n * D * t ^ (1 - r) = M * t ^ (1 - r) := by rw [hM]
    rw [this]
    linarith
  exact mixedLpBound_of_density_and_maxCorr μ hm hr1 hr2 hD0 hρ0 ht hsmall hdensμ hcorrμ

/-- **Unit mixed `Lʳ` norm of a fixed graph law for large primes, for every `r > 1`**
(`lem:density:global-moment`, first paragraph). It takes `Target.Weil` and a single-label
correlation bound `ρ(y_v; y_{W \ {v}}) ≤ C/√p` for primes `p ≥ p₁`. -/
theorem graphLaw_eventually_unit [Nonempty W] (G' : Labellings.OrientedGraph W)
    (hW : Target.Weil) {C : ℝ} {p₁ : ℕ}
    (hcorr : ∀ (p : ℕ) [Fact p.Prime], p₁ ≤ p →
      ∀ (hInj : (injLabellings (ofLabellings G') p).Nonempty) (v : W),
        maxCorr (graphLaw (ofLabellings G') p hInj) (fun z => z v)
          (fun z (u : {u // u ≠ v}) => z u) ≤ C / √(p : ℝ))
    {r : ℝ} (hr : 1 < r) :
    ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p →
      ∃ hne : (Labellings.injLabellings (ZMod p) G').Nonempty,
        MixedLpBound (Labellings.graphLaw G' hne) r 1 := by
  obtain ⟨p₀, hp₀⟩ := graphLaw_eventually_unit_le_two G' hW hcorr
    (r := min r 2) (lt_min hr (by norm_num)) (min_le_right _ _)
  refine ⟨p₀, fun p _ hp => ?_⟩
  obtain ⟨hne, hmix⟩ := hp₀ p hp
  exact ⟨hne, hmix.mono_exponent zero_le_one (by linarith [lt_min hr (by norm_num : (1 : ℝ) < 2)])
    (min_le_left _ _)⟩

/-- The tail hypothesis in the shape of `hunit` of `Sarkozy.Comparison.paperMain_powerSavingBound`
(unit mixed `L³⁶` above a prime threshold, primes given as `[NeZero q]`, `q.Prime`), for a fixed
graph law. The law is `Influence.graphLaw`, which equals `Labellings.graphLaw` by
`graphLaw_ofLabellings`. -/
theorem graphLaw_unit_mixed_L36 [Nonempty W] (G' : Labellings.OrientedGraph W)
    (hW : Target.Weil) {C : ℝ} {p₁ : ℕ}
    (hcorr : ∀ (p : ℕ) [Fact p.Prime], p₁ ≤ p →
      ∀ (hInj : (injLabellings (ofLabellings G') p).Nonempty) (v : W),
        maxCorr (graphLaw (ofLabellings G') p hInj) (fun z => z v)
          (fun z (u : {u // u ≠ v}) => z u) ≤ C / √(p : ℝ)) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q →
      ∃ hInj : (injLabellings (ofLabellings G') q).Nonempty,
        MixedLpBound (graphLaw (ofLabellings G') q hInj) 36 1 := by
  obtain ⟨p₀, hp₀⟩ := graphLaw_eventually_unit G' hW hcorr (r := 36) (by norm_num)
  refine ⟨p₀, fun q _ hq hle => ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨hne, hmix⟩ := hp₀ q hle
  have hInj : (injLabellings (ofLabellings G') q).Nonempty := by
    rw [injLabellings_ofLabellings]
    exact hne
  refine ⟨hInj, ?_⟩
  rw [graphLaw_ofLabellings G' hInj hne]
  exact hmix

end Sarkozy.TailMoment

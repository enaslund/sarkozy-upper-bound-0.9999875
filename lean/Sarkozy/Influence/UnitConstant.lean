module

public import Sarkozy.Moments.CenteredInterpolation
public import Sarkozy.Peyre.Correlation




@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]

omit [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X] in
theorem sqrt_prod_eq (S : Finset V) (a : V → ℝ) (ha : ∀ v ∈ S, 0 ≤ a v) :
    √(∏ v ∈ S, a v) = ∏ v ∈ S, √(a v) := by
  have h0 : 0 ≤ ∏ v ∈ S, √(a v) := Finset.prod_nonneg (fun v _ => Real.sqrt_nonneg _)
  rw [← Real.sqrt_sq h0, ← Finset.prod_pow]
  congr 1
  exact Finset.prod_congr rfl (fun v hv => (Real.sq_sqrt (ha v hv)).symm)

/-- **The unit-constant argument.** Under uniform single-label marginals, a correlation bound
`ρ(z_v; z_{V \ {v}}) ≤ ρ` for every label and a density bound `D` for every marginal give
`|E_μ ∏_{v ∈ S} g_v(z_v)| ≤ ρ √D ∏_{v ∈ S} ‖g_v‖₂` for centred inputs on a nonempty `S`. -/
theorem slotForm_centeredL2_of_maxCorr (μ : FiniteLaw (V → X)) (hm : HasUniformMarginals μ)
    {ρ D : ℝ} (hρ : 0 ≤ ρ) (hD : 0 ≤ D)
    (hcorr : ∀ v : V, maxCorr μ (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤ ρ)
    (hdens : ∀ S : Finset V, ∀ g : V → X → ℝ,
      |slotForm μ S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform X).expect (fun x => |g v x|))
    (S : Finset V) (hS : S.Nonempty) (g : V → X → ℝ)
    (hg : ∀ v ∈ S, (FiniteLaw.uniform X).expect (g v) = 0) :
    |slotForm μ S g| ≤
      ρ * √D * ∏ v ∈ S, √((FiniteLaw.uniform X).expect (fun x => g v x ^ 2)) := by
  obtain ⟨v₀, hv₀⟩ := hS
  set Un := FiniteLaw.uniform X with hUn
  set F : (V → X) → ℝ := fun z => g v₀ (z v₀) with hF
  set G : (V → X) → ℝ := fun z => ∏ v ∈ S.erase v₀, g v (z v) with hG
  have hsplit : slotForm μ S g = μ.expect (fun z => F z * G z) := by
    unfold slotForm
    exact μ.expect_congr (fun z => (Finset.mul_prod_erase S (fun v => g v (z v)) hv₀).symm)
  have hcorrLe := corrLe_of_maxCorr_le (hcorr v₀)
  have hFfun : IsFunOf (fun z : V → X => z v₀) F := fun z z' h => by simp only [hF, h]
  have hGfun : IsFunOf (fun z : V → X => fun u : {u // u ≠ v₀} => z u) G := by
    intro z z' h
    simp only [hG]
    refine Finset.prod_congr rfl (fun v hv => ?_)
    have hne : v ≠ v₀ := Finset.ne_of_mem_erase hv
    have := congrFun h ⟨v, hne⟩
    simp only at this
    rw [this]
  have hF0 : μ.expect F = 0 := by
    rw [hF, hm v₀ (g v₀), hg v₀ hv₀]
  have hmain := corrLe_isFunOf hcorrLe hFfun hGfun hF0
  have hvar : μ.expect (fun z => (G z - μ.expect G) ^ 2) ≤ μ.expect (fun z => G z ^ 2) := by
    rw [FiniteLaw.expect_sq_sub_mean]
    nlinarith [sq_nonneg (μ.expect G)]
  have hF2 : μ.expect (fun z => F z ^ 2) = Un.expect (fun x => g v₀ x ^ 2) :=
    hm v₀ (fun x => g v₀ x ^ 2)
  have hG2 : μ.expect (fun z => G z ^ 2) ≤
      D * ∏ v ∈ S.erase v₀, Un.expect (fun x => g v x ^ 2) := by
    have h1 := hdens (S.erase v₀) (fun v x => g v x ^ 2)
    have e1 : slotForm μ (S.erase v₀) (fun v x => g v x ^ 2) = μ.expect (fun z => G z ^ 2) := by
      unfold slotForm
      exact μ.expect_congr (fun z => by simp only [hG, Finset.prod_pow])
    have e2 : ∀ v, Un.expect (fun x => |g v x ^ 2|) = Un.expect (fun x => g v x ^ 2) :=
      fun v => Un.expect_congr (fun x => abs_of_nonneg (sq_nonneg _))
    rw [e1] at h1
    simp only [e2] at h1
    exact (le_abs_self _).trans h1
  have hprod0 : ∀ v ∈ S.erase v₀, 0 ≤ Un.expect (fun x => g v x ^ 2) :=
    fun v _ => Un.second_moment_nonneg _
  rw [hsplit]
  calc |μ.expect (fun z => F z * G z)|
      ≤ ρ * √(μ.expect (fun z => F z ^ 2)) * √(μ.expect (fun z => (G z - μ.expect G) ^ 2)) :=
        hmain
    _ ≤ ρ * √(Un.expect (fun x => g v₀ x ^ 2)) *
          √(D * ∏ v ∈ S.erase v₀, Un.expect (fun x => g v x ^ 2)) := by
        rw [hF2]
        exact mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hvar.trans hG2))
          (mul_nonneg hρ (Real.sqrt_nonneg _))
    _ = ρ * √D * ∏ v ∈ S, √(Un.expect (fun x => g v x ^ 2)) := by
        rw [Real.sqrt_mul hD, sqrt_prod_eq _ _ hprod0,
          ← Finset.mul_prod_erase S (fun v => √(Un.expect (fun x => g v x ^ 2))) hv₀]
        ring

/-- **Unit mixed `Lʳ` norm from bounded density and small single-label correlations.**
This is the form in which `lem:density:global-moment` uses the pinned influence estimate.
Let the laws `μ n` have uniform single-label marginals and a common density bound `D` on
every marginal, and let `ρ(z_v; z_{V \ {v}}) ≤ ρ_n → 0` under `μ n`. Then `μ n` has unit
mixed `Lʳ` norm for all large `n` (`1 < r ≤ 2`). -/
theorem eventually_mixedLpBound_of_density_and_maxCorr [Nonempty V]
    (μ : ℕ → FiniteLaw (V → X)) (hm : ∀ n, HasUniformMarginals (μ n)) {r D : ℝ}
    (hr1 : 1 < r) (hr2 : r ≤ 2) (hD : 0 ≤ D) (ρ : ℕ → ℝ) (hρ0 : ∀ n, 0 ≤ ρ n)
    (hρ : Filter.Tendsto ρ Filter.atTop (nhds 0))
    (hdens : ∀ n, ∀ S : Finset V, ∀ g : V → X → ℝ,
      |slotForm (μ n) S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform X).expect (fun x => |g v x|))
    (hcorr : ∀ n, ∀ v : V,
      maxCorr (μ n) (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤ ρ n) :
    ∀ᶠ n in Filter.atTop, MixedLpBound (μ n) r 1 := by
  have hε : Filter.Tendsto (fun n => ρ n * √D) Filter.atTop (nhds 0) := by
    simpa only [zero_mul] using hρ.mul_const (√D)
  refine eventually_mixedLpBound_of_density_and_centeredL2 μ hm hr1 hr2 hD
    (fun n => ρ n * √D) (fun n => mul_nonneg (hρ0 n) (Real.sqrt_nonneg _)) hε
    (fun n S _ g => hdens n S g) ?_
  intro n S hS g hg
  have hSne : S.Nonempty := by
    have h2 : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
    exact Finset.card_pos.mp (by omega)
  exact slotForm_centeredL2_of_maxCorr (μ n) (hm n) (hρ0 n) hD (hcorr n) (hdens n) S hSne g hg

/-- **Unit mixed `Lʳ` norm for one law** (any alphabet, e.g. `ZMod p` with `p` varying). If
`ρ(z_v; z_{V \ {v}}) ≤ ρ` for every label, marginal densities are at most `D`, and
`ρ √D t^{|V|(1-r/2)} + 4^{|V|} D t^{1-r} ≤ τ_V(r)` for some `t ≥ 1`, then `μ` has unit mixed
`Lʳ` norm. The constant `τ_V(r)` (`centeredTolerance`) depends only on `|V|` and `r`. -/
theorem mixedLpBound_of_density_and_maxCorr [Nonempty V] (μ : FiniteLaw (V → X))
    (hm : HasUniformMarginals μ) {r D ρ t : ℝ} (hr1 : 1 < r) (hr2 : r ≤ 2) (hD : 0 ≤ D)
    (hρ : 0 ≤ ρ) (ht : 1 ≤ t)
    (hsmall : ρ * √D * t ^ ((Fintype.card V : ℝ) * (1 - r / 2)) +
      4 ^ Fintype.card V * D * t ^ (1 - r) ≤ centeredTolerance V r)
    (hdens : ∀ S : Finset V, ∀ g : V → X → ℝ,
      |slotForm μ S g| ≤ D * ∏ v ∈ S, (FiniteLaw.uniform X).expect (fun x => |g v x|))
    (hcorr : ∀ v : V, maxCorr μ (fun z => z v) (fun z (u : {u // u ≠ v}) => z u) ≤ ρ) :
    MixedLpBound μ r 1 := by
  refine mixedLpBound_of_density_and_centeredL2 μ hm hr1 hr2 hD
    (mul_nonneg hρ (Real.sqrt_nonneg D)) ht hsmall (fun S _ g => hdens S g) ?_
  intro S hS g hg
  have hSne : S.Nonempty := by
    have h2 : 2 ≤ S.card := (Finset.mem_filter.mp hS).2
    exact Finset.card_pos.mp (by omega)
  exact slotForm_centeredL2_of_maxCorr μ hm hρ hD hcorr hdens S hSne g hg

end Sarkozy.Influence

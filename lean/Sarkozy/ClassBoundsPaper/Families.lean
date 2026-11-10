module

public import Sarkozy.Param.Criterion
public import Sarkozy.Comparison.Criterion

@[expose] public section

/-!
# Uniform robust class bounds from two families (`def:cp5`, `def:robust`, `def:cp8`(b))

`ClassInputs.robust` asks for the robust class bounds of all the classes of the construction with
one relative error, one remainder constant and one family of remainders ("uniformly in the class",
`def:cp5`; `def:robust`: a family of bounds is robust uniformly if the remainders of the whole
family together satisfy (a)). The paper proves them in two families: the envelope classes
(`thm:envelopes`(i), `cor:envelope-costs`) and the variance classes (`cor:var-classes`,
`lem:var-gain`), each uniformly within the family.

`robust_of_families`: if the classes are indexed by `ι₁ ⊕ ι₂` and each family is robust uniformly
with nonnegative relative errors and remainders, then all the classes are robust uniformly, with the
sums `ε₁ + ε₂`, `c₁ + c₂`, `r₁ + r₂` (at a counterexample `Y > 0`, `counterexample_pos`). This is
the form in which `ClassInputs.robust` is meant to be supplied.
-/

open Finset Filter
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.Comparison
open Sarkozy.Param (Params)

theorem remainder_add (c₁ c₂ : ℝ) (L : ℕ) (A : Finset ℤ) :
    remainder (c₁ + c₂) L A = remainder c₁ L A + remainder c₂ L A := by
  unfold remainder
  ring

/-- **Two uniformly robust families of class bounds give one** (`def:robust`, uniformly in the
class). -/
theorem robust_of_families {P : Params} {Y : ℕ → Finset ℤ → ℝ} {X : ℕ → Type}
    {ι₁ ι₂ : ℕ → Type} [∀ L, DecidableEq (ι₁ L)] [∀ L, DecidableEq (ι₂ L)]
    (cls : ∀ L, X L → Option (ι₁ L ⊕ ι₂ L)) (sel : ∀ L, Finset (X L))
    (I : ∀ L, Finset ℤ → X L → ℝ) (φ π : ∀ L, X L → ℝ) (hπ : ∀ L ω, 0 ≤ π L ω)
    (h₁ : ∃ ε : ℕ → ℝ, (∀ L, 0 ≤ ε L) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∃ r : ∀ L, Finset ℤ → X L → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
      Param.AtCounterexamples P Y fun L A =>
        (∀ i, ∑ ω ∈ (sel L).filter (fun ω => cls L ω = some (Sum.inl i)), I L A ω ≤
          ∑ ω ∈ (sel L).filter (fun ω => cls L ω = some (Sum.inl i)),
            ((φ L ω + ε L * π L ω) * Y L A + r L A ω)) ∧
        ∑ ω ∈ sel L, r L A ω ≤ remainder c L A)
    (h₂ : ∃ ε : ℕ → ℝ, (∀ L, 0 ≤ ε L) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∃ r : ∀ L, Finset ℤ → X L → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
      Param.AtCounterexamples P Y fun L A =>
        (∀ i, ∑ ω ∈ (sel L).filter (fun ω => cls L ω = some (Sum.inr i)), I L A ω ≤
          ∑ ω ∈ (sel L).filter (fun ω => cls L ω = some (Sum.inr i)),
            ((φ L ω + ε L * π L ω) * Y L A + r L A ω)) ∧
        ∑ ω ∈ sel L, r L A ω ≤ remainder c L A) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∃ r : ∀ L, Finset ℤ → X L → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
      Param.AtCounterexamples P Y fun L A =>
        (∀ i, ∑ ω ∈ (sel L).filter (fun ω => cls L ω = some i), I L A ω ≤
          ∑ ω ∈ (sel L).filter (fun ω => cls L ω = some i),
            ((φ L ω + ε L * π L ω) * Y L A + r L A ω)) ∧
        ∑ ω ∈ sel L, r L A ω ≤ remainder c L A := by
  obtain ⟨ε₁, hε₁0, hε₁, c₁, hc₁, r₁, hr₁, H₁⟩ := h₁
  obtain ⟨ε₂, hε₂0, hε₂, c₂, hc₂, r₂, hr₂, H₂⟩ := h₂
  refine ⟨fun L => ε₁ L + ε₂ L, by simpa using hε₁.add hε₂, c₁ + c₂, add_nonneg hc₁ hc₂,
    fun L A ω => r₁ L A ω + r₂ L A ω, fun L A ω => add_nonneg (hr₁ L A ω) (hr₂ L A ω), ?_⟩
  unfold Param.AtCounterexamples at H₁ H₂ ⊢
  filter_upwards [H₁, H₂] with L g₁ g₂ C hC hk A hA hY
  have hY0 : 0 < Y L A := Param.counterexample_pos P hC hY
  obtain ⟨g₁a, g₁b⟩ := g₁ C hC hk A hA hY
  obtain ⟨g₂a, g₂b⟩ := g₂ C hC hk A hA hY
  refine ⟨?_, ?_⟩
  · rintro (i | i)
    · refine (g₁a i).trans (sum_le_sum fun ω _ => ?_)
      have h1 : 0 ≤ ε₂ L * π L ω * Y L A :=
        mul_nonneg (mul_nonneg (hε₂0 L) (hπ L ω)) hY0.le
      have h2 := hr₂ L A ω
      nlinarith
    · refine (g₂a i).trans (sum_le_sum fun ω _ => ?_)
      have h1 : 0 ≤ ε₁ L * π L ω * Y L A :=
        mul_nonneg (mul_nonneg (hε₁0 L) (hπ L ω)) hY0.le
      have h2 := hr₁ L A ω
      nlinarith
  · rw [sum_add_distrib, remainder_add]
    exact add_le_add g₁b g₂b

end Sarkozy.ClassBoundsPaper

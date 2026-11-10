module

public import Sarkozy.Functional.Model
public import Sarkozy.RelativeErrors

/-!
# Least normalized counterexamples (`def:record:counterexample`)

`def:record:counterexample` of the paper (`paper/sections/08_scale_comparison.tex`):
for exponents `a > 0`, `0 < θ ≤ 1` and a constant `C₀ ≥ 1`, a pair `(L, A)` with
`A ⊆ [K L]` square-difference-free is a *least normalized counterexample* if
`Y(L, A) > C₀ L^{-a} α^θ` and `Y(ℓ, A') ≤ C₀ ℓ^{-a} α_{A'}^θ` for every smaller scale
`ℓ < L` and every square-difference-free `A' ⊆ [K ℓ]`.

The functional is an arbitrary `Y : ℕ → Finset ℤ → ℝ`, as in the project's
`EnergyUpperBoundAt` and `RawComparison` (`Sarkozy/Induction.lean`,
`Sarkozy/RelativeErrors.lean`); the interval scale is `K = blockScale`, and the
paper's functional is `Sarkozy.Functional.FunctionalData.functional`. The smaller
scales are `1 ≤ ℓ < L` (the scale `0` carries only `A' = ∅`).

* `ScaleBound Y a θ C₀ ℓ`: the bound at the scale `ℓ`.
* `IsLeastCounterexample Y a θ C₀ L A`: `def:record:counterexample`.
* `scaleBound_iff_energyUpperBoundAt`, `isLeastCounterexample_iff`: with the
  project's exponents `(a, θ) = (decay, densityExponent)` these are exactly
  `EnergyUpperBoundAt` and the antecedent of `RawComparison`.
* `IsLeastCounterexample.density_pos`: `α > 0`, since `F_∅ = 0`
  (`FunctionalData.functional_empty`).

The project's endgame uses `densityExponent = 1.014587 > 1` (the improved
induction of `sec:density:moments-prefix`–`sec:four-routes-closing`), while
`prop:record:density-structured` needs `θ ≤ 1` for its final Jensen step; the
definitions here allow any `θ`.
-/

@[expose] public section

open Finset

namespace Sarkozy.Structured

/-- The bound `Y(ℓ, A') ≤ C₀ ℓ^{-a} α_{A'}^θ` for every square-difference-free
`A' ⊆ [K ℓ]`. -/
def ScaleBound (Y : ℕ → Finset ℤ → ℝ) (a θ C0 : ℝ) (ℓ : ℕ) : Prop :=
  ∀ A : Finset ℤ, Admissible (blockScale * ℓ) A →
    Y ℓ A ≤ C0 * (ℓ : ℝ) ^ (-a) * density (blockScale * ℓ) A ^ θ

/-- **`def:record:counterexample`**: `(L, A)` is a least normalized counterexample for
`(a, θ, C₀)`. -/
def IsLeastCounterexample (Y : ℕ → Finset ℤ → ℝ) (a θ C0 : ℝ) (L : ℕ) (A : Finset ℤ) :
    Prop :=
  Admissible (blockScale * L) A ∧
    C0 * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ θ < Y L A ∧
    ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < L → ScaleBound Y a θ C0 ℓ

theorem scaleBound_iff_energyUpperBoundAt (Y : ℕ → Finset ℤ → ℝ) (C : ℝ) (ℓ : ℕ) :
    ScaleBound Y decay densityExponent C ℓ ↔ EnergyUpperBoundAt Y C ℓ :=
  Iff.rfl

/-- With the project's exponents, the least normalized counterexamples are exactly
the pairs in the antecedent of `RawComparison` (and of `Comparison.AtCounterexamples`). -/
theorem isLeastCounterexample_iff (Y : ℕ → Finset ℤ → ℝ) (C : ℝ) (L : ℕ) (A : Finset ℤ) :
    IsLeastCounterexample Y decay densityExponent C L A ↔
      Admissible (blockScale * L) A ∧
        (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k) ∧
        C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A := by
  unfold IsLeastCounterexample
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, fun k hk hkL => (scaleBound_iff_energyUpperBoundAt Y C k).mp (h3 k hk hkL), h2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h3, fun k hk hkL => (scaleBound_iff_energyUpperBoundAt Y C k).mpr (h2 k hk hkL)⟩

namespace IsLeastCounterexample

variable {Y : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}

theorem admissible (h : IsLeastCounterexample Y a θ C0 L A) : Admissible (blockScale * L) A :=
  h.1

theorem lower (h : IsLeastCounterexample Y a θ C0 L A) :
    C0 * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ θ < Y L A :=
  h.2.1

/-- The hypothesis on smaller scales. -/
theorem smaller (h : IsLeastCounterexample Y a θ C0 L A) {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hℓL : ℓ < L)
    {A' : Finset ℤ} (hA' : Admissible (blockScale * ℓ) A') :
    Y ℓ A' ≤ C0 * (ℓ : ℝ) ^ (-a) * density (blockScale * ℓ) A' ^ θ :=
  h.2.2 ℓ hℓ hℓL A' hA'

/-- `α > 0` at a least normalized counterexample, if `Y(L, ∅) ≤ 0` (for the paper's
functional `F_∅ = 0`, so `Y(L, ∅) = 0`) and `θ ≠ 0`. -/
theorem density_pos (h : IsLeastCounterexample Y a θ C0 L A) (hθ : θ ≠ 0)
    (hY0 : Y L ∅ ≤ 0) : 0 < density (blockScale * L) A := by
  rcases (density_nonneg (blockScale * L) A).lt_or_eq with hpos | hzero
  · exact hpos
  · exfalso
    have hcard : A.card = 0 ∨ ((blockScale * L : ℕ) : ℝ) = 0 := by
      unfold density at hzero
      rcases div_eq_zero_iff.mp hzero.symm with h1 | h1
      · left; exact_mod_cast h1
      · right; exact h1
    have hA : A = ∅ ∨ ((blockScale * L : ℕ) : ℝ) = 0 := by
      rcases hcard with h1 | h1
      · left; exact Finset.card_eq_zero.mp h1
      · right; exact h1
    have hlow := h.lower
    rw [← hzero, Real.zero_rpow hθ, mul_zero] at hlow
    rcases hA with hA | hN
    · subst hA
      linarith
    · -- `N = 0` forces `A ⊆ Icc 1 0 = ∅`
      have hN' : blockScale * L = 0 := by exact_mod_cast hN
      have hsub := h.admissible.1
      rw [hN'] at hsub
      have hAe : A = ∅ := by
        apply Finset.eq_empty_of_forall_notMem
        intro x hx
        have := Finset.mem_Icc.mp (hsub hx)
        push_cast at this
        omega
      subst hAe
      linarith

end IsLeastCounterexample

/-! ### The paper's functional -/

namespace FunctionalDataLemmas

open Sarkozy.Functional Sarkozy.FourierArithmetic

/-- `F_∅ = 0`: the lift of the zero function vanishes. -/
theorem liftAt_empty (d : FunctionalData) (L : ℕ) (z : (d.family L).Group) :
    d.liftAt L ∅ z = 0 := by
  simp [FunctionalData.liftAt, wholeLift, lift, liftOn, intervalCoeff, indicator]

/-- `Y(L, ∅) = 0` for the paper's functional. -/
theorem functional_empty (d : FunctionalData) (L : ℕ) : d.functional L ∅ = 0 := by
  unfold FunctionalData.functional referenceEnergy
  have h : (fun z : Slot → (d.family L).Group => ∏ v, d.liftAt L ∅ (z v)) = fun _ => 0 := by
    funext z
    simp only [liftAt_empty]
    exact Finset.prod_eq_zero (Finset.mem_univ (0, 0, 0)) rfl
  rw [h]
  simp [FiniteLaw.expect]

end FunctionalDataLemmas

end Sarkozy.Structured

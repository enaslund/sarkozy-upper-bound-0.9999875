module

public import Sarkozy.Closing
public import Sarkozy.PowerBounds

@[expose] public section

/-!
# The least-counterexample step

Formalizes the scalar induction at the end of `thm:density:induction`.
The comparison recurrence, reflection inequality, finite initialization, and
uniform relative-error estimate are hypotheses, not supplied analytic proofs.
-/

namespace Sarkozy

/-- Desired upper energy estimate at a single physical scale. -/
def EnergyUpperBoundAt (Y : ℕ → Finset ℤ → ℝ) (C : ℝ) (L : ℕ) : Prop :=
  ∀ A : Finset ℤ, Admissible (blockScale * L) A →
    Y L A ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent

/-- A strict scalar contraction rules out a positive least counterexample.

No sign condition on q or the error is needed: only their sum must be < 1.
The recurrence may depend on all previous scales, including different sets.
-/
theorem energyUpperBound_of_contraction
    {Y : ℕ → Finset ℤ → ℝ} {C q : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hC : 0 ≤ C)
    (hinit : ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt Y C L)
    (hrec : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ l : ℕ, 1 ≤ l → l < L → EnergyUpperBoundAt Y C l) →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A →
        C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A →
        Y L A ≤ (q + error L A) * Y L A)
    (hmargin : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A → q + error L A < 1) :
    ∀ L : ℕ, 1 ≤ L → EnergyUpperBoundAt Y C L := by
  intro L
  induction L using Nat.strong_induction_on with
  | h L ih =>
    intro hL A hA
    by_cases hsmall : L < L₀
    · exact hinit L hL hsmall A hA
    have hlarge : L₀ ≤ L := Nat.le_of_not_gt hsmall
    by_contra! hbad
    have hnonneg : 0 ≤ C * (L : ℝ) ^ (-decay) *
        density (blockScale * L) A ^ densityExponent :=
      mul_nonneg (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (Real.rpow_nonneg (density_nonneg _ _) _)
    have hy : 0 < Y L A := hnonneg.trans_lt hbad
    have hc := hrec L hL hlarge (fun l hl hlt => ih l hlt hl) A hA hbad
    have hm := hmargin L hL hlarge A hA
    have hstrict := mul_lt_mul_of_pos_right hm hy
    linarith

/-- Reflection and the scalar induction together supply the explicit energy interface. -/
theorem scaledEnergyEstimate_of_contraction
    {Y : ℕ → Finset ℤ → ℝ} {C q : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hC : 0 < C)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hinit : ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt Y C L)
    (hrec : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ l : ℕ, 1 ≤ l → l < L → EnergyUpperBoundAt Y C l) →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A →
        C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A →
        Y L A ≤ (q + error L A) * Y L A)
    (hmargin : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A → q + error L A < 1) :
    ScaledEnergyEstimate Y := by
  refine ⟨C, hC, ?_⟩
  intro L hL A hA
  exact ⟨hreflection L hL A hA,
    energyUpperBound_of_contraction hC.le hinit hrec hmargin L hL A hA⟩

/-- The final bound conditional on the paper's still-unformalized analytic interfaces.

This is deliberately an implication, not an unconditional formalization of the paper.
-/
theorem powerSavingBound_of_jointClosing
    {l : ClosingLedger} (hledger : l.Bounds)
    {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} {L₀ : ℕ}
    {error : ℕ → Finset ℤ → ℝ}
    (hC : 0 < C)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hinit : ∀ L : ℕ, 1 ≤ L → L < L₀ → EnergyUpperBoundAt Y C L)
    (hrec : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L →
      (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k) →
      ∀ A : Finset ℤ, Admissible (blockScale * L) A →
        C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A →
        Y L A ≤ (l.theta + error L A) * Y L A)
    (herror : ∀ L : ℕ, 1 ≤ L → L₀ ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → error L A ≤ closingMargin) :
    PowerSavingBound := by
  apply powerSavingBound_of_scaledEnergyEstimate
  apply scaledEnergyEstimate_of_contraction hC hreflection hinit hrec
  intro L hL hlarge A hA
  exact ClosingLedger.perturbed_lt_one hledger (herror L hL hlarge A hA)

end Sarkozy

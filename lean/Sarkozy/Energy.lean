module

public import Sarkozy.FourierLift
public import Sarkozy.Slots
public import Sarkozy.RelativeErrors

/-!
# The Fourier energy and its density lower bound

The energy is a literal expectation of a product over the 72 slots. The lower
bound follows from the proved signed Hölder theorem, normalization, uniform
marginals, and character orthogonality. No density lower bound is included in
the model's definition. Constructing the paper's particular reference law and
proving its reflection positivity remain separate tasks.
-/

@[expose] public section

open scoped BigOperators Topology

namespace Sarkozy

def HasUniformMarginals {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]
    (μ : FiniteLaw (V → X)) : Prop :=
  ∀ v : V, ∀ f : X → ℝ, μ.expect (fun z => f (z v)) = (FiniteLaw.uniform X).expect f

noncomputable def referenceEnergy {X : Type*} [Fintype X]
    (μ : FiniteLaw (Slot → X)) (f : X → ℝ) : ℝ :=
  μ.expect (fun z => ∏ v, f (z v))

theorem referenceEnergy_eq_diagonal {X : Type*} [Fintype X]
    (μ : FiniteLaw (Slot → X)) (f : X → ℝ) :
    referenceEnergy μ f = diagonalIntegral (signedIntegral μ.weight) f := rfl

theorem referenceEnergy_nonneg {X : Type*} [Fintype X]
    (μ : FiniteLaw (Slot → X)) (hp : SlotReflectionPositive (signedIntegral μ.weight))
    (f : X → ℝ) : 0 ≤ referenceEnergy μ f := slot_diagonal_nonneg hp f

/-- The reference energy controls the 72nd power of the uniform mean, even
when the input function has negative values. -/
theorem mean_pow_le_referenceEnergy {X : Type*} [Fintype X] [Nonempty X]
    (μ : FiniteLaw (Slot → X)) (hp : SlotReflectionPositive (signedIntegral μ.weight))
    (hm : HasUniformMarginals μ) (f : X → ℝ) :
    |(FiniteLaw.uniform X).expect f| ^ 72 ≤ referenceEnergy μ f := by
  have hL : signedIntegral μ.weight (fun _ => 1) = 1 := μ.expect_const 1
  have hholder : ∀ a : Slot → X → ℝ,
      |multilinearIntegral (signedIntegral μ.weight) a| ≤
        ∏ v, diagonalIntegral (signedIntegral μ.weight) (a v) ^
          ((1 : ℝ) / (Fintype.card Slot : ℝ)) := by
    intro a
    simpa only [card_slot, Nat.cast_ofNat] using slot_signed_holder hp a
  simpa only [card_slot, referenceEnergy_eq_diagonal] using
    mean_pow_le_diagonal (signedIntegral μ.weight) (FiniteLaw.uniform X).expect
      hL hm hholder f (slot_diagonal_nonneg hp f)

theorem abs_referenceEnergy_le {X : Type*} [Fintype X]
    (μ : FiniteLaw (Slot → X)) {f : X → ℝ} {B : ℝ}
    (hf : ∀ x, |f x| ≤ B) : |referenceEnergy μ f| ≤ B ^ 72 := by
  apply μ.abs_expect_le_const
  intro z
  calc
    |∏ v, f (z v)| = ∏ v, |f (z v)| := Finset.abs_prod _ _
    _ ≤ ∏ _v : Slot, B := Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) (fun v _ => hf (z v))
    _ = B ^ 72 := by simp only [Finset.prod_const, Finset.card_univ, card_slot]

variable {G : ℕ → Type*} [∀ L, AddCommGroup (G L)] [∀ L, Fintype (G L)]

/-- Data for the concrete energy. Group sizes, frequency sets, and reference
laws may depend on the physical scale. -/
structure FourierModel (G : ℕ → Type*) [∀ L, AddCommGroup (G L)] [∀ L, Fintype (G L)] where
  residue : ∀ L, ℤ →+ G L
  characters : ∀ L, Finset (AddChar (G L) ℂ)
  law : ∀ L, FiniteLaw (Slot → G L)

namespace FourierModel

noncomputable def energy (model : FourierModel G) (L : ℕ) (A : Finset ℤ) : ℝ :=
  referenceEnergy (model.law L)
    (fourierLift (model.residue L) (blockScale * L) A (model.characters L))

def Regular (model : FourierModel G) : Prop :=
  ∀ L : ℕ, 1 ≤ L →
    (1 : AddChar (G L) ℂ) ∈ model.characters L ∧
    HasUniformMarginals (model.law L) ∧
    SlotReflectionPositive (signedIntegral (model.law L).weight)

@[simp] theorem energy_empty (model : FourierModel G) (L : ℕ) : model.energy L ∅ = 0 := by
  unfold energy referenceEnergy
  simp only [fourierLift_empty, Finset.prod_const, Finset.card_univ, card_slot,
    zero_pow (by decide : 72 ≠ 0), FiniteLaw.expect_const]

theorem density_pow_le_energy (model : FourierModel G) (hr : model.Regular)
    (L : ℕ) (hL : 1 ≤ L) (A : Finset ℤ) :
    density (blockScale * L) A ^ slots ≤ model.energy L A := by
  obtain ⟨hT, hm, hp⟩ := hr L hL
  have h := mean_pow_le_referenceEnergy (model.law L) hp hm
    (fourierLift (model.residue L) (blockScale * L) A (model.characters L))
  rw [mean_fourierLift _ _ _ _ hT, abs_of_nonneg (density_nonneg _ _)] at h
  exact h

theorem abs_energy_le (model : FourierModel G) (L : ℕ) (A : Finset ℤ) :
    |model.energy L A| ≤ ((model.characters L).card * density (blockScale * L) A) ^ 72 := by
  exact abs_referenceEnergy_le (model.law L)
    (abs_fourierLift_le (model.residue L) (blockScale * L) A (model.characters L))

/-- The endgame for an explicit Fourier model. Reflection lower bounds,
initialization, and uniform error absorption are all derived internally.
The remaining hypotheses identify the unresolved analytic inputs precisely. -/
theorem powerSavingBound (model : FourierModel G) (hr : model.Regular)
    {l : ClosingLedger} (hledger : l.Bounds)
    {M E : ℝ} {q : ℕ → ℝ} (hM : 0 < M) (hE : 0 ≤ E)
    (hglobal : GlobalMomentBound model.energy M)
    (hrec : RawComparison model.energy q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound :=
  powerSavingBound_of_rawComparison hledger hM hE
    (fun L hL A _ => model.density_pow_le_energy hr L hL A) hglobal hrec hq

end FourierModel
end Sarkozy

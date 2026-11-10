module

public import Sarkozy.Moments.Basic
public import Sarkozy.Energy

/-!
# The L36 moment bridge

This isolates the two mathematical estimates used for the global second-density
bound: a mixed L36 bound for the reference law, and a 36th-moment bound for the
Fourier lift. The passage to the global bound, including its constants and
scale exponents, is proved here.
-/

@[expose] public section

open scoped BigOperators Topology

namespace Sarkozy

def MixedLpBound {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]
    (μ : FiniteLaw (V → X)) (p C : ℝ) : Prop :=
  ∀ f : V → X → ℝ, |μ.expect (fun z => ∏ v, f v (z v))| ≤
    C * ∏ v, (FiniteLaw.uniform X).lpNorm p (f v)

theorem referenceEnergy_le_moment_sq {X : Type*} [Fintype X] [Nonempty X]
    (μ : FiniteLaw (Slot → X)) {C : ℝ} (h : MixedLpBound μ 36 C) (f : X → ℝ) :
    referenceEnergy μ f ≤ C * ((FiniteLaw.uniform X).moment 36 f) ^ 2 := by
  have hm := h (fun _ => f)
  simp only [Finset.prod_const, Finset.card_univ, card_slot] at hm
  have he : (FiniteLaw.uniform X).lpNorm 36 f ^ 72 =
      ((FiniteLaw.uniform X).moment 36 f) ^ 2 := by
    rw [show 72 = 36 * 2 by omega, pow_mul]
    rw [← Real.rpow_natCast ((FiniteLaw.uniform X).lpNorm 36 f) 36]
    norm_num only [Nat.cast_ofNat]
    rw [(FiniteLaw.uniform X).lpNorm_rpow (by norm_num : (36 : ℝ) ≠ 0)]
  rw [he] at hm
  exact (le_abs_self _).trans hm

namespace FourierModel

variable {G : ℕ → Type*} [∀ L, AddCommGroup (G L)] [∀ L, Fintype (G L)]

/-- The analytic Fourier-lift estimate at the selected moment and slack. -/
def LiftMomentBound (model : FourierModel G) (D : ℝ) : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
    (FiniteLaw.uniform (G L)).moment 36
      (fourierLift (model.residue L) (blockScale * L) A (model.characters L)) ≤
        D * (L : ℝ) ^ (momentSlack / 2) * density (blockScale * L) A

theorem globalMomentBound_of_mixed (model : FourierModel G) {C D : ℝ}
    (hC : 0 ≤ C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    (hlift : model.LiftMomentBound D) : GlobalMomentBound model.energy (C * D ^ 2) := by
  intro L hL A hA
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hbound := referenceEnergy_le_moment_sq (model.law L) (hmixed L hL)
    (fourierLift (model.residue L) (blockScale * L) A (model.characters L))
  apply hbound.trans
  have hsquare := pow_le_pow_left₀
    ((FiniteLaw.uniform (G L)).moment_nonneg 36 _) (hlift L hL A hA) 2
  apply (mul_le_mul_of_nonneg_left hsquare hC).trans_eq
  rw [mul_pow, mul_pow, ← Real.rpow_natCast ((L : ℝ) ^ (momentSlack / 2)) 2,
    ← Real.rpow_mul hLpos.le]
  norm_num only [Nat.cast_ofNat]
  rw [show momentSlack / 2 * 2 = momentSlack by ring]
  ring

/-- A stronger endgame interface: the global moment bound is now a conclusion
of the two explicit moment inputs rather than an additional hypothesis. -/
theorem powerSavingBound_of_mixed (model : FourierModel G) (hr : model.Regular)
    {l : ClosingLedger} (hledger : l.Bounds)
    {C D E : ℝ} {q : ℕ → ℝ} (hC : 0 < C) (hD : 0 < D) (hE : 0 ≤ E)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    (hlift : model.LiftMomentBound D) (hrec : RawComparison model.energy q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound :=
  model.powerSavingBound hr hledger (mul_pos hC (pow_pos hD 2)) hE
    (model.globalMomentBound_of_mixed hC.le hmixed hlift) hrec hq

end FourierModel
end Sarkozy

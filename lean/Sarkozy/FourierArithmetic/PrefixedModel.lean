module

public import Sarkozy.FourierArithmetic.PrefixedIndicatorMoments
public import Sarkozy.Moments.Energy

/-!
# Fourier models with a fixed finite prefix

The prefix group and its set of characters are fixed, while the tail
coordinates and the whole-support families can change with the scale.
The Fourier moment estimate is proved uniformly in that changing tail.
-/

@[expose] public section

open scoped BigOperators Topology

namespace Sarkozy

open FourierArithmetic

variable {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    (p : ∀ L, J L → ℕ) [∀ L j, NeZero (p L j)]
    (X₀ : Type) [AddCommGroup X₀] [Fintype X₀]

structure PrefixedResidueModel (p : ∀ L, J L → ℕ) [∀ L j, NeZero (p L j)]
    (X₀ : Type) [AddCommGroup X₀] [Fintype X₀] where
  prefixResidue : ℤ →+ X₀
  prefixSet : Finset (AddChar X₀ ℂ)
  supports : ∀ L, AddChar X₀ ℂ → Finset (Finset (J L))
  cutoff : ℕ → ℕ
  law : ∀ L, FiniteLaw (Slot → X₀ × ResidueSpace (p L))

namespace PrefixedResidueModel

noncomputable def toFourierModel (model : PrefixedResidueModel p X₀) :
    FourierModel (fun L => X₀ × ResidueSpace (p L)) where
  residue L := model.prefixResidue.prod (integerResidue (p L))
  characters L := prefixCharacters (p L) model.prefixSet (model.supports L)
  law := model.law

def Arithmetic (model : PrefixedResidueModel p X₀) : Prop :=
  ∀ L : ℕ, 1 ≤ L →
    (Pairwise fun i j => (p L i).Coprime (p L j)) ∧ Function.Injective (p L) ∧
    0 < model.cutoff L ∧
    (∀ χ ∈ model.prefixSet, ∀ U ∈ model.supports L χ, ∏ j ∈ U, p L j ≤ model.cutoff L) ∧
    2 * model.cutoff L ≤ blockScale * L + 1 ∧
    model.cutoff L ^ 5 ≤ blockScale * L + 1

theorem regular (model : PrefixedResidueModel p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight)) :
    (model.toFourierModel p X₀).Regular := by
  intro L hL
  exact ⟨prefixCharacters_one (p L) hprefix (hzero L hL), hm L hL, hp L hL⟩

theorem exists_liftMomentBound (model : PrefixedResidueModel p X₀)
    (ha : model.Arithmetic p X₀) :
    ∃ D : ℝ, 0 < D ∧ (model.toFourierModel p X₀).LiftMomentBound D := by
  have hε : 0 < momentSlack / 2 := by norm_num [momentSlack]
  obtain ⟨C, hC, hc⟩ := uniform_prefixed_indicator_moment 18 (by norm_num)
    (momentSlack / 2) hε
  refine ⟨((model.prefixSet.card : ℝ) + 1) ^ 36 * C *
      (blockScale : ℝ) ^ (momentSlack / 2), ?_, ?_⟩
  · have hcard : (0 : ℝ) < model.prefixSet.card + 1 := by positivity
    exact mul_pos (mul_pos (pow_pos hcard _) hC)
      (Real.rpow_pos_of_pos (by norm_num [blockScale]) _)
  intro L hL A hA
  obtain ⟨hcop, hinj, hQ, hden, hsmall, hsmall'⟩ := ha L hL
  have hN : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hA0 : A ⊆ Finset.Icc 0 ((blockScale * L : ℕ) : ℤ) := by
    intro a ha
    have hab := Finset.mem_Icc.mp (hA.1 ha)
    exact Finset.mem_Icc.mpr ⟨by omega, hab.2⟩
  have hm := hc (p L) model.prefixResidue hcop hinj model.prefixSet (model.supports L)
    (model.cutoff L) hQ hden (blockScale * L) hN
    (by exact_mod_cast hsmall) (by exact_mod_cast hsmall') A hA0
  have hQle : model.cutoff L ≤ blockScale * L := by omega
  have hpow : (model.cutoff L : ℝ) ^ (momentSlack / 2) ≤
      ((blockScale * L : ℕ) : ℝ) ^ (momentSlack / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hQle) hε.le
  have hcard : (model.prefixSet.card : ℝ) ^ 36 ≤ ((model.prefixSet.card : ℝ) + 1) ^ 36 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) _
  apply hm.trans
  apply (mul_le_mul_of_nonneg_right
    (mul_le_mul (mul_le_mul_of_nonneg_right hcard hC.le) hpow
      (Real.rpow_nonneg (Nat.cast_nonneg _) _) (by positivity))
    (density_nonneg _ _)).trans_eq
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- The scalar endgame for the prefixed whole-support construction. The
remaining inputs concern the reference law, the comparison, and the ledger. -/
theorem powerSavingBound (model : PrefixedResidueModel p X₀)
    (ha : model.Arithmetic p X₀) (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {l : ClosingLedger} (hledger : l.Bounds) {C E : ℝ} {q : ℕ → ℝ}
    (hC : 0 < C) (hE : 0 ≤ E)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    (hrec : RawComparison (model.toFourierModel p X₀).energy q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p X₀ ha
  exact (model.toFourierModel p X₀).powerSavingBound_of_mixed
    (model.regular p X₀ hprefix hzero hm hp) hledger hC hD hE hmixed hlift hrec hq

end PrefixedResidueModel
end Sarkozy

module

public import Sarkozy.FourierArithmetic.IndicatorMoments
public import Sarkozy.Moments.Energy

/-!
# A concrete residue-coordinate Fourier model

For whole-support truncations on pairwise coprime, distinct coordinate
moduli, the Fourier-lift moment hypothesis is discharged by the arithmetic
moment theorem. Only elementary cutoff conditions are needed to apply it.
The actual reference law and the comparison recurrence remain separate data.
-/

@[expose] public section

open scoped BigOperators Topology

namespace Sarkozy

open FourierArithmetic

variable {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    (p : ∀ L, J L → ℕ) [∀ L j, NeZero (p L j)]

structure ResidueModel where
  supports : ∀ L, Finset (Finset (J L))
  cutoff : ℕ → ℕ
  law : ∀ L, FiniteLaw (Slot → ResidueSpace (p L))

namespace ResidueModel

noncomputable def toFourierModel (model : ResidueModel p) :
    FourierModel (fun L => ResidueSpace (p L)) where
  residue L := integerResidue (p L)
  characters L := supportCharacters (p L) (model.supports L)
  law := model.law

def Arithmetic (model : ResidueModel p) : Prop :=
  ∀ L : ℕ, 1 ≤ L →
    (Pairwise fun i j => (p L i).Coprime (p L j)) ∧ Function.Injective (p L) ∧
    0 < model.cutoff L ∧
    (∀ U ∈ model.supports L, ∏ j ∈ U, p L j ≤ model.cutoff L) ∧
    2 * model.cutoff L ≤ blockScale * L + 1 ∧
    model.cutoff L ^ 5 ≤ blockScale * L + 1

theorem regular (model : ResidueModel p)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight)) :
    (model.toFourierModel p).Regular := by
  intro L hL
  exact ⟨supportCharacters_one (p L) (hzero L hL), hm L hL, hp L hL⟩

/-- The global Fourier moment bound is a theorem for this model class,
uniform over the changing finite set of coordinate moduli. -/
theorem exists_liftMomentBound (model : ResidueModel p) (ha : model.Arithmetic p) :
    ∃ D : ℝ, 0 < D ∧ (model.toFourierModel p).LiftMomentBound D := by
  have hε : 0 < momentSlack / 2 := by norm_num [momentSlack]
  obtain ⟨C, hC, hc⟩ := uniform_indicator_moment 18 (by norm_num) (momentSlack / 2) hε
  refine ⟨C * (blockScale : ℝ) ^ (momentSlack / 2), ?_, ?_⟩
  · apply mul_pos hC (Real.rpow_pos_of_pos _ _)
    norm_num [blockScale]
  intro L hL A hA
  obtain ⟨hcop, hinj, hQ, hden, hsmall, hsmall'⟩ := ha L hL
  have hN : 0 < blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hA0 : A ⊆ Finset.Icc 0 ((blockScale * L : ℕ) : ℤ) := by
    intro a ha
    have hab := Finset.mem_Icc.mp (hA.1 ha)
    exact Finset.mem_Icc.mpr ⟨by omega, hab.2⟩
  have hm := hc (p L) hcop hinj (model.supports L) (model.cutoff L) hQ hden
    (blockScale * L) hN (by exact_mod_cast hsmall) (by exact_mod_cast hsmall') A hA0
  have hQle : model.cutoff L ≤ blockScale * L := by omega
  have hpow : (model.cutoff L : ℝ) ^ (momentSlack / 2) ≤
      ((blockScale * L : ℕ) : ℝ) ^ (momentSlack / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hQle) hε.le
  apply hm.trans
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hC.le)
    (density_nonneg _ _)).trans_eq
  rw [Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- The endgame with the lift-moment assumption removed for residue models.
The reference law's mixed L36 estimate and the comparison are still analytic
obligations for the paper's selected construction. -/
theorem powerSavingBound (model : ResidueModel p) (ha : model.Arithmetic p)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {l : ClosingLedger} (hledger : l.Bounds) {C E : ℝ} {q : ℕ → ℝ}
    (hC : 0 < C) (hE : 0 ≤ E)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    (hrec : RawComparison (model.toFourierModel p).energy q E)
    (hq : Filter.Tendsto q Filter.atTop (𝓝 l.theta)) : PowerSavingBound := by
  obtain ⟨D, hD, hlift⟩ := model.exists_liftMomentBound p ha
  exact (model.toFourierModel p).powerSavingBound_of_mixed
    (model.regular p hzero hm hp) hledger hC hD hE hmixed hlift hrec hq

end ResidueModel
end Sarkozy

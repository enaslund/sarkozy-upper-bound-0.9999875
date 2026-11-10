module

public import Sarkozy.Comparison.Final
public import Sarkozy.Reflection.SlotProduct
public import Sarkozy.Moments.FiniteAlphabet

/-!
# The conditional theorem for a fixed low part times a tail

The paper's reference law is a product over atoms; its atoms below a fixed bound form a
low part that does not depend on the scale, and the remaining tail atoms change with
the scale (`def:record:functional`, `lem:density:global-moment`). For a prefixed residue
model whose law is `μ₀ ⊗ μ_tail(L)`:

* uniform marginals and reflection positivity are required of the two factors
  separately (`Sarkozy.HasUniformMarginals.slotProduct`,
  `Sarkozy.slotReflectionPositive_slotProduct`);
* the low part's mixed `L³⁶` constant is a theorem (`|X₀|²`,
  `Sarkozy.mixedLpBound_finite_alphabet`), as are the constants at the finitely many
  scales below any threshold, so only an eventual *unit* mixed `L³⁶` bound for the tail
  factor remains a hypothesis — exactly the tail statement proved in the paper for its
  tail catalogue.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Sarkozy.Comparison

open FourierArithmetic

/-- **Conditional main theorem, product form.** -/
theorem PrefixedResidueModel.powerSavingBound_of_product
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀] [DecidableEq X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (μ₀ : FiniteLaw (Slot → X₀)) (μt : ∀ L, FiniteLaw (Slot → ResidueSpace (p L)))
    (hlaw : ∀ L, model.law L = μ₀.slotProduct (μt L))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmt : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (μt L))
    (hpt : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (μt L).weight))
    (htail : ∀ᶠ L in atTop, MixedLpBound (μt L) 36 1)
    {l : PrimitiveLedger} (hledger : l.Bounds)
    (e : ClosingEstimates (model.toFourierModel p X₀).energy 6 l.L₀ l.J l.W
      l.jointConstant) : PowerSavingBound := by
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp htail
  set C₀ : ℝ := (Fintype.card X₀ : ℝ) ^ ((Fintype.card Slot : ℝ) / 36) with hC₀def
  have hC₀ : 0 ≤ C₀ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set small : ℕ → ℝ := fun L =>
    (Fintype.card (X₀ × ResidueSpace (p L)) : ℝ) ^ ((Fintype.card Slot : ℝ) / 36)
  have hsmall0 (L : ℕ) : 0 ≤ small L := Real.rpow_nonneg (Nat.cast_nonneg _) _
  set C : ℝ := 1 + C₀ + ∑ L ∈ Finset.range L₀, small L with hCdef
  have hsum0 : 0 ≤ ∑ L ∈ Finset.range L₀, small L := Finset.sum_nonneg fun L _ => hsmall0 L
  have hC : 0 < C := by linarith
  have hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C := by
    intro L _
    rw [hlaw L]
    by_cases hLL : L₀ ≤ L
    · have hfix := mixedLpBound_finite_alphabet μ₀ (p := 36) (by norm_num)
      have hprod := hfix.slotProduct (hL₀ L hLL) zero_le_one (by norm_num)
      refine hprod.mono_constant ?_
      rw [mul_one]
      linarith
    · have hfin := mixedLpBound_finite_alphabet (μ₀.slotProduct (μt L)) (p := 36) (by norm_num)
      refine hfin.mono_constant ?_
      have hmem : L ∈ Finset.range L₀ := Finset.mem_range.mpr (lt_of_not_ge hLL)
      have hle : small L ≤ ∑ L ∈ Finset.range L₀, small L :=
        Finset.single_le_sum (fun L _ => hsmall0 L) hmem
      change small L ≤ C
      linarith
  have hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L) := by
    intro L hL
    rw [hlaw L]
    exact hm₀.slotProduct (hmt L hL)
  have hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight) := by
    intro L hL
    rw [hlaw L]
    exact slotReflectionPositive_slotProduct hp₀ (hpt L hL)
  exact PrefixedResidueModel.powerSavingBound_of_closingEstimates model ha hprefix hzero hm hp
    hC hmixed hledger e

end Sarkozy.Comparison

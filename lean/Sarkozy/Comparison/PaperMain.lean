module

public import Sarkozy.Functional.PrefixModel
public import Sarkozy.Comparison.Final
public import Sarkozy.Reflection.SlotProduct
public import Sarkozy.Moments.TensorMixed
public import Sarkozy.Moments.FiniteAlphabet
public import Sarkozy.TensorMarginals

/-!
# The conditional main theorem for the paper's functional

This module combines

* the paper's group and lift (`Sarkozy.Functional.paperPrefixedModel`, WP-FI): the clique
  prefix `X₀ = ∏ ℤ/m₀ᵢℤ` times the prime tail coordinates, the actual conductor, and the
  retained characters of total conductor at most `N^(1/20)`; its energy is the paper's
  functional `Y(L, A)` (`Sarkozy.Functional.paperPrefixedModel_energy`);
* the paper's product structure of the reference law, `μ = μ₀ ⊗ ⊗_{p tail} μ_p`, with
  scale-independent prime laws;
* the closing criterion of Theorem C with robust errors (`ClosingEstimates`) and the
  primitive closing ledger (`PrimitiveLedger`).

`paperMain_powerSavingBound` is the strongest conditional theorem of the project at the
time of writing. Its remaining hypotheses are listed in its docstring.

**Intended instantiation.** The prefix coordinates are all primes below `P₄ = 2^512`
(the clique primes `𝒫₁`, with moduli `p^(e_p)`, `e_p = 2·8192`, and the middle and upper
primes `𝒫₃`, with moduli `p`), a fixed finite family present at every scale; the tail
coordinates at scale `L` are the primes `P₄ ≤ p ≤ N^(1/20)`. Then `μ₀` is the product of
the clique laws and of the middle and upper *block* laws (no product structure over the
primes of a block is assumed: the paper's block references are mixtures of block
records), and the prime laws `μ_p` are the tail laws of `def:tail-law`, one atom per
prime. (`Sarkozy.Functional.paperPrefixedModel` allows any split; its docstring's split,
with `𝒫₃` in the tail, would not match the per-prime hypothesis below, because the
paper's middle and upper reference laws are not products over the primes of a block.)
-/

@[expose] public section

open Filter Finset
open scoped Topology

namespace Sarkozy.Comparison

open Functional FourierArithmetic

/-! ## Transfer of the closing estimates between equal functionals -/

theorem AtCounterexamples.transfer {Y Y' : ℕ → Finset ℤ → ℝ}
    (h : ∀ L A, Admissible (blockScale * L) A → Y L A = Y' L A)
    {Q : ℝ → ℕ → Finset ℤ → Prop} (hQ : AtCounterexamples Y fun L A => Q (Y L A) L A) :
    AtCounterexamples Y' fun L A => Q (Y' L A) L A := by
  filter_upwards [hQ] with L hL
  intro C hC hind A hA hcounter
  have hind' : ∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k := by
    intro k hk hkL A' hA'
    rw [h k A' hA']
    exact hind k hk hkL A' hA'
  have hc : C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A := by
    rw [h L A hA]
    exact hcounter
  have hq := hL C hC hind' A hA hc
  rwa [h L A hA] at hq

/-- The closing estimates only see the functional on admissible sets. -/
noncomputable def ClosingEstimates.transfer {Y Y' : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (h : ∀ L A, Admissible (blockScale * L) A → Y L A = Y' L A)
    (e : ClosingEstimates Y k L₀ J W H) : ClosingEstimates Y' k L₀ J W H where
  Yfs := e.Yfs
  Yν := e.Yν
  Jν := e.Jν
  eL := e.eL
  eR := e.eR
  VL := e.VL
  VR := e.VR
  εwrap := e.εwrap
  εenv := e.εenv
  εfirst := e.εfirst
  εjoint := e.εjoint
  cwrap := e.cwrap
  cenv := e.cenv
  cfirst := e.cfirst
  cjoint := e.cjoint
  εwrap_tendsto := e.εwrap_tendsto
  εenv_tendsto := e.εenv_tendsto
  εfirst_tendsto := e.εfirst_tendsto
  εjoint_tendsto := e.εjoint_tendsto
  cwrap_nonneg := e.cwrap_nonneg
  cenv_nonneg := e.cenv_nonneg
  cfirst_nonneg := e.cfirst_nonneg
  cjoint_nonneg := e.cjoint_nonneg
  wrap := AtCounterexamples.transfer h
    (Q := fun y L A => 2 ^ k * e.Yν L A ≤ e.Jν L A + (2 ^ k * W + e.εwrap L) * y +
      remainder e.cwrap L A) e.wrap
  frame := AtCounterexamples.transfer h
    (Q := fun _ L A => e.Jν L A ≤ e.Yν L A + ((e.VL L A - e.eL L A) + (e.VR L A - e.eR L A)) / 2)
    e.frame
  envelopeL := AtCounterexamples.transfer h
    (Q := fun y L A => e.VL L A ≤ (2 ^ k * J + e.εenv L) * y + remainder e.cenv L A) e.envelopeL
  envelopeR := AtCounterexamples.transfer h
    (Q := fun y L A => e.VR L A ≤ (2 ^ k * J + e.εenv L) * y + remainder e.cenv L A) e.envelopeR
  firstStage := AtCounterexamples.transfer h
    (Q := fun y L A => (1 - L₀ - e.εfirst L) * y - remainder e.cfirst L A ≤ e.Yfs L A)
    e.firstStage
  joint := AtCounterexamples.transfer h
    (Q := fun y L A => (2 ^ k - 1) * (e.Yfs L A - e.Yν L A) - (e.eL L A + e.eR L A) / 2 ≤
      (2 ^ k * H - 1 + e.εjoint L) * y + remainder e.cjoint L A) e.joint

/-! ## The paper's reference law -/

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The tail law at scale `L`: the tensor product of the prime laws. -/
noncomputable def primeTailLaw (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (L : ℕ) : FiniteLaw (Slot → ResidueSpace (p L)) :=
  FiniteLaw.tensor (fun j : J L => μp (p L j))

/-- The reference law `μ₀ ⊗ ⊗_{p tail} μ_p`. -/
noncomputable def paperLaw (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    FiniteLaw (Slot → ResidueSpace m₀ × ResidueSpace (p L)) :=
  μ₀.slotProduct (primeTailLaw p μp L)

/-- A mixed `L³⁶` constant for the tail laws, uniform in the scale. -/
theorem primeTailLaw_mixed (hinj : ∀ L, Function.Injective (p L))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (p₀ : ℕ)
    (hunit : ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    (hp : ∀ L j, (p L j).Prime) (L : ℕ) :
    MixedLpBound (primeTailLaw p μp L) 36 (((p₀ : ℝ) ^ 2) ^ p₀) := by
  classical
  set C : J L → ℝ := fun j =>
    if p₀ ≤ p L j then 1 else (Fintype.card (ZMod (p L j)) : ℝ) ^
      ((Fintype.card Slot : ℝ) / 36) with hCdef
  have hC0 : ∀ j, 0 ≤ C j := by
    intro j
    simp only [hCdef]
    split_ifs
    · norm_num
    · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hbound : ∀ j, MixedLpBound (μp (p L j)) 36 (C j) := by
    intro j
    simp only [hCdef]
    split_ifs with hj
    · exact hunit _ (hp L j) hj
    · exact mixedLpBound_finite_alphabet _ (by norm_num)
  have ht := MixedLpBound.tensor (fun j : J L => μp (p L j)) (by norm_num) C hC0 hbound
  refine ht.mono_constant ?_
  have hsmall : ∀ j, C j ≤ if p L j < p₀ then (p₀ : ℝ) ^ 2 else 1 := by
    intro j
    simp only [hCdef]
    split_ifs with h1 h2 h2
    · omega
    · exact le_rfl
    · rw [ZMod.card, card_slot]
      have hq : (p L j : ℝ) ≤ p₀ := by exact_mod_cast h2.le
      rw [show ((72 : ℕ) : ℝ) / 36 = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      exact pow_le_pow_left₀ (Nat.cast_nonneg _) hq 2
    · omega
  calc ∏ j, C j ≤ ∏ j, (if p L j < p₀ then (p₀ : ℝ) ^ 2 else 1) :=
        prod_le_prod₀ (fun j _ => hC0 j) (fun j _ => hsmall j)
    _ = ((p₀ : ℝ) ^ 2) ^ (univ.filter fun j : J L => p L j < p₀).card := by
        rw [prod_ite, prod_const, prod_const_one, mul_one]
    _ ≤ ((p₀ : ℝ) ^ 2) ^ p₀ := by
        rcases Nat.eq_zero_or_pos p₀ with hp0 | hp0
        · subst hp0
          have hempty : (univ.filter fun j : J L => p L j < 0) = ∅ := by
            ext j
            simp
          rw [hempty]
          simp
        · have hp1 : (1 : ℝ) ≤ (p₀ : ℝ) ^ 2 := by
            have : (1 : ℝ) ≤ p₀ := by exact_mod_cast hp0
            nlinarith
          apply pow_le_pow_right₀ hp1
          have hinjOn : Set.InjOn (p L) ↑(univ.filter fun j : J L => p L j < p₀) :=
            fun i _ j _ h => hinj L h
          have hmaps : ∀ j ∈ (univ.filter fun j : J L => p L j < p₀), p L j ∈ range p₀ :=
            fun j hj => mem_range.mpr (mem_filter.mp hj).2
          have h := card_le_card_of_injOn _ hmaps hinjOn
          simpa using h

/-- **The conditional main theorem for the paper's functional.**

For the paper's group `G_N` (clique prefix `∏ ℤ/m₀ᵢℤ` times distinct tail primes) and lift
(total conductor at most `N^(1/20)`), and the reference law `μ₀ ⊗ ⊗_{p tail} μ_p`, the
following hypotheses imply `s(N) ≤ C N^(1-ε)`, `ε = 1814179/141970826000`:

* the low law `μ₀` and every prime law `μ_p` have uniform one-slot marginals and are
  reflection positive at the seven sorting cuts;
* the prime laws have unit mixed `L³⁶` norm for all primes above some threshold;
* the fourteen primitive totals of the final closing ledger (`PrimitiveLedger.Bounds`);
* the five robust closing estimates of Theorem C for the paper's functional `Y`
  (`ClosingEstimates`), with the paper's six queries and joint constant.

The lift-moment estimate, the global second-density bound, the arithmetic conditions of
the lift, the reflection lower bound `α⁷² ≤ Y`, finite initialization, absorption of the
density-linear errors, the scalar induction, the evaluation of the closing number and the
passage to cardinalities are proved. -/
theorem paperMain_powerSavingBound (hp : ∀ L j, (p L j).Prime)
    (hinj : ∀ L, Function.Injective (p L))
    (μ₀ : FiniteLaw (Slot → ResidueSpace m₀))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hm₀ : HasUniformMarginals μ₀) (hp₀ : SlotReflectionPositive (signedIntegral μ₀.weight))
    (hmp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (μp q) 36 1)
    {l : PrimitiveLedger} (hledger : l.Bounds)
    (e : ClosingEstimates (prefixedFunctional m₀ p (paperLaw m₀ p μ₀ μp)) 6 l.L₀ l.J l.W
      l.jointConstant) :
    PowerSavingBound := by
  classical
  obtain ⟨p₀, hp₀unit⟩ := hunit
  set law := paperLaw m₀ p μ₀ μp
  set model := paperPrefixedModel m₀ p law
  -- The estimates for the paper's functional are estimates for the model's energy.
  have e' : ClosingEstimates model.toFourierModel.energy 6 l.L₀ l.J l.W l.jointConstant :=
    e.transfer fun L A hA => (paperPrefixedModel_energy m₀ p hp law L hA.1).symm
  set Ct : ℝ := ((p₀ : ℝ) ^ 2) ^ p₀
  set C₀ : ℝ := (Fintype.card (ResidueSpace m₀) : ℝ) ^ ((Fintype.card Slot : ℝ) / 36)
  have hC₀ : 0 ≤ C₀ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCt : 0 ≤ Ct := pow_nonneg (sq_nonneg _) _
  have hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 (1 + C₀ * Ct) := by
    intro L _
    have h := (mixedLpBound_finite_alphabet μ₀ (p := 36) (by norm_num)).slotProduct
      (primeTailLaw_mixed p hinj μp p₀ hp₀unit hp L) hCt (by norm_num)
    exact h.mono_constant (by linarith)
  have hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L) := by
    intro L _
    exact hm₀.slotProduct (tensor_uniform_marginals _ fun j => hmp _ (hp L j))
  have hrp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight) := by
    intro L _
    exact slotReflectionPositive_slotProduct hp₀ (tensor_slot_reflection_positive _ fun j =>
      hpp _ (hp L j))
  have hprefix : (1 : AddChar (ResidueSpace m₀) ℂ) ∈ model.prefixSet :=
    mem_image.mpr ⟨0, mem_univ _, productCharacter_zero m₀⟩
  have hzero : ∀ L : ℕ, 1 ≤ L → (∅ : Finset (J L)) ∈ model.supports L 1 := by
    intro L hL
    have hN : 1 ≤ blockScale * L :=
      Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by norm_num [blockScale]) (by omega))
    simp only [model, paperPrefixedModel, tailSupports, mem_filter, mem_univ, true_and,
      prod_empty, mul_one]
    have h1 : prefixLabel m₀ 1 = 0 := by
      rw [← productCharacter_zero m₀, prefixLabel_productCharacter]
    rw [h1, conductor_zero, Nat.cast_one]
    exact one_le_paperCutoff hN
  exact PrefixedResidueModel.powerSavingBound_of_closingEstimates model
    (paperPrefixedModel_arithmetic m₀ p hp hinj law) hprefix hzero hm hrp (by positivity) hmixed
    hledger e'

end Sarkozy.Comparison

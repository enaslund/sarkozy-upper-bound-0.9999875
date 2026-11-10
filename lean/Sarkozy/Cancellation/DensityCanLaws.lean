module

public import Sarkozy.Cancellation.DensityCan
public import Sarkozy.Cancellation.CondExpectation

@[expose] public section

/-!
# `lem:record:density-can` from the pair laws

`density_can_of_pair_laws` is `density_can` with Step 1 discharged by WP-S's
`pair_support_decay` (through `step1_pair_decomposition`), and with Step 1's `∫‖E_U φ_x‖₂²`
identified with the pair averages of Step 3 (`expect_condProjOn_sq_eq`). Its data:

* the prefix law `μ` on `X`;
* the tail primes `q_j ≥ 64` with the laws `κ_j` of hypothesis (a): pair alphabet
  `PairAlphabet q j = Ω_{q_j}`, other-slot alphabet `B j`, uniform pair marginal, contraction by
  `q_j^{-γ}`;
* for every prefix label `x`, the pair factors `F₁(x, ·)`, `F₂(x, ·)` (`G_u`, `G_v`) on the tail
  group and the product `W(x, ·)` of the other factors. The integral is
  `I = ∫_x ∫ φ_x W_x`, `φ_x(a) = F₁(x, x(a)) F₂(x, y(a))`.

Its hypotheses:

* Step 2: the two moment bounds (`step2_holder_moments` supplies them from
  `lem:record:lift-moments`(c));
* Step 3: for every `U` with `q_U ≤ T₀`, a fibre modulus `D` and classes `𝔞₁, 𝔞₂` on the labels
  `ω = (x, a)` with the conditions of `LowPairInput`; the pointwise conditions (square class, fibre
  formula) are asked only `ϱ_pre`-almost surely, for `μ(x) ≠ 0`, as in (b) of the lemma. The inputs `g_i(ω)` are now determined: `F_i(x, ·)` with the
  coordinates of `U` frozen at `a` (`fibre_formula_of_input` supplies their fibre formula).

New material for this paper.
-/

namespace Sarkozy.Cancellation

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset Complex
open scoped BigOperators ComplexConjugate Matrix
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Mixing

/-- **`lem:record:density-can` from the pair laws.** See the module docstring. -/
theorem density_can_of_pair_laws :
    ∃ Cker : ℝ, 0 < Cker ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : ℝ, 1 ≤ L → L ≤ N →
      ∀ (K₀ : Type) [Fintype K₀] [DecidableEq K₀] (q : K₀ → ℕ) [∀ j, NeZero (q j)]
        [∀ j, Fact (q j).Prime], Function.Injective q → (∀ j, 64 ≤ q j) →
      ∀ (X : Type) [Fintype X] (μ : FiniteLaw X) (B : K₀ → Type) [∀ j, Fintype (B j)]
        (κ : ∀ j, FiniteLaw (PairAlphabet q j × B j)),
        (∀ j a, srcWeight (κ j) a = (Fintype.card (PairAlphabet q j) : ℝ)⁻¹) →
        (∀ j, ContractsMeanZero (κ j) ((q j : ℝ) ^ (-stageGamma))) →
      ∀ (F₁ F₂ : X → ResidueSpace q → ℝ) (W : X → (∀ j, B j) → ℝ),
      ∀ (A : Finset ℤ), Admissible N A →
      ∀ (u₁ v₁ u₂ v₂ : ℤ), v₁ < u₂ → u₂ ≤ v₂ → ((v₂ - u₂ + 1 : ℤ) : ℝ) ≤ L →
      ∀ (α C₂ Kc M₀ Cε : ℝ), 0 ≤ α → 0 ≤ C₂ → 0 ≤ Kc → 0 ≤ M₀ → 0 ≤ Cε → (N : ℝ) / L ≤ Kc →
      -- Step 2: the moments
      (μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b * W x b ^ 2) ≤
        C₂ * (N : ℝ) ^ (72 * stageDelta) * α →
      (μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
          (fun a => (F₁ x (pairsToVectors q a).1 * F₂ x (pairsToVectors q a).2) ^ 2)) ≤
        C₂ * (N : ℝ) ^ (72 * stageDelta) * α →
      -- Step 3: the fibre data at every low pair support
      (∀ U : K₀ → Bool, supportConductor q U ≤ (N : ℝ) ^ stageTan →
        ∃ (D : ℕ) (𝔞₁ 𝔞₂ : X × (∀ j, PairAlphabet q j) → ℤ),
          (D : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) ∧ (D : ℝ) ≤ L ∧
          (∀ k : {j // U j = false}, Nat.Coprime (q k.1) D) ∧
          (∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → ¬ ℓ ∣ D →
            ∃ k : {j // U j = false}, q k.1 = ℓ) ∧
          (∀ ω : X × (∀ j, PairAlphabet q j), μ.weight ω.1 ≠ 0 →
            Kernel.IsNonvanishingSquareClass D (𝔞₂ ω - 𝔞₁ ω)) ∧
          (∀ ω : X × (∀ j, PairAlphabet q j), μ.weight ω.1 ≠ 0 →
            ∀ a : ResidueSpace (fun k : {j // U j = false} => q k.1),
            (supportDenominator (fun k : {j // U j = false} => q k.1) a : ℝ) ≤
              (N : ℝ) ^ (1 / 40 : ℝ) →
            groupCoeff (fun k : {j // U j = false} => q k.1)
                (fun x' => (F₁ ω.1 (mergeFree U (pairsToVectors q ω.2).1 x') : ℂ)) a =
              (D : ℂ) * (L : ℂ)⁻¹ * ∑ n ∈ Kernel.classPart A u₁ v₁ (𝔞₁ ω) D,
                conj (prodChar (fun k : {j // U j = false} => q k.1) a
                  (integerResidue (fun k : {j // U j = false} => q k.1) n))) ∧
          (∀ ω : X × (∀ j, PairAlphabet q j), μ.weight ω.1 ≠ 0 →
            ∀ a : ResidueSpace (fun k : {j // U j = false} => q k.1),
            (supportDenominator (fun k : {j // U j = false} => q k.1) a : ℝ) ≤
              (N : ℝ) ^ (1 / 40 : ℝ) →
            groupCoeff (fun k : {j // U j = false} => q k.1)
                (fun y' => (F₂ ω.1 (mergeFree U (pairsToVectors q ω.2).2 y') : ℂ)) a =
              (D : ℂ) * (L : ℂ)⁻¹ * ∑ n ∈ Kernel.classPart A u₂ v₂ (𝔞₂ ω) D,
                conj (prodChar (fun k : {j // U j = false} => q k.1) a
                  (integerResidue (fun k : {j // U j = false} => q k.1) n))) ∧
          ∑ ω : X × (∀ j, PairAlphabet q j),
              (μ.weight ω.1 * (Fintype.card (∀ j, PairAlphabet q j) : ℝ)⁻¹) *
                ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card) ≤ M₀ * Kc * α ∧
          ∑ ω : X × (∀ j, PairAlphabet q j),
              (μ.weight ω.1 * (Fintype.card (∀ j, PairAlphabet q j) : ℝ)⁻¹) *
                ((𝔼 z, ‖(F₁ ω.1 (mergeFree U (pairsToVectors q ω.2).1 z) : ℂ)‖ ^ 2) *
                  (𝔼 z, ‖(F₂ ω.1 (mergeFree U (pairsToVectors q ω.2).2 z) : ℂ)‖ ^ 2)) ≤
            Cε * (N : ℝ) ^ (72 * stageDelta) * α) →
      let I := μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b *
        condOp (prodJoint κ) (fun a => F₁ x (pairsToVectors q a).1 * F₂ x (pairsToVectors q a).2)
          b * W x b
      let Ccan := Real.sqrt C₂ * (Real.sqrt C₂ + Real.sqrt ((4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) *
            (1 + 1 / (1 - 2 * stageGamma))))
      |I| ≤ Ccan * (N : ℝ) ^ (72 * stageDelta) * α *
          ((N : ℝ) ^ (-(stageGamma * stageTan)) +
            (N : ℝ) ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma))) ∧
        |I| ≤ 2 * Ccan * L ^ (-stageSigma) * α := by
  obtain ⟨Cker, hCker, N₀, hmain⟩ := density_can
  refine ⟨Cker, hCker, N₀, ?_⟩
  intro N hN L hL hLN K₀ _ _ q _ _ hqinj h64 X _ μ B _ κ hsrc hmix F₁ F₂ W A hA u₁ v₁ u₂ v₂
    huv huv₂ hlen α C₂ Kc M₀ Cε hα hC₂ hKc hM₀ hCε hNL hW hφ h3 I Ccan
  have hNr : (1 : ℝ) ≤ N := hL.trans hLN
  have hT₀ : (1 : ℝ) ≤ (N : ℝ) ^ stageTan :=
    Real.one_le_rpow hNr (by unfold stageTan; norm_num)
  have hγ : 0 ≤ stageGamma := by unfold stageGamma; norm_num
  have hq0 : ∀ j, 0 < q j := fun j => (Fact.out : (q j).Prime).pos
  set φ : X → (∀ j, PairAlphabet q j) → ℝ :=
    fun x a => F₁ x (pairsToVectors q a).1 * F₂ x (pairsToVectors q a).2 with hφdef
  -- Step 1 from WP-S's lemma
  have hstep1 := step1_pair_decomposition μ κ hsrc q hq0 hγ hmix hT₀ φ W
  have hφ0 : 0 ≤ μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
      (fun a => φ x a ^ 2) :=
    μ.expect_nonneg (fun x => (FiniteLaw.uniform _).expect_nonneg (fun a => sq_nonneg _))
  exact hmain N hN L hL hLN K₀ q (fun j => Fact.out) hqinj A hA u₁ v₁ u₂ v₂ huv huv₂ hlen
    I _ _ α C₂ Kc M₀ Cε
    (fun U => μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
      (fun a => (condProjOn (PairAlphabet q) U *ᵥ φ x) a ^ 2))
    hα hC₂ hKc hM₀ hCε hNL hstep1 hW hφ0 hφ (by
      intro U hU
      obtain ⟨D, 𝔞₁, 𝔞₂, hD, hDL, hcopD, hcover, hsq, hg₁, hg₂, hE₁, hEm⟩ := h3 U hU
      set S := (univ : Finset (X × (∀ j, PairAlphabet q j))).filter (fun ω => μ.weight ω.1 ≠ 0)
        with hS
      have hsupp : ∀ g : X × (∀ j, PairAlphabet q j) → ℝ,
          ∑ ω ∈ S, (μ.weight ω.1 * (Fintype.card (∀ j, PairAlphabet q j) : ℝ)⁻¹) * g ω =
            ∑ ω, (μ.weight ω.1 * (Fintype.card (∀ j, PairAlphabet q j) : ℝ)⁻¹) * g ω := by
        intro g
        apply sum_filter_of_ne
        intro ω _ hne h0
        exact hne (by rw [h0, zero_mul, zero_mul])
      refine ⟨{j // U j = false}, inferInstance, inferInstance, fun k => q k.1, inferInstance,
        inferInstance, D, X × (∀ j, PairAlphabet q j), S,
        fun ω => μ.weight ω.1 * (Fintype.card (∀ j, PairAlphabet q j) : ℝ)⁻¹, 𝔞₁, 𝔞₂,
        fun ω x' => (F₁ ω.1 (mergeFree U (pairsToVectors q ω.2).1 x') : ℂ),
        fun ω y' => (F₂ ω.1 (mergeFree U (pairsToVectors q ω.2).2 y') : ℂ),
        fun k₁ k₂ h => Subtype.ext (hqinj h), fun k => h64 k.1, hD, hcopD, hcover,
        fun ω _ => mul_nonneg (μ.nonneg _) (by positivity),
        fun ω hω => hsq ω (mem_filter.mp hω).2,
        fun ω hω => hg₁ ω (mem_filter.mp hω).2, fun ω hω => hg₂ ω (mem_filter.mp hω).2, hDL,
        by rw [hsupp]; exact hE₁, by rw [hsupp]; exact hEm, ?_⟩
      rw [hsupp]
      exact expect_condProjOn_sq_eq q μ U F₁ F₂)

end Sarkozy.Cancellation

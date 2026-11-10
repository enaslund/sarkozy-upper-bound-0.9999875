module

public import Sarkozy.Cancellation.LowPair
public import Sarkozy.Cancellation.Assembly
public import Sarkozy.Cancellation.ScaleInputs

@[expose] public section

/-!
# `lem:record:density-can`: accepted-pair cancellation with a density factor

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can` (line 815; proof to line 971):
`|∫ ∏_w G_w dϱ| ≤ C_can N^{72δ} α (N^{-γ t_an} + N^{-1/120 + t_an(1/2-γ)}) ≤ 2 C_can 𝔏^{-σ} α`.

`density_can` proves the lemma from the inputs of its Steps 1–2 and the per-support data of
Step 3, with Steps 3 and 4 proved:

* **Step 1** (pair decomposition: `lem:tr:pairsupport` at the tail factors for each prefix label,
  integrated over the prefix labels with Cauchy–Schwarz) is the hypothesis `hstep1`, in the form
  of WP-S's `Sarkozy.Mixing.pair_support_decay` integrated over `x`
  (`step1_integrate` below does the integration);
* **Step 2** (moments: Hölder with 70 factors and `lem:record:lift-moments`(c)) is the pair of
  hypotheses `hW`, `hφ`;
* **Step 3** is `step3_low_pair_support` (`Sarkozy.Cancellation.LowPair`), applied to the data
  `LowPairInput` at every pair support `U` with `q_U ≤ T₀`; its inputs are the fibre formula of
  `lem:record:fibre-scale`(a) on `X_{𝒮'}`, the bounds `D ≤ min(N^{1/20}, 𝔏)` on the fibre modulus
  (`fibreModulus_le_of_scaleConditions` derives them from WP-FI's `ScaleConditionsAt`), the
  average fibre density `E α_{f,1} ≤ M₀ K α` and the fourth-moment bound
  `E(‖g₁‖²‖g₂‖²) ≤ C_ε N^ε α`; `α_{f,2} ≤ 2` is proved (`fibreDensity_le_two`);
* **Step 4** is `sum_supportConductor_rpow_le` (`Sarkozy.Cancellation.Summation`).

The pair supports are indexed by `l : K₀ → Bool` over the tail primes `q : K₀ → ℕ`, with
`q_U = ∏_j (if l j then q_j else 1)` (WP-S's `supportConductor`, written out). The constant is
`C_can = √C₂ (√C₂ + √(C₃ (1 + 1/(1-2γ))))`, `C₃ = 4 C² K³ M₀ + 2 C_ε`, with `C` the constant of
`prop:record:kernel20`(iii) at the triple of `cor:kernel20`. Every hypothesis is per instance and
the constants are parameters, so the bound is uniform in `b`, `s`, `r` and the other indices.
-/

namespace Sarkozy.Cancellation

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional

/-- **The data of Step 3 at one pair support `U`** (`lem:record:density-can`), for the value
`e = ∫ ‖E_U φ_x‖₂² dϱ_pre(x)`: the tail primes outside `U` (`p_j ≥ 64`, coprime to the fibre
modulus `D ≤ N^{1/20}`, containing every prime `ℓ ≤ N^{1/40}` with `ℓ ∤ D`), the labels
`ω = (x, y)` with their weight, the classes `𝔞₁(ω), 𝔞₂(ω)` modulo `D` with `𝔞₂ − 𝔞₁` a
nonvanishing square class, the two pair inputs `g₁(ω), g₂(ω)` on `X_{𝒮'}` with the fibre formula
of `lem:record:fibre-scale`(a), `D ≤ 𝔏`, the average fibre density, the moment bound, and
`e = ∑_ω w(ω) |∫ g₁(ω) ⊗ g₂(ω) dπ|²`. -/
def LowPairInput (N : ℕ) (A : Finset ℤ) (u₁ v₁ u₂ v₂ : ℤ) (L Kc M₀ α Cε ε e : ℝ) : Prop :=
  ∃ (K : Type) (_ : Fintype K) (_ : DecidableEq K) (p : K → ℕ) (_ : ∀ j, NeZero (p j))
    (_ : ∀ j, Fact (p j).Prime) (D : ℕ) (Ω : Type) (s : Finset Ω) (w : Ω → ℝ)
    (𝔞₁ 𝔞₂ : Ω → ℤ) (g₁ g₂ : Ω → ResidueSpace p → ℂ),
    Function.Injective p ∧ (∀ j, 64 ≤ p j) ∧
    (D : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) ∧ (∀ j, Nat.Coprime (p j) D) ∧
    (∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → ¬ ℓ ∣ D → ∃ j, p j = ℓ) ∧
    (∀ ω ∈ s, 0 ≤ w ω) ∧
    (∀ ω ∈ s, Kernel.IsNonvanishingSquareClass D (𝔞₂ ω - 𝔞₁ ω)) ∧
    (∀ ω ∈ s, ∀ a, (supportDenominator p a : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) →
      groupCoeff p (g₁ ω) a = (D : ℂ) * (L : ℂ)⁻¹ *
        ∑ n ∈ Kernel.classPart A u₁ v₁ (𝔞₁ ω) D, conj (prodChar p a (integerResidue p n))) ∧
    (∀ ω ∈ s, ∀ a, (supportDenominator p a : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) →
      groupCoeff p (g₂ ω) a = (D : ℂ) * (L : ℂ)⁻¹ *
        ∑ n ∈ Kernel.classPart A u₂ v₂ (𝔞₂ ω) D, conj (prodChar p a (integerResidue p n))) ∧
    (D : ℝ) ≤ L ∧
    ∑ ω ∈ s, w ω * ((D : ℝ) / L * (Kernel.classPart A u₁ v₁ (𝔞₁ ω) D).card) ≤ M₀ * Kc * α ∧
    ∑ ω ∈ s, w ω * ((𝔼 z, ‖g₁ ω z‖ ^ 2) * (𝔼 z, ‖g₂ ω z‖ ^ 2)) ≤ Cε * (N : ℝ) ^ ε * α ∧
    e = ∑ ω ∈ s, w ω * ‖pairAvg p (g₁ ω) (g₂ ω)‖ ^ 2

/-- **`lem:record:density-can`** (accepted-pair cancellation with a density factor), with
Steps 3–4 proved and the inputs of Steps 1–2 as hypotheses (see the module docstring). With
`γ = 255/1024`, `t_an = 1/60`, `σ = 1/825`, `δ = 10^{-10}`, `T₀ = N^{t_an}`, `H = N^{1/40}`:
`|I| ≤ C_can N^{72δ} α (N^{-γ t_an} + N^{-1/120 + t_an(1/2-γ)}) ≤ 2 C_can 𝔏^{-σ} α`. -/
theorem density_can :
    ∃ Cker : ℝ, 0 < Cker ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∀ L : ℝ, 1 ≤ L → L ≤ N →
      ∀ (K₀ : Type) [Fintype K₀] [DecidableEq K₀] (q : K₀ → ℕ), (∀ j, (q j).Prime) →
        Function.Injective q →
      ∀ (A : Finset ℤ), Admissible N A →
      ∀ (u₁ v₁ u₂ v₂ : ℤ), v₁ < u₂ → u₂ ≤ v₂ → ((v₂ - u₂ + 1 : ℤ) : ℝ) ≤ L →
      ∀ (I Wsq φsq α C₂ Kc M₀ Cε : ℝ) (e : (K₀ → Bool) → ℝ),
      0 ≤ α → 0 ≤ C₂ → 0 ≤ Kc → 0 ≤ M₀ → 0 ≤ Cε → (N : ℝ) / L ≤ Kc →
      -- Step 1: the pair decomposition
      I ^ 2 ≤ Wsq * (((N : ℝ) ^ stageTan) ^ (-2 * stageGamma) * φsq +
        ∑ l ∈ univ.filter (fun l : K₀ → Bool =>
            (∏ j, (if l j then (q j : ℝ) else 1)) ≤ (N : ℝ) ^ stageTan),
          (∏ j, (if l j then (q j : ℝ) else 1)) ^ (-2 * stageGamma) * e l) →
      -- Step 2: the moments
      Wsq ≤ C₂ * (N : ℝ) ^ (72 * stageDelta) * α →
      0 ≤ φsq → φsq ≤ C₂ * (N : ℝ) ^ (72 * stageDelta) * α →
      -- Step 3: the data at every low pair support
      (∀ l : K₀ → Bool, (∏ j, (if l j then (q j : ℝ) else 1)) ≤ (N : ℝ) ^ stageTan →
        LowPairInput N A u₁ v₁ u₂ v₂ L Kc M₀ α Cε (72 * stageDelta) (e l)) →
      |I| ≤ Real.sqrt C₂ * (Real.sqrt C₂ + Real.sqrt ((4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) *
            (1 + 1 / (1 - 2 * stageGamma)))) * (N : ℝ) ^ (72 * stageDelta) * α *
          ((N : ℝ) ^ (-(stageGamma * stageTan)) +
            (N : ℝ) ^ (-(1 : ℝ) / 120 + stageTan * (1 / 2 - stageGamma))) ∧
        |I| ≤ 2 * (Real.sqrt C₂ * (Real.sqrt C₂ + Real.sqrt ((4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) *
            (1 + 1 / (1 - 2 * stageGamma))))) * L ^ (-stageSigma) * α := by
  obtain ⟨Cker, hCker, N₀, hstep3⟩ := step3_low_pair_support.{0, 0}
  refine ⟨Cker, hCker, max N₀ 1, ?_⟩
  intro N hN L hL hLN K₀ _ _ q hqp hqinj A hA u₁ v₁ u₂ v₂ huv huv₂ hlen I Wsq φsq α C₂ Kc M₀
    Cε e hα hC₂ hKc hM₀ hCε hNL hstep1 hW hφ0 hφ h3
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hL0 : 0 < L := by linarith
  have hδ : 0 ≤ 72 * stageDelta := by unfold stageDelta; norm_num
  have hT₀ : (1 : ℝ) ≤ (N : ℝ) ^ stageTan :=
    Real.one_le_rpow hNr (by unfold stageTan; norm_num)
  set 𝒰 := univ.filter (fun l : K₀ → Bool =>
    (∏ j, (if l j then (q j : ℝ) else 1)) ≤ (N : ℝ) ^ stageTan) with h𝒰
  -- Step 3 at every low pair support
  have hdata : ∀ l ∈ 𝒰, 0 ≤ e l ∧
      e l ≤ (4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) *
        (N : ℝ) ^ (-(1 : ℝ) / 60 + 72 * stageDelta) * α := by
    intro l hl
    obtain ⟨K, _, _, p, _, _, D, Ω, s, w, 𝔞₁, 𝔞₂, g₁, g₂, hinj, h64, hD, hcopD, hcover, hw, hsq,
      hg₁, hg₂, hDL, hE₁, hEm, he⟩ := h3 l (mem_filter.mp hl).2
    have haf₂ : ∀ ω ∈ s, (D : ℝ) / L * (Kernel.classPart A u₂ v₂ (𝔞₂ ω) D).card ≤ 2 := by
      intro ω hω
      have hD0 : 0 < D := by
        rcases Nat.eq_zero_or_pos D with h | h
        · exfalso
          have h3' := (hsq ω hω).1
          rw [h, Nat.factorization_zero] at h3'
          simp at h3'
        · exact h
      exact fibreDensity_le_two A huv₂ (𝔞₂ ω) hD0 hlen hDL
    refine ⟨?_, ?_⟩
    · rw [he]
      exact sum_nonneg (fun ω hω => mul_nonneg (hw ω hω) (sq_nonneg _))
    · rw [he]
      exact (hstep3 N (le_trans (le_max_left _ _) hN) K p hinj h64 D hD hcopD hcover A hA
        u₁ v₁ u₂ v₂ huv L hL0 Ω s w hw 𝔞₁ 𝔞₂ g₁ g₂ hsq hg₁ hg₂ Kc M₀ α Cε (72 * stageDelta) hNL
        haf₂ hE₁ hEm).trans (step3_rhs_le hN1 hKc hM₀ hα hδ)
  -- Step 4
  have hγ0 : 0 < stageGamma := by unfold stageGamma; norm_num
  have hγ1 : stageGamma < 1 / 2 := by unfold stageGamma; norm_num
  have hsum := sum_supportConductor_rpow_le q hqp hqinj hγ0 hγ1 hT₀
  have hq : ∀ l ∈ 𝒰, 0 < ∏ j, (if l j then (q j : ℝ) else 1) := by
    intro l _
    apply prod_pos
    intro j _
    split_ifs
    · exact_mod_cast (hqp j).pos
    · exact one_pos
  have hC₃ : 0 ≤ 4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε := by positivity
  exact density_can_of_inputs 𝒰 (fun l => ∏ j, (if l j then (q j : ℝ) else 1)) e I Wsq φsq α
    (N : ℝ) L C₂ (4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) hL hLN hα hC₂ hC₃ hstep1 hW hφ0 hφ hq
    (fun l hl => (hdata l hl).1) (fun l hl => (hdata l hl).2) hsum

end Sarkozy.Cancellation

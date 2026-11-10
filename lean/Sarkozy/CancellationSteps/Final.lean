module

public import Sarkozy.CancellationSteps.Structural

/-!
# `DensityCancellation` from Step 2 and the three analytic clauses of Step 3

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, over WP-FI's
`TheoremC.DensityCancellation`. This is `densityCancellation_of_rest` with the structural clauses
of `FibreRest` discharged (`Structural.lean`): the size of `D` and `H D_E ≤ Q`
(`lem:scale-conditions`(vi), for `L` large; the threshold is
`(K M₀ ∏ m₀ ∏_{n ≤ P₅} n)^{120}`), the coprimality of `D` with the free tail primes, and the
coverage of the small primes (`lem:scale-conditions`(v)) from the elementary hypothesis `hcover`.

`densityCancellation_of_core` takes, besides elementary facts about the data:
* Step 2, `LiftMoments` (`lem:record:lift-moments`(c)) at the encoded data;
* `FibreCore` at every low support: for the fibre modulus `D = M₀ ∏_{c ∈ E} m_c` and every choice
  of the fibre classes `𝔞₁, 𝔞₂`,
  - `𝔞₂ − 𝔞₁` is a nonvanishing square class mod `D`, `μ`-a.s. (the local conditions (b));
  - the uniformity of `𝔞₁`: `E (D/L)|A ∩ I_b ∩ (𝔞₁ + Dℤ)| ≤ M₀' K α`;
  - the `L²` bound `E(‖g₁‖² ‖g₂‖²) ≤ C_ε N^{72δ} α`.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The analytic clauses of Step 3 at a low support `U`**, for the encoded data: for the fibre
modulus `D = M ∏_{c ∈ E} m_c` and every choice of fibre classes `𝔞₁`, `𝔞₂` of the frozen labels of
`u` (residue `s`) and `v` (residue `s'`): `𝔞₂ − 𝔞₁` is a nonvanishing square class mod `D`
`μ`-a.s. (the local conditions of (b)), the uniformity of `𝔞₁`, and the `L²` bound. -/
def FibreCore (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {M : ℕ} (s s' : ZMod M) (u v : Slot)
    (μ : FiniteLaw (LowLabels m₀ p L P5))
    (F₁ F₂ : LowLabels m₀ p L P5 → ResidueSpace (tailQ p L P5) → ℝ) (A : Finset ℤ) (u₁ v₁ : ℤ)
    (N : ℕ) (Lr Kc M₀ Cε α : ℝ) : Prop :=
  ∀ 𝔞₁ 𝔞₂ : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℤ,
    (∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1) s n ↔
        n ≡ 𝔞₁ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)]) →
    (∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 v ω.1 (pairsToVectors (tailQ p L P5) ω.2).2) s' n ↔
        n ≡ 𝔞₂ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)]) →
    (∀ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k), μ.weight ω.1 ≠ 0 →
      Kernel.IsNonvanishingSquareClass (fibreModulus m₀ p L P5 U M) (𝔞₂ ω - 𝔞₁ ω)) ∧
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        (μ.weight ω.1 * (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
          (((fibreModulus m₀ p L P5 U M : ℕ) : ℝ) / Lr *
            (Kernel.classPart A u₁ v₁ (𝔞₁ ω) (fibreModulus m₀ p L P5 U M)).card) ≤
      M₀ * Kc * α ∧
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        (μ.weight ω.1 * (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
          ((𝔼 z, ‖(F₁ ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 z) : ℂ)‖ ^ 2) *
            (𝔼 z, ‖(F₂ ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 z) : ℂ)‖ ^ 2)) ≤
      Cε * (N : ℝ) ^ (72 * stageDelta) * α

lemma supportConductor_nonneg {K : Type*} [Fintype K] (q : K → ℕ) (U : K → Bool) :
    0 ≤ supportConductor q U := by
  unfold supportConductor
  exact prod_nonneg fun j _ => by split_ifs <;> positivity

section Final

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from Step 2 and the analytic
clauses of Step 3.** Hypotheses:
* distinct tail primes and `P₅ ≥ 64`;
* elementary facts about the data: `M₀ = modulus pr h` is coprime to every atom modulus, the atom
  moduli are pairwise coprime, and every prime `ℓ ≤ N^{1/40}` divides `M₀` or a prefix modulus
  or is a tail prime (`hcover`; the paper's `lem:scale-conditions`(v) and the choice of the
  atoms);
* for every query at every scale `L ≥ L₁`: `LiftMoments` (`lem:record:lift-moments`(c)) at the
  encoded data, and `FibreCore` (the square class from (b), the uniformity of `𝔞₁`, the `L²`
  bound) at every low support `q_U ≤ N^{t_an}`, for the interval `I_b = [(c − 1)L + 1, cL]`,
  `c = b.val`.

The intervals, the fibre formulas, the size of `D`, `H D_E ≤ Q`, the coprimality of `D` with the
free tail primes and the coverage of the small primes are proved. -/
theorem densityCancellation_of_core (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ M₀ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hM₀ : 0 ≤ M₀) (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ)
    (hSteps : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      ∀ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
      (∀ b, HasUniformMarginals (ϱ b)) → ∀ (u v : Slot) (huv : u ≠ v),
      ∀ ha : (∀ j : J L, P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (some j)) u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (some j)) {u, v}),
      (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ p pp ep L b (z u) (z v)) →
      ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
      IsNonvanishingSquareClass (modulus pr h) r →
      ∀ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
      G u = indexInputAt m₀ p pr h L A (bI, s) →
      G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) →
      (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) →
        LiftMoments (tailQ p L P5)
          (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
          (encKappa m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1)) (encF m₀ p L P5 G u)
          (encF m₀ p L P5 G v) (encW m₀ p L P5 G u v) (blockScale * L) C₂
          (density (blockScale * L) A) ∧
        ∀ U : TailIdx p L P5 → Bool,
          supportConductor (tailQ p L P5) U ≤
            ((blockScale * L : ℕ) : ℝ) ^ Cancellation.stageTan →
          FibreCore m₀ p L P5 U s (s + r) u v
            (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
            (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A (((bI.val : ℤ) - 1) * L + 1)
            ((bI.val : ℤ) * L) (blockScale * L) (L : ℝ) (blockScale : ℝ) M₀ Cε
            (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  have hK : 1 ≤ blockScale := by unfold blockScale; norm_num
  have hMod : 1 ≤ modulus pr h :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun q _ => NeZero.ne _)
  have hB := one_le_lowBound m₀ P5
  set T : ℕ := blockScale * modulus pr h * lowBound m₀ P5 with hT
  have hT1 : 0 < T := by positivity
  set L₂ := max L₁ (T ^ 120) with hL₂
  have hlarge : ∀ L, L₂ ≤ L →
      ((blockScale * modulus pr h * lowBound m₀ P5 : ℕ) : ℝ) ^ 120 ≤
        ((blockScale * L : ℕ) : ℝ) := by
    intro L hL
    have h1 : T ^ 120 ≤ L := le_trans (le_max_right _ _) hL
    have h2 : L ≤ blockScale * L := Nat.le_mul_of_pos_left L (by omega)
    have h3 : T ^ 120 ≤ blockScale * L := le_trans h1 h2
    exact_mod_cast h3
  have hL₂1 : 1 ≤ L₂ := le_trans (Nat.one_le_pow _ _ hT1) (le_max_right _ _)
  have hsizes : ∀ L, L₂ ≤ L → ∀ U : TailIdx p L P5 → Bool,
      supportConductor (tailQ p L P5) U ≤ ((blockScale * L : ℕ) : ℝ) ^ Cancellation.stageTan →
      ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) *
          ((lowModulus m₀ p L P5 : ℝ) * supportConductor (tailQ p L P5) U) ≤
          ((blockScale * L : ℕ) : ℝ) ^ (1 / 20 : ℝ) ∧
        (modulus pr h : ℝ) * ((lowModulus m₀ p L P5 : ℝ) * supportConductor (tailQ p L P5) U) ≤
          ((blockScale * L : ℕ) : ℝ) ^ (1 / 20 : ℝ) ∧
        (modulus pr h : ℝ) * ((lowModulus m₀ p L P5 : ℝ) * supportConductor (tailQ p L P5) U) ≤
          (L : ℝ) := by
    intro L hL U hU
    have hU' : supportConductor (tailQ p L P5) U ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 60 : ℝ) := hU
    exact fibre_sizes hK hMod hB (lowModulus_le m₀ p L P5 (hinj L))
      (supportConductor_nonneg _ U) hU' (hlarge L hL)
  apply densityCancellation_of_rest m₀ p pr h P5 pp ep hinj h64 hC₂ hM₀ hCε L₂ hL₂1 hcop0 hcopE
  · intro L hL U hU
    rw [prod_frozenCoords_real]
    exact (hsizes L hL U hU).1
  · intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
    obtain ⟨hMom, hCore⟩ := hSteps L (le_trans (le_max_left _ _) hL) A hA ϱ hϱ u v huv ha hb bI
      s r hbI hr G hGu hGv hGw
    refine ⟨hMom, fun U hU => ?_⟩
    intro 𝔞₁ 𝔞₂ c₁ c₂
    obtain ⟨hsq, hun, hl2⟩ := hCore U hU 𝔞₁ 𝔞₂ c₁ c₂
    have hD : ((fibreModulus m₀ p L P5 U (modulus pr h) : ℕ) : ℝ) =
        (modulus pr h : ℝ) * ((lowModulus m₀ p L P5 : ℝ) * supportConductor (tailQ p L P5) U) := by
      rw [fibreModulus, Nat.cast_mul, prod_frozenCoords_real]
    obtain ⟨-, hs2, hs3⟩ := hsizes L hL U hU
    refine ⟨by rw [hD]; exact hs2, by rw [hD]; exact hs3,
      coprime_free_fibreModulus m₀ p L P5 U (hcop0 L) (hcopE L),
      cover_free_of_cover m₀ p L P5 U _ (hcover L), hsq, hun, hl2⟩

end Final

end Sarkozy.CancellationSteps

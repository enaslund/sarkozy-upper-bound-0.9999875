module

public import Sarkozy.Cancellation.DensityCanLaws
public import Sarkozy.TheoremC.Cancellation

@[expose] public section









namespace Sarkozy.Cancellation

open Finset

/-- **Uniformity on `X × X` contradicts acceptance**: a law on labellings `Slot → X` cannot have
its `(u, v)`-marginal uniform on `X × X` (`PairUniform`) and also `z_v − z_u ≠ 0` almost surely.
This is the bug in the tail hypotheses of `ComparisonLaw` before 17:10 UTC. -/
theorem pairUniform_accepted_false {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]
    [AddGroup X] (ρ : FiniteLaw (Slot → X)) (u v : Slot)
    (hU : Sarkozy.TheoremC.PairUniform ρ u v) (hacc : ∀ z, ρ.weight z ≠ 0 → z v - z u ≠ 0) :
    False := by
  have h := hU (fun x y => if y - x = 0 then (1 : ℝ) else 0)
  have hL : ρ.expect (fun z => if z v - z u = 0 then (1 : ℝ) else 0) = 0 := by
    unfold FiniteLaw.expect
    apply sum_eq_zero
    intro z _
    by_cases hz : ρ.weight z = 0
    · rw [hz, zero_mul]
    · show ρ.weight z * (if z v - z u = 0 then (1 : ℝ) else 0) = 0
      rw [ite_eq_right (hacc z hz), mul_zero]
  have hcard : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hR : (FiniteLaw.uniform (X × X)).expect
      (fun xy => if xy.2 - xy.1 = 0 then (1 : ℝ) else 0) = (Fintype.card X : ℝ)⁻¹ := by
    rw [FiniteLaw.expect_uniform, Fintype.sum_prod_type, Fintype.card_prod]
    have h1 : ∀ x : X, ∑ y : X, (if y - x = 0 then (1 : ℝ) else 0) = 1 := by
      intro x
      have : ∀ y : X, (if y - x = 0 then (1 : ℝ) else 0) = if y = x then 1 else 0 := by
        intro y; simp only [sub_eq_zero]
      rw [sum_congr rfl fun y _ => this y, sum_ite_eq']
      simp
    simp only [h1, sum_const, card_univ, nsmul_eq_mul, mul_one]
    push_cast
    field_simp
  rw [hL, hR] at h
  exact (inv_pos.mpr hcard).ne' h.symm

end Sarkozy.Cancellation

namespace Sarkozy.Cancellation

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Mixing

/-! ## The pair-law form of a coupled integral -/

/-- **Step 2 of `lem:record:density-can`**, from `lem:record:lift-moments`(c) for the paper's
lift: the moment bounds of the other factors `W` and of the pair factor `φ = F₁ F₂`. -/
def LiftMoments {K₀ : Type} [Fintype K₀] [DecidableEq K₀] (q : K₀ → ℕ) [∀ j, NeZero (q j)]
    [∀ j, Fact (q j).Prime] {X : Type} [Fintype X] (μ : FiniteLaw X) {B : K₀ → Type}
    [∀ j, Fintype (B j)] (κ : ∀ j, FiniteLaw (PairAlphabet q j × B j))
    (F₁ F₂ : X → ResidueSpace q → ℝ) (W : X → (∀ j, B j) → ℝ) (N : ℕ) (C₂ α : ℝ) : Prop :=
  (μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b * W x b ^ 2) ≤
      C₂ * (N : ℝ) ^ (72 * stageDelta) * α ∧
    (μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
        (fun a => (F₁ x (pairsToVectors q a).1 * F₂ x (pairsToVectors q a).2) ^ 2)) ≤
      C₂ * (N : ℝ) ^ (72 * stageDelta) * α

/-- **Step 3 of `lem:record:density-can` at one low support `U`**: a fibre modulus `D` and classes
`𝔞₁, 𝔞₂` of the labels `ω = (x, a)`, with, in order:
* the size of `D` (`D ≤ N^{1/20}`, `D ≤ L`);
* coprimality and coverage (`D` prime to the free tail primes, and every prime `ℓ ≤ N^{1/40}` not
  dividing `D` is a free tail prime);
* the local conditions of (b): `𝔞₂ − 𝔞₁` is a nonvanishing square class mod `D`, `ϱ_pre`-a.s.;
* the fibre formulas of the frozen inputs (`fibre_formula_joinModel`, WP-FI's
  `groupCoeff_input_freeze`);
* the uniformity of `𝔞₁` (the class-part counts average to at most `M₀ K α`);
* the `L²` bound of the frozen inputs. -/
def FibreData {K₀ : Type} [Fintype K₀] [DecidableEq K₀] (q : K₀ → ℕ) [∀ j, NeZero (q j)]
    [∀ j, Fact (q j).Prime] {X : Type} [Fintype X] (μ : FiniteLaw X)
    (F₁ F₂ : X → ResidueSpace q → ℝ) (A : Finset ℤ) (u₁ v₁ u₂ v₂ : ℤ) (N : ℕ)
    (L Kc M₀ Cε α : ℝ) (U : K₀ → Bool) : Prop :=
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
      Cε * (N : ℝ) ^ (72 * stageDelta) * α

/-- **The pair-law form of a coupled integral `I₀`** at `N`, `L`, `A` with the constants
`C₂, Kc, M₀, Cε` and `α = |A|/N`: the encoding of `I₀` (Step 1: a prefix law `μ`, tail primes
`q_j ≥ 64` with laws `κ_j` on `Ω_{q_j} × B_j`, uniform on `Ω_{q_j}` and contracting mean-zero
functions by `q_j^{-γ}`, the pair factors `F₁, F₂` on the intervals `[u₁, v₁]`, `[u₂, v₂]` and
the other factors `W`, with `I₀ = ∫_x ∫ φ_x W_x`), the moments (`LiftMoments`) and the fibre
data at every low support (`FibreData`). These are the hypotheses of `density_can_of_pair_laws`. -/
def PairLawForm (N : ℕ) (L : ℝ) (A : Finset ℤ) (C₂ Kc M₀ Cε : ℝ) (I₀ : ℝ) : Prop :=
  ∃ (K₀ : Type) (_ : Fintype K₀) (_ : DecidableEq K₀) (q : K₀ → ℕ) (_ : ∀ j, NeZero (q j))
    (_ : ∀ j, Fact (q j).Prime), Function.Injective q ∧ (∀ j, 64 ≤ q j) ∧
  ∃ (X : Type) (_ : Fintype X) (μ : FiniteLaw X) (B : K₀ → Type) (_ : ∀ j, Fintype (B j))
    (κ : ∀ j, FiniteLaw (PairAlphabet q j × B j)),
    (∀ j a, srcWeight (κ j) a = (Fintype.card (PairAlphabet q j) : ℝ)⁻¹) ∧
    (∀ j, ContractsMeanZero (κ j) ((q j : ℝ) ^ (-stageGamma))) ∧
  ∃ (F₁ F₂ : X → ResidueSpace q → ℝ) (W : X → (∀ j, B j) → ℝ) (u₁ v₁ u₂ v₂ : ℤ),
    v₁ < u₂ ∧ u₂ ≤ v₂ ∧ ((v₂ - u₂ + 1 : ℤ) : ℝ) ≤ L ∧
    LiftMoments q μ κ F₁ F₂ W N C₂ (density N A) ∧
    (∀ U : K₀ → Bool, supportConductor q U ≤ (N : ℝ) ^ stageTan →
      FibreData q μ F₁ F₂ A u₁ v₁ u₂ v₂ N L Kc M₀ Cε (density N A) U) ∧
    I₀ = μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b *
      condOp (prodJoint κ) (fun a => F₁ x (pairsToVectors q a).1 * F₂ x (pairsToVectors q a).2)
        b * W x b

/-- The constant `C_can` of `density_can_of_pair_laws`. -/
noncomputable def canConst (Cker C₂ Kc M₀ Cε : ℝ) : ℝ :=
  Real.sqrt C₂ * (Real.sqrt C₂ + Real.sqrt ((4 * Cker ^ 2 * Kc ^ 3 * M₀ + 2 * Cε) *
    (1 + 1 / (1 - 2 * stageGamma))))

lemma canConst_nonneg (Cker C₂ Kc M₀ Cε : ℝ) : 0 ≤ canConst Cker C₂ Kc M₀ Cε := by
  unfold canConst; positivity

/-- **`lem:record:density-can` for a coupled integral in pair-law form**: `|I₀| ≤ 2C_can L^{-σ} α`. -/
theorem abs_le_of_pairLawForm :
    ∃ Cker : ℝ, 0 < Cker ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ L : ℝ, 1 ≤ L → L ≤ N →
      ∀ A : Finset ℤ, Admissible N A → ∀ C₂ Kc M₀ Cε : ℝ, 0 ≤ C₂ → 0 ≤ Kc → 0 ≤ M₀ → 0 ≤ Cε →
      (N : ℝ) / L ≤ Kc → ∀ I₀ : ℝ, PairLawForm N L A C₂ Kc M₀ Cε I₀ →
      |I₀| ≤ 2 * canConst Cker C₂ Kc M₀ Cε * L ^ (-stageSigma) * density N A := by
  obtain ⟨Cker, hCker, N₀, hmain⟩ := density_can_of_pair_laws
  refine ⟨Cker, hCker, N₀, ?_⟩
  intro N hN L hL hLN A hA C₂ Kc M₀ Cε hC₂ hKc hM₀ hCε hNL I₀ hP
  obtain ⟨K₀, _, _, q, _, _, hinj, h64, X, _, μ, B, _, κ, hsrc, hmix, F₁, F₂, W, u₁, v₁, u₂,
    v₂, huv, huv₂, hlen, ⟨hW, hφ⟩, h3, hI⟩ := hP
  have hα : 0 ≤ density N A := by
    unfold density; positivity
  have h := (hmain N hN L hL hLN K₀ q hinj h64 X μ B κ hsrc hmix F₁ F₂ W A hA u₁ v₁ u₂ v₂
    huv huv₂ hlen (density N A) C₂ Kc M₀ Cε hα hC₂ hKc hM₀ hCε hNL hW hφ h3).2
  rw [hI]
  exact h

end Sarkozy.Cancellation

namespace Sarkozy.TheoremC

open Finset Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-! ## The glue: `lem:record:density-can` over the PaperFrame objects -/

namespace Glue

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

/-- The hypotheses of `DensityCancellation` at one query, with the tail condition (a) a
parameter `Tail`. -/
def DensityQuery (Tail : ∀ L (j : J L), FiniteLaw (Slot → AtomLabel m₀ p L (some j)) →
      Slot → Slot → Prop) (P5 : ℕ) (pp ep : J₀ → ℕ) (L : ℕ) (A : Finset ℤ) (I₀ : ℝ) : Prop :=
  ∃ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
    (∀ b, HasUniformMarginals (ϱ b)) ∧
    ∃ u v : Slot, u ≠ v ∧
    (∀ j : J L, P5 ≤ p L j → Tail L j (ϱ (some j)) u v) ∧
    (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ p pp ep L b (z u) (z v)) ∧
    ∃ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 ∧
    IsNonvanishingSquareClass (modulus pr h) r ∧
    ∃ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
    G u = indexInputAt m₀ p pr h L A (bI, s) ∧
    G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) ∧
    (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) ∧
    I₀ = multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b).weight) G

/-- `stageSigma = σ = 1/825`. -/
lemma stageSigma_eq : Sarkozy.Cancellation.stageSigma = cancellationDecay := by
  unfold Sarkozy.Cancellation.stageSigma cancellationDecay; rfl

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- **The glue** (generic in the tail condition): if every query integral at every large
scale has a pair-law form with the constants `C₂, K, M₀, Cε` fixed (`hEnc`), the uniform
density-linear bound `|I₀| ≤ 2C_can L^{-σ} α` of `lem:record:density-can` holds. -/
theorem densityQuery_bound (Tail : ∀ L (j : J L), FiniteLaw (Slot → AtomLabel m₀ p L (some j)) →
      Slot → Slot → Prop) (P5 : ℕ) (pp ep : J₀ → ℕ) {C₂ M₀ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hM₀ : 0 ≤ M₀) (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hEnc : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A → ∀ I₀ : ℝ,
      DensityQuery m₀ p pr h Tail P5 pp ep L A I₀ →
      Sarkozy.Cancellation.PairLawForm (blockScale * L) (L : ℝ) A C₂ (blockScale : ℝ) M₀ Cε I₀) :
    ∃ Ccan : ℝ, 0 ≤ Ccan ∧ ∃ Lstar : ℕ, ∀ L : ℕ, Lstar ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → ∀ I₀ : ℝ, DensityQuery m₀ p pr h Tail P5 pp ep L A I₀ →
      |I₀| ≤ remainder (2 * Ccan) L A := by
  obtain ⟨Cker, -, N₀, hmain⟩ := Sarkozy.Cancellation.abs_le_of_pairLawForm
  refine ⟨Sarkozy.Cancellation.canConst Cker C₂ blockScale M₀ Cε,
    Sarkozy.Cancellation.canConst_nonneg _ _ _ _ _, max L₁ (max N₀ 1), ?_⟩
  intro L hL A hA I₀ hQ
  have hL₁ : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hN₀ : N₀ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hL
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hL
  have hK : 1 ≤ blockScale := by unfold blockScale; norm_num
  have hLN : L ≤ blockScale * L := Nat.le_mul_of_pos_left L (by omega)
  have hLr : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hLNr : (L : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) := by exact_mod_cast hLN
  have hNL : ((blockScale * L : ℕ) : ℝ) / L ≤ blockScale := by
    rw [Nat.cast_mul, mul_div_assoc, div_self (by positivity : (L : ℝ) ≠ 0), mul_one]
  have hb := hmain (blockScale * L) (le_trans hN₀ hLN) (L : ℝ) hLr hLNr A hA C₂ blockScale M₀ Cε
    hC₂ (by positivity) hM₀ hCε hNL I₀ (hEnc L hL₁ A hA I₀ hQ)
  unfold remainder
  rw [← stageSigma_eq]
  exact hb

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- **`DensityCancellation` from the pair-law forms**, for WP-FI's corrected statement, in which
(a) is `PairUniformOmega`, the `(u, v)`-marginal uniform on the strict-square pairs `Ω_p`. -/
theorem densityCancellation_of_pairLawForm (P5 : ℕ) (pp ep : J₀ → ℕ) {C₂ M₀ Cε : ℝ}
    (hC₂ : 0 ≤ C₂) (hM₀ : 0 ≤ M₀) (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hEnc : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A → ∀ I₀ : ℝ,
      DensityQuery m₀ p pr h (fun L j ρ u v => PairUniformOmega (q := p L j) ρ u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ ρ {u, v}) P5 pp ep L A I₀ →
      Sarkozy.Cancellation.PairLawForm (blockScale * L) (L : ℝ) A C₂ (blockScale : ℝ) M₀ Cε I₀) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  obtain ⟨Ccan, hCcan, Lstar, hb⟩ := densityQuery_bound m₀ p pr h _ P5 pp ep hC₂ hM₀ hCε L₁ hEnc
  refine ⟨Ccan, hCcan, Lstar, ?_⟩
  intro L hL A hA ϱ hϱ u v huv ha hbelow bI s r hbI hr G hGu hGv hGw
  exact hb L hL A hA _ ⟨ϱ, hϱ, u, v, huv, ha, hbelow, bI, s, r, hbI, hr, G, hGu, hGv, hGw, rfl⟩

end Glue

end Sarkozy.TheoremC

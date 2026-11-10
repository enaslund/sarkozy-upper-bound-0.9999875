module

public import Sarkozy.CancellationSteps.SquareStep

/-!
# `DensityCancellation` from the moment and uniformity inputs alone

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, over WP-FI's
`TheoremC.DensityCancellation`. `densityCancellation_of_core` with the square-class clause of
`FibreCore` discharged by `squareClass_step` (the local conditions (b)). What remains is:

* Step 2: `LiftMoments` (`lem:record:lift-moments`(c)) at the encoded data;
* `FibreAnalytic` at every low support: for every choice of fibre classes `𝔞₁, 𝔞₂`,
  - the uniformity of `𝔞₁`: `E (D/L)|A ∩ I_b ∩ (𝔞₁ + Dℤ)| ≤ M₀' K α`;
  - the `L²` bound `E(‖g₁‖² ‖g₂‖²) ≤ C_ε N^{72δ} α` of the frozen inputs;
* elementary facts about the data (coprimality of the moduli, the prefix moduli prime powers,
  the coverage of the small primes).

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

/-- **The analytic clauses of Step 3 that remain** at a low support `U`, for the encoded data:
for every choice of fibre classes `𝔞₁`, `𝔞₂` (modulo `D = M ∏_{c ∈ E} m_c`), the uniformity of
`𝔞₁` and the `L²` bound of the frozen inputs. -/
def FibreAnalytic (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {M : ℕ} (s s' : ZMod M) (u v : Slot)
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

section Final

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from the moment and uniformity
inputs alone.** Hypotheses:
* distinct tail primes and `P₅ ≥ 64`;
* elementary facts about the data: `M₀ = modulus pr h` coprime to every atom modulus; the atom
  moduli pairwise coprime; the prefix moduli prime powers `m₀ i = pp_i^{ep_i}`, `pp_i` prime,
  `ep_i ≥ 1` (the `pp, ep` of the acceptance condition); every prime `ℓ ≤ N^{1/40}` divides `M₀`
  or a prefix modulus or is a tail prime;
* for every query at every scale `L ≥ L₁`: `LiftMoments` (`lem:record:lift-moments`(c), Step 2)
  at the encoded data, and `FibreAnalytic` (the uniformity of `𝔞₁` and the `L²` bound) at
  every low support `q_U ≤ N^{t_an}`, for the interval `I_b = [(c − 1)L + 1, cL]`, `c = b.val`.

Proved: Step 1 (WP-K), the intervals, the fibre formulas, the size of `D`, `H D_E ≤ Q`, the
coprimality and coverage conditions, and the square class of `𝔞₂ − 𝔞₁` from the acceptance (b). -/
theorem densityCancellation_of_analytic (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ M₀ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hM₀ : 0 ≤ M₀) (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
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
          FibreAnalytic m₀ p L P5 U s (s + r) u v
            (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
            (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A (((bI.val : ℤ) - 1) * L + 1)
            ((bI.val : ℤ) * L) (blockScale * L) (L : ℝ) (blockScale : ℝ) M₀ Cε
            (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  have hMod : modulus pr h ≠ 0 := prod_ne_zero_iff.mpr fun q _ => NeZero.ne _
  have : NeZero (modulus pr h) := ⟨hMod⟩
  apply densityCancellation_of_core m₀ p pr h P5 pp ep hinj h64 hC₂ hM₀ hCε L₁ hcop0 hcopE
    hcover
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  obtain ⟨hMom, hAn⟩ := hSteps L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  refine ⟨hMom, fun U hU => ?_⟩
  intro 𝔞₁ 𝔞₂ c₁ c₂
  obtain ⟨hun, hl2⟩ := hAn U hU 𝔞₁ 𝔞₂ c₁ c₂
  exact ⟨fun ω hω => squareClass_step m₀ p pp ep hpre L P5 U (hcop0 L) (hcopE L) s r hr u v ϱ hb
    𝔞₁ 𝔞₂ c₁ c₂ ω hω, hun, hl2⟩

end Final

/-! ## The uniformity of `𝔞₁` as an equidistribution statement -/

/-- **The two analytic inputs of Step 3**, with the uniformity of `𝔞₁` in the paper's form: for
every choice of fibre classes `𝔞₁`, `𝔞₂`, the class `𝔞₁` modulo `D` is equidistributed among the
classes above `s` modulo `M` ("the class `𝔞₁` is uniform among the classes modulo `D` above `s`",
for `D`-periodic test functions `f`), and the `L²` bound of the frozen inputs. -/
def FibreEquidist (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {M : ℕ} (s s' : ZMod M) (u v : Slot)
    (μ : FiniteLaw (LowLabels m₀ p L P5))
    (F₁ F₂ : LowLabels m₀ p L P5 → ResidueSpace (tailQ p L P5) → ℝ) (N : ℕ) (Cε α : ℝ) : Prop :=
  ∀ 𝔞₁ 𝔞₂ : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℤ,
    (∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1) s n ↔
        n ≡ 𝔞₁ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)]) →
    (∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 v ω.1 (pairsToVectors (tailQ p L P5) ω.2).2) s' n ↔
        n ≡ 𝔞₂ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)]) →
    (∀ f : ℤ → ℝ, (∀ c, f (c + fibreModulus m₀ p L P5 U M) = f c) →
      ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
          (μ.weight ω.1 * (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) * f (𝔞₁ ω) =
        (M : ℝ) / (fibreModulus m₀ p L P5 U M : ℕ) *
          ∑ c ∈ (range (fibreModulus m₀ p L P5 U M)).filter
            (fun c : ℕ => (c : ℤ) ≡ (s.val : ℤ) [ZMOD (M : ℤ)]), f c) ∧
    ∑ ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k),
        (μ.weight ω.1 * (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) *
          ((𝔼 z, ‖(F₁ ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).1 z) : ℂ)‖ ^ 2) *
            (𝔼 z, ‖(F₂ ω.1 (mergeFree U (pairsToVectors (tailQ p L P5) ω.2).2 z) : ℂ)‖ ^ 2)) ≤
      Cε * (N : ℝ) ^ (72 * stageDelta) * α

section Equidist

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from Step 2, the equidistribution
of the fibre classes and the `L²` bound.** `densityCancellation_of_analytic` with the uniformity
clause derived from the equidistribution of `𝔞₁` (`Cancellation.expect_fibreDensity_le`, with the
constant `M₀ = modulus pr h`). Hypotheses: as in `densityCancellation_of_analytic`, with
`FibreEquidist` in place of `FibreAnalytic`. -/
theorem densityCancellation_of_equidist (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
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
          FibreEquidist m₀ p L P5 U s (s + r) u v
            (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
            (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) (blockScale * L) Cε
            (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  have hMod : modulus pr h ≠ 0 := prod_ne_zero_iff.mpr fun q _ => NeZero.ne _
  have hKpos : 0 < blockScale := by unfold blockScale; norm_num
  apply densityCancellation_of_analytic m₀ p pr h P5 pp ep hinj h64 hC₂
    (Nat.cast_nonneg (modulus pr h)) hCε (max L₁ 1) hcop0 hcopE hpre hcover
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  obtain ⟨hMom, hEq⟩ := hSteps L (le_trans (le_max_left _ _) hL) A hA ϱ hϱ u v huv ha hb bI
    s r hbI hr G hGu hGv hGw
  refine ⟨hMom, fun U hU => ?_⟩
  intro 𝔞₁ 𝔞₂ c₁ c₂
  obtain ⟨hunif, hl2⟩ := hEq U hU 𝔞₁ 𝔞₂ c₁ c₂
  refine ⟨?_, hl2⟩
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) hL
  have hD : 0 < fibreModulus m₀ p L P5 U (modulus pr h) := by
    unfold fibreModulus
    exact Nat.pos_of_ne_zero (mul_ne_zero hMod (prod_ne_zero_iff.mpr fun c _ => NeZero.ne _))
  have hdvd : modulus pr h ∣ fibreModulus m₀ p L P5 U (modulus pr h) := by
    unfold fibreModulus
    exact dvd_mul_right _ _
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL1
  have hN : 0 < blockScale * L := Nat.mul_pos hKpos hL1
  have hNL : ((blockScale * L : ℕ) : ℝ) / L ≤ blockScale := by
    rw [Nat.cast_mul, mul_div_assoc, div_self hLr.ne', mul_one]
  have := expect_fibreDensity_le univ
    (fun ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) =>
      (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 *
        (Fintype.card (∀ k, PairAlphabet (tailQ p L P5) k) : ℝ)⁻¹) 𝔞₁ A
    (((bI.val : ℤ) - 1) * L + 1) ((bI.val : ℤ) * L) hD hdvd (s.val : ℤ) hLr hN hNL hunif
  unfold density
  exact this

end Equidist

end Sarkozy.CancellationSteps

module

public import Sarkozy.CancellationSteps.Moment4

/-!
# Step 2 for the pair factor

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 2: the moment bound
`∫_x ‖φ_x‖₂² ≤ C₂ N^{72δ} α` of the pair factor `φ_x(a) = F₁(x, x(a)) F₂(x, y(a))` under
`⊗_p Unif(Ω_p)`, the second clause of WP-K's `LiftMoments`:

* `pair_slot_uniform`, `pair_slot_uniform_snd`: the slot labels `mergeAt x_u y_u` and
  `mergeAt x_v y_v`, with `(y_u, y_v)` uniform on `∏_p Ω_p`, are uniform on `G_N`
  (`slot_uniform` with every tail prime frozen);
* `pairFactor_moment`: the pair-factor bound, from WP-K's `step2_pair_factor` and the fourth
  moments of the query inputs (`indexedInput_fourth_moment`);
* `densityCancellation_of_otherSlots`: WP-FI's `DensityCancellation` from the Step 2 bound of the
  other factors `W = ∏_{w ≠ u, v} G_w` alone (and elementary facts about the data).

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

/-- With every tail prime frozen, `mergeFree` is the identity. -/
lemma mergeFree_allTrue {K : Type*} {A : K → Type*} (a : ∀ j, A j)
    (c : ∀ j : {j : K // (fun _ => true) j = false}, A j.1) :
    mergeFree (fun _ => true) a c = a := by
  funext j
  exact mergeFree_fixed (fun _ => true) a c rfl

/-- The slot label `mergeAt x_u y_u`, `(y_u, y_v)` uniform on `∏_p Ω_p`, is uniform on `G_N`. -/
theorem pair_slot_uniform [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (w : Slot)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (f : ResidueSpace (joinModuli m₀ (p L)) → ℝ) :
    ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).expect fun x =>
      (FiniteLaw.uniform (∀ k, PairAlphabet (tailQ p L P5) k)).expect
        (fun a => f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w)
          (pairsToVectors (tailQ p L P5) a).1)))) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect f := by
  have h := slot_uniform m₀ p L P5 (fun _ => true) w ϱ hϱ f
  rw [← h]
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [mergeFree_allTrue]
  rw [Fintype.expect_const]
  simp only [FiniteLaw.uniform]
  ring

/-- The slot label `mergeAt x_v y_v`, `(y_u, y_v)` uniform on `∏_p Ω_p`, is uniform on `G_N`. -/
theorem pair_slot_uniform_snd [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (w : Slot)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) (f : ResidueSpace (joinModuli m₀ (p L)) → ℝ) :
    ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).expect fun x =>
      (FiniteLaw.uniform (∀ k, PairAlphabet (tailQ p L P5) k)).expect
        (fun a => f (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w)
          (pairsToVectors (tailQ p L P5) a).2)))) =
      (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect f := by
  have h := slot_uniform_snd m₀ p L P5 (fun _ => true) w ϱ hϱ f
  rw [← h]
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  simp only [mergeFree_allTrue]
  rw [Fintype.expect_const]
  simp only [FiniteLaw.uniform]
  ring

/-! ## The pair factor -/

section Final

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) from the Step 2 bound of the other
factors alone.** Hypotheses:
* elementary facts about the data: distinct tail primes, `P₅ ≥ 64`, `M₀` coprime to every atom
  modulus, the atom moduli pairwise coprime, the prefix moduli prime powers `pp_i^{ep_i}`, and the
  coverage of the primes up to `N^{1/40}` (`hcover`);
* for every query at every scale `L ≥ L₁`: the first clause of `LiftMoments`, the bound
  `∫_x ‖W_x‖₂² ≤ C₂ N^{72δ} α` of the other factors `W = ∏_{w ≠ u, v} G_w` under the encoded
  laws (Step 2, from `lem:record:lift-moments`(c) and Hölder).

Proved: Step 1 (WP-K); the pair-factor clause of Step 2 (`step2_pair_factor`, from the uniformity
of the slot labels and the fourth moments of the inputs); and all of Step 3. -/
theorem densityCancellation_of_otherSlots (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ : ℝ} (hC₂ : 0 ≤ C₂) (L₁ : ℕ)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i)
    (hcover : ∀ L : ℕ, ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) →
      ℓ ∣ modulus pr h ∨ (∃ i, ℓ ∣ m₀ i) ∨ ∃ j, p L j = ℓ)
    (hOther : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
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
        ((FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).expect fun x =>
          ∑ b, tgtWeight (prodJoint (encKappa m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1))) b *
            encW m₀ p L P5 G u v x b ^ 2) ≤
          C₂ * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (blockScale * L) A) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  obtain ⟨C, hC, hmomC⟩ := DensityDC.moment_input_le 2 (by norm_num) (1440 * stageDelta)
    (by unfold stageDelta; norm_num)
  have hK : 1 ≤ blockScale := by unfold blockScale; norm_num
  have : NeZero blockScale := ⟨by unfold blockScale; norm_num⟩
  set Cε : ℝ := ((modulus pr h : ℕ) : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) *
    blockScale with hCε
  have hCε0 : 0 ≤ Cε := by positivity
  apply densityCancellation_of_step2 m₀ p pr h P5 pp ep hinj h64 (C₂ := max C₂ Cε)
    (le_trans hC₂ (le_max_left _ _)) (max L₁ (2 ^ 20 * blockScale)) hcop0 hcopE hpre hcover
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  have hL₁ : L₁ ≤ L := le_trans (le_max_left _ _) hL
  have hL₂ : 2 ^ 20 * blockScale ≤ L := le_trans (le_max_right _ _) hL
  have hNα : 0 ≤ ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (blockScale * L) A :=
    mul_nonneg (by positivity) (density_nonneg _ _)
  refine ⟨?_, ?_⟩
  · refine (hOther L hL₁ A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw).trans ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hNα
  · -- the pair factor
    set Gu := indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
      (modulus pr h) A (bI, s) with hGuDef
    set Gv := indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
      (modulus pr h) A (bI + 1, s + r) with hGvDef
    have hmom : ∀ (bI' : ZMod blockScale) (s' : ZMod (modulus pr h)),
        (FiniteLaw.uniform (ResidueSpace (joinModuli m₀ (p L)))).expect (fun y =>
          |indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
            (modulus pr h) A (bI', s') y| ^ ((4 : ℕ) : ℝ)) ≤
          max C₂ Cε * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) *
            density (blockScale * L) A := by
      intro bI' s'
      have h4 := indexedInput_fourth_moment m₀ (p L) C
        (fun Q hQ c M hM h1 h2 => hmomC m₀ (p L) (fun j => (Fact.out : (p L j).Prime)) (hinj L)
          Q hQ c M hM h1 h2)
        hC hK hL₂ A bI' s'
      simp only [Real.rpow_natCast]
      refine h4.trans ?_
      have e1 : ((modulus pr h : ℕ) : ℝ) ^ 4 * ((Fintype.card (ResidueSpace m₀) : ℝ) ^ 4 * C) *
          (blockScale : ℝ) * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) *
          density (blockScale * L) A =
          Cε * (((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) * density (blockScale * L) A) := by
        rw [hCε]
        ring
      have e2 : max C₂ Cε * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) *
          density (blockScale * L) A = max C₂ Cε * (((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) *
            density (blockScale * L) A) := by ring
      rw [e1, e2]
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) hNα
    have hM : 0 ≤ max C₂ Cε * ((blockScale * L : ℕ) : ℝ) ^ (72 * stageDelta) *
        density (blockScale * L) A := by
      rw [mul_assoc]
      exact mul_nonneg (le_trans hC₂ (le_max_left _ _)) hNα
    exact step2_pair_factor (tailQ p L P5)
      (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
      (fun x y => atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i u) y))
      (fun x y => atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i v) y)) Gu Gv
      (encF m₀ p L P5 G u) (encF m₀ p L P5 G v)
      (fun x y => by unfold encF; rw [hGu]; rfl) (fun x y => by unfold encF; rw [hGv]; rfl)
      (fun f => pair_slot_uniform m₀ p L P5 u ϱ hϱ f)
      (fun f => pair_slot_uniform_snd m₀ p L P5 v ϱ hϱ f)
      hM (hmom bI s) (hmom (bI + 1) (s + r))

end Final

end Sarkozy.CancellationSteps

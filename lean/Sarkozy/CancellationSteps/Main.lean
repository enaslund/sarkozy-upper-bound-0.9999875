module

public import Sarkozy.CancellationSteps.Intervals
public import Sarkozy.CancellationSteps.FibreFormula

/-!
# `DensityCancellation` with the intervals and the fibre formulas discharged

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, over WP-FI's
`TheoremC.DensityCancellation`. WP-K's `Cancellation.densityCancellation_of_steps` derives it from
`hSteps`: for every query, intervals `[u₁, v₁]`, `[u₂, v₂]` with Step 2 (`LiftMoments`) and Step 3
(`FibreData`) at the encoded data. Here:

* the intervals are `I_b = [(c − 1)L + 1, cL]`, `I_{b+1} = [cL + 1, (c + 1)L]`, `c = b.val`
  (`blockInterval_eq_Icc`, `queryIntervals_ok`), no longer a hypothesis;
* the fibre formulas of `FibreData` (both pair factors, every frequency with `q(a) ≤ N^{1/40}`)
  are proved (`encInput_fibre_formula`), with the fibre modulus `D = M₀ ∏_{c ∈ E} m_c`
  (`fibreModulus`) and the classes of the fibres chosen by the CRT (`inFibre_iff_modEq`);
* `fibreData_of_rest`: `FibreData` from `FibreRest`, the other clauses of `FibreData` stated for
  this `D` and for every choice of fibre classes.

`densityCancellation_of_rest` is the result. Its hypotheses are:
* structural facts about the data (all elementary):
  - `M₀` coprime to every atom modulus (`def:record:functional`, "the small modulus is coprime
    to `D_{𝒫_N}`");
  - the atom moduli pairwise coprime;
  - `H ∏_{c ∈ E} m_c ≤ Q` at every low support (`lem:scale-conditions`(vi), first part);
* Step 2 at the encoded data: `LiftMoments` (`lem:record:lift-moments`(c));
* `FibreRest` at every low support: the size of `D` and the coprimality and covering conditions
  (`lem:scale-conditions`(v), (vi)), the square class of `𝔞₂ − 𝔞₁` (the local conditions (b)),
  the uniformity of `𝔞₁` and the `L²` bound.

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

/-- The frozen label of the slot `w` at the low labels `x` and the tail labels `y`:
`mergeAt x_w y`, read in `G_N`. -/
noncomputable def frozenAt (L P5 : ℕ) (w : Slot) (x : LowLabels m₀ p L P5)
    (y : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) : ResidueSpace (joinModuli m₀ (p L)) :=
  atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 (fun i => x i w) y)

/-- **What remains of Step 3 at a low support `U`** (`FibreData` without its fibre formulas), for
the encoded data: with the fibre modulus `D = M ∏_{c ∈ E} m_c` (`fibreModulus`) and any classes
`𝔞₁(ω)`, `𝔞₂(ω)` of the fibres of the frozen labels of the slots `u` (residue `s`) and `v`
(residue `s'`) at `ω = (x, a)`:
* `D ≤ N^{1/20}` and `D ≤ L`;
* `D` is prime to the free tail primes, and every prime `ℓ ≤ N^{1/40}` not dividing `D` is a free
  tail prime (`lem:scale-conditions`(v));
* `𝔞₂ − 𝔞₁` is a nonvanishing square class mod `D`, `μ`-a.s. (the local conditions of (b));
* the uniformity of `𝔞₁`: `E (D/L)|A ∩ I_b ∩ (𝔞₁ + Dℤ)| ≤ M₀ K α`;
* the `L²` bound `E(‖g₁‖² ‖g₂‖²) ≤ C_ε N^{72δ} α` of the frozen inputs. -/
def FibreRest (L P5 : ℕ) (U : TailIdx p L P5 → Bool) {M : ℕ} (s s' : ZMod M) (u v : Slot)
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
    ((fibreModulus m₀ p L P5 U M : ℕ) : ℝ) ≤ (N : ℝ) ^ (1 / 20 : ℝ) ∧
    ((fibreModulus m₀ p L P5 U M : ℕ) : ℝ) ≤ Lr ∧
    (∀ k : {j // U j = false}, Nat.Coprime (tailQ p L P5 k.1) (fibreModulus m₀ p L P5 U M)) ∧
    (∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℝ) ≤ (N : ℝ) ^ (1 / 40 : ℝ) → ¬ ℓ ∣ fibreModulus m₀ p L P5 U M →
      ∃ k : {j // U j = false}, tailQ p L P5 k.1 = ℓ) ∧
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

/-- **`FibreData` from `FibreRest`**: for the encoded pair factors `F₁ = G_u`, `F₂ = G_v` of
`PaperEncoding`, with `G_u = Re g^{[u₁, v₁], M, s}`, `G_v = Re g^{[u₂, v₂], M, s'}` read through
`atomGroupEquiv`, `|[u₁, v₁]| = |[u₂, v₂]| = L`, `M` coprime to the frozen moduli, the frozen
moduli pairwise coprime and `N^{1/40} ∏_{c ∈ E} m_c ≤ Q`: the fibre formulas of `FibreData` hold
with `D = fibreModulus` and the CRT classes of the fibres, so `FibreData` follows from the
remaining clauses `FibreRest`. -/
theorem fibreData_of_rest [∀ L j, Fact (p L j).Prime] (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    {M : ℕ} (s s' : ZMod M) (u v : Slot) (μ : FiniteLaw (LowLabels m₀ p L P5))
    (G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ) (Q : ℝ) (A : Finset ℤ) (u₁ v₁ u₂ v₂ : ℤ)
    (hGu : ∀ x, G u x = (input (joinModuli m₀ (p L)) Q (Icc u₁ v₁) M s A
      (atomGroupEquiv m₀ p L x)).re)
    (hGv : ∀ x, G v x = (input (joinModuli m₀ (p L)) Q (Icc u₂ v₂) M s' A
      (atomGroupEquiv m₀ p L x)).re)
    (N : ℕ) (Lr Kc M₀ Cε α : ℝ)
    (hcard₁ : ((Icc u₁ v₁).card : ℝ) = Lr) (hcard₂ : ((Icc u₂ v₂).card : ℝ) = Lr)
    (hcop0 : ∀ c ∈ frozenCoords (J₀ := J₀) p L P5 U, Nat.Coprime M (joinModuli m₀ (p L) c))
    (hcopE : ∀ i ∈ frozenCoords (J₀ := J₀) p L P5 U, ∀ j ∈ frozenCoords (J₀ := J₀) p L P5 U,
      i ≠ j → Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hHQ : (N : ℝ) ^ (1 / 40 : ℝ) *
      (∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) ≤ Q)
    (hrest : FibreRest m₀ p L P5 U s s' u v μ (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A u₁ v₁
      N Lr Kc M₀ Cε α) :
    FibreData (tailQ p L P5) μ (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A u₁ v₁ u₂ v₂ N Lr Kc
      M₀ Cε α U := by
  classical
  have hcls : ∀ (w : Slot) (t : ZMod M) (x : LowLabels m₀ p L P5)
      (y : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)), ∃ 𝔞 : ℤ, ∀ n : ℤ,
      InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U) (frozenAt m₀ p L P5 w x y)
        t n ↔ n ≡ 𝔞 [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)] := fun w t x y =>
    inFibre_iff_modEq (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U) t
      (frozenAt m₀ p L P5 w x y) hcop0 hcopE
  set 𝔞₁ : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℤ := fun ω =>
    Classical.choose (hcls u s ω.1 (pairsToVectors (tailQ p L P5) ω.2).1) with h𝔞₁def
  set 𝔞₂ : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℤ := fun ω =>
    Classical.choose (hcls v s' ω.1 (pairsToVectors (tailQ p L P5) ω.2).2) with h𝔞₂def
  have h𝔞₁ : ∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
      (frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1) s n ↔
      n ≡ 𝔞₁ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)] := fun ω =>
    Classical.choose_spec (hcls u s ω.1 (pairsToVectors (tailQ p L P5) ω.2).1)
  have h𝔞₂ : ∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
      (frozenAt m₀ p L P5 v ω.1 (pairsToVectors (tailQ p L P5) ω.2).2) s' n ↔
      n ≡ 𝔞₂ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)] := fun ω =>
    Classical.choose_spec (hcls v s' ω.1 (pairsToVectors (tailQ p L P5) ω.2).2)
  obtain ⟨r1, r2, r3, r4, r5, r6, r7⟩ := hrest 𝔞₁ 𝔞₂ h𝔞₁ h𝔞₂
  refine ⟨fibreModulus m₀ p L P5 U M, 𝔞₁, 𝔞₂, r1, r2, r3, r4, r5, ?_, ?_, r6, r7⟩
  · intro ω _ a ha
    have hF := encInput_fibre_formula m₀ p L P5 U (Q := Q) u₁ v₁ s A (fun i => ω.1 i u)
      (pairsToVectors (tailQ p L P5) ω.2).1 (𝔞₁ ω) (h𝔞₁ ω) hHQ a ha
    rw [hcard₁] at hF
    refine Eq.trans ?_ hF
    congr 1
    funext x'
    unfold encF
    rw [hGu]
  · intro ω _ a ha
    have hF := encInput_fibre_formula m₀ p L P5 U (Q := Q) u₂ v₂ s' A (fun i => ω.1 i v)
      (pairsToVectors (tailQ p L P5) ω.2).2 (𝔞₂ ω) (h𝔞₂ ω) hHQ a ha
    rw [hcard₂] at hF
    refine Eq.trans ?_ hF
    congr 1
    funext x'
    unfold encF
    rw [hGv]

/-! ## `DensityCancellation` -/

section Final

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)

open Sarkozy.TheoremC Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`lem:record:density-can` (WP-FI's `DensityCancellation`) with the intervals and the fibre
formulas discharged.** Hypotheses:
* distinct tail primes, `P₅ ≥ 64` (as in `densityCancellation_of_steps`);
* the small modulus `M₀ = modulus pr h` is coprime to every atom modulus, and the atom moduli
  are pairwise coprime (`def:record:functional`; in the paper the primes of `M₀` are `2` and
  primes `≡ 3 (4)` below `Q₃`, none of them an atom prime);
* `N^{1/40} ∏_{c ∈ E} m_c ≤ Q = N^{1/20}` at every low support (`lem:scale-conditions`(vi));
* for every query at every scale `L ≥ L₁ ≥ 1`: Step 2 (`LiftMoments`,
  `lem:record:lift-moments`(c)) at the encoded data, and `FibreRest` at every low support
  `q_U ≤ N^{t_an}`, for the query interval `I_b = [(c − 1)L + 1, cL]`, `c = b.val`.

The constants `C₂`, `M₀` (of the uniformity bound) and `C_ε` are fixed in advance. -/
theorem densityCancellation_of_rest (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ M₀ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hM₀ : 0 ≤ M₀) (hCε : 0 ≤ Cε) (L₁ : ℕ) (hL₁ : 1 ≤ L₁)
    (hcop0 : ∀ L (c : J₀ ⊕ J L), Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) c))
    (hcopE : ∀ L, ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (hHQ : ∀ L : ℕ, L₁ ≤ L → ∀ U : TailIdx p L P5 → Bool,
      supportConductor (tailQ p L P5) U ≤ ((blockScale * L : ℕ) : ℝ) ^ Cancellation.stageTan →
      ((blockScale * L : ℕ) : ℝ) ^ (1 / 40 : ℝ) *
        (∏ c ∈ frozenCoords (J₀ := J₀) p L P5 U, joinModuli m₀ (p L) c : ℕ) ≤
        paperCutoff (blockScale * L))
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
          supportConductor (tailQ p L P5) U ≤ ((blockScale * L : ℕ) : ℝ) ^ Cancellation.stageTan →
          FibreRest m₀ p L P5 U s (s + r) u v
            (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
            (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A (((bI.val : ℤ) - 1) * L + 1)
            ((bI.val : ℤ) * L) (blockScale * L) (L : ℝ) (blockScale : ℝ) M₀ Cε
            (density (blockScale * L) A)) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  apply densityCancellation_of_steps m₀ p pr h P5 pp ep hinj h64 hC₂ hM₀ hCε L₁
  intro L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  obtain ⟨hMom, hRest⟩ := hSteps L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  have hK : 2 ≤ blockScale := by unfold blockScale; norm_num
  obtain ⟨hI₁, hI₂⟩ := blockInterval_eq_Icc hK L hbI
  have hL1 : 1 ≤ L := le_trans hL₁ hL
  obtain ⟨o1, o2, o3⟩ := queryIntervals_ok bI.val L hL1
  refine ⟨((bI.val : ℤ) - 1) * L + 1, (bI.val : ℤ) * L, (bI.val : ℤ) * L + 1,
    ((bI.val : ℤ) + 1) * L, o1, o2, o3, hMom, ?_⟩
  intro U hU
  have hGu' : ∀ x, G u x = (input (joinModuli m₀ (p L)) (paperCutoff (blockScale * L))
      (Icc (((bI.val : ℤ) - 1) * L + 1) ((bI.val : ℤ) * L)) (modulus pr h) s A
      (atomGroupEquiv m₀ p L x)).re := by
    intro x
    rw [hGu, ← hI₁]
    rfl
  have hGv' : ∀ x, G v x = (input (joinModuli m₀ (p L)) (paperCutoff (blockScale * L))
      (Icc ((bI.val : ℤ) * L + 1) (((bI.val : ℤ) + 1) * L)) (modulus pr h) (s + r) A
      (atomGroupEquiv m₀ p L x)).re := by
    intro x
    rw [hGv, ← hI₂]
    rfl
  have hc₁ : (((Icc (((bI.val : ℤ) - 1) * L + 1) ((bI.val : ℤ) * L)).card : ℕ) : ℝ) = (L : ℝ) := by
    have := card_queryInterval ((bI.val : ℤ) - 1) L
    rwa [sub_add_cancel] at this
  have hc₂ : (((Icc ((bI.val : ℤ) * L + 1) (((bI.val : ℤ) + 1) * L)).card : ℕ) : ℝ) = (L : ℝ) :=
    card_queryInterval (bI.val : ℤ) L
  exact fibreData_of_rest m₀ p L P5 U s (s + r) u v _ G (paperCutoff (blockScale * L)) A _ _ _ _
    hGu' hGv' (blockScale * L) (L : ℝ) (blockScale : ℝ) M₀ Cε _ hc₁ hc₂
    (fun c _ => hcop0 L c) (fun i _ j _ hij => hcopE L i j hij) (hHQ L hL U hU) (hRest U hU)

end Final

end Sarkozy.CancellationSteps

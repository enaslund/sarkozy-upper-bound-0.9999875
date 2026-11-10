module

public import Sarkozy.EnvelopeEnergiesPaper.BlockCRT
public import Sarkozy.EnvelopeInputsBlock.Inputs

@[expose] public section

/-!
# The envelope-energy terms (`fix`, `env`) in cyclic coordinates

G1's bundles `FixedIntervalInputs` and `EnvelopeEnergyInputs` (`lem:envelope-energy`) ask per-term
bounds on multilinear energies of block-atom laws `⊗_𝔟 Λ_𝔟` (envelope increments at a set `f` of
atoms, the bracket `Ñ_𝔟` elsewhere) with revealed pair inputs. This file carries those energies to
the cyclic coordinates `ℤ/crtModuli` of `BlockCRT`, **for every block law** (no product prefix):

* `blockInput_crtLabel`: the paper's inputs `g^{I_b, M₀, s}` on the block labels are the inputs
  `indexedInput crtModuli` of the cyclic group (`CRTLift.lift_comp_eq`);
* `revealedInput_crtLabel`: the revealed slot functions likewise (`revealedInputCRT`);
* `pairInputs_comp`: the pair inputs commute with a relabelling;
* **`env_term_crt`**, **`fix_term_crt`**: the energies in `EnvelopeEnergyInputs.htermL/R` and
  `FixedIntervalInputs.htermL/R` are the energies of the pulled laws `crtLaws` on the cyclic
  coordinates with cyclic inputs.

So both bundles are statements about the cyclic group `G_N ≅ ∏_𝔟 ℤ/crtModuli_𝔟`, where the formal
coordinate chains (WP-R's `Structured`, `DensityDC`, WP-S's `density_structured_theta_few`) are
stated. What they still need is not a coordinate change but the bracket outside law `Ñ` and the
revealed inputs (see the report).
-/

open Finset Function
open scoped BigOperators Matrix

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame Sarkozy.BlockFrame
  Sarkozy.Structured Sarkozy.IndexSupport Sarkozy.TheoremC

/-- **The pair inputs commute with a relabelling** `g : Y → X`. -/
theorem pairInputs_comp {E Ωi X Y : Type} [Fintype E] [DecidableEq E]
    (u w : E → reservedCut.Half) (φ ψ : E → Ωi → X → ℝ) (F : X → ℝ) (ω ω' : E → Ωi)
    (g : Y → X) (s : Slot) (y : Y) :
    pairInputs u w φ ψ F ω ω' s (g y) =
      pairInputs u w (fun e o y => φ e o (g y)) (fun e o y => ψ e o (g y)) (F ∘ g) ω ω' s y := by
  unfold pairInputs halfInput
  split_ifs <;> rfl

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- **The paper's inputs on the block labels are cyclic inputs** (`def:record:functional`(f)):
`g^{I_b, M₀, s}(crt y) = indexedInput crtModuli … y`. -/
theorem blockInput_crtLabel (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) {E : Type} (e : E) (η : ∀ j, CoordSpace blockScale pr h j)
    (y : ResidueSpace (crtModuli m₀ blk p L)) :
    blockInput m₀ blk p pr h hcop L A e η (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      indexedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) blockScale L
        (modulus pr h) A ((crtEquiv blockScale pr h hcop).symm η) y := by
  unfold blockInput atomInput indexedInput
  congr 1
  unfold input
  exact lift_comp_eq (joinModuli m₀ (p L)) (crtModuli m₀ blk p L) hpair
    (crtModuli_pairwise blk hpair) (prod_crtModuli blk L).symm
    (fun y => blockGroupEquiv m₀ blk p L (crtLabelEquiv blk (prefix_pairwise hpair) L y))
    (blockGroupEquiv_crtLabel_integerResidue blk (prefix_pairwise hpair) L) _ _ _ y

variable {a : ℝ} {E : Type} [Fintype E] [DecidableEq E]

/-- The revealed slot functions of `EnvelopeEnergyInputs` on the cyclic coordinates: the cyclic
inputs `indexedInput crtModuli` with the conditional expectation of the depth vector applied to
their index. -/
noncomputable def revealedInputCRT (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    ℝ :=
  ((piKron fun j => (D.index.C e j).cond (Jq e j)) *ᵥ
    (fun η' => indexedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) blockScale L
      (modulus pr h) A ((crtEquiv blockScale pr h hcop).symm η') y)) η

/-- The revealed inputs on the block labels are `revealedInputCRT`. -/
theorem revealedInput_crtLabel (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    EnvelopeInputsBlock.revealedInput hcop D L A Jq e η
        (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      revealedInputCRT blk hcop D L A Jq e η y := by
  unfold EnvelopeInputsBlock.revealedInput revealedInputCRT
  congr 2
  funext η'
  exact blockInput_crtLabel blk hcop L hpair A e η' y

/-- **A pair-input energy on the block atoms is a pair-input energy on the cyclic coordinates**:
for every block-atom law `⊗_𝔟 Λ_𝔟` and slot inputs `φ, ψ` on the block labels with cyclic forms
`φ', ψ'` (`φ(crt y) = φ'(y)`), the energy with `F_A` off the query slots is the energy of
`crtLaws Λ` with `φ', ψ'` and `unchangedInput crtModuli`. -/
theorem multilinear_pairInputs_crt (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) {Ωi : Type}
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (u w : E → reservedCut.Half) (φ ψ : E → Ωi → (∀ b, BlockLabel m₀ blk p L b) → ℝ)
    (φ' ψ' : E → Ωi → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
    (hφ : ∀ e o y, φ e o (crtLabelEquiv blk (prefix_pairwise hpair) L y) = φ' e o y)
    (hψ : ∀ e o y, ψ e o (crtLabelEquiv blk (prefix_pairwise hpair) L y) = ψ' e o y)
    (ω ω' : E → Ωi) :
    multilinearIntegral (tensorLaw Λ) (pairInputs u w φ ψ (blockLift m₀ blk p L A) ω ω') =
      multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (pairInputs u w φ' ψ' (unchangedInput (crtModuli m₀ blk p L)
          (paperCutoff (blockScale * L)) A L) ω ω') := by
  rw [multilinearIntegral_crt blk (prefix_pairwise hpair) L Λ]
  congr 1
  funext s y
  rw [pairInputs_comp]
  have e1 : (fun e o y => φ e o (crtLabelEquiv blk (prefix_pairwise hpair) L y)) = φ' :=
    funext fun e => funext fun o => funext fun y => hφ e o y
  have e2 : (fun e o y => ψ e o (crtLabelEquiv blk (prefix_pairwise hpair) L y)) = ψ' :=
    funext fun e => funext fun o => funext fun y => hψ e o y
  have e3 : (blockLift m₀ blk p L A ∘ crtLabelEquiv blk (prefix_pairwise hpair) L) =
      unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L :=
    funext fun y => blockLift_crtLabel blk L hpair A y
  rw [e1, e2, e3]

/-- **The energies of `EnvelopeEnergyInputs.htermL/R` in cyclic coordinates**
(`lem:envelope-energy`): for every block-atom law and every depth vector `𝒥`, the revealed
pair-input energy on the block atoms equals the energy of `crtLaws Λ` with the cyclic revealed
inputs `revealedInputCRT` and `unchangedInput crtModuli`. -/
theorem env_term_crt (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (u : E → reservedCut.Half) (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    multilinearIntegral (tensorLaw Λ)
        (pairInputs u u (EnvelopeInputsBlock.revealedInput hcop D L A Jq)
          (EnvelopeInputsBlock.revealedInput hcop D L A Jq) (blockLift m₀ blk p L A) ω ω) =
      multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (pairInputs u u (revealedInputCRT blk hcop D L A Jq) (revealedInputCRT blk hcop D L A Jq)
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) :=
  multilinear_pairInputs_crt blk L hpair A Λ u u _ _ _ _
    (fun e o y => revealedInput_crtLabel blk hcop D L hpair A Jq e o y)
    (fun e o y => revealedInput_crtLabel blk hcop D L hpair A Jq e o y) ω ω

/-- The fixed-interval inputs of the wrapping terms on the cyclic coordinates: the cyclic input
with interval coordinate `t` (`t = 0` for the sources, `1` for the targets) for `e ∈ 𝒮`,
`unchangedInput crtModuli` otherwise. -/
noncomputable def wrapInputCRT (L : ℕ) (A : Finset ℤ) (S : Finset E) (t : ZMod blockScale)
    (e : E) (η : ∀ j, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    ℝ :=
  if e ∈ S then indexedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) blockScale L
      (modulus pr h) A ((crtEquiv blockScale pr h hcop).symm
        (Function.update η none (t : CoordSpace blockScale pr h none))) y
  else unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L y

omit [∀ q, NeZero (pr q ^ h q)] [Fintype E] in
theorem wrapSourceInput_crtLabel (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (S : Finset E) (e : E) (η : ∀ j, CoordSpace blockScale pr h j)
    (y : ResidueSpace (crtModuli m₀ blk p L)) :
    TheoremCBlock.wrapSourceInput m₀ blk p pr h hcop L A S e η
        (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      wrapInputCRT blk hcop L A S 0 e η y := by
  unfold TheoremCBlock.wrapSourceInput wrapInputCRT
  split_ifs
  · exact blockInput_crtLabel blk hcop L hpair A e _ y
  · exact blockLift_crtLabel blk L hpair A y

omit [∀ q, NeZero (pr q ^ h q)] [Fintype E] in
theorem wrapTargetInput_crtLabel (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (S : Finset E) (e : E) (η : ∀ j, CoordSpace blockScale pr h j)
    (y : ResidueSpace (crtModuli m₀ blk p L)) :
    TheoremCBlock.wrapTargetInput m₀ blk p pr h hcop L A S e η
        (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      wrapInputCRT blk hcop L A S 1 e η y := by
  unfold TheoremCBlock.wrapTargetInput wrapInputCRT
  split_ifs
  · exact blockInput_crtLabel blk hcop L hpair A e _ y
  · exact blockLift_crtLabel blk L hpair A y

/-- **The energies of `FixedIntervalInputs.htermL` in cyclic coordinates** (`lem:envelope-energy` at
fixed intervals): the revealed fixed-interval source energy on the block atoms equals the energy of
`crtLaws Λ` with the cyclic inputs `wrapInputCRT … 0`. -/
theorem fix_term_crt_source (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (S : Finset E)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (u : E → reservedCut.Half)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    multilinearIntegral (tensorLaw Λ)
        (pairInputs u u
          (EnvelopeInputs.revealedSlot Jq (TheoremCBlock.wrapSourceInput m₀ blk p pr h hcop L A S))
          (EnvelopeInputs.revealedSlot Jq (TheoremCBlock.wrapSourceInput m₀ blk p pr h hcop L A S))
          (blockLift m₀ blk p L A) ω ω) =
      multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (pairInputs u u (EnvelopeInputs.revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
          (EnvelopeInputs.revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) := by
  have hφ : ∀ e o y, EnvelopeInputs.revealedSlot Jq
      (TheoremCBlock.wrapSourceInput m₀ blk p pr h hcop L A S) e o
        (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      EnvelopeInputs.revealedSlot Jq (wrapInputCRT blk hcop L A S 0) e o y := by
    intro e o y
    unfold EnvelopeInputs.revealedSlot
    congr 2
    funext η'
    exact wrapSourceInput_crtLabel blk hcop L hpair A S e η' y
  exact multilinear_pairInputs_crt blk L hpair A Λ u u _ _ _ _ hφ hφ ω ω

/-- The same for the targets (`FixedIntervalInputs.htermR`), with `wrapInputCRT … 1`. -/
theorem fix_term_crt_target (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (S : Finset E)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (u : E → reservedCut.Half)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1))
    (ω : E → ∀ j : Option P, CoordSpace blockScale pr h j) :
    multilinearIntegral (tensorLaw Λ)
        (pairInputs u u
          (EnvelopeInputs.revealedSlot Jq (TheoremCBlock.wrapTargetInput m₀ blk p pr h hcop L A S))
          (EnvelopeInputs.revealedSlot Jq (TheoremCBlock.wrapTargetInput m₀ blk p pr h hcop L A S))
          (blockLift m₀ blk p L A) ω ω) =
      multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (pairInputs u u (EnvelopeInputs.revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
          (EnvelopeInputs.revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
          (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) := by
  have hφ : ∀ e o y, EnvelopeInputs.revealedSlot Jq
      (TheoremCBlock.wrapTargetInput m₀ blk p pr h hcop L A S) e o
        (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      EnvelopeInputs.revealedSlot Jq (wrapInputCRT blk hcop L A S 1) e o y := by
    intro e o y
    unfold EnvelopeInputs.revealedSlot
    congr 2
    funext η'
    exact wrapTargetInput_crtLabel blk hcop L hpair A S e η' y
  exact multilinear_pairInputs_crt blk L hpair A Λ u u _ _ _ _ hφ hφ ω ω

end Sarkozy.EnvelopeEnergiesPaper

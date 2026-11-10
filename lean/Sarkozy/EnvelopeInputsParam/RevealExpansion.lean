module

public import Sarkozy.EnvelopeInputs.RevealExpansion
public import Sarkozy.EnvelopeInputsParam.ConductorPrice
public import Sarkozy.TheoremCParam.Cancellation

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.EnvelopeInputsParam

open Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The revealed slot function of the query `e`: the input `g^{I,M₀,·}` of `e` with the
conditional expectation `⊗_j E_{e,j,𝒥_{e,j}}` applied to its index (`X^𝒥` at `u_e`). -/
noncomputable def revealedInput (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ)
    (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (x : ∀ b, AtomLabel m₀ p L b) : ℝ :=
  ((piKron fun j => (D.index.C e j).cond (Jq e j)) *ᵥ
    (fun η' => atomInput m₀ p pr h hcop L A e η' x)) η

/-- **The revealed source half-function is a product half-function** with the revealed slot
functions at the sources `u_e` and `F_A` elsewhere. -/
theorem revealL_eq_productHalf (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ)
    (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) :
    TheoremCParam.Structured.revealL hcop D L A Jq =
      productHalf D.index.u (revealedInput hcop D L A Jq) (atomLift m₀ p L A) := by
  unfold TheoremCParam.Structured.revealL queryReveal
  rw [act_productHalf]
  rfl

/-- The revealed target half-function is a product half-function at the targets `w_e`. -/
theorem revealR_eq_productHalf (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ)
    (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) :
    TheoremCParam.Structured.revealR hcop D L A Jq =
      productHalf D.index.w (revealedInput hcop D L A Jq) (atomLift m₀ p L A) := by
  unfold TheoremCParam.Structured.revealR queryReveal
  rw [act_productHalf]
  rfl

/-- **The energy of the revealed source half-function** (`eq:cc:bilinear`): a multilinear
integral with the slot inputs `pairInputs` (the revealed input of `e` at `u_e` and at `ι u_e`,
`F_A` elsewhere). -/
theorem form_revealL (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (M : ((Slot → ∀ b, AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) :
    reservedCut.form M (TheoremCParam.Structured.revealL hcop D L A Jq ω)
        (TheoremCParam.Structured.revealL hcop D L A Jq ω) =
      multilinearIntegral M (pairInputs D.index.u D.index.u (revealedInput hcop D L A Jq)
        (revealedInput hcop D L A Jq) (atomLift m₀ p L A) ω ω) := by
  rw [revealL_eq_productHalf]
  exact form_productHalf M D.index.hu D.index.hu _ _ _ ω ω

/-- The energy of the revealed target half-function. -/
theorem form_revealR (D : TheoremCParam.ComparisonData a m₀ p pr h E) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)
    (M : ((Slot → ∀ b, AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) :
    reservedCut.form M (TheoremCParam.Structured.revealR hcop D L A Jq ω)
        (TheoremCParam.Structured.revealR hcop D L A Jq ω) =
      multilinearIntegral M (pairInputs D.index.w D.index.w (revealedInput hcop D L A Jq)
        (revealedInput hcop D L A Jq) (atomLift m₀ p L A) ω ω) := by
  rw [revealR_eq_productHalf]
  exact form_productHalf M D.index.hw D.index.hw _ _ _ ω ω

open Classical in
omit [DecidableEq E] in
/-- **At most `2k` changed slots** (item 5): the slots where the input of a pair of product
half-functions at the same slots `u` differs from `F` are among the `2k` endpoints `u_e`, `ι u_e`.
So for `k ≤ 35` queries `#changed · ϑ/72 ≤ 1` (WP-S's `TraceMixing.few_of_card_le_seventy`), and
WP-S's `density_structured_theta_few` needs no two-occurrence or independence hypothesis. -/
theorem card_changed_le {Ωi X : Type} (u : E → reservedCut.Half) (φ : E → Ωi → X → ℝ)
    (F : X → ℝ) (ω : E → Ωi) :
    (univ.filter fun s : Slot => pairInputs u u φ φ F ω ω s ≠ F).card ≤
      2 * Fintype.card E := by
  have hsub : (univ.filter fun s : Slot => pairInputs u u φ φ F ω ω s ≠ F) ⊆
      univ.image (fun e => (u e).1) ∪ univ.image (fun e => reservedCut.flip (u e).1) := by
    intro s hs
    rw [mem_filter] at hs
    by_contra hns
    rw [mem_union, mem_image, mem_image] at hns
    push Not at hns
    exact hs.2 (pairInputs_self_eq_lift u φ F ω s (fun e he => hns.1 e (mem_univ e) he.symm)
      (fun e he => hns.2 e (mem_univ e) he.symm))
  calc (univ.filter fun s : Slot => pairInputs u u φ φ F ω ω s ≠ F).card
      ≤ (univ.image (fun e => (u e).1) ∪ univ.image (fun e => reservedCut.flip (u e).1)).card :=
        card_le_card hsub
    _ ≤ (univ.image (fun e => (u e).1)).card +
          (univ.image (fun e => reservedCut.flip (u e).1)).card := card_union_le _ _
    _ ≤ Fintype.card E + Fintype.card E := add_le_add card_image_le card_image_le
    _ = 2 * Fintype.card E := by ring

/-- **`EnvelopeEnergies` from bounds on multilinear integrals with explicit slot inputs**
(`lem:envelope-energy`, `lem:hyb:moment`): `envelopeEnergies_of_conductor` with the per-term
bounds stated for `∫ ∏_s G_s(z_s) d(⊗_𝔟 (f_𝔟 ? Q_𝔟 : Ñ_𝔟))`, `G = pairInputs` of the revealed
slot functions (`form_revealL`, `form_revealR`). -/
theorem envelopeEnergies_of_inputs (D : TheoremCParam.ComparisonData a m₀ p pr h E)
    (ha : 0 ≤ a) (hRI : IndexMomentBound D)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rL rR : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ)
    (htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral
          (tensorLaw fun b => if f b then TheoremCParam.Structured.envIncL D L b else D.GB.N L b)
          (pairInputs D.index.u D.index.u (revealedInput hcop D L A Jq)
            (revealedInput hcop D L A Jq) (atomLift m₀ p L A) ω ω)| ≤
        (D.B + z L) * conductorPrice pr h (priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.envPriceL D L b else 1) + rL L A Jq ω f))
    (htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral
          (tensorLaw fun b => if f b then TheoremCParam.Structured.envIncR D L b else D.GB.N L b)
          (pairInputs D.index.w D.index.w (revealedInput hcop D L A Jq)
            (revealedInput hcop D L A Jq) (atomLift m₀ p L A) ω ω)| ≤
        (D.B + z L) * conductorPrice pr h (priceExponent a) Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.envPriceR D L b else 1) + rR L A Jq ω f))
    (hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A Jq ω f)) ≤ remainder c L A))
    (hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A Jq ω f)) ≤ remainder c L A)) :
    D.EnvelopeEnergies hcop := by
  refine envelopeEnergies_of_conductor hcop D ha hRI z hz0 hzt hc rL rR ?_ ?_ hremL hremR
  · filter_upwards [htermL] with L hL
    intro C hC hk A hA hY Jq ω f
    rw [form_revealL]
    exact hL C hC hk A hA hY Jq ω f
  · filter_upwards [htermR] with L hL
    intro C hC hk A hA hY Jq ω f
    rw [form_revealR]
    exact hL C hC hk A hA hY Jq ω f

/-- **`FixedIntervalEnvelopeEnergies` from bounds on multilinear integrals with explicit slot
inputs** (`lem:envelope-energy` at fixed intervals, `lem:hyb:moment`):
`fixedIntervalEnvelopeEnergies_of_conductor` with the revealed fixed-interval half-functions
unfolded (`queryReveal_productHalf`, `TheoremC.form_productHalf`). The slot inputs are the
revealed fixed-interval inputs at `u_e` and `ι u_e` (resp. `w_e`, `ι w_e`), `F_A` elsewhere. -/
theorem fixedIntervalEnvelopeEnergies_of_inputs (D : TheoremCParam.ComparisonData a m₀ p pr h E)
    (ha : 0 ≤ a) (hRI : IndexMomentBound D)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rL rR : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ)
    (htermL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral
          (tensorLaw fun b => if f b then TheoremCParam.Structured.wrapInc D L b else D.GB.N L b)
          (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapSourceInput m₀ p pr h hcop L A S))
            (revealedSlot Jq (wrapSourceInput m₀ p pr h hcop L A S)) (atomLift m₀ p L A)
            ω ω)| ≤
        (D.B + z L) * fixedPrice pr h (priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.wrapPrice D L b else 1) + rL L A S Jq ω f))
    (htermR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : PaperAtom J L → Bool),
      |multilinearIntegral
          (tensorLaw fun b => if f b then TheoremCParam.Structured.wrapInc D L b else D.GB.N L b)
          (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapTargetInput m₀ p pr h hcop L A S))
            (revealedSlot Jq (wrapTargetInput m₀ p pr h hcop L A S)) (atomLift m₀ p L A)
            ω ω)| ≤
        (D.B + z L) * fixedPrice pr h (priceExponent a) S Jq * D.Y L A *
          ∏ b, (if f b then TheoremCParam.Structured.wrapPrice D L b else 1) + rR L A S Jq ω f))
    (hremL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rL L A S Jq ω f)) ≤ remainder c L A))
    (hremR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rR L A S Jq ω f)) ≤ remainder c L A)) :
    D.FixedIntervalEnvelopeEnergies hcop := by
  refine fixedIntervalEnvelopeEnergies_of_conductor hcop D ha hRI z hz0 hzt hc rL rR ?_ ?_ hremL
    hremR
  · filter_upwards [htermL] with L hL
    intro C hC hk A hA hY S hS Jq ω f
    unfold wrapSourceHalf
    rw [queryReveal_productHalf, form_productHalf _ D.S.Q.hu D.S.Q.hu]
    exact hL C hC hk A hA hY S hS Jq ω f
  · filter_upwards [htermR] with L hL
    intro C hC hk A hA hY S hS Jq ω f
    unfold wrapTargetHalf
    rw [queryReveal_productHalf, form_productHalf _ D.S.Q.hw D.S.Q.hw]
    exact hL C hC hk A hA hY S hS Jq ω f

end Sarkozy.EnvelopeInputsParam

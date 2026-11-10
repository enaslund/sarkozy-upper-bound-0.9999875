module

public import Sarkozy.PartVRecords.MergeMarginals
public import Sarkozy.PartVRecords.OneStageSym

@[expose] public section

/-!
# Sanity checks: the new hypothesis bundles are jointly satisfiable

Toy instances (WORKER_GUIDE rule 9) for the hypotheses introduced in `Sarkozy.PartVRecords`:

* `toyFrame` (labels in `Unit`, all inputs `0`, all weights `1`, `r = 1/2`, `b = 5`) satisfies
  **every hypothesis of `FrameData.gram_cp3`** at once: the layer caps (V1's `MiddleLayerCaps`),
  `v_𝔱 ≥ k_𝔱 w_𝔱`, the protection, the new `MatchingReservedBound`, the layer-swap invariance and
  the uniform vertex marginals (`toyFrame_gram_cp3`). With one label every measure of nonnegative
  mass is positive at every cut (`unit_positive`), so this checks consistency only, not the paper's
  spectral inputs (which are the content of `sec:frontier:empty-triple-negative`(c) and
  `lem:front12:reference`(ii)).
* `toySignedComponents_valid`: `SignedComponents.Valid` holds for one-label halves with the
  constant density `1`, so `Ksigned_mass` and its companions apply non-vacuously.
* `toyFrame_repair`: the reference record of `E₀` is a repair of itself (`FrameData.IsRepair`).
* Non-vacuity of the replacement laws themselves is by construction: `plusLaw` and
  `blockPlusLaw` are defined for every block of class-three primes `p ≥ 7`, and `firstLaw` at
  every odd prime; the mirror law needs `Inj_p(mirrorGraph) ≠ ∅`, which holds for large `p`
  under H1 by V1's `exists_injLabellings_nonempty`.
* The tail bundle `AcceptedTailData` has the instance `rootAcceptedTailData` in
  `Sarkozy.PartVRecords.TailMixing`.
* The one-prime hypotheses of `OneStage`, `OneStageNorms`, `OneStageDelta` (`ringChar ≠ 2`,
  `q ≡ 3 (mod 4)`, `k > 0`) hold for `ZMod 7`, and those of `OneStageSym` (`q ≥ 11`) for `ZMod 11`
  (`zmod7_hyps`, `zmod11_hyps`); the mirror-edge law exists at `p = 7`
  (`mirror_nonempty_seven`, the labelling `(x₀, x₁, y₀, y₁) = (0, 3, 4, 1)`).
* `ClassThreeBlock` holds for the block of the single prime `7` (`classThree_seven`), so
  `blockPlusLaw` and its theorems apply to a concrete block.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC Sarkozy.Comparison

/-- With one label, a measure is its mass times the evaluation at the unique labelling. -/
theorem unit_apply (L : SlotMeasure Unit) (f : (Slot → Unit) → ℝ) :
    L f = f (fun _ => ()) * L (fun _ => 1) := by
  have h : f = f (fun _ => ()) • (fun _ : Slot → Unit => (1 : ℝ)) := by
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, mul_one]
  conv_lhs => rw [h]
  rw [map_smul, smul_eq_mul]

/-- **With one label, every measure of nonnegative mass is positive at every cut.** -/
theorem unit_positive (c : ReflectionCut Slot) (L : SlotMeasure Unit) (hL : 0 ≤ L (fun _ => 1)) :
    c.Positive L := by
  constructor
  · intro F G
    unfold ReflectionCut.form
    rw [unit_apply L, unit_apply L (fun z => G (fun v => z v.1) * F (fun v => z (c.flip v.1)))]
    ring
  · intro F
    unfold ReflectionCut.form
    rw [unit_apply]
    exact mul_nonneg (mul_self_nonneg _) hL

/-- The toy field laws: the unique law on one-label configurations. -/
noncomputable def toyF : MiddleFieldLaws Unit where
  two _ := FiniteLaw.uniform _
  one _ := FiniteLaw.uniform _

/-- The toy weights: all `1`. -/
def toyW : MiddleWeights where
  w _ := 1
  v _ := 1
  w_L := rfl
  w_nonneg _ := zero_le_one
  v_nonneg _ := zero_le_one

/-- The toy inputs: all `0`. -/
def toyI : MiddleInputs where
  d := 0
  d₁ := 0
  f₁ := 0
  f₂ := 0
  h₁ := 0
  h₂ := 0
  k _ := 0

/-- **The toy frame.** -/
noncomputable def toyFrame : FrameData Unit where
  F := toyF
  W := toyW
  I := toyI
  r := 1 / 2
  r_nonneg := by norm_num
  b := 5
  κnew := FiniteLaw.uniform _

theorem law_mass_one {Ω : Type} [Fintype Ω] (μ : FiniteLaw Ω) :
    signedIntegral μ.weight (fun _ => 1) = 1 := μ.expect_const 1

/-- **All hypotheses of `gram_cp3` hold for the toy frame**, so its conclusion does. -/
theorem toyFrame_gram_cp3 :
    (∀ i, IsPositiveRecord (toyFrame.bracketRec i)) ∧
      (∀ i, IsDiagonalAt reservedCut (toyFrame.bracketRec i)) ∧
      toyFrame.Nbr0 - toyFrame.mu = ∑ i, toyFrame.bracketRec i ∧
      Sarkozy.RecordExpansion.IsSymmetricAt reservedCut toyFrame.lam ∧
      toyFrame.Nbr = toyFrame.Nbr0 + toyFrame.deltaE ∧
      IsNonneg (toyFrame.Nbr0 + toyFrame.deltaE) ∧
      reservedCut.Bracket (toyFrame.Nbr0 + toyFrame.deltaE) toyFrame.lam
        (toyFrame.Nbr0 + toyFrame.deltaE) := by
  refine toyFrame.gram_cp3 (by norm_num [toyFrame, toyI]) (by norm_num [toyFrame]) ?_ ?_ ?_ ?_ ?_ ?_
  · intro t φ
    apply unit_positive
    change 0 ≤ signedIntegral _ (fun _ => 1) - (-(0 * (1 / 2 : ℝ))) * signedIntegral _ (fun _ => 1)
    rw [law_mass_one, law_mass_one]
    norm_num
  · intro t
    change (0 : ℝ) * 1 ≤ 1
    norm_num
  · change 2 * (0 : ℝ) * 1 ≤ 1
    norm_num
  · intro s
    apply unit_positive
    change 0 ≤ signedIntegral _ (fun _ => 1) + 3 / ((5 : ℝ) - 3) * signedIntegral _ (fun _ => 1)
    rw [law_mass_one, law_mass_one]
    norm_num
  · intro f H
    apply FiniteLaw.expect_congr
    intro y
    rfl
  · intro f o g
    rw [FiniteLaw.expect_uniform]
    have : (fun y : f.Obj × Fin 1 → Unit => g (y o)) = fun _ => g () := rfl
    rw [this, FiniteLaw.expect_const]
    simp

/-- **`SignedComponents.Valid` is satisfiable**: one-label halves with the constant density `1`. -/
theorem toySignedComponents_valid :
    (SignedComponents.Valid (ι := Unit) (H := fun _ => Unit)
      ⟨fun _ => FiniteLaw.uniform Unit, fun _ _ _ => 1, fun _ _ _ => 1, fun _ _ _ => 1⟩) := by
  intro i
  have h : IsMarginalDensity (FiniteLaw.uniform Unit) (fun _ _ => (1 : ℝ)) :=
    ⟨fun _ _ => zero_le_one, fun _ => by simp [FiniteLaw.uniform],
      fun _ => by simp [FiniteLaw.uniform]⟩
  exact ⟨h, h, h⟩

/-- **`FrameData.IsRepair` is satisfiable**: in the toy frame the reference record of `E₀` is a
repair of itself (one component, coefficient one). -/
theorem toyFrame_repair : toyFrame.IsRepair (fun _ => True) .E0 (toyFrame.refRec .E0) := by
  refine ⟨law_mass_one _, 1, fun _ => 1, fun _ => toyFrame.refRec .E0, ?_, fun _ => ?_⟩
  · simp
  · refine ⟨toyFrame.refRec_isProbability _, trivial, rfl, ?_⟩
    funext x
    unfold halfMarginalMinus FrameData.halfLaw halfMarginalPlus
    congr 1

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The one-prime hypotheses hold at `p = 7`. -/
theorem zmod7_hyps :
    ringChar (ZMod 7) ≠ 2 ∧ Fintype.card (ZMod 7) % 4 = 3 ∧ 0 < kP (ZMod 7) := by
  refine ⟨by rw [ZMod.ringChar_zmod_n]; norm_num, by rw [ZMod.card], ?_⟩
  apply kP_pos
  rw [ZMod.card]

/-- The hypotheses of `abs_form_Dop_le` hold at `p = 11`. -/
theorem zmod11_hyps :
    ringChar (ZMod 11) ≠ 2 ∧ Fintype.card (ZMod 11) % 4 = 3 ∧ 0 < kP (ZMod 11) ∧
      11 ≤ Fintype.card (ZMod 11) := by
  refine ⟨by rw [ZMod.ringChar_zmod_n]; norm_num, by rw [ZMod.card], ?_, by rw [ZMod.card]⟩
  apply kP_pos
  rw [ZMod.card]
  norm_num

/-- **The mirror-edge law exists at `p = 7`**: `(x₀, x₁, y₀, y₁) = (0, 3, 4, 1)` has `x₁ → y₀`
(`4 - 3 = 1`) and `x₀ → y₁` (`1 - 0 = 1`). -/
theorem mirror_nonempty_seven : (injLabellings (ZMod 7) mirrorGraph).Nonempty := by
  refine ⟨quadConfig ((0 : ZMod 7), (3 : ZMod 7), (4 : ZMod 7), (1 : ZMod 7)),
    (mem_inj_mirror_iff _).mpr ⟨by decide, by decide, by decide, by decide, ?_, ?_⟩⟩
  · change quadraticChar (ZMod 7) ((4 : ZMod 7) - 3) = 1
    rw [show (4 : ZMod 7) - 3 = 1 by decide, map_one]
  · change quadraticChar (ZMod 7) ((1 : ZMod 7) - 0) = 1
    rw [show (1 : ZMod 7) - 0 = 1 by decide, map_one]

/-- **`ClassThreeBlock` is satisfiable**: the block of the single prime `7`. -/
theorem classThree_seven : ClassThreeBlock (fun _ : Unit => 7) :=
  ⟨fun _ => rfl, fun _ => le_refl _⟩

end Sarkozy.PartVRecords

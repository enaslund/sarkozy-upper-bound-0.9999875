module

public import Sarkozy.PartVLaws.TailRP

@[expose] public section

/-!
# The upper block laws are reflection positive (`lem:upper-reference-rp`)

`paper/sections/25_upper_reference.tex`, `def:upper-reference`, `subsec:upper-reference-rp`,
`lem:upper-reference-rp`.

For a block `𝔅` of primes the field laws are the tensors `λ_𝔅(G) = ⊗_{p ∈ 𝔅} λ_p(G)`
(`blockGraphLaw`). A block labelling is charged exactly when each prime component is an
injective strict-square labelling (`blockGraphLaw_weight_ne_zero`), so the extension property
holds prime by prime (`blockLaws_suppExt`), under Weil's bound at every prime of the block and
`p ≥ 2²⁰` (every upper block lies above `P₃ = 167·2⁴⁰`).

**Headline.** `upperBlockReference_familyPositive`: the upper block reference with weights
satisfying `WeightsOK` and valid inputs (V1)–(V3) (`ValidInputs`, the spectral inputs of
`lem:upper-reference-rp`(ii), as a hypothesis) is reflection positive at every cut of `𝔉`; with
V1's `upperBlockReference_uniform` and `upperBlockReference_affine` this is (R1)–(R3) for the upper
blocks (`upperBlock_R1R3`), the conclusion of `lem:upper-reference-rp`(ii) given (i)'s inputs.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The support of a block law**: a block labelling is charged exactly when every prime
component is an injective strict-square labelling. -/
theorem blockGraphLaw_weight_ne_zero {W : Type} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (z : W → BlockLabel pr) :
    (blockGraphLaw pr G hne).weight z ≠ 0 ↔
      ∀ i, (fun w => z w i) ∈ injLabellings (ZMod (pr i)) G := by
  unfold blockGraphLaw
  rw [tensor_weight, Finset.prod_ne_zero_iff]
  exact ⟨fun h i => (graphLaw_weight_ne_zero _ _ _).mp (h i (mem_univ i)),
    fun h i _ => (graphLaw_weight_ne_zero _ _ _).mpr (h i)⟩

/-- The block laws `λ_𝔅(G_{φ₀φ₁})`. -/
noncomputable def blockLaws {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']
    (hne : ∀ f₀ f₁ i, (injLabellings (ZMod (pr i)) (fieldGraph f₀ f₁ Λ')).Nonempty)
    (f₀ f₁ : FType) : FiniteLaw (f₀.Obj × f₁.Obj × Λ' → BlockLabel pr) :=
  blockGraphLaw pr (fieldGraph f₀ f₁ Λ') (hne f₀ f₁)

theorem blockLaws_graphInv {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']
    (hne : ∀ f₀ f₁ i, (injLabellings (ZMod (pr i)) (fieldGraph f₀ f₁ Λ')).Nonempty) :
    GraphInv (blockLaws pr hne) :=
  fun _ _ π hπ g => blockGraphLaw_expect_auto pr _ _ π hπ g

/-- **The extension property of the block laws**, prime by prime, under Weil's bound at every
prime of the block, all primes being at least `2²⁰`. -/
theorem blockLaws_suppExt (hW : ∀ i, WeilBound (ZMod (pr i))) (hp : ∀ i, (2 : ℝ) ^ 20 ≤ pr i)
    {Λ' : Type} [Fintype Λ'] [DecidableEq Λ'] (hΛ : LayerOK Λ')
    (hne : ∀ f₀ f₁ i, (injLabellings (ZMod (pr i)) (fieldGraph f₀ f₁ Λ')).Nonempty) :
    SuppExt (blockLaws pr hne) where
  left f y hy j hj := by
    have hy' := (blockGraphLaw_weight_ne_zero pr _ _ y).mp hy
    choose z hz hzy using fun i => extend_left (pr i) (hW i) (hp i) hΛ f _ (hy' i) j hj
    refine ⟨fun w i => z i w, (blockGraphLaw_weight_ne_zero pr _ _ _).mpr hz, fun w hw => ?_⟩
    funext i
    exact hzy i w hw
  right f y hy j hj := by
    have hy' := (blockGraphLaw_weight_ne_zero pr _ _ y).mp hy
    choose z hz hzy using fun i => extend_right (pr i) (hW i) (hp i) hΛ f _ (hy' i) j hj
    refine ⟨fun w i => z i w, (blockGraphLaw_weight_ne_zero pr _ _ _).mpr hz, fun w hw => ?_⟩
    funext i
    exact hzy i w hw

/-- **The row data of an upper block form five-type data** (`subsec:upper-rows`), at every block
of primes `≥ 2²⁰` under Weil's bound. -/
theorem block_upperDatumHyp (hW : ∀ i, WeilBound (ZMod (pr i))) (hp : ∀ i, (2 : ℝ) ^ 20 ≤ pr i)
    (hne : UpperNonempty pr) : UpperDatumHyp (upperBlockFieldLaws pr hne) :=
  upperDatumHyp_of (upperBlockFieldLaws pr hne) (blockLaws_graphInv pr hne.two)
    (blockLaws_graphInv pr hne.one) (blockLaws_suppExt pr hW hp layerOK_two hne.two)
    (blockLaws_suppExt pr hW hp layerOK_one hne.one)

/-- **`lem:upper-reference-rp`(i) for the paper's upper blocks**: if the weights satisfy the gates
(`WeightsOK`) and the inputs are valid on the block (`ValidInputs`, (V1)–(V3)), the upper block
reference is reflection positive at every cut of `𝔉`. -/
theorem upperBlockReference_familyPositive (hW : ∀ i, WeilBound (ZMod (pr i)))
    (hp : ∀ i, (2 : ℝ) ^ 20 ≤ pr i) (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ}
    (hr : 0 < r) {ord res : FieldTy → CompletionInput} {k : PType → PType → ℝ}
    (hWOK : WeightsOK W ord res k)
    (hV : ValidInputs (upperBlockFieldLaws pr hne) (block_upperDatumHyp pr hW hp hne) r ord res k) :
    TheoremC.FamilyReflectionPositive
      (signedIntegral (upperBlockReference pr hne W hr.le).weight) :=
  upperReference_familyPositive (upperBlockFieldLaws pr hne) W hr
    (block_upperDatumHyp pr hW hp hne) hV hWOK

/-- **(R1)–(R3) for an upper block** (`lem:upper-reference-rp`(ii), "every upper block satisfies
(R1)–(R3), with (R2) at every cut of `𝔉`", given the validity of the inputs): reflection
positivity at every cut of `𝔉`, uniform one-slot marginals, square-affine invariance. -/
theorem upperBlock_R1R3 (hW : Target.Weil) (hp : ∀ i, (2 : ℝ) ^ 20 ≤ pr i)
    (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ} (hr : 0 < r)
    {ord res : FieldTy → CompletionInput} {k : PType → PType → ℝ} (hWOK : WeightsOK W ord res k)
    (hV : ∀ hW', ValidInputs (upperBlockFieldLaws pr hne) (block_upperDatumHyp pr hW' hp hne) r
      ord res k) :
    TheoremC.FamilyReflectionPositive
        (signedIntegral (upperBlockReference pr hne W hr.le).weight) ∧
      HasUniformMarginals (upperBlockReference pr hne W hr.le) ∧
      ∀ (α β : BlockLabel pr), (∀ i, quadraticChar (ZMod (pr i)) (α i) = 1) →
        ∀ H : (Slot → BlockLabel pr) → ℝ,
          (upperBlockReference pr hne W hr.le).expect (fun z => H (fun v i => α i * z v i + β i)) =
            (upperBlockReference pr hne W hr.le).expect H := by
  have hp2 : ∀ i, pr i ≠ 2 := by
    intro i h
    have := hp i
    rw [h] at this
    norm_num at this
  have hW' : ∀ i, WeilBound (ZMod (pr i)) := fun i => weilBound_of_target hW (pr i) (hp2 i)
  exact ⟨upperBlockReference_familyPositive pr hW' hp hne W hr hWOK (hV hW'),
    upperBlockReference_uniform pr hne W hr.le,
    fun α β hα H => upperBlockReference_affine pr hne W hr.le α β hα H⟩

end Sarkozy.PartVLaws

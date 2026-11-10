module

public import Sarkozy.Param.Primitive
public import Sarkozy.Target

@[expose] public section

/-!
# The endgame at the formal exponent `a₀ = 8896611739/10¹³`

The formalization first targeted the exponent `ε′ = a₀/(72 − ϑ)` with `a₀ = 8896611739/10¹³`
(the paper's middle charge anchor `\FourRoutesAnchor` of `sec:four-routes-closing`) and
`ϑ = 1014587/10⁶` (user decision of 1 November 2026), `Target.epsAnchor ≈ 1.25330·10⁻⁵`.

**Since 7 November 2026 the endgame runs at the baseline `ϑ = 1`** (`Sarkozy.densityExponent`).
The saving of `Params.anchor` is then `anchorSaving = a₀/71 = 8896611739/710000000000000
≈ 1.25304·10⁻⁵`, slightly below `Target.epsAnchor`. The endgame at `a₀` therefore concludes
`Target.SarkozyBound anchorSaving` (names such as `sarkozyBound_epsAnchor_*` are kept for
continuity; their statements are at `anchorSaving`). `anchorSaving` is still above the owner's
round target `Target.epsTarget = 1.2·10⁻⁵` (`sarkozyBound_epsTarget_of_anchorSaving`), and
`1 − anchorSaving < 0.9999875`.

* `Sarkozy.Target.epsAnchor` (`Sarkozy/Target.lean`): the exponent `ε′`, defined there as
  `(8896611739/10¹³)/(72 − 1014587/10⁶)`. `epsAnchor_def` gives its value as one rational.
  `anchor_saving_eq` identifies the saving `a₀/(72 − ϑ) = a₀/71` of `Params.anchor` with
  `anchorSaving`; `anchorSaving_le_epsAnchor` compares the two.
* `sarkozyBound_iff`: `Param.PowerSavingBound P ↔ Target.SarkozyBound P.saving` for all `P`.
* `sarkozyBound_of_closingEstimates`: the parametrized endgame with the conclusion stated as
  `Target.SarkozyBound`, for every `P` with `P.Valid`.
* `sarkozyBound_epsAnchor_of_closingEstimates`: **the endgame at `a₀`**, concluding
  `Target.SarkozyBound anchorSaving`, with the closing number `jointTheta k L₀ J W H < 1` as a
  hypothesis; `_primitive` and `_prefixedModel` forms follow.

As everywhere in the endgame, the closing estimates, the global moment bound and the closing
number (or the ledger) are hypotheses; at `a₀` they are to be supplied by the paper's
`prop:density:production`, `lem:density:restoration`, `lem:density:global-moment` and a closing
certificate at `a₀`.
-/

open Filter
open scoped Topology

namespace Sarkozy.Param

open Sarkozy.Comparison (jointTheta PrimitiveLedger)

/-- **The formal exponent as one rational**: `Target.epsAnchor = a₀/(72 − ϑ)
= 8896611739/709854130000000 ≈ 1.25330·10⁻⁵`, with `a₀ = 8896611739/10¹³` and `ϑ = 1014587/10⁶`.
The proofs below use this equation rather than unfolding `Target.epsAnchor`. -/
theorem epsAnchor_def : Target.epsAnchor = 8896611739 / 709854130000000 := by
  norm_num [Target.epsAnchor]

theorem epsAnchor_eq : Target.epsAnchor = Params.anchorDecay / (72 - 1014587 / 1000000) := by
  norm_num [epsAnchor_def, Params.anchorDecay]

/-- **The saving at the anchor at the baseline `ϑ = 1`**: `a₀/71 = 8896611739/710000000000000
≈ 1.25304·10⁻⁵`. -/
noncomputable def anchorSaving : ℝ := 8896611739 / 710000000000000

/-- The saving of the anchor parameters is `anchorSaving` (at `ϑ = 1`). -/
theorem anchor_saving_eq : Params.anchor.saving = anchorSaving := Params.anchor_saving

/-- At `ϑ = 1` the anchor's saving lies (just) below the old `Target.epsAnchor`, computed at the
upgraded `ϑ = 1014587/10⁶`. -/
theorem anchorSaving_le_epsAnchor : anchorSaving ≤ Target.epsAnchor := by
  norm_num [anchorSaving, epsAnchor_def]

/-- The anchor's saving is above the owner's round target `1.2·10⁻⁵`. -/
theorem epsTarget_le_anchorSaving : Target.epsTarget ≤ anchorSaving := by
  norm_num [anchorSaving, Target.epsTarget]

theorem anchorSaving_pos : 0 < anchorSaving := by norm_num [anchorSaving]

/-- The bound at `anchorSaving` is `N^{1−ε}` with `1 − ε < 0.9999875`. -/
theorem one_sub_anchorSaving_lt : 1 - anchorSaving < 0.9999875 := by
  norm_num [anchorSaving]

theorem epsAnchor_pos : 0 < Target.epsAnchor := by norm_num [epsAnchor_def]

/-- `ε′ < ε`: the formal exponent is below the paper's (`ε′/ε = a₀/a ≈ 0.9808`). -/
theorem epsAnchor_lt_epsPaper : Target.epsAnchor < Target.epsPaper := by
  norm_num [epsAnchor_def, Target.epsPaper]

/-- The bound at `ε′` is `N^{1−ε′}` with `1 − ε′ < 0.9999875`. -/
theorem one_sub_epsAnchor_lt : 1 - Target.epsAnchor < 0.9999875 := by
  norm_num [epsAnchor_def]

/-! ## The conclusion in the target's form -/

/-- `CardinalityBound (1 − ε)` is the target's `SarkozyBound ε`; the definitions differ only in
currying (`Sarkozy.powerSavingBound_iff_target` at a general exponent). -/
theorem cardinalityBound_iff_sarkozyBound (ε : ℝ) :
    CardinalityBound (1 - ε) ↔ Target.SarkozyBound ε := by
  unfold CardinalityBound Target.SarkozyBound Admissible
  constructor
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun N hN A hA hsq => h N hN A ⟨hA, hsq⟩⟩
  · rintro ⟨C, hC, h⟩
    exact ⟨C, hC, fun N hN A hA => h N hN A hA.1 hA.2⟩

theorem sarkozyBound_iff (P : Params) :
    PowerSavingBound P ↔ Target.SarkozyBound P.saving :=
  cardinalityBound_iff_sarkozyBound P.saving

/-- A bound with a larger saving implies the bound with a smaller one. -/
theorem sarkozyBound_mono {ε ε' : ℝ} (hle : ε' ≤ ε) (h : Target.SarkozyBound ε) :
    Target.SarkozyBound ε' := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun N hN A hA hsq => (h N hN A hA hsq).trans ?_⟩
  have hn : (1 : ℝ) ≤ N := by exact_mod_cast hN
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hn (by linarith)) hC.le

theorem anchor_powerSavingBound_iff :
    PowerSavingBound Params.anchor ↔ Target.SarkozyBound anchorSaving := by
  rw [sarkozyBound_iff, anchor_saving_eq]

/-- The rounded form `s(N) ≤ C N^{0.9999875}`. -/
theorem cardinalityBound_rounded_of_epsAnchor (h : Target.SarkozyBound anchorSaving) :
    CardinalityBound 0.9999875 := by
  have h' := (cardinalityBound_iff_sarkozyBound _).mpr
    (sarkozyBound_mono (show 1 - 0.9999875 ≤ anchorSaving by norm_num [anchorSaving]) h)
  simpa only [sub_sub_cancel] using h'

/-! ## The endgame, general exponents, conclusion in the target's form -/

/-- **The parametrized endgame, target form**: for exponents `P` with `P.Valid`, reflection,
the global moment bound and the five robust closing estimates with closing number below one
give `s(N) ≤ C N^{1 − a/(72 − ϑ)}` as `Target.SarkozyBound P.saving` (`thm:density:induction`). -/
theorem sarkozyBound_of_closingEstimates {P : Params} (hP : P.Valid)
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound P Y M) (e : ClosingEstimates P Y k L₀ J W H) :
    Target.SarkozyBound P.saving :=
  (sarkozyBound_iff P).mp
    (powerSavingBound_of_closingEstimates hP hθ hM hreflection hglobal e)

/-! ## The endgame at `a₀` -/

/-- **The endgame at the formal exponent** `a₀`, concluding at `anchorSaving = a₀/71` (before the
switch to `ϑ = 1` on 7 November 2026 the conclusion was at `ε′ = Target.epsAnchor`)
(`thm:density:induction` at `a = a₀`, `ϑ = 1`, `K = 863660`, joint form of
`cor:joint-closing`). For any energy functional `Y` with the reflection lower bound
`α^{72} ≤ Y`, the global moment bound `Y ≤ M L^{1/10000} α²` (`lem:density:global-moment`) and
the five robust closing estimates at the anchor exponents (`thm:record:criterion`), with joint
closing number `Θ = jointTheta k L₀ J W H < 1`: every square-difference-free `A ⊆ [1, N]` has
`|A| ≤ C N^{1−ε′}`.

Hypotheses: `hθ` (the closing number at `a₀`), `hglobal`, `hreflection` and the estimates `e`.
Proved: finite initialization, error absorption (error gate at `a₀`: `Params.anchor_valid`), the
scalar induction and the passage to cardinalities. -/
theorem sarkozyBound_epsAnchor_of_closingEstimates
    {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H M : ℝ}
    (hθ : jointTheta k L₀ J W H < 1) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Params.anchor Y M)
    (e : ClosingEstimates Params.anchor Y k L₀ J W H) :
    Target.SarkozyBound anchorSaving := by
  rw [← anchor_saving_eq]
  exact sarkozyBound_of_closingEstimates Params.anchor_valid hθ hM hreflection hglobal e

/-- The endgame at `ε′` with the primitive ledger of `tab:four-routes-ledger` as the closing
hypothesis. The ledger bounds are the paper's, computed at the record `a`; that the primitive
totals at `a₀` satisfy them is part of the hypothesis `hledger`. -/
theorem sarkozyBound_epsAnchor_of_closingEstimates_primitive
    {Y : ℕ → Finset ℤ → ℝ} {M : ℝ} {l : PrimitiveLedger} (hledger : l.Bounds) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Params.anchor Y M)
    (e : ClosingEstimates Params.anchor Y 6 l.L₀ l.J l.W l.jointConstant) :
    Target.SarkozyBound anchorSaving :=
  sarkozyBound_epsAnchor_of_closingEstimates (l.jointTheta_lt_one hledger) hM hreflection
    hglobal e

/-- The endgame at `ε′` for the prefixed residue model: reflection and the global moment bound
are proved; the closing number and the closing estimates at the anchor are hypotheses. -/
theorem sarkozyBound_epsAnchor_of_prefixedModel
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {C : ℝ} (hC : 0 < C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    {k : ℕ} {L₀ J W H : ℝ} (hθ : jointTheta k L₀ J W H < 1)
    (e : ClosingEstimates Params.anchor (model.toFourierModel p X₀).energy k L₀ J W H) :
    Target.SarkozyBound anchorSaving :=
  anchor_powerSavingBound_iff.mp
    (PrefixedResidueModel.powerSavingBound_of_closingEstimates_theta Params.anchor_valid model ha
      hprefix hzero hm hp hC hmixed hθ e)

/-- **A bound at the anchor's baseline saving gives the round target `N^{0.999988}`**
(`a₀/71 ≥ 1.2·10⁻⁵`). This replaces `Target.sarkozyBound_epsTarget_of_epsAnchor` for the
endgame at `a₀`, `ϑ = 1`. -/
theorem sarkozyBound_epsTarget_of_anchorSaving (h : Target.SarkozyBound anchorSaving) :
    Target.SarkozyBound Target.epsTarget :=
  sarkozyBound_mono epsTarget_le_anchorSaving h

end Sarkozy.Param

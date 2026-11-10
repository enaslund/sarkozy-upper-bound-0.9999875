module

public import Sarkozy.OpsVariance.FoldRestoration

@[expose] public section

/-!
# The structural inputs of `lem:record:restoration` at the paper's middle blocks

`paper/sections/22_variance.tex`, proof of `lem:record:restoration` ("(C) The root carries the
reference", "(B) Contraction and comparison": "the fold chamber `ϑ_{2j}` is a cut of the
family", "the measure `Π_X` is positive and diagonal at `ϑ_{2j}`", "the root `Π^rt` is a
probability coupling at `ϑ_{2j}` with both half marginals `ν`").

`hRes_pointwise` / `hRes_variance` take three structural inputs. At V1's middle frame they are
proved here:

* **`middleReference_split`** (`hmix`): the middle block law is
  `μ_𝔅 = (1 + h_𝔅)⁻¹ (Π^rt_𝔅 + 𝓜_𝔅)`, with `𝓜_𝔅 = ∑_{ρ ≠ root} c_ρ Π_ρ ≥ 0` and
  `h_𝔅 = P(r) − 1` its mass (`w_L = 1`);
* `foldCutA`, `fold_reflect`, **`isDiagonalAt_fold`** (`hd`): the fold record `Π_{F_j}` (emitted
  by `F_{j+1}`) is diagonal at the first-coordinate chamber cut `ϑ_{a_j}`, `a = 2, 1`, whose
  reflection `u ↦ 2a − 1 − u` fixes the pattern; `ϑ_{a_j}` is a cut of the family;
* **`rootMinus_eq_plus_uniform`** (`hplus`, `hminus`): for the uniform root (V1's
  `uniformRoot`, the graph law of `G_L`), the root component has equal half marginals at these
  cuts, because `u ↦ k − u` (`k` odd) is an automorphism of `G_L` (`recordGraph_reflection`).

For the positive roots (`individualBlockRoot`, `coherentBlockRoot`) the equality of the two half
marginals at the fold chambers is not proved here; the paper uses it in step (B).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.RecordExpansion Sarkozy.Variance Sarkozy.Labellings

/-! ## The root split of the middle block law -/

section Split

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The root index `(two-layer, L)`. -/
abbrev rootIdx : MidIdx := (true, ⟨PType.L, ()⟩)

/-- The nonroot part `𝓜_𝔅 = ∑_{ρ ≠ root} c_ρ Π_ρ` of `μ̃_𝔅`. -/
noncomputable def nonroot (F : MiddleFieldLaws X) (W : MiddleWeights) (r : ℝ) :
    ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i ∈ univ.erase rootIdx, midCoeff W r i • signedIntegral (midComponent F i).weight

theorem midCoeff_root (W : MiddleWeights) (r : ℝ) : midCoeff W r rootIdx = 1 := by
  show W.w PType.L * r ^ PType.L.deg = 1
  rw [W.w_L]
  simp [PType.deg]

/-- The nonroot mass `h_𝔅 = P(r) − 1 ≥ 0`. -/
theorem nonroot_mass (W : MiddleWeights) (r : ℝ) :
    ∑ i ∈ univ.erase rootIdx, midCoeff W r i = ∑ i, midCoeff W r i - 1 := by
  rw [← add_sum_erase _ _ (mem_univ rootIdx), midCoeff_root]
  ring

/-- **The root split of the middle block law** (`hmix` of `hRes_pointwise`). -/
theorem middleReference_split (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) :
    signedIntegral (middleReference F W hr).weight =
      (1 + (∑ i, midCoeff W r i - 1))⁻¹ •
        (signedIntegral (midComponent F rootIdx).weight + nonroot F W r) := by
  have hS : 0 < ∑ i, midCoeff W r i := midPoly_pos W hr
  apply LinearMap.ext
  intro f
  rw [add_sub_cancel, LinearMap.smul_apply, LinearMap.add_apply, nonroot, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  have e1 : signedIntegral (middleReference F W hr).weight f =
      ∑ i, (midCoeff W r i / ∑ j, midCoeff W r j) *
        signedIntegral (midComponent F i).weight f := by
    change ∑ z, (∑ i, (midCoeff W r i / ∑ j, midCoeff W r j) * (midComponent F i).weight z) *
      f z = _
    simp only [sum_mul, signedIntegral, LinearMap.coe_mk, AddHom.coe_mk, mul_sum]
    rw [sum_comm]
    exact sum_congr rfl fun i _ => sum_congr rfl fun z _ => by ring
  rw [e1]
  have e2 : signedIntegral (midComponent F rootIdx).weight f +
      ∑ i ∈ univ.erase rootIdx, midCoeff W r i * signedIntegral (midComponent F i).weight f =
      ∑ i, midCoeff W r i * signedIntegral (midComponent F i).weight f := by
    rw [← add_sum_erase _ _ (mem_univ rootIdx), midCoeff_root, one_mul]
  rw [e2, mul_sum]
  exact sum_congr rfl fun i _ => by field_simp

end Split

/-! ## The fold records are diagonal at their fold chambers -/

/-- The fold chamber of `F_{j+1}`: `a = 2` for `F₁` (`u ↦ 3 − u`), `a = 1` for `F₂`
(`u ↦ 1 − u`). -/
def foldCutA : Fin 2 → Chamber := ![2, 1]

theorem fold_reflect (j : Fin 2) (u : ZMod 6) :
    Labellings.fold (MiddleComparison.foldPat j) (chamberReflection (foldCutA j) u) =
      Labellings.fold (MiddleComparison.foldPat j) u := by
  fin_cases j <;> fin_cases u <;> rfl

theorem isFamilyCut_fold (j : Fin 2) : IsFamilyCut (firstChamberCut (foldCutA j)) :=
  Or.inl ⟨_, rfl⟩

section Diag

variable {O X : Type} [Fintype O] [DecidableEq O] [Fintype X] [DecidableEq X]

/-- **An emitted record is diagonal at a first-coordinate chamber cut whose reflection fixes its
pattern.** -/
theorem isDiagonalAt_emit (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O) (a : Chamber)
    (hφ : ∀ u, φ (chamberReflection a u) = φ u) :
    IsDiagonalAt (firstChamberCut a) (signedIntegral (emit lam (midEmission φ)).weight) := by
  intro z hz v
  rw [PaperFrame.lawDensity_signedIntegral] at hz
  change (∑ y, if y ∘ midEmission φ = z then lam.weight y else 0) ≠ 0 at hz
  obtain ⟨y, -, hy⟩ := exists_ne_zero_of_sum_ne_zero hz
  have hyz : y ∘ midEmission φ = z := by
    by_contra hne
    simp [hne] at hy
  rw [← hyz]
  change y (φ (chamberReflection a v.1), layerFin v.2.2) = y (φ v.1, layerFin v.2.2)
  rw [hφ]

end Diag

theorem isDiagonalAt_fold {X : Type} [Fintype X] [DecidableEq X]
    (lam : FiniteLaw (Fin 3 × Fin 2 → X)) (j : Fin 2) :
    IsDiagonalAt (firstChamberCut (foldCutA j))
      (signedIntegral
        (emit lam (midEmission (Labellings.fold (MiddleComparison.foldPat j)))).weight) :=
  isDiagonalAt_emit lam _ _ (fold_reflect j)

/-! ## The uniform root has equal half marginals at the fold chambers -/

section Root

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

theorem reflect_odd (j : Fin 2) :
    (2 * foldCutA j - 1 : ZMod 6) = 1 ∨ (2 * foldCutA j - 1 : ZMod 6) = 3 ∨
      (2 * foldCutA j - 1 : ZMod 6) = 5 := by
  fin_cases j
  · right; left; rfl
  · left; rfl

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- A half marginal of an emitted law as an expectation under the emitted law. -/
theorem marg_emit_eq {I X H : Type} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [DecidableEq H] (μ : FiniteLaw (I → X)) (e : Slot → I) (proj : (Slot → X) → H) (x : H) :
    (∑ z, if proj z = x then (emit μ e).weight z else 0) =
      μ.expect (fun y => if proj (y ∘ e) = x then 1 else 0) := by
  calc _ = (emit μ e).expect (fun z => if proj z = x then (1 : ℝ) else 0) := by
        unfold FiniteLaw.expect
        refine sum_congr rfl fun z _ => ?_
        beta_reduce
        by_cases hz : proj z = x
        · simp only [hz, ↓reduceIte, mul_one]
        · simp only [hz, ↓reduceIte, mul_zero]
    _ = _ := expect_emit μ e _

/-- **The uniform root component has equal half marginals at the fold chambers** (`hplus`,
`hminus` of `hRes_pointwise` with `ν` its plus marginal). -/
theorem rootMinus_eq_plus_uniform (hne : MiddleNonempty pr) (j : Fin 2) :
    minusMarginal (firstChamberCut (foldCutA j))
        (emit (uniformRoot pr hne) (midEmission (PType.pat .L ()))).weight =
      plusMarginal (firstChamberCut (foldCutA j))
        (emit (uniformRoot pr hne) (midEmission (PType.pat .L ()))).weight := by
  have hauto := recordGraph_reflection (Fin 2) (2 * foldCutA j - 1) (reflect_odd j)
  funext x
  unfold minusMarginal plusMarginal
  rw [marg_emit_eq, marg_emit_eq]
  have e : ∀ y : ZMod 6 × Fin 2 → BlockLabel pr,
      (fun v : (firstChamberCut (foldCutA j)).Half =>
        (y ∘ midEmission (PType.pat .L ())) ((firstChamberCut (foldCutA j)).flip v.1)) =
      (fun v : (firstChamberCut (foldCutA j)).Half =>
        ((y ∘ reflectionMap (Fin 2) (2 * foldCutA j - 1)) ∘ midEmission (PType.pat .L ())) v.1) :=
    fun y => funext fun v => rfl
  simp_rw [e]
  exact blockGraphLaw_expect_auto pr (recordGraph (Fin 2)) hne.L2 _ hauto
    (fun y => if (fun v : (firstChamberCut (foldCutA j)).Half =>
      (y ∘ midEmission (PType.pat .L ())) v.1) = x then 1 else 0)

end Root

/-! ## The root split at the paper's block specifications and at the obligations' data -/

section Spec

open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] in
/-- **The root split of every middle block law** (`hmix`): for a middle specification with
weights `W`, scale `r` and root `Γ`, the block law is `(1 + h)⁻¹ (Π^rt + 𝓜)` with
`h = P(r) − 1`, `Π^rt` the root component and `𝓜` the nonroot part. -/
theorem spec_split (hW : Target.Weil) {b : B} (S : PaperBlockSpec blockOf b) :
    (∃ U, S = .upper U) ∨ ∃ (hne : MiddleNonempty (blockPrimes blockOf b))
      (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel (blockPrimes blockOf b)))
      (W : MiddleWeights) (r : ℝ), 0 ≤ r ∧
      signedIntegral (S.toAtom hW).law.weight =
        (1 + (∑ i, midCoeff W r i - 1))⁻¹ •
          (signedIntegral (midComponent (middleBlockFieldLaws _ hne root) rootIdx).weight +
            nonroot (middleBlockFieldLaws _ hne root) W r) := by
  cases S with
  | upper U => exact Or.inl ⟨U, rfl⟩
  | middleUniform M =>
    exact Or.inr ⟨M.hne, _, M.W, M.r, M.hr, middleReference_split _ M.W M.hr⟩
  | middleIndividual M =>
    exact Or.inr ⟨M.hne, _, M.W, M.r, M.hr, middleReference_split _ M.W M.hr⟩
  | middleCoherent M =>
    exact Or.inr ⟨M.hne, _, M.W, M.r, M.hr, middleReference_split _ M.W M.hr⟩

end Spec

section Front

open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.MainFinalF1 (Blk specF)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperRecordTables}

/-- **The reference of the obligations' data at a block atom is the block law of its
specification** (by definition), so `spec_split` gives `hmix` there. -/
theorem refLaw_front (F : CompanionFrontND hW hMR hFour UpT) (hB : Target.BMOR)
    (hRR : Target.ThetaSmallRR) (L : ℕ) (b : Blk) :
    (F.X hB hRR).data.R.law CancellationSteps.paperTail L (.inl (.inr b)) =
      signedIntegral ((specF hW (MainFinalF1.analyticInputs
        (F.toK.PCu.toPC2'.toPC hW hMR hFour) F.toK.BA) b).toAtom hW).law.weight :=
  rfl

end Front

end Sarkozy.OpsVariance

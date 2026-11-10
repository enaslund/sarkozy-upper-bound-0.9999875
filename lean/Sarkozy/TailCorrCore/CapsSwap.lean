module

public import Sarkozy.TailCorrCore.Core0

@[expose] public section

/-!
# The layer caps of `φ₀φ₁` and `φ₁φ₀` coincide

`paper/sections/25_upper_reference.tex`, `it:upper-valid-layer` (V3) and
`def:record:upper-bands`(e): the caps `κ_{φφ'}` of the tail datum are recorded for unordered
field pairs (`k_LF = 9`, `k_LE = 7`, `k_FE = 3`, …).

The layer cut `ι` (`Reserved.fieldCut`) only reflects the layer, so it commutes with the
coordinate swap `swap3`; the two-layer and one-layer field laws of `φ₁φ₀` are the images of
those of `φ₀φ₁` (`lam2_swap`, `lam1_swap`, from `graphLaw_swap`); `diagF` commutes with the swap;
and `κ_{φ₀φ₁} = κ_{φ₁φ₀}` (`tailKappa_symm`). Hence:

* `fieldCut_positive_swap`: positivity at `ι` transfers along the swap;
* **`cap_swap`**: the cap (V3) of the field pair `φ₁φ₀` follows from that of `φ₀φ₁`;
* **`TailSpectralCore1`**: `TailSpectralCore0` with the caps of the five field pairs
  `LL`, `FF`, `LF`, `LE`, `FE` only (`EE` is HC's `layerCap_EE`; `FL`, `EL`, `EF` follow);
  `tailSpectralCore0_of_core1`, and **`tailInputsCorr_of_core1`**, the plug-in for `hC`.

New material for this paper.
-/

namespace Sarkozy.TailCorrCore

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.TailCorr

/-! ## Positivity at the layer cut transfers along the swap -/

section Cut

variable {O0 O1 X : Type*} [Fintype O0] [DecidableEq O0] [Fintype O1] [DecidableEq O1]

lemma mem_fieldCut_half (v : O0 × O1 × ZMod 2) :
    v ∈ (Reserved.fieldCut O0 O1).half ↔ v.2.2 = 0 := by
  simp only [Reserved.fieldCut, ReflectionCut.prodRight, layerCut]
  simp only [Finset.product_eq_sprod, Finset.mem_product, Finset.mem_univ, true_and,
    Finset.mem_singleton]

lemma fieldCut_flip (v : O0 × O1 × ZMod 2) :
    (Reserved.fieldCut O0 O1).flip v = (v.1, v.2.1, 1 - v.2.2) := rfl

/-- **Positivity at `ι` transfers along the coordinate swap.** -/
theorem fieldCut_positive_swap (L : ((O0 × O1 × ZMod 2 → X) → ℝ) →ₗ[ℝ] ℝ)
    (h : (Reserved.fieldCut O0 O1).Positive L) :
    (Reserved.fieldCut O1 O0).Positive
      (pushFunctional L (fun y : O0 × O1 × ZMod 2 → X => fun w => y (swap3 w))) := by
  set c := Reserved.fieldCut O0 O1
  set c' := Reserved.fieldCut O1 O0
  -- the relabelling of half-configurations
  have hmem : ∀ v' : c'.Half, swap3 v'.1 ∈ c.half := fun v' =>
    (mem_fieldCut_half _).mpr ((mem_fieldCut_half v'.1).mp v'.2)
  let rel : (c.Half → X) → (c'.Half → X) := fun g v' => g ⟨swap3 v'.1, hmem v'⟩
  have hform : ∀ F G : (c'.Half → X) → ℝ,
      c'.form (pushFunctional L (fun y : O0 × O1 × ZMod 2 → X => fun w => y (swap3 w))) F G =
        c.form L (F ∘ rel) (G ∘ rel) := by
    intro F G
    rfl
  constructor
  · intro F G
    rw [hform, hform]
    exact h.symmetric _ _
  · intro F
    rw [hform]
    exact h.nonneg _

end Cut

/-! ## The field laws of `φ₁φ₀` -/

section Laws

variable {p : ℕ} [Fact p.Prime]

/-- `λ_{φ₁φ₀}` is the image of `λ_{φ₀φ₁}` under the swap (two layers). -/
theorem lam2_swap (hne : TailNonempty p) (f0 f1 : FieldTy) :
    lam2 (tailFieldLaws p hne) f1 f0 =
      (lam2 (tailFieldLaws p hne) f0 f1).map (fun y => fun w => y (swap3 w)) := by
  refine law_eq_of_expect fun h => ?_
  simp only [lam2, FiniteLaw.expect_map]
  change (graphLaw (fieldGraph (toFType f1) (toFType f0) (Fin 2)) (hne.two _ _)).expect _ =
    (graphLaw (fieldGraph (toFType f0) (toFType f1) (Fin 2)) (hne.two _ _)).expect _
  rw [graphLaw_swap (toFType f0) (toFType f1) (Fin 2) (hne.two _ _) (hne.two _ _)]
  rfl

/-- `λ^{(1)}_{φ₁φ₀}` is the image of `λ^{(1)}_{φ₀φ₁}` under the swap (one layer). -/
theorem lam1_swap (hne : TailNonempty p) (f0 f1 : FieldTy) :
    lam1 (tailFieldLaws p hne) f1 f0 =
      (lam1 (tailFieldLaws p hne) f0 f1).map (fun y => fun w => y (swap3 w)) := by
  refine law_eq_of_expect fun h => ?_
  simp only [lam1, FiniteLaw.expect_map]
  change (graphLaw (fieldGraph (toFType f1) (toFType f0) (Fin 1)) (hne.one _ _)).expect _ =
    (graphLaw (fieldGraph (toFType f0) (toFType f1) (Fin 1)) (hne.one _ _)).expect _
  rw [graphLaw_swap (toFType f0) (toFType f1) (Fin 1) (hne.one _ _) (hne.one _ _)]
  rfl

theorem tailKappa_symm (f0 f1 : FieldTy) : tailKappa f1 f0 = tailKappa f0 f1 := by
  cases f0 <;> cases f1 <;> rfl

/-- **The cap (V3) of `φ₁φ₀` from that of `φ₀φ₁`** (`it:upper-valid-layer`). -/
theorem cap_swap (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) (f0 f1 : FieldTy)
    (h : (Reserved.fieldCut f0.Obj f1.Obj).Below
      (-(tailKappa f0 f1 * tailR q) •
        pushFunctional (lawL (lam1 (tailFieldLaws q hne) f0 f1)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws q hne) f0 f1))) :
    (Reserved.fieldCut f1.Obj f0.Obj).Below
      (-(tailKappa f1 f0 * tailR q) •
        pushFunctional (lawL (lam1 (tailFieldLaws q hne) f1 f0)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws q hne) f1 f0)) := by
  have h' := fieldCut_positive_swap _ h
  unfold ReflectionCut.Below
  convert h' using 1
  rw [tailKappa_symm, lam2_swap hne f0 f1, lam1_swap hne f0 f1]
  refine LinearMap.ext fun Φ => ?_
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, pushFunctional, LinearMap.coe_mk,
    AddHom.coe_mk, lawL_apply, FiniteLaw.expect_map]
  rfl

end Laws

/-! ## The reduced bundle -/

/-- **The remaining spectral inputs of the tail datum, reduced by the two symmetries**
(`lem:tail-law`(i), spectral part). Hypothesis bundle, not proved here: `TailSpectralCore0` with
the layer caps (V3) only for the five field pairs `LL`, `FF`, `LF`, `LE`, `FE`. -/
structure TailSpectralCore1 (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) : Prop where
  root20 : ∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f').d (tailR q)
  root10 : ∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f').d (tailR q)
  fold20 : ∀ f', FoldCorr (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailCF (tailOrd f') * tailR q)
  fold10 : ∀ f', FoldCorr (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailCF (tailRes f') * tailR q)
  match20 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) ((tailOrd f').h * tailR q)
  match10 : ∀ f', f' ≠ .E → MatchNorm (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) ((tailRes f').h * tailR q)
  caps : ∀ f0 f1 : FieldTy, (f0, f1) ∈ ({(.L, .L), (.F, .F), (.L, .F), (.L, .E), (.F, .E)} :
      Finset (FieldTy × FieldTy)) →
    (Reserved.fieldCut f0.Obj f1.Obj).Below
      (-(tailKappa f0 f1 * tailR q) •
        pushFunctional (lawL (lam1 (tailFieldLaws q hne) f0 f1)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws q hne) f0 f1))

theorem tailSpectralCore0_of_core1 (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)
    (hW : WeilBound (ZMod q)) (hp : (2 : ℝ) ^ 20 ≤ q) (h : TailSpectralCore1 q hne hW hp) :
    TailSpectralCore0 q hne hW hp := by
  refine ⟨h.root20, h.root10, h.fold20, h.fold10, h.match20, h.match10, fun f0 f1 hEE => ?_⟩
  cases f0 <;> cases f1
  · exact h.caps .L .L (by decide)
  · exact h.caps .L .F (by decide)
  · exact h.caps .L .E (by decide)
  · exact cap_swap q hne .L .F (h.caps .L .F (by decide))
  · exact h.caps .F .F (by decide)
  · exact h.caps .F .E (by decide)
  · exact cap_swap q hne .L .E (h.caps .L .E (by decide))
  · exact cap_swap q hne .F .E (h.caps .F .E (by decide))
  · exact absurd ⟨rfl, rfl⟩ hEE

/-- **`TailInputsCorr P` from the reduced bundle**: with `P = P₄` this is the obligation `hC`. -/
theorem tailInputsCorr_of_core1 {P : ℕ} (hP : P4 ≤ P)
    (hS : ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectralCore1 q hne hW hp) :
    TailInputsCorr P :=
  tailInputsCorr_of_core0 hP fun q _ hq hne hW hp =>
    tailSpectralCore0_of_core1 q hne hW hp (hS q hq hne hW hp)

/-- **`TailInputsValid P₄` from the reduced bundle.** -/
theorem tailInputsValid_of_core1
    (hS : ∀ (q : ℕ) [Fact q.Prime], P4 ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectralCore1 q hne hW hp) :
    TailInputsValid P4 :=
  tailInputsValid_of_corr le_rfl (tailInputsCorr_of_core1 le_rfl hS)

end Sarkozy.TailCorrCore

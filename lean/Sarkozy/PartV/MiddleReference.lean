module

public import Sarkozy.PartV.Components
public import Sarkozy.PartV.Parameters

@[expose] public section

/-!
# The reference law of a middle block (`lem:front12:reference`, `def:record:exact-blocks`)

`paper/sections/20c_middle_frame.tex`, `subsec:middle-reference-law`, `lem:front12:reference`;
`paper/sections/20_middle_reference.tex`, `def:record:exact-blocks`, `subsec:push:layer12spectral`;
`paper/sections/18_design.tex`, `def:construction`(b).

**The law.** For a middle block `𝔅` with least prime `b` and `r = b^{-1/2}`,
`μ̃_𝔅 = ∑_𝔱 w_𝔱 r^{deg 𝔱} π_{𝔱,2} + r ∑_𝔱 v_𝔱 r^{deg 𝔱} Diag_ι(π_{𝔱,1})` and
`μ_𝔅 = μ̃_𝔅 / μ̃_𝔅(1)`, where `π_{𝔱,j}` is the sum of the `j`-layer components of the type `𝔱`:
the images, under the patterns of `def:patterns` and the middle emission (the slot
`(u₀, u₁, ℓ)` reads `y_{φ(u₀), ℓ}`), of the two-layer root (`𝔱 = L`), the `F` law
`λ_𝔅(G_{F,2})` (`𝔱 = D`) and the `E` law `λ_𝔅(G_{E,2})` (`𝔱 = S, R, C`), and of their one-layer
versions placed on both layers.

Here the law is `middleReference F W r` for arbitrary field laws `F` (`MiddleFieldLaws`), and
`middleBlockReference` instantiates it with the paper's block laws: the root is a parameter
(the uniform `λ_𝔅(G_{L,2})` on the pieces below `2³⁰`, the positive root of
`Sarkozy.PartV.PositiveRoot` on the seven pieces from `2³⁰`), and the other five field laws
are the block graph laws of `G_{F,2}`, `G_{E,2}`, `G_{L,1}`, `G_{F,1}`, `G_{E,1}`.

**Proved** (for every nonnegative weight vector with `w_L = 1` and every `r ≥ 0`):
* `μ_𝔅` is a probability law and `μ̃_𝔅(1) = P(r) = ∑_𝔱 m_𝔱 (w_𝔱 r^{deg 𝔱} + v_𝔱 r^{deg 𝔱 + 1})
  ≥ 1` (`middleTilde_mass`, `one_le_midPoly`), which is the mass statement of (iii);
* uniform one-slot marginals (`middleReference_uniform`, from the field laws; for the block laws
  `middleBlockReference_uniform`);
* reflection positivity at every chamber cut of the second coordinate
  (`middleReference_secondCut_positive`: the law is a pullback that ignores `u₁`, the last
  paragraph of the proof of (iii));
* the one-layer diagonal part is positive at `ι` (`middleDiag_reserved_positive`);
* square-affine invariance (R3) for the block law (`middleBlockReference_affine`).

**Elsewhere in `Sarkozy.PartV`:** reflection positivity at the chamber cuts of the first
coordinate (`ChamberCut`, `PositiveRootRP`, `CoherentRP`) and at `ι` (`LayerCut`), from the rows
(i) and the caps (ii) as hypotheses and the thirteen inequalities `MiddleWeights.Completes`; the
protection (iv) (`Protection`); (R3) and the layer swap for the positive roots (`RootAffine`,
`LayerSwap`). **Not proved:** the rows (i) and the caps (ii). The weights of the 33 pieces
(`tab:data:middle-weights`) are not entered.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## Weights and the thirteen inequalities (`lem:front12:reference`(iii)) -/

/-- **Completion weights** of a middle piece: `w = (w_L, …, w_C)` with `w_L = 1` and
`v = (v_L, …, v_C)`, nonnegative. -/
structure MiddleWeights where
  w : PType → ℝ
  v : PType → ℝ
  w_L : w .L = 1
  w_nonneg : ∀ t, 0 ≤ w t
  v_nonneg : ∀ t, 0 ≤ v t

/-- The inputs of the completion of a piece (`lem:front12:reference`(i),(ii)): the root caps `d`
(L20) and `d₁` (L10), the row constants `f_j, h_j`, and the layer caps `k_𝔱` (with
`k_S = k_R = k_C = k_E` in the paper). -/
structure MiddleInputs where
  d : ℝ
  d₁ : ℝ
  f₁ : ℝ
  f₂ : ℝ
  h₁ : ℝ
  h₂ : ℝ
  k : PType → ℝ

/-- **The thirteen inequalities** of `lem:front12:reference`(iii). -/
def MiddleWeights.Completes (W : MiddleWeights) (I : MiddleInputs) : Prop :=
  I.d ≤ W.w .D ∧ W.w .D ≤ W.w .S ∧ I.f₂ * W.w .D + I.h₂ * W.w .S ≤ W.w .R ∧
    W.w .R ^ 2 ≤ W.w .C * W.w .S ∧
  I.d₁ * W.v .L ≤ W.v .D ∧ W.v .D ≤ W.v .S ∧ I.f₁ * W.v .D + I.h₁ * W.v .S ≤ W.v .R ∧
    W.v .R ^ 2 ≤ W.v .C * W.v .S ∧
  ∀ t, I.k t * W.w t ≤ W.v t

/-- **The protection inequality** `v_D ≥ 2 k_D w_D` (`eq:protection`,
`lem:front12:reference`(iv)). -/
def MiddleWeights.Protects (W : MiddleWeights) (I : MiddleInputs) : Prop :=
  2 * I.k .D * W.w .D ≤ W.v .D

/-! ## Field laws, components and the completion -/

/-- **The field laws of a middle block**: the two-layer laws (`two .L` the root, `two .F` the `F`
law, `two .E` the `E` law) and the one-layer laws, on labellings of `O_𝔣 × Λ_j`. -/
structure MiddleFieldLaws (X : Type*) [Fintype X] [DecidableEq X] where
  two : (f : FType) → FiniteLaw (f.Obj × Fin 2 → X)
  one : (f : FType) → FiniteLaw (f.Obj × Fin 1 → X)

/-- The index set of the components: two-layer (`true`) or one-layer diagonal (`false`), a type
and one of its patterns. -/
abbrev MidIdx : Type := Bool × (Σ t : PType, t.Pat)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The components** `Π_φ` (two-layer) and `Diag_ι(Π⁽¹⁾_φ)` (one-layer copy on both layers). -/
noncomputable def midComponent (F : MiddleFieldLaws X) : MidIdx → FiniteLaw (Slot → X)
  | (true, ⟨t, φ⟩) => emit (F.two t.field) (midEmission (t.pat φ))
  | (false, ⟨t, φ⟩) => emit (F.one t.field) (midDiagEmission (t.pat φ))

/-- The graded weights: `w_𝔱 r^{deg 𝔱}` on the two-layer components and `v_𝔱 r^{deg 𝔱 + 1}` on
the one-layer copies. -/
noncomputable def midCoeff (W : MiddleWeights) (r : ℝ) : MidIdx → ℝ
  | (true, ⟨t, _⟩) => W.w t * r ^ t.deg
  | (false, ⟨t, _⟩) => W.v t * r ^ (t.deg + 1)

theorem midCoeff_nonneg (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (i : MidIdx) :
    0 ≤ midCoeff W r i := by
  rcases i with ⟨b, t, φ⟩
  cases b
  · exact mul_nonneg (W.v_nonneg t) (pow_nonneg hr _)
  · exact mul_nonneg (W.w_nonneg t) (pow_nonneg hr _)

/-- The normalizing polynomial `P(r) = ∑_𝔱 m_𝔱 (w_𝔱 r^{deg 𝔱} + v_𝔱 r^{deg 𝔱 + 1})`. -/
noncomputable def midPoly (W : MiddleWeights) (r : ℝ) : ℝ :=
  ∑ t : PType, (t.mult : ℝ) * (W.w t * r ^ t.deg + W.v t * r ^ (t.deg + 1))

theorem sum_midCoeff (W : MiddleWeights) (r : ℝ) : ∑ i, midCoeff W r i = midPoly W r := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  unfold midPoly
  rw [Fintype.sum_sigma, Fintype.sum_sigma, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  simp only [midCoeff, sum_const, card_univ, PType.card_pat, nsmul_eq_mul]
  ring

/-- `P(r) ≥ 1`: the root has weight `w_L = 1` and the other terms are nonnegative. -/
theorem one_le_midPoly (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ midPoly W r := by
  unfold midPoly
  have hterm : ∀ t : PType, 0 ≤ (t.mult : ℝ) * (W.w t * r ^ t.deg + W.v t * r ^ (t.deg + 1)) :=
    fun t => mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg (W.w_nonneg t)
      (pow_nonneg hr _)) (mul_nonneg (W.v_nonneg t) (pow_nonneg hr _)))
  have hL : (1 : ℝ) ≤ (PType.L.mult : ℝ) *
      (W.w .L * r ^ PType.L.deg + W.v .L * r ^ (PType.L.deg + 1)) := by
    simp only [PType.mult, PType.deg, W.w_L, pow_zero, Nat.cast_one, one_mul, zero_add, pow_one]
    linarith [mul_nonneg (W.v_nonneg .L) hr]
  exact hL.trans (single_le_sum (fun t _ => hterm t) (mem_univ PType.L))

/-- **The normalizing mass in the paper's form** (`lem:four-routes-normalized`, the display of
`Z_i(r)` in `subsec` "Accounting for the normalizing factor"):
`P(r) = 1 + (3w_D + 2w_S + v_L) r + (6w_R + 3v_D + 2v_S) r² + (2w_C + 6v_R) r³ + 2v_C r⁴`. -/
theorem midPoly_eq (W : MiddleWeights) (r : ℝ) :
    midPoly W r = 1 + (3 * W.w .D + 2 * W.w .S + W.v .L) * r +
      (6 * W.w .R + 3 * W.v .D + 2 * W.v .S) * r ^ 2 + (2 * W.w .C + 6 * W.v .R) * r ^ 3 +
      2 * W.v .C * r ^ 4 := by
  unfold midPoly
  rw [PType.sum_pType]
  simp only [PType.mult, PType.deg, W.w_L]
  push_cast
  ring

theorem midPoly_pos (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) : 0 < ∑ i, midCoeff W r i := by
  rw [sum_midCoeff]
  exact lt_of_lt_of_le one_pos (one_le_midPoly W hr)

/-- **The middle reference law** `μ_𝔅 = μ̃_𝔅 / μ̃_𝔅(1)` (`lem:front12:reference`). -/
noncomputable def middleReference (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ}
    (hr : 0 ≤ r) : FiniteLaw (Slot → X) :=
  weightedCompletion (midCoeff W r) (midCoeff_nonneg W hr) (midPoly_pos W hr) (midComponent F)

/-- The unnormalized law `μ̃_𝔅`. -/
noncomputable def middleTilde (F : MiddleFieldLaws X) (W : MiddleWeights) (r : ℝ) :
    ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  tildeMeasure (midCoeff W r) (midComponent F)

/-- **`μ̃_𝔅` is a nonnegative measure of mass `P(r) ≥ 1`** (`lem:front12:reference`(iii), mass). -/
theorem middleTilde_mass (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) :
    middleTilde F W r (fun _ => 1) = midPoly W r ∧ 1 ≤ midPoly W r ∧
      ∀ f : (Slot → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ middleTilde F W r f :=
  ⟨by rw [middleTilde, tildeMeasure_mass, sum_midCoeff], one_le_midPoly W hr,
    fun f hf => tildeMeasure_nonneg _ (midCoeff_nonneg W hr) _ f hf⟩

/-- `μ_𝔅` is `μ̃_𝔅 / P(r)`. -/
theorem middleReference_eq (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) :
    signedIntegral (middleReference F W hr).weight = (midPoly W r)⁻¹ • middleTilde F W r := by
  unfold middleReference middleTilde
  rw [signedIntegral_weightedCompletion, sum_midCoeff]

/-- **Uniform one-slot marginals** (`lem:front12:reference`(iii)), when every field law has
uniform vertex marginals. -/
theorem middleReference_uniform [Nonempty X] (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ}
    (hr : 0 ≤ r)
    (h2 : ∀ f (o : f.Obj × Fin 2) (g : X → ℝ),
      (F.two f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g)
    (h1 : ∀ f (o : f.Obj × Fin 1) (g : X → ℝ),
      (F.one f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g) :
    HasUniformMarginals (middleReference F W hr) := by
  refine weightedCompletion_uniform _ _ _ _ fun i => ?_
  rcases i with ⟨b, t, φ⟩
  cases b
  · exact emit_uniform _ _ (h1 t.field)
  · exact emit_uniform _ _ (h2 t.field)

/-- **Reflection positivity at the chamber cuts of the second coordinate**: the middle law is
the pullback of a law on `(u₀, ℓ)`, so every configuration is fixed by these cuts
(`lem:front12:reference`(iii), "Second-coordinate cuts"). -/
theorem middleReference_secondCut_positive (F : MiddleFieldLaws X) (W : MiddleWeights) {r : ℝ}
    (hr : 0 ≤ r) (a : Chamber) :
    (secondChamberCut a).Positive (signedIntegral (middleReference F W hr).weight) := by
  refine weightedCompletion_positive _ _ _ _ _ fun i => ?_
  rcases i with ⟨b, t, φ⟩
  cases b
  · exact emit_positive _ _ _ (midDiagEmission_secondCut _ a)
  · exact emit_positive _ _ _ (midEmission_secondCut _ a)

/-- **The one-layer diagonal copies are positive at `ι`** (each is fixed samplewise by the
layer flip; `lem:commoncut`(i)). -/
theorem middleDiag_reserved_positive (F : MiddleFieldLaws X) (t : PType) (φ : t.Pat) :
    reservedCut.Positive (signedIntegral (midComponent F (false, ⟨t, φ⟩)).weight) :=
  emit_positive _ _ _ (midDiagEmission_reserved _)

/-! ## The paper's block laws -/

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- Nonemptiness of `Inj_p(G)` at every prime of the block, for the five non-root graphs of the
middle reference (`G_{F,2}`, `G_{E,2}`, `G_{L,1}`, `G_{F,1}`, `G_{E,1}`) and the twelve-label
root `G_{L,2}`. Discharged for blocks of large primes by `exists_injLabellings_nonempty`. -/
structure MiddleNonempty : Prop where
  L2 : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty
  F2 : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph (Fin 2))).Nonempty
  E2 : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty
  L1 : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 1))).Nonempty
  F1 : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph (Fin 1))).Nonempty
  E1 : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 1))).Nonempty

/-- The uniform twelve-label root `λ_𝔅(G_{L,2})`. -/
noncomputable def uniformRoot (hne : MiddleNonempty pr) :
    FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr) :=
  blockGraphLaw pr (recordGraph (Fin 2)) hne.L2

/-- **The field laws of a middle block** with a given two-layer root: the block graph laws of
`G_{F,2}`, `G_{E,2}` and of the one-layer graphs `G_{L,1}`, `G_{F,1}`, `G_{E,1}`. The one-layer
root is untilted on every piece (`lem:front12:reference`, `subsec:middle-reference-law`). -/
noncomputable def middleBlockFieldLaws (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) : MiddleFieldLaws (BlockLabel pr) where
  two f := match f with
    | .L => root
    | .F => blockGraphLaw pr (foldGraph (Fin 2)) hne.F2
    | .E => blockGraphLaw pr (matchGraph (Fin 2)) hne.E2
  one f := match f with
    | .L => blockGraphLaw pr (recordGraph (Fin 1)) hne.L1
    | .F => blockGraphLaw pr (foldGraph (Fin 1)) hne.F1
    | .E => blockGraphLaw pr (matchGraph (Fin 1)) hne.E1

/-- **The reference law of a middle block** (`lem:front12:reference`, `def:construction`(b)):
the middle completion of the block field laws with the root `root` and the weights `W` at
`r` (in the paper `r = b^{-1/2}`, `b` the least prime of the block). -/
noncomputable def middleBlockReference (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) {r : ℝ}
    (hr : 0 ≤ r) : FiniteLaw (Slot → BlockLabel pr) :=
  middleReference (middleBlockFieldLaws pr hne root) W hr

/-- **The middle block law has uniform one-slot marginals** whenever its root has uniform vertex
marginals (the uniform root: `uniformRoot_vertex_uniform`; the positive root:
`Sarkozy.PartV.PositiveRoot`). -/
theorem middleBlockReference_uniform (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
    (hroot : ∀ (o : ZMod 6 × Fin 2) (g : BlockLabel pr → ℝ),
      root.expect (fun y => g (y o)) = (FiniteLaw.uniform (BlockLabel pr)).expect g)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) :
    HasUniformMarginals (middleBlockReference pr hne root W hr) := by
  refine middleReference_uniform _ W hr (fun f => ?_) (fun f => ?_)
  · cases f
    · exact hroot
    · exact blockGraphLaw_vertex_uniform pr _ hne.F2
    · exact blockGraphLaw_vertex_uniform pr _ hne.E2
  · cases f
    · exact blockGraphLaw_vertex_uniform pr _ hne.L1
    · exact blockGraphLaw_vertex_uniform pr _ hne.F1
    · exact blockGraphLaw_vertex_uniform pr _ hne.E1

theorem uniformRoot_vertex_uniform (hne : MiddleNonempty pr) (o : ZMod 6 × Fin 2)
    (g : BlockLabel pr → ℝ) :
    (uniformRoot pr hne).expect (fun y => g (y o)) =
      (FiniteLaw.uniform (BlockLabel pr)).expect g :=
  blockGraphLaw_vertex_uniform pr _ hne.L2 o g

/-- An emitted law inherits square-affine invariance from its field law. -/
theorem expect_emit_affine {I : Type*} [Fintype I] [DecidableEq I]
    (lam : FiniteLaw (I → BlockLabel pr)) (π : Slot → I) (α β : BlockLabel pr)
    (hlam : ∀ H : (I → BlockLabel pr) → ℝ,
      lam.expect (fun z => H (fun w i => α i * z w i + β i)) = lam.expect H)
    (H : (Slot → BlockLabel pr) → ℝ) :
    (emit lam π).expect (fun z => H (fun v i => α i * z v i + β i)) = (emit lam π).expect H := by
  rw [expect_emit, expect_emit]
  exact hlam (fun y => H (y ∘ π))

/-- **(R3) for the middle block law**: invariance under the square-affine maps
`z_{v,p} ↦ α_p z_{v,p} + β_p` (`χ_p(α_p) = 1`), independently at each prime, whenever the root
is invariant (the uniform root: `blockGraphLaw_expect_affine`). -/
theorem middleBlockReference_affine (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (α β : BlockLabel pr)
    (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (hroot : ∀ H : (ZMod 6 × Fin 2 → BlockLabel pr) → ℝ,
      root.expect (fun z => H (fun w i => α i * z w i + β i)) = root.expect H)
    (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (H : (Slot → BlockLabel pr) → ℝ) :
    (middleBlockReference pr hne root W hr).expect (fun z => H (fun v i => α i * z v i + β i)) =
      (middleBlockReference pr hne root W hr).expect H := by
  unfold middleBlockReference middleReference
  rw [expect_weightedCompletion, expect_weightedCompletion]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rcases j with ⟨b, t, φ⟩
  cases b <;> cases t
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (recordGraph (Fin 1)) hne.L1 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (foldGraph (Fin 1)) hne.F1 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (matchGraph (Fin 1)) hne.E1 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (matchGraph (Fin 1)) hne.E1 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (matchGraph (Fin 1)) hne.E1 α β hα) H
  · exact expect_emit_affine pr _ _ α β hroot H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (foldGraph (Fin 2)) hne.F2 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (matchGraph (Fin 2)) hne.E2 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (matchGraph (Fin 2)) hne.E2 α β hα) H
  · exact expect_emit_affine pr _ _ α β
      (blockGraphLaw_expect_affine pr (matchGraph (Fin 2)) hne.E2 α β hα) H

end Block

/-! ## Middle blocks (`def:record:exact-blocks`) -/

/-- **A middle block** (`def:record:exact-blocks`): a nonempty set of class-three primes of one
piece, of logarithmic length `∑_{p ∈ 𝔅} log p ≤ L = 570`. The partition of each piece into
blocks (the greedy exact blocks of (c), built from the authenticated histogram of
`subsec:data:pieces`, and the fixed-cardinality cells of (d)) is data not entered here; every
block of that partition has these properties, which are what the reference law and its local
estimates use (the local-domain lemma of section 20, not formalized here). -/
structure MiddleBlock where
  piece : Fin 33
  primes : Finset ℕ
  nonempty : primes.Nonempty
  prime : ∀ p ∈ primes, p.Prime
  class3 : ∀ p ∈ primes, p % 4 = 3
  inPiece : ∀ p ∈ primes, pieceStart piece ≤ p ∧ p < pieceStop piece
  budget : ∑ p ∈ primes, Real.log p ≤ middleBudget

/-- The least prime `b_𝔅` of a middle block. -/
noncomputable def MiddleBlock.least (B : MiddleBlock) : ℕ := B.primes.min' B.nonempty

/-- `r = b_𝔅^{-1/2}`. -/
noncomputable def MiddleBlock.r (B : MiddleBlock) : ℝ := ((B.least : ℝ)) ^ (-(1 / 2 : ℝ))

theorem MiddleBlock.r_nonneg (B : MiddleBlock) : 0 ≤ B.r :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The primes of a middle block are middle primes. -/
theorem MiddleBlock.isMiddlePrime (B : MiddleBlock) {p : ℕ} (hp : p ∈ B.primes) :
    IsMiddlePrime p := by
  refine ⟨B.prime p hp, B.class3 p hp, ?_, ?_⟩
  · have h := (B.inPiece p hp).1
    have hQ : Q3 ≤ pieceStart B.piece := by
      have := B.piece.isLt
      revert this
      generalize B.piece = i
      revert i
      unfold pieceStart pieceEnds Q3
      decide +kernel
    omega
  · have h := (B.inPiece p hp).2
    have hP : pieceStop B.piece ≤ P3 := by
      generalize B.piece = i
      revert i
      unfold pieceStop pieceEnds P3
      decide +kernel
    omega

/-- The primes of a block, as a finite type. -/
abbrev MiddleBlock.Idx (B : MiddleBlock) : Type := {p // p ∈ B.primes}

instance (B : MiddleBlock) (p : B.Idx) : Fact (p.1).Prime := ⟨B.prime p.1 p.2⟩

end Sarkozy.PartV

module

public import Sarkozy.PartV.Components
public import Sarkozy.PartV.Parameters

@[expose] public section

/-!
# The upper reference and the tail law (`def:upper-reference`, `def:tail-law`)

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(d),(e), `subsec:layer72:upper`,
`def:upper-reference`; `paper/sections/27_tail_index.tex`, `def:tail-law`, `lem:tail-law`.

**The law.** For a block `𝔅` with least prime `b`, `r = b^{-1/2}` and weights `w_𝔱, v_𝔱` indexed
by the 25 states `𝔱 = (𝔱₀, 𝔱₁)`,
`μ̃_𝔅 = ∑_𝔱 w_𝔱 r^{deg 𝔱} π_{𝔱,2} + r ∑_𝔱 v_𝔱 r^{deg 𝔱} Diag_ι(π_{𝔱,1})`,
`μ_𝔅 = μ̃_𝔅 / P_μ(r)`, `P_μ(r) = ∑_𝔱 m_𝔱 (w_𝔱 r^{deg 𝔱} + v_𝔱 r^{deg 𝔱 + 1})`, where
`π_{𝔱,j} = ∑_φ Π_{𝔱,φ}` and `Π_{𝔱,φ}` is the image of the field law
`λ_𝔅(G_{𝔣(𝔱₀)𝔣(𝔱₁),j})` under the emission `e_φ` (hidden objects forgotten). Here:
`upperReference F W` for arbitrary field laws, `upperBlockReference` for the paper's block laws.

**The tail law** (`def:tail-law`) is the upper reference at a single prime `p ≥ P₄` with the
weights of the tail datum (`def:record:upper-bands`(e)). Its fifty weights are entered from the
record `upper_v2_local.json` (`pieces[-1].weights`, `reserved_weights`), and two checks bind them
to the paper:
* `tailPoly_eq`: their normalizing polynomial is exactly the paper's
  `P_μ(r) = ∑_{d=0}^{7} c_d r^d` with `c_0 = 1`, `c_1 = 5988/5`, …, `c_7 = 970455252992/7`;
* `tailDatum_gates`: they satisfy the 105 inequalities of `def:record:upper-bands`(d)
  (`eq:upper-slice` with the ordinary and the reserved inputs of (e), `M = 21/20`, and the
  domination `eq:independent-fold-domination` with the caps of (e)), checked exactly.

**Proved for the laws:** probability, `μ̃(1) = P_μ(r) ≥ 1` (`upperTilde_mass`), uniform one-slot
marginals and square-affine invariance (R3) of the block and tail laws, positivity at `ι` of the
one-layer diagonal copies. Positivity at `ι` from the layer caps is in `LayerCut`. **Not
proved:** reflection positivity at the chamber cuts (the reflection-positivity lemma of the upper
reference in section 25, and the corresponding part of the tail-law lemma, from
`lem:five-type`(d) with the band inputs).
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## Weights of the 25 states -/

/-- **Upper completion weights** (`def:record:upper-bands`(d)): `w_𝔱, v_𝔱 ≥ 0` indexed by the
states `𝔱 = (𝔱₀, 𝔱₁)`, with `w_LL = 1`. -/
structure UpperWeights where
  w : PType → PType → ℝ
  v : PType → PType → ℝ
  w_LL : w .L .L = 1
  w_nonneg : ∀ t₀ t₁, 0 ≤ w t₀ t₁
  v_nonneg : ∀ t₀ t₁, 0 ≤ v t₀ t₁

/-- The index set of the upper components: two-layer or one-layer copy, a state, and a pair of
patterns `φ = (φ₀, φ₁) ∈ P_{𝔱₀} × P_{𝔱₁}`. -/
abbrev UpIdx : Type := Bool × (Σ t : PType × PType, t.1.Pat × t.2.Pat)

/-- **The field laws of an upper block**: for each pair of field types the two-layer and the
one-layer law on labellings of `O_{φ₀} × O_{φ₁} × Λ_j`. -/
structure UpperFieldLaws (X : Type*) [Fintype X] [DecidableEq X] where
  two : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Fin 2 → X)
  one : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Fin 1 → X)

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- **The pattern summands** `Π_{𝔱,φ}` and `Diag_ι(Π⁽¹⁾_{𝔱,φ})` (`subsec:layer72:upper`). -/
noncomputable def upComponent (F : UpperFieldLaws X) : UpIdx → FiniteLaw (Slot → X)
  | (true, ⟨t, φ⟩) => emit (F.two t.1.field t.2.field) (upEmission (t.1.pat φ.1) (t.2.pat φ.2))
  | (false, ⟨t, φ⟩) =>
      emit (F.one t.1.field t.2.field) (upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2))

/-- The graded weights `w_𝔱 r^{deg 𝔱}` and `v_𝔱 r^{deg 𝔱 + 1}`, `deg 𝔱 = deg 𝔱₀ + deg 𝔱₁`. -/
noncomputable def upCoeff (W : UpperWeights) (r : ℝ) : UpIdx → ℝ
  | (true, ⟨t, _⟩) => W.w t.1 t.2 * r ^ (t.1.deg + t.2.deg)
  | (false, ⟨t, _⟩) => W.v t.1 t.2 * r ^ (t.1.deg + t.2.deg + 1)

theorem upCoeff_nonneg (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) (i : UpIdx) :
    0 ≤ upCoeff W r i := by
  rcases i with ⟨b, t, φ⟩
  cases b
  · exact mul_nonneg (W.v_nonneg _ _) (pow_nonneg hr _)
  · exact mul_nonneg (W.w_nonneg _ _) (pow_nonneg hr _)

/-- **The normalizing polynomial** `P_μ(r) = ∑_𝔱 m_𝔱 (w_𝔱 r^{deg 𝔱} + v_𝔱 r^{deg 𝔱 + 1})`
(`eq:independent-fold-polynomial`), `m_𝔱 = m_{𝔱₀} m_{𝔱₁}`. -/
noncomputable def upPoly (W : UpperWeights) (r : ℝ) : ℝ :=
  ∑ t : PType × PType, ((t.1.mult * t.2.mult : ℕ) : ℝ) *
    (W.w t.1 t.2 * r ^ (t.1.deg + t.2.deg) + W.v t.1 t.2 * r ^ (t.1.deg + t.2.deg + 1))

theorem sum_upCoeff (W : UpperWeights) (r : ℝ) : ∑ i, upCoeff W r i = upPoly W r := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  unfold upPoly
  rw [Fintype.sum_sigma, Fintype.sum_sigma, ← sum_add_distrib]
  refine sum_congr rfl fun t _ => ?_
  simp only [upCoeff, sum_const, card_univ, Fintype.card_prod, PType.card_pat, nsmul_eq_mul]
  push_cast
  ring

theorem one_le_upPoly (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) : 1 ≤ upPoly W r := by
  unfold upPoly
  have hterm : ∀ t : PType × PType, 0 ≤ ((t.1.mult * t.2.mult : ℕ) : ℝ) *
      (W.w t.1 t.2 * r ^ (t.1.deg + t.2.deg) + W.v t.1 t.2 * r ^ (t.1.deg + t.2.deg + 1)) :=
    fun t => mul_nonneg (Nat.cast_nonneg _) (add_nonneg (mul_nonneg (W.w_nonneg _ _)
      (pow_nonneg hr _)) (mul_nonneg (W.v_nonneg _ _) (pow_nonneg hr _)))
  have hL : (1 : ℝ) ≤ ((PType.L.mult * PType.L.mult : ℕ) : ℝ) *
      (W.w .L .L * r ^ (PType.L.deg + PType.L.deg) +
        W.v .L .L * r ^ (PType.L.deg + PType.L.deg + 1)) := by
    simp only [PType.mult, PType.deg, W.w_LL, pow_zero, Nat.cast_one, one_mul,
      mul_one, zero_add, pow_one]
    linarith [mul_nonneg (W.v_nonneg .L .L) hr]
  exact hL.trans (single_le_sum (fun t _ => hterm t) (mem_univ (PType.L, PType.L)))

theorem upPoly_pos (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) : 0 < ∑ i, upCoeff W r i := by
  rw [sum_upCoeff]
  exact lt_of_lt_of_le one_pos (one_le_upPoly W hr)

/-- **The upper reference** `μ_𝔅 = μ̃_𝔅 / P_μ(r)` (`def:upper-reference`). -/
noncomputable def upperReference (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    FiniteLaw (Slot → X) :=
  weightedCompletion (upCoeff W r) (upCoeff_nonneg W hr) (upPoly_pos W hr) (upComponent F)

/-- The unnormalized law `μ̃_𝔅`. -/
noncomputable def upperTilde (F : UpperFieldLaws X) (W : UpperWeights) (r : ℝ) :
    ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  tildeMeasure (upCoeff W r) (upComponent F)

/-- **`μ̃_𝔅` is a nonnegative measure of mass `P_μ(r) ≥ 1`** (`eq:independent-fold-polynomial`). -/
theorem upperTilde_mass (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    upperTilde F W r (fun _ => 1) = upPoly W r ∧ 1 ≤ upPoly W r ∧
      ∀ f : (Slot → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ upperTilde F W r f :=
  by
  refine ⟨?_, one_le_upPoly W hr, fun f hf => ?_⟩
  · unfold upperTilde
    rw [tildeMeasure_mass]
    exact sum_upCoeff W r
  · unfold upperTilde tildeMeasure
    rw [LinearMap.sum_apply]
    refine sum_nonneg fun i _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg (upCoeff_nonneg W hr i) ((upComponent F i).expect_nonneg hf)

theorem upperReference_eq (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r) :
    signedIntegral (upperReference F W hr).weight = (upPoly W r)⁻¹ • upperTilde F W r := by
  unfold upperReference upperTilde
  rw [signedIntegral_weightedCompletion, sum_upCoeff]

/-- **Uniform one-slot marginals** when every field law has uniform vertex marginals. -/
theorem upperReference_uniform [Nonempty X] (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r)
    (h2 : ∀ f₀ f₁ (o : f₀.Obj × f₁.Obj × Fin 2) (g : X → ℝ),
      (F.two f₀ f₁).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g)
    (h1 : ∀ f₀ f₁ (o : f₀.Obj × f₁.Obj × Fin 1) (g : X → ℝ),
      (F.one f₀ f₁).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g) :
    HasUniformMarginals (upperReference F W hr) := by
  refine weightedCompletion_uniform _ _ _ _ fun i => ?_
  rcases i with ⟨b, t, φ⟩
  cases b
  · exact emit_uniform _ _ (h1 _ _)
  · exact emit_uniform _ _ (h2 _ _)

/-- **The one-layer diagonal copies are positive at `ι`.** -/
theorem upperDiag_reserved_positive (F : UpperFieldLaws X) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) :
    reservedCut.Positive (signedIntegral (upComponent F (false, ⟨t, φ⟩)).weight) :=
  emit_positive _ _ _ (upDiagEmission_reserved _ _)

/-- **Square-affine invariance (R3)** of the upper reference, when every field law is invariant
under a given label map `T`. -/
theorem upperReference_invariant (F : UpperFieldLaws X) (W : UpperWeights) {r : ℝ} (hr : 0 ≤ r)
    (T : X → X)
    (h2 : ∀ f₀ f₁ (H : (f₀.Obj × f₁.Obj × Fin 2 → X) → ℝ),
      (F.two f₀ f₁).expect (fun y => H (fun o => T (y o))) = (F.two f₀ f₁).expect H)
    (h1 : ∀ f₀ f₁ (H : (f₀.Obj × f₁.Obj × Fin 1 → X) → ℝ),
      (F.one f₀ f₁).expect (fun y => H (fun o => T (y o))) = (F.one f₀ f₁).expect H)
    (H : (Slot → X) → ℝ) :
    (upperReference F W hr).expect (fun z => H (fun v => T (z v))) =
      (upperReference F W hr).expect H := by
  unfold upperReference
  rw [expect_weightedCompletion, expect_weightedCompletion]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  congr 1
  rcases j with ⟨b, t, φ⟩
  cases b
  · simp only [upComponent, expect_emit]
    exact h1 _ _ (fun y => H (y ∘ _))
  · simp only [upComponent, expect_emit]
    exact h2 _ _ (fun y => H (y ∘ _))

/-! ## The paper's field laws -/

/-- The two-layer graph `G_{φ₀φ₁,j}` of two field types (`subsec:push:layer72spectral`). -/
def fieldGraph (f₀ f₁ : FType) (Λ : Type) [Fintype Λ] : OrientedGraph (f₀.Obj × f₁.Obj × Λ) :=
  twoLayerGraph f₀.rel f₁.rel f₀.rel_proper f₁.rel_proper Λ

/-- The root `G_{LL,2}` is `Sarkozy.Labellings.rootGraph`. -/
theorem fieldGraph_LL : fieldGraph .L .L (Fin 2) = rootGraph := rfl

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- Nonemptiness of the labelling sets of the eighteen graphs `G_{φ₀φ₁,j}` at every prime of
the block (discharged for large primes by `exists_injLabellings_nonempty`). -/
structure UpperNonempty : Prop where
  two : ∀ f₀ f₁ i, (injLabellings (ZMod (pr i)) (fieldGraph f₀ f₁ (Fin 2))).Nonempty
  one : ∀ f₀ f₁ i, (injLabellings (ZMod (pr i)) (fieldGraph f₀ f₁ (Fin 1))).Nonempty

/-- **The field laws of an upper block**: `λ_𝔅(G_{φ₀φ₁,j})`, `j = 1, 2`. -/
noncomputable def upperBlockFieldLaws (hne : UpperNonempty pr) :
    UpperFieldLaws (BlockLabel pr) where
  two f₀ f₁ := blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁)
  one f₀ f₁ := blockGraphLaw pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)

/-- **The reference law of an upper block** (`def:upper-reference`, `def:construction`(b)). -/
noncomputable def upperBlockReference (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r) : FiniteLaw (Slot → BlockLabel pr) :=
  upperReference (upperBlockFieldLaws pr hne) W hr

theorem upperBlockReference_uniform (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r) : HasUniformMarginals (upperBlockReference pr hne W hr) :=
  upperReference_uniform (upperBlockFieldLaws pr hne) W hr
    (fun f₀ f₁ => blockGraphLaw_vertex_uniform pr (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁))
    (fun f₀ f₁ => blockGraphLaw_vertex_uniform pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁))

/-- **(R3) for the upper block law.** -/
theorem upperBlockReference_affine (hne : UpperNonempty pr) (W : UpperWeights) {r : ℝ}
    (hr : 0 ≤ r) (α β : BlockLabel pr) (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1)
    (H : (Slot → BlockLabel pr) → ℝ) :
    (upperBlockReference pr hne W hr).expect (fun z => H (fun v i => α i * z v i + β i)) =
      (upperBlockReference pr hne W hr).expect H :=
  upperReference_invariant (upperBlockFieldLaws pr hne) W hr (fun x i => α i * x i + β i)
    (fun f₀ f₁ H' => blockGraphLaw_expect_affine pr (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁)
      α β hα H')
    (fun f₀ f₁ H' => blockGraphLaw_expect_affine pr (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)
      α β hα H') H

end Block

/-! ## The tail datum (`def:record:upper-bands`(e)) -/

/-- **The fifty weights of the tail datum** (`upper_v2_local.json`, `pieces[-1].weights`): the
two-layer weights `w_𝔱`, `𝔱 = (𝔱₀, 𝔱₁)`. -/
def tailW : PType → PType → ℚ
  | .L, .L => 1 | .L, .D => 113 | .D, .L => 113 | .L, .S => 2373 / 20 | .S, .L => 2373 / 20
  | .D, .D => 2712 | .L, .R => 43392 | .R, .L => 43392 | .D, .S => 16611 / 5
  | .S, .D => 16611 / 5 | .L, .C => 111083520 / 7 | .C, .L => 111083520 / 7
  | .D, .R => 1214976 | .R, .D => 1214976 | .S, .S => 348831 / 100
  | .D, .C => 444334080 | .C, .D => 444334080 | .S, .R => 6378624 / 5
  | .R, .S => 6378624 / 5 | .S, .C => 466550784 | .C, .S => 466550784
  | .R, .R => 54977664 / 5 | .R, .C => 4021223424 | .C, .R => 4021223424
  | .C, .C => 242613813248 / 7

/-- The one-layer (reserved) weights `v_𝔱` of the tail datum (`reserved_weights`). -/
def tailV : PType → PType → ℚ
  | .L, .L => 45 | .L, .D => 1017 | .D, .L => 1017 | .L, .S => 21357 / 20 | .S, .L => 21357 / 20
  | .D, .D => 10848 | .L, .R => 303744 | .R, .L => 303744 | .D, .S => 56952 / 5
  | .S, .D => 56952 / 5 | .L, .C => 111083520 | .C, .L => 111083520
  | .D, .R => 3644928 | .R, .D => 3644928 | .S, .S => 298998 / 25
  | .D, .C => 1333002240 | .C, .D => 1333002240 | .S, .R => 19135872 / 5
  | .R, .S => 19135872 / 5 | .S, .C => 1399652352 | .C, .S => 1399652352
  | .R, .R => 73809792 / 5 | .R, .C => 5398659072 | .C, .R => 5398659072
  | .C, .C => 242613813248 / 7

/-- A completion input `(d, f, h, M)` (`def:record:upper-bands`(c)). -/
structure CompletionInput where
  d : ℚ
  f : ℚ
  h : ℚ
  M : ℚ

/-- The ordinary inputs of the tail datum: `(113, 258, 120)` for `L`, `(24, 30, 11)` for `F`,
`(28, 8, 1)` for `E`, with `M = 21/20`. -/
def tailOrdinary : FType → CompletionInput
  | .L => ⟨113, 258, 120, 21 / 20⟩
  | .F => ⟨24, 30, 11, 21 / 20⟩
  | .E => ⟨28, 8, 1, 21 / 20⟩

/-- The reserved inputs of the tail datum: `(12, 18, 10)`, `(5, 5, 3)`, `(5, 3, 1)`, `M = 21/20`. -/
def tailReserved : FType → CompletionInput
  | .L => ⟨12, 18, 10, 21 / 20⟩
  | .F => ⟨5, 5, 3, 21 / 20⟩
  | .E => ⟨5, 3, 1, 21 / 20⟩

/-- The caps `k_𝔱 = k_{𝔣(𝔱)}` of the tail datum: `k_LL = 45`, `k_LF = 9`, `k_LE = 7`, `k_FF = 4`,
`k_FE = 3`, `k_EE = 1` (unordered field pairs). -/
def tailFieldCap : FType → FType → ℚ
  | .L, .L => 45 | .L, .F => 9 | .F, .L => 9 | .L, .E => 7 | .E, .L => 7
  | .F, .F => 4 | .F, .E => 3 | .E, .F => 3 | .E, .E => 1

/-- `eq:upper-slice`: the four conditions `a_D ≥ d a_L`, `a_S ≥ M a_D`, `a_R ≥ f a_D + h a_S`,
`a_C a_S ≥ a_R²` on five weights `a`. -/
def SliceOK (I : CompletionInput) (a : PType → ℚ) : Prop :=
  I.d * a .L ≤ a .D ∧ I.M * a .D ≤ a .S ∧ I.f * a .D + I.h * a .S ≤ a .R ∧ a .R ^ 2 ≤ a .C * a .S

/-- The slice of the coordinate `c` at the type `t'` of the other coordinate:
`s ↦ w_{(s, t')}` (`c = 0`) or `s ↦ w_{(t', s)}` (`c = 1`). -/
def slice (w : PType → PType → ℚ) (c : Fin 2) (t' : PType) (s : PType) : ℚ :=
  if c = 0 then w s t' else w t' s

/-- **The 105 inequalities of `def:record:upper-bands`(d)**: the forty slice inequalities of
the weights `w` with the ordinary inputs, the forty of `v` with the reserved inputs (each at the
field type of the other coordinate), and the 25 dominations `v_𝔱 ≥ k_𝔱 w_𝔱`. -/
def UpperGates (w v : PType → PType → ℚ) (ord res : FType → CompletionInput)
    (cap : FType → FType → ℚ) : Prop :=
  (∀ c t', SliceOK (ord t'.field) (slice w c t')) ∧
    (∀ c t', SliceOK (res t'.field) (slice v c t')) ∧
    ∀ t₀ t₁, cap t₀.field t₁.field * w t₀ t₁ ≤ v t₀ t₁

/-- **The tail datum satisfies its 105 completion and domination gates** (exact rational
arithmetic; `def:record:upper-bands`(e), last item, and `cert:upper-completion`). -/
theorem tailDatum_gates : UpperGates tailW tailV tailOrdinary tailReserved tailFieldCap := by
  refine ⟨?_, ?_, ?_⟩
  · intro c t'
    fin_cases c <;> cases t' <;>
      norm_num [SliceOK, slice, tailW, tailOrdinary, PType.field]
  · intro c t'
    fin_cases c <;> cases t' <;>
      norm_num [SliceOK, slice, tailV, tailReserved, PType.field]
  · intro t₀ t₁
    cases t₀ <;> cases t₁ <;> norm_num [tailW, tailV, tailFieldCap, PType.field]

/-- **The tail weights as an `UpperWeights`.** -/
noncomputable def tailWeights : UpperWeights where
  w t₀ t₁ := (tailW t₀ t₁ : ℝ)
  v t₀ t₁ := (tailV t₀ t₁ : ℝ)
  w_LL := by norm_num [tailW]
  w_nonneg t₀ t₁ := by cases t₀ <;> cases t₁ <;> norm_num [tailW]
  v_nonneg t₀ t₁ := by cases t₀ <;> cases t₁ <;> norm_num [tailV]

/-- **The normalizing polynomial of the tail law is the paper's** (`def:tail-law`):
`P_μ(r) = 1 + (5988/5) r + (15232626/25) r² + (24807984744/175) r³ + (50638290432/5) r⁴
+ (621170191872/5) r⁵ + (1877429977088/7) r⁶ + (970455252992/7) r⁷`. -/
theorem tailPoly_eq (r : ℝ) :
    upPoly tailWeights r = 1 + 5988 / 5 * r + 15232626 / 25 * r ^ 2 +
      24807984744 / 175 * r ^ 3 + 50638290432 / 5 * r ^ 4 + 621170191872 / 5 * r ^ 5 +
      1877429977088 / 7 * r ^ 6 + 970455252992 / 7 * r ^ 7 := by
  unfold upPoly
  rw [Fintype.sum_prod_type]
  simp only [PType.sum_pType]
  simp only [tailWeights, tailW, tailV, PType.mult, PType.deg]
  push_cast
  ring

/-! ## The tail law at one prime (`def:tail-law`) -/

section Tail

variable (p : ℕ) [Fact p.Prime]

/-- Nonemptiness of the labelling sets of the eighteen graphs at the prime `p`. -/
structure TailNonempty : Prop where
  two : ∀ f₀ f₁, (injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 2))).Nonempty
  one : ∀ f₀ f₁, (injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 1))).Nonempty

/-- The field laws at the single prime `p`: `λ_p(G_{φ₀φ₁,j})`. -/
noncomputable def tailFieldLaws (hne : TailNonempty p) : UpperFieldLaws (ZMod p) where
  two f₀ f₁ := graphLaw (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁)
  one f₀ f₁ := graphLaw (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁)

/-- `r = p^{-1/2}`. -/
noncomputable def tailR : ℝ := (p : ℝ) ^ (-(1 / 2 : ℝ))

omit [Fact p.Prime] in
theorem tailR_nonneg : 0 ≤ tailR p := Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- **The tail law at `p`** (`def:tail-law`): the upper reference at the single prime `p` with
the weights of the tail datum, `μ_p = μ̃_p / P_μ(p^{-1/2})`. The paper uses it at every prime
`p ≥ P₄` of either class; the definition makes sense at every prime with nonempty labelling
sets. -/
noncomputable def tailLaw (hne : TailNonempty p) : FiniteLaw (Slot → ZMod p) :=
  upperReference (tailFieldLaws p hne) tailWeights (tailR_nonneg p)

/-- **`lem:tail-law`(iii), mass**: `μ̃_p(1) = P_μ(r) = 1 + h_p` with the paper's coefficients. -/
theorem tailTilde_mass (hne : TailNonempty p) :
    upperTilde (tailFieldLaws p hne) tailWeights (tailR p) (fun _ => 1) =
      1 + 5988 / 5 * tailR p + 15232626 / 25 * tailR p ^ 2 + 24807984744 / 175 * tailR p ^ 3 +
        50638290432 / 5 * tailR p ^ 4 + 621170191872 / 5 * tailR p ^ 5 +
        1877429977088 / 7 * tailR p ^ 6 + 970455252992 / 7 * tailR p ^ 7 := by
  rw [(upperTilde_mass _ tailWeights (tailR_nonneg p)).1, tailPoly_eq]

/-- **`lem:tail-law`(ii), uniform marginals**: every one-slot marginal of the tail law is
uniform on `𝔽_p`. -/
theorem tailLaw_uniform (hne : TailNonempty p) : HasUniformMarginals (tailLaw p hne) :=
  upperReference_uniform (tailFieldLaws p hne) tailWeights (tailR_nonneg p)
    (fun f₀ f₁ => graphLaw_vertex_uniform (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁))
    (fun f₀ f₁ => graphLaw_vertex_uniform (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁))

/-- **`lem:tail-law`(ii), invariance**: the tail law is invariant under the square-affine maps
`z_v ↦ s z_v + u` (`s` a nonzero square, `u ∈ 𝔽_p`). -/
theorem tailLaw_affine (hne : TailNonempty p) {s : ZMod p} (hs : quadraticChar (ZMod p) s = 1)
    (u : ZMod p) (H : (Slot → ZMod p) → ℝ) :
    (tailLaw p hne).expect (fun z => H (fun v => s * z v + u)) = (tailLaw p hne).expect H :=
  upperReference_invariant (tailFieldLaws p hne) tailWeights (tailR_nonneg p) (fun x => s * x + u)
    (fun f₀ f₁ H' => graphLaw_expect_affine (fieldGraph f₀ f₁ (Fin 2)) (hne.two f₀ f₁) hs u H')
    (fun f₀ f₁ H' => graphLaw_expect_affine (fieldGraph f₀ f₁ (Fin 1)) (hne.one f₀ f₁) hs u H') H

end Tail

end Sarkozy.PartV

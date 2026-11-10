module

public import Sarkozy.FiveType.TwoCoordinate

/-!
# The reserved cut: fold pairing (`lem:five-type`(e))

Source: `lem:five-type`(e), `paper/sections/17_completion_repair.tex`.

The layers are `Λ = {0, 1}` (`ZMod 2`). The layer swap is `ι`: `layerCut`, extended to the slots
by `reservedCut` (`Slots.lean`), and to the field labels by `fieldCut`. For a one-layer measure
`κ`, `Diag_ι(κ)` is the law carrying the same one-layer configuration on both layers: the
pushforward of `κ` along a diagonal embedding `D`. Here `D` is `diagW` on the slots and `diagF`
on the field labels; a one-layer configuration has the single layer `Unit`.

**Generic statements** (any finite slot sets, any cuts):
* `diag_positive_of_fixed`: a diagonal copy is fixed samplewise by `ι`, so the copy of a
  nonnegative measure is positive at `ι` (`lem:commoncut`(i)).
* `pair_term_positive`: if `Π ⪰_ι -K Diag_ι(Π^{(1)})`, `W ≥ 0` and `V ≥ K W`, then
  `W Π + V Diag_ι(Π^{(1)}) ⪰_ι 0`. This is the display of the proof of (e), with
  `W = w_t r^{deg t}`, `V = v_t r^{deg t + 1}` and `K = k_t r`.
* `below_pullback`: emissions inherit the order. If `λ ⪰_ι -c Diag_ι(λ^{(1)})` for a field law
  and its one-layer law, then the same holds for their images under an emission `y ↦ y ∘ π`
  that intertwines the layer swaps (`CutMap`) and commutes with the diagonal embeddings
  (`lem:commoncut`(v), via `Positive.pullback`).
* `diag_below_halfLocal`: a diagonal embedding that is half-local for a chamber cut on the
  one-layer and the two-layer slots preserves the order `⪰_ϑ` (`lem:commoncut`(v)).

**Two coordinates** (`def:two-coordinate-five-type`, with the two-layer field laws `lam2` and
the one-layer field laws `lam1`):
* `comp_below_of_field`: a field-law bound `λ ⪰_ι -c Diag_ι(λ^{(1)})` gives the same bound for
  every component `Π_{t,φ}` built from that field law. So merges and constants, which use only
  some objects, inherit it.
* `fold_pairing_two`: the paired measure
  `μ̃ = ∑_t w_t r^{deg t} π_{t,2} + r ∑_t v_t r^{deg t} Diag_ι(π_{t,1})` satisfies `μ̃ ⪰_ι 0`,
  when every two-layer component satisfies `Π_{t,φ} ⪰_ι -k_t r Diag_ι(Π^{(1)}_{t,φ})` and
  `v_t ≥ k_t w_t ≥ 0`.
* `diag_positive_cut0`, `diag_positive_cut1` (and `diag_below_cut0`, `diag_below_cut1` for the
  order): `Diag_ι` carries reflection positivity at `ϑ_{c,i}` of the one-layer slots to
  `ϑ_{c,i}` of the two-layer slots.
* `below_mono_coeff`: a component may be used with a smaller proved coefficient.
* `reserved_rp_two_of_field`: the same conclusion from field-law bounds
  `λ_{𝔣₀𝔣₁} ⪰_ι -κ r Diag_ι(λ^{(1)}_{𝔣₀𝔣₁})` with `κ_{𝔣(t₀)𝔣(t₁)} ≤ k_t`.
* **`reserved_rp_two`**: if the two-layer measure with the weights `w_t r^{deg t}` and the
  one-layer measure with the weights `v_t r^{deg t}` are reflection positive at every chamber
  cut of both coordinates, then `μ̃` is reflection positive at every `ϑ_{c,i}` and at `ι`. The
  chamber hypotheses are the conclusions of (b), (c), (d) or (f) (`two_coordinate_rp`, with
  root envelopes in the hypotheses of (b), (c), (f)).

The argument uses each component only through its own order at `ι`, and the one-layer sums only
through their own completion inequalities. So a component may carry any proved coefficient, and
`Π^{(1)}` need not be the one-layer marginal of `Π`: this is the last sentence of (e).

**Scope.** The paper states (e) for one coordinate and for two coordinates. The generic lemmas
cover both. The concrete instance proved here is the two-coordinate one. The one-coordinate
components of `Datum` are written with configurations `ℤ/6ℤ → 𝔛`, where the layer is inside
the label `𝔛 = X^Λ`. Applying the generic lemmas to them needs the uncurried slot set
`ℤ/6ℤ × Λ`; that instance is `FiveType/ReservedCutOne.lean`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings ReflectionCut TwoCoord

namespace Reserved

/-! ## Generic statements -/

section Generic

variable {V U X : Type*} [Fintype V] [DecidableEq V]

theorem push_apply {Ω Ξ : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (e : Ω → Ξ) (f : Ξ → ℝ) :
    pushFunctional L e f = L (f ∘ e) := rfl

/-- **A diagonal copy is positive at the cut that fixes it samplewise** (`lem:commoncut`(i)):
if `D z' ∘ ι = D z'` for every one-layer configuration `z'` and `κ` is a nonnegative measure,
then `Diag_ι(κ) = D_* κ` is reflection positive at `ι`. -/
theorem diag_positive_of_fixed (ι : ReflectionCut V) (D : (U → X) → (V → X))
    (hD : ∀ z', D z' ∘ ι.flip = D z') {κ : ((U → X) → ℝ) →ₗ[ℝ] ℝ}
    (hκ : ∀ f, (∀ z, 0 ≤ f z) → 0 ≤ κ f) : ι.Positive (pushFunctional κ D) := by
  have hform : ∀ F G : (ι.Half → X) → ℝ, ι.form (pushFunctional κ D) F G =
      κ (fun z' => F (fun v => D z' v.1) * G (fun v => D z' v.1)) := by
    intro F G
    change κ (fun z' => F (fun v => D z' v.1) * G (fun v => D z' (ι.flip v.1))) = _
    congr 1
    funext z'
    have h := congrFun (hD z')
    simp only [Function.comp_apply] at h
    simp only [h]
  constructor
  · intro F G
    rw [hform, hform]
    congr 1
    funext z'
    ring
  · intro F
    rw [hform]
    exact hκ _ fun z' => mul_self_nonneg _

/-- **One pair of the fold pairing**: if `Π ⪰_ι -K Diag_ι(Π^{(1)})`, `0 ≤ W` and `K W ≤ V`,
then `W Π + V Diag_ι(Π^{(1)}) ⪰_ι 0`. This is the display in the proof of (e), with
`W = w_t r^{deg t}`, `V = v_t r^{deg t + 1}`, `K = k_t r`, so that
`V - K W = (v_t - k_t w_t) r^{deg t + 1}`. -/
theorem pair_term_positive (ι : ReflectionCut V) (D : (U → X) → (V → X))
    (hD : ∀ z', D z' ∘ ι.flip = D z') {P2 : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    {P1 : ((U → X) → ℝ) →ₗ[ℝ] ℝ} (hP1 : ∀ f, (∀ z, 0 ≤ f z) → 0 ≤ P1 f) {K W V' : ℝ}
    (hbound : ι.Below (-K • pushFunctional P1 D) P2) (hW : 0 ≤ W) (hKW : K * W ≤ V') :
    ι.Positive (W • P2 + V' • pushFunctional P1 D) := by
  have hdiag := diag_positive_of_fixed ι D hD hP1
  have h1 : ι.Positive (W • (P2 - -K • pushFunctional P1 D)) := hbound.smul hW
  have h2 : ι.Positive ((V' - K * W) • pushFunctional P1 D) := hdiag.smul (by linarith)
  have heq : W • P2 + V' • pushFunctional P1 D =
      W • (P2 - -K • pushFunctional P1 D) + (V' - K * W) • pushFunctional P1 D := by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    ring
  rw [heq]
  exact h1.add h2

/-- **Emissions inherit the order at the layer swap** (`lem:commoncut`(v)). Let `π` carry the
layer swap `ιB` of the slots to the layer swap `ιA` of the field labels (`CutMap`), and let the
diagonal embeddings commute with it, `D_A(y') ∘ π = D_B(y' ∘ π₁)`. If
`λ ⪰_{ιA} -c Diag(λ^{(1)})`, then `π^* λ ⪰_{ιB} -c Diag(π₁^* λ^{(1)})`. -/
theorem below_pullback {VA UA UB : Type*} [Fintype VA] [DecidableEq VA]
    (ιA : ReflectionCut VA) (ιB : ReflectionCut V) (π : V → VA) (hπ : CutMap ιB ιA π)
    (π1 : UB → UA) (DA : (UA → X) → (VA → X)) (DB : (UB → X) → (V → X))
    (hcomm : ∀ y', DA y' ∘ π = DB (y' ∘ π1)) {lam2 : ((VA → X) → ℝ) →ₗ[ℝ] ℝ}
    {lam1 : ((UA → X) → ℝ) →ₗ[ℝ] ℝ} {c : ℝ} (h : ιA.Below (-c • pushFunctional lam1 DA) lam2) :
    ιB.Below (-c • pushFunctional (ReflectionCut.pullback lam1 π1) DB)
      (ReflectionCut.pullback lam2 π) := by
  have hp := Positive.pullback hπ h
  have heq : ReflectionCut.pullback (lam2 - -c • pushFunctional lam1 DA) π =
      ReflectionCut.pullback lam2 π - -c • pushFunctional (ReflectionCut.pullback lam1 π1) DB := by
    refine LinearMap.ext fun f => ?_
    change (lam2 - -c • pushFunctional lam1 DA) (fun y => f (y ∘ π)) =
      lam2 (fun y => f (y ∘ π)) - -c * lam1 (fun y' => f (DB (y' ∘ π1)))
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, push_apply]
    congr 3
    funext y'
    simp only [Function.comp_apply, hcomm]
  change ιB.Positive _
  rw [← heq]
  exact hp

/-- **A half-local diagonal embedding preserves the order at a chamber cut**
(`lem:commoncut`(v)): `Diag` maps `L ⪯_{c₁} M` to `Diag L ⪯_{c₂} Diag M`. -/
theorem diag_below_halfLocal {W' : Type*} [Fintype U] [DecidableEq U] [Fintype W']
    [DecidableEq W'] (c1 : ReflectionCut U) (c2 : ReflectionCut W') (D : (U → X) → (W' → X))
    (φ : (c1.Half → X) → (c2.Half → X))
    (hplus : ∀ z, (fun w : c2.Half => D z w.1) = φ (fun v : c1.Half => z v.1))
    (hminus : ∀ z, (fun w : c2.Half => D z (c2.flip w.1)) = φ (fun v : c1.Half => z (c1.flip v.1)))
    {L M : ((U → X) → ℝ) →ₗ[ℝ] ℝ} (h : c1.Below L M) :
    c2.Below (pushFunctional L D) (pushFunctional M D) := by
  have hp := positive_push_halfLocal c2 h D φ hplus hminus
  have heq : pushFunctional (M - L) D = pushFunctional M D - pushFunctional L D :=
    LinearMap.ext fun _ => rfl
  change c2.Positive _
  rw [← heq]
  exact hp

/-- **A smaller proved coefficient may be used** (last sentence of (e)): if
`Π ⪰_ι -K' Diag_ι(Π^{(1)})` with `K' ≤ K`, then `Π ⪰_ι -K Diag_ι(Π^{(1)})`, because the
diagonal copy is positive at `ι`. -/
theorem below_mono_coeff (ι : ReflectionCut V) {P2 : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    {Q1 : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (hQ1 : ι.Positive Q1) {K K' : ℝ} (hK : K' ≤ K)
    (h : ι.Below (-K' • Q1) P2) : ι.Below (-K • Q1) P2 := by
  have h2 : ι.Positive ((K - K') • Q1) := hQ1.smul (by linarith)
  have heq : P2 - -K • Q1 = (P2 - -K' • Q1) + (K - K') • Q1 := by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    ring
  change ι.Positive _
  rw [heq]
  exact h.add h2

end Generic

/-! ## Two coordinates -/

section Two

variable {X : Type*} [Fintype X]

/-- The layer swap `ι` on the two-layer field labels `O₀ × O₁ × {0, 1}`. -/
def fieldCut (O0 O1 : Type*) [Fintype O0] [DecidableEq O0] [Fintype O1] [DecidableEq O1] :
    ReflectionCut (O0 × O1 × ZMod 2) :=
  (layerCut.prodRight O1).prodRight O0

/-- The diagonal embedding of one-layer field labels: both layers carry the one-layer label. -/
def diagF {O0 O1 : Type*} (y' : O0 × O1 × Unit → X) : O0 × O1 × ZMod 2 → X :=
  fun p => y' (p.1, p.2.1, ())

/-- The diagonal embedding of one-layer slot configurations, `z_{(u,ℓ)} = z'_u`. -/
def diagW (z' : ZMod 6 × ZMod 6 × Unit → X) : ZMod 6 × ZMod 6 × ZMod 2 → X :=
  fun w => z' (w.1, w.2.1, ())

/-- The slot map of the emission `e_φ`: `(u₀, u₁, ℓ) ↦ (φ₀(u₀), φ₁(u₁), ℓ)`. -/
def emitMap {O0 O1 Λ' : Type*} (φ0 : ZMod 6 → O0) (φ1 : ZMod 6 → O1) (w : ZMod 6 × ZMod 6 × Λ') :
    O0 × O1 × Λ' :=
  (φ0 w.1, φ1 w.2.1, w.2.2)

omit [Fintype X] in
/-- **The diagonal copy is fixed samplewise by the reserved cut.** -/
theorem diagW_fixed (z' : ZMod 6 × ZMod 6 × Unit → X) : diagW z' ∘ reservedCut.flip = diagW z' :=
  rfl

/-- **The emission intertwines the layer swaps**: `π` maps the plus half (layer `0`) of the
slots into the plus half of the field labels, and commutes with the swaps. -/
theorem cutMap_emitMap {O0 O1 : Type*} [Fintype O0] [DecidableEq O0] [Fintype O1]
    [DecidableEq O1] (φ0 : ZMod 6 → O0) (φ1 : ZMod 6 → O1) :
    CutMap reservedCut (fieldCut O0 O1) (emitMap φ0 φ1) := by
  constructor
  · intro w hw
    have h := (Finset.mem_product.mp (Finset.mem_product.mp hw).2).2
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,
      Finset.mem_product.mpr ⟨Finset.mem_univ _, h⟩⟩
  · intro w
    rfl

variable (lam2 : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × ZMod 2 → X))
variable (lam1 : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Unit → X))

/-- A component is the pullback of its field law along the emission's slot map. -/
theorem comp_eq_pullback {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ']
    (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ' → X)) (t0 : Ty)
    (φ0 : PatIdx t0) (t1 : Ty) (φ1 : PatIdx t1) :
    comp lam t0 φ0 t1 φ1 =
      ReflectionCut.pullback (lawL (lam (fieldOf t0) (fieldOf t1)))
        (emitMap (patMap t0 φ0) (patMap t1 φ1)) :=
  LinearMap.ext fun _ => rfl

/-- **Components inherit the field-law bound at `ι`** (last claims of (e)): if the two-layer
field law of `(𝔣(t₀), 𝔣(t₁))` satisfies `λ ⪰_ι -c Diag_ι(λ^{(1)})`, then so does every
component built from it, `Π_{t,φ} ⪰_ι -c Diag_ι(Π^{(1)}_{t,φ})`. This covers the merges and the
constants, which use only some objects of the field law. -/
theorem comp_below_of_field (t0 : Ty) (φ0 : PatIdx t0) (t1 : Ty) (φ1 : PatIdx t1) {c : ℝ}
    (h : (fieldCut (fieldOf t0).Obj (fieldOf t1).Obj).Below
      (-c • pushFunctional (lawL (lam1 (fieldOf t0) (fieldOf t1))) diagF)
      (lawL (lam2 (fieldOf t0) (fieldOf t1)))) :
    reservedCut.Below (-c • pushFunctional (comp lam1 t0 φ0 t1 φ1) diagW)
      (comp lam2 t0 φ0 t1 φ1) := by
  rw [comp_eq_pullback lam1, comp_eq_pullback lam2]
  exact below_pullback _ reservedCut _ (cutMap_emitMap _ _)
    (emitMap (patMap t0 φ0) (patMap t1 φ1)) diagF diagW (fun _ => rfl) h

theorem comp_nonneg {Λ' : Type*} [Fintype Λ'] [DecidableEq Λ']
    (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ' → X)) (t0 : Ty)
    (φ0 : PatIdx t0) (t1 : Ty) (φ1 : PatIdx t1) (f : (ZMod 6 × ZMod 6 × Λ' → X) → ℝ)
    (hf : ∀ z, 0 ≤ f z) : 0 ≤ comp lam t0 φ0 t1 φ1 f :=
  (lam (fieldOf t0) (fieldOf t1)).expect_nonneg fun _ => hf _

/-- The paired measure of (e) in two coordinates:
`μ̃ = ∑_t w_t r^{deg t} π_{t,2} + r ∑_t v_t r^{deg t} Diag_ι(π_{t,1})`. -/
noncomputable def pairedMeasure (w v : Ty → Ty → ℝ) (r : ℝ) :
    ((ZMod 6 × ZMod 6 × ZMod 2 → X) → ℝ) →ₗ[ℝ] ℝ :=
  Q2 lam2 (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1) +
    r • pushFunctional (Q2 lam1 (fun t0 t1 => v t0 t1 * r ^ stateDeg t0 t1)) diagW

/-- `μ̃` as a sum of pairs, one for each two-layer component. -/
theorem pairedMeasure_eq (w v : Ty → Ty → ℝ) (r : ℝ) :
    pairedMeasure lam2 lam1 w v r =
      ∑ t0, ∑ t1, ∑ φ0 : PatIdx t0, ∑ φ1 : PatIdx t1,
        ((w t0 t1 * r ^ stateDeg t0 t1) • comp lam2 t0 φ0 t1 φ1 +
          (v t0 t1 * r ^ (stateDeg t0 t1 + 1)) • pushFunctional (comp lam1 t0 φ0 t1 φ1) diagW) := by
  refine LinearMap.ext fun f => ?_
  simp only [pairedMeasure, Q2, piT2, LinearMap.add_apply, LinearMap.smul_apply,
    LinearMap.sum_apply, smul_eq_mul, push_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun t0 _ => Finset.sum_congr rfl fun t1 _ =>
    Finset.sum_congr rfl fun φ0 _ => Finset.sum_congr rfl fun φ1 _ => ?_
  rw [pow_succ]
  ring

/-- **`lem:five-type`(e), the reserved cut, two coordinates.** Suppose that every two-layer
component satisfies `Π_{t,φ} ⪰_ι -k_t r Diag_ι(Π^{(1)}_{t,φ})`, where `Π^{(1)}_{t,φ}` is the
one-layer component with the same patterns, and let `w_t, v_t ≥ 0` with `v_t ≥ k_t w_t`. Then
`μ̃ ⪰_ι 0`. -/
theorem fold_pairing_two (w v k : Ty → Ty → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hw : ∀ t0 t1, 0 ≤ w t0 t1) (hvk : ∀ t0 t1, k t0 t1 * w t0 t1 ≤ v t0 t1)
    (hcomp : ∀ t0 (φ0 : PatIdx t0) t1 (φ1 : PatIdx t1),
      reservedCut.Below (-(k t0 t1 * r) • pushFunctional (comp lam1 t0 φ0 t1 φ1) diagW)
        (comp lam2 t0 φ0 t1 φ1)) :
    reservedCut.Positive (pairedMeasure lam2 lam1 w v r) := by
  rw [pairedMeasure_eq]
  refine Positive.sum _ fun t0 _ => Positive.sum _ fun t1 _ =>
    Positive.sum _ fun φ0 _ => Positive.sum _ fun φ1 _ => ?_
  refine pair_term_positive reservedCut diagW diagW_fixed (comp_nonneg lam1 t0 φ0 t1 φ1)
    (hcomp t0 φ0 t1 φ1) (mul_nonneg (hw t0 t1) (pow_nonneg hr _)) ?_
  have h := mul_le_mul_of_nonneg_right (hvk t0 t1) (pow_nonneg hr (stateDeg t0 t1 + 1))
  calc k t0 t1 * r * (w t0 t1 * r ^ stateDeg t0 t1)
      = k t0 t1 * w t0 t1 * r ^ (stateDeg t0 t1 + 1) := by rw [pow_succ]; ring
    _ ≤ v t0 t1 * r ^ (stateDeg t0 t1 + 1) := h

omit [Fintype X] in
/-- **`Diag_ι` preserves reflection positivity at `ϑ_{0,i}`**: the diagonal embedding is
half-local for `ϑ_{0,i}` on the one-layer and on the two-layer slots. -/
theorem diag_positive_cut0 (i : ZMod 6) {L : ((ZMod 6 × ZMod 6 × Unit → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (cut0 Unit i).Positive L) : (cut0 (ZMod 2) i).Positive (pushFunctional L diagW) :=
  positive_push_halfLocal (cut0 (ZMod 2) i) h diagW
    (fun x w => x ⟨(w.1.1, w.1.2.1, ()), Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp w.2).1, Finset.mem_univ _⟩⟩)
    (fun _ => rfl) (fun _ => rfl)

omit [Fintype X] in
/-- **`Diag_ι` preserves reflection positivity at `ϑ_{1,i}`.** -/
theorem diag_positive_cut1 (i : ZMod 6) {L : ((ZMod 6 × ZMod 6 × Unit → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (cut1 Unit i).Positive L) : (cut1 (ZMod 2) i).Positive (pushFunctional L diagW) :=
  positive_push_halfLocal (cut1 (ZMod 2) i) h diagW
    (fun x w => x ⟨(w.1.1, w.1.2.1, ()), Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp (Finset.mem_product.mp w.2).2).1, Finset.mem_univ _⟩⟩⟩)
    (fun _ => rfl) (fun _ => rfl)

/-- **`lem:five-type`(e), conclusion.** If the two-layer measure with the weights
`w_t r^{deg t}` and the one-layer measure with the weights `v_t r^{deg t}` are reflection
positive at every chamber cut `ϑ_{c,i}` of both coordinates (by (b), (c), (d) or (f)), and the
component bounds and `v_t ≥ k_t w_t ≥ 0` of `fold_pairing_two` hold, then `μ̃` is reflection
positive at every chamber cut of both coordinates and at `ι`. -/
theorem reserved_rp_two (w v k : Ty → Ty → ℝ) {r : ℝ} (hr : 0 ≤ r)
    (hw : ∀ t0 t1, 0 ≤ w t0 t1) (hvk : ∀ t0 t1, k t0 t1 * w t0 t1 ≤ v t0 t1)
    (hcomp : ∀ t0 (φ0 : PatIdx t0) t1 (φ1 : PatIdx t1),
      reservedCut.Below (-(k t0 t1 * r) • pushFunctional (comp lam1 t0 φ0 t1 φ1) diagW)
        (comp lam2 t0 φ0 t1 φ1))
    (h2 : ∀ i, (cut0 (ZMod 2) i).Positive (Q2 lam2 (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1)) ∧
      (cut1 (ZMod 2) i).Positive (Q2 lam2 (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1)))
    (h1 : ∀ i, (cut0 Unit i).Positive (Q2 lam1 (fun t0 t1 => v t0 t1 * r ^ stateDeg t0 t1)) ∧
      (cut1 Unit i).Positive (Q2 lam1 (fun t0 t1 => v t0 t1 * r ^ stateDeg t0 t1))) :
    (∀ i, (cut0 (ZMod 2) i).Positive (pairedMeasure lam2 lam1 w v r) ∧
      (cut1 (ZMod 2) i).Positive (pairedMeasure lam2 lam1 w v r)) ∧
    reservedCut.Positive (pairedMeasure lam2 lam1 w v r) := by
  refine ⟨fun i => ⟨?_, ?_⟩, fold_pairing_two lam2 lam1 w v k hr hw hvk hcomp⟩
  · exact (h2 i).1.add ((diag_positive_cut0 i (h1 i).1).smul hr)
  · exact (h2 i).2.add ((diag_positive_cut1 i (h1 i).2).smul hr)

omit [Fintype X] in
/-- **`Diag_ι` preserves the order `⪰_ϑ` at `ϑ_{0,i}`.** -/
theorem diag_below_cut0 (i : ZMod 6) {L M : ((ZMod 6 × ZMod 6 × Unit → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (cut0 Unit i).Below L M) :
    (cut0 (ZMod 2) i).Below (pushFunctional L diagW) (pushFunctional M diagW) :=
  diag_below_halfLocal (cut0 Unit i) (cut0 (ZMod 2) i) diagW
    (fun x w => x ⟨(w.1.1, w.1.2.1, ()), Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp w.2).1, Finset.mem_univ _⟩⟩)
    (fun _ => rfl) (fun _ => rfl) h

omit [Fintype X] in
/-- **`Diag_ι` preserves the order `⪰_ϑ` at `ϑ_{1,i}`.** -/
theorem diag_below_cut1 (i : ZMod 6) {L M : ((ZMod 6 × ZMod 6 × Unit → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : (cut1 Unit i).Below L M) :
    (cut1 (ZMod 2) i).Below (pushFunctional L diagW) (pushFunctional M diagW) :=
  diag_below_halfLocal (cut1 Unit i) (cut1 (ZMod 2) i) diagW
    (fun x w => x ⟨(w.1.1, w.1.2.1, ()), Finset.mem_product.mpr
      ⟨Finset.mem_univ _, Finset.mem_product.mpr
        ⟨(Finset.mem_product.mp (Finset.mem_product.mp w.2).2).1, Finset.mem_univ _⟩⟩⟩)
    (fun _ => rfl) (fun _ => rfl) h

/-- **`lem:five-type`(e) from field-law bounds.** If every pair of field laws satisfies
`λ_{𝔣₀𝔣₁} ⪰_ι -κ_{𝔣₀𝔣₁} r Diag_ι(λ^{(1)}_{𝔣₀𝔣₁})`, and the state coefficients satisfy
`κ_{𝔣(t₀)𝔣(t₁)} ≤ k_t` (a component may be used with a smaller proved coefficient), then every
two-layer component satisfies the hypothesis of `fold_pairing_two`, and the conclusions of
`reserved_rp_two` hold under its chamber hypotheses. -/
theorem reserved_rp_two_of_field (w v k : Ty → Ty → ℝ) (κ : FieldTy → FieldTy → ℝ) {r : ℝ}
    (hr : 0 ≤ r) (hw : ∀ t0 t1, 0 ≤ w t0 t1) (hvk : ∀ t0 t1, k t0 t1 * w t0 t1 ≤ v t0 t1)
    (hκk : ∀ t0 t1, κ (fieldOf t0) (fieldOf t1) ≤ k t0 t1)
    (hfield : ∀ f0 f1, (fieldCut f0.Obj f1.Obj).Below
      (-(κ f0 f1 * r) • pushFunctional (lawL (lam1 f0 f1)) diagF) (lawL (lam2 f0 f1)))
    (h2 : ∀ i, (cut0 (ZMod 2) i).Positive (Q2 lam2 (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1)) ∧
      (cut1 (ZMod 2) i).Positive (Q2 lam2 (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1)))
    (h1 : ∀ i, (cut0 Unit i).Positive (Q2 lam1 (fun t0 t1 => v t0 t1 * r ^ stateDeg t0 t1)) ∧
      (cut1 Unit i).Positive (Q2 lam1 (fun t0 t1 => v t0 t1 * r ^ stateDeg t0 t1))) :
    (∀ i, (cut0 (ZMod 2) i).Positive (pairedMeasure lam2 lam1 w v r) ∧
      (cut1 (ZMod 2) i).Positive (pairedMeasure lam2 lam1 w v r)) ∧
    reservedCut.Positive (pairedMeasure lam2 lam1 w v r) := by
  refine reserved_rp_two lam2 lam1 w v k hr hw hvk (fun t0 φ0 t1 φ1 => ?_) h2 h1
  refine below_mono_coeff reservedCut
    (diag_positive_of_fixed reservedCut diagW diagW_fixed (comp_nonneg lam1 t0 φ0 t1 φ1))
    (mul_le_mul_of_nonneg_right (hκk t0 t1) hr) ?_
  exact comp_below_of_field lam2 lam1 t0 φ0 t1 φ1 (hfield _ _)

end Two

end Reserved

end Sarkozy.FiveType

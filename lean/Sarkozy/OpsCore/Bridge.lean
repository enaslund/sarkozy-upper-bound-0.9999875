module

public import Sarkozy.OpsCore.BracketOp
public import Sarkozy.PrimeGram.Features
public import Sarkozy.EnvelopeSteps.FeatureCorr
public import Sarkozy.PaperFrame.TailMarginal

@[expose] public section

/-!
# The bridge between `m_{0,𝔅}` on object triples and the actual half marginal (OPS-L)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(a) (the actual half marginal
`m₀ = g₀ ν_F` of the fold record); `paper/sections/23_envelopes.tex`, `subsec:envelope-tools`
(`L²(m_{φ,𝔅})`).

The record operators of `OpsCore` live on `L²(m)` of the half labellings `reservedCut.Half → X`,
with `m` the actual half marginal (`selMarg`, which is B8's `mOf` at the middle blocks:
`selMarg_eq_of_diag`). OPS-F's feature frame lives on `L²(m_{0,𝔅})` of the object triples
`Tri = ∀ p, F_p × F_p × F_p` (`m0B = ∏_p oldW_p/oldZ_p`). This file proves:

* **`plusMarginal_emit_mid`**: the plus marginal of a record emitted through a middle pattern `φ`
  is the push of the layer-`0` object marginal by the placement `placeH φ` (`u ↦ x(φ(u₀))`);
* `tensor_expect_place`: for a block law (a tensor over the primes) it factorizes over the primes;
* **`mOf_fold_eq_push`**: at a middle block of primes `p ≡ 3 (mod 4)`, `p ≥ 19`, the actual half
  marginal of the fold record `F_j` is **`push m0B (triPlace j)`**, with
  `triPlace j x = (u ↦ (x_p)_{fold_j(u₀)})_p` (B8's `m0`, PG's `m0_eq_oldW`);
* `triPlace_injective`: the placement is injective (the fold patterns are onto `Fin 3`);
* **`ip_push`**: `⟨f, g⟩_{push m ψ} = ⟨f ∘ ψ, g ∘ ψ⟩_m`, so the inner products, norms and frame
  bounds of OPS-F on `L²(m0B)` transfer to the half labellings (`ip_push_ext`: for functions on
  the triples, through their extension by `0` off the image of the injective `ψ`; `frame_push`);
* **`opPos_push`**: operator positivity (hence `OpLE`, the form of `hdom`) transfers from `L²(m)`
  to `L²(push m ψ)` for operators whose kernels correspond on the image (`ip_push_op`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps Sarkozy.SignedComponents Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.RecordExpansion Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.MiddleRecords

/-! ## The plus marginal of an emitted record -/

/-- The placement of an object labelling into a half labelling through a middle pattern:
`(u₀, u₁, 0) ↦ x(φ(u₀))`. -/
def placeH {X : Type*} {O : Type*} (φ : ZMod 6 → O) (x : O → X) : reservedCut.Half → X :=
  fun v => x (φ v.1.1)

/-- **The plus marginal of a middle record** is the push of its layer-`0` object marginal by
`placeH φ`, as an expectation. -/
theorem plusMarginal_emit_mid {X : Type} [Fintype X] [DecidableEq X] {O : Type} [Fintype O]
    [DecidableEq O] (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O)
    (h : reservedCut.Half → X) :
    plusMarginal reservedCut (emit lam (midEmission φ)).weight h =
      lam.expect (fun y => if placeH φ (fun o => y (o, 0)) = h then 1 else 0) := by
  have e1 : plusMarginal reservedCut (emit lam (midEmission φ)).weight h =
      (emit lam (midEmission φ)).expect
        (fun z => if (fun v : reservedCut.Half => z v.1) = h then 1 else 0) := by
    unfold plusMarginal FiniteLaw.expect
    refine sum_congr rfl fun z _ => ?_
    by_cases hz : (fun v : reservedCut.Half => z v.1) = h <;> simp [hz]
  rw [e1, expect_emit]
  refine FiniteLaw.expect_congr _ fun y => ?_
  have e2 : (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) =
      placeH φ (fun o => y (o, 0)) := plusHalf_mid φ y
  simp only [e2]

/-- **The block factorization**: for a tensor of laws over the primes, the placed layer-`0`
indicator factorizes. -/
theorem tensor_expect_place {ι : Type} [Fintype ι] [DecidableEq ι] {Y : ι → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] {O : Type} [Fintype O] [DecidableEq O]
    (μ : ∀ i, FiniteLaw (O × Fin 2 → Y i)) (φ : ZMod 6 → O) (h : reservedCut.Half → ∀ i, Y i) :
    (FiniteLaw.tensor μ).expect (fun y => if placeH φ (fun o => y (o, 0)) = h then 1 else 0) =
      ∏ i, (μ i).expect
        (fun y => if placeH φ (fun o => y (o, 0)) = (fun v => h v i) then 1 else 0) := by
  rw [Sarkozy.PaperFrame.tensor_expect_sum]
  have hind : ∀ z : ∀ i, O × Fin 2 → Y i,
      (if placeH φ (fun o => (fun v i => z i v) (o, 0)) = h then (1 : ℝ) else 0) =
        ∏ i, (if placeH φ (fun o => z i (o, 0)) = (fun v => h v i) then 1 else 0) := by
    intro z
    rw [Finset.prod_boole]
    congr 1
    apply propext
    constructor
    · intro hz i _
      funext v
      exact congrFun (congrFun hz v) i
    · intro hz
      funext v i
      exact congrFun (hz i (mem_univ i)) v
  simp only [hind, ← prod_mul_distrib]
  unfold FiniteLaw.expect
  exact (Fintype.prod_sum (fun i (y : O × Fin 2 → Y i) => (μ i).weight y *
    (if placeH φ (fun o => y (o, 0)) = (fun v => h v i) then (1 : ℝ) else 0))).symm

/-! ## The fold record of a middle block -/

section Fold

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The triple `(a, b, c)` as a labelling of the three fold objects. -/
def tri3 {K : Type*} (t : K × K × K) : Fin 3 → K := ![t.1, t.2.1, t.2.2]

/-- **The placement of object triples** into the half labellings of the fold record `F_j`:
`x ↦ (u ↦ (x_p)_{fold_j(u₀)})_p`. -/
def triPlace (j : Fin 2) (x : ∀ i, ZMod (pr i) × ZMod (pr i) × ZMod (pr i)) :
    reservedCut.Half → BlockLabel pr :=
  fun v i => tri3 (x i) (Labellings.fold (foldPat j) v.1.1)

/-- The fold patterns `F₁`, `F₂` are onto the three objects. -/
theorem foldPat_surjective (j : Fin 2) : Function.Surjective (Labellings.fold (foldPat j)) := by
  revert j
  decide

theorem tri3_injective {K : Type*} : Function.Injective (tri3 (K := K)) := by
  intro s t h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  have h2 := congrFun h 2
  simp only [tri3, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- **The placement of triples is injective.** -/
theorem triPlace_injective (j : Fin 2) : Function.Injective (triPlace pr j) := by
  intro x y h
  funext i
  apply tri3_injective
  funext o
  obtain ⟨u, hu⟩ := foldPat_surjective j o
  have hv : ((u, 0, 0) : Slot) ∈ reservedCut.half := (reserved_mem _).2 rfl
  have := congrFun (congrFun h ⟨(u, 0, 0), hv⟩) i
  simp only [triPlace] at this
  rw [← hu]
  exact this

/-- `∑` over triples of a function of `tri3`. -/
theorem sum_tri3 {K : Type} [Fintype K] [DecidableEq K] (G : (Fin 3 → K) → ℝ) :
    ∑ t : K × K × K, G (tri3 t) = ∑ x, G x := by
  rw [Sarkozy.PrimeGram.sum_triple, Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => ?_
  rw [Fintype.sum_prod_type]
  rfl

/-- **The actual half marginal of the fold record `F_j` of a middle block is the push of
`m_{0,𝔅}` by the placement of triples** (`lem:old-f-law`(a) at every prime, through B8's `m0` and
PG's `m0_eq_oldW`). Here `m0B` is `∏_p oldW_p/oldZ_p` on `Tri = ∀ p, F_p × F_p × F_p`. -/
theorem mOf_fold_eq_push (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr)
    (hR : ∀ i, ringChar (ZMod (pr i)) ≠ 2) (h3 : ∀ i, Fintype.card (ZMod (pr i)) % 4 = 3)
    (h19 : ∀ i, 19 ≤ Fintype.card (ZMod (pr i))) (j : Fin 2) :
    mOf (middleFrame pr hne root W I hr b h) (.inl j) =
      push (m0B (F := fun i => ZMod (pr i))) (triPlace pr j) := by
  funext g
  change plusMarginal reservedCut
    (emit (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2)
      (midEmission (Labellings.fold (foldPat j)))).weight g = _
  rw [plusMarginal_emit_mid, blockGraphLaw, tensor_expect_place]
  -- each prime: the layer-`0` marginal is B8's `m0`, i.e. `oldW/oldZ`
  have hprime : ∀ i, (graphLaw (foldGraph (Fin 2)) (hne.F2 i)).expect
      (fun y => if placeH (Labellings.fold (foldPat j)) (fun o => y (o, 0)) = (fun v => g v i)
        then (1 : ℝ) else 0) =
      ∑ t : ZMod (pr i) × ZMod (pr i) × ZMod (pr i),
        oldW t.1 t.2.1 t.2.2 / oldZ (F := ZMod (pr i)) *
          (if placeH (Labellings.fold (foldPat j)) (tri3 t) = (fun v => g v i) then 1 else 0) := by
    intro i
    have hm := m0_expect (hne.F2 i)
      (fun x => if placeH (Labellings.fold (foldPat j)) x = (fun v => g v i) then (1 : ℝ) else 0)
    change _ = (K0 (hne.F2 i)).expect _ at hm
    change (K0 (hne.F2 i)).expect _ = _
    refine Eq.trans hm.symm ?_
    unfold FiniteLaw.expect
    rw [← sum_tri3 (fun x => (m0 (hne.F2 i)).weight x *
      (if placeH (Labellings.fold (foldPat j)) x = (fun v => g v i) then (1 : ℝ) else 0))]
    refine sum_congr rfl fun t _ => ?_
    rw [Sarkozy.PrimeGram.m0_eq_oldW (hne.F2 i) (hR i) (h3 i) (h19 i)]
    rfl
  simp only [hprime]
  -- the push of `m0B`
  unfold push
  rw [sum_filter]
  have hpush : ∀ x : ∀ i, ZMod (pr i) × ZMod (pr i) × ZMod (pr i),
      (if triPlace pr j x = g then m0B (F := fun i => ZMod (pr i)) x else 0) =
        ∏ i, oldW (x i).1 (x i).2.1 (x i).2.2 / oldZ (F := ZMod (pr i)) *
          (if placeH (Labellings.fold (foldPat j)) (tri3 (x i)) = (fun v => g v i) then 1
            else 0) := by
    intro x
    rw [prod_mul_distrib, Finset.prod_boole]
    have hiff : triPlace pr j x = g ↔
        ∀ i ∈ univ, placeH (Labellings.fold (foldPat j)) (tri3 (x i)) = (fun v => g v i) := by
      constructor
      · intro hx i _
        funext v
        exact congrFun (congrFun hx v) i
      · intro hx
        funext v i
        exact congrFun (hx i (mem_univ i)) v
    by_cases hx : triPlace pr j x = g
    · simp only [hx, ↓reduceIte]
      rw [ite_eq_left_of_eq_true _ _ (eq_true (hiff.mp hx)), mul_one]
      rfl
    · have hn : ¬ ∀ i ∈ univ,
          placeH (Labellings.fold (foldPat j)) (tri3 (x i)) = (fun v => g v i) :=
        fun h' => hx (hiff.mpr h')
      simp only [hx, hn, ↓reduceIte, mul_zero]
  simp only [hpush]
  exact Fintype.prod_sum (fun i (t : ZMod (pr i) × ZMod (pr i) × ZMod (pr i)) =>
    oldW t.1 t.2.1 t.2.2 / oldZ (F := ZMod (pr i)) *
      (if placeH (Labellings.fold (foldPat j)) (tri3 t) = (fun v => g v i) then (1 : ℝ) else 0))

end Fold

/-! ## Inner products under the push -/

/-- **`⟨f, g⟩_{push m ψ} = ⟨f ∘ ψ, g ∘ ψ⟩_m`.** -/
theorem ip_push {O H : Type*} [Fintype O] [Fintype H] [DecidableEq H] (m : O → ℝ) (ψ : O → H)
    (f g : H → ℝ) : ip (push m ψ) f g = ip m (f ∘ ψ) (g ∘ ψ) := by
  unfold ip
  rw [sum_push m ψ (fun h => f h * g h)]
  rfl

/-- The extension by `0` of a function on `O` along an injective `ψ`. -/
noncomputable def extend0 {O H : Type*} [Fintype O] [DecidableEq H] (ψ : O → H) (f : O → ℝ) :
    H → ℝ :=
  fun x => ∑ o ∈ univ.filter (fun o => ψ o = x), f o

theorem extend0_comp {O H : Type*} [Fintype O] [DecidableEq H] {ψ : O → H}
    (hψ : Function.Injective ψ) (f : O → ℝ) : extend0 ψ f ∘ ψ = f := by
  funext o
  simp only [Function.comp_apply, extend0]
  rw [show univ.filter (fun o' => ψ o' = ψ o) = {o} by
    ext o'
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun h => hψ h, fun h => h ▸ rfl⟩]
  simp

/-- **Functions on the triples transfer**: for an injective `ψ`, the extensions by `0` have the
same inner products in `L²(push m ψ)` as the functions in `L²(m)`. So OPS-F's correlation and
frame bounds in `L²(m_{0,𝔅})` hold verbatim for the extended features in `L²(mOf)`. -/
theorem ip_push_ext {O H : Type*} [Fintype O] [Fintype H] [DecidableEq H] (m : O → ℝ) {ψ : O → H}
    (hψ : Function.Injective ψ) (f g : O → ℝ) :
    ip (push m ψ) (extend0 ψ f) (extend0 ψ g) = ip m f g := by
  rw [ip_push, extend0_comp hψ, extend0_comp hψ]

theorem extend0_sum {O H : Type*} [Fintype O] [DecidableEq H] (ψ : O → H) {V : Type*}
    [Fintype V] (h : V → O → ℝ) :
    extend0 ψ (fun x => ∑ v, h v x) = fun u => ∑ v, extend0 ψ (h v) u := by
  funext u
  unfold extend0
  rw [sum_comm]

/-- **A frame bound transfers along an injective placement**: if features on `O` satisfy
`‖∑ h_v‖² ≤ Γ ∑ ‖h_v‖²` in `L²(m)`, their extensions by `0` satisfy the same bound in
`L²(push m ψ)`. -/
theorem frame_push {O H : Type*} [Fintype O] [Fintype H] [DecidableEq H] (m : O → ℝ)
    {ψ : O → H} (hψ : Function.Injective ψ) {V : Type*} [Fintype V] (h : V → O → ℝ) {Γ : ℝ}
    (hfr : ip m (fun x => ∑ v, h v x) (fun x => ∑ v, h v x) ≤ Γ * ∑ v, ip m (h v) (h v)) :
    ip (push m ψ) (fun u => ∑ v, extend0 ψ (h v) u) (fun u => ∑ v, extend0 ψ (h v) u) ≤
      Γ * ∑ v, ip (push m ψ) (extend0 ψ (h v)) (extend0 ψ (h v)) := by
  rw [← extend0_sum, ip_push_ext m hψ]
  simp only [ip_push_ext m hψ]
  exact hfr

/-! ## Operator inequalities under the push -/

/-- The sum over `H` of a function vanishing off the image of an injective `ψ`. -/
theorem sum_of_image {O H : Type*} [Fintype O] [Fintype H] [DecidableEq H] {ψ : O → H}
    (hψ : Function.Injective ψ) (G : H → ℝ) (hG : ∀ u, (∀ x, ψ x ≠ u) → G u = 0) :
    ∑ u, G u = ∑ x, G (ψ x) := by
  rw [← sum_image (fun x _ y _ h => hψ h)]
  refine (sum_subset (subset_univ _) fun u _ hu => hG u fun x hx => hu ?_).symm
  exact mem_image.mpr ⟨x, mem_univ x, hx⟩

/-- **`⟨f, K g⟩_{push m ψ} = ⟨f ∘ ψ, K' (g ∘ ψ)⟩_m`** when the kernel of `K` relative to
`push m ψ` is that of `K'` relative to `m` on the image, and vanishes when the second point is
off the image (off the image in the first point it vanishes since `push m ψ = 0` there). -/
theorem ip_push_op {O H : Type*} [Fintype O] [DecidableEq O] [Fintype H] [DecidableEq H]
    (m : O → ℝ) {ψ : O → H} (hψ : Function.Injective ψ) (K : (H → ℝ) →ₗ[ℝ] (H → ℝ))
    (K' : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hK : ∀ x y, kern (push m ψ) K (ψ x) (ψ y) = kern m K' x y)
    (hK0 : ∀ u w, (∀ y, ψ y ≠ w) → kern (push m ψ) K u w = 0) (f g : H → ℝ) :
    ip (push m ψ) f (K g) = ip m (f ∘ ψ) (K' (g ∘ ψ)) := by
  have hpush0 : ∀ u, (∀ x, ψ x ≠ u) → push m ψ u = 0 := by
    intro u hu
    unfold push
    exact sum_eq_zero fun x hx => absurd (mem_filter.mp hx).2 (hu x)
  rw [ip_eq_kern, ip_eq_kern]
  rw [sum_of_image hψ _ fun u hu => sum_eq_zero fun w _ => by
    rw [show kern (push m ψ) K u w = 0 by unfold kern; rw [hpush0 u hu, zero_mul], zero_mul]]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_of_image hψ _ fun w hw => by rw [hK0 _ w hw, zero_mul]]
  refine sum_congr rfl fun y _ => ?_
  rw [hK]
  rfl

/-- **Operator positivity transfers along an injective placement** (kernels as in
`ip_push_op`). -/
theorem opPos_push {O H : Type*} [Fintype O] [DecidableEq O] [Fintype H] [DecidableEq H]
    (m : O → ℝ) {ψ : O → H} (hψ : Function.Injective ψ) {K : (H → ℝ) →ₗ[ℝ] (H → ℝ)}
    {K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (hK : ∀ x y, kern (push m ψ) K (ψ x) (ψ y) = kern m K' x y)
    (hK0 : ∀ u w, (∀ y, ψ y ≠ w) → kern (push m ψ) K u w = 0) (h : OpPos m K') :
    OpPos (push m ψ) K where
  symm f g := by
    rw [ip_push_op m hψ K K' hK hK0, ip_push_op m hψ K K' hK hK0]
    exact h.symm _ _
  nonneg f := by
    rw [ip_push_op m hψ K K' hK hK0]
    exact h.nonneg _

/-- **`OpLE` transfers along an injective placement** (the form of `hdom`). -/
theorem opLE_push {O H : Type*} [Fintype O] [DecidableEq O] [Fintype H] [DecidableEq H]
    (m : O → ℝ) {ψ : O → H} (hψ : Function.Injective ψ) {K₁ K₂ : (H → ℝ) →ₗ[ℝ] (H → ℝ)}
    {K₁' K₂' : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (hK₁ : ∀ x y, kern (push m ψ) K₁ (ψ x) (ψ y) = kern m K₁' x y)
    (hK₂ : ∀ x y, kern (push m ψ) K₂ (ψ x) (ψ y) = kern m K₂' x y)
    (hK₁0 : ∀ u w, (∀ y, ψ y ≠ w) → kern (push m ψ) K₁ u w = 0)
    (hK₂0 : ∀ u w, (∀ y, ψ y ≠ w) → kern (push m ψ) K₂ u w = 0) (h : OpLE m K₁' K₂') :
    OpLE (push m ψ) K₁ K₂ :=
  opPos_push m hψ (fun x y => by rw [kern_sub, kern_sub, hK₁, hK₂])
    (fun u w hw => by rw [kern_sub, hK₁0 u w hw, hK₂0 u w hw, sub_zero]) h

end Sarkozy.OpsCore

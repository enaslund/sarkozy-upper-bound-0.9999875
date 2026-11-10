module

public import Sarkozy.Slots
public import Sarkozy.Reflection.Coordinates
public import Sarkozy.Reflection.CommonCut

/-!
# Reflection positivity of chamber pullbacks of independent labels

Tools for the reference laws of Part V that draw one label per chamber independently (given
shared data) and copy it to the slots: the square-clique law of `lem:frontier:iidlocal`
(`paper/sections/19_prefix.tex`), part (i).

* `iidLaw ν`: the law of independent labels with common law `ν` on a finite index set.
* `iidLaw_positive`: an i.i.d. law is reflection positive at every cut of its index set. The
  form is `c.form (iidLaw ν) F G = E[F] E[G]` over independent copies of the half
  (`form_iidLaw`).
* `pullback L π`: the law of `y ∘ π` for `y ∼ L`. `Positive.pullback`: pullbacks along a map that
  carries one cut to another (`CutMap`) preserve reflection positivity. `pullback_positive_of_fixed`:
  the pullback of a nonnegative law along a map invariant under a cut is reflection positive
  (the labels are fixed samplewise).
* `chamberIid_positive`: a nonnegative mixture `∑_ω w_ω · pullback_{v ↦ v.1}(iidLaw ν_ω)` is
  reflection positive at every chamber cut of both chamber coordinates and at the reserved cut,
  hence at every cut of the slot family (`SlotReflectionPositive`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

namespace ReflectionCut

variable {I V X : Type*} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V] [Fintype X]

/-- Independent labels with common law `ν` on the index set `I`. -/
noncomputable def iidLaw (ν : FiniteLaw X) : ((I → X) → ℝ) →ₗ[ℝ] ℝ :=
  signedIntegral (fun y : I → X => ∏ i, ν.weight (y i))

/-- The cut form of an i.i.d. law factorizes over the two halves. -/
theorem form_iidLaw (c : ReflectionCut I) (ν : FiniteLaw X) (F G : (c.Half → X) → ℝ) :
    c.form (iidLaw ν) F G =
      (∑ x : c.Half → X, (∏ v, ν.weight (x v)) * F x) *
        (∑ x : c.Half → X, (∏ v, ν.weight (x v)) * G x) := by
  classical
  change (∑ y : I → X, (∏ i, ν.weight (y i)) *
    (F (fun v => y v.1) * G (fun v => y (c.flip v.1)))) = _
  rw [← Fintype.sum_equiv c.configurationEquiv.symm
    (fun p : (c.Half → X) × (c.Half → X) => (∏ i, ν.weight (c.join p.1 p.2 i)) *
      (F (fun v => c.join p.1 p.2 v.1) * G (fun v => c.join p.1 p.2 (c.flip v.1))))
    _ (fun _ => rfl)]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
  rw [c.prod_split (fun i => ν.weight (c.join x x' i))]
  simp only [join_plus, join_minus]
  ring

/-- **An i.i.d. law is reflection positive at every cut of its index set.** -/
theorem iidLaw_positive (c : ReflectionCut I) (ν : FiniteLaw X) : c.Positive (iidLaw ν) := by
  constructor
  · intro F G
    rw [form_iidLaw, form_iidLaw, mul_comm]
  · intro F
    rw [form_iidLaw]
    exact mul_self_nonneg _

/-- The law of `y ∘ π` for `y ∼ L`. -/
def pullback (L : ((I → X) → ℝ) →ₗ[ℝ] ℝ) (π : V → I) : ((V → X) → ℝ) →ₗ[ℝ] ℝ where
  toFun f := L (fun y => f (y ∘ π))
  map_add' f g := by
    change L (fun y => f (y ∘ π) + g (y ∘ π)) = L _ + L _
    exact L.map_add _ _
  map_smul' a f := by
    change L (fun y => a * f (y ∘ π)) = a * L _
    exact L.map_smul a _

/-- `π : V → I` carries the cut `c` of `V` to the cut `d` of `I`: it maps the plus half of `c`
into the plus half of `d` and intertwines the reflections. -/
structure CutMap (c : ReflectionCut V) (d : ReflectionCut I) (π : V → I) : Prop where
  half_mem : ∀ v ∈ c.half, π v ∈ d.half
  flip_comm : ∀ v, π (c.flip v) = d.flip (π v)

omit [Fintype X] in
/-- **Pullbacks along cut maps preserve reflection positivity.** -/
theorem Positive.pullback {c : ReflectionCut V} {d : ReflectionCut I} {π : V → I}
    (hπ : CutMap c d π) {L : ((I → X) → ℝ) →ₗ[ℝ] ℝ} (hL : d.Positive L) :
    c.Positive (ReflectionCut.pullback L π) := by
  -- a half-function on `c` is a half-function on `d` through `π`
  let lift : ((c.Half → X) → ℝ) → ((d.Half → X) → ℝ) := fun F x =>
    F (fun v => x ⟨π v.1, hπ.half_mem v.1 v.2⟩)
  have hform : ∀ F G, c.form (ReflectionCut.pullback L π) F G = d.form L (lift F) (lift G) := by
    intro F G
    change L (fun y => F (fun v => (y ∘ π) v.1) * G (fun v => (y ∘ π) (c.flip v.1))) =
      L (fun y => lift F (fun v => y v.1) * lift G (fun v => y (d.flip v.1)))
    congr 1
    funext y
    simp only [lift, Function.comp_apply, hπ.flip_comm]
  constructor
  · intro F G
    rw [hform, hform]
    exact hL.symmetric _ _
  · intro F
    rw [hform]
    exact hL.nonneg _

omit [Fintype I] [DecidableEq I] [Fintype X] in
/-- **The pullback along a map invariant under a cut is reflection positive** (each pulled-back
labelling is fixed by the reflection), for a nonnegative law. -/
theorem pullback_positive_of_fixed (c : ReflectionCut V) {π : V → I} (hπ : ∀ v, π (c.flip v) = π v)
    {L : ((I → X) → ℝ) →ₗ[ℝ] ℝ} (hL : ∀ f, (∀ y, 0 ≤ f y) → 0 ≤ L f) :
    c.Positive (ReflectionCut.pullback L π) := by
  have hform : ∀ F G : (c.Half → X) → ℝ, c.form (ReflectionCut.pullback L π) F G =
      L (fun y => F (fun v => y (π v.1)) * G (fun v => y (π v.1))) := by
    intro F G
    change L (fun y => F (fun v => (y ∘ π) v.1) * G (fun v => (y ∘ π) (c.flip v.1))) = _
    congr 1
    funext y
    simp only [Function.comp_apply, hπ]
  constructor
  · intro F G
    rw [hform, hform]
    congr 1
    funext y
    ring
  · intro F
    rw [hform]
    exact hL _ fun y => mul_self_nonneg _

theorem iidLaw_nonneg (ν : FiniteLaw X) {f : (I → X) → ℝ} (hf : ∀ y, 0 ≤ f y) :
    0 ≤ iidLaw (I := I) ν f :=
  Finset.sum_nonneg fun y _ =>
    mul_nonneg (Finset.prod_nonneg fun _ _ => ν.nonneg _) (hf y)

end ReflectionCut

open ReflectionCut

/-- The first chamber coordinate of a slot. -/
def firstChamber (v : Slot) : Chamber := v.1

theorem cutMap_firstChamber (a : Chamber) :
    CutMap (firstChamberCut a) (chamberCut a) firstChamber := by
  constructor
  · intro v hv
    exact (Finset.mem_product.mp hv).1
  · intro v
    rfl

theorem firstChamber_secondCut (a : Chamber) (v : Slot) :
    firstChamber ((secondChamberCut a).flip v) = firstChamber v := rfl

theorem firstChamber_reservedCut (v : Slot) : firstChamber (reservedCut.flip v) = firstChamber v :=
  rfl

variable {Ω X : Type*} [Fintype Ω] [Fintype X]

/-- A nonnegative mixture of chamber pullbacks of i.i.d. laws: given shared data `ω` (weight
`w ω`), one label per chamber is drawn independently from `ν ω` and copied to the slots of that
first chamber. -/
noncomputable def chamberIid (w : Ω → ℝ) (ν : Ω → FiniteLaw X) : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ :=
  ∑ ω, w ω • pullback (iidLaw (I := Chamber) (ν ω)) firstChamber

/-- **Chamber pullbacks of i.i.d. labels are reflection positive** at every chamber cut of both
chamber coordinates and at the reserved cut. -/
theorem chamberIid_positive_cut (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) (ν : Ω → FiniteLaw X) :
    (∀ a, (firstChamberCut a).Positive (chamberIid w ν)) ∧
      (∀ a, (secondChamberCut a).Positive (chamberIid w ν)) ∧
      reservedCut.Positive (chamberIid w ν) := by
  refine ⟨fun a => ?_, fun a => ?_, ?_⟩
  · exact Positive.sum Finset.univ fun ω _ =>
      ((iidLaw_positive (chamberCut a) (ν ω)).pullback (cutMap_firstChamber a)).smul (hw ω)
  · exact Positive.sum Finset.univ fun ω _ =>
      (pullback_positive_of_fixed (secondChamberCut a) (firstChamber_secondCut a)
        fun f hf => iidLaw_nonneg (ν ω) hf).smul (hw ω)
  · exact Positive.sum Finset.univ fun ω _ =>
      (pullback_positive_of_fixed reservedCut firstChamber_reservedCut
        fun f hf => iidLaw_nonneg (ν ω) hf).smul (hw ω)

theorem chamberIid_slotReflectionPositive (w : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω)
    (ν : Ω → FiniteLaw X) : SlotReflectionPositive (chamberIid w ν) := by
  obtain ⟨h1, h2, h3⟩ := chamberIid_positive_cut w hw ν
  intro c hc
  simp only [slotSortingCuts, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1 0
  · exact h1 4
  · exact h1 0
  · exact h2 0
  · exact h2 4
  · exact h2 0
  · exact h3

end Sarkozy

module

public import Sarkozy.Variance.Quadratic
public import Sarkozy.TraceMixing.DisjointTripleOrdered

/-!
# The centred norm of a matching record at one prime (`lem:record:paired-e-bridge`(b))

`paper/sections/22_variance.tex`, `lem:record:paired-e-bridge`(b), at one prime. By
`lem:record:fold-identification`(d) the matching record `Π_{E_s}` is symmetric at `ι`; its actual
half marginal is uniform on the ordered triples of distinct labels, and given the layer-zero
triple the layer-one triple is uniform among those disjoint from it. Read on the triples, the
record at `ι` is the **disjoint-triple coupling** on two slots (`disjCoupling`): the plus slot
carries an ordered triple `x` of distinct elements of `F`, the reflected slot an ordered triple
`y` disjoint from `x`, all such pairs equally weighted. Its Markov operator is the disjoint-triple
operator `T` of `sec:frontier:empty-triple-negative` (`TraceMixing.tripleOp`).

* `twoSlotCut`: the cut of the two slots `Bool` (plus half `{true}`).
* `form_disjCoupling`: `Q(f, g) = ∑_{x ∈ 𝒯} f(x) (T g)(x)`.
* `disjCoupling_marginal`, `disjCoupling_symm`: the half marginal is the counting measure of `𝒯`
  (`tripleMarginal`), and the coupling is symmetric.
* `centredNormLe_disjCoupling`: **`‖T - 𝒥‖ ≤ 3/(n - 3)`** for `n = |F| ≥ 7`, as
  `CentredNormLe`, from `TraceMixing.tripleOp_abs_le` and `centredNormLe_of_quadratic`. With
  `F = 𝔽_p` this is `κ_E = 3/(p - 3)`.

The weights are not normalized (the coupling has mass `|𝒯|`); `CentredNormLe` is invariant
under scaling `π` and `m` by the same positive factor. **Not formalized:** the identification of
the paper's record on the 72 slots with this coupling (it needs the record laws), and the block
version, the tensor product over the primes of a block (`lem:sector`(c), (P4)).
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion Sarkozy.TraceMixing

namespace Sarkozy.Variance

/-- The cut of two slots: `true` is the plus half, `false` its reflection. -/
def twoSlotCut : ReflectionCut Bool where
  half := {true}
  flip := Equiv.swap true false
  flip_flip v := Equiv.swap_apply_self true false v
  crosses v := by cases v <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]

/-- The plus slot. -/
def tPlus : twoSlotCut.Half := ⟨true, by simp [twoSlotCut]⟩

theorem half_eq_tPlus (v : twoSlotCut.Half) : v = tPlus := by
  apply Subtype.ext
  have h := v.2
  simp only [twoSlotCut, mem_singleton] at h
  exact h

theorem flip_tPlus : twoSlotCut.flip tPlus.1 = false := by
  simp [twoSlotCut, tPlus, Equiv.swap_apply_left]

section Coupling

variable {F : Type*} [Fintype F] [DecidableEq F]

/-- A half-function on the two-slot cut, read on the plus label. -/
def onPlus (f : (twoSlotCut.Half → (Fin 3 → F)) → ℝ) (x : Fin 3 → F) : ℝ := f (fun _ => x)

omit [DecidableEq F] in
theorem sum_half (G : (twoSlotCut.Half → (Fin 3 → F)) → ℝ) :
    ∑ xh, G xh = ∑ x : Fin 3 → F, G (fun _ => x) := by
  let e : (twoSlotCut.Half → (Fin 3 → F)) ≃ (Fin 3 → F) :=
    { toFun := fun xh => xh tPlus
      invFun := fun x _ => x
      left_inv := fun xh => funext fun v => by rw [half_eq_tPlus v]
      right_inv := fun _ => rfl }
  exact Fintype.sum_equiv e _ _ (fun xh => by
    congr 1
    funext v
    rw [half_eq_tPlus v]
    rfl)

/-- **The disjoint-triple coupling** on the two slots: weight `D⁻¹` on the pairs `(x, y)` of
ordered triples of distinct elements with `y` disjoint from `x`, `D = (n-3)(n-4)(n-5)`. -/
noncomputable def disjWeight (z : Bool → (Fin 3 → F)) : ℝ :=
  if Function.Injective (z true) ∧ DisjTriple (z true) (z false) then
    ((Fintype.card F - 3).descFactorial 3 : ℝ)⁻¹ else 0

/-- The coupling as a measure. -/
noncomputable def disjCoupling : ((Bool → (Fin 3 → F)) → ℝ) →ₗ[ℝ] ℝ :=
  signedIntegral (disjWeight (F := F))

/-- Its half marginal: the counting measure of the ordered triples of distinct elements. -/
noncomputable def tripleMarginal (xh : twoSlotCut.Half → (Fin 3 → F)) : ℝ :=
  if Function.Injective (xh tPlus) then 1 else 0

/-- `Q(f, g) = ∑_{x ∈ 𝒯} f(x) (T g)(x)`. -/
theorem form_disjCoupling (f g : (twoSlotCut.Half → (Fin 3 → F)) → ℝ) :
    twoSlotCut.form (disjCoupling (F := F)) f g =
      ∑ x, (if Function.Injective x then onPlus f x * tripleOp (onPlus g) x else 0) := by
  change ∑ z, disjWeight z * (f (fun v => z v.1) * g (fun v => z (twoSlotCut.flip v.1))) = _
  have h1 : ∀ z : Bool → (Fin 3 → F), (fun v : twoSlotCut.Half => z v.1) = fun _ => z true := by
    intro z
    funext v
    rw [half_eq_tPlus v]
    rfl
  have h2 : ∀ z : Bool → (Fin 3 → F),
      (fun v : twoSlotCut.Half => z (twoSlotCut.flip v.1)) = fun _ => z false := by
    intro z
    funext v
    rw [half_eq_tPlus v, flip_tPlus]
  simp_rw [h1, h2]
  have key : ∀ G : (Fin 3 → F) → (Fin 3 → F) → ℝ,
      ∑ z : Bool → (Fin 3 → F), G (z true) (z false) = ∑ x, ∑ y, G x y := by
    intro G
    have h := Fintype.sum_equiv (Equiv.boolArrowEquivProd (Fin 3 → F))
      (fun z => G (z true) (z false)) (fun p => G p.2 p.1) (fun z => rfl)
    rw [h, Fintype.sum_prod_type, sum_comm]
  have e := key (fun x y => (if Function.Injective x ∧ DisjTriple x y then
    ((Fintype.card F - 3).descFactorial 3 : ℝ)⁻¹ else 0) * (f (fun _ => x) * g (fun _ => y)))
  unfold disjWeight
  rw [e]
  refine sum_congr rfl fun x _ => ?_
  unfold tripleOp onPlus
  by_cases hx : Function.Injective x
  · simp only [hx, true_and, ↓reduceIte]
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    split_ifs <;> ring
  · simp [hx]

theorem disjCoupling_marginal (hn : 6 ≤ Fintype.card F)
    (f : (twoSlotCut.Half → (Fin 3 → F)) → ℝ) :
    twoSlotCut.form (disjCoupling (F := F)) f 1 = ∑ xh, tripleMarginal xh * f xh := by
  rw [form_disjCoupling, sum_half]
  refine sum_congr rfl fun x _ => ?_
  unfold tripleMarginal onPlus
  by_cases hx : Function.Injective x
  · have h1 : tripleOp (fun y : Fin 3 → F => (1 : (twoSlotCut.Half → (Fin 3 → F)) → ℝ)
        (fun _ => y)) x = 1 := tripleOp_one hn hx
    simp only [hx, ↓reduceIte, h1, mul_one, one_mul]
  · simp [hx]

theorem disjCoupling_symm (f g : (twoSlotCut.Half → (Fin 3 → F)) → ℝ) :
    twoSlotCut.form (disjCoupling (F := F)) f g = twoSlotCut.form (disjCoupling (F := F)) g f := by
  rw [form_disjCoupling, form_disjCoupling, tripleOp_selfAdjoint (onPlus g) (onPlus f)]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> ring

/-- **`lem:record:paired-e-bridge`(b) at one prime**: for `n = |F| ≥ 7` the disjoint-triple
coupling has centred norm `‖T - 𝒥‖ ≤ 3/(n - 3)` relative to its half marginal. -/
theorem centredNormLe_disjCoupling (hn : 7 ≤ Fintype.card F) :
    CentredNormLe twoSlotCut (disjCoupling (F := F)) tripleMarginal
      (3 / ((Fintype.card F : ℝ) - 3)) := by
  have hm : ∀ xh, 0 ≤ tripleMarginal (F := F) xh := fun xh => by
    unfold tripleMarginal
    split_ifs <;> norm_num
  have hmpos : 0 < ∑ xh, tripleMarginal (F := F) xh := by
    -- an injective triple exists
    have hemb : Nonempty (Fin 3 ↪ F) :=
      Function.Embedding.nonempty_of_card_le (by simp; omega)
    obtain ⟨e⟩ := hemb
    have hle : tripleMarginal (F := F) (fun _ => e) ≤ ∑ xh, tripleMarginal (F := F) xh :=
      single_le_sum (fun xh _ => hm xh) (mem_univ _)
    have h1 : tripleMarginal (F := F) (fun _ => e) = 1 := by
      simp [tripleMarginal, e.injective]
    linarith
  have hκ : 0 ≤ 3 / ((Fintype.card F : ℝ) - 3) := by
    apply div_nonneg (by norm_num)
    have : (7 : ℝ) ≤ Fintype.card F := by exact_mod_cast hn
    linarith
  refine centredNormLe_of_quadratic twoSlotCut hm hmpos disjCoupling_symm
    (disjCoupling_marginal (by omega)) hκ ?_
  intro f hf
  rw [form_disjCoupling]
  have hf' : ∑ x, (if Function.Injective x then onPlus f x else 0) = 0 := by
    rw [sum_half] at hf
    calc ∑ x, (if Function.Injective x then onPlus f x else 0)
        = ∑ x : Fin 3 → F, tripleMarginal (fun _ => x) * f (fun _ => x) := by
          refine sum_congr rfl fun x _ => ?_
          unfold tripleMarginal onPlus
          split_ifs <;> simp
      _ = 0 := hf
  have h := tripleOp_abs_le hn (onPlus f) hf'
  refine h.trans (le_of_eq ?_)
  congr 1
  rw [sum_half]
  refine sum_congr rfl fun x _ => ?_
  unfold tripleMarginal onPlus
  split_ifs <;> simp

end Coupling

end Sarkozy.Variance

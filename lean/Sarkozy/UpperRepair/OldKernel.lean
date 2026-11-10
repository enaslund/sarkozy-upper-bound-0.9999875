module

public import Sarkozy.UpperRepair.Kernel
public import Sarkozy.UpperRepair.OneWay

@[expose] public section

/-!
# The old kernel of a record in the form W8's dense and LE propositions take

W8's `dense_comparison_b` and `le_mixture_change` (`prop:dense-comparison`(b), `prop:le-mixture`)
take an old kernel `K₀` with both marginals `1 + u₀` **at every point** (`hO1`, `hO2`). The old
kernel of a record, `pairDensity π^old λ_H`, has these marginals only on the support of `λ_H`: off
it, its rows vanish (`0/0 = 0`), while `1 + u₀ = 1` there (`halfDensity` is `0` off the support).
Since `λ_H` charges only injective strict-square labellings, the support is proper, so W8's
hypotheses fail for `pairDensity π^old λ_H` itself. This is an implicit hypothesis of the
formalized statements, not an error in the paper (the paper works in `L²(μ)`, where null points do
not exist). Here:

* `oldKernel_col`: the columns of `pairDensity lam ν` are `1 + u₀` on the support of `ν`, when the
  two layers of `lam` are exchangeable;
* `modK lam ν`: the old kernel set to `1` off `supp ν × supp ν`; **`modK_row`**, **`modK_col`**:
  both marginals are `1 + u₀` at every point (W8's `hO1`, `hO2`); **`modK_centredForm`**: its
  centred forms are those of `pairDensity lam ν`;
* `recK pr hne t`, `recK_row`, `recK_col`, `recK_centredForm`: the same for the old record of state
  `t` of an upper block;
* **`pairDensity_hO1_fails`**: W8's `hO1` is false for `pairDensity π^old λ_H` itself, at the
  constant labelling `0` (not charged by `λ_H`), on every block with at least one prime.

So W8's two propositions apply with `K₀ := recK pr hne t`, and their conclusions are the fields
`sym`, `skew` of `KernelInput` after `recK_centredForm`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured

section Generic

variable {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Z] [DecidableEq Z]

/-- **The columns of the old kernel** are `1 + u₀` on the support of `ν` when the two layers of the
law are exchangeable. -/
theorem oldKernel_col (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (hs : LayersSupported lam ν)
    (hsym : ∀ φ ψ : (O₀ × O₁ → Z) → ℝ, lam.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) =
      lam.expect (fun y => ψ (layerOf y 0) * φ (layerOf y 1)))
    (y : O₀ × O₁ → Z) (hy : ν.weight y ≠ 0) :
    ν.expect (fun x => pairDensity lam ν (x, y)) = 1 + halfDensity lam ν y := by
  set δ : (O₀ × O₁ → Z) → ℝ := fun z => if z = y then 1 else 0 with hδ
  have h1 := pair_density_eq lam ν hs (fun _ => 1) δ
  have h3 : lam.expect (fun z => 1 * δ (layerOf z 1)) = lam.expect (fun z => δ (layerOf z 0)) := by
    have := hsym (fun _ => 1) δ
    simpa using this
  have h2 := half_density_lin lam ν hs δ
  rw [h3, h2] at h1
  have e2 : ν.expect (fun z => (1 + halfDensity lam ν z) * δ z) =
      ν.weight y * (1 + halfDensity lam ν y) := by
    unfold FiniteLaw.expect
    rw [Finset.sum_eq_single y]
    · simp [hδ]
    · intro z _ hz
      simp [hδ, hz]
    · simp
  have e3 : kform ν ν (pairDensity lam ν) (fun _ => 1) δ =
      ν.weight y * ν.expect (fun x => pairDensity lam ν (x, y)) := by
    rw [kform, expect_comm]
    unfold FiniteLaw.expect
    rw [Finset.sum_eq_single y]
    · simp only [hδ, ↓reduceIte, one_mul, mul_one]
    · intro z _ hz
      simp [hδ, hz]
    · simp
  rw [e2, e3] at h1
  exact (mul_left_cancel₀ hy h1).symm

/-- The old kernel set to `1` off `supp ν × supp ν`. -/
noncomputable def modK (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (p : (O₀ × O₁ → Z) × (O₀ × O₁ → Z)) : ℝ :=
  if ν.weight p.1 = 0 ∨ ν.weight p.2 = 0 then 1 else pairDensity lam ν p

theorem halfDensity_of_zero (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    {x : O₀ × O₁ → Z} (hx : ν.weight x = 0) : halfDensity lam ν x = 0 := by
  unfold halfDensity
  simp [hx]

/-- **The rows of `modK` are `1 + u₀` at every point** (W8's `hO1`). -/
theorem modK_row (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (hs : LayersSupported lam ν) (x : O₀ × O₁ → Z) :
    ν.expect (fun y => modK lam ν (x, y)) = 1 + halfDensity lam ν x := by
  by_cases hx : ν.weight x = 0
  · rw [halfDensity_of_zero lam ν hx]
    have : (fun y => modK lam ν (x, y)) = fun _ => 1 := by
      funext y
      simp [modK, hx]
    rw [this, FiniteLaw.expect_const, add_zero]
  · rw [← oldKernel_row lam ν hs x hx]
    refine expect_congr_supp _ fun y hy => ?_
    simp [modK, hx, hy]

/-- **The columns of `modK` are `1 + u₀` at every point** (W8's `hO2`), for exchangeable layers. -/
theorem modK_col (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (hs : LayersSupported lam ν)
    (hsym : ∀ φ ψ : (O₀ × O₁ → Z) → ℝ, lam.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) =
      lam.expect (fun y => ψ (layerOf y 0) * φ (layerOf y 1)))
    (y : O₀ × O₁ → Z) :
    ν.expect (fun x => modK lam ν (x, y)) = 1 + halfDensity lam ν y := by
  by_cases hy : ν.weight y = 0
  · rw [halfDensity_of_zero lam ν hy]
    have : (fun x => modK lam ν (x, y)) = fun _ => 1 := by
      funext x
      simp [modK, hy]
    rw [this, FiniteLaw.expect_const, add_zero]
  · rw [← oldKernel_col lam ν hs hsym y hy]
    refine expect_congr_supp _ fun x hx => ?_
    simp [modK, hx, hy]

/-- **`modK` has the centred forms of the old kernel.** -/
theorem modK_centredForm (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (ν : FiniteLaw (O₀ × O₁ → Z))
    (u : (O₀ × O₁ → Z) → ℝ) (φ ψ : (O₀ × O₁ → Z) → ℝ) :
    centredForm ν u (modK lam ν) φ ψ = centredForm ν u (pairDensity lam ν) φ ψ := by
  unfold centredForm kform
  congr 1
  refine expect_congr_supp _ fun x hx => expect_congr_supp _ fun y hy => ?_
  simp [modK, hx, hy]

end Generic

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The old kernel of the record of state `t`, in W8's form. -/
noncomputable abbrev recK (hne : UpperNonempty pr) (t : PType × PType) :
    (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) ×
      (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ :=
  modK (recOld pr hne t) (recHalf pr hne t)

/-- W8's `hO1` for the old record. -/
theorem recK_row (hne : UpperNonempty pr) (t : PType × PType)
    (x : t.1.field.Obj × t.2.field.Obj → BlockLabel pr) :
    (recHalf pr hne t).expect (fun y => recK pr hne t (x, y)) = 1 + recU pr hne t x :=
  modK_row _ _ (upper_layersSupported pr hne _ _) x

/-- W8's `hO2` for the old record. -/
theorem recK_col (hne : UpperNonempty pr) (t : PType × PType)
    (y : t.1.field.Obj × t.2.field.Obj → BlockLabel pr) :
    (recHalf pr hne t).expect (fun x => recK pr hne t (x, y)) = 1 + recU pr hne t y :=
  modK_col _ _ (upper_layersSupported pr hne _ _) (recOld_pair_symm pr hne t) y

/-- The centred forms of `recK` are those of the old record. -/
theorem recK_centredForm (hne : UpperNonempty pr) (t : PType × PType)
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → BlockLabel pr) → ℝ) :
    centredForm (recHalf pr hne t) (recU pr hne t) (recK pr hne t) φ' ψ' =
      centredForm (recHalf pr hne t) (recU pr hne t)
        (pairDensity (recOld pr hne t) (recHalf pr hne t)) φ' ψ' :=
  modK_centredForm _ _ _ φ' ψ'

/-! ## W8's `hO1` fails for the unmodified old kernel -/

/-- The rows of `pairDensity lam ν` vanish off the support of `ν`. -/
theorem pairDensity_row_of_zero {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁]
    [DecidableEq O₁] [Fintype Z] [DecidableEq Z] (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z))
    (ν : FiniteLaw (O₀ × O₁ → Z)) {x : O₀ × O₁ → Z} (hx : ν.weight x = 0) :
    ν.expect (fun y => pairDensity lam ν (x, y)) = 0 := by
  unfold pairDensity
  simp [hx]

theorem one_lt_card_obj (f : FType) : 1 < Fintype.card f.Obj := by
  cases f <;> decide

/-- The constant labelling `0` is not charged by the half law `λ_H` (it is not injective). -/
theorem recHalf_weight_zero [Nonempty ι] (hne : UpperNonempty pr) (t : PType × PType) :
    (recHalf pr hne t).weight (fun _ => 0) = 0 := by
  obtain ⟨a, a', haa⟩ := Fintype.exists_pair_of_one_lt_card (one_lt_card_obj t.1.field)
  obtain ⟨b⟩ : Nonempty t.2.field.Obj :=
    Fintype.card_pos_iff.mp (lt_trans zero_lt_one (one_lt_card_obj t.2.field))
  obtain ⟨i₀⟩ := ‹Nonempty ι›
  change (∑ y, if (fun o : t.1.field.Obj × t.2.field.Obj => y (o.1, o.2, 0)) = (fun _ => 0) then
    (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 1))
      (hne.one t.1.field t.2.field)).weight y else 0) = 0
  refine Finset.sum_eq_zero fun y _ => ?_
  split_ifs with hy
  · by_contra hw
    have hfeas := (Labellings.mem_injLabellings_iff_feasible _ _).mp
      (blockGraphLaw_support pr _ _ hw i₀)
    have h1 : y (a, b, 0) = 0 := congrFun hy (a, b)
    have h2 : y (a', b, 0) = 0 := congrFun hy (a', b)
    have h := hfeas.1 (a, b, 0) (mem_univ _) (a', b, 0) (mem_univ _)
      (by simp only [h1, h2])
    simp only [Prod.mk.injEq, and_true] at h
    exact haa h
  · rfl

/-- **W8's `hO1` fails for the unmodified old kernel** `pairDensity π^old λ_H`: at the constant
labelling `0` its row is `0`, while `1 + u₀ = 1`. So W8's `dense_comparison_b`, `le_mixture_change`
apply to `recK`, not to `pairDensity π^old λ_H` (§5 of the report). -/
theorem pairDensity_hO1_fails [Nonempty ι] (hne : UpperNonempty pr) (t : PType × PType) :
    ¬ ∀ x, (recHalf pr hne t).expect (fun y => pairDensity (recOld pr hne t) (recHalf pr hne t)
      (x, y)) = 1 + recU pr hne t x := by
  intro h
  have h0 := recHalf_weight_zero pr hne t
  have e := h (fun _ => 0)
  rw [pairDensity_row_of_zero _ _ h0] at e
  have hu : recU pr hne t (fun _ => 0) = 0 := halfDensity_of_zero _ _ h0
  rw [hu] at e
  norm_num at e

end Sarkozy.UpperRepair

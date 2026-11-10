module

public import Sarkozy.F7Repair.TwoLayer
public import Sarkozy.TailPrices.RepairBound
public import Sarkozy.PartV.RootAffine
public import Sarkozy.UpperComparison.Symmetry

@[expose] public section

/-!
# The one-way repairs at a tail prime (`lem:tail-prices`(i),(ii), (F7); K2's field 10)

`paper/sections/27_tail_index.tex`, proof of `lem:tail-prices`(i),(ii): "By `lem:tr:repair`(a)–(c)
a repaired record becomes a probability law with exactly the actual half marginals at `ι` of the
record it replaces, supported in the support of the uniform law of the repaired graph …, so it
accepts the twelve queries; its data are square-affine invariant, so it is invariant. Its
difference from the replaced record has zero marginals and norm at most `C_ϱ r` relative to these
marginals (`lem:tr:repair`(f) with (F7))."

This file builds T2's `TailRepair` from the inputs of (F7):

* `tailOld_affine`, `tailOld_symm`: the old tail record `λ_p(G_{φ₀φ₁,2})` is square-affine
  invariant and its two layers have one law (the layer swap is an automorphism of `G`);
* **`TailF7 p hne t φ`**: the (F7) inputs of the changed record `(t, φ)` at the prime: an
  `F7Record` (the new law `π^new`, its support, `U`, `ρ_new`, `K_∞`, the gate, `ρ_old`), and two
  properties of `π^new`: its emission accepts `𝓔₆`, and it is square-affine invariant.
  *Hypotheses*;
* **`TailF7.toRepair`**: the `TailRepair` (K2's field 10, per record), with the repaired law
  `π^rep` of `F7Record.lam`; acceptance, invariance, support and the norm bound are *proved* from
  the inputs; `Cs = Ca = ρ_old + ρ'` (the paper charges each repair bound in full in both totals);
* **`TailF7s`, `TailF7s.toRepairs`**: all changed records at one prime, i.e. T2's `TailRepairs`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
  Sarkozy.TailPrices

variable {p : ℕ} [Fact p.Prime]

/-- The square-affine map `y ↦ αy + β` on labellings, `α ≠ 0`. -/
def affEquiv {W : Type*} (α β : ZMod p) (hα : α ≠ 0) : (W → ZMod p) ≃ (W → ZMod p) where
  toFun y w := α * y w + β
  invFun y w := α⁻¹ * (y w - β)
  left_inv y := by
    funext w
    simp only [add_sub_cancel_right, ← mul_assoc, inv_mul_cancel₀ hα, one_mul]
  right_inv y := by
    funext w
    simp only [← mul_assoc, mul_inv_cancel₀ hα, one_mul, sub_add_cancel]

theorem affEquiv_apply {W : Type*} (α β : ZMod p) (hα : α ≠ 0) (y : W → ZMod p) :
    affEquiv α β hα y = fun w => α * y w + β := rfl

variable (hne : TailNonempty p)

/-- **The old tail record is square-affine invariant** (two-layer level). -/
theorem tailOld_affine (t : PType × PType) {α : ZMod p} (hα : quadraticChar (ZMod p) α = 1)
    (β : ZMod p) (y : t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p) :
    (tailOld p hne t).weight (fun w => α * y w + β) = (tailOld p hne t).weight y :=
  graphLaw_weight_affine' p (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _) hα β y

/-- **The two layers of the old tail record have one law** (the layer swap is an automorphism of
`G_{φ₀φ₁,2}`; "by the layer symmetry of `G`"). -/
theorem tailOld_symm (t : PType × PType) (φ : (t.1.field.Obj × t.2.field.Obj → ZMod p) → ℝ) :
    (tailOld p hne t).expect (fun y => φ (lay1 y)) = (tailOld p hne t).expect (fun y => φ (lay0 y)) := by
  have h := graphLaw_expect_comp (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _)
    (upLayerSwap _ _) (upLayerSwap_automorphism _ _) (fun y => φ (lay0 y))
  have e : ∀ z : t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p,
      lay0 (z ∘ upLayerSwap t.1.field.Obj t.2.field.Obj) = lay1 z := by
    intro z
    funext o
    simp only [lay0, lay1, layerOf, Function.comp_apply, upLayerSwap, Equiv.prodCongr_apply,
      Equiv.coe_refl, Prod.map, id_eq, Equiv.swap_apply_left]
  simp only [e] at h
  exact h

/-- **The (F7) inputs of a changed tail record** (`lem:tr:repair`(a)–(d),(f), (F7) with the
all-prime cap; `lem:tail-prices`(i),(ii)). *Hypotheses*: the `F7Record` of the record (the new
law `π^new = λ_p(G^new)`, its support, `U`, `ρ_new`, `K_∞`, the gate `2F < 1` and `ρ_old`), the
acceptance of `𝓔₆` by the emitted `π^new` (the projected queries are edges of `G^new`), and the
square-affine invariance of `π^new` (`G^new` is a graph with nonzero-square edge constraints). -/
structure TailF7 (t : PType × PType) (φ : t.1.Pat × t.2.Pat) where
  /-- The (F7) record data at the prime. -/
  data : F7Record (tailOld p hne t) (tailHalf p hne t.1.field t.2.field)
  /-- The emitted new law accepts `𝓔₆`. -/
  accepts : ∀ z, (emit data.lamN (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 →
    ∀ j : Chamber, quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1
  /-- The new law is square-affine invariant. -/
  inv : ∀ α β : ZMod p, quadraticChar (ZMod p) α = 1 →
    ∀ y, data.lamN.weight (fun w => α * y w + β) = data.lamN.weight y

namespace TailF7

variable {hne} {t : PType × PType} {φ : t.1.Pat × t.2.Pat} (T : TailF7 hne t φ)

/-- The repaired law `π^rep` is square-affine invariant (two-layer level). -/
theorem lam_affine {α : ZMod p} (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p)
    (y : t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod p) :
    T.data.lam.weight (fun w => α * y w + β) = T.data.lam.weight y := by
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  exact T.data.invariant (affEquiv α β hα0) (affEquiv α β hα0) (fun y => T.inv α β hα y)
    (fun y => tailOld_affine hne t hα β y) (fun _ => rfl) (fun _ => rfl) y

/-- **The emitted repair accepts `𝓔₆`** (it lives on the support of `π^new`). -/
theorem rep_accepts : ∀ z, (emit T.data.lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 →
    ∀ j : Chamber, quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 :=
  fun z hz => T.accepts z
    (map_weight_ne_zero_of_support (fun _ hy => T.data.support hy) _ hz)

/-- **The emitted repair is square-affine invariant.** -/
theorem rep_inv :
    AffineInvariant p (emit T.data.lam (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight := by
  intro α β hα z
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  exact map_weight_equivariant T.data.lam (fun y => y ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2))
    (affEquiv α β hα0) (affEquiv α β hα0) (fun y => T.lam_affine hα β y) (fun _ => rfl) z

/-- **T2's `TailRepair` from the (F7) inputs** (K2's field 10 for one record): the repaired law
is `π^rep`, and `C^s = C^a = ρ_old + ρ'`. -/
noncomputable def toRepair : TailRepair p hne t φ :=
  TailRepair.ofChangeBound T.data.lam T.data.supp T.rep_accepts T.rep_inv T.data.C T.data.C_nonneg
    (fun φ' ψ' => by
      unfold tailChangeForm
      exact T.data.change_bound (tail_layersSupported p hne _ _) (tailOld_symm hne t) φ' ψ')

theorem toRepair_C (e : ChangeType) : T.toRepair.C e = T.data.C := by
  cases e <;> rfl

end TailF7

/-- The (F7) inputs of every changed record at one tail prime. -/
abbrev TailF7s : Type :=
  ∀ (t : PType × PType) (φ : t.1.Pat × t.2.Pat), upperFate (true, ⟨t, φ⟩) = .changed →
    TailF7 hne t φ

variable {hne}

/-- **T2's `TailRepairs` from the (F7) inputs** (K2's field 10 at one prime). -/
noncomputable def TailF7s.toRepairs (F : TailF7s hne) : TailRepairs p hne :=
  fun t φ h => (F t φ h).toRepair

theorem TailF7s.toRepairs_C (F : TailF7s hne) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    (F.toRepairs t φ h).C e = (F t φ h).data.C :=
  (F t φ h).toRepair_C e

end Sarkozy.F7Repair

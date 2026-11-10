module

public import Sarkozy.PartVLaws.UpperRP
public import Sarkozy.PartVLaws.Extension

@[expose] public section

/-!
# The row data of the paper's upper laws form five-type data

`paper/sections/25_upper_reference.tex`, `subsec:upper-rows` ("the two-layer row data of `c` at
`𝔣(𝔱')` form a five-type datum"), `lem:upper-geometry`(b),(d); `paper/sections/12_labellings.tex`,
`lem:graphs:sequential`.

This discharges `UpperDatumHyp` (the hypothesis "the row data form five-type data" of
`lem:upper-reference-rp`(i)) for field laws that are invariant under the automorphisms of their
graphs (`GraphInv`) and whose supports have the extension property `SuppExt`:
* exchangeability of the `E` rows and `𝒢₆`-invariance of the `L` rows come from the
  automorphisms of `lem:upper-geometry`(b) (`twoLayer_auto` with `typeE_preserves` and
  `typeL_preserves_g6`), transported to C1's coordinates (`lamOf_inv`);
* the `Γ`-support of the `F` rows (`GamSupported`) is the extension property: a fold labelling
  of `G_{F𝔣}` restricted to the rows `{0,1}` (or `{1,2}`) is a feasible labelling of the same rows
  of `G_{E𝔣}`, because `F` and `E` agree there (`lem:upper-geometry`(d)), and it extends to a full
  matching labelling.

**For the paper's laws** (`graphLaws`, the single-prime laws `λ_p(G_{φ₀φ₁,j})` of the tail law):
`graphLaws_suppExt` proves `SuppExt` under Weil's bound at every prime `p ≥ 2²⁰`, from the
explicit extension count (`exists_extension`, degree at most `8`); this is the "positive extension
counts" input of V1's finding 3, with an explicit threshold. Hence **`tail_upperDatumHyp`**: the
tail law's row data form five-type data at every prime `p ≥ 2²⁰` (in particular at every
`p ≥ P₄`), under H1.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## Field laws in C1's format, from V1-format laws -/

section LamOf

variable {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']

/-- C1-format field laws from V1-format laws `G f₀ f₁` on `O_{f₀} × O_{f₁} × Λ'`, the layer read
through `κ : Λ → Λ'`. -/
noncomputable def lamOf (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (κ : Λ → Λ') (f0 f1 : FieldTy) :
    FiniteLaw (f0.Obj × f1.Obj × Λ → X) :=
  (G (toFType f0) (toFType f1)).map fun y w => y (objCast f0 w.1, objCast f1 w.2.1, κ w.2.2)

theorem lam2_eq (F : UpperFieldLaws X) : lam2 F = lamOf F.two layerFin := rfl

theorem lam1_eq (F : UpperFieldLaws X) : lam1 F = lamOf F.one (fun _ : Unit => (0 : Fin 1)) :=
  rfl

/-- C1's field types' relations. -/
def cRel : (f : FieldTy) → FieldType f.Obj
  | .L => typeL
  | .F => typeF
  | .E => typeE

/-- A permutation of the objects of a C1 field type, on the V1 field type. -/
def toFEquiv : (f : FieldTy) → (f.Obj ≃ f.Obj) → ((toFType f).Obj ≃ (toFType f).Obj)
  | .L, σ => σ
  | .F, σ => σ
  | .E, σ => σ

theorem objCast_toFEquiv (f : FieldTy) (σ : f.Obj ≃ f.Obj) (a : f.Obj) :
    objCast f (σ a) = toFEquiv f σ (objCast f a) := by
  cases f <;> rfl

theorem preserves_toFEquiv (f : FieldTy) (σ : f.Obj ≃ f.Obj) (h : (cRel f).Preserves σ) :
    (toFType f).rel.Preserves (toFEquiv f σ) := by
  cases f <;> exact h

theorem preserves_refl {O : Type} (c : FieldType O) : c.Preserves (Equiv.refl O) :=
  fun _ _ => ⟨rfl, rfl⟩

/-- **V1-format laws invariant under the automorphisms of their graphs** `G_{f₀f₁}`. -/
def GraphInv (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X)) : Prop :=
  ∀ (f₀ f₁ : FType) (π : f₀.Obj × f₁.Obj × Λ' ≃ f₀.Obj × f₁.Obj × Λ'),
    IsAutomorphism (fieldGraph f₀ f₁ Λ') π →
      ∀ g : (f₀.Obj × f₁.Obj × Λ' → X) → ℝ, (G f₀ f₁).expect (fun y => g (y ∘ π)) =
        (G f₀ f₁).expect g

/-- **Coordinatewise relation-preserving maps leave the C1-format laws invariant**
(`lem:upper-geometry`(b), transported). -/
theorem lamOf_inv (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    (hG : GraphInv G) {Λ : Type} [Fintype Λ] [DecidableEq Λ] (κ : Λ → Λ') (f0 f1 : FieldTy)
    (σ₀ : f0.Obj ≃ f0.Obj) (σ₁ : f1.Obj ≃ f1.Obj) (h₀ : (cRel f0).Preserves σ₀)
    (h₁ : (cRel f1).Preserves σ₁) (g : (f0.Obj × f1.Obj × Λ → X) → ℝ) :
    (lamOf G κ f0 f1).expect (fun y => g (y ∘ σ₀.prodCongr (σ₁.prodCongr (Equiv.refl Λ)))) =
      (lamOf G κ f0 f1).expect g := by
  unfold lamOf
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map]
  have hπ := twoLayer_auto (toFType f0).rel (toFType f1).rel (toFType f0).rel_proper
    (toFType f1).rel_proper (toFEquiv f0 σ₀) (toFEquiv f1 σ₁) (Equiv.refl Λ')
    (preserves_toFEquiv f0 σ₀ h₀) (preserves_toFEquiv f1 σ₁ h₁)
  have := hG _ _ _ hπ (fun y => g (fun w => y (objCast f0 w.1, objCast f1 w.2.1, κ w.2.2)))
  refine Eq.trans ?_ this
  refine FiniteLaw.expect_congr _ fun y => ?_
  simp only [Function.comp_apply]
  congr 1
  funext w
  simp only [Function.comp_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply,
    objCast_toFEquiv]

/-- The weight of a V1-format law is invariant under the automorphisms of its graph. -/
theorem weight_auto (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    (hG : GraphInv G) (f₀ f₁ : FType) (π : f₀.Obj × f₁.Obj × Λ' ≃ f₀.Obj × f₁.Obj × Λ')
    (hπ : IsAutomorphism (fieldGraph f₀ f₁ Λ') π) (z : f₀.Obj × f₁.Obj × Λ' → X) :
    (G f₀ f₁).weight (z ∘ π) = (G f₀ f₁).weight z :=
  weight_comp_of_expect _ (relabelEquiv π) (fun f => hG f₀ f₁ π hπ f) z

end LamOf

/-! ## Exchangeability and `𝒢₆`-invariance of the rows -/

section Rows

variable {A O Λ : Type} [Fintype A] [DecidableEq A] [Fintype O] [DecidableEq O]
  [Fintype Λ] [DecidableEq Λ]

/-- Invariance of a law of labellings of `A × O × Λ` under `σ` on `A` makes the law of its rows
`σ`-invariant. -/
theorem rows0_weight_comp (μ : FiniteLaw (A × O × Λ → X)) (σ : A ≃ A)
    (h : ∀ g : (A × O × Λ → X) → ℝ,
      μ.expect (fun y => g (y ∘ σ.prodCongr ((Equiv.refl O).prodCongr (Equiv.refl Λ)))) =
        μ.expect g)
    (ω : A → O × Λ → X) :
    (μ.map fun y => (rows0 y : A → O × Λ → X)).weight (ω ∘ σ) =
      (μ.map fun y => (rows0 y : A → O × Λ → X)).weight ω := by
  refine weight_comp_of_expect _ (relabelEquiv σ) (fun f => ?_) ω
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map]
  exact h (fun y => f (rows0 y))

/-- The same for the rows of the coordinate `1`. -/
theorem rows1_weight_comp (μ : FiniteLaw (O × A × Λ → X)) (σ : A ≃ A)
    (h : ∀ g : (O × A × Λ → X) → ℝ,
      μ.expect (fun y => g (y ∘ (Equiv.refl O).prodCongr (σ.prodCongr (Equiv.refl Λ)))) =
        μ.expect g)
    (ω : A → O × Λ → X) :
    (μ.map fun y => (rows1 y : A → O × Λ → X)).weight (ω ∘ σ) =
      (μ.map fun y => (rows1 y : A → O × Λ → X)).weight ω := by
  refine weight_comp_of_expect _ (relabelEquiv σ) (fun f => ?_) ω
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map]
  exact h (fun y => f (rows1 y))

end Rows

/-- **`𝒢₆` preserves the relations of `L`** (`lem:upper-geometry`(b), all six elements). -/
theorem typeL_preserves_g6 (k : Fin 6) : typeL.Preserves (g6Equiv k) := by
  have key : ∀ (k : Fin 6) (x y : ZMod 6), typeL.rel (g6 k x) (g6 k y) = typeL.rel x y ∧
      typeL.fwd (g6 k x) (g6 k y) = typeL.fwd x y := by
    unfold typeL g6
    decide +kernel
  intro x y
  exact key k x y

/-! ## The `Γ`-support of the fold rows -/

section Support

variable {Λ' : Type} [Fintype Λ'] [DecidableEq Λ']

/-- **The extension property of the supports** (V1's finding 3): every charged fold labelling of
`G_{F𝔣}` (resp. `G_{𝔣F}`) agrees, off the object `j ∈ {0, 2}` of its fold coordinate, with some
charged matching labelling of `G_{E𝔣}` (resp. `G_{𝔣E}`). -/
structure SuppExt (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X)) : Prop where
  left : ∀ (f : FType) (y : Fin 3 × f.Obj × Λ' → X), (G .F f).weight y ≠ 0 →
    ∀ j : Fin 3, j ≠ 1 → ∃ z, (G .E f).weight z ≠ 0 ∧ ∀ w, w.1 ≠ j → z w = y w
  right : ∀ (f : FType) (y : f.Obj × Fin 3 × Λ' → X), (G f .F).weight y ≠ 0 →
    ∀ j : Fin 3, j ≠ 1 → ∃ z, (G f .E).weight z ≠ 0 ∧ ∀ w, w.2.1 ≠ j → z w = y w

omit [DecidableEq Λ'] in
/-- The swap of the objects `0, 2` of the matching coordinate is an automorphism of `G_{E𝔣}`. -/
theorem swap_auto_left (f : FType) :
    IsAutomorphism (fieldGraph .E f Λ')
      ((Equiv.swap (0 : Fin 3) 2).prodCongr ((Equiv.refl f.Obj).prodCongr (Equiv.refl Λ'))) :=
  twoLayer_auto typeE f.rel typeE_proper f.rel_proper _ _ _ (typeE_preserves _)
    (preserves_refl _)

omit [DecidableEq Λ'] in
theorem swap_auto_right (f : FType) :
    IsAutomorphism (fieldGraph f .E Λ')
      ((Equiv.refl f.Obj).prodCongr ((Equiv.swap (0 : Fin 3) 2).prodCongr (Equiv.refl Λ'))) :=
  twoLayer_auto f.rel typeE f.rel_proper typeE_proper _ _ _ (preserves_refl _)
    (typeE_preserves _)

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- **The fold rows of the coordinate `0` are `Γ`-supported.** -/
theorem gamSupported0 (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    (hG : GraphInv G) (hS : SuppExt G) (κ : Λ → Λ') (f' : FieldTy) :
    GamSupported ((lamOf G κ .E f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))
      ((lamOf G κ .F f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X)) := by
  intro ω hω
  unfold lamOf at hω
  rw [map_map', map_weight_ne_zero] at hω
  obtain ⟨y, hy, rfl⟩ := hω
  have hgam : ∀ z, (G .E (toFType f')).weight z ≠ 0 → ∀ x b : f'.Obj × Λ → X,
      (∀ p : f'.Obj × Λ, z (0, objCast f' p.1, κ p.2) = x p) →
      (∀ p : f'.Obj × Λ, z (1, objCast f' p.1, κ p.2) = b p) →
      (gamOf ((lamOf G κ .E f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))).weight
        ![x, b] ≠ 0 := by
    intro z hz x b hx hb
    unfold gamOf lamOf
    rw [map_map', map_map', map_weight_ne_zero]
    refine ⟨z, hz, ?_⟩
    funext i
    fin_cases i
    · funext p
      exact hx p
    · funext p
      exact hb p
  constructor
  · obtain ⟨z, hz, hzy⟩ := hS.left _ y hy 2 (by decide)
    exact hgam z hz _ _ (fun p => hzy _ (show (0 : Fin 3) ≠ 2 by decide))
      (fun p => hzy _ (show (1 : Fin 3) ≠ 2 by decide))
  · obtain ⟨z, hz, hzy⟩ := hS.left _ y hy 0 (by decide)
    have hz' : (G .E (toFType f')).weight (z ∘ (Equiv.swap (0 : Fin 3) 2).prodCongr
        ((Equiv.refl _).prodCongr (Equiv.refl Λ'))) ≠ 0 := by
      rw [weight_auto G hG _ _ _ (swap_auto_left _)]
      exact hz
    refine hgam _ hz' _ _ (fun p => ?_) (fun p => ?_)
    · change z (Equiv.swap (0 : Fin 3) 2 0, objCast f' p.1, κ p.2) = _
      rw [Equiv.swap_apply_left]
      exact hzy _ (show (2 : Fin 3) ≠ 0 by decide)
    · change z (Equiv.swap (0 : Fin 3) 2 1, objCast f' p.1, κ p.2) = _
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact hzy _ (show (1 : Fin 3) ≠ 0 by decide)

/-- **The fold rows of the coordinate `1` are `Γ`-supported.** -/
theorem gamSupported1 (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    (hG : GraphInv G) (hS : SuppExt G) (κ : Λ → Λ') (f' : FieldTy) :
    GamSupported ((lamOf G κ f' .E).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X))
      ((lamOf G κ f' .F).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X)) := by
  intro ω hω
  unfold lamOf at hω
  rw [map_map', map_weight_ne_zero] at hω
  obtain ⟨y, hy, rfl⟩ := hω
  have hgam : ∀ z, (G (toFType f') .E).weight z ≠ 0 → ∀ x b : f'.Obj × Λ → X,
      (∀ p : f'.Obj × Λ, z (objCast f' p.1, 0, κ p.2) = x p) →
      (∀ p : f'.Obj × Λ, z (objCast f' p.1, 1, κ p.2) = b p) →
      (gamOf ((lamOf G κ f' .E).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X))).weight
        ![x, b] ≠ 0 := by
    intro z hz x b hx hb
    unfold gamOf lamOf
    rw [map_map', map_map', map_weight_ne_zero]
    refine ⟨z, hz, ?_⟩
    funext i
    fin_cases i
    · funext p
      exact hx p
    · funext p
      exact hb p
  constructor
  · obtain ⟨z, hz, hzy⟩ := hS.right _ y hy 2 (by decide)
    exact hgam z hz _ _ (fun p => hzy _ (show (0 : Fin 3) ≠ 2 by decide))
      (fun p => hzy _ (show (1 : Fin 3) ≠ 2 by decide))
  · obtain ⟨z, hz, hzy⟩ := hS.right _ y hy 0 (by decide)
    have hz' : (G (toFType f') .E).weight (z ∘ (Equiv.refl _).prodCongr
        ((Equiv.swap (0 : Fin 3) 2).prodCongr (Equiv.refl Λ'))) ≠ 0 := by
      rw [weight_auto G hG _ _ _ (swap_auto_right _)]
      exact hz
    refine hgam _ hz' _ _ (fun p => ?_) (fun p => ?_)
    · change z (objCast f' p.1, Equiv.swap (0 : Fin 3) 2 0, κ p.2) = _
      rw [Equiv.swap_apply_left]
      exact hzy _ (show (2 : Fin 3) ≠ 0 by decide)
    · change z (objCast f' p.1, Equiv.swap (0 : Fin 3) 2 1, κ p.2) = _
      rw [Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)]
      exact hzy _ (show (1 : Fin 3) ≠ 0 by decide)

/-- **The row data of the coordinate `0` form five-type data**, for automorphism-invariant laws
with the extension property. -/
theorem rowHyp0_of (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    (hG : GraphInv G) (hS : SuppExt G) (κ : Λ → Λ') (f' : FieldTy) :
    RowHyp0 (lamOf G κ) f' where
  exch σ ω := rows0_weight_comp _ σ
    (lamOf_inv G hG κ .E f' σ (Equiv.refl _) (typeE_preserves σ) (preserves_refl _)) ω
  supp := gamSupported0 G hG hS κ f'
  root k Ψ := rows0_weight_comp _ (g6Equiv k)
    (lamOf_inv G hG κ .L f' (g6Equiv k) (Equiv.refl _) (typeL_preserves_g6 k)
      (preserves_refl _)) Ψ

/-- **The row data of the coordinate `1` form five-type data.** -/
theorem rowHyp1_of (G : (f₀ f₁ : FType) → FiniteLaw (f₀.Obj × f₁.Obj × Λ' → X))
    (hG : GraphInv G) (hS : SuppExt G) (κ : Λ → Λ') (f' : FieldTy) :
    RowHyp1 (lamOf G κ) f' where
  exch σ ω := rows1_weight_comp _ σ
    (lamOf_inv G hG κ f' .E (Equiv.refl _) σ (preserves_refl _) (typeE_preserves σ)) ω
  supp := gamSupported1 G hG hS κ f'
  root k Ψ := rows1_weight_comp _ (g6Equiv k)
    (lamOf_inv G hG κ f' .L (Equiv.refl _) (g6Equiv k) (preserves_refl _)
      (typeL_preserves_g6 k)) Ψ

end Support

/-- **`UpperDatumHyp` from automorphism invariance and the extension property** of the two-layer
and the one-layer field laws. -/
theorem upperDatumHyp_of (F : UpperFieldLaws X) (h2 : GraphInv F.two) (h1 : GraphInv F.one)
    (s2 : SuppExt F.two) (s1 : SuppExt F.one) : UpperDatumHyp F where
  two0 f' := rowHyp0_of F.two h2 s2 layerFin f'
  two1 f' := rowHyp1_of F.two h2 s2 layerFin f'
  one0 f' := rowHyp0_of F.one h1 s1 (fun _ : Unit => (0 : Fin 1)) f'
  one1 f' := rowHyp1_of F.one h1 s1 (fun _ : Unit => (0 : Fin 1)) f'

end Sarkozy.PartVLaws

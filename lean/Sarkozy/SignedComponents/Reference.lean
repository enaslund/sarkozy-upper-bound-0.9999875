module

public import Sarkozy.SignedComponents.Repair
public import Sarkozy.TraceMixing.Paley

@[expose] public section

/-!
# The reference fold record at one prime: its half marginal `m₀` (`lem:old-f-law`(a), partly)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`, `lem:signed-components`.

At one prime `p ≡ 3 (4)` the two-layer fold record of the middle reference is the graph law
`K₀ = λ_p(G_{F,2})` of the fold graph: uniform on the six-label configurations with distinct
labels and the edges `x₀ → x₂, x₀ → y₂, y₀ → x₂, y₀ → y₂`. Its half marginal is
`m₀ = g₀ ν_F` (`lem:old-f-law`(a)). This file proves the facts about `m₀` that the marginal repair
of `lem:signed-components` uses, without computing `g₀`:

* `lay y ℓ`, `toY`, `pairEquiv`: a two-layer labelling is a pair of halves;
* `m0 hF`: the half marginal of `K₀` (layer `0`), a law on the triples;
* `m0_coord`: each coordinate of `m₀` is uniform (`lem:marginals`);
* `m0_translate`: `m₀` is translation invariant;
* **`m0_pos`** (`lem:old-f-law`(a): `N₀(x) > 0`): `m₀(x) > 0` for every `x ∈ H_F` (distinct
  labels with `x₀ → x₂`), at `p ≥ 19`, by the Paley counts of `lem:paley-triple`(a);
* `m0_layer1`: the layer-`1` marginal of `K₀` is also `m₀` (layer swap);
* `m0_refl` (`lem:old-f-law`(a): `g₀ ∘ ς = g₀`): `m₀` is invariant under the reflection
  `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-! ## Pairs of halves -/

/-- The layer `ℓ` of a two-layer labelling of the fold objects. -/
def lay (y : Fin 3 × Fin 2 → F) (ℓ : Fin 2) : Fin 3 → F := fun o => y (o, ℓ)

/-- The two-layer labelling of a pair of halves. -/
def toY (p : (Fin 3 → F) × (Fin 3 → F)) : Fin 3 × Fin 2 → F :=
  fun w => if w.2 = 0 then p.1 w.1 else p.2 w.1

/-- Two-layer labellings are pairs of halves. -/
def pairEquiv : (Fin 3 → F) × (Fin 3 → F) ≃ (Fin 3 × Fin 2 → F) where
  toFun := toY
  invFun y := (lay y 0, lay y 1)
  left_inv p := by
    ext o
    · simp [toY, lay]
    · simp [toY, lay]
  right_inv y := by
    funext w
    obtain ⟨o, ℓ⟩ := w
    fin_cases ℓ
    · simp [toY, lay]
    · simp [toY, lay]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem lay_toY_zero (p : (Fin 3 → F) × (Fin 3 → F)) : lay (toY p) 0 = p.1 := by
  funext o
  simp [lay, toY]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem lay_toY_one (p : (Fin 3 → F) × (Fin 3 → F)) : lay (toY p) 1 = p.2 := by
  funext o
  simp [lay, toY]

/-- The weight of the image of a law under an equivalence. -/
theorem map_equiv_weight {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (e : Ω ≃ Ξ) (ξ : Ξ) : (μ.map e).weight ξ = μ.weight (e.symm ξ) := by
  change (∑ ω, if e ω = ξ then μ.weight ω else 0) = _
  rw [Finset.sum_eq_single (e.symm ξ)]
  · simp
  · intro ω _ hω
    have : e ω ≠ ξ := fun h => hω (by rw [← h, Equiv.symm_apply_apply])
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

/-- The translation of a labelling by `c`. -/
def trans {W : Type*} (c : F) : (W → F) ≃ (W → F) := Equiv.piCongrRight fun _ => Equiv.addRight c

omit [Fintype F] [DecidableEq F] in
@[simp] theorem trans_apply {W : Type*} (c : F) (z : W → F) (w : W) : trans c z w = z w + c := rfl

/-! ## Paley counts -/

theorem chi_cases (a : F) : χ a = 0 ∨ χ a = 1 ∨ χ a = -1 := by
  by_cases ha : a = 0
  · left
    rw [ha, quadraticChar_zero]
  · right
    exact quadraticChar_dichotomy ha

omit [Field F] in
/-- An element with a property, outside a smaller set. -/
theorem exists_avoid (P : F → Prop) [DecidablePred P] (s : Finset F)
    (h : s.card < (univ.filter P).card) : ∃ c, P c ∧ c ∉ s := by
  by_contra hcon
  push Not at hcon
  have hsub : univ.filter P ⊆ s := fun c hc => hcon c (mem_filter.mp hc).2
  exact absurd (card_le_card hsub) (not_le.mpr h)

omit [Field F] [Fintype F] in
theorem card_pair_le (a b : F) : ({a, b} : Finset F).card ≤ 2 := Finset.card_le_two

/-- **Two cross channels with prescribed signs** (`lem:paley-triple`(a)): for `a ≠ a'` and signs
`σ, σ'` there is `c` with `χ(c - a) = σ`, `χ(c - a') = σ'`, at `p ≥ 7`. -/
theorem exists_sign_pair (hF : ringChar F ≠ 2) (h7 : 7 ≤ Fintype.card F) {a a' : F}
    (haa : a ≠ a') {σ σ' : ℤ} (hσ : σ = 1 ∨ σ = -1) (hσ' : σ' = 1 ∨ σ' = -1) :
    ∃ c, χ (c - a) = σ ∧ χ (c - a') = σ' := by
  have h := card_sign_pair hF haa hσ hσ'
  have h1 : χ (a - a') = 1 ∨ χ (a - a') = -1 := quadraticChar_dichotomy (sub_ne_zero.mpr haa)
  have h2 : χ (a' - a) = 1 ∨ χ (a' - a) = -1 :=
    quadraticChar_dichotomy (sub_ne_zero.mpr (Ne.symm haa))
  have hpos : 0 < ((univ.filter fun c => χ (c - a) = σ ∧ χ (c - a') = σ').card : ℤ) := by
    have h7' : (7 : ℤ) ≤ Fintype.card F := by exact_mod_cast h7
    rcases hσ with rfl | rfl <;> rcases hσ' with rfl | rfl <;> rcases h1 with e1 | e1 <;>
      rcases h2 with e2 | e2 <;> rw [e1, e2] at h <;> linarith
  obtain ⟨c, hc⟩ := card_pos.mp (by exact_mod_cast hpos)
  exact ⟨c, (mem_filter.mp hc).2⟩

/-! ## The half marginal of the reference fold record -/

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- The reference fold record `K₀ = λ_p(G_{F,2})` at one prime. -/
noncomputable abbrev K0 : FiniteLaw (Fin 3 × Fin 2 → F) := graphLaw (foldGraph (Fin 2)) hF

/-- **The half marginal `m₀` of the reference fold record** (layer `0`). -/
noncomputable def m0 : FiniteLaw (Fin 3 → F) := (K0 hF).map fun y => lay y 0

theorem m0_expect (g : (Fin 3 → F) → ℝ) :
    (m0 hF).expect g = (K0 hF).expect (fun y => g (lay y 0)) :=
  FiniteLaw.expect_map _ _ _

/-- **Each coordinate of `m₀` is uniform.** -/
theorem m0_coord (o : Fin 3) (g : F → ℝ) :
    ∑ x, (m0 hF).weight x * g (x o) = (∑ c, g c) / (Fintype.card F : ℝ) := by
  have h := m0_expect hF (fun x => g (x o))
  unfold FiniteLaw.expect at h
  rw [h]
  have h2 := graphLaw_vertex_uniform (foldGraph (Fin 2)) hF (o, 0) g
  unfold FiniteLaw.expect at h2
  rw [show (∑ y, (K0 hF).weight y * g (lay y 0 o)) = ∑ y, (graphLaw (foldGraph (Fin 2)) hF).weight y
    * g (y (o, 0)) from rfl, h2]
  exact FiniteLaw.expect_uniform g

/-- **`m₀` is translation invariant.** -/
theorem m0_translate (c : F) (x : Fin 3 → F) :
    (m0 hF).weight (fun o => x o + c) = (m0 hF).weight x := by
  change (∑ y, if lay y 0 = (fun o => x o + c) then (K0 hF).weight y else 0) =
    ∑ y, if lay y 0 = x then (K0 hF).weight y else 0
  refine (Fintype.sum_equiv (trans c) _ _ fun y => ?_).symm
  have hw : (K0 hF).weight (trans c y) = (K0 hF).weight y :=
    graphLaw_weight_translate (foldGraph (Fin 2)) hF c y
  have hl : (lay (trans c y) 0 = fun o => x o + c) ↔ lay y 0 = x := by
    constructor
    · intro h
      funext o
      have := congrFun h o
      simp only [lay, trans_apply] at this
      exact add_right_cancel this
    · intro h
      funext o
      simp only [lay, trans_apply, ← h]
  by_cases hy : lay y 0 = x
  · simp only [hy, ↓reduceIte, hl.mpr hy, hw]
  · have : ¬ (lay (trans c y) 0 = fun o => x o + c) := fun h => hy (hl.mp h)
    simp only [hy, this, ↓reduceIte]

/-- The fold half `H_F`: distinct labels with `x₀ → x₂`. -/
def HF (x : Fin 3 → F) : Prop := Function.Injective x ∧ χ (x 2 - x 0) = 1

instance (x : Fin 3 → F) : Decidable (HF x) := by unfold HF; infer_instance

theorem HF_translate (c : F) (x : Fin 3 → F) : HF (fun o => x o + c) ↔ HF x := by
  unfold HF
  have e : (x 2 + c) - (x 0 + c) = x 2 - x 0 := by ring
  simp only [e]
  constructor
  · rintro ⟨hi, he⟩
    exact ⟨fun a b hab => hi (by simp only [hab]), he⟩
  · rintro ⟨hi, he⟩
    exact ⟨fun a b hab => hi (add_right_cancel hab), he⟩

/-- **`m₀(x) > 0` on `H_F`** (`lem:old-f-law`(a): the fibre count `N₀(x)` is positive), at
`p ≡ 3 (4)`, `p ≥ 19`. -/
theorem m0_pos (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)
    {x : Fin 3 → F} (hx : HF x) : 0 < (m0 hF).weight x := by
  obtain ⟨hinj, h02⟩ := hx
  have h01 : x 0 ≠ x 1 := fun e => absurd (hinj e) (by decide)
  have h02' : x 0 ≠ x 2 := fun e => absurd (hinj e) (by decide)
  have h12 : x 1 ≠ x 2 := fun e => absurd (hinj e) (by decide)
  -- `y₀ → x₂`, `y₀ ∉ {x₀, x₁}`
  have hin := card_in hR h3 (x 2)
  obtain ⟨y0, hy0, hy0s⟩ := exists_avoid (fun b => χ (x 2 - b) = 1) {x 0, x 1} (by
    have := card_pair_le (x 0) (x 1)
    have : (19 : ℤ) ≤ Fintype.card F := by exact_mod_cast h19
    have : (2 : ℤ) < ((univ.filter fun b => χ (x 2 - b) = 1).card : ℤ) := by linarith
    have : (({x 0, x 1} : Finset F).card : ℤ) ≤ 2 := by exact_mod_cast card_pair_le (x 0) (x 1)
    exact_mod_cast (show (({x 0, x 1} : Finset F).card : ℤ) <
      ((univ.filter fun b => χ (x 2 - b) = 1).card : ℤ) by linarith))
  simp only [mem_insert, mem_singleton, not_or] at hy0s
  have hy0x2 : y0 ≠ x 2 := by
    rintro rfl
    rw [sub_self, quadraticChar_zero] at hy0
    exact zero_ne_one hy0
  -- `x₀ → y₂`, `y₀ → y₂`, `y₂ ∉ {x₁, x₂}`
  have hco := card_common_out hR h3 (fun h => hy0s.1 h.symm)
  obtain ⟨y2, hy2, hy2s⟩ := exists_avoid (fun c => χ (c - x 0) = 1 ∧ χ (c - y0) = 1) {x 1, x 2}
    (by
      have : (19 : ℤ) ≤ Fintype.card F := by exact_mod_cast h19
      have : (({x 1, x 2} : Finset F).card : ℤ) ≤ 2 := by exact_mod_cast card_pair_le (x 1) (x 2)
      exact_mod_cast (show (({x 1, x 2} : Finset F).card : ℤ) <
        ((univ.filter fun c => χ (c - x 0) = 1 ∧ χ (c - y0) = 1).card : ℤ) by linarith))
  simp only [mem_insert, mem_singleton, not_or] at hy2s
  have hy2x0 : y2 ≠ x 0 := by
    intro e
    have h := hy2.1
    rw [e, sub_self, quadraticChar_zero] at h
    exact zero_ne_one h
  have hy2y0 : y2 ≠ y0 := by
    intro e
    have h := hy2.2
    rw [e, sub_self, quadraticChar_zero] at h
    exact zero_ne_one h
  -- `y₁` any other label
  obtain ⟨y1, hy1s⟩ := exists_not_mem_of_card ({x 0, x 1, x 2, y0, y2} : Finset F) (by
    have h5 : ({x 0, x 1, x 2, y0, y2} : Finset F).card ≤ 5 := by
      refine (card_insert_le _ _).trans ?_
      refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
      refine Nat.succ_le_succ ((card_insert_le _ _).trans ?_)
      exact Nat.succ_le_succ (card_pair_le _ _)
    omega)
  simp only [mem_insert, mem_singleton, not_or] at hy1s
  let y : Fin 3 → F := ![y0, y1, y2]
  have hyinj : Function.Injective y :=
    injective_three (fun e => hy1s.2.2.2.1 e.symm) (Ne.symm hy2y0) hy1s.2.2.2.2
  have hyx : ∀ o', y o' ∉ ({x 0, x 1, x 2} : Finset F) := by
    intro o'
    simp only [mem_insert, mem_singleton, not_or]
    fin_cases o'
    · exact ⟨hy0s.1, hy0s.2, hy0x2⟩
    · exact ⟨hy1s.1, hy1s.2.1, hy1s.2.2.1⟩
    · exact ⟨hy2x0, hy2s.1, hy2s.2⟩
  have hxx : ∀ o, x o ∈ ({x 0, x 1, x 2} : Finset F) := by
    intro o
    fin_cases o <;> simp
  have hxy : ∀ o o', x o ≠ y o' := fun o o' e => hyx o' (e ▸ hxx o)
  have hY : toY (x, y) ∈ injLabellings F (foldGraph (Fin 2)) := by
    rw [mem_injLabellings_iff_feasible]
    refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
    · obtain ⟨o, ℓ⟩ := a
      obtain ⟨o', ℓ'⟩ := b
      fin_cases ℓ <;> fin_cases ℓ'
      · simp only [toY, Fin.zero_eta, Fin.isValue, ↓reduceIte] at hab
        rw [hinj hab]
      · simp only [toY, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero] at hab
        exact absurd hab (hxy o o')
      · simp only [toY, Fin.zero_eta, Fin.isValue, ↓reduceIte, Fin.mk_one, one_ne_zero] at hab
        exact absurd hab.symm (hxy o' o)
      · simp only [toY, Fin.isValue, Fin.mk_one, one_ne_zero, ↓reduceIte] at hab
        rw [hyinj hab]
    · rw [mem_foldGraph] at he
      obtain ⟨⟨o, ℓ⟩, ⟨o', ℓ'⟩⟩ := e
      simp only at he
      obtain ⟨rfl, rfl⟩ := he
      fin_cases ℓ <;> fin_cases ℓ'
      · exact h02
      · exact hy2.1
      · exact hy0
      · exact hy2.2
  have hK : 0 < (K0 hF).weight (toY (x, y)) := by
    change 0 < (if toY (x, y) ∈ injLabellings F (foldGraph (Fin 2)) then
      1 / ((injLabellings F (foldGraph (Fin 2))).card : ℝ) else 0)
    simp only [hY, ↓reduceIte]
    have : (0 : ℝ) < (injLabellings F (foldGraph (Fin 2))).card := by
      exact_mod_cast card_pos.mpr hF
    positivity
  have hle := le_map_weight (K0 hF) (fun y => lay y 0) (toY (x, y))
  rw [lay_toY_zero] at hle
  exact lt_of_lt_of_le hK hle

/-- The layer swap of the fold objects. -/
theorem K0_swap (y : Fin 3 × Fin 2 → F) :
    (K0 hF).weight (y ∘ layerSwapMap (Fin 3)) = (K0 hF).weight y := by
  have hmem : y ∘ layerSwapMap (Fin 3) ∈ injLabellings F (foldGraph (Fin 2)) ↔
      y ∈ injLabellings F (foldGraph (Fin 2)) :=
    mem_injLabellings_comp_iff _ _ foldGraph_layerSwap y
  simp only [K0, graphLaw, hmem]

/-- **The layer-`1` marginal of `K₀` is `m₀`.** -/
theorem m0_layer1 (x : Fin 3 → F) :
    (∑ y, if lay y 1 = x then (K0 hF).weight y else 0) = (m0 hF).weight x := by
  change _ = ∑ y, if lay y 0 = x then (K0 hF).weight y else 0
  refine Fintype.sum_equiv (relabel (layerSwapMap (Fin 3))) _ _ fun y => ?_
  have hl : lay (relabel (layerSwapMap (Fin 3)) y) 0 = lay y 1 := by
    funext o
    simp [lay, relabel, layerSwapMap]
  change _ = if lay (y ∘ layerSwapMap (Fin 3)) 0 = x then (K0 hF).weight (y ∘ layerSwapMap (Fin 3))
    else 0
  rw [K0_swap]
  rw [show lay (y ∘ layerSwapMap (Fin 3)) 0 = lay y 1 from hl]

/-- The reflection `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)` of a half (`def:record:mixture`(d)). -/
def refl (x : Fin 3 → F) : Fin 3 → F := fun o => -x (Fin.rev o)

omit [Fintype F] [DecidableEq F] in
theorem refl_refl (x : Fin 3 → F) : refl (refl x) = x := by
  funext o
  simp [refl]

/-- The reflection as an equivalence. -/
def reflEquiv : (Fin 3 → F) ≃ (Fin 3 → F) where
  toFun := refl
  invFun := refl
  left_inv := refl_refl
  right_inv := refl_refl

/-- The reflected transpose on two-layer labellings: `Φ(y)_{o, ℓ} = -y_{rev o, 1 - ℓ}`. -/
def reflT (y : Fin 3 × Fin 2 → F) : Fin 3 × Fin 2 → F := toY (refl (lay y 1), refl (lay y 0))

omit [Fintype F] [DecidableEq F] in
theorem reflT_reflT (y : Fin 3 × Fin 2 → F) : reflT (reflT y) = y := by
  unfold reflT
  rw [lay_toY_zero, lay_toY_one, refl_refl, refl_refl]
  exact pairEquiv.right_inv y

/-- The reflected transpose preserves `Inj_p(G_{F,2})` (`K₀^ς = K₀`, `def:record:mixture`(d)). -/
theorem reflT_mem (y : Fin 3 × Fin 2 → F)
    (hy : y ∈ injLabellings F (foldGraph (Fin 2))) :
    reflT y ∈ injLabellings F (foldGraph (Fin 2)) := by
  rw [mem_injLabellings_iff_feasible] at hy ⊢
  obtain ⟨hinj, hedge⟩ := hy
  have hv : ∀ w : Fin 3 × Fin 2, reflT y w = -y (Fin.rev w.1, 1 - w.2) := by
    rintro ⟨o, ℓ⟩
    fin_cases ℓ <;> simp [reflT, toY, refl, lay]
  refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
  · rw [hv, hv, neg_inj] at hab
    have := hinj _ (mem_univ _) _ (mem_univ _) hab
    obtain ⟨o, ℓ⟩ := a
    obtain ⟨o', ℓ'⟩ := b
    simp only [Prod.mk.injEq, Fin.rev_inj, sub_right_inj] at this
    rw [this.1, this.2]
  · rw [mem_foldGraph] at he
    obtain ⟨⟨o, ℓ⟩, ⟨o', ℓ'⟩⟩ := e
    simp only at he
    obtain ⟨rfl, rfl⟩ := he
    rw [hv, hv]
    have hrev0 : Fin.rev (0 : Fin 3) = 2 := rfl
    have hrev2 : Fin.rev (2 : Fin 3) = 0 := rfl
    simp only [hrev0, hrev2]
    have e := hedge ((0, 1 - ℓ'), (2, 1 - ℓ)) ((mem_foldGraph (Fin 2) _).mpr ⟨rfl, rfl⟩)
      (mem_univ _)
      (mem_univ _)
    simp only at e
    rw [show -y (0, 1 - ℓ') - -y (2, 1 - ℓ) = y (2, 1 - ℓ) - y (0, 1 - ℓ') by ring]
    exact e

/-- **`m₀ ∘ ς = m₀`** (`lem:old-f-law`(a): `g₀ ∘ ς = g₀`). -/
theorem m0_refl (x : Fin 3 → F) :
    (m0 hF).weight (refl x) = (m0 hF).weight x := by
  have hK : ∀ y, (K0 hF).weight (reflT y) = (K0 hF).weight y := by
    intro y
    have hmem : reflT y ∈ injLabellings F (foldGraph (Fin 2)) ↔
        y ∈ injLabellings F (foldGraph (Fin 2)) :=
      ⟨fun h => by rw [← reflT_reflT y]; exact reflT_mem _ h, reflT_mem y⟩
    simp only [K0, graphLaw, hmem]
  let Φ : (Fin 3 × Fin 2 → F) ≃ (Fin 3 × Fin 2 → F) :=
    ⟨reflT, reflT, reflT_reflT, reflT_reflT⟩
  rw [← m0_layer1 hF x]
  change (∑ y, if lay y 0 = refl x then (K0 hF).weight y else 0) = _
  refine (Fintype.sum_equiv Φ _ _ fun y => ?_).symm
  change _ = if lay (reflT y) 0 = refl x then (K0 hF).weight (reflT y) else 0
  rw [hK]
  have hl : lay (reflT y) 0 = refl (lay y 1) := by rw [reflT, lay_toY_zero]
  rw [hl]
  have hiff : refl (lay y 1) = refl x ↔ lay y 1 = x :=
    ⟨fun h => by rw [← refl_refl (lay y 1), h, refl_refl], fun h => by rw [h]⟩
  by_cases h : lay y 1 = x
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, mt hiff.mp h]

end Sarkozy.SignedComponents

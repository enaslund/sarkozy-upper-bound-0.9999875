module

public import Sarkozy.BlockAdapter.Root

@[expose] public section

/-!
# The block adapter for the layer cuts L21 and E21 (`lem:front12:reference`(ii), third display)

`paper/sections/20c_middle_frame.tex`, proof of `lem:front12:reference`(ii), last paragraph;
`lem:layer12-geometry`(c); `lem:spec:cutkernel`(e); `lem:spec:tensorcomp`(b),(c),
`lem:majorant`(c) (W7's `cut_block_cap`).

The proof reads: at `ι`, the half graphs of `G_{L,2}` and `G_{E,2}` are their one-layer graphs
(`lem:layer12-geometry`(c)), and the cut form of `Diag_ι(Π⁽¹⁾_φ)` at `Φ` is the mean of `Φ²` under
`Π⁽¹⁾_φ`; so the caps L21 and E21 give `Π_φ ⪰_ι -k r Diag_ι(Π⁽¹⁾_φ)`. Formalized here, for any
object set `O`, two-layer graph `G₂` invariant under the layer swap, one-layer graph `G₁` equal to
the layer-`0` restriction of `G₂`, and pattern `φ : ℤ/6ℤ → O`:

* `layerData O G₂`: the spectral data (`def:spec:data`) of the layer swap of `O × Fin 2`
  (plus half: layer `0`);
* `layerHalfEquiv_edges`: its half graph is `G₁` (`lem:layer12-geometry`(c));
* `reservedForm_two`, `reservedForm_diag`: the cut forms at `ι` of the emitted two-layer component
  `emit λ₂ (midEmission φ)` and of the diagonal copy `emit λ₁ (midDiagEmission φ)`;
* `block_cut_expect`: `lem:spec:cutkernel`(e) for block graph laws `λ_𝔅(G) = ⊗_p λ_p(G)` (labels
  in `∏_p 𝔽_p`);
* **`layerCap_of_cutCaps`**: `Π_φ ⪰_ι -g e^{BL/(X log X)} b^{-1/2} Diag_ι(Π⁽¹⁾_φ)` for the block
  laws, from the per-prime bounds `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` of the layer cut;
* `recordLayer`, `matchLayer`: the instances `G₂ = G_{L,2}` (L21) and `G₂ = G_{E,2}` (E21).
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockAdapter

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts

/-! ## The layer swap of `O × Fin 2` -/

/-- The layer swap of `Fin 2`: plus half `{0}`, flip `j ↦ 1 - j`. -/
def finCut : ReflectionCut (Fin 2) where
  half := {0}
  flip :=
    { toFun := fun j => 1 - j
      invFun := fun j => 1 - j
      left_inv := by
        intro j
        fin_cases j <;> rfl
      right_inv := by
        intro j
        fin_cases j <;> rfl }
  flip_flip := by
    intro j
    fin_cases j <;> rfl
  crosses := by decide

variable (O : Type) [Fintype O] [DecidableEq O]

/-- A two-layer graph is invariant under the layer swap. -/
def SwapInvariant (G : OrientedGraph (O × Fin 2)) : Prop :=
  ∀ u w, (u, w) ∈ G.E ↔ ((u.1, 1 - u.2), (w.1, 1 - w.2)) ∈ G.E

/-- **The spectral data of the reserved cut** of a two-layer graph invariant under the layer
swap (`def:spec:data`): the cuts L21 (`G_{L,2}`), F21 (`G_{F,2}`), E21 (`G_{E,2}`). -/
noncomputable def layerData (G : OrientedGraph (O × Fin 2)) (hG : SwapInvariant O G) :
    SpecData (O × Fin 2) where
  G := G
  cut := finCut.prodRight O
  aut u w := hG u w
  order := by
    classical
    simpa only [Fintype.card_coe] using (Fintype.equivFin (finCut.prodRight O).Half).symm

theorem mem_layerHalf (v : O × Fin 2) : v ∈ (finCut.prodRight O).half ↔ v.2 = 0 := by
  change v ∈ (Finset.univ : Finset O) ×ˢ ({0} : Finset (Fin 2)) ↔ _
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton, true_and]

section Graph

variable (G₂ : OrientedGraph (O × Fin 2)) (hG : SwapInvariant O G₂)
  (G₁ : OrientedGraph (O × Fin 1))

/-- The plus half of the layer swap is `O × {0}`. -/
def layerHalfEquiv : (layerData O G₂ hG).cut.Half ≃ O × Fin 1 where
  toFun v := (v.1.1, 0)
  invFun v := ⟨(v.1, 0), (mem_layerHalf O _).mpr rfl⟩
  left_inv v := Subtype.ext (Prod.ext rfl ((mem_layerHalf O _).mp v.2).symm)
  right_inv _ := Prod.ext rfl (Subsingleton.elim _ _)

/-- `G₁` is the layer-`0` restriction of `G₂`. -/
def LayerRestricts : Prop := ∀ o o' : O, ((o, 0), (o', 0)) ∈ G₂.E ↔ ((o, 0), (o', 0)) ∈ G₁.E

/-- **`lem:layer12-geometry`(c)**: the half graph of the layer swap is the one-layer graph. -/
theorem layerHalfEquiv_edges (hres : LayerRestricts O G₂ G₁) (a b : (layerData O G₂ hG).cut.Half) :
    (a, b) ∈ (layerData O G₂ hG).halfGraph.E ↔
      (layerHalfEquiv O G₂ hG a, layerHalfEquiv O G₂ hG b) ∈ G₁.E := by
  rw [SpecData.mem_halfGraph]
  obtain ⟨⟨o, l⟩, ha⟩ := a
  obtain ⟨⟨o', l'⟩, hb⟩ := b
  have hl : l = 0 := (mem_layerHalf O _).mp ha
  have hl' : l' = 0 := (mem_layerHalf O _).mp hb
  subst hl hl'
  exact hres o o'

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The half law of the layer swap is the one-layer graph law. -/
theorem layerHalfLaw_expect (hres : LayerRestricts O G₂ G₁)
    (hne₂ : (injLabellings F G₂).Nonempty) (hne₁ : (injLabellings F G₁).Nonempty)
    (Ψ : ((layerData O G₂ hG).cut.Half → F) → ℝ) :
    ((layerData O G₂ hG).halfLaw hne₂).expect Ψ =
      (graphLaw G₁ hne₁).expect (fun y => Ψ (y ∘ layerHalfEquiv O G₂ hG)) := by
  let e := layerHalfEquiv O G₂ hG
  have hedge : ∀ a b, (a, b) ∈ G₁.E ↔
      (e.symm a, e.symm b) ∈ (layerData O G₂ hG).halfGraph.E := by
    intro a b
    rw [layerHalfEquiv_edges O G₂ hG G₁ hres, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact Cuts.graphLaw_iso _ _ e.symm hedge hne₁ ((layerData O G₂ hG).half_nonempty hne₂) Ψ

theorem layerHalfLaw_weight (hres : LayerRestricts O G₂ G₁)
    (hne₂ : (injLabellings F G₂).Nonempty) (hne₁ : (injLabellings F G₁).Nonempty)
    (y : O × Fin 1 → F) :
    ((layerData O G₂ hG).halfLaw hne₂).weight (precomp (layerHalfEquiv O G₂ hG) F y) =
      (graphLaw G₁ hne₁).weight y :=
  weight_of_expect_equiv _ _ (precomp (layerHalfEquiv O G₂ hG) F)
    (layerHalfLaw_expect O G₂ hG G₁ hres hne₂ hne₁) y

end Graph

/-! ## The cut forms at `ι` of the emitted components -/

theorem reserved_half_layer (v : reservedCut.Half) : v.1.2.2 = 0 := by
  have h := v.2
  change v.1 ∈ (Finset.univ : Finset Chamber) ×ˢ
    ((Finset.univ : Finset Chamber) ×ˢ ({0} : Finset Layer)) at h
  simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_singleton, true_and] at h
  exact h

theorem layerFin_flip_zero : layerFin (layerCut.flip 0) = finCut.flip 0 := by decide

/-- The slots of the plus half of `ι` read the layer-`0` labels of the objects `φ(u₀)`. -/
def slotRows {X : Type} (φ : ZMod 6 → O) (x : (finCut.prodRight O).Half → X) :
    reservedCut.Half → X :=
  fun v => x ⟨(φ v.1.1, 0), (mem_layerHalf O _).mpr rfl⟩

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The cut form at `ι` of a two-layer component** `Π_φ = emit λ (midEmission φ)`: the plus half
reads layer `0`, the minus half layer `1`. -/
theorem reservedForm_two (lam : FiniteLaw (O × Fin 2 → X)) (φ : ZMod 6 → O)
    (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (midEmission φ)).weight) F G =
      lam.expect (fun y => F (slotRows O φ (fun h => y h.1)) *
        G (slotRows O φ (fun h => y ((finCut.prodRight O).flip h.1)))) := by
  change (emit lam (midEmission φ)).expect _ = _
  rw [expect_emit]
  refine lam.expect_congr fun y => ?_
  have h1 : (fun v : reservedCut.Half => (y ∘ midEmission φ) v.1) =
      slotRows O φ (fun h => y h.1) := by
    funext v
    have hv := reserved_half_layer v
    simp only [Function.comp_apply, midEmission, slotRows, hv]
    rfl
  have h2 : (fun v : reservedCut.Half => (y ∘ midEmission φ) (reservedCut.flip v.1)) =
      slotRows O φ (fun h => y ((finCut.prodRight O).flip h.1)) := by
    funext v
    have hv := reserved_half_layer v
    obtain ⟨⟨u₀, u₁, l⟩, hmem⟩ := v
    change l = 0 at hv
    subst hv
    change y (φ u₀, layerFin (layerCut.flip 0)) = y (φ u₀, finCut.flip 0)
    rw [layerFin_flip_zero]
  rw [h1, h2]

/-- **The cut form at `ι` of a diagonal copy** `Diag_ι(Π⁽¹⁾_φ)`: the mean of `Φ²`
(`lem:commoncut`). -/
theorem reservedForm_diag (lam : FiniteLaw (O × Fin 1 → X)) (φ : ZMod 6 → O)
    (F : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (midDiagEmission φ)).weight) F F =
      lam.expect (fun y => F (fun v => y (φ v.1.1, 0)) * F (fun v => y (φ v.1.1, 0))) := by
  change (emit lam (midDiagEmission φ)).expect _ = _
  rw [expect_emit]
  rfl

/-! ## Blocks -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  {U : Type} [Fintype U] [DecidableEq U]

/-- The block half configuration read as per-prime half configurations. -/
def blockHalfRows (D : SpecData U) (ξ : ∀ i, D.cut.Half → ZMod (pr i)) :
    D.cut.Half → BlockLabel pr :=
  fun h i => ξ i h

/-- **`lem:spec:cutkernel`(e) for block graph laws**: under `λ_𝔅(G) = ⊗_p λ_p(G)` with labels in
`∏_p 𝔽_p`, `E[F(x) H(x')] = ⟨F, (⊗_p A_p) H⟩_{⊗ μ_p}`. -/
theorem block_cut_expect (D : SpecData U)
    (hL : ∀ i, (injLabellings (ZMod (pr i)) D.G).Nonempty)
    (Fn Hn : (D.cut.Half → BlockLabel pr) → ℝ) :
    (blockGraphLaw pr D.G hL).expect
        (fun y => Fn (fun h => y h.1) * Hn (fun h => y (D.cut.flip h.1))) =
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i))
        (Fn ∘ blockHalfRows pr D) (Hn ∘ blockHalfRows pr D) := by
  rw [← SpecData.block_cut_form D hL]
  unfold blockGraphLaw
  rw [expect_tensor_eq_sum]
  rfl

variable (G₂ : OrientedGraph (O × Fin 2)) (hG : SwapInvariant O G₂)
  (G₁ : OrientedGraph (O × Fin 1))

/-- **The layer cap from per-prime cut caps** (`lem:front12:reference`(ii), third display, with
`lem:layer12-geometry`(c), `lem:spec:tensorcomp`(b),(c), `lem:majorant`(c)): for the block laws
`λ₂ = λ_𝔅(G₂)`, `λ₁ = λ_𝔅(G₁)` and a pattern `φ`, on a block of primes `p_i ≥ b ≥ X > 1` with
`∑ log p_i ≤ L`, if the per-prime cut operators of the layer swap satisfy
`-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p`, then `Π_φ ⪰_ι -d b^{-1/2} Diag_ι(Π⁽¹⁾_φ)`,
`d = g e^{BL/(X log X)}`. -/
theorem layerCap_of_cutCaps (hres : LayerRestricts O G₂ G₁)
    (hL : ∀ i, (injLabellings (ZMod (pr i)) G₂).Nonempty)
    (h₁ : ∀ i, (injLabellings (ZMod (pr i)) G₁).Nonempty) (φ : ZMod 6 → O)
    {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(pr i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (layerData O G₂ hG) (hL i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, Spectral.cutOp (layerData O G₂ hG) (hL i) v⟫_ℝ ≤
      (1 + B / pr i) * ‖v‖ ^ 2) :
    reservedCut.Below
      (-(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) •
        signedIntegral (emit (blockGraphLaw pr G₁ h₁) (midDiagEmission φ)).weight)
      (signedIntegral (emit (blockGraphLaw pr G₂ hL) (midEmission φ)).weight) := by
  set D := layerData O G₂ hG
  set μ := FiniteLaw.pi fun i => D.halfLaw (hL i)
  set K := fun x y : (∀ i, D.cut.Half → ZMod (pr i)) =>
    ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i)
  have htwo : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL) (midEmission φ)).weight)
        F G = kernelForm μ μ K ((F ∘ slotRows O φ) ∘ blockHalfRows pr D)
          ((G ∘ slotRows O φ) ∘ blockHalfRows pr D) := by
    intro F G
    rw [reservedForm_two]
    exact block_cut_expect pr D hL (F ∘ slotRows O φ) (G ∘ slotRows O φ)
  have hdiagPos := emit_positive (blockGraphLaw pr G₁ h₁) (midDiagEmission φ) reservedCut
    (midDiagEmission_reserved φ)
  have hK : ∀ x y, K y x = K x y := by
    intro x y
    simp only [K]
    exact Finset.prod_congr rfl fun i _ => by rw [D.cutK_symm]
  constructor
  · intro F G
    change reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (midEmission φ)).weight) F G -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (midDiagEmission φ)).weight) F G =
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (midEmission φ)).weight) G F -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (midDiagEmission φ)).weight) G F
    rw [htwo, htwo, kernelForm_symm μ K hK, hdiagPos.symmetric F G]
  · intro F
    change 0 ≤ reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (midEmission φ)).weight) F F -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (midDiagEmission φ)).weight) F F
    have hdiag : reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
        (midDiagEmission φ)).weight) F F =
        μ.expect (fun ξ => ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ξ *
          ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ξ) := by
      rw [reservedForm_diag, pi_expect_equiv (fun i => D.halfLaw (hL i))
        (fun i => graphLaw G₁ (h₁ i)) (fun i => precomp (layerHalfEquiv O G₂ hG) _)
        (fun i y => layerHalfLaw_weight O G₂ hG G₁ hres (hL i) (h₁ i) y)]
      unfold blockGraphLaw
      rw [expect_tensor_eq_sum]
      rfl
    rw [htwo, hdiag]
    have h := UpperReference.cut_block_cap D pr hL hg hB hX hXb hbp hLs hgp hlow hup
      ((F ∘ slotRows O φ) ∘ blockHalfRows pr D)
    have hn : Recentering.nrm μ ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ^ 2 =
        μ.expect (fun ξ => ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ξ *
          ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ξ) := by
      unfold Recentering.nrm Recentering.ip
      exact Real.sq_sqrt (μ.expect_nonneg fun ξ => mul_self_nonneg _)
    rw [hn] at h
    linarith

end Block

/-! ## The instances L21 and E21 -/

/-- `G_{L,2}` is invariant under the layer swap. -/
theorem recordGraph_swap : SwapInvariant (ZMod 6) (recordGraph (Fin 2)) := by
  intro u w
  rw [mem_recordGraph, mem_recordGraph]

/-- `G_{E,2}` (edgeless) is invariant under the layer swap. -/
theorem matchGraph_swap : SwapInvariant (Fin 3) (matchGraph (Fin 2)) := by
  intro u w
  simp [matchGraph]

/-- `G_{L,1}` is the layer-`0` restriction of `G_{L,2}`. -/
theorem recordGraph_restricts :
    LayerRestricts (ZMod 6) (recordGraph (Fin 2)) (recordGraph (Fin 1)) := by
  intro o o'
  rw [mem_recordGraph, mem_recordGraph]

/-- `G_{E,1}` is the layer-`0` restriction of `G_{E,2}`. -/
theorem matchGraph_restricts :
    LayerRestricts (Fin 3) (matchGraph (Fin 2)) (matchGraph (Fin 1)) := by
  intro o o'
  simp [matchGraph]

/-- The spectral data of the cut L21 (the layer swap of `G_{L,2}`). -/
noncomputable abbrev recordLayer : SpecData (ZMod 6 × Fin 2) :=
  layerData (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap

/-- The spectral data of the cut E21 (the layer swap of `G_{E,2}`). -/
noncomputable abbrev matchLayer : SpecData (Fin 3 × Fin 2) :=
  layerData (Fin 3) (matchGraph (Fin 2)) matchGraph_swap

end Sarkozy.BlockAdapter

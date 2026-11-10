module

public import Sarkozy.BlockInputs.Middle

@[expose] public section

/-!
# The positive-root caps L20, L21 from per-prime certificates

`prop:root-chamber`, `prop:root-layer`.

`paper/sections/20b_positive_roots.tex`, `prop:root-chamber` (the chamber cut `ϑ₀` of
`Γ_{p,u}`, in the fixed half chart `L²(μ_p)`, `μ_p = λ_p(G_F)`: `-g^u_{20} p^{-1/2} ⪯ T_u ⪯
1 + c^{+,u}_{20}/p`, and the block cap by `lem:spec:tensorcomp`(b)), `prop:root-layer` (the same at
the layer cut, in the chart of the untilted one-layer root), `cert:positive-root-caps`;
`13_cuts_correlations.tex`, `lem:spec:cutkernel`(f) (the cut form of a reweighted law);
`20c_middle_frame.tex`, proof of `lem:front12:reference`(ii) (`rem:root-charts`).

B6 kept the L20 envelope and the L21 cap of the individual-square root of the pieces `2³⁶`, `2⁴⁰`
as block-level hypotheses (inside `MiddleIndividualBlockInputs`): the positive root is a
reweighted law, and B6's adapter covered graph laws only. This file is that adapter for reweighted
laws:

* `glue_swap`: `glue x' x = (glue x x') ∘ ϑ`; `wKer D hne w` (the kernel
  `w(x ⊔ x') K(x, x')/(Z E w)` of `lem:spec:cutkernel`(f)); `wKer_symm` (for `w ∘ ϑ = w`);
* **`wKer_block_lower`**: per-prime `-g p^{-1/2} ⪯ A^w_p ⪯ 1 + B/p` give
  `⊗ A^w_p ⪰ -g e^{BL/(X log X)} b^{-1/2}` (`lem:spec:tensorcomp`(b), `lem:majorant`(c));
* `tensor_cut_expect_w`: `lem:spec:cutkernel`(f) for a tensor of reweighted laws (labels in
  `∏ 𝔽_p`); `individualRoot_eq_reweight`;
* `IndRootChamberCap u g B p`, `IndRootLayerCap u g B p` (the per-prime statements of
  `prop:root-chamber` and `prop:root-layer`), `MiddleIndividualRootCert i u` (per-piece constants
  for both cuts, block caps at most `capVal i 0` and `capK i L`);
* **`rootEnvelope_individual_of_caps`**, **`individualRootLayerCap_of_caps`**,
  **`middleIndividualRoot_of_cert`**: B6's two block-level fields from the certificates.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.BlockAdapter

/-! ## Reweighted cut kernels -/

section Weighted

variable {U : Type} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- Exchanging the halves of a glued labelling is precomposition with the cut's flip. -/
theorem glue_swap {F : Type} (x x' : D.cut.Half → F) : D.glue x' x = D.glue x x' ∘ D.cut.flip := by
  funext v
  simp only [Function.comp_apply]
  unfold SpecData.glue
  by_cases h : v ∈ D.cut.half
  · have h' : D.cut.flip v ∉ D.cut.half := fun hf => (D.cut.crosses v).1 hf h
    rw [dite_eq_left h, dite_eq_right h']
    congr 1
    exact Subtype.ext (D.cut.flip_flip v).symm
  · have hf : D.cut.flip v ∈ D.cut.half := (D.cut.crosses v).2 h
    rw [dite_eq_right h, dite_eq_left hf]

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The kernel of the cut operator `A^w` of a reweighted law** (`lem:spec:cutkernel`(f)),
relative to `μ ⊗ μ`: `w(x ⊔ x') K(x, x')/(Z E_λ w)`. -/
noncomputable def wKer (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ)
    (x x' : D.cut.Half → F) : ℝ :=
  w (D.glue x x') * D.cutK x x' / (D.cutZ hne * (graphLaw D.G hne).expect w)

theorem wKer_symm (hne : (injLabellings F D.G).Nonempty) {w : (U → F) → ℝ}
    (hw : ∀ y, w (y ∘ D.cut.flip) = w y) (x x' : D.cut.Half → F) :
    wKer D hne w x x' = wKer D hne w x' x := by
  unfold wKer
  rw [glue_swap D x' x, hw, D.cutK_symm]

end Weighted

section Block

variable {U : Type} [Fintype U] [DecidableEq U] (D : SpecData U) {ι : Type} [Fintype ι]
  [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hL : ∀ i, (injLabellings (ZMod (pr i)) D.G).Nonempty)

/-- **The block cap of a tensor of reweighted cut operators** (`lem:spec:tensorcomp`(b),
`lem:majorant`(c)): per-prime `-g p^{-1/2} ⪯ A^w_p ⪯ 1 + B/p` give
`⊗_p A^w_p ⪰ -g e^{BL/(X log X)} b^{-1/2}` on `L²(⊗ μ_p)`. -/
theorem wKer_block_lower (w : ∀ i, (U → ZMod (pr i)) → ℝ)
    (hsym : ∀ i y, w i (y ∘ D.cut.flip) = w i y) {g B X L b : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B)
    (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ pr i) (hLs : ∑ i, Real.log (pr i) ≤ L)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : (D.cut.Half → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm (D.halfLaw (hL i)) f ^ 2 ≤
        kernelForm (D.halfLaw (hL i)) (D.halfLaw (hL i)) (wKer D (hL i) (w i)) f f)
    (hup : ∀ i (f : (D.cut.Half → ZMod (pr i)) → ℝ),
      kernelForm (D.halfLaw (hL i)) (D.halfLaw (hL i)) (wKer D (hL i) (w i)) f f ≤
        (1 + B / pr i) * Recentering.nrm (D.halfLaw (hL i)) f ^ 2)
    (Fn : (∀ i, D.cut.Half → ZMod (pr i)) → ℝ) :
    -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hL i)) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hL i)) (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (fun x y => ∏ i, wKer D (hL i) (w i) (x i) (y i)) Fn Fn := by
  have hb : 0 < b := by linarith
  have h := Spectral.tensorcomp_block_supp (fun i => D.halfLaw (hL i))
    (fun i => wKer D (hL i) (w i)) (fun i x y => wKer_symm D (hL i) (hsym i) x y)
    (fun i => (pr i : ℝ)) hg hB hb hbp hgp hlow hup Fn
  have hprod := UpperReference.prod_one_add_le_exp (fun i => (pr i : ℝ)) hB hX
    (fun i => hXb.trans (hbp i)) hLs
  have hn : 0 ≤ Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hL i)) Fn ^ 2 := sq_nonneg _
  have hsb : 0 ≤ (√b)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hcmp : g * (√b)⁻¹ * ∏ i, (1 + B / (pr i : ℝ)) ≤
      g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹ := by
    calc g * (√b)⁻¹ * ∏ i, (1 + B / (pr i : ℝ)) ≤
          g * (√b)⁻¹ * Real.exp (B * L / (X * Real.log X)) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hg hsb)
      _ = g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹ := by ring
  calc -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hL i)) Fn ^ 2 ≤
      -(g * (√b)⁻¹ * ∏ i, (1 + B / (pr i : ℝ))) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hL i)) Fn ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ _ := h

/-- **`lem:spec:cutkernel`(f) for a tensor of reweighted laws** (labels in `∏_p 𝔽_p`):
`E[F(x) H(x')] = ⟨F, (⊗_p A^{w_p}) H⟩_{⊗ μ_p}`. -/
theorem tensor_cut_expect_w (w : ∀ i, (U → ZMod (pr i)) → ℝ) (hw : ∀ i y, 0 ≤ w i y)
    (hpos : ∀ i, 0 < (graphLaw D.G (hL i)).expect (w i))
    (Fn Hn : (D.cut.Half → BlockLabel pr) → ℝ) :
    (FiniteLaw.tensor fun i => reweight (graphLaw D.G (hL i)) (w i) (hw i) (hpos i)).expect
        (fun y => Fn (fun h => y h.1) * Hn (fun h => y (D.cut.flip h.1))) =
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (fun x y => ∏ i, wKer D (hL i) (w i) (x i) (y i))
        (Fn ∘ blockHalfRows pr D) (Hn ∘ blockHalfRows pr D) := by
  unfold wKer
  rw [← SpecData.block_cut_form_w D hL w hw hpos]
  rw [expect_tensor_eq_sum]
  rfl

end Block

/-! ## The individual-square root as a reweighted law -/

theorem individualRoot_eq_reweight (p : ℕ) [Fact p.Prime] (u : ℚ)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) :
    individualRoot p u hne = reweight (graphLaw (recordGraph (Fin 2)) hne) (individualWeight p u)
      (fun x => (individualWeight_pos p u x).le)
      (expect_pos_of_pos _ (individualWeight_pos p u)) := by
  unfold individualRoot tiltLaw reweight
  congr 1
  funext x
  ring

/-- The ϑ₀ flip of the twelve labels is `g₆(5)`: `u ↦ 5 - u`. -/
theorem recordFlip_eq (v : ZMod 6 × Fin 2) : (recordData (Fin 2)).cut.flip v = g6Vert 5 v := by
  have key : ∀ u : ZMod 6, (chamberCut 0).flip u = g6 5 u := by decide
  exact Prod.ext (key v.1) rfl

/-- The layer flip of the twelve labels is the layer swap. -/
theorem layerFlip_eq (v : ZMod 6 × Fin 2) : recordLayer.cut.flip v = layerSwapMap (ZMod 6) v := by
  have key : ∀ j : Fin 2, finCut.flip j = Equiv.swap (0 : Fin 2) 1 j := by decide
  exact Prod.ext rfl (key v.2)

theorem individualWeight_recordFlip (p : ℕ) [Fact p.Prime] (u : ℚ)
    (y : ZMod 6 × Fin 2 → ZMod p) :
    individualWeight p u (y ∘ (recordData (Fin 2)).cut.flip) = individualWeight p u y := by
  have h : y ∘ (recordData (Fin 2)).cut.flip = y ∘ g6Vert 5 := funext fun v => by
    simp only [Function.comp_apply, recordFlip_eq]
  rw [h, individualWeight_g6]

theorem individualWeight_layerFlip (p : ℕ) [Fact p.Prime] (u : ℚ)
    (y : ZMod 6 × Fin 2 → ZMod p) :
    individualWeight p u (y ∘ recordLayer.cut.flip) = individualWeight p u y := by
  have h : y ∘ recordLayer.cut.flip = y ∘ layerSwapMap (ZMod 6) := funext fun v => by
    simp only [Function.comp_apply, layerFlip_eq]
  rw [h]
  unfold individualWeight rootScore
  simp only [rootTrace_layerSwap]

/-! ## The block caps of the positive root -/

section Caps

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The cut form of the block positive root at `ϑ₀` is the tensor of the per-prime reweighted
cut operators** (`lem:spec:cutkernel`(f), `rem:root-charts`: the chart is the fixed half law
`μ_p = λ_p(G_F)`). -/
theorem blockIndRootForm (u : ℚ)
    (hL : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (φ ψ : ((chamberCut 0).Half → Fin 2 → BlockLabel pr) → ℝ) :
    (chamberCut 0).form (lawL (objLaw (individualBlockRoot pr u hL))) φ ψ =
      kernelForm (halfPi (Fin 2) pr hL) (halfPi (Fin 2) pr hL)
        (fun x y => ∏ i, wKer (recordData (Fin 2)) (hL i) (individualWeight (pr i) u) (x i) (y i))
        (φ ∘ blockRows (Fin 2) pr) (ψ ∘ blockRows (Fin 2) pr) := by
  unfold wKer
  rw [← SpecData.block_cut_form_w (recordData (Fin 2)) hL (fun i => individualWeight (pr i) u)
    (fun i y => (individualWeight_pos (pr i) u y).le)
    (fun i => expect_pos_of_pos _ (individualWeight_pos (pr i) u))]
  change (objLaw (individualBlockRoot pr u hL)).expect _ = _
  rw [expect_objLaw]
  unfold individualBlockRoot
  simp only [individualRoot_eq_reweight]
  rw [expect_tensor_eq_sum]
  rfl

/-- **The L20 envelope of the positive root from per-prime caps** (`prop:root-chamber` with
`lem:spec:tensorcomp`(b); `lem:front12:reference`(ii), first inequality, pieces from `2³⁰`):
per-prime `-g p^{-1/2} ⪯ T_u ⪯ 1 + B/p` in the chart `L²(μ_p)` give
`Π_L ⪰_{ϑ₀} -g e^{BL/(X log X)} b^{-1/2} Π_{F₀}` for the individual-root datum. -/
theorem rootEnvelope_individual_of_caps (hne : MiddleNonempty pr) (u : ℚ) {g B X L b : ℝ}
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ pr i)
    (hLs : ∑ i, Real.log (pr i) ≤ L) (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : ((recordData (Fin 2)).cut.Half → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm ((recordData (Fin 2)).halfLaw (hne.L2 i)) f ^ 2 ≤
        kernelForm ((recordData (Fin 2)).halfLaw (hne.L2 i))
          ((recordData (Fin 2)).halfLaw (hne.L2 i))
          (wKer (recordData (Fin 2)) (hne.L2 i) (individualWeight (pr i) u)) f f)
    (hup : ∀ i (f : ((recordData (Fin 2)).cut.Half → ZMod (pr i)) → ℝ),
      kernelForm ((recordData (Fin 2)).halfLaw (hne.L2 i))
          ((recordData (Fin 2)).halfLaw (hne.L2 i))
          (wKer (recordData (Fin 2)) (hne.L2 i) (individualWeight (pr i) u)) f f ≤
        (1 + B / pr i) * Recentering.nrm ((recordData (Fin 2)).halfLaw (hne.L2 i)) f ^ 2) :
    RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u))
      (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ := by
  set D := fieldDatum (middleBlock_datumHyp₂_individual pr hne u)
  have hcompL : D.compL = lawL (objLaw (individualBlockRoot pr u hne.L2)) := rfl
  have hcompF : D.compF 0 =
      lawL (patternLaw (fold 0) (objLaw (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2))) := rfl
  constructor
  · intro φ ψ
    change (chamberCut 0).form D.compL φ ψ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) φ ψ =
      (chamberCut 0).form D.compL ψ φ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) ψ φ
    rw [form_symm_of_flip_inv (chamberCut 0) (flip_inv_of_inv6 D.compL_inv6) φ ψ,
      D.compF0_positive.symmetric φ ψ]
  · intro φ
    change 0 ≤ (chamberCut 0).form D.compL φ φ -
        -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) * (chamberCut 0).form (D.compF 0) φ φ
    rw [hcompL, hcompF, blockIndRootForm pr u hne.L2 φ φ, blockFoldForm (Fin 2) pr hne.L2 hne.F2 φ]
    have h := wKer_block_lower (recordData (Fin 2)) pr hne.L2 (fun i => individualWeight (pr i) u)
      (fun i y => individualWeight_recordFlip (pr i) u y) hg hB hX hXb hbp hLs hgp hlow hup
      (φ ∘ blockRows (Fin 2) pr)
    have hn : Recentering.nrm (halfPi (Fin 2) pr hne.L2) (φ ∘ blockRows (Fin 2) pr) ^ 2 =
        (halfPi (Fin 2) pr hne.L2).expect
          (fun ξ => (φ ∘ blockRows (Fin 2) pr) ξ * (φ ∘ blockRows (Fin 2) pr) ξ) := by
      unfold Recentering.nrm Recentering.ip
      exact Real.sq_sqrt ((halfPi (Fin 2) pr hne.L2).expect_nonneg fun ξ => mul_self_nonneg _)
    change _ ≤ kernelForm (halfPi (Fin 2) pr hne.L2) (halfPi (Fin 2) pr hne.L2) _ _ _ at h
    rw [hn] at h
    linarith

/-- **The L21 cap of the positive root from per-prime caps** (`prop:root-layer` with
`lem:spec:tensorcomp`(b); `lem:front12:reference`(ii), third display, the root type; the chart is
the half law of `Diag_ι(Π⁽¹⁾_L)`, the untilted one-layer root): per-prime
`-g p^{-1/2} ⪯ T^ι_u ⪯ 1 + B/p` give `Π_L ⪰_ι -g e^{BL/(X log X)} b^{-1/2} Diag_ι(Π⁽¹⁾_L)`. -/
theorem individualRootLayerCap_of_caps (hne : MiddleNonempty pr) (u : ℚ) {g B X L b : ℝ}
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ pr i)
    (hLs : ∑ i, Real.log (pr i) ≤ L) (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : (recordLayer.cut.Half → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm (recordLayer.halfLaw (hne.L2 i)) f ^ 2 ≤
        kernelForm (recordLayer.halfLaw (hne.L2 i)) (recordLayer.halfLaw (hne.L2 i))
          (wKer recordLayer (hne.L2 i) (individualWeight (pr i) u)) f f)
    (hup : ∀ i (f : (recordLayer.cut.Half → ZMod (pr i)) → ℝ),
      kernelForm (recordLayer.halfLaw (hne.L2 i)) (recordLayer.halfLaw (hne.L2 i))
          (wKer recordLayer (hne.L2 i) (individualWeight (pr i) u)) f f ≤
        (1 + B / pr i) * Recentering.nrm (recordLayer.halfLaw (hne.L2 i)) f ^ 2) :
    IndividualRootLayerCap pr u hne (g * Real.exp (B * L / (X * Real.log X))) (√b)⁻¹ := by
  set D := recordLayer
  set μ := FiniteLaw.pi fun i => D.halfLaw (hne.L2 i)
  set K := fun x y : (∀ i, D.cut.Half → ZMod (pr i)) =>
    ∏ i, wKer D (hne.L2 i) (individualWeight (pr i) u) (x i) (y i)
  set c := g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹
  set φ : ZMod 6 → ZMod 6 := fun v => v
  have htwo : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (signedIntegral (emit (individualBlockRoot pr u hne.L2)
        (midEmission φ)).weight) F G = kernelForm μ μ K ((F ∘ slotRows (ZMod 6) φ) ∘
          blockHalfRows pr D) ((G ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D) := by
    intro F G
    rw [reservedForm_two]
    unfold individualBlockRoot
    simp only [individualRoot_eq_reweight]
    exact tensor_cut_expect_w D pr hne.L2 (fun i => individualWeight (pr i) u)
      (fun i y => (individualWeight_pos (pr i) u y).le)
      (fun i => expect_pos_of_pos _ (individualWeight_pos (pr i) u))
      (F ∘ slotRows (ZMod 6) φ) (G ∘ slotRows (ZMod 6) φ)
  have hdiagPos := emit_positive (blockGraphLaw pr (recordGraph (Fin 1)) hne.L1)
    (midDiagEmission φ) reservedCut (midDiagEmission_reserved φ)
  have hK : ∀ x y, K y x = K x y := by
    intro x y
    simp only [K]
    exact Finset.prod_congr rfl fun i _ =>
      wKer_symm D (hne.L2 i) (fun y => individualWeight_layerFlip (pr i) u y) (y i) (x i)
  constructor
  · intro F G
    change reservedCut.form (signedIntegral (emit (individualBlockRoot pr u hne.L2)
          (midEmission φ)).weight) F G - -c *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr (recordGraph (Fin 1)) hne.L1)
            (midDiagEmission φ)).weight) F G =
      reservedCut.form (signedIntegral (emit (individualBlockRoot pr u hne.L2)
          (midEmission φ)).weight) G F - -c *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr (recordGraph (Fin 1)) hne.L1)
            (midDiagEmission φ)).weight) G F
    rw [htwo, htwo, kernelForm_symm μ K hK, hdiagPos.symmetric F G]
  · intro F
    change 0 ≤ reservedCut.form (signedIntegral (emit (individualBlockRoot pr u hne.L2)
          (midEmission φ)).weight) F F - -c *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr (recordGraph (Fin 1)) hne.L1)
            (midDiagEmission φ)).weight) F F
    have hdiag : reservedCut.form (signedIntegral (emit (blockGraphLaw pr (recordGraph (Fin 1))
        hne.L1) (midDiagEmission φ)).weight) F F =
        μ.expect (fun ξ => ((F ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D) ξ *
          ((F ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D) ξ) := by
      rw [reservedForm_diag, pi_expect_equiv (fun i => D.halfLaw (hne.L2 i))
        (fun i => graphLaw (recordGraph (Fin 1)) (hne.L1 i))
        (fun i => precomp (layerHalfEquiv (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap) _)
        (fun i y => layerHalfLaw_weight (ZMod 6) (recordGraph (Fin 2)) recordGraph_swap
          (recordGraph (Fin 1)) recordGraph_restricts (hne.L2 i) (hne.L1 i) y)]
      unfold blockGraphLaw
      rw [expect_tensor_eq_sum]
      rfl
    rw [htwo, hdiag]
    have h := wKer_block_lower D pr hne.L2 (fun i => individualWeight (pr i) u)
      (fun i y => individualWeight_layerFlip (pr i) u y) hg hB hX hXb hbp hLs hgp hlow hup
      ((F ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D)
    have hn : Recentering.nrm μ ((F ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D) ^ 2 =
        μ.expect (fun ξ => ((F ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D) ξ *
          ((F ∘ slotRows (ZMod 6) φ) ∘ blockHalfRows pr D) ξ) := by
      unfold Recentering.nrm Recentering.ip
      exact Real.sq_sqrt (μ.expect_nonneg fun ξ => mul_self_nonneg _)
    rw [hn] at h
    linarith

end Caps

/-! ## The per-prime and per-piece certificates -/

/-- **The per-prime chamber cap of the positive root** (`prop:root-chamber` at one prime):
`-g p^{-1/2} ⪯ T_u ⪯ 1 + B/p` for the cut operator `T_u` of `Γ_{p,u}` at `ϑ₀` in the fixed half
chart `L²(μ_p)`, `μ_p = λ_p(G_F)` (the paper's `g = g^u_{20}`, `B = c^{+,u}_{20}`). -/
def IndRootChamberCap (u : ℚ) (g B : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (f : ((recordData (Fin 2)).cut.Half → ZMod p) → ℝ),
    -(g * (√(p : ℝ))⁻¹) * Recentering.nrm ((recordData (Fin 2)).halfLaw hne) f ^ 2 ≤
        kernelForm ((recordData (Fin 2)).halfLaw hne) ((recordData (Fin 2)).halfLaw hne)
          (wKer (recordData (Fin 2)) hne (individualWeight p u)) f f ∧
      kernelForm ((recordData (Fin 2)).halfLaw hne) ((recordData (Fin 2)).halfLaw hne)
          (wKer (recordData (Fin 2)) hne (individualWeight p u)) f f ≤
        (1 + B / p) * Recentering.nrm ((recordData (Fin 2)).halfLaw hne) f ^ 2

/-- **The per-prime layer cap of the positive root** (`prop:root-layer` at one prime):
`-g p^{-1/2} ⪯ T^ι_u ⪯ 1 + B/p` for the cut operator of `Γ_{p,u}` at the layer cut, in the chart
of the untilted one-layer root `λ_p(G_{L,1})` (the half law of L21). -/
def IndRootLayerCap (u : ℚ) (g B : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (f : (recordLayer.cut.Half → ZMod p) → ℝ),
    -(g * (√(p : ℝ))⁻¹) * Recentering.nrm (recordLayer.halfLaw hne) f ^ 2 ≤
        kernelForm (recordLayer.halfLaw hne) (recordLayer.halfLaw hne)
          (wKer recordLayer hne (individualWeight p u)) f f ∧
      kernelForm (recordLayer.halfLaw hne) (recordLayer.halfLaw hne)
          (wKer recordLayer hne (individualWeight p u)) f f ≤
        (1 + B / p) * Recentering.nrm (recordLayer.halfLaw hne) f ^ 2

/-- A per-piece certificate for a cut: constants `(g, B)` with `g X_i^{-1/2} < 1` and block cap
`g e^{B·570/(X_i log X_i)}` at most `d`, and the per-prime statement `C g B p` at every
class-three prime of the piece. -/
def PieceCert (i : Fin 33) (d : ℝ) (C : ℝ → ℝ → (p : ℕ) → [Fact p.Prime] → Prop) : Prop :=
  ∃ g B : ℝ, 0 ≤ g ∧ 0 ≤ B ∧ g * (√(pieceStart i : ℝ))⁻¹ < 1 ∧
    g * Real.exp (B * 570 / ((pieceStart i : ℝ) * Real.log (pieceStart i))) ≤ d ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i → C g B p

/-- **The positive-root certificate of an individual piece** (`cert:positive-root-caps`): the
chamber cut at the block cap `capVal i 0` (L20) and the layer cut at `capK i L` (L21).
*Hypothesis* (per prime, with per-piece constants). -/
def MiddleIndividualRootCert (i : Fin 33) (u : ℚ) : Prop :=
  PieceCert i (capVal i 0) (fun g B p _ => IndRootChamberCap u g B p) ∧
    PieceCert i (capK i .L) (fun g B p _ => IndRootLayerCap u g B p)

/-- **B6's positive-root block fields from the certificate** (`MiddleIndividualRoot`). -/
theorem middleIndividualRoot_of_cert {i : Fin 33} {u : ℚ} (hc : MiddleIndividualRootCert i u) :
    MiddleIndividualRoot i u := by
  intro ι _ _ pr _ b _hinj h3 hpc hbud hb hb' hne
  obtain ⟨⟨g, B, hg, hB, hgX, hd, hp⟩, ⟨g', B', hg', hB', hgX', hd', hp'⟩⟩ := hc
  have hX : (1 : ℝ) < pieceStart i := lt_trans (by norm_num) (pieceStart_gt_36 i)
  have hXp : ∀ k, (pieceStart i : ℝ) ≤ pr k := fun k => by exact_mod_cast (hpc k).1
  have hXb : (pieceStart i : ℝ) ≤ b := by
    obtain ⟨j₀, hj₀⟩ := hb'
    rw [← hj₀]
    exact hXp j₀
  have hLs : ∑ k, Real.log (pr k) ≤ 570 := middleBudget_real ▸ hbud
  have hgp : ∀ {g : ℝ}, 0 ≤ g → g * (√(pieceStart i : ℝ))⁻¹ < 1 →
      ∀ k, g * (√(pr k : ℝ))⁻¹ < 1 := fun hg hgX k =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (hXp k))) hg) hgX
  have hbp : ∀ k, (b : ℝ) ≤ pr k := fun k => by exact_mod_cast hb k
  have hr : 0 ≤ (√(b : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [rpow_neg_half_eq]
  constructor
  · have hc := fun k => hp (pr k) (h3 k) (hpc k).1 (hpc k).2
    have h := rootEnvelope_individual_of_caps pr hne u hg hB hX hXb hbp hLs (hgp hg hgX)
      (fun k f => (hc k (hne.L2 k) f).1) (fun k f => (hc k (hne.L2 k) f).2)
    exact Reserved.below_mono_coeff (chamberCut 0) (fieldDatum
      (middleBlock_datumHyp₂_individual pr hne u)).compF0_positive
      (mul_le_mul_of_nonneg_right hd hr) h
  · have hc := fun k => hp' (pr k) (h3 k) (hpc k).1 (hpc k).2
    have h := individualRootLayerCap_of_caps pr hne u hg' hB' hX hXb hbp hLs (hgp hg' hgX')
      (fun k f => (hc k (hne.L2 k) f).1) (fun k f => (hc k (hne.L2 k) f).2)
    have hdiag := emit_positive (blockGraphLaw pr (recordGraph (Fin 1)) hne.L1)
      (midDiagEmission fun v : ZMod 6 => v) reservedCut (midDiagEmission_reserved _)
    exact Reserved.below_mono_coeff reservedCut hdiag (mul_le_mul_of_nonneg_right hd' hr) h

end Sarkozy.BlockInputs

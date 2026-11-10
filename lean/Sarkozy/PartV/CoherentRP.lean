module

public import Sarkozy.PartV.PositiveRootRP

@[expose] public section

/-!
# The coherent root under `𝒢₆`, and (R2) on the last middle piece

`paper/sections/20b_selected_refinements.tex`, `lem:imp:coherent39-law` (invariance of the
coherent law under the chamber reflections and the rotation); `lem:front12:reference`(iii) on
`[2⁴⁵, P₃)`.

* `Dictionary.Invariant`: for every `g ∈ 𝒢₆` the relabelled dictionary is a permutation of `𝒟`.
  For `𝒟₃₉` this is the first step of the proof of `lem:imp:coherent39-law` (the average over
  `eq:merge-local-I-20`); since `𝒟₃₉` is not entered, it is a hypothesis here.
* `coherentScore_g6`, `coherentRoot_weight_g6`, `objLaw_coherentRoot_inv`: the coherent score,
  root and block root of an invariant dictionary are `𝒢₆`-invariant.
* `middleBlock_datumHyp₂_coherent`, `middleBlockReference_coherent_familyPositive`: **(R2) at every
  cut of the family for the middle law on `[2⁴⁵, P₃)`**, with the rows, the root envelopes and
  the layer caps as hypotheses.

With `Sarkozy.PartV.ChamberCut` (uniform root, 26 pieces) and `Sarkozy.PartV.PositiveRootRP`
(individual squares, 6 pieces) this covers all 33 middle pieces.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings Sarkozy.FiveType

/-- **A `𝒢₆`-invariant dictionary**: for every `g ∈ 𝒢₆`, the relabelled dictionary
`{(g(D), c_D)}` is a permutation of `𝒟` (`lem:imp:coherent39-law`: the average over
`eq:merge-local-I-20` makes the signed dictionary invariant under the chamber reflections and the
rotation). -/
def Dictionary.Invariant (D : Dictionary) : Prop :=
  ∀ k : Fin 6, (D.map fun Sc => (Sc.1.image (g6Vert k), Sc.2)).Perm D

section Prime

variable (p : ℕ) [Fact p.Prime]

/-- One term of the coherent score. -/
noncomputable def coherentTerm (x : ZMod 6 × Fin 2 → ZMod p) (Sc : Finset (ZMod 6 × Fin 2) × ℚ) :
    ℝ :=
  (Sc.2 : ℝ) * ((∑ s : ZMod p, ∏ i ∈ Sc.1, (quadraticChar (ZMod p) (s - x i) : ℝ)) / p)

theorem coherentTerm_g6 (k : Fin 6) (x : ZMod 6 × Fin 2 → ZMod p)
    (Sc : Finset (ZMod 6 × Fin 2) × ℚ) :
    coherentTerm p (x ∘ g6Vert k) Sc = coherentTerm p x (Sc.1.image (g6Vert k), Sc.2) := by
  unfold coherentTerm
  congr 2
  refine sum_congr rfl fun s _ => ?_
  rw [prod_image]
  · rfl
  · intro a _ b _ hab
    exact (g6Vert k).injective hab

/-- **The coherent score of an invariant dictionary is `𝒢₆`-invariant.** -/
theorem coherentScore_g6 (D : Dictionary) (hD : D.Invariant) (k : Fin 6)
    (x : ZMod 6 × Fin 2 → ZMod p) : coherentScore p D (x ∘ g6Vert k) = coherentScore p D x := by
  have h1 : (D.map fun Sc => (Sc.2 : ℝ) *
      ((∑ s : ZMod p, ∏ i ∈ Sc.1, (quadraticChar (ZMod p) (s - (x ∘ g6Vert k) i) : ℝ)) / p)) =
      (D.map fun Sc => (Sc.1.image (g6Vert k), Sc.2)).map (coherentTerm p x) := by
    rw [List.map_map]
    exact List.map_congr_left fun Sc _ => coherentTerm_g6 p k x Sc
  unfold coherentScore
  rw [h1]
  congr 1
  exact ((hD k).map (coherentTerm p x)).sum_eq

theorem coherentRoot_weight_g6 (D : Dictionary) (hD : D.Invariant) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty) (k : Fin 6)
    (x : ZMod 6 × Fin 2 → ZMod p) :
    (coherentRoot p D u hη hne).weight (x ∘ g6Vert k) = (coherentRoot p D u hη hne).weight x := by
  change (graphLaw _ hne).weight (x ∘ g6Vert k) * coherentWeight p D u η (x ∘ g6Vert k) / _ =
    (graphLaw _ hne).weight x * coherentWeight p D u η x / _
  have hlam : (graphLaw (recordGraph (Fin 2)) hne).weight (x ∘ g6Vert k) =
      (graphLaw (recordGraph (Fin 2)) hne).weight x := by
    have hmem : x ∘ g6Vert k ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) ↔
        x ∈ injLabellings (ZMod p) (recordGraph (Fin 2)) :=
      mem_injLabellings_comp_iff _ (g6Vert k) (recordGraph_g6 (Fin 2) k) x
    simp only [graphLaw, hmem]
  rw [hlam]
  unfold coherentWeight
  rw [coherentScore_g6 p D hD]

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

theorem objLaw_coherentRoot_inv (D : Dictionary) (hD : D.Invariant) (u : ℚ) {η : ℚ}
    (hη : 0 < η) (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty)
    (k : Fin 6) (Ψ : ZMod 6 → Fin 2 → BlockLabel pr) :
    (objLaw (coherentBlockRoot pr D u hη hne)).weight (Ψ ∘ g6 k) =
      (objLaw (coherentBlockRoot pr D u hη hne)).weight Ψ := by
  rw [objLaw_weight, objLaw_weight]
  unfold coherentBlockRoot
  rw [tensor_weight, tensor_weight]
  refine prod_congr rfl fun i _ => ?_
  exact coherentRoot_weight_g6 (pr i) D hD u hη (hne i) k (fun v => Ψ v.1 v.2 i)

/-- **The datum hypotheses for the middle block laws with the coherent root** of an invariant
dictionary. -/
theorem middleBlock_datumHyp₂_coherent (hne : MiddleNonempty pr) (D : Dictionary)
    (hD : D.Invariant) (u : ℚ) {η : ℚ} (hη : 0 < η) :
    DatumHyp (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2) (coherentBlockRoot pr D u hη hne.L2) :=
  ⟨objLaw_match_exch pr hne.E2, objLaw_fold_supp pr hne.F2 hne.E2,
    objLaw_coherentRoot_inv pr D hD u hη hne.L2⟩

/-- **(R2) for the middle block law with the coherent root** (`lem:front12:reference`(iii) on
`[2⁴⁵, P₃)`), for a `𝒢₆`-invariant dictionary, with the rows, the root envelopes and the layer
caps as hypotheses. -/
theorem middleBlockReference_coherent_familyPositive (hne : MiddleNonempty pr) (D : Dictionary)
    (hD : D.Invariant) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf₂ : 0 ≤ I.f₂) (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds (fieldDatum (middleBlock_datumHyp₂_coherent pr hne D hD u hη))
      I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope (fieldDatum (middleBlock_datumHyp₂_coherent pr hne D hD u hη)) I.d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.d₁ r)
    (hcap : MiddleLayerCaps
      (middleBlockFieldLaws pr hne (coherentBlockRoot pr D u hη hne.L2)) I.k r) :
    TheoremC.FamilyReflectionPositive
      (signedIntegral
        (middleBlockReference pr hne (coherentBlockRoot pr D u hη hne.L2) W hr).weight) := by
  have hdom : ∀ t, I.k t * W.w t ≤ W.v t := hW.2.2.2.2.2.2.2.2
  refine middleReference_familyPositive _ W I.k hr hcap hdom fun a => ?_
  rw [middleReference_eq]
  exact (middleTilde_firstCut_positive
    (middleBlockFieldLaws pr hne (coherentBlockRoot pr D u hη hne.L2))
    (middleBlock_datumHyp₂_coherent pr hne D hD u hη) (middleBlock_datumHyp₁ pr hne) W I hr hW
    hf₂ hf₁ hrows₂ hrows₁ hroot₂ hroot₁ a).smul
    (inv_nonneg.mpr (le_trans zero_le_one (one_le_midPoly W hr)))

end Block

end Sarkozy.PartV

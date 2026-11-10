module

public import Sarkozy.PartVLaws.RowFrame

@[expose] public section

/-!
# `TailInputsValid P₄` reduced to the root envelopes, the correlations and the layer caps

`paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i);
`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`, items (F1), (F3)–(F5)(b).

The tail datum has four families of row data at each field type `𝔣'`: the two-layer rows of the
coordinates `0` and `1` (ordinary inputs) and the one-layer rows of the coordinates `0` and `1`
(reserved inputs). Each family is a row frame (`RowFrame`): its fold and matching laws are the
laws of the rows under `Inj_p(G_{F·})` and `Inj_p(G_{E·})`, and the two graphs have the same
edges off the row `2` and off the row `0` (`lem:upper-geometry`(d); `edge_agree_left`,
`edge_agree_right`). So, at every prime `p ≥ P₄`:

* **`tail_two0_schurInputs`**, **`tail_two1_schurInputs`**, **`tail_one0_schurInputs`**,
  **`tail_one1_schurInputs`**: the Schur inputs (`SchurInputs`) of each family follow from the
  correlation bounds (F4) (`CorrInputs`: the maximal correlation `ρ_F` of the fold kernel and
  `‖T_E^b - J‖ ≤ ρ_E`) and the two numerical conditions `f_Schur ≤ f`, `ρ_E/r ≤ h` with the
  counted constants `H = ρ^{144}`, `R_m = ρ^{288}`, `υ = ρ^{288} - 1`, `ρ = 1 + 2²⁸/√p`;
* **`tailInputsValid_of_corr`**: `TailInputsCorr P → TailInputsValid P` for `P ≥ P₄`, where
  `TailInputsCorr P` asks, at every prime `q ≥ P`, for (V1) the root envelopes, the correlations
  and numerical conditions of the four families, and (V3) the layer caps;
  `tailFamilyFrom_rpp_of_corr` is `Reference.rpp` in this form;
* `tailSchurF_le`, `tailSchurF_zero_le`: `f_Schur ≤ 2√p ρ_F + 2⁻¹⁰⁰`, so the numerical conditions
  are smallness conditions on `ρ_F`, `ρ_E` only, and hold at `ρ_F = ρ_E = 0` (non-vacuity).

So `lem:tail-law`(i) is partly proved here: its count-type inputs are proved, and its spectral
inputs (V1), (F4), (V3) are the hypotheses `TailInputsCorr`.

The mass, marginal and deviation fields of (F3) and (F1), `H ≤ 50`, `H + 1/50 ≤ M` and the exact
matching marginals are proved, not assumed.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

/-- **The correlation inputs (F4) of a row datum**: at every middle value, the maximal
correlation of the fold kernel is at most `ρ_F`, and `‖T_E^b - J‖ ≤ ρ_E`. -/
def CorrInputs {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛) (ρF ρE : ℝ) : Prop :=
  ∀ b, D.nu.weight b ≠ 0 →
    (∀ g g' : 𝔛 → ℝ, |kf (D.nub b) (covKernel (D.nub b) (D.TF b)) g g'| ≤
      ρF * Real.sqrt (wvar (D.nub b) (margL (D.nub b) (D.TF b)) g) *
        Real.sqrt (wvar (D.nub b) (margR (D.nub b) (D.TF b)) g')) ∧
    NormBound (D.nub b) (D.TE b) ρE

/-- The Schur coefficient `f_Schur = (H R_m ρ_F + (H + 50H²)υ²)/r` with the counted constants. -/
noncomputable def tailSchurF (p : ℕ) (ρF : ℝ) : ℝ :=
  (countRho p ^ 144 * countRho p ^ 288 * ρF +
    (countRho p ^ 144 + 50 * (countRho p ^ 144) ^ 2) * (countRho p ^ 288 - 1) ^ 2) / tailR p

section Frame

variable {p : ℕ} [Fact p.Prime] {W V Q : Type} [Fintype W] [DecidableEq W] [Fintype Q]
  [DecidableEq Q]

/-- **The Schur inputs of a row frame from its correlations** (generic form). -/
theorem frame_schurInputs (hW : WeilBound (ZMod p)) (hp : P4 ≤ p) (hW72 : Fintype.card W ≤ 72)
    (G1 G2 : OrientedGraph W) (hne1 : (injLabellings (ZMod p) G1).Nonempty)
    (hne2 : (injLabellings (ZMod p) G2).Nonempty) (hdeg1 : ∀ v, nbrCount G1 univ v ≤ 20)
    (hdeg2 : ∀ v, nbrCount G2 univ v ≤ 20) (e : Fin 3 × V ≃ W) (c : Q ≃ V)
    (HE : FrameEdges G1 G2 e) (πE πF : FiniteLaw (Fin 3 → Q → ZMod p))
    (hπE : πE = (graphLaw G2 hne2).map (rowRead e c))
    (hπF : πF = (graphLaw G1 hne1).map (rowRead e c)) (piL : FiniteLaw (ZMod 6 → Q → ZMod p))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Q → ZMod p), πE.weight (ω ∘ σ) = πE.weight ω)
    (hS : GamSupported πE πF)
    (hL : ∀ (k : Fin 6) (Ψ : ZMod 6 → Q → ZMod p), piL.weight (Ψ ∘ g6 k) = piL.weight Ψ)
    {ρF ρE : ℝ} (hρF : 0 ≤ ρF) {I : CompletionInput} (hM : (I.M : ℝ) = 21 / 20)
    (hcorr : CorrInputs (datumOfGam πE πF piL hexch hS hL) ρF ρE)
    (hf : tailSchurF p ρF ≤ (I.f : ℝ)) (hh : ρE / tailR p ≤ (I.h : ℝ)) :
    SchurInputs (datumOfGam πE πF piL hexch hS hL) (tailR p) I :=
  schurInputs_of_rowData _ hM (one_le_pow₀ (one_le_countRho p))
    (countRho_pow_le p hp (n := 144) (by norm_num))
    (le_trans zero_le_one (one_le_pow₀ (one_le_countRho p))) hρF hf hh fun b hb =>
      frame_schurRowData hW hp hW72 G1 G2 hne1 hne2 hdeg1 hdeg2 e c HE πE πF hπE hπF hS hexch hb
        (hcorr b hb).1 (hcorr b hb).2

end Frame

/-! ## The four row families of the tail datum -/

section Families

/-- The row coordinates of the two-layer rows. -/
def cTwo (f' : FieldTy) : f'.Obj × ZMod 2 ≃ (toFType f').Obj × Fin 2 where
  toFun q := (objCast f' q.1, layerFin q.2)
  invFun v := (objUncast f' v.1, layerUn v.2)
  left_inv q := by
    obtain ⟨o, l⟩ := q
    simp only [objUncast_objCast, layerUn_layerFin]
  right_inv v := by
    obtain ⟨o, l⟩ := v
    simp only [objCast_objUncast, layerFin_layerUn]

/-- The row coordinates of the one-layer rows. -/
def cOne (f' : FieldTy) : f'.Obj × Unit ≃ (toFType f').Obj × Fin 1 where
  toFun q := (objCast f' q.1, 0)
  invFun v := (objUncast f' v.1, ())
  left_inv q := by
    obtain ⟨o, u⟩ := q
    simp only [objUncast_objCast]
  right_inv v := by
    obtain ⟨o, l⟩ := v
    simp only [objCast_objUncast, Prod.mk.injEq, true_and]
    exact (Fin.fin_one_eq_zero l).symm

/-- The rows of the coordinate `1`: `Fin 3 × (O × L) ≃ O × Fin 3 × L`. -/
def eRow1 (O L : Type) : Fin 3 × (O × L) ≃ O × Fin 3 × L where
  toFun x := (x.2.1, x.1, x.2.2)
  invFun w := (w.2.1, (w.1, w.2.2))
  left_inv _ := rfl
  right_inv _ := rfl

/-- The fold and matching graphs of the coordinate `0` have the same edges off the rows `2`
and `0`. -/
theorem frameEdges_row0 (f' : FieldTy) (L : Type) [Fintype L] :
    FrameEdges (W := Fin 3 × (toFType f').Obj × L) (fieldGraph .F (toFType f') L)
      (fieldGraph .E (toFType f') L) (Equiv.refl _) := by
  constructor
  · intro a b ha hb
    rw [fieldGraph, fieldGraph, mem_twoLayerGraph, mem_twoLayerGraph]
    have := edge_agree_left (toFType f').rel (j := Fin.last 2) (by decide) a b ha hb
    change twoLayerEdge typeF _ a b = true ↔ twoLayerEdge typeE _ a b = true
    rw [this]
  · intro a b ha hb
    rw [fieldGraph, fieldGraph, mem_twoLayerGraph, mem_twoLayerGraph]
    have := edge_agree_left (toFType f').rel (j := 0) (by decide) a b ha hb
    change twoLayerEdge typeF _ a b = true ↔ twoLayerEdge typeE _ a b = true
    rw [this]

/-- The same for the coordinate `1`. -/
theorem frameEdges_row1 (f' : FieldTy) (L : Type) [Fintype L] :
    FrameEdges (W := (toFType f').Obj × Fin 3 × L) (fieldGraph (toFType f') .F L)
      (fieldGraph (toFType f') .E L) (eRow1 _ _) := by
  constructor
  · intro a b ha hb
    rw [fieldGraph, fieldGraph, mem_twoLayerGraph, mem_twoLayerGraph]
    have := edge_agree_right (toFType f').rel (j := Fin.last 2) (by decide) a b ha hb
    change twoLayerEdge _ typeF a b = true ↔ twoLayerEdge _ typeE a b = true
    rw [this]
  · intro a b ha hb
    rw [fieldGraph, fieldGraph, mem_twoLayerGraph, mem_twoLayerGraph]
    have := edge_agree_right (toFType f').rel (j := 0) (by decide) a b ha hb
    change twoLayerEdge _ typeF a b = true ↔ twoLayerEdge _ typeE a b = true
    rw [this]

theorem card_vertices_le (f' : FieldTy) (L : Type) [Fintype L] (hL : Fintype.card L ≤ 2) :
    Fintype.card (Fin 3 × (toFType f').Obj × L) ≤ 72 ∧
      Fintype.card ((toFType f').Obj × Fin 3 × L) ≤ 72 := by
  have h6 := card_obj_le (toFType f')
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_prod, Fintype.card_prod,
    Fintype.card_fin]
  constructor <;> nlinarith

theorem tailOrd_M (f' : FieldTy) : ((tailOrd f').M : ℝ) = 21 / 20 := by
  cases f' <;> norm_num [tailOrd, tailOrdinary, toFType]

theorem tailRes_M (f' : FieldTy) : ((tailRes f').M : ℝ) = 21 / 20 := by
  cases f' <;> norm_num [tailRes, tailReserved, toFType]

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f' : FieldTy)

/-- The laws of the two-layer rows of the coordinate `0`. -/
theorem two0F_eq : (lam2 (tailFieldLaws p hne) .F f').map
      (fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) =
    (graphLaw (fieldGraph .F (toFType f') (Fin 2)) (hne.two .F (toFType f'))).map
      (rowRead (W := Fin 3 × (toFType f').Obj × Fin 2) (Equiv.refl _) (cTwo f')) := by
  unfold lam2
  rw [map_map']
  rfl

theorem two0E_eq : (lam2 (tailFieldLaws p hne) .E f').map
      (fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) =
    (graphLaw (fieldGraph .E (toFType f') (Fin 2)) (hne.two .E (toFType f'))).map
      (rowRead (W := Fin 3 × (toFType f').Obj × Fin 2) (Equiv.refl _) (cTwo f')) := by
  unfold lam2
  rw [map_map']
  rfl

/-- The laws of the two-layer rows of the coordinate `1`. -/
theorem two1F_eq : (lam2 (tailFieldLaws p hne) f' .F).map
      (fun y => (rows1 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) =
    (graphLaw (W := (toFType f').Obj × Fin 3 × Fin 2) (fieldGraph (toFType f') .F (Fin 2))
      (hne.two (toFType f') .F)).map
      (rowRead (eRow1 (toFType f').Obj (Fin 2)) (cTwo f')) := by
  unfold lam2
  rw [map_map']
  rfl

theorem two1E_eq : (lam2 (tailFieldLaws p hne) f' .E).map
      (fun y => (rows1 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) =
    (graphLaw (W := (toFType f').Obj × Fin 3 × Fin 2) (fieldGraph (toFType f') .E (Fin 2))
      (hne.two (toFType f') .E)).map
      (rowRead (eRow1 (toFType f').Obj (Fin 2)) (cTwo f')) := by
  unfold lam2
  rw [map_map']
  rfl

/-- The laws of the one-layer rows of the coordinate `0`. -/
theorem one0F_eq : (lam1 (tailFieldLaws p hne) .F f').map
      (fun y => (rows0 y : Fin 3 → f'.Obj × Unit → ZMod p)) =
    (graphLaw (fieldGraph .F (toFType f') (Fin 1)) (hne.one .F (toFType f'))).map
      (rowRead (W := Fin 3 × (toFType f').Obj × Fin 1) (Equiv.refl _) (cOne f')) := by
  unfold lam1
  rw [map_map']
  rfl

theorem one0E_eq : (lam1 (tailFieldLaws p hne) .E f').map
      (fun y => (rows0 y : Fin 3 → f'.Obj × Unit → ZMod p)) =
    (graphLaw (fieldGraph .E (toFType f') (Fin 1)) (hne.one .E (toFType f'))).map
      (rowRead (W := Fin 3 × (toFType f').Obj × Fin 1) (Equiv.refl _) (cOne f')) := by
  unfold lam1
  rw [map_map']
  rfl

/-- The laws of the one-layer rows of the coordinate `1`. -/
theorem one1F_eq : (lam1 (tailFieldLaws p hne) f' .F).map
      (fun y => (rows1 y : Fin 3 → f'.Obj × Unit → ZMod p)) =
    (graphLaw (W := (toFType f').Obj × Fin 3 × Fin 1) (fieldGraph (toFType f') .F (Fin 1))
      (hne.one (toFType f') .F)).map
      (rowRead (eRow1 (toFType f').Obj (Fin 1)) (cOne f')) := by
  unfold lam1
  rw [map_map']
  rfl

theorem one1E_eq : (lam1 (tailFieldLaws p hne) f' .E).map
      (fun y => (rows1 y : Fin 3 → f'.Obj × Unit → ZMod p)) =
    (graphLaw (W := (toFType f').Obj × Fin 3 × Fin 1) (fieldGraph (toFType f') .E (Fin 1))
      (hne.one (toFType f') .E)).map
      (rowRead (eRow1 (toFType f').Obj (Fin 1)) (cOne f')) := by
  unfold lam1
  rw [map_map']
  rfl

/-- **The Schur inputs of the two-layer rows of the coordinate `0` from their correlations.** -/
theorem tail_two0_schurInputs (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') {ρF ρE : ℝ} (hρF : 0 ≤ ρF)
    (hcorr : CorrInputs (rowD0 (lam2 (tailFieldLaws p hne)) f' h) ρF ρE)
    (hf : tailSchurF p ρF ≤ ((tailOrd f').f : ℝ)) (hh : ρE / tailR p ≤ ((tailOrd f').h : ℝ)) :
    SchurInputs (rowD0 (lam2 (tailFieldLaws p hne)) f' h) (tailR p) (tailOrd f') :=
  frame_schurInputs hW hp (card_vertices_le f' (Fin 2) (by simp)).1
    (fieldGraph .F (toFType f') (Fin 2)) (fieldGraph .E (toFType f') (Fin 2))
    (hne.two .F (toFType f')) (hne.two .E (toFType f')) (fieldGraph_degree_two .F (toFType f'))
    (fieldGraph_degree_two .E (toFType f'))
    _ (cTwo f') (frameEdges_row0 f' _)
    _ _ (two0E_eq p hne f') (two0F_eq p hne f') _ h.exch h.supp h.root hρF (tailOrd_M f') hcorr
    hf hh

/-- **The Schur inputs of the two-layer rows of the coordinate `1` from their correlations.** -/
theorem tail_two1_schurInputs (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp1 (lam2 (tailFieldLaws p hne)) f') {ρF ρE : ℝ} (hρF : 0 ≤ ρF)
    (hcorr : CorrInputs (rowD1 (lam2 (tailFieldLaws p hne)) f' h) ρF ρE)
    (hf : tailSchurF p ρF ≤ ((tailOrd f').f : ℝ)) (hh : ρE / tailR p ≤ ((tailOrd f').h : ℝ)) :
    SchurInputs (rowD1 (lam2 (tailFieldLaws p hne)) f' h) (tailR p) (tailOrd f') :=
  frame_schurInputs hW hp (card_vertices_le f' (Fin 2) (by simp)).2
    (fieldGraph (toFType f') .F (Fin 2)) (fieldGraph (toFType f') .E (Fin 2))
    (hne.two (toFType f') .F) (hne.two (toFType f') .E) (fieldGraph_degree_two (toFType f') .F)
    (fieldGraph_degree_two (toFType f') .E)
    _ (cTwo f') (frameEdges_row1 f' _)
    _ _ (two1E_eq p hne f') (two1F_eq p hne f') _ h.exch h.supp h.root hρF (tailOrd_M f') hcorr
    hf hh

/-- **The Schur inputs of the one-layer rows of the coordinate `0` from their correlations.** -/
theorem tail_one0_schurInputs (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam1 (tailFieldLaws p hne)) f') {ρF ρE : ℝ} (hρF : 0 ≤ ρF)
    (hcorr : CorrInputs (rowD0 (lam1 (tailFieldLaws p hne)) f' h) ρF ρE)
    (hf : tailSchurF p ρF ≤ ((tailRes f').f : ℝ)) (hh : ρE / tailR p ≤ ((tailRes f').h : ℝ)) :
    SchurInputs (rowD0 (lam1 (tailFieldLaws p hne)) f' h) (tailR p) (tailRes f') :=
  frame_schurInputs hW hp (card_vertices_le f' (Fin 1) (by simp)).1
    (fieldGraph .F (toFType f') (Fin 1)) (fieldGraph .E (toFType f') (Fin 1))
    (hne.one .F (toFType f')) (hne.one .E (toFType f')) (fieldGraph_degree_one .F (toFType f'))
    (fieldGraph_degree_one .E (toFType f'))
    _ (cOne f') (frameEdges_row0 f' _)
    _ _ (one0E_eq p hne f') (one0F_eq p hne f') _ h.exch h.supp h.root hρF (tailRes_M f') hcorr
    hf hh

/-- **The Schur inputs of the one-layer rows of the coordinate `1` from their correlations.** -/
theorem tail_one1_schurInputs (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp1 (lam1 (tailFieldLaws p hne)) f') {ρF ρE : ℝ} (hρF : 0 ≤ ρF)
    (hcorr : CorrInputs (rowD1 (lam1 (tailFieldLaws p hne)) f' h) ρF ρE)
    (hf : tailSchurF p ρF ≤ ((tailRes f').f : ℝ)) (hh : ρE / tailR p ≤ ((tailRes f').h : ℝ)) :
    SchurInputs (rowD1 (lam1 (tailFieldLaws p hne)) f' h) (tailR p) (tailRes f') :=
  frame_schurInputs hW hp (card_vertices_le f' (Fin 1) (by simp)).2
    (fieldGraph (toFType f') .F (Fin 1)) (fieldGraph (toFType f') .E (Fin 1))
    (hne.one (toFType f') .F) (hne.one (toFType f') .E) (fieldGraph_degree_one (toFType f') .F)
    (fieldGraph_degree_one (toFType f') .E)
    _ (cOne f') (frameEdges_row1 f' _)
    _ _ (one1E_eq p hne f') (one1F_eq p hne f') _ h.exch h.supp h.root hρF (tailRes_M f') hcorr
    hf hh

end Families

/-! ## The tail inputs reduced to the correlations -/

/-- **The correlation form of the Schur inputs of a row datum**: correlation constants `ρ_F ≥ 0`,
`ρ_E` with (F4) and the numerical conditions `f_Schur ≤ f`, `ρ_E/r ≤ h` of (F5)(b). -/
def CorrSchur {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (p : ℕ) (D : Datum 𝔛)
    (I : CompletionInput) : Prop :=
  ∃ ρF ρE : ℝ, 0 ≤ ρF ∧ CorrInputs D ρF ρE ∧ tailSchurF p ρF ≤ (I.f : ℝ) ∧
    ρE / tailR p ≤ (I.h : ℝ)

/-- **The tail inputs in correlation form at every tail prime `q ≥ P`**: (V1) the root
envelopes, the correlation form (F4) of the Schur inputs of the four row families, and (V3) the
layer caps of the nine field laws. Compared with `TailInputsSchur`, the mass, marginal and
deviation fields of the Schur rows, `H ≤ 50` and `H + 1/50 ≤ M` are no longer assumed. -/
def TailInputsCorr (P : ℕ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
    (hp : (2 : ℝ) ^ 20 ≤ q),
    (∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f').d (tailR q)) ∧
    (∀ f', RootEnv (rowD1 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailOrd f').d (tailR q)) ∧
    (∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f').d (tailR q)) ∧
    (∀ f', RootEnv (rowD1 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailRes f').d (tailR q)) ∧
    (∀ f', CorrSchur q (rowD0 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f')) ∧
    (∀ f', CorrSchur q (rowD1 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailOrd f')) ∧
    (∀ f', CorrSchur q (rowD0 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f')) ∧
    (∀ f', CorrSchur q (rowD1 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailRes f')) ∧
    FieldLayerCaps (tailFieldLaws q hne) tailKappa (tailR q)

/-- **The correlation form gives the Schur form of the tail inputs** at the primes `q ≥ P ≥ P₄`. -/
theorem tailInputsSchur_of_corr {P : ℕ} (hP : P4 ≤ P) (h : TailInputsCorr P) :
    TailInputsSchur P := by
  intro q _ hq hne hW hp
  obtain ⟨r20, r21, r10, r11, c20, c21, c10, c11, hcaps⟩ := h q hq hne hW hp
  have hq4 : P4 ≤ q := hP.trans hq
  refine ⟨r20, r21, r10, r11, fun f' => ?_, fun f' => ?_, fun f' => ?_, fun f' => ?_, hcaps⟩
  · obtain ⟨ρF, ρE, hρF, hc, hf, hh⟩ := c20 f'
    exact tail_two0_schurInputs q hne f' hW hq4 _ hρF hc hf hh
  · obtain ⟨ρF, ρE, hρF, hc, hf, hh⟩ := c21 f'
    exact tail_two1_schurInputs q hne f' hW hq4 _ hρF hc hf hh
  · obtain ⟨ρF, ρE, hρF, hc, hf, hh⟩ := c10 f'
    exact tail_one0_schurInputs q hne f' hW hq4 _ hρF hc hf hh
  · obtain ⟨ρF, ρE, hρF, hc, hf, hh⟩ := c11 f'
    exact tail_one1_schurInputs q hne f' hW hq4 _ hρF hc hf hh

/-- **`TailInputsValid` from the correlation form** (the hypothesis `hV` of `tailFamilyFrom_rpp`,
`tailReference`): for `P ≥ P₄`, the root envelopes, the correlations (F4) with the numerical
conditions of (F5)(b), and the layer caps at the primes `q ≥ P` give `TailInputsValid P`. -/
theorem tailInputsValid_of_corr {P : ℕ} (hP : P4 ≤ P) (h : TailInputsCorr P) :
    TailInputsValid P :=
  tailInputsValid_of_schur (tailInputsSchur_of_corr hP h)

/-! ## The numerical condition is a smallness condition on `ρ_F` -/

theorem tailR_eq_inv_sqrt (p : ℕ) : tailR p = (Real.sqrt p)⁻¹ := by
  unfold tailR
  rw [Real.rpow_neg (Nat.cast_nonneg _), ← Real.sqrt_eq_rpow]

/-- The arithmetic of `tailSchurF_le`, with `H = ρ^{144}`, `R = ρ^{288}`, `s = √p`. -/
theorem schurF_arith {H R s ρF : ℝ} (hH : H ≤ 1 + 1 / 2 ^ 200) (hH1 : 1 ≤ H)
    (hR : R ≤ 1 + 1 / 2 ^ 200) (hR1 : 1 ≤ R) (hs : 2 ^ 256 ≤ s) (hυ' : R - 1 ≤ 576 * (2 ^ 28 / s))
    (hρF : 0 ≤ ρF) :
    (H * R * ρF + (H + 50 * H ^ 2) * (R - 1) ^ 2) * s ≤ 2 * s * ρF + 1 / 2 ^ 100 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hυ0 : 0 ≤ R - 1 := by linarith
  have h1 : H * R ≤ 2 := by
    calc H * R ≤ (1 + 1 / 2 ^ 200) * (1 + 1 / 2 ^ 200) :=
          mul_le_mul hH hR (by linarith) (by positivity)
      _ ≤ 2 := by norm_num
  have h2 : H + 50 * H ^ 2 ≤ 202 := by
    have hHsq : H ^ 2 ≤ (1 + 1 / 2 ^ 200) ^ 2 := pow_le_pow_left₀ (by linarith) hH 2
    have : (1 : ℝ) + 1 / 2 ^ 200 + 50 * (1 + 1 / 2 ^ 200) ^ 2 ≤ 202 := by norm_num
    linarith
  have h3 : (R - 1) ^ 2 * s ≤ (576 * 2 ^ 28) ^ 2 / s := by
    have hsq : (R - 1) ^ 2 ≤ (576 * (2 ^ 28 / s)) ^ 2 := pow_le_pow_left₀ hυ0 hυ' 2
    calc (R - 1) ^ 2 * s ≤ (576 * (2 ^ 28 / s)) ^ 2 * s := mul_le_mul_of_nonneg_right hsq hs0.le
      _ = (576 * 2 ^ 28) ^ 2 / s := by field_simp
  have h4 : (576 * 2 ^ 28 : ℝ) ^ 2 / s ≤ 1 / 2 ^ 100 / 202 := by
    rw [div_le_iff₀ hs0]
    have : (576 * 2 ^ 28 : ℝ) ^ 2 ≤ 1 / 2 ^ 100 / 202 * 2 ^ 256 := by norm_num
    have h5 : 1 / 2 ^ 100 / 202 * 2 ^ 256 ≤ 1 / 2 ^ 100 / 202 * s :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    linarith
  have e1 : H * R * ρF * s ≤ 2 * s * ρF := by
    calc H * R * ρF * s = (H * R) * (ρF * s) := by ring
      _ ≤ 2 * (ρF * s) := mul_le_mul_of_nonneg_right h1 (mul_nonneg hρF hs0.le)
      _ = 2 * s * ρF := by ring
  have e2 : (H + 50 * H ^ 2) * (R - 1) ^ 2 * s ≤ 1 / 2 ^ 100 := by
    have hυs : 0 ≤ (R - 1) ^ 2 * s := mul_nonneg (sq_nonneg _) hs0.le
    calc (H + 50 * H ^ 2) * (R - 1) ^ 2 * s = (H + 50 * H ^ 2) * ((R - 1) ^ 2 * s) := by ring
      _ ≤ 202 * ((R - 1) ^ 2 * s) := mul_le_mul_of_nonneg_right h2 hυs
      _ ≤ 202 * (1 / 2 ^ 100 / 202) := by linarith
      _ = 1 / 2 ^ 100 := by norm_num
  have e3 : (H * R * ρF + (H + 50 * H ^ 2) * (R - 1) ^ 2) * s =
      H * R * ρF * s + (H + 50 * H ^ 2) * (R - 1) ^ 2 * s := by ring
  rw [e3]
  linarith

/-- **`f_Schur ≤ 2√p ρ_F + 2⁻¹⁰⁰`** at every prime `p ≥ P₄`: the condition `f_Schur ≤ f` of
`CorrSchur` holds as soon as `ρ_F ≤ (f - 2⁻¹⁰⁰)/(2√p)`; in particular it holds with `ρ_F = 0`
(non-vacuity of the numerical part of `TailInputsCorr`). -/
theorem tailSchurF_le (p : ℕ) [Fact p.Prime] (hp : P4 ≤ p) {ρF : ℝ} (hρF : 0 ≤ ρF) :
    tailSchurF p ρF ≤ 2 * Real.sqrt p * ρF + 1 / 2 ^ 100 := by
  have hs := sqrt_ge_of_P4 p hp
  rw [ZMod.card] at hs
  have hH := countRho_pow_le p hp (n := 144) (by norm_num)
  have hR := countRho_pow_le p hp (n := 288) (by norm_num)
  have hH1 : 1 ≤ countRho p ^ 144 := one_le_pow₀ (one_le_countRho p)
  have hR1 : 1 ≤ countRho p ^ 288 := one_le_pow₀ (one_le_countRho p)
  clear hp
  have hs0 : 0 < Real.sqrt (p : ℝ) := lt_of_lt_of_le (by positivity) hs
  have hε : (0 : ℝ) ≤ 2 ^ 28 / Real.sqrt p := div_nonneg (by positivity) hs0.le
  have hnε : ((288 : ℕ) : ℝ) * (2 ^ 28 / Real.sqrt p) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hs0]
    have : ((288 : ℕ) : ℝ) * 2 ^ 28 ≤ 1 / 2 * 2 ^ 256 := by norm_num
    linarith
  have hυ := one_add_pow_le hε 288 hnε
  have hυ' : countRho p ^ 288 - 1 ≤ 576 * (2 ^ 28 / Real.sqrt p) := by
    rw [sub_le_iff_le_add']
    refine le_trans hυ (le_of_eq ?_)
    push_cast
    ring
  unfold tailSchurF
  rw [tailR_eq_inv_sqrt, div_inv_eq_mul]
  exact schurF_arith hH hH1 hR hR1 hs hυ' hρF

/-- **The numerical part of `CorrSchur` is satisfiable** (non-vacuity): at every prime `p ≥ P₄`,
`ρ_F = ρ_E = 0` satisfy `f_Schur ≤ f` and `ρ_E/r ≤ h` for every ordinary and reserved input of
the tail datum. -/
theorem tailSchurF_zero_le (p : ℕ) [Fact p.Prime] (hp : P4 ≤ p) (f' : FieldTy) :
    tailSchurF p 0 ≤ ((tailOrd f').f : ℝ) ∧ tailSchurF p 0 ≤ ((tailRes f').f : ℝ) ∧
      (0 : ℝ) / tailR p ≤ ((tailOrd f').h : ℝ) ∧ (0 : ℝ) / tailR p ≤ ((tailRes f').h : ℝ) := by
  have h0 := tailSchurF_le p hp (le_refl (0 : ℝ))
  rw [mul_zero, zero_add] at h0
  have hsmall : (1 : ℝ) / 2 ^ 100 ≤ 1 := by norm_num
  have hf1 : (1 : ℝ) ≤ ((tailOrd f').f : ℝ) ∧ (1 : ℝ) ≤ ((tailRes f').f : ℝ) := by
    cases f' <;> norm_num [tailOrd, tailRes, tailOrdinary, tailReserved, toFType]
  have hh0 : (0 : ℝ) ≤ ((tailOrd f').h : ℝ) ∧ (0 : ℝ) ≤ ((tailRes f').h : ℝ) := by
    cases f' <;> norm_num [tailOrd, tailRes, tailOrdinary, tailReserved, toFType]
  rw [zero_div]
  exact ⟨by linarith [hf1.1], by linarith [hf1.2], hh0.1, hh0.2⟩

/-- **`Reference.rpp` from the correlation form of the tail inputs** (`tailFamilyFrom_rpp` with
`tailInputsValid_of_corr`). -/
theorem tailFamilyFrom_rpp_of_corr (hW : Target.Weil) {P : ℕ} (hP : P4 ≤ P)
    (hC : TailInputsCorr P) (q : ℕ) [NeZero q] (hq : q.Prime) :
    TheoremC.FamilyReflectionPositive (signedIntegral (tailFamilyFrom P q).weight) :=
  tailFamilyFrom_rpp hW hP (tailInputsValid_of_corr hP hC) q hq

end Sarkozy.PartVLaws

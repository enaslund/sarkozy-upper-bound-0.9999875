module

public import Sarkozy.TailCorr.Uniform

@[expose] public section

/-!
# The matching rows of the field type `E` of the tail datum: (F4) proved

`paper/sections/25_upper_reference.tex`, `it:record:upper-F4` and `subsec:row-anova-correlation`
(the matching correlation `ρ_E`), for the rows at `𝔣' = E`;
`paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i).

The matching graph of the rows at the field type `E` is `G_{EE}` (in both coordinates and for
both layer counts). It has no edges (`fieldGraph_EE_noEdge`): `E` relates distinct objects but has
no forward pair. So its law is uniform on the injective labellings, and the law of its three rows
is uniform on the jointly injective row configurations (`edgeless_rows_weight`). By
`uniform_normBound_sqrt`, `‖T_E^b - J‖ ≤ q^{-1/2} = 1·r` at every middle value, and `1` is the
recorded `h` of both the ordinary and the reserved `E` input. So:

* **`matchE_two0`**, **`matchE_two1`**, **`matchE_one0`**, **`matchE_one1`**: the matching half
  of (F4) at `𝔣' = E` for the four row families, at every prime `q ≥ 2²⁰` (no Weil bound is used:
  the bound is a count of injective labellings).
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws

/-! ## Laws of graphs without edges -/

section Edgeless

variable {W V Q : Type} [Fintype W] [DecidableEq W] [Fintype Q] [DecidableEq Q]
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The labelling of `W` whose rows are `ω` (inverse of `rowRead`). -/
def unread (e : Fin 3 × V ≃ W) (c : Q ≃ V) (ω : Fin 3 → Q → F) (w : W) : F :=
  ω (e.symm w).1 (c.symm (e.symm w).2)

omit [Fintype W] [DecidableEq W] [Fintype Q] [DecidableEq Q] [Field F] [Fintype F]
  [DecidableEq F] in
theorem rowRead_eq_iff (e : Fin 3 × V ≃ W) (c : Q ≃ V) (y : W → F) (ω : Fin 3 → Q → F) :
    (fun i q => y (e (i, c q))) = ω ↔ y = unread e c ω := by
  constructor
  · rintro rfl
    funext w
    simp only [unread, Prod.mk.eta, Equiv.apply_symm_apply]
  · rintro rfl
    funext i q
    simp only [unread, Equiv.symm_apply_apply]

omit [Fintype W] [DecidableEq W] [Fintype Q] [DecidableEq Q] [Field F] [Fintype F]
  [DecidableEq F] in
theorem unread_injective_iff (e : Fin 3 × V ≃ W) (c : Q ≃ V) (ω : Fin 3 → Q → F) :
    Function.Injective (unread e c ω) ↔ JInj ω := by
  have h : unread e c ω = (fun z : Fin 3 × Q => ω z.1 z.2) ∘
      (e.symm.trans (Equiv.prodCongr (Equiv.refl _) c.symm)) := rfl
  rw [h, EquivLike.injective_comp]
  rfl

omit [Fintype Q] [DecidableEq Q] in
/-- In a graph without edges the injective strict-square labellings are the injective ones. -/
theorem mem_inj_noEdge (G : OrientedGraph W) (hG : ∀ e, e ∉ G.E) (y : W → F) :
    y ∈ injLabellings F G ↔ Function.Injective y := by
  rw [mem_injLabellings_iff_feasible]
  constructor
  · exact fun h a b hab => h.1 a (mem_univ _) b (mem_univ _) hab
  · exact fun h => ⟨fun a _ b _ hab => h hab, fun e he => absurd he (hG e)⟩

/-- **The law of the rows of a graph without edges** is uniform on the jointly injective row
configurations. -/
theorem edgeless_rows_weight (G : OrientedGraph W) (hG : ∀ e, e ∉ G.E)
    (hne : (injLabellings F G).Nonempty) (e : Fin 3 × V ≃ W) (c : Q ≃ V) (ω : Fin 3 → Q → F) :
    ((graphLaw G hne).map fun y i q => y (e (i, c q))).weight ω =
      if JInj ω then 1 / ((injLabellings F G).card : ℝ) else 0 := by
  rw [map_weight_eq]
  have hfilt : (univ.filter fun y : W → F => (fun i q => y (e (i, c q))) = ω) =
      {unread e c ω} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact rowRead_eq_iff e c y ω
  rw [hfilt, sum_singleton]
  change (if unread e c ω ∈ injLabellings F G then 1 / ((injLabellings F G).card : ℝ) else 0) = _
  simp only [mem_inj_noEdge G hG, unread_injective_iff]

end Edgeless

/-- **`G_{EE}` has no edges**: `E` has no forward pair. -/
theorem fieldGraph_EE_noEdge (Λ : Type) [Fintype Λ] :
    ∀ e, e ∉ (fieldGraph FType.E FType.E Λ).E := by
  intro e he
  rw [fieldGraph, mem_twoLayerGraph] at he
  simp [twoLayerEdge, FType.rel, typeE] at he

/-! ## The four row families at `𝔣' = E` -/

section Tail

variable (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) (hW : WeilBound (ZMod q))
  (hp : (2 : ℝ) ^ 20 ≤ q)

/-- The recorded matching coefficients of the `E` inputs are `h = 1`. -/
theorem tail_h_E : ((tailOrd .E).h : ℝ) = 1 ∧ ((tailRes .E).h : ℝ) = 1 := by
  norm_num [tailOrd, tailRes, tailOrdinary, tailReserved, toFType]

theorem card_EObj_two : Fintype.card (FieldTy.E.Obj × ZMod 2) ≤ 6 := by decide

theorem card_EObj_one : Fintype.card (FieldTy.E.Obj × Unit) ≤ 6 := by decide

include hp in
/-- The generic step: a uniform law on injective configurations with `k ≤ 6` labels per row over
`𝔽_q`, `q ≥ 2²⁰`, has `‖T_E^b - J‖ ≤ h r` with `h = 1`. -/
theorem uniform_tail {Q : Type} [Fintype Q] [DecidableEq Q] (hk : Fintype.card Q ≤ 6)
    (πE : FiniteLaw (Fin 3 → Q → ZMod q)) {c0 : ℝ}
    (hπ : ∀ ω, πE.weight ω = if JInj ω then c0 else 0) (hc0 : 0 < c0) {b : Q → ZMod q}
    (hb : (nuOf πE).weight b ≠ 0) :
    NormBound (nubOf πE b) (kernelOf πE πE b) (1 * tailR q) := by
  have hN : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod q) := by rw [ZMod.card]; exact hp
  have h := uniform_normBound_sqrt πE hπ hc0 hk hN hb
  rw [ZMod.card, one_div, ← tailR_eq_inv_sqrt] at h
  rw [one_mul]
  exact h

include hp in
/-- **(F4), matching half, two-layer rows of the coordinate `0` at `𝔣' = E`**:
`‖T_E^b - J‖ ≤ h r` with the recorded `h = 1`. -/
theorem matchE_two0 :
    ∀ b, (rowD0 (lam2 (tailFieldLaws q hne)) .E
        ((tail_upperDatumHyp q hW hp hne).two0 .E)).nu.weight b ≠ 0 →
      NormBound ((rowD0 (lam2 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).two0 .E)).nub b)
        ((rowD0 (lam2 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).two0 .E)).TE b) ((tailOrd .E).h * tailR q) := by
  intro b hb
  rw [tail_h_E.1]
  have e := two0E_eq q hne .E
  have hπ := edgeless_rows_weight (fieldGraph .E (toFType .E) (Fin 2))
    (fieldGraph_EE_noEdge (Fin 2)) (hne.two .E (toFType .E))
    (Equiv.refl (Fin 3 × (toFType .E).Obj × Fin 2)) (cTwo .E)
  change NormBound (nubOf ((lam2 (tailFieldLaws q hne) .E .E).map
      fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q)) b)
    (kernelOf ((lam2 (tailFieldLaws q hne) .E .E).map
      fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q))
      ((lam2 (tailFieldLaws q hne) .E .E).map
        fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q)) b) (1 * tailR q)
  change (nuOf ((lam2 (tailFieldLaws q hne) .E .E).map
      fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q))).weight b ≠ 0 at hb
  rw [e] at hb ⊢
  exact uniform_tail q hp card_EObj_two _ hπ (one_div_pos.mpr (by
    exact_mod_cast (hne.two .E (toFType .E)).card_pos)) hb

include hp in
/-- **(F4), matching half, two-layer rows of the coordinate `1` at `𝔣' = E`**. -/
theorem matchE_two1 :
    ∀ b, (rowD1 (lam2 (tailFieldLaws q hne)) .E
        ((tail_upperDatumHyp q hW hp hne).two1 .E)).nu.weight b ≠ 0 →
      NormBound ((rowD1 (lam2 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).two1 .E)).nub b)
        ((rowD1 (lam2 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).two1 .E)).TE b) ((tailOrd .E).h * tailR q) := by
  intro b hb
  rw [tail_h_E.1]
  have e := two1E_eq q hne .E
  have hπ := edgeless_rows_weight (fieldGraph (toFType .E) .E (Fin 2))
    (fieldGraph_EE_noEdge (Fin 2)) (hne.two (toFType .E) .E)
    (eRow1 (toFType .E).Obj (Fin 2)) (cTwo .E)
  change NormBound (nubOf ((lam2 (tailFieldLaws q hne) .E .E).map
      fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q)) b)
    (kernelOf ((lam2 (tailFieldLaws q hne) .E .E).map
      fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q))
      ((lam2 (tailFieldLaws q hne) .E .E).map
        fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q)) b) (1 * tailR q)
  change (nuOf ((lam2 (tailFieldLaws q hne) .E .E).map
      fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × ZMod 2 → ZMod q))).weight b ≠ 0 at hb
  rw [e] at hb ⊢
  exact uniform_tail q hp card_EObj_two _ hπ (one_div_pos.mpr (by
    exact_mod_cast (hne.two (toFType .E) .E).card_pos)) hb

include hp in
/-- **(F4), matching half, one-layer rows of the coordinate `0` at `𝔣' = E`**. -/
theorem matchE_one0 :
    ∀ b, (rowD0 (lam1 (tailFieldLaws q hne)) .E
        ((tail_upperDatumHyp q hW hp hne).one0 .E)).nu.weight b ≠ 0 →
      NormBound ((rowD0 (lam1 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).one0 .E)).nub b)
        ((rowD0 (lam1 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).one0 .E)).TE b) ((tailRes .E).h * tailR q) := by
  intro b hb
  rw [tail_h_E.2]
  have e := one0E_eq q hne .E
  have hπ := edgeless_rows_weight (fieldGraph .E (toFType .E) (Fin 1))
    (fieldGraph_EE_noEdge (Fin 1)) (hne.one .E (toFType .E))
    (Equiv.refl (Fin 3 × (toFType .E).Obj × Fin 1)) (cOne .E)
  change NormBound (nubOf ((lam1 (tailFieldLaws q hne) .E .E).map
      fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q)) b)
    (kernelOf ((lam1 (tailFieldLaws q hne) .E .E).map
      fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q))
      ((lam1 (tailFieldLaws q hne) .E .E).map
        fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q)) b) (1 * tailR q)
  change (nuOf ((lam1 (tailFieldLaws q hne) .E .E).map
      fun y => (rows0 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q))).weight b ≠ 0 at hb
  rw [e] at hb ⊢
  exact uniform_tail q hp card_EObj_one _ hπ (one_div_pos.mpr (by
    exact_mod_cast (hne.one .E (toFType .E)).card_pos)) hb

include hp in
/-- **(F4), matching half, one-layer rows of the coordinate `1` at `𝔣' = E`**. -/
theorem matchE_one1 :
    ∀ b, (rowD1 (lam1 (tailFieldLaws q hne)) .E
        ((tail_upperDatumHyp q hW hp hne).one1 .E)).nu.weight b ≠ 0 →
      NormBound ((rowD1 (lam1 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).one1 .E)).nub b)
        ((rowD1 (lam1 (tailFieldLaws q hne)) .E
          ((tail_upperDatumHyp q hW hp hne).one1 .E)).TE b) ((tailRes .E).h * tailR q) := by
  intro b hb
  rw [tail_h_E.2]
  have e := one1E_eq q hne .E
  have hπ := edgeless_rows_weight (fieldGraph (toFType .E) .E (Fin 1))
    (fieldGraph_EE_noEdge (Fin 1)) (hne.one (toFType .E) .E)
    (eRow1 (toFType .E).Obj (Fin 1)) (cOne .E)
  change NormBound (nubOf ((lam1 (tailFieldLaws q hne) .E .E).map
      fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q)) b)
    (kernelOf ((lam1 (tailFieldLaws q hne) .E .E).map
      fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q))
      ((lam1 (tailFieldLaws q hne) .E .E).map
        fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q)) b) (1 * tailR q)
  change (nuOf ((lam1 (tailFieldLaws q hne) .E .E).map
      fun y => (rows1 y : Fin 3 → FieldTy.E.Obj × Unit → ZMod q))).weight b ≠ 0 at hb
  rw [e] at hb ⊢
  exact uniform_tail q hp card_EObj_one _ hπ (one_div_pos.mpr (by
    exact_mod_cast (hne.one (toFType .E) .E).card_pos)) hb

end Tail

end Sarkozy.TailCorr

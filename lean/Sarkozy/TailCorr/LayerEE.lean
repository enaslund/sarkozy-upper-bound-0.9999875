module

public import Sarkozy.TailCorr.Uniform2
public import Sarkozy.TailCorr.MatchingE

@[expose] public section

/-!
# The layer cap of the field pair `EE` of the tail datum: (V3) proved for `EE`

`paper/sections/25_upper_reference.tex`, `subsec:upper-reference-rp`, (V3)
(`it:upper-valid-layer`) for the field pair `EE`, with the recorded cap `κ_{EE} = 1`;
`paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i).

The graphs `G_{EE,2}` and `G_{EE,1}` have no edges, so `λ_{EE}` and `λ⁽¹⁾_{EE}` are uniform on the
injective labellings. At the layer cut `ι` the two halves `x, y` of a two-layer labelling are
jointly injective and uniform; the half marginal is the one-layer law. So the cut form of
`λ_{EE} + κ r Diag_ι(λ⁽¹⁾_{EE})` is `⟨F, T G⟩ + κ r ⟨F, G⟩` in `L²(μ)`, with the pair kernel `T` of
`Uniform2`, and `‖T - J‖ ≤ q^{-1/2} = r` (`uniform2_normBound`, `defect2_le_sqrt`). Hence:

* **`layerCap_EE`**: `λ_{EE} ⪰_ι -κ_{EE} r Diag_ι(λ⁽¹⁾_{EE})` at every prime `q ≥ 2²⁰` (no Weil
  bound is used).
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws

/-! ## Reindexed laws of graphs without edges -/

section Reindex

variable {W V' : Type} [Fintype W] [DecidableEq W] [Fintype V'] [DecidableEq V']
  {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- **The reindexed law of a graph without edges** is uniform on the injective labellings. -/
theorem edgeless_reindex_weight (G : OrientedGraph W) (hG : ∀ e, e ∉ G.E)
    (hne : (injLabellings F G).Nonempty) (σ : V' ≃ W) (z : V' → F) :
    ((graphLaw G hne).map fun y => y ∘ σ).weight z =
      if Function.Injective z then 1 / ((injLabellings F G).card : ℝ) else 0 := by
  rw [map_weight_eq]
  have hfilt : (univ.filter fun y : W → F => y ∘ σ = z) = {z ∘ σ.symm} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro rfl
      funext w
      simp
    · rintro rfl
      funext v
      simp
  rw [hfilt, sum_singleton]
  change (if z ∘ σ.symm ∈ injLabellings F G then 1 / ((injLabellings F G).card : ℝ) else 0) = _
  simp only [mem_inj_noEdge G hG, EquivLike.injective_comp]

end Reindex

/-! ## The field pair `EE` -/

/-- The vertices of `G_{EE,2}` in C1's and V1's indexing. -/
def sig2 : FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2 ≃
    (toFType .E).Obj × (toFType .E).Obj × Fin 2 where
  toFun w := (objCast .E w.1, objCast .E w.2.1, layerFin w.2.2)
  invFun v := (objUncast .E v.1, objUncast .E v.2.1, layerUn v.2.2)
  left_inv w := by
    obtain ⟨a, b, l⟩ := w
    simp only [objUncast_objCast, layerUn_layerFin]
  right_inv v := by
    obtain ⟨a, b, l⟩ := v
    simp only [objCast_objUncast, layerFin_layerUn]

/-- The vertices of `G_{EE,1}` in C1's and V1's indexing. -/
def sig1 : FieldTy.E.Obj × FieldTy.E.Obj × Unit ≃
    (toFType .E).Obj × (toFType .E).Obj × Fin 1 where
  toFun w := (objCast .E w.1, objCast .E w.2.1, 0)
  invFun v := (objUncast .E v.1, objUncast .E v.2.1, ())
  left_inv w := by
    obtain ⟨a, b, u⟩ := w
    simp only [objUncast_objCast]
  right_inv v := by
    obtain ⟨a, b, l⟩ := v
    simp only [objCast_objUncast, Prod.mk.injEq, true_and]
    exact (Fin.fin_one_eq_zero l).symm

/-- The layer cut of the field pair `EE`. -/
abbrev cutEE : ReflectionCut (FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2) :=
  Reserved.fieldCut FieldTy.E.Obj FieldTy.E.Obj

theorem mem_cutEE_half (v : FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2) :
    v ∈ cutEE.half ↔ v.2.2 = 0 := by
  obtain ⟨a, b, l⟩ := v
  change (a, b, l) ∈ (univ : Finset FieldTy.E.Obj) ×ˢ
    ((univ : Finset FieldTy.E.Obj) ×ˢ ({0} : Finset (ZMod 2))) ↔ l = 0
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_singleton]
  simp only [Finset.mem_univ, true_and]

theorem flip_cutEE (v : FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2) :
    (cutEE.flip v).1 = v.1 ∧ (cutEE.flip v).2.1 = v.2.1 := ⟨rfl, rfl⟩

/-- The half of the layer cut is the one-layer vertex set. -/
def halfEquiv : cutEE.Half ≃ FieldTy.E.Obj × FieldTy.E.Obj × Unit where
  toFun v := (v.1.1, v.1.2.1, ())
  invFun w := ⟨(w.1, w.2.1, 0), (mem_cutEE_half _).mpr rfl⟩
  left_inv v := by
    obtain ⟨⟨a, b, l⟩, hv⟩ := v
    have hl : l = 0 := (mem_cutEE_half _).mp hv
    subst hl
    rfl
  right_inv w := by
    obtain ⟨a, b, u⟩ := w
    rfl

theorem card_half_EE : Fintype.card cutEE.Half = 9 := by
  rw [Fintype.card_congr halfEquiv]
  decide

/-- **The join of two halves is injective iff the halves are jointly injective.** -/
theorem join_injective_iff {X : Type*} (x y : cutEE.Half → X) :
    Function.Injective (cutEE.join x y) ↔ JInj ![x, y] := by
  constructor
  · intro h ⟨i, a⟩ ⟨j, b⟩ hab
    simp only at hab
    fin_cases i <;> fin_cases j
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero] at hab
      rw [← cutEE.join_plus x y a, ← cutEE.join_plus x y b] at hab
      exact Prod.ext rfl (Subtype.ext (h hab))
    · simp only [Fin.zero_eta, Fin.isValue, Matrix.cons_val_zero, Fin.mk_one,
        Matrix.cons_val_one] at hab
      rw [← cutEE.join_plus x y a, ← cutEE.join_minus x y b] at hab
      exact absurd ((h hab) ▸ a.2) (cutEE.flip_not_mem b.2)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Fin.zero_eta,
        Matrix.cons_val_zero] at hab
      rw [← cutEE.join_minus x y a, ← cutEE.join_plus x y b] at hab
      exact absurd ((h hab).symm ▸ b.2) (cutEE.flip_not_mem a.2)
    · simp only [Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero] at hab
      rw [← cutEE.join_minus x y a, ← cutEE.join_minus x y b] at hab
      have := cutEE.flip.injective (h hab)
      exact Prod.ext rfl (Subtype.ext this)
  · intro h v w hvw
    by_cases hv : v ∈ cutEE.half <;> by_cases hw : w ∈ cutEE.half
    · have e1 : cutEE.join x y v = x ⟨v, hv⟩ := cutEE.join_plus x y ⟨v, hv⟩
      have e2 : cutEE.join x y w = x ⟨w, hw⟩ := cutEE.join_plus x y ⟨w, hw⟩
      rw [e1, e2] at hvw
      have := h (a₁ := ((0 : Fin 2), ⟨v, hv⟩)) (a₂ := ((0 : Fin 2), ⟨w, hw⟩)) hvw
      exact congrArg Subtype.val (Prod.mk.inj this).2
    · have hw' : cutEE.flip w ∈ cutEE.half := (cutEE.crosses w).mpr hw
      have e1 : cutEE.join x y v = x ⟨v, hv⟩ := cutEE.join_plus x y ⟨v, hv⟩
      have e2 : cutEE.join x y w = y ⟨cutEE.flip w, hw'⟩ := by
        have := cutEE.join_minus x y ⟨cutEE.flip w, hw'⟩
        rwa [cutEE.flip_flip] at this
      rw [e1, e2] at hvw
      have := h (a₁ := ((0 : Fin 2), ⟨v, hv⟩)) (a₂ := ((1 : Fin 2), ⟨cutEE.flip w, hw'⟩)) hvw
      exact absurd (Prod.mk.inj this).1 (by decide)
    · have hv' : cutEE.flip v ∈ cutEE.half := (cutEE.crosses v).mpr hv
      have e1 : cutEE.join x y v = y ⟨cutEE.flip v, hv'⟩ := by
        have := cutEE.join_minus x y ⟨cutEE.flip v, hv'⟩
        rwa [cutEE.flip_flip] at this
      have e2 : cutEE.join x y w = x ⟨w, hw⟩ := cutEE.join_plus x y ⟨w, hw⟩
      rw [e1, e2] at hvw
      have := h (a₁ := ((1 : Fin 2), ⟨cutEE.flip v, hv'⟩)) (a₂ := ((0 : Fin 2), ⟨w, hw⟩)) hvw
      exact absurd (Prod.mk.inj this).1 (by decide)
    · have hv' : cutEE.flip v ∈ cutEE.half := (cutEE.crosses v).mpr hv
      have hw' : cutEE.flip w ∈ cutEE.half := (cutEE.crosses w).mpr hw
      have e1 : cutEE.join x y v = y ⟨cutEE.flip v, hv'⟩ := by
        have := cutEE.join_minus x y ⟨cutEE.flip v, hv'⟩
        rwa [cutEE.flip_flip] at this
      have e2 : cutEE.join x y w = y ⟨cutEE.flip w, hw'⟩ := by
        have := cutEE.join_minus x y ⟨cutEE.flip w, hw'⟩
        rwa [cutEE.flip_flip] at this
      rw [e1, e2] at hvw
      have := h (a₁ := ((1 : Fin 2), ⟨cutEE.flip v, hv'⟩))
        (a₂ := ((1 : Fin 2), ⟨cutEE.flip w, hw'⟩)) hvw
      exact cutEE.flip.injective (congrArg Subtype.val (Prod.mk.inj this).2)

/-! ## The cut forms -/

section Forms

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The cut form of a law at `ι`** as a double sum over the two halves. -/
theorem form_lawL_EE (μ : FiniteLaw (FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2 → X))
    (Φ Ψ : (cutEE.Half → X) → ℝ) :
    cutEE.form (lawL μ) Φ Ψ = ∑ x, ∑ y, μ.weight (cutEE.join x y) * Φ x * Ψ y := by
  rw [ReflectionCut.form, cut_form_eq_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have h := ReflectionCut.matrix_signedIntegral cutEE μ.weight x y
  change cutEE.matrix (lawL μ) x y * Φ x * Ψ y = _
  rw [show lawL μ = signedIntegral μ.weight from rfl, h]

omit [DecidableEq X] in
/-- **The cut form of `Diag_ι(λ⁽¹⁾)` at `ι`**: `∫ Φ(z') Ψ(z') dλ⁽¹⁾(z')`, with the half read as the
one-layer vertex set. -/
theorem form_diag_EE (μ : FiniteLaw (FieldTy.E.Obj × FieldTy.E.Obj × Unit → X))
    (Φ Ψ : (cutEE.Half → X) → ℝ) :
    cutEE.form (pushFunctional (lawL μ) Reserved.diagF) Φ Ψ =
      ∑ x : cutEE.Half → X, μ.weight (x ∘ halfEquiv.symm) * Φ x * Ψ x := by
  change ∑ z', μ.weight z' * (Φ (fun v => Reserved.diagF z' v.1) *
    Ψ (fun v => Reserved.diagF z' (cutEE.flip v.1))) = _
  refine Fintype.sum_equiv (halfEquiv.symm.arrowCongr (Equiv.refl X)) _ _ fun z' => ?_
  have e1 : (fun v : cutEE.Half => Reserved.diagF z' v.1) =
      (halfEquiv.symm.arrowCongr (Equiv.refl X)) z' := rfl
  have e2 : (fun v : cutEE.Half => Reserved.diagF z' (cutEE.flip v.1)) =
      (halfEquiv.symm.arrowCongr (Equiv.refl X)) z' := rfl
  have e3 : (halfEquiv.symm.arrowCongr (Equiv.refl X)) z' ∘ halfEquiv.symm = z' := by
    funext w
    simp [Equiv.arrowCongr_apply]
  rw [e1, e2, e3]
  ring

end Forms

/-! ## The pair counts -/

section Pairs

variable {F : Type} [Fintype F] [DecidableEq F] {Q : Type} [Fintype Q] [DecidableEq Q]

/-- `∑_{x, y} c [(x, y) injective] = c A M`. -/
theorem sum_pairs (c : ℝ) :
    ∑ x : Q → F, ∑ y : Q → F, (if JInj ![x, y] then c else 0) =
      c * ((cntA2 F Q : ℝ) * cntM2 F Q) := by
  have hinner : ∀ x : Q → F, ∑ y : Q → F, (if JInj ![x, y] then c else 0) =
      if Function.Injective x then c * cntM2 F Q else 0 := by
    intro x
    rw [sum_ite_const]
    by_cases hx : Function.Injective x
    · simp only [hx, ↓reduceIte, card_pair hx]
    · have he : (univ.filter fun y : Q → F => JInj ![x, y]) = ∅ := by
        ext y
        simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
        exact fun h => hx ((inj2_iff x y).mp h).2.1
      simp only [hx, ↓reduceIte, he, card_empty, Nat.cast_zero, mul_zero]
  simp_rw [hinner]
  rw [sum_ite_const, card_inj1]
  ring

omit [DecidableEq Q] in
/-- The pair kernel is symmetric. -/
theorem pairKernel_symm (x y : Q → F) : pairKernel x y = pairKernel y x := by
  unfold pairKernel
  have e1 : (Function.Injective x ∧ Function.Injective y) ↔
      (Function.Injective y ∧ Function.Injective x) := and_comm
  simp only [e1, inj2_swap x y]

end Pairs

/-! ## The layer cap of `EE` -/

section Tail

variable (q : ℕ) [Fact q.Prime] (hne : TailNonempty q)

/-- `λ_{EE}` is uniform on the injective labellings. -/
theorem lamEE2_weight (z : FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2 → ZMod q) :
    (lam2 (tailFieldLaws q hne) .E .E).weight z = if Function.Injective z then
      1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 2))).card : ℝ) else 0 := by
  change ((graphLaw (fieldGraph (toFType .E) (toFType .E) (Fin 2)) (hne.two _ _)).map
    fun y => y ∘ sig2).weight z = _
  exact edgeless_reindex_weight _ (fieldGraph_EE_noEdge (Fin 2)) _ sig2 z

/-- `λ⁽¹⁾_{EE}` is uniform on the injective labellings. -/
theorem lamEE1_weight (z : FieldTy.E.Obj × FieldTy.E.Obj × Unit → ZMod q) :
    (lam1 (tailFieldLaws q hne) .E .E).weight z = if Function.Injective z then
      1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 1))).card : ℝ) else 0 := by
  change ((graphLaw (fieldGraph (toFType .E) (toFType .E) (Fin 1)) (hne.one _ _)).map
    fun y => y ∘ sig1).weight z = _
  exact edgeless_reindex_weight _ (fieldGraph_EE_noEdge (Fin 1)) _ sig1 z

include hne in
/-- The normalization of `λ_{EE}`: `|Inj(G_{EE,2})| = A M`. -/
theorem normEE2 :
    1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 2))).card : ℝ) *
      ((cntA2 (ZMod q) cutEE.Half : ℝ) * cntM2 (ZMod q) cutEE.Half) = 1 := by
  have htot := (lam2 (tailFieldLaws q hne) .E .E).total
  simp_rw [lamEE2_weight] at htot
  set c2 := 1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 2))).card : ℝ) with hc2
  have key : ∑ z : FieldTy.E.Obj × FieldTy.E.Obj × ZMod 2 → ZMod q,
      (if Function.Injective z then c2 else 0) =
        ∑ x : cutEE.Half → ZMod q, ∑ y : cutEE.Half → ZMod q,
          (if JInj ![x, y] then c2 else 0) := by
    rw [← Fintype.sum_prod_type']
    refine Fintype.sum_equiv cutEE.configurationEquiv _ _ fun z => ?_
    have h := join_injective_iff (cutEE.configurationEquiv z).1 (cutEE.configurationEquiv z).2
    rw [show cutEE.join (cutEE.configurationEquiv z).1 (cutEE.configurationEquiv z).2 = z from
      cutEE.configurationEquiv.symm_apply_apply z] at h
    simp only [h]
  rw [← sum_pairs, ← key]
  exact htot

include hne in
/-- The normalization of `λ⁽¹⁾_{EE}`: `|Inj(G_{EE,1})| = A`. -/
theorem normEE1 :
    1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 1))).card : ℝ) *
      (cntA2 (ZMod q) cutEE.Half : ℝ) = 1 := by
  have htot := (lam1 (tailFieldLaws q hne) .E .E).total
  simp_rw [lamEE1_weight] at htot
  rw [sum_ite_const, card_inj1] at htot
  have hc : cntA2 (ZMod q) (FieldTy.E.Obj × FieldTy.E.Obj × Unit) = cntA2 (ZMod q) cutEE.Half := by
    unfold cntA2
    rw [Fintype.card_congr halfEquiv]
  rw [hc] at htot
  exact htot

include hne in
/-- **(V3) for the field pair `EE`** (`it:upper-valid-layer` with `κ_{EE} = 1`):
`λ_{EE} ⪰_ι -κ_{EE} r Diag_ι(λ⁽¹⁾_{EE})` at every prime `q ≥ 2²⁰`. -/
theorem layerCap_EE (hp : (2 : ℝ) ^ 20 ≤ q) :
    (Reserved.fieldCut FieldTy.E.Obj FieldTy.E.Obj).Below
      (-(tailKappa .E .E * tailR q) •
        pushFunctional (lawL (lam1 (tailFieldLaws q hne) .E .E)) Reserved.diagF)
      (lawL (lam2 (tailFieldLaws q hne) .E .E)) := by
  have hk : Fintype.card cutEE.Half ≤ 9 := card_half_EE.le
  have hN : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod q) := by rw [ZMod.card]; exact hp
  have hN' : 2 * Fintype.card cutEE.Half ≤ Fintype.card (ZMod q) := by
    have : (2 * Fintype.card cutEE.Half : ℝ) ≤ Fintype.card (ZMod q) := by
      have hk' : (Fintype.card cutEE.Half : ℝ) ≤ 9 := by exact_mod_cast hk
      linarith
    exact_mod_cast this
  have hA : 0 < cntA2 (ZMod q) cutEE.Half := Nat.pos_of_ne_zero fun h0 => by
    unfold cntA2 at h0
    rw [Nat.descFactorial_eq_zero_iff_lt] at h0
    omega
  have hM : 0 < cntM2 (ZMod q) cutEE.Half := Nat.pos_of_ne_zero fun h0 => by
    unfold cntM2 at h0
    rw [Nat.descFactorial_eq_zero_iff_lt] at h0
    omega
  have hA' : (0 : ℝ) < cntA2 (ZMod q) cutEE.Half := by exact_mod_cast hA
  have hM' : (0 : ℝ) < cntM2 (ZMod q) cutEE.Half := by exact_mod_cast hM
  set c2 := 1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 2))).card : ℝ) with hc2def
  set c1 := 1 / ((injLabellings (ZMod q) (fieldGraph .E .E (Fin 1))).card : ℝ) with hc1def
  have hc2 : c2 = ((cntA2 (ZMod q) cutEE.Half : ℝ) * cntM2 (ZMod q) cutEE.Half)⁻¹ := by
    have := normEE2 q hne
    rw [← hc2def] at this
    field_simp
    linarith
  have hc1 : c1 = (cntA2 (ZMod q) cutEE.Half : ℝ)⁻¹ := by
    have := normEE1 q hne
    rw [← hc1def] at this
    field_simp
    linarith
  have hκ : tailKappa .E .E = 1 := by
    simp [tailKappa, tailFieldCap, toFType]
  -- the cut form
  have hform : ∀ Φ Ψ : (cutEE.Half → ZMod q) → ℝ,
      cutEE.form (lawL (lam2 (tailFieldLaws q hne) .E .E) -
        (-(tailKappa .E .E * tailR q) •
          pushFunctional (lawL (lam1 (tailFieldLaws q hne) .E .E)) Reserved.diagF)) Φ Ψ =
        kf (injLaw hA) pairKernel Φ Ψ + tailR q * ip (injLaw hA) Φ Ψ := by
    intro Φ Ψ
    change cutEE.form (lawL (lam2 (tailFieldLaws q hne) .E .E)) Φ Ψ -
      (-(tailKappa .E .E * tailR q)) *
        cutEE.form (pushFunctional (lawL (lam1 (tailFieldLaws q hne) .E .E)) Reserved.diagF)
          Φ Ψ = _
    have ha : ∑ x, ∑ y, (lam2 (tailFieldLaws q hne) .E .E).weight (cutEE.join x y) * Φ x * Ψ y =
        kf (injLaw hA) pairKernel Φ Ψ := by
      unfold kf
      refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
      rw [lamEE2_weight, ← hc2def, hc2]
      have hw := pair_weight hA hM x y
      rw [show (injLaw hA).weight x * (injLaw hA).weight y * (Φ x * pairKernel x y * Ψ y) =
        ((injLaw hA).weight x * (injLaw hA).weight y * pairKernel x y) * Φ x * Ψ y by ring, hw]
      simp only [join_injective_iff]
    have hb : ∑ x, (lam1 (tailFieldLaws q hne) .E .E).weight (x ∘ halfEquiv.symm) * Φ x * Ψ x =
        ip (injLaw hA) Φ Ψ := by
      unfold ip FiniteLaw.expect
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [lamEE1_weight, ← hc1def, hc1]
      change _ = (if Function.Injective x then (cntA2 (ZMod q) cutEE.Half : ℝ)⁻¹ else 0) *
        (Φ x * Ψ x)
      simp only [EquivLike.injective_comp]
      ring
    rw [form_lawL_EE, form_diag_EE, hκ, one_mul, ha, hb]
    ring
  have hδ := uniform2_normBound hA hM
  have hδr : 2 * (((cntA2 (ZMod q) cutEE.Half : ℝ) - cntM2 (ZMod q) cutEE.Half) /
      cntA2 (ZMod q) cutEE.Half) ≤ tailR q := by
    have := defect2_le_sqrt hk hN
    rw [ZMod.card, one_div, ← tailR_eq_inv_sqrt] at this
    exact this
  refine ⟨fun Φ Ψ => ?_, fun Φ => ?_⟩
  · rw [hform, hform]
    have hk : kf (injLaw hA) pairKernel Φ Ψ = kf (injLaw hA) pairKernel Ψ Φ := by
      unfold kf
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => ?_
      rw [pairKernel_symm]
      ring
    have hi : ip (injLaw hA) Φ Ψ = ip (injLaw hA) Ψ Φ := by
      unfold ip
      exact FiniteLaw.expect_congr _ fun x => mul_comm _ _
    rw [hk, hi]
  · rw [hform]
    have hb := hδ Φ Φ
    have hip : 0 ≤ ip (injLaw hA) Φ Φ :=
      Finset.sum_nonneg fun x _ => mul_nonneg ((injLaw hA).nonneg x) (mul_self_nonneg _)
    have hn : nrm (injLaw hA) Φ * nrm (injLaw hA) Φ = ip (injLaw hA) Φ Φ :=
      Real.mul_self_sqrt hip
    have hδ0 : 0 ≤ 2 * (((cntA2 (ZMod q) cutEE.Half : ℝ) - cntM2 (ZMod q) cutEE.Half) /
        cntA2 (ZMod q) cutEE.Half) := by
      have hMA : (cntM2 (ZMod q) cutEE.Half : ℝ) ≤ cntA2 (ZMod q) cutEE.Half := by
        exact_mod_cast Nat.descFactorial_le _ (Nat.sub_le _ _)
      have : (0 : ℝ) ≤ ((cntA2 (ZMod q) cutEE.Half : ℝ) - cntM2 (ZMod q) cutEE.Half) /
          cntA2 (ZMod q) cutEE.Half := div_nonneg (by linarith) hA'.le
      linarith
    rw [mul_assoc, hn] at hb
    have h1 := (abs_le.mp hb).1
    have h2 : 0 ≤ (injLaw hA).expect Φ * (injLaw hA).expect Φ := mul_self_nonneg _
    have h3 : 2 * (((cntA2 (ZMod q) cutEE.Half : ℝ) - cntM2 (ZMod q) cutEE.Half) /
        cntA2 (ZMod q) cutEE.Half) * ip (injLaw hA) Φ Φ ≤ tailR q * ip (injLaw hA) Φ Φ :=
      mul_le_mul_of_nonneg_right hδr hip
    linarith

end Tail

end Sarkozy.TailCorr

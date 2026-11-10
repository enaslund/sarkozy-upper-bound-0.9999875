module

public import Sarkozy.PartVLaws.RowDatum
public import Sarkozy.FiveType.ReservedCut

@[expose] public section

/-!
# The upper reference in the two-coordinate language of `FiveType`

`paper/sections/25_upper_reference.tex`, `def:upper-reference`, `subsec:layer72:upper`,
`lem:upper-reference-rp` ("Chamber cuts"); `paper/sections/17_completion_repair.tex`,
`def:two-coordinate-five-type`, `lem:five-type`(d),(e).

V1's upper reference (`PartV.upperTilde`, indexed by V1's `PType`/`FType` and with layers in
`Fin 2`, `Fin 1`) and C1's two-coordinate setting (`FiveType.TwoCoord`, indexed by `Ty`/`FieldTy`,
with layers `ZMod 2` and `Unit`) describe the same measure. This file makes that precise.

* `lam2 F`, `lam1 F`: the two-layer and one-layer field laws of an `UpperFieldLaws F` in C1's
  format (`λ_{𝔣₀𝔣₁}` on `O_{𝔣₀} × O_{𝔣₁} × {0,1}` and on `O_{𝔣₀} × O_{𝔣₁} × Unit`).
* **`upperTilde_eq_paired`**:
  `μ̃_𝔅 = ∑_𝔱 w_𝔱 r^{deg 𝔱} π_{𝔱,2} + r ∑_𝔱 v_𝔱 r^{deg 𝔱} Diag_ι(π_{𝔱,1})` is C1's
  `Reserved.pairedMeasure (lam2 F) (lam1 F) w v r`, as a functional on the 72 slots.
* **Row data.** `RowHyp0 lam 𝔣'` (resp. `RowHyp1`) collects what makes the row data of the
  coordinate `0` (resp. `1`) at the field type `𝔣'` a five-type datum: the `E` rows are
  exchangeable, the `F` rows are `Γ`-supported (`GamSupported`, the implicit extension
  hypothesis of `subsec:upper-rows`, V1's finding 3), the `L` rows are `𝒢₆`-invariant.
  `rowD0`/`rowD1` is that datum (`datumOfGam`), and `rowDatum0`/`rowDatum1` prove C1's
  `RowDatum0`/`RowDatum1` for it, the hypothesis of `lem:five-type`(d).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

/-! ## Dictionary between V1's and C1's indices -/

/-- C1's field types as V1's. -/
def toFType : FieldTy → FType
  | .L => .L
  | .F => .F
  | .E => .E

/-- The objects of a C1 field type are those of the V1 field type (the identity in each case). -/
def objCast : (f : FieldTy) → f.Obj → (toFType f).Obj
  | .L => fun x => x
  | .F => fun x => x
  | .E => fun x => x

/-- The pattern types as `Ty`. -/
def tyEquiv : Ty ≃ PType where
  toFun := ofTy
  invFun := toTy
  left_inv t := by cases t <;> rfl
  right_inv t := by cases t <;> rfl

/-- The two-layer weights `w_𝔱` on `Ty × Ty`. -/
def wTy (W : UpperWeights) (t0 t1 : Ty) : ℝ := W.w (ofTy t0) (ofTy t1)

/-- The one-layer weights `v_𝔱` on `Ty × Ty`. -/
def vTy (W : UpperWeights) (t0 t1 : Ty) : ℝ := W.v (ofTy t0) (ofTy t1)

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## The field laws in C1's format -/

/-- The two-layer field laws `λ_{𝔣₀𝔣₁}` on `O_{𝔣₀} × O_{𝔣₁} × ℤ/2ℤ` (the layer read through
`layerFin`). -/
noncomputable def lam2 (F : UpperFieldLaws X) (f0 f1 : FieldTy) :
    FiniteLaw (f0.Obj × f1.Obj × ZMod 2 → X) :=
  (F.two (toFType f0) (toFType f1)).map fun y w =>
    y (objCast f0 w.1, objCast f1 w.2.1, layerFin w.2.2)

/-- The one-layer field laws `λ^{(1)}_{𝔣₀𝔣₁}` on `O_{𝔣₀} × O_{𝔣₁} × Unit`. -/
noncomputable def lam1 (F : UpperFieldLaws X) (f0 f1 : FieldTy) :
    FiniteLaw (f0.Obj × f1.Obj × Unit → X) :=
  (F.one (toFType f0) (toFType f1)).map fun y w => y (objCast f0 w.1, objCast f1 w.2.1, 0)

/-- A two-layer component of V1 is C1's component. -/
theorem two_comp_eq (F : UpperFieldLaws X) (f0 f1 : FieldTy) (ψ0 : ZMod 6 → f0.Obj)
    (ψ1 : ZMod 6 → f1.Obj) :
    signedIntegral (PartV.emit (F.two (toFType f0) (toFType f1))
        (upEmission (fun u => objCast f0 (ψ0 u)) (fun u => objCast f1 (ψ1 u)))).weight =
      pushFunctional (lawL (lam2 F f0 f1)) (TwoCoord.emit ψ0 ψ1) := by
  refine LinearMap.ext fun f => ?_
  rw [← FiniteLaw.expect_eq_signedIntegral, PartV.expect_emit]
  change _ = (lam2 F f0 f1).expect (f ∘ TwoCoord.emit ψ0 ψ1)
  rw [lam2, FiniteLaw.expect_map]
  rfl

/-- A one-layer diagonal component of V1 is C1's `Diag_ι` of the one-layer component. -/
theorem one_comp_eq (F : UpperFieldLaws X) (f0 f1 : FieldTy) (ψ0 : ZMod 6 → f0.Obj)
    (ψ1 : ZMod 6 → f1.Obj) :
    signedIntegral (PartV.emit (F.one (toFType f0) (toFType f1))
        (upDiagEmission (fun u => objCast f0 (ψ0 u)) (fun u => objCast f1 (ψ1 u)))).weight =
      pushFunctional (pushFunctional (lawL (lam1 F f0 f1)) (TwoCoord.emit ψ0 ψ1))
        Reserved.diagW := by
  refine LinearMap.ext fun f => ?_
  rw [← FiniteLaw.expect_eq_signedIntegral, PartV.expect_emit]
  change _ = (lam1 F f0 f1).expect ((f ∘ Reserved.diagW) ∘ TwoCoord.emit ψ0 ψ1)
  rw [lam1, FiniteLaw.expect_map]
  rfl

theorem pair_smul_eq {M : Type*} [AddCommMonoid M] [Module ℝ M] {a b c d : ℝ} {A B C D : M}
    (h1 : a = c) (h2 : A = C) (h3 : b = d) (h4 : B = D) : a • A + b • B = c • C + d • D := by
  rw [h1, h2, h3, h4]

/-- **The two parts of one state agree**: for a state `(t₀, t₁)`, the summands of V1's `μ̃_𝔅`
are those of C1's paired measure. -/
theorem state_eq (F : UpperFieldLaws X) (W : UpperWeights) (r : ℝ) (t0 t1 : Ty) :
    ∑ φ0 : PatIdx t0, ∑ φ1 : PatIdx t1,
        ((wTy W t0 t1 * r ^ stateDeg t0 t1) • comp (lam2 F) t0 φ0 t1 φ1 +
          (vTy W t0 t1 * r ^ (stateDeg t0 t1 + 1)) •
            pushFunctional (comp (lam1 F) t0 φ0 t1 φ1) Reserved.diagW) =
      ∑ φ : (ofTy t0).Pat × (ofTy t1).Pat,
        (upCoeff W r (true, ⟨(ofTy t0, ofTy t1), φ⟩) •
            signedIntegral (upComponent F (true, ⟨(ofTy t0, ofTy t1), φ⟩)).weight +
          upCoeff W r (false, ⟨(ofTy t0, ofTy t1), φ⟩) •
            signedIntegral (upComponent F (false, ⟨(ofTy t0, ofTy t1), φ⟩)).weight) := by
  rw [Fintype.sum_prod_type]
  cases t0 <;> cases t1 <;>
  exact Finset.sum_congr rfl fun φ0 _ => Finset.sum_congr rfl fun φ1 _ =>
    pair_smul_eq rfl (two_comp_eq F (fieldOf _) (fieldOf _) (patMap _ φ0) (patMap _ φ1)).symm rfl
      (one_comp_eq F (fieldOf _) (fieldOf _) (patMap _ φ0) (patMap _ φ1)).symm

/-- **`μ̃_𝔅` is C1's paired measure** (`def:upper-reference` = the measure of
`lem:five-type`(e) in two coordinates, with the field laws `lam2 F`, `lam1 F`). -/
theorem upperTilde_eq_paired (F : UpperFieldLaws X) (W : UpperWeights) (r : ℝ) :
    upperTilde F W r = Reserved.pairedMeasure (lam2 F) (lam1 F) (wTy W) (vTy W) r := by
  rw [Reserved.pairedMeasure_eq]
  unfold upperTilde tildeMeasure
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib, Fintype.sum_sigma,
    Fintype.sum_prod_type]
  rw [← Fintype.sum_equiv tyEquiv (fun t0 => ∑ t1 : PType, ∑ φ : (ofTy t0).Pat × t1.Pat,
      (upCoeff W r (true, ⟨(ofTy t0, t1), φ⟩) •
          signedIntegral (upComponent F (true, ⟨(ofTy t0, t1), φ⟩)).weight +
        upCoeff W r (false, ⟨(ofTy t0, t1), φ⟩) •
          signedIntegral (upComponent F (false, ⟨(ofTy t0, t1), φ⟩)).weight)) _
      (fun _ => rfl)]
  refine Finset.sum_congr rfl fun t0 _ => ?_
  rw [← Fintype.sum_equiv tyEquiv (fun t1 => ∑ φ : (ofTy t0).Pat × (ofTy t1).Pat,
      (upCoeff W r (true, ⟨(ofTy t0, ofTy t1), φ⟩) •
          signedIntegral (upComponent F (true, ⟨(ofTy t0, ofTy t1), φ⟩)).weight +
        upCoeff W r (false, ⟨(ofTy t0, ofTy t1), φ⟩) •
          signedIntegral (upComponent F (false, ⟨(ofTy t0, ofTy t1), φ⟩)).weight)) _
      (fun _ => rfl)]
  exact Finset.sum_congr rfl fun t1 _ => (state_eq F W r t0 t1).symm

/-! ## Row data -/

variable {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- **The row data of the coordinate `0` at `𝔣'` form a five-type datum**: the hypotheses of
`datumOfGam` for the row laws of `λ_{E𝔣'}`, `λ_{F𝔣'}`, `λ_{L𝔣'}`:
* `exch`: the `E` rows are exchangeable (every permutation of `O_E` is an automorphism of
  `G_{E𝔣'}`);
* `supp`: the `F` rows are `Γ`-supported: every pair of rows `(0,1)` or `(2,1)` of a charged
  `F` configuration extends to a charged `E` configuration (`subsec:upper-rows`; this is the
  extension count input, V1's finding 3);
* `root`: the `L` rows are `𝒢₆`-invariant (`lem:upper-geometry`(b)). -/
structure RowHyp0 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) : Prop where
  exch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → f'.Obj × Λ → X),
    ((lam .E f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X)).weight (ω ∘ σ) =
      ((lam .E f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X)).weight ω
  supp : GamSupported ((lam .E f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))
    ((lam .F f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))
  root : ∀ (k : Fin 6) (Ψ : ZMod 6 → f'.Obj × Λ → X),
    ((lam .L f').map fun y => (rows0 y : ZMod 6 → f'.Obj × Λ → X)).weight (Ψ ∘ g6 k) =
      ((lam .L f').map fun y => (rows0 y : ZMod 6 → f'.Obj × Λ → X)).weight Ψ

/-- The same for the coordinate `1` (the laws `λ_{𝔣'E}`, `λ_{𝔣'F}`, `λ_{𝔣'L}`). -/
structure RowHyp1 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) : Prop where
  exch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → f'.Obj × Λ → X),
    ((lam f' .E).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X)).weight (ω ∘ σ) =
      ((lam f' .E).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X)).weight ω
  supp : GamSupported ((lam f' .E).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X))
    ((lam f' .F).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X))
  root : ∀ (k : Fin 6) (Ψ : ZMod 6 → f'.Obj × Λ → X),
    ((lam f' .L).map fun y => (rows1 y : ZMod 6 → f'.Obj × Λ → X)).weight (Ψ ∘ g6 k) =
      ((lam f' .L).map fun y => (rows1 y : ZMod 6 → f'.Obj × Λ → X)).weight Ψ

/-- **The row datum of the coordinate `0` at `𝔣'`** (`def:two-coordinate-five-type`). -/
noncomputable def rowD0 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp0 lam f') : Datum (f'.Obj × Λ → X) :=
  datumOfGam _ _ _ h.exch h.supp h.root

/-- **The row datum of the coordinate `1` at `𝔣'`.** -/
noncomputable def rowD1 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp1 lam f') : Datum (f'.Obj × Λ → X) :=
  datumOfGam _ _ _ h.exch h.supp h.root

/-- **`rowD0` is the row data of the coordinate `0`** (C1's `RowDatum0`). The middle law is the
law of the row `1`, which is that of the row `0` by exchangeability. -/
theorem rowDatum0 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp0 lam f') : RowDatum0 lam f' (rowD0 lam f' h) where
  piL := rfl
  piF := rfl
  piE := rfl
  Gam := by
    change gamOf _ = _
    rw [gamOf, map_map']
    rfl
  nu := by
    change nuOf _ = _
    rw [nuOf_eq_obj0 _ h.exch, map_map']
    rfl

/-- **`rowD1` is the row data of the coordinate `1`** (C1's `RowDatum1`). -/
theorem rowDatum1 (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp1 lam f') : RowDatum1 lam f' (rowD1 lam f' h) where
  piL := rfl
  piF := rfl
  piE := rfl
  Gam := by
    change gamOf _ = _
    rw [gamOf, map_map']
    rfl
  nu := by
    change nuOf _ = _
    rw [nuOf_eq_obj0 _ h.exch, map_map']
    rfl

end Sarkozy.PartVLaws

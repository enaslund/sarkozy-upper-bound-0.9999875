module

public import Sarkozy.FiveType.ReservedCutOne





@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings ReflectionCut TwoCoord Reserved ReservedOne

namespace TwoCoordSanity

/-- The point law on a one-point type. -/
noncomputable def pt (Ω : Type*) [Fintype Ω] [Unique Ω] : FiniteLaw Ω where
  weight _ := 1
  nonneg _ := zero_le_one
  total := by simp

/-- Two laws on a one-point type are equal. -/
theorem law_eq_of_unique {Ω : Type*} [Fintype Ω] [Unique Ω] (μ ν : FiniteLaw Ω) : μ = ν := by
  obtain ⟨w, hw0, hw⟩ := μ
  obtain ⟨w', hw0', hw'⟩ := ν
  have h1 : w default = 1 := by simpa only [Fintype.sum_unique] using hw
  have h2 : w' default = 1 := by simpa only [Fintype.sum_unique] using hw'
  have he : w = w' := by
    funext x
    rw [Unique.eq_default x, h1, h2]
  subst he
  rfl

/-- **A toy five-type datum** on a one-point row space: point masses and unit kernels. -/
noncomputable def toyDatum (𝔛 : Type*) [Fintype 𝔛] [DecidableEq 𝔛] [Unique 𝔛] : Datum 𝔛 where
  nu := pt 𝔛
  nub _ := pt 𝔛
  Gam := pt (Fin 2 → 𝔛)
  Gam_weight _ := by simp [pt]
  Gam_symm _ := rfl
  piE := pt (Fin 3 → 𝔛)
  TE _ _ _ := 1
  TE_nonneg _ _ _ := zero_le_one
  piE_weight _ := by simp [pt]
  piE_exch _ _ := rfl
  piF := pt (Fin 3 → 𝔛)
  TF _ _ _ := 1
  TF_nonneg _ _ _ := zero_le_one
  piF_weight _ := by simp [pt]
  piL := pt (ZMod 6 → 𝔛)
  piL_inv _ _ := rfl

/-- **On one-point labels every functional with `L 𝟙 ≥ 0` is positive at every cut.** -/
theorem positive_of_subsingleton {V A : Type*} [Fintype V] [DecidableEq V] [Unique A]
    (c : ReflectionCut V) (L : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (hL : 0 ≤ L (fun _ => 1)) :
    c.Positive L := by
  have hform : ∀ F G : (c.Half → A) → ℝ,
      c.form L F G = F (fun _ => default) * G (fun _ => default) * L (fun _ => 1) := by
    intro F G
    have hfun : (fun z : V → A => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) =
        (F (fun _ => default) * G (fun _ => default)) • (fun _ : V → A => (1 : ℝ)) := by
      funext z
      have h1 : (fun v : c.Half => z v.1) = fun _ => default := Subsingleton.elim _ _
      have h2 : (fun v : c.Half => z (c.flip v.1)) = fun _ => default := Subsingleton.elim _ _
      simp only [h1, h2, Pi.smul_apply, smul_eq_mul, mul_one]
    change L (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) = _
    rw [hfun, L.map_smul, smul_eq_mul]
  constructor
  · intro F G
    rw [hform, hform]
    ring
  · intro F
    rw [hform]
    exact mul_nonneg (mul_self_nonneg _) hL

theorem lawL_nonneg {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) {g : Ω → ℝ} (hg : ∀ z, 0 ≤ g z) :
    0 ≤ lawL μ g :=
  μ.expect_nonneg hg

/-- `π_t` is a nonnegative measure. -/
theorem Datum.piT_nonneg {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛) (t : Ty)
    {f : (ZMod 6 → 𝔛) → ℝ} (hf : ∀ z, 0 ≤ f z) : 0 ≤ D.piT t f := by
  cases t with
  | L => exact lawL_nonneg _ hf
  | D =>
    change 0 ≤ (∑ j, D.compF j) f
    rw [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun j _ => lawL_nonneg _ hf
  | S =>
    change 0 ≤ (∑ s, D.compE s) f
    rw [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun s _ => lawL_nonneg _ hf
  | R =>
    change 0 ≤ (∑ s, ∑ k, D.compG s k) f
    rw [LinearMap.sum_apply]
    refine Finset.sum_nonneg fun s _ => ?_
    rw [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun k _ => lawL_nonneg _ hf
  | C =>
    change 0 ≤ (∑ _k : Fin 2, D.compC) f
    rw [LinearMap.sum_apply]
    exact Finset.sum_nonneg fun k _ => lawL_nonneg _ hf

/-- **A five-type measure with nonnegative weights is a nonnegative measure.** -/
theorem Datum.Q_nonneg {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛) {a : Ty → ℝ}
    (ha : ∀ t, 0 ≤ a t) {f : (ZMod 6 → 𝔛) → ℝ} (hf : ∀ z, 0 ≤ f z) : 0 ≤ D.Q a f := by
  change 0 ≤ (∑ t, a t • D.piT t) f
  rw [LinearMap.sum_apply]
  exact Finset.sum_nonneg fun t _ => mul_nonneg (ha t) (Datum.piT_nonneg D t hf)

/-! ## The toy two-coordinate instance -/

/-- The toy field laws: one label, so point masses. -/
noncomputable def toyLam (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (f0 f1 : FieldTy) :
    FiniteLaw (f0.Obj × f1.Obj × Λ → Unit) :=
  pt _

/-- **Non-vacuity of `lem:five-type`(d)**: for one label and nonnegative weights, the toy row
data form five-type data in both coordinates (`RowDatum0`, `RowDatum1`), and every row five-type
measure is reflection positive at every chamber cut. So `two_coordinate_rp` applies. -/
theorem toy_two_coordinate (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (a : Ty → Ty → ℝ)
    (ha : ∀ t0 t1, 0 ≤ a t0 t1) :
    (∀ f', RowDatum0 (toyLam Λ) f' (toyDatum (f'.Obj × Λ → Unit))) ∧
    (∀ f', RowDatum1 (toyLam Λ) f' (toyDatum (f'.Obj × Λ → Unit))) ∧
    (∀ t1, RPAll ((toyDatum ((fieldOf t1).Obj × Λ → Unit)).Q (fun t0 => a t0 t1))) ∧
    (∀ t0, RPAll ((toyDatum ((fieldOf t0).Obj × Λ → Unit)).Q (fun t1 => a t0 t1))) ∧
    ∀ i : ZMod 6,
      (cut0 Λ i).Positive (Q2 (toyLam Λ) a) ∧ (cut1 Λ i).Positive (Q2 (toyLam Λ) a) := by
  have hrow0 : ∀ f', RowDatum0 (toyLam Λ) f' (toyDatum (f'.Obj × Λ → Unit)) := fun _ =>
    ⟨law_eq_of_unique _ _, law_eq_of_unique _ _, law_eq_of_unique _ _, law_eq_of_unique _ _,
      law_eq_of_unique _ _⟩
  have hrow1 : ∀ f', RowDatum1 (toyLam Λ) f' (toyDatum (f'.Obj × Λ → Unit)) := fun _ =>
    ⟨law_eq_of_unique _ _, law_eq_of_unique _ _, law_eq_of_unique _ _, law_eq_of_unique _ _,
      law_eq_of_unique _ _⟩
  have hrp0 : ∀ t1, RPAll ((toyDatum ((fieldOf t1).Obj × Λ → Unit)).Q (fun t0 => a t0 t1)) :=
    fun t1 i => positive_of_subsingleton _ _
      (Datum.Q_nonneg _ (fun t0 => ha t0 t1) fun _ => zero_le_one)
  have hrp1 : ∀ t0, RPAll ((toyDatum ((fieldOf t0).Obj × Λ → Unit)).Q (fun t1 => a t0 t1)) :=
    fun t0 i => positive_of_subsingleton _ _
      (Datum.Q_nonneg _ (fun t1 => ha t0 t1) fun _ => zero_le_one)
  exact ⟨hrow0, hrow1, hrp0, hrp1,
    two_coordinate_rp (toyLam Λ) a _ _ hrow0 hrow1 hrp0 hrp1⟩

/-- The toy two-coordinate measures are nonnegative. -/
theorem toy_Q2_nonneg (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (b : Ty → Ty → ℝ)
    (hb : ∀ t0 t1, 0 ≤ b t0 t1) : 0 ≤ Q2 (toyLam Λ) b (fun _ => 1) := by
  change 0 ≤ (∑ t0, ∑ t1, b t0 t1 • piT2 (toyLam Λ) t0 t1) (fun _ => 1)
  simp only [piT2, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  exact Finset.sum_nonneg fun t0 _ => Finset.sum_nonneg fun t1 _ =>
    mul_nonneg (hb t0 t1) (Finset.sum_nonneg fun φ0 _ => Finset.sum_nonneg fun φ1 _ =>
      comp_nonneg _ t0 φ0 t1 φ1 _ fun _ => zero_le_one)

/-- The toy two-coordinate measures are reflection positive at every chamber cut. -/
theorem toy_Q2_rp (Λ : Type*) [Fintype Λ] [DecidableEq Λ] (b : Ty → Ty → ℝ)
    (hb : ∀ t0 t1, 0 ≤ b t0 t1) (i : ZMod 6) :
    (cut0 Λ i).Positive (Q2 (toyLam Λ) b) ∧ (cut1 Λ i).Positive (Q2 (toyLam Λ) b) :=
  ⟨positive_of_subsingleton _ _ (toy_Q2_nonneg Λ b hb),
    positive_of_subsingleton _ _ (toy_Q2_nonneg Λ b hb)⟩

/-- The toy components satisfy the bound of (e) at `ι` for every `k r ≥ 0`. -/
theorem toy_comp_below (t0 : Ty) (φ0 : PatIdx t0) (t1 : Ty) (φ1 : PatIdx t1) {c : ℝ}
    (hc : 0 ≤ c) :
    reservedCut.Below (-c • pushFunctional (comp (toyLam Unit) t0 φ0 t1 φ1) diagW)
      (comp (toyLam (ZMod 2)) t0 φ0 t1 φ1) := by
  refine positive_of_subsingleton _ _ ?_
  have h2 := comp_nonneg (toyLam (ZMod 2)) t0 φ0 t1 φ1 (fun _ => (1 : ℝ)) fun _ => zero_le_one
  have h1 := comp_nonneg (toyLam Unit) t0 φ0 t1 φ1 ((fun _ => (1 : ℝ)) ∘ diagW)
    fun _ => zero_le_one
  change 0 ≤ comp (toyLam (ZMod 2)) t0 φ0 t1 φ1 (fun _ => 1) -
    -c * comp (toyLam Unit) t0 φ0 t1 φ1 ((fun _ => (1 : ℝ)) ∘ diagW)
  nlinarith

/-- **Non-vacuity of `lem:five-type`(e)**: for one label, `w, k ≥ 0`, `v = k w` and `r ≥ 0`,
every hypothesis of `reserved_rp_two` holds for the toy two-layer and one-layer field laws. -/
theorem toy_reserved (w k : Ty → Ty → ℝ) (hw : ∀ t0 t1, 0 ≤ w t0 t1)
    (hk : ∀ t0 t1, 0 ≤ k t0 t1) {r : ℝ} (hr : 0 ≤ r) :
    (∀ t0 (φ0 : PatIdx t0) t1 (φ1 : PatIdx t1),
      reservedCut.Below
        (-(k t0 t1 * r) • pushFunctional (comp (toyLam Unit) t0 φ0 t1 φ1) diagW)
        (comp (toyLam (ZMod 2)) t0 φ0 t1 φ1)) ∧
    (∀ i, (cut0 (ZMod 2) i).Positive
        (Q2 (toyLam (ZMod 2)) (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1)) ∧
      (cut1 (ZMod 2) i).Positive
        (Q2 (toyLam (ZMod 2)) (fun t0 t1 => w t0 t1 * r ^ stateDeg t0 t1))) ∧
    (∀ i, (cut0 Unit i).Positive
        (Q2 (toyLam Unit) (fun t0 t1 => k t0 t1 * w t0 t1 * r ^ stateDeg t0 t1)) ∧
      (cut1 Unit i).Positive
        (Q2 (toyLam Unit) (fun t0 t1 => k t0 t1 * w t0 t1 * r ^ stateDeg t0 t1))) :=
  ⟨fun t0 φ0 t1 φ1 => toy_comp_below t0 φ0 t1 φ1 (mul_nonneg (hk t0 t1) hr),
    toy_Q2_rp (ZMod 2) _ fun t0 t1 => mul_nonneg (hw t0 t1) (pow_nonneg hr _),
    toy_Q2_rp Unit _ fun t0 t1 =>
      mul_nonneg (mul_nonneg (hk t0 t1) (hw t0 t1)) (pow_nonneg hr _)⟩

/-- The toy instance of the conclusion of (e). -/
theorem toy_reserved_rp (w k : Ty → Ty → ℝ) (hw : ∀ t0 t1, 0 ≤ w t0 t1)
    (hk : ∀ t0 t1, 0 ≤ k t0 t1) {r : ℝ} (hr : 0 ≤ r) :
    (∀ i, (cut0 (ZMod 2) i).Positive
        (pairedMeasure (toyLam (ZMod 2)) (toyLam Unit) w (fun t0 t1 => k t0 t1 * w t0 t1) r) ∧
      (cut1 (ZMod 2) i).Positive
        (pairedMeasure (toyLam (ZMod 2)) (toyLam Unit) w (fun t0 t1 => k t0 t1 * w t0 t1) r)) ∧
    reservedCut.Positive
      (pairedMeasure (toyLam (ZMod 2)) (toyLam Unit) w (fun t0 t1 => k t0 t1 * w t0 t1) r) := by
  obtain ⟨hcomp, h2, h1⟩ := toy_reserved w k hw hk hr
  exact reserved_rp_two _ _ w _ k hr hw (fun _ _ => le_rfl) hcomp h2 h1

/-- **Non-vacuity of `lem:five-type`(e), one coordinate**: for one label, `w, k, r ≥ 0` and
`v = k w`, every hypothesis of `reserved_rp_one` holds for the toy two-layer and one-layer data,
and so does its conclusion. -/
theorem toy_reserved_one (w k : Ty → ℝ) (hw : ∀ t, 0 ≤ w t) (hk : ∀ t, 0 ≤ k t) {r : ℝ}
    (hr : 0 ≤ r) :
    (∀ t (φ : PatIdx t), (resCut (ZMod 6)).Below
      (-(k t * r) • pushFunctional (dcomp (toyDatum Unit) t φ) diag1)
      (pushFunctional (dcomp (toyDatum (ZMod 2 → Unit)) t φ) unc)) ∧
    RPAll ((toyDatum (ZMod 2 → Unit)).Q (fun t => w t * r ^ t.deg)) ∧
    RPAll ((toyDatum Unit).Q (fun t => k t * w t * r ^ t.deg)) ∧
    (∀ i, (chamberCut2 i).Positive
      (pairedMeasure1 (toyDatum (ZMod 2 → Unit)) (toyDatum Unit) w (fun t => k t * w t) r)) ∧
    (resCut (ZMod 6)).Positive
      (pairedMeasure1 (toyDatum (ZMod 2 → Unit)) (toyDatum Unit) w (fun t => k t * w t) r) := by
  have hcomp : ∀ t (φ : PatIdx t), (resCut (ZMod 6)).Below
      (-(k t * r) • pushFunctional (dcomp (toyDatum Unit) t φ) diag1)
      (pushFunctional (dcomp (toyDatum (ZMod 2 → Unit)) t φ) unc) := by
    intro t φ
    refine positive_of_subsingleton _ _ ?_
    have h2 := dcomp_nonneg (toyDatum (ZMod 2 → Unit)) t φ
      (f := (fun _ => (1 : ℝ)) ∘ unc) fun _ => zero_le_one
    have h1 := dcomp_nonneg (toyDatum Unit) t φ (f := (fun _ => (1 : ℝ)) ∘ diag1)
      fun _ => zero_le_one
    have hkr : 0 ≤ k t * r := mul_nonneg (hk t) hr
    change 0 ≤ dcomp (toyDatum (ZMod 2 → Unit)) t φ ((fun _ => (1 : ℝ)) ∘ unc) -
      -(k t * r) * dcomp (toyDatum Unit) t φ ((fun _ => (1 : ℝ)) ∘ diag1)
    nlinarith
  have h2 : RPAll ((toyDatum (ZMod 2 → Unit)).Q (fun t => w t * r ^ t.deg)) := fun i =>
    positive_of_subsingleton _ _
      (Datum.Q_nonneg _ (fun t => mul_nonneg (hw t) (pow_nonneg hr _)) fun _ => zero_le_one)
  have h1 : RPAll ((toyDatum Unit).Q (fun t => k t * w t * r ^ t.deg)) := fun i =>
    positive_of_subsingleton _ _
      (Datum.Q_nonneg _ (fun t => mul_nonneg (mul_nonneg (hk t) (hw t)) (pow_nonneg hr _))
        fun _ => zero_le_one)
  obtain ⟨hch, hres⟩ := reserved_rp_one (toyDatum (ZMod 2 → Unit)) (toyDatum Unit) w
    (fun t => k t * w t) k hr hw (fun _ => le_rfl) hcomp h2 h1
  exact ⟨hcomp, h2, h1, hch, hres⟩

end TwoCoordSanity

end Sarkozy.FiveType

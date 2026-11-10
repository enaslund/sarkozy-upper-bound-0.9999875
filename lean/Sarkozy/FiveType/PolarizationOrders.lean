module

public import Sarkozy.FiveType.Criteria

/-!
# Polarization for a five-type datum (`lem:tr:polarization`, the inequality, (a) and (b))

Source: `paper/sections/17_completion_repair.tex`, `lem:tr:polarization` and its proof.

* `polarization_form`: **`eq:polarization`** in the norm convention of `FiveType/Datum.lean`:
  `⟨U, T_E U⟩ + ⟨V, T_E' V⟩ - 2⟨U, T_F V⟩ ≥ (u - v)² - (e_F + e_E)(‖U‖² + ‖V‖²)`.
  (WP-R's `Structured.polarization` is the same inequality in an inner product space.)
* `Datum.polarization_a`: **(a)**
  `Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o}) ⪰_{ϑ₀} Π_{F_1} + Π_{F_2}`
  for `ε ≥ e_F + e_E`.
* `Datum.polarization_b`: **(b)**, the two orders
  `Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o}) ⪰_{ϑ₀} ±(Π_{F_1} + Π_{F_2})`, and
  `Datum.polarization_b_diag`: the diagonal blocks `Π_{E_0} + εΠ_{G_e}` and `Π_{E_1} + εΠ_{G_o}`
  are positive at `ϑ₀` ("in particular `A, D ⪰ 0`").

**Remark on the hypothesis of (b).** The paper assumes `ν^b({b}) = 0` for `b ∈ supp ν` and
proves the lower sign through `g̃` (`g` on `𝒰`, `-g` on `𝒱`). The formal proof does not need
this hypothesis for the two orders: the cut forms of (a) hold for every `g`, and
`eq:polarization` applied to `(U_b, -V_b)` bounds the form of the lower-sign order below by
`E_b(u_b + v_b)² ≥ 0`. The hypothesis is what places the cut matrices on the corner blocks
`𝒰 × 𝒰`, `𝒱 × 𝒱`, `𝒰 × 𝒱`, i.e. the block-matrix reformulation of (b) used in (c); that
reformulation and (c) (tensor products over blocks, `lem:record:block-gram`) are not formalized
here. Part (d) is WP-R's `Structured/Polarization.lean`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings

variable {𝔛 : Type*} [Fintype 𝔛]

/-- A norm bound is nonnegative (test it on `Φ = Ψ = 𝟙`). -/
theorem NormBound.nonneg {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} {e : ℝ} (h : NormBound μ T e) :
    0 ≤ e := by
  have h11 := h (fun _ => 1) (fun _ => 1)
  have hn : nrm μ (fun _ => (1 : ℝ)) = 1 := by
    unfold nrm ip
    simp only [mul_one, FiniteLaw.expect_const, Real.sqrt_one]
  rw [hn, mul_one, mul_one] at h11
  exact le_trans (abs_nonneg _) h11

/-- **`eq:polarization`**, form version. -/
theorem polarization_form {μ : FiniteLaw 𝔛} {TF TE TE' : 𝔛 → 𝔛 → ℝ} {eF eE : ℝ}
    (hF : NormBound μ TF eF) (hE : NormBound μ TE eE) (hE' : NormBound μ TE' eE)
    (U V : 𝔛 → ℝ) :
    (μ.expect U - μ.expect V) ^ 2 - (eF + eE) * (ip μ U U + ip μ V V) ≤
      kf μ TE U U + kf μ TE' V V - 2 * kf μ TF U V := by
  have heF := hF.nonneg
  have k1 := hE.lower U U
  have k2 := hE'.lower V V
  have k3 : kf μ TF U V - μ.expect U * μ.expect V ≤ eF * nrm μ U * nrm μ V :=
    (le_abs_self _).trans (hF U V)
  have hU := ip_self_eq μ U
  have hV := ip_self_eq μ V
  have hnU := nrm_nonneg μ U
  have hnV := nrm_nonneg μ V
  have t4 : 2 * (eF * nrm μ U * nrm μ V) ≤ eF * (nrm μ U ^ 2 + nrm μ V ^ 2) := by
    have h0 := mul_nonneg heF (sq_nonneg (nrm μ U - nrm μ V))
    have : eF * (nrm μ U - nrm μ V) ^ 2 =
        eF * (nrm μ U ^ 2 + nrm μ V ^ 2) - 2 * (eF * nrm μ U * nrm μ V) := by ring
    linarith
  rw [hU, hV]
  nlinarith [k1, k2, k3, t4]

/-- `kf` is bilinear: negating the right argument negates the form. -/
theorem kf_neg_right (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (U V : 𝔛 → ℝ) :
    kf μ T U (fun y => -V y) = -kf μ T U V := by
  simp only [kf, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem kf_neg_neg (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (V : 𝔛 → ℝ) :
    kf μ T (fun x => -V x) (fun y => -V y) = kf μ T V V := by
  simp only [kf]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

namespace Datum

variable [DecidableEq 𝔛] (D : Datum 𝔛)

/-- `Π_{G_e}` and `Π_{G_o}` are fixed by `ϑ₀` (`lem:record:fold-identification`(e)). -/
theorem compG_diag_flip_inv (f : (ZMod 6 → 𝔛) → ℝ) :
    D.compG 0 0 (fun z => f (z ∘ (chamberCut 0).flip)) = D.compG 0 0 f ∧
      D.compG 1 1 (fun z => f (z ∘ (chamberCut 0).flip)) = D.compG 1 1 f := by
  simp only [compG, lawL_pattern]
  have h5 : ∀ u, (chamberCut 0).flip u = chamberRefl 5 u := fun u => by
    rw [← g6_five_eq_flip]; revert u; decide
  constructor
  · refine D.Gam.expect_congr fun ω => ?_
    congr 1
    funext u
    simp only [Function.comp_apply, h5]
    exact congrArg ω (fixed_reflections u).2.1
  · refine D.Gam.expect_congr fun ω => ?_
    congr 1
    funext u
    simp only [Function.comp_apply, h5]
    exact congrArg ω (fixed_reflections u).2.2.1

/-- `ϑ₀` exchanges `Π_{F_1}` and `Π_{F_2}` (`lem:record:fold-identification`(e)). -/
theorem compF12_flip (f : (ZMod 6 → 𝔛) → ℝ) :
    D.compF 1 (fun z => f (z ∘ (chamberCut 0).flip)) = D.compF 2 f ∧
      D.compF 2 (fun z => f (z ∘ (chamberCut 0).flip)) = D.compF 1 f := by
  simp only [compF, lawL_pattern]
  have h5 : ∀ u, (chamberCut 0).flip u = chamberRefl 5 u := fun u => by
    rw [← g6_five_eq_flip]; revert u; decide
  constructor
  · refine D.piF.expect_congr fun ω => ?_
    congr 1
    funext u
    simp only [Function.comp_apply, h5]
    exact congrArg ω (fold_refl5 u).2.1
  · refine D.piF.expect_congr fun ω => ?_
    congr 1
    funext u
    simp only [Function.comp_apply, h5]
    exact congrArg ω (fold_refl5 u).2.2

/-- The matching side `𝒬^E_ε = Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o})`. -/
noncomputable def QE (ε : ℝ) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ :=
  D.compE 0 + D.compE 1 + ε • (D.compG 0 0 + D.compG 1 1)

/-- The fold side `𝒬^F = Π_{F_1} + Π_{F_2}`. -/
noncomputable def QF : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ := D.compF 1 + D.compF 2

theorem QE_flip_inv (ε : ℝ) (f : (ZMod 6 → 𝔛) → ℝ) :
    D.QE ε (fun z => f (z ∘ (chamberCut 0).flip)) = D.QE ε f := by
  simp only [QE, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [flip_inv_of_inv6 (D.compE_inv6 0), flip_inv_of_inv6 (D.compE_inv6 1),
    (D.compG_diag_flip_inv f).1, (D.compG_diag_flip_inv f).2]

theorem QF_flip_inv (f : (ZMod 6 → 𝔛) → ℝ) :
    D.QF (fun z => f (z ∘ (chamberCut 0).flip)) = D.QF f := by
  simp only [QF, LinearMap.add_apply]
  rw [(D.compF12_flip f).1, (D.compF12_flip f).2, add_comm]

/-- The cut forms of the two sides at `ϑ₀` (`lem:five-type`(a)). -/
theorem form_QE (ε : ℝ) (G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.QE ε) G G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Uf G b) (Uf G b) +
        kf (D.nub b) (D.TE b) (Vf G b) (Vf G b) +
        ε * (ip (D.nub b) (Uf G b) (Uf G b) + ip (D.nub b) (Vf G b) (Vf G b))) := by
  simp only [QE, form_add, form_smul]
  rw [D.form_E0, D.form_E1, D.form_G00, D.form_G11]
  simp only [FiniteLaw.expect_add, FiniteLaw.expect_const_mul]

theorem form_QF (G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form D.QF G G =
      D.nu.expect (fun b => 2 * kf (D.nub b) (D.TF b) (Uf G b) (Vf G b)) := by
  simp only [QF, form_add]
  rw [D.form_F1, D.form_F2, FiniteLaw.expect_const_mul]
  ring

/-- **`lem:tr:polarization`(a)**:
`Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o}) ⪰_{ϑ₀} Π_{F_1} + Π_{F_2}`
when `‖T_F^b - J‖ ≤ e_F`, `‖T_E^b - J‖ ≤ e_E` on `supp ν` and `ε ≥ e_F + e_E`. -/
theorem polarization_a {eF eE ε : ℝ}
    (hF : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TF b) eF)
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) eE) (hε : eF + eE ≤ ε) :
    (chamberCut 0).Below D.QF (D.QE ε) := by
  constructor
  · intro F G
    refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
    simp only [LinearMap.sub_apply]
    rw [D.QE_flip_inv, D.QF_flip_inv]
  · intro G
    change 0 ≤ (chamberCut 0).form (D.QE ε - D.QF) G G
    rw [form_sub, form_QE, form_QF, ← FiniteLaw.expect_sub]
    refine expect_nonneg_supp D.nu fun b hb => ?_
    have hp := polarization_form (hF b hb) (hE b hb) (hE b hb) (Uf G b) (Vf G b)
    have hU := ip_self_eq (D.nub b) (Uf G b)
    have hV := ip_self_eq (D.nub b) (Vf G b)
    have h0 : 0 ≤ (ε - (eF + eE)) * (ip (D.nub b) (Uf G b) (Uf G b) +
        ip (D.nub b) (Vf G b) (Vf G b)) := by
      rw [hU, hV]; exact mul_nonneg (by linarith) (by positivity)
    nlinarith [sq_nonneg ((D.nub b).expect (Uf G b) - (D.nub b).expect (Vf G b))]

/-- **`lem:tr:polarization`(b), the two orders**:
`Π_{E_0} + Π_{E_1} + ε(Π_{G_e} + Π_{G_o}) ⪰_{ϑ₀} ±(Π_{F_1} + Π_{F_2})`. The paper's hypothesis
`ν^b({b}) = 0` is not needed for the orders (see the module docstring). -/
theorem polarization_b {eF eE ε : ℝ}
    (hF : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TF b) eF)
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) eE) (hε : eF + eE ≤ ε) :
    (chamberCut 0).Below D.QF (D.QE ε) ∧ (chamberCut 0).Below (-D.QF) (D.QE ε) := by
  refine ⟨D.polarization_a hF hE hε, ?_⟩
  constructor
  · intro F G
    refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
    simp only [LinearMap.sub_apply, LinearMap.neg_apply]
    rw [D.QE_flip_inv, D.QF_flip_inv]
  · intro G
    change 0 ≤ (chamberCut 0).form (D.QE ε - -D.QF) G G
    rw [sub_neg_eq_add, form_add, form_QE, form_QF, ← FiniteLaw.expect_add]
    refine expect_nonneg_supp D.nu fun b hb => ?_
    have hp := polarization_form (hF b hb) (hE b hb) (hE b hb) (Uf G b) (fun y => -Vf G b y)
    rw [kf_neg_neg, kf_neg_right] at hp
    have hip : ip (D.nub b) (fun y => -Vf G b y) (fun y => -Vf G b y) =
        ip (D.nub b) (Vf G b) (Vf G b) :=
      (D.nub b).expect_congr fun y => by ring
    have hmean : (D.nub b).expect (fun y => -Vf G b y) = -(D.nub b).expect (Vf G b) := by
      rw [show (fun y => -Vf G b y) = fun y => (-1) * Vf G b y from funext fun y => by ring,
        FiniteLaw.expect_const_mul]
      ring
    rw [hip, hmean] at hp
    have hU := ip_self_eq (D.nub b) (Uf G b)
    have hV := ip_self_eq (D.nub b) (Vf G b)
    have h0 : 0 ≤ (ε - (eF + eE)) * (ip (D.nub b) (Uf G b) (Uf G b) +
        ip (D.nub b) (Vf G b) (Vf G b)) := by
      rw [hU, hV]; exact mul_nonneg (by linarith) (by positivity)
    nlinarith [sq_nonneg ((D.nub b).expect (Uf G b) + (D.nub b).expect (Vf G b))]

/-- **`lem:tr:polarization`(b), "in particular `A, D ⪰ 0`"**: `Π_{E_0} + εΠ_{G_e}` and
`Π_{E_1} + εΠ_{G_o}` are positive at `ϑ₀` when `‖T_E^b - J‖ ≤ e_E` and `ε ≥ e_E`. -/
theorem polarization_b_diag {eE ε : ℝ}
    (hE : ∀ b, D.nu.weight b ≠ 0 → NormBound (D.nub b) (D.TE b) eE) (hε : eE ≤ ε) :
    (chamberCut 0).Positive (D.compE 0 + ε • D.compG 0 0) ∧
      (chamberCut 0).Positive (D.compE 1 + ε • D.compG 1 1) := by
  have key : ∀ b : 𝔛, D.nu.weight b ≠ 0 →
      ∀ Y : 𝔛 → ℝ, 0 ≤ kf (D.nub b) (D.TE b) Y Y + ε * ip (D.nub b) Y Y := by
    intro b hb Y
    have k := (hE b hb).lower Y Y
    have hY := ip_self_eq (D.nub b) Y
    have hn := nrm_nonneg (D.nub b) Y
    rw [hY]
    nlinarith [sq_nonneg ((D.nub b).expect Y)]
  refine ⟨⟨fun F G => ?_, fun G => ?_⟩, ⟨fun F G => ?_, fun G => ?_⟩⟩
  · refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [flip_inv_of_inv6 (D.compE_inv6 0), (D.compG_diag_flip_inv f).1]
  · rw [form_add, form_smul, D.form_E0, D.form_G00, ← FiniteLaw.expect_const_mul,
      ← FiniteLaw.expect_add]
    exact expect_nonneg_supp D.nu fun b hb => key b hb (Uf G b)
  · refine form_symm_of_flip_inv (chamberCut 0) (fun f => ?_) F G
    simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [flip_inv_of_inv6 (D.compE_inv6 1), (D.compG_diag_flip_inv f).2]
  · rw [form_add, form_smul, D.form_E1, D.form_G11, ← FiniteLaw.expect_const_mul,
      ← FiniteLaw.expect_add]
    exact expect_nonneg_supp D.nu fun b hb => key b hb (Vf G b)

end Datum

end Sarkozy.FiveType

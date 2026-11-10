module

public import Sarkozy.FiveType.PolarizationTensor

/-!
# The corner-block form of `lem:tr:polarization`(b)

Source: `paper/sections/17_completion_repair.tex`, `lem:tr:polarization`(b), the sentence
"Equivalently, with `A = C_{ϑ₀}(Π_{E_0} + εΠ_{G_e})`, `D = C_{ϑ₀}(Π_{E_1} + εΠ_{G_o})` and
`K = C_{ϑ₀}(Π_{F_1})`, viewed as matrices on `ℝ^{𝔛^{H_0}}` supported on the blocks `𝒰 × 𝒰`,
`𝒱 × 𝒱` and `𝒰 × 𝒱` respectively and zero elsewhere, both matrices `(A ±K; ±Kᵀ D)` on
`ℝ^𝒰 ⊕ ℝ^𝒱` are positive semidefinite; in particular `A, D ⪰ 0`".

Under the hypothesis of (b), `ν^b({b}) = 0` for `b ∈ supp ν`:
* `Datum.A_support`: the cut form of `Π_{E_0} + εΠ_{G_e}` vanishes when either argument vanishes on
  `𝒰 = {(b, y, y) : y ≠ b}`;
* `Datum.D_support`: that of `Π_{E_1} + εΠ_{G_o}` vanishes when either argument vanishes on
  `𝒱 = {(y, y, b) : y ≠ b}`;
* `Datum.K_support`: that of `Π_{F_1}` vanishes when its first argument vanishes on `𝒰` or its
  second
  on `𝒱`;
* `Datum.K_transpose` (no hypothesis): the cut matrix of `Π_{F_2}` is `Kᵀ`.

Positive semidefiniteness of `(A ±K; ±Kᵀ D)` on all half-functions is `Datum.bracket_F1` and
`Bracket.neg` (`PolarizationTensor.lean`); it holds without the hypothesis, and with the supports
above it is the paper's statement on `ℝ^𝒰 ⊕ ℝ^𝒱`. "In particular `A, D ⪰ 0`" is
`Datum.polarization_b_diag`.

The bilinear cut forms used here (`form_E0_bil`, `form_E1_bil`, `form_G00_bil`, `form_G11_bil`) are
those of `lem:five-type`(a) at two half-functions.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings

variable {𝔛 : Type*} [Fintype 𝔛]

/-- A form whose left argument vanishes on the support is zero. -/
theorem kf_eq_zero_left {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} {U V : 𝔛 → ℝ}
    (hU : ∀ x, μ.weight x ≠ 0 → U x = 0) : kf μ T U V = 0 := by
  unfold kf
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  by_cases hx : μ.weight x = 0
  · rw [hx, zero_mul, zero_mul]
  · rw [hU x hx, zero_mul, zero_mul, mul_zero]

/-- A form whose right argument vanishes on the support is zero. -/
theorem kf_eq_zero_right {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} {U V : 𝔛 → ℝ}
    (hV : ∀ y, μ.weight y ≠ 0 → V y = 0) : kf μ T U V = 0 := by
  unfold kf
  refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
  by_cases hy : μ.weight y = 0
  · rw [hy, mul_zero, zero_mul]
  · rw [hV y hy, mul_zero, mul_zero]

theorem ip_eq_zero_left {μ : FiniteLaw 𝔛} {U V : 𝔛 → ℝ}
    (hU : ∀ x, μ.weight x ≠ 0 → U x = 0) : ip μ U V = 0 :=
  (expect_congr_supp μ fun x hx => by rw [hU x hx, zero_mul]).trans (μ.expect_const 0)

theorem ip_eq_zero_right {μ : FiniteLaw 𝔛} {U V : 𝔛 → ℝ}
    (hV : ∀ x, μ.weight x ≠ 0 → V x = 0) : ip μ U V = 0 :=
  (expect_congr_supp μ fun x hx => by rw [hV x hx, mul_zero]).trans (μ.expect_const 0)

namespace Datum

variable [DecidableEq 𝔛] (D : Datum 𝔛)

/-! ## Bilinear cut forms -/

theorem form_E0_bil (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.compE 0) F G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Uf F b) (Uf G b)) := by
  unfold compE
  rw [form_pattern, expect_perm D.piE (Equiv.swap 0 1) (D.piE_exch _), expect_piE,
    ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : matching 0 0 = 0 ∧ matching 0 1 = 1 ∧ matching 0 2 = 1 ∧
      matching 0 5 = 0 ∧ matching 0 4 = 2 ∧ matching 0 3 = 2 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rfl

theorem form_E1_bil (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.compE 1) F G =
      D.nu.expect (fun b => kf (D.nub b) (D.TE b) (Vf F b) (Vf G b)) := by
  unfold compE
  rw [form_pattern, expect_piE, ← triple_kf]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : matching 1 0 = 0 ∧ matching 1 1 = 0 ∧ matching 1 2 = 1 ∧
      matching 1 5 = 2 ∧ matching 1 4 = 2 ∧ matching 1 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  rfl

theorem form_G00_bil (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.compG 0 0) F G =
      D.nu.expect (fun b => ip (D.nub b) (Uf F b) (Uf G b)) := by
  unfold compG
  rw [form_pattern, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 0 0 0 = 1 ∧ merge 0 0 1 = 0 ∧ merge 0 0 2 = 0 ∧
      merge 0 0 5 = 1 ∧ merge 0 0 4 = 0 ∧ merge 0 0 3 = 0 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  exact D.pair_expect (fun b x => Uf F b x * Uf G b x)

theorem form_G11_bil (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.compG 1 1) F G =
      D.nu.expect (fun b => ip (D.nub b) (Vf F b) (Vf G b)) := by
  unfold compG
  rw [form_pattern, expect_Gam]
  obtain ⟨h0, h1, h2, h5, h4, h3⟩ : merge 1 1 0 = 0 ∧ merge 1 1 1 = 0 ∧ merge 1 1 2 = 1 ∧
      merge 1 1 5 = 0 ∧ merge 1 1 4 = 0 ∧ merge 1 1 3 = 1 := by decide
  simp only [h0, h1, h2, h3, h4, h5]
  exact D.pair_expect (fun b x => Vf F b x * Vf G b x)

theorem form_QE0_bil (ε : ℝ) (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.QE0 ε) F G = D.nu.expect (fun b =>
      kf (D.nub b) (D.TE b) (Uf F b) (Uf G b) + ε * ip (D.nub b) (Uf F b) (Uf G b)) := by
  simp only [QE0, form_add, form_smul]
  rw [D.form_E0_bil, D.form_G00_bil, FiniteLaw.expect_add, FiniteLaw.expect_const_mul]

theorem form_QE1_bil (ε : ℝ) (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.QE1 ε) F G = D.nu.expect (fun b =>
      kf (D.nub b) (D.TE b) (Vf F b) (Vf G b) + ε * ip (D.nub b) (Vf F b) (Vf G b)) := by
  simp only [QE1, form_add, form_smul]
  rw [D.form_E1_bil, D.form_G11_bil, FiniteLaw.expect_add, FiniteLaw.expect_const_mul]

/-! ## The corner supports -/

/-- `g` vanishes on the corner `𝒰 = {(b, y, y) : y ≠ b}`. -/
def VanishesU (G : (Half0 → 𝔛) → ℝ) : Prop := ∀ b y : 𝔛, y ≠ b → G (hp b y y) = 0

/-- `g` vanishes on the corner `𝒱 = {(y, y, b) : y ≠ b}`. -/
def VanishesV (G : (Half0 → 𝔛) → ℝ) : Prop := ∀ b y : 𝔛, y ≠ b → G (hp y y b) = 0

omit [DecidableEq 𝔛] in
theorem Uf_supp {G : (Half0 → 𝔛) → ℝ} (hG : VanishesU G) {μ : FiniteLaw 𝔛} {b : 𝔛}
    (hb : μ.weight b = 0) : ∀ y, μ.weight y ≠ 0 → Uf G b y = 0 :=
  fun y hy => hG b y fun h => hy (h ▸ hb)

omit [DecidableEq 𝔛] in
theorem Vf_supp {G : (Half0 → 𝔛) → ℝ} (hG : VanishesV G) {μ : FiniteLaw 𝔛} {b : 𝔛}
    (hb : μ.weight b = 0) : ∀ y, μ.weight y ≠ 0 → Vf G b y = 0 :=
  fun y hy => hG b y fun h => hy (h ▸ hb)

/-- **`A` is supported on `𝒰 × 𝒰`** when `ν^b({b}) = 0` on `supp ν`. -/
theorem A_support (hsupp : ∀ b, D.nu.weight b ≠ 0 → (D.nub b).weight b = 0) (ε : ℝ)
    {F : (Half0 → 𝔛) → ℝ} (hF : VanishesU F) (G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.QE0 ε) F G = 0 ∧ (chamberCut 0).form (D.QE0 ε) G F = 0 := by
  rw [D.form_QE0_bil, D.form_QE0_bil]
  constructor
  · refine (expect_congr_supp D.nu fun b hb => ?_).trans (D.nu.expect_const 0)
    rw [kf_eq_zero_left (Uf_supp hF (hsupp b hb)), ip_eq_zero_left (Uf_supp hF (hsupp b hb)),
      mul_zero, add_zero]
  · refine (expect_congr_supp D.nu fun b hb => ?_).trans (D.nu.expect_const 0)
    rw [kf_eq_zero_right (Uf_supp hF (hsupp b hb)), ip_eq_zero_right (Uf_supp hF (hsupp b hb)),
      mul_zero, add_zero]

/-- **`D` is supported on `𝒱 × 𝒱`** when `ν^b({b}) = 0` on `supp ν`. -/
theorem D_support (hsupp : ∀ b, D.nu.weight b ≠ 0 → (D.nub b).weight b = 0) (ε : ℝ)
    {F : (Half0 → 𝔛) → ℝ} (hF : VanishesV F) (G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.QE1 ε) F G = 0 ∧ (chamberCut 0).form (D.QE1 ε) G F = 0 := by
  rw [D.form_QE1_bil, D.form_QE1_bil]
  constructor
  · refine (expect_congr_supp D.nu fun b hb => ?_).trans (D.nu.expect_const 0)
    rw [kf_eq_zero_left (Vf_supp hF (hsupp b hb)), ip_eq_zero_left (Vf_supp hF (hsupp b hb)),
      mul_zero, add_zero]
  · refine (expect_congr_supp D.nu fun b hb => ?_).trans (D.nu.expect_const 0)
    rw [kf_eq_zero_right (Vf_supp hF (hsupp b hb)), ip_eq_zero_right (Vf_supp hF (hsupp b hb)),
      mul_zero, add_zero]

/-- **`K` is supported on `𝒰 × 𝒱`** when `ν^b({b}) = 0` on `supp ν`. -/
theorem K_support (hsupp : ∀ b, D.nu.weight b ≠ 0 → (D.nub b).weight b = 0)
    {F G : (Half0 → 𝔛) → ℝ} (h : VanishesU F ∨ VanishesV G) :
    (chamberCut 0).form (D.compF 1) F G = 0 := by
  rw [D.form_F1_bil]
  refine (expect_congr_supp D.nu fun b hb => ?_).trans (D.nu.expect_const 0)
  rcases h with hF | hG
  · exact kf_eq_zero_left (Uf_supp hF (hsupp b hb))
  · exact kf_eq_zero_right (Vf_supp hG (hsupp b hb))

/-- **The cut matrix of `Π_{F_2}` is `Kᵀ`**: `Π_{F_2}` is the image of `Π_{F_1}` under `ϑ₀`. -/
theorem K_transpose (F G : (Half0 → 𝔛) → ℝ) :
    (chamberCut 0).form (D.compF 2) F G = (chamberCut 0).form (D.compF 1) G F :=
  form_of_flip_image (chamberCut 0) (fun f => ((D.compF12_flip f).1).symm) F G

end Datum

end Sarkozy.FiveType

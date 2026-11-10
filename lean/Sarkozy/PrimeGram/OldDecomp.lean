module

public import Sarkozy.PrimeGram.OldLaw

@[expose] public section

/-!
# `lem:old-f-law`(f): the actual centred remainder of the reference (PG)

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(a),(f) and the proof of (e),(f)
("The remainder"), with the constants of `eq:signed-constants`.

* **`z0_eq`**, **`z0_bounds`** (`lem:old-f-law`(a)):
  `z₀ = (p-3)(p-4)(p-5)(p-7)/(p(p-1)(p-2)²)` and `h₀ = 1 - 14q ≤ z₀ ≤ 1`.
* `oForm_sub_left`, `oForm_sub_right`: `O₀` is bilinear (through `oForm_eq_kernel`).
* **`oldDecomp_of_inputs`**: from `ABBound` (`lem:old-f-law`(b)(ii)) and `CollisionBound c_col`
  (`lem:record:conditional-collision`(d)), **`OldDecomp m₀ C₀ e_o`** with
  `e_o = r_o + n_o`, `r_o = 2/(Z(1 - e₀)) + c_col + c_g/q + (D_g/q) Γ r`,
  `n_o = (14/h₀)(Γ + r_o r) r`, `c_g = e₀²/(1 - e₀)²`, `D_g = (2e₀ + e₀²)/(1 - e₀)²`,
  `Z = (1 - q)(1 - 2q)`, `h₀ = 1 - 14q` (`eq:signed-constants`, with W6's `Γ ≤ Γ_A`).

The proof is the paper's: `O = Π_⊥ T_old Π_⊥ = z₀⁻¹ × (the centred operator of `Ψ₀`)`; the
constant kernel costs `c_g` (T3), `𝖫` gives `O₀` up to `D_g Γ r` (T2), `𝖠𝖡` costs
`2q/(Z(1 - e₀))` (T1), `𝖢_rem` costs `c_col q`; then `O = O₀ + R' + (z₀⁻¹ - 1)(O₀ + R')`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.PrimeGram

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents
  Sarkozy.SignedEstimates Sarkozy.MiddleRecords

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

local notation "qF" => (Fintype.card F : ℝ)

/-! ## The normalizer `z₀` -/

theorem z0_eq (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) (hR : ringChar F ≠ 2)
    (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F) :
    z0 (F := F) = (qF - 3) * (qF - 4) * (qF - 5) * (qF - 7) / (qF * (qF - 1) * (qF - 2) ^ 2) := by
  have _ := hF
  have h : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have h0 : qF ≠ 0 := by intro e; rw [e] at h; norm_num at h
  have h1 : qF - 1 ≠ 0 := by intro e; linarith
  have h2 : qF - 2 ≠ 0 := by intro e; linarith
  unfold z0 Icard
  rw [card_inj_val hR h3, Hcard_eq hR]
  field_simp
  ring

/-- **`h₀ = 1 - 14q ≤ z₀ ≤ 1`** (`lem:old-f-law`(a)). -/
theorem z0_bounds (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) (hR : ringChar F ≠ 2)
    (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F) :
    1 - 14 * qF⁻¹ ≤ z0 (F := F) ∧ z0 (F := F) ≤ 1 := by
  rw [z0_eq hF hR h3 h19]
  have h : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have h0 : (0 : ℝ) < qF := by linarith
  have hd : 0 < qF * (qF - 1) * (qF - 2) ^ 2 := by
    have : (0 : ℝ) < qF - 1 := by linarith
    have : (0 : ℝ) < qF - 2 := by linarith
    positivity
  constructor
  · rw [le_div_iff₀ hd]
    have e : (1 - 14 * qF⁻¹) * (qF * (qF - 1) * (qF - 2) ^ 2) =
        (qF - 14) * (qF - 1) * (qF - 2) ^ 2 := by field_simp
    rw [e]
    nlinarith [sq_nonneg (qF - 3)]
  · rw [div_le_one hd]
    nlinarith [sq_nonneg (qF - 5), mul_pos h0 h0]

/-! ## Bilinearity of `O₀` -/

theorem oForm_sub_left (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (m u u' v : (Fin 3 → F) → ℝ) :
    oForm m (fun x => u x - u' x) v = oForm m u v - oForm m u' v := by
  rw [oForm_eq_kernel hR h3, oForm_eq_kernel hR h3, oForm_eq_kernel hR h3, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun y _ => by ring

theorem oForm_sub_right (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (m u v v' : (Fin 3 → F) → ℝ) :
    oForm m u (fun x => v x - v' x) = oForm m u v - oForm m u v' := by
  rw [oForm_eq_kernel hR h3, oForm_eq_kernel hR h3, oForm_eq_kernel hR h3, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_sub_distrib]
  exact sum_congr rfl fun y _ => by ring

/-! ## The constants of `eq:signed-constants` -/

/-- `c_g = e₀²/(1 - e₀)²`. -/
noncomputable def cgC (e : ℝ) : ℝ := (e / (1 - e)) ^ 2

/-- `D_g = (2e₀ + e₀²)/(1 - e₀)²`. -/
noncomputable def DgC (e : ℝ) : ℝ := (2 * e + e ^ 2) / (1 - e) ^ 2

/-- `r_o = 2/(Z(1 - e₀)) + c_col + c_g/q + (D_g/q) Γ r`, `Z = (1 - q)(1 - 2q)`. -/
noncomputable def roC (q r e Γ ccol : ℝ) : ℝ :=
  2 / ((1 - q) * (1 - 2 * q) * (1 - e)) + ccol + cgC e / q + DgC e / q * Γ * r

/-- `n_o = (14/h₀)(Γ + r_o r) r`, `h₀ = 1 - 14q`. -/
noncomputable def noC (q r e Γ ccol : ℝ) : ℝ :=
  14 / (1 - 14 * q) * (Γ + roC q r e Γ ccol * r) * r

/-- `e_o = r_o + n_o` (`eq:signed-constants`). -/
noncomputable def eoC (q r e Γ ccol : ℝ) : ℝ := roC q r e Γ ccol + noC q r e Γ ccol

/-! ## Arithmetic of the constants -/

theorem dg_coef {e : ℝ} (he1 : e < 1) :
    e / (1 - e) * (1 / (1 - e)) + e / (1 - e) ≤ DgC e := by
  unfold DgC
  have h1e : 0 < 1 - e := by linarith
  have e6 : e / (1 - e) * (1 / (1 - e)) + e / (1 - e) = (2 * e - e ^ 2) / (1 - e) ^ 2 := by
    field_simp
    ring
  rw [e6]
  apply div_le_div_of_nonneg_right _ (by positivity)
  nlinarith [sq_nonneg e]

theorem ab_coef {q e N : ℝ} (hq : 0 < q) (hq1 : q ≤ 1 / 19) (he1 : e < 1)
    (hN : 0 ≤ N) :
    2 * q / (1 - q) * (1 / (1 - e) * N) ≤ 2 / ((1 - q) * (1 - 2 * q) * (1 - e)) * q * N := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  have h1e : 0 < 1 - e := by linarith
  have eL : 2 * q / (1 - q) * (1 / (1 - e) * N) = 2 * q * N / ((1 - q) * (1 - e)) := by
    field_simp
  have eR : 2 / ((1 - q) * (1 - 2 * q) * (1 - e)) * q * N =
      2 * q * N / ((1 - q) * (1 - 2 * q) * (1 - e)) := by
    field_simp
  rw [eL, eR]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  nlinarith [mul_pos h1 h1e]

theorem zinv_bound {z q : ℝ} (hh0 : 0 < 1 - 14 * q) (hz1 : 1 - 14 * q ≤ z) (hz2 : z ≤ 1) :
    0 ≤ z⁻¹ - 1 ∧ z⁻¹ - 1 ≤ 14 * q / (1 - 14 * q) := by
  have hz : 0 < z := lt_of_lt_of_le hh0 hz1
  refine ⟨by rw [sub_nonneg, one_le_inv₀ hz]; exact hz2, ?_⟩
  have e5 : z⁻¹ - 1 = (1 - z) / z := by field_simp
  rw [e5]
  have hq : 0 ≤ 14 * q := by linarith
  calc (1 - z) / z ≤ 14 * q / z := div_le_div_of_nonneg_right (by linarith) hz.le
    _ ≤ 14 * q / (1 - 14 * q) := div_le_div_of_nonneg_left hq hh0 hz1

theorem ro_split {q r e Γ ccol N : ℝ} (hq : q ≠ 0) :
    roC q r e Γ ccol * q * N = cgC e * N + DgC e * Γ * r * N +
      2 / ((1 - q) * (1 - 2 * q) * (1 - e)) * q * N + ccol * q * N := by
  unfold roC
  field_simp
  ring

theorem eo_split {q r e Γ ccol N : ℝ} (hqr : q = r * r) (hh0 : 1 - 14 * q ≠ 0) :
    eoC q r e Γ ccol * q * N = roC q r e Γ ccol * q * N +
      14 * q / (1 - 14 * q) * ((Γ * r + roC q r e Γ ccol * q) * N) := by
  unfold eoC noC
  generalize roC q r e Γ ccol = ro
  subst hqr
  field_simp

/-! ## The decomposition -/

section Decomp

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) (hR : ringChar F ≠ 2)
  (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F)

include hR h3 h19 in
/-- **`lem:old-f-law`(f)**, given `lem:old-f-law`(b)(ii) (`ABBound`) and
`lem:record:conditional-collision`(d) (`CollisionBound c_col`): `T_old = O₀ + R_o` on the
`m₀`-centred functions with `‖R_o‖ ≤ e_o q`, `e_o = r_o + n_o` of `eq:signed-constants`. -/
theorem oldDecomp_of_inputs {ccol : ℝ} (hAB : ABBound (F := F)) (hCC : CollisionBound hF ccol) :
    OldDecomp (m0 hF).weight (C0 hF)
      (eoC qF⁻¹ (√qF)⁻¹ (e0 qF) (gammaW (F := F)) ccol) := by
  intro f g hf hg
  set m := (m0 hF).weight with hm_def
  have hm : ∀ x, 0 ≤ m x := (m0 hF).nonneg
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have hq0 : (0 : ℝ) < qF := by linarith
  set q := qF⁻¹ with hq_def
  set r := (√qF)⁻¹ with hr_def
  set e := e0 qF with he_def
  set Γ := gammaW (F := F) with hΓ_def
  have hqpos : 0 < q := inv_pos.mpr hq0
  have hrpos : 0 < r := inv_pos.mpr (Real.sqrt_pos.mpr hq0)
  have hqr : q = r * r := by rw [hr_def, ← mul_inv, Real.mul_self_sqrt hq0.le]
  have hq19 : q ≤ 1 / 19 := by
    rw [hq_def, ← one_div]; exact one_div_le_one_div_of_le (by norm_num) h19'
  have he1 : e < 1 := e0_lt_one h19
  have he0 : 0 ≤ e := e0_nonneg h19
  have hΓ : 0 ≤ Γ := gammaW_nonneg (by linarith)
  have hframe : ∀ u, FrameAt m Γ u := fun u => frame_analysis hF hR h3 h19 u
  set Nf := √(mip m f f)
  set Ng := √(mip m g g)
  have hNf : 0 ≤ Nf := Real.sqrt_nonneg _
  have hNg : 0 ≤ Ng := Real.sqrt_nonneg _
  set N := Nf * Ng with hN_def
  have hN : 0 ≤ N := mul_nonneg hNf hNg
  set k := e / (1 - e) with hk_def
  have hk : 0 ≤ k := div_nonneg he0 (by linarith)
  -- the decomposition of the form
  set df := divG hF f
  set dg := divG hF g
  set X := Enu f * Enu g + oForm m df dg + E2 (fun x y => chA x y * chB x y) f g -
    E2 Crem f g with hX_def
  have hL : E2 (fun x y => chA x y + chB x y) f g = oForm m df dg := by
    rw [E2_eq_m hF hR h3 h19, oForm_eq_kernel hR h3]
    rfl
  have hdot : f ⬝ᵥ (C0 hF *ᵥ g) = (z0 (F := F))⁻¹ * X := by
    rw [dot_C0 hF hR h19, E2_split, hL]
  -- (T3) the constants
  have hJ : |Enu f * Enu g| ≤ cgC e * N := by
    rw [abs_mul]
    have h1 := Enu_centred hF hR h3 h19 f hf
    have h2 := Enu_centred hF hR h3 h19 g hg
    calc |Enu f| * |Enu g| ≤ (k * Nf) * (k * Ng) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg hk hNf)
      _ = cgC e * N := by unfold cgC; rw [hN_def]; ring
  -- norms of `f/g₀`
  have hdf_sub : √(mip m (fun x => df x - f x) (fun x => df x - f x)) ≤ k * Nf := by
    calc _ ≤ √(k ^ 2 * mip m f f) := Real.sqrt_le_sqrt (norm_divG_sub hF hR h3 h19 f)
      _ = k * Nf := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]
  have hdg_sub : √(mip m (fun x => dg x - g x) (fun x => dg x - g x)) ≤ k * Ng := by
    calc _ ≤ √(k ^ 2 * mip m g g) := Real.sqrt_le_sqrt (norm_divG_sub hF hR h3 h19 g)
      _ = k * Ng := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hk]
  have hinv : 0 ≤ 1 / (1 - e) := div_nonneg zero_le_one (by linarith)
  have hdg : √(mip m dg dg) ≤ 1 / (1 - e) * Ng := by
    calc _ ≤ √((1 / (1 - e)) ^ 2 * mip m g g) := Real.sqrt_le_sqrt (norm_divG hF hR h3 h19 g)
      _ = 1 / (1 - e) * Ng := by rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hinv]
  -- (T2) the leading kernel
  have hLd : |oForm m df dg - oForm m f g| ≤ DgC e * Γ * r * N := by
    have e1 : oForm m df dg - oForm m f g =
        oForm m (fun x => df x - f x) dg + oForm m f (fun x => dg x - g x) := by
      rw [oForm_sub_left hR h3, oForm_sub_right hR h3]
      ring
    rw [e1]
    have b1 := oForm_bound hm hΓ (hframe (fun x => df x - f x)) (hframe dg)
    have b2 := oForm_bound hm hΓ (hframe f) (hframe (fun x => dg x - g x))
    have hΓr : 0 ≤ Γ * r := mul_nonneg hΓ hrpos.le
    have c1 : |oForm m (fun x => df x - f x) dg| ≤ Γ * r * ((k * Nf) * (1 / (1 - e) * Ng)) :=
      b1.trans (mul_le_mul_of_nonneg_left (mul_le_mul hdf_sub hdg (Real.sqrt_nonneg _)
        (mul_nonneg hk hNf)) hΓr)
    have c2 : |oForm m f (fun x => dg x - g x)| ≤ Γ * r * (Nf * (k * Ng)) :=
      b2.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdg_sub hNf) hΓr)
    have hD : k * (1 / (1 - e)) + k ≤ DgC e := dg_coef he1
    calc _ ≤ |oForm m (fun x => df x - f x) dg| + |oForm m f (fun x => dg x - g x)| :=
          abs_add_le _ _
      _ ≤ Γ * r * ((k * Nf) * (1 / (1 - e) * Ng)) + Γ * r * (Nf * (k * Ng)) := add_le_add c1 c2
      _ = Γ * r * N * (k * (1 / (1 - e)) + k) := by rw [hN_def]; ring
      _ ≤ Γ * r * N * DgC e := mul_le_mul_of_nonneg_left hD (mul_nonneg hΓr hN)
      _ = DgC e * Γ * r * N := by ring
  -- (T1) the kernel `𝖠𝖡`
  have hABb : |E2 (fun x y => chA x y * chB x y) f g| ≤
      2 / ((1 - q) * (1 - 2 * q) * (1 - e)) * q * N := by
    have h1 := hAB f g
    have hs : ∀ u : (Fin 3 → F) → ℝ, √(Enu (fun x => u x ^ 2)) ≤
        √(1 / (1 - e)) * √(mip m u u) := by
      intro u
      rw [← Real.sqrt_mul hinv]
      apply Real.sqrt_le_sqrt
      rw [one_div_mul_eq_div]
      exact Enu_sq hF hR h3 h19 u
    have hsf := hs f
    have hsg := hs g
    have hss : √(1 / (1 - e)) * √(1 / (1 - e)) = 1 / (1 - e) := Real.mul_self_sqrt hinv
    have hprod : √(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2)) ≤ 1 / (1 - e) * N := by
      calc _ ≤ (√(1 / (1 - e)) * Nf) * (√(1 / (1 - e)) * Ng) :=
            mul_le_mul hsf hsg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) hNf)
        _ = 1 / (1 - e) * N := by
            rw [hN_def, show (√(1 / (1 - e)) * Nf) * (√(1 / (1 - e)) * Ng) =
              (√(1 / (1 - e)) * √(1 / (1 - e))) * (Nf * Ng) by ring, hss]
    have hq1 : 0 < 1 - q := by linarith
    have hq2 : 0 < 1 - 2 * q := by linarith
    have hc : 0 ≤ 2 * q / (1 - q) := by positivity
    calc _ ≤ 2 * q / (1 - q) * (√(Enu (fun x => f x ^ 2)) * √(Enu (fun x => g x ^ 2))) := h1
      _ ≤ 2 * q / (1 - q) * (1 / (1 - e) * N) := mul_le_mul_of_nonneg_left hprod hc
      _ ≤ 2 / ((1 - q) * (1 - 2 * q) * (1 - e)) * q * N := ab_coef hqpos hq19 he1 hN
  -- `c_col`
  have hCCb : |E2 Crem f g| ≤ ccol * q * N := hCC f g hf hg
  -- the remainder `R'`
  set ro := roC q r e Γ ccol with hro_def
  have hR' : |X - oForm m f g| ≤ ro * q * N := by
    have e1 : X - oForm m f g = Enu f * Enu g + (oForm m df dg - oForm m f g) +
        E2 (fun x y => chA x y * chB x y) f g - E2 Crem f g := by rw [hX_def]; ring
    rw [e1]
    have hro : ro * q * N = cgC e * N + DgC e * Γ * r * N +
        2 / ((1 - q) * (1 - 2 * q) * (1 - e)) * q * N + ccol * q * N := ro_split hqpos.ne'
    rw [hro]
    have t1 := abs_add_le (Enu f * Enu g + (oForm m df dg - oForm m f g) +
      E2 (fun x y => chA x y * chB x y) f g) (-E2 Crem f g)
    have t2 := abs_add_le (Enu f * Enu g + (oForm m df dg - oForm m f g))
      (E2 (fun x y => chA x y * chB x y) f g)
    have t3 := abs_add_le (Enu f * Enu g) (oForm m df dg - oForm m f g)
    rw [abs_neg] at t1
    rw [sub_eq_add_neg]
    linarith
  -- `|X| ≤ (Γ r + r_o q) N`
  have hO := oForm_bound hm hΓ (hframe f) (hframe g)
  have hXb : |X| ≤ (Γ * r + ro * q) * N := by
    have := abs_sub_abs_le_abs_sub X (oForm m f g)
    have e2 : Γ * (√qF)⁻¹ * N = Γ * r * N := rfl
    rw [e2] at hO
    nlinarith [abs_nonneg X]
  -- `z₀`
  obtain ⟨hz1, hz2⟩ := z0_bounds hF hR h3 h19
  have hh0 : 0 < 1 - 14 * q := by linarith
  obtain ⟨hzi0, hzi1⟩ := zinv_bound hh0 hz1 hz2
  -- assembly: `z₀⁻¹ X - O₀ = (X - O₀) + (z₀⁻¹ - 1) X`
  rw [hdot]
  have e3 : (z0 (F := F))⁻¹ * X - oForm m f g =
      (X - oForm m f g) + ((z0 (F := F))⁻¹ - 1) * X := by ring
  rw [e3]
  have t := abs_add_le (X - oForm m f g) (((z0 (F := F))⁻¹ - 1) * X)
  rw [abs_mul, abs_of_nonneg hzi0] at t
  have h5 : ((z0 (F := F))⁻¹ - 1) * |X| ≤ 14 * q / (1 - 14 * q) * ((Γ * r + ro * q) * N) :=
    mul_le_mul hzi1 hXb (abs_nonneg _) (by positivity)
  have e4 : eoC q r e Γ ccol * q * N =
      ro * q * N + 14 * q / (1 - 14 * q) * ((Γ * r + ro * q) * N) := eo_split hqr hh0.ne'
  rw [e4]
  linarith

end Decomp

end Sarkozy.PrimeGram

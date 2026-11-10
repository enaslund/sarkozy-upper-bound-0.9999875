module

public import Sarkozy.PartVRecords.Gram

@[expose] public section

/-!
# Middle prices (`lem:record:middle-prices`) and the two tags of `δ_E` (`def:record:frame`(e))

`paper/sections/20c_middle_frame.tex`, `subsec:middle-frame-prices`, `lem:record:middle-prices`,
`def:record:frame`(e), and the paragraph "(CP2)(b)" after `lem:record:one-stage-folded-e`.

For a block with least prime `b ≥ X > 3` and `r² = 1/b`, with selection factor `sel = q_𝔅^{2a} ≥ 0`
(`def:price`), the prices of the frame records are at most `sel` times:
* `Ñ₀ - μ`: `2 v_D r² + (2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X)) r³` (`price_Nbr0`, and `uprice_le`
  for the sum `∑_i mass(κu_i) sel` over the six records of `gram_cp3`);
* `F_fold + E_add + G`: `4 v_D r² + 2 v_D (f₁ + h₁) r³` (`price_first_stage`);
* `δ_E`, sharp: `2 (v_S + v_D) k r³` when each record difference has the sharp constant `k r`
  (`sharpPrice_deltaE`; in the paper `k = k_new(X)` of `lem:record:one-stage-folded-e`(d));
* `δ_E`, variation: `4 (v_S + v_D) r²` (`vprice_deltaE`);
and each of the two tags (`s = 0`, the records of type `E₀`, sharp at `ϑ₁`; `s = 1`, type `E₁`,
sharp at `ϑ₂`) carries exactly half of the last two prices (`tag_prices_equal`: the two records of
a block have the same mass and the same sharp constant).

The record differences of `δ_E` (`def:record:frame`(e), (CP2)(b)): `δ_E = ∑_s (κ'_s - κ_s)`
(`deltaE_eq_sum`), where `κ_s = (v_S + v_D) r² Diag_ι(Π⁽¹⁾_{E_s}) / P(r)` is the folded matching
record of type `E_s` of `E_fold + E_add` and `κ'_s` its replacement in `E_new`, of the same mass
(`oldRec_mass`, `newRecN_mass`); each difference has variation at most twice the mass
(`totalVar_sub_le`).

**Proved in full**, except that the sharp constant `k_new(X) b^{-1/2}` of each difference (part
(d)–(e) of `lem:record:one-stage-folded-e`) enters as the parameter `k`: the bound is stated for
the sharp price computed with any constant `k r`.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC Sarkozy.RecordExpansion

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The total mass of the density of a nonnegative measure is its mass. -/
theorem sum_lawDensity (κ : SlotMeasure X) : ∑ z, lawDensity κ z = mass κ := by
  unfold lawDensity mass
  rw [← map_sum]
  congr 1
  funext y
  rw [Finset.sum_apply]
  simp

theorem lawDensity_nonneg {κ : SlotMeasure X} (h : IsNonneg κ) (z : Slot → X) :
    0 ≤ lawDensity κ z :=
  h _ fun y => by split_ifs <;> norm_num

/-- **The variation of a difference of two nonnegative measures is at most the sum of their
masses** (`lem:record:one-stage-folded-e`(e): "by at most twice its mass in variation"). -/
theorem totalVar_sub_le {κ κ' : SlotMeasure X} (h : IsNonneg κ) (h' : IsNonneg κ') :
    totalVar (κ' - κ) ≤ mass κ + mass κ' := by
  unfold totalVar
  have hsplit : ∀ z, lawDensity (κ' - κ) z = lawDensity κ' z - lawDensity κ z := fun _ => rfl
  calc ∑ z, |lawDensity (κ' - κ) z| ≤ ∑ z, (lawDensity κ z + lawDensity κ' z) := by
        refine sum_le_sum fun z _ => ?_
        rw [hsplit, abs_le]
        have := lawDensity_nonneg h z
        have := lawDensity_nonneg h' z
        constructor <;> linarith
    _ = mass κ + mass κ' := by rw [sum_add_distrib, sum_lawDensity, sum_lawDensity]

namespace FrameData

variable (D : FrameData X)

/-- The folded matching record `κ_s` of type `E_s` in `E_fold + E_add`, divided by `P(r)`: mass
`(v_S + v_D) r² / P(r)`. -/
noncomputable def oldRec (s : Fin 2) : SlotMeasure X :=
  (D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2)) • D.diag .S s

/-- Its replacement `κ'_s` in `E_new`, divided by `P(r)`. -/
noncomputable def newRecN (s : Fin 2) : SlotMeasure X :=
  (D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2)) • D.newRec s

theorem recCoef_nonneg : 0 ≤ D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) :=
  mul_nonneg (inv_nonneg.mpr D.P_pos.le)
    (mul_nonneg (add_nonneg (D.W.v_nonneg _) (D.W.v_nonneg _)) (sq_nonneg _))

/-- **`δ_E = ∑_s (κ'_s - κ_s)`** (`def:record:frame`(e), (CP2)(b)). -/
theorem deltaE_eq_sum : D.deltaE = ∑ s, (D.newRecN s - D.oldRec s) := by
  rw [Fin.sum_univ_two]
  apply LinearMap.ext
  intro f
  simp only [deltaE, Enew, Efold, Eadd, newRecN, oldRec, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

theorem oldRec_mass (s : Fin 2) :
    mass (D.oldRec s) = D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) := by
  have h := D.diag_mass .S s
  unfold mass at h ⊢
  simp only [oldRec, LinearMap.smul_apply, smul_eq_mul, h, mul_one]

theorem newRecN_mass (s : Fin 2) :
    mass (D.newRecN s) = D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) := by
  have h := D.newRec_mass s
  unfold mass at h ⊢
  simp only [newRecN, LinearMap.smul_apply, smul_eq_mul, h, mul_one]

/-- The replaced and replacing records have equal mass (`def:cp2`(b)). -/
theorem newRecN_mass_eq (s : Fin 2) : mass (D.newRecN s) = mass (D.oldRec s) := by
  rw [D.newRecN_mass, D.oldRec_mass]

theorem oldRec_nonneg (s : Fin 2) : IsNonneg (D.oldRec s) :=
  nonneg_smul (D.diag_nonneg _ _) D.recCoef_nonneg

theorem newRecN_nonneg (s : Fin 2) : IsNonneg (D.newRecN s) :=
  nonneg_smul (D.newRec_nonneg _) D.recCoef_nonneg

/-- **Each record difference has variation at most twice its mass.** -/
theorem totalVar_recDiff (s : Fin 2) :
    totalVar (D.newRecN s - D.oldRec s) ≤ 2 * mass (D.oldRec s) := by
  have h := totalVar_sub_le (D.oldRec_nonneg s) (D.newRecN_nonneg s)
  rw [D.newRecN_mass_eq] at h
  linarith

/-- `r/(b - 3) ≤ r³/(1 - 3/X)` for `r² = 1/b` and `b ≥ X > 3`: the coefficient `3/(b - 3)` of `H`
is `3 r²/(1 - 3q) ≤ 3 r²/(1 - 3/X)`. -/
theorem r_div_le (hrb : D.r ^ 2 * D.b = 1) {Xs : ℝ} (hX : 3 < Xs) (hXb : Xs ≤ D.b) :
    D.r / (D.b - 3) ≤ D.r ^ 3 / (1 - 3 / Xs) := by
  have hb3 : 0 < D.b - 3 := by linarith
  have hb0 : 0 < D.b := by linarith
  have hX0 : 0 < Xs := by linarith
  have h1X : 0 < 1 - 3 / Xs := by
    rw [sub_pos, div_lt_one hX0]
    exact hX
  have hr := D.r_nonneg
  -- `r/(b - 3) = r³/(1 - 3/b)`
  have he : D.r / (D.b - 3) = D.r ^ 3 / (1 - 3 / D.b) := by
    have hbne : D.b ≠ 0 := hb0.ne'
    have h1b : 1 - 3 / D.b = (D.b - 3) / D.b := by field_simp
    rw [h1b, div_div_eq_mul_div]
    have h3 : D.r ^ 3 * D.b = D.r := by
      have : D.r ^ 3 * D.b = D.r * (D.r ^ 2 * D.b) := by ring
      rw [this, hrb, mul_one]
    rw [h3]
  rw [he]
  apply div_le_div_of_nonneg_left (pow_nonneg hr 3) h1X
  have : 3 / D.b ≤ 3 / Xs := div_le_div_of_nonneg_left (by norm_num) hX0 hXb
  linarith

/-- **`lem:record:middle-prices`, `Ñ₀ - μ`**: its price (mass times `sel = q_𝔅^{2a}`) is at most
`(2 v_D r² + (2 v_D (f₁ + h₁) + 12 w_S/(1 - 3/X)) r³) sel`. -/
theorem price_Nbr0 (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hrb : D.r ^ 2 * D.b = 1) {Xs : ℝ} (hX : 3 < Xs)
    (hXb : Xs ≤ D.b) {sel : ℝ} (hsel : 0 ≤ sel) :
    mass (D.Nbr0 - D.mu) * sel ≤ (2 * D.W.v .D * D.r ^ 2 +
      (2 * D.W.v .D * (D.I.f₁ + D.I.h₁) + 12 * D.W.w .S / (1 - 3 / Xs)) * D.r ^ 3) * sel := by
  have hb : 3 < D.b := lt_of_lt_of_le hX hXb
  obtain ⟨-, -, mEa, mG, mH, -, -⟩ := D.records_mass
  have hm : mass (D.Nbr0 - D.mu) = D.P⁻¹ * (mass D.Eadd + mass D.Gpol + mass D.Hdiag) := by
    rw [D.Nbr0_sub_mu]
    rfl
  rw [hm, mEa, mG, mH]
  apply mul_le_mul_of_nonneg_right _ hsel
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have hS : 0 ≤ 2 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3 +
      12 * D.W.w .S * D.r / (D.b - 3) := by
    have := D.W.v_nonneg .D
    have := D.W.w_nonneg .S
    have := D.r_nonneg
    have h3 : 0 < D.b - 3 := by linarith
    positivity
  have hdiv := D.r_div_le hrb hX hXb
  have h12 : 12 * D.W.w .S * D.r / (D.b - 3) ≤ 12 * D.W.w .S * D.r ^ 3 / (1 - 3 / Xs) := by
    have := D.W.w_nonneg .S
    rw [mul_div_assoc, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hdiv (by positivity)
  calc D.P⁻¹ * (2 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3 +
        12 * D.W.w .S * D.r / (D.b - 3))
      ≤ 1 * (2 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3 +
        12 * D.W.w .S * D.r / (D.b - 3)) :=
        mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hP1) hS
    _ ≤ _ := by
        rw [one_mul]
        have : 12 * D.W.w .S * D.r ^ 3 / (1 - 3 / Xs) =
            12 * D.W.w .S / (1 - 3 / Xs) * D.r ^ 3 := by ring
        nlinarith [h12, this]

/-- The (CP3) price `u_𝔅 = ∑_i mass(κu_i) sel` of the six records of `Ñ₀ - μ` equals the price of
`Ñ₀ - μ`. -/
theorem uprice_eq (sel : ℝ) :
    ∑ i, mass (D.bracketRec i) * sel = mass (D.Nbr0 - D.mu) * sel := by
  rw [← sum_mul, D.Nbr0_sub_mu_eq_sum]
  unfold mass
  rw [LinearMap.sum_apply]


/-- **`lem:record:middle-prices` for (CP3)**: `u_𝔅 ≤ (2 v_D r² + (2 v_D (f₁ + h₁) +
12 w_S/(1 - 3/X)) r³) q_𝔅^{2a}`. -/
theorem uprice_le (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hrb : D.r ^ 2 * D.b = 1) {Xs : ℝ} (hX : 3 < Xs)
    (hXb : Xs ≤ D.b) {sel : ℝ} (hsel : 0 ≤ sel) :
    ∑ i, mass (D.bracketRec i) * sel ≤ (2 * D.W.v .D * D.r ^ 2 +
      (2 * D.W.v .D * (D.I.f₁ + D.I.h₁) + 12 * D.W.w .S / (1 - 3 / Xs)) * D.r ^ 3) * sel := by
  rw [D.uprice_eq]
  exact D.price_Nbr0 hfh hrb hX hXb hsel

/-- **`lem:record:middle-prices`, `F_fold + E_add + G`**: the variation price `p_𝔅` of the positive
records of `ρ - μ = (E_add + G - F_fold)/P(r)` (`lem:middle-polarization`, (CP2)(a)) is at most
`(4 v_D r² + 2 v_D (f₁ + h₁) r³) sel`. -/
theorem price_first_stage (hfh : 0 ≤ D.I.f₁ + D.I.h₁) {sel : ℝ} (hsel : 0 ≤ sel) :
    D.P⁻¹ * (mass D.Ffold + mass D.Eadd + mass D.Gpol) * sel ≤
      (4 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3) * sel := by
  obtain ⟨mF, -, mEa, mG, -, -, -⟩ := D.records_mass
  rw [mF, mEa, mG]
  apply mul_le_mul_of_nonneg_right _ hsel
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have hS : 0 ≤ 2 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * D.r ^ 2 +
      2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3 := by
    have := D.W.v_nonneg .D
    have := D.r_nonneg
    positivity
  calc D.P⁻¹ * (2 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * D.r ^ 2 +
        2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3)
      ≤ 1 * (2 * D.W.v .D * D.r ^ 2 + 2 * D.W.v .D * D.r ^ 2 +
        2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3) :=
        mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hP1) hS
    _ = _ := by ring

/-- `ρ - μ = ∑ cᵢ κᵢ` with the three positive records `F_fold`, `E_add`, `G` (coefficients
`-P⁻¹, P⁻¹, P⁻¹`), so its variation price is `P⁻¹ (mass F_fold + mass E_add + mass G) sel`. -/
theorem rho_sub_mu_eq : D.rho - D.mu = (-D.P⁻¹) • D.Ffold + D.P⁻¹ • D.Eadd + D.P⁻¹ • D.Gpol := by
  rw [D.rho_sub_mu]
  apply LinearMap.ext
  intro f
  simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **`lem:record:middle-prices`, `δ_E`, sharp**: with sharp constant `k r` for each of the two
record differences, the summed sharp price is at most `2 (v_S + v_D) k r³ sel`. -/
theorem sharpPrice_deltaE {k : ℝ} (hk : 0 ≤ k) {sel : ℝ} (hsel : 0 ≤ sel) :
    ∑ s, sharpPrice sel (D.oldRec s) (k * D.r) ≤
      2 * (D.W.v .S + D.W.v .D) * k * D.r ^ 3 * sel := by
  simp only [sharpPrice, oldRec_mass, Fin.sum_univ_two]
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have hc : 0 ≤ (D.W.v .S + D.W.v .D) * D.r ^ 2 * (k * D.r) * sel := by
    have := D.W.v_nonneg .S
    have := D.W.v_nonneg .D
    have := D.r_nonneg
    positivity
  have h1 : D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) * (k * D.r) * sel ≤
      (D.W.v .S + D.W.v .D) * D.r ^ 2 * (k * D.r) * sel := by
    have := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hP1) hc
    calc D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) * (k * D.r) * sel
        = D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2 * (k * D.r) * sel) := by ring
      _ ≤ 1 * ((D.W.v .S + D.W.v .D) * D.r ^ 2 * (k * D.r) * sel) := this
      _ = _ := one_mul _
  nlinarith [h1]

/-- **`lem:record:middle-prices`, `δ_E`, variation**: the summed variation price
`∑_s (mass κ_s + mass κ'_s) sel` is at most `4 (v_S + v_D) r² sel`. -/
theorem vprice_deltaE {sel : ℝ} (hsel : 0 ≤ sel) :
    ∑ s, (mass (D.oldRec s) + mass (D.newRecN s)) * sel ≤
      4 * (D.W.v .S + D.W.v .D) * D.r ^ 2 * sel := by
  simp only [oldRec_mass, newRecN_mass, Fin.sum_univ_two]
  have hP1 : 1 ≤ D.P := one_le_midPoly D.W D.r_nonneg
  have hc : 0 ≤ (D.W.v .S + D.W.v .D) * D.r ^ 2 * sel := by
    have := D.W.v_nonneg .S
    have := D.W.v_nonneg .D
    positivity
  have h1 : D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) * sel ≤
      (D.W.v .S + D.W.v .D) * D.r ^ 2 * sel := by
    have := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hP1) hc
    calc D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2) * sel
        = D.P⁻¹ * ((D.W.v .S + D.W.v .D) * D.r ^ 2 * sel) := by ring
      _ ≤ 1 * ((D.W.v .S + D.W.v .D) * D.r ^ 2 * sel) := this
      _ = _ := one_mul _
  nlinarith [h1]

/-- **The two tags have equal totals** (`def:record:frame`(e)): the records of type `E₀` (tag `0`)
and `E₁` (tag `1`) of a block have the same mass, hence the same sharp price for a common sharp
constant and the same variation price; each tag carries half of the sharp and variation prices. -/
theorem tag_prices_equal (d sel : ℝ) :
    sharpPrice sel (D.oldRec 0) d = sharpPrice sel (D.oldRec 1) d ∧
      (mass (D.oldRec 0) + mass (D.newRecN 0)) * sel =
        (mass (D.oldRec 1) + mass (D.newRecN 1)) * sel := by
  simp only [sharpPrice, oldRec_mass, newRecN_mass]
  exact ⟨trivial, trivial⟩

end FrameData

end Sarkozy.PartVRecords

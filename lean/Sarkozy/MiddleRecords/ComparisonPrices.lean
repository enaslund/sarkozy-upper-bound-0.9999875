module

public import Sarkozy.TheoremC.Defs
public import Sarkozy.PartV.MiddleReference
public import Sarkozy.MiddleRecords.MergePrices

/-!
# Comparison prices of a middle block (`lem:middle-comparison-prices`)

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`,
`lem:middle-comparison-prices`.

**The decomposition** (proved for the paper's measures, `SlotMeasure`): the comparison law of a
block is `ν_𝔅 = ν⁺_𝔅 - (t/2) w Π^{--}_{F₁} - (t/2) w Π^{--}_{F₂}` with `ν⁺ ≥ 0` and `Π^{--}`
probability records (`signedLaw`). Then `ν_𝔅(1) = ν⁺(1) - t w` and
`|ν|_𝔅 ≤ ν_𝔅(1) + 2 t w` (`middle_comparison_decomposition`); if the root (weight one in
`μ̃_𝔅`) is retained, `ν⁺(1) ≥ 1/μ̃_𝔅(1)`, and with `w = w_D r/μ̃_𝔅(1)` and `t w_D r < 1`,
`ν_𝔅(1) ≥ (1 - t w_D r)/μ̃_𝔅(1) > 0` (`middle_comparison_mass_pos`); the paper's numbers
`t = 127/500`, `w_D < 6`, `r < 2^{-12}` give `t w_D r < 1` (`twr_lt_one`); the uniform one-slot
marginals pass to `ν_𝔅` (`signedLaw_uniform`).

**The prices** (`middle_comparison_prices`): with the norm bounds of the replaced records as
hypotheses, carrying their labels,
* the fold records `F₁, F₂` (weight `w_D r`): symmetric `≤ s_F r²`, skew `≤ ℓ_t r + a_F r²`
  (`prop:signed-bounds`(a), (b), (e));
* the matching records `E₀, E₁` (weight `w_S r`): `≤ s_E r`, `≤ a_E r`
  (`lem:record:exact-marginal-e`(ii));
* the six merges (weight `w_R r²`): the bounds of `lem:merge-repair` (`MergeRepairBounds`),
  priced by `cor:merge-repair` (`merge_prices`);
* the two two-layer constants (weight `w_C r³`): their total prices
  `≤ 2w_C/(1 - q_X)² r⁵` and `≤ 2w_C/(1 - q_X) r⁴` (`lem:record:accepting-c2`);
* the deleted records (the six folded merges `6 v_R r³`, `G` of mass `2 v_D (f₁ + h₁) r³`, the two
  folded constants `2 v_C r⁴`), charged their masses to the symmetric part
  (`rem:cp:charging`(i));

every weight divided by the normalizer `P = μ̃_𝔅(1) ≥ 1` and every price multiplied by the
selection factor `sel = q_𝔅^{2a} ≥ 0`, the totals are at most
`(S₂ r² + S₃ r³ + S₄ r⁴ + S₅ r⁵) sel` and `(A₂ r² + A₃ r³ + A₄ r⁴) sel` with the paper's
`S₂, …, A₄` (`coefS2`, …, `coefA4`). **The auxiliary prices** (`middle_aux_prices`): from the arm,
leading and remainder norms of the skew changes, the sums `2w_D r²`, `2w_D ℓ_t r²`, `2w_D a_F r³`
and `2w_S r²`, `2w_S r²/(1 - q_X)`, `2w_S r_E r⁴`.

**Not formalized here:** the acceptance of the six queries by each component and their
invariance (they are proved for the individual replacements elsewhere: V3's
`blockMergeRep_accepts`, `newRec_accepts`), (O1)–(O2) admissibility, and the identification of
`symF`, `skewF`, … with the operator norms of the actual record differences (they are parameters
with the stated bounds). The weights are V1's `MiddleWeights` (`w_D = W.w .D`, …) and the row
constants `f₁, h₁` V1's `MiddleInputs`.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.TheoremC Sarkozy.PartV

/-! ## The decomposition and the variation -/

section Decomposition

variable {X : Type} [Fintype X] [DecidableEq X]

theorem lawDensity_nonneg_of {κ : SlotMeasure X} (h : IsNonneg κ) (z : Slot → X) :
    0 ≤ lawDensity κ z :=
  h _ fun y => by split_ifs <;> norm_num

theorem sum_lawDensity_eq (κ : SlotMeasure X) : ∑ z, lawDensity κ z = mass κ := by
  unfold lawDensity mass
  rw [← map_sum]
  congr 1
  funext y
  rw [Finset.sum_apply]
  simp

/-- **The signed comparison law of a middle block**: `ν = ν⁺ - c κ₁ - c κ₂`, with
`c = (t/2) w` in the paper. -/
def signedLaw (νp κ₁ κ₂ : SlotMeasure X) (c : ℝ) : SlotMeasure X := νp - c • κ₁ - c • κ₂

omit [DecidableEq X] in
theorem signedLaw_mass (νp κ₁ κ₂ : SlotMeasure X) (c : ℝ) :
    mass (signedLaw νp κ₁ κ₂ c) = mass νp - c * mass κ₁ - c * mass κ₂ := by
  simp only [signedLaw, mass, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]

theorem signedLaw_totalVar {νp κ₁ κ₂ : SlotMeasure X} {c : ℝ} (hν : IsNonneg νp)
    (h₁ : IsNonneg κ₁) (h₂ : IsNonneg κ₂) (hc : 0 ≤ c) :
    totalVar (signedLaw νp κ₁ κ₂ c) ≤ mass νp + c * mass κ₁ + c * mass κ₂ := by
  unfold totalVar
  have hsplit : ∀ z, lawDensity (signedLaw νp κ₁ κ₂ c) z =
      lawDensity νp z - c * lawDensity κ₁ z - c * lawDensity κ₂ z := fun _ => rfl
  calc ∑ z, |lawDensity (signedLaw νp κ₁ κ₂ c) z|
      ≤ ∑ z, (lawDensity νp z + c * lawDensity κ₁ z + c * lawDensity κ₂ z) := by
        refine sum_le_sum fun z _ => ?_
        rw [hsplit, abs_le]
        have a0 := lawDensity_nonneg_of hν z
        have a1 := mul_nonneg hc (lawDensity_nonneg_of h₁ z)
        have a2 := mul_nonneg hc (lawDensity_nonneg_of h₂ z)
        constructor <;> linarith
    _ = mass νp + c * mass κ₁ + c * mass κ₂ := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, sum_lawDensity_eq,
          sum_lawDensity_eq, sum_lawDensity_eq]

/-- **`lem:middle-comparison-prices`, the decomposition**: for `ν⁺ ≥ 0` and probability records
`κ₁, κ₂`, the law `ν = ν⁺ - (t/2) w κ₁ - (t/2) w κ₂` has `ν(1) = ν⁺(1) - t w` and total
variation `|ν| ≤ ν(1) + 2 t w`. -/
theorem middle_comparison_decomposition {νp κ₁ κ₂ : SlotMeasure X} (hν : IsNonneg νp)
    (h₁ : IsProbability κ₁) (h₂ : IsProbability κ₂) {t w : ℝ} (ht : 0 ≤ t) (hw : 0 ≤ w) :
    mass (signedLaw νp κ₁ κ₂ (t / 2 * w)) = mass νp - t * w ∧
      totalVar (signedLaw νp κ₁ κ₂ (t / 2 * w)) ≤
        mass (signedLaw νp κ₁ κ₂ (t / 2 * w)) + 2 * t * w := by
  have hm := signedLaw_mass νp κ₁ κ₂ (t / 2 * w)
  rw [h₁.2, h₂.2] at hm
  have hv := signedLaw_totalVar hν h₁.1 h₂.1 (show 0 ≤ t / 2 * w by positivity)
  rw [h₁.2, h₂.2] at hv
  constructor
  · rw [hm]; ring
  · rw [hm]; linarith

omit [DecidableEq X] in
/-- **`ν_𝔅(1) > 0`** (`lem:middle-comparison-prices`): if `ν⁺(1) ≥ 1/P` (the retained root has
weight one in `μ̃_𝔅`, `P = μ̃_𝔅(1) > 0`), `w = w_D r/P` and `t w_D r < 1`, then
`ν(1) ≥ (1 - t w_D r)/P > 0`. -/
theorem middle_comparison_mass_pos {νp κ₁ κ₂ : SlotMeasure X} (h₁ : IsProbability κ₁)
    (h₂ : IsProbability κ₂) {t wD r P : ℝ} (hP : 0 < P) (hroot : 1 / P ≤ mass νp)
    (htwr : t * wD * r < 1) :
    (1 - t * wD * r) / P ≤ mass (signedLaw νp κ₁ κ₂ (t / 2 * (wD * r / P))) ∧
      0 < mass (signedLaw νp κ₁ κ₂ (t / 2 * (wD * r / P))) := by
  have hm := signedLaw_mass νp κ₁ κ₂ (t / 2 * (wD * r / P))
  rw [h₁.2, h₂.2] at hm
  have e : (1 - t * wD * r) / P = 1 / P - t * (wD * r / P) := by field_simp
  have hlow : (1 - t * wD * r) / P ≤ mass (signedLaw νp κ₁ κ₂ (t / 2 * (wD * r / P))) := by
    rw [hm, e]; linarith
  refine ⟨hlow, lt_of_lt_of_le ?_ hlow⟩
  exact div_pos (by linarith) hP

/-- The paper's numbers: `0 ≤ t ≤ 1`, `w_D < 6`, `0 ≤ r < 2^{-12}` give `t w_D r < 1`. -/
theorem twr_lt_one {t wD r : ℝ} (ht0 : 0 ≤ t) (ht : t ≤ 1) (hw : wD < 6)
    (hr0 : 0 ≤ r) (hr : r < 1 / 4096) : t * wD * r < 1 := by
  have h1 : t * wD ≤ 6 := by nlinarith
  have h2 : t * wD * r ≤ 6 * r := mul_le_mul_of_nonneg_right h1 hr0
  linarith

omit [DecidableEq X] in
/-- **Uniform one-slot marginals pass to the signed law** (the part of (a) of
`def:record:comparison-law` about the marginals). -/
theorem signedLaw_uniform {νp κ₁ κ₂ : SlotMeasure X} (hν : HasUniformSlotMarginals νp)
    (h₁ : HasUniformSlotMarginals κ₁) (h₂ : HasUniformSlotMarginals κ₂) (c : ℝ) :
    HasUniformSlotMarginals (signedLaw νp κ₁ κ₂ c) := by
  intro v g
  rw [signedLaw_mass]
  simp only [signedLaw, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  rw [hν v g, h₁ v g, h₂ v g]
  ring

end Decomposition

/-! ## The price coefficients -/

/-- `S₂ = 2 w_S s_E`. -/
def coefS2 (W : MiddleWeights) (sE : ℝ) : ℝ := 2 * W.w .S * sE

/-- `S₃ = 2 w_D s_F + 6 v_R + 2 v_D (f₁ + h₁)`. -/
def coefS3 (W : MiddleWeights) (I : MiddleInputs) (sF : ℝ) : ℝ :=
  2 * W.w .D * sF + 6 * W.v .R + 2 * W.v .D * (I.f₁ + I.h₁)

/-- `S₄ = 2 v_C + w_R g_S`. -/
def coefS4 (W : MiddleWeights) (gS : ℝ) : ℝ := 2 * W.v .C + W.w .R * gS

/-- `S₅ = 2 w_C/(1 - q_X)²`. -/
noncomputable def coefS5 (W : MiddleWeights) (qX : ℝ) : ℝ := 2 * W.w .C / (1 - qX) ^ 2

/-- `A₂ = 2 w_D ℓ_t + 2 w_S a_E`. -/
def coefA2 (W : MiddleWeights) (ℓ aE : ℝ) : ℝ := 2 * W.w .D * ℓ + 2 * W.w .S * aE

/-- `A₃ = 2 w_D a_F + w_R g_A`. -/
def coefA3 (W : MiddleWeights) (aF gA : ℝ) : ℝ := 2 * W.w .D * aF + W.w .R * gA

/-- `A₄ = 2 w_C/(1 - q_X)`. -/
noncomputable def coefA4 (W : MiddleWeights) (qX : ℝ) : ℝ := 2 * W.w .C / (1 - qX)

/-! ## The prices -/

/-- A sum over two records of `m · n_i · sel` with `0 ≤ n_i ≤ B` and `0 ≤ m ≤ M`. -/
theorem sum_two_le {n : Fin 2 → ℝ} {m M B sel : ℝ} (hm : 0 ≤ m) (hmM : m ≤ M)
    (hsel : 0 ≤ sel) (hn : ∀ i, 0 ≤ n i) (hB : ∀ i, n i ≤ B) :
    ∑ i, m * n i * sel ≤ 2 * (M * B) * sel := by
  simp only [Fin.sum_univ_two]
  have hB0 : 0 ≤ B := (hn 0).trans (hB 0)
  have h0 : m * n 0 ≤ M * B := mul_le_mul hmM (hB 0) (hn 0) (hm.trans hmM)
  have h1 : m * n 1 ≤ M * B := mul_le_mul hmM (hB 1) (hn 1) (hm.trans hmM)
  nlinarith

/-- **`lem:middle-comparison-prices`, the prices.** Let `X ≥ 4` be the piece start, `b ≥ X`
the least prime of the block, `r = b^{-1/2}`, `q_X = 1/X`, `P = μ̃_𝔅(1) ≥ 1` and `sel ≥ 0`.
Given the norm bounds of the replaced records (see the module docstring) and the deletions, the
total symmetric and skew prices are at most `(S₂ r² + S₃ r³ + S₄ r⁴ + S₅ r⁵) sel` and
`(A₂ r² + A₃ r³ + A₄ r⁴) sel`, with `g_S = g_S(X)`, `g_A = g_A(X)` of `cor:merge-repair`. -/
theorem middle_comparison_prices (W : MiddleWeights) (I : MiddleInputs) {X : ℕ} {b P sel : ℝ}
    (hX : 4 ≤ X) (hb : (X : ℝ) ≤ b) (hP : 1 ≤ P) (hsel : 0 ≤ sel)
    (hfh : 0 ≤ I.f₁ + I.h₁)
    {sF aF ℓ sE aE : ℝ}
    -- `prop:signed-bounds` (a), (b), (e): the two fold records
    (symF skewF : Fin 2 → ℝ) (hsymF0 : ∀ i, 0 ≤ symF i) (hskewF0 : ∀ i, 0 ≤ skewF i)
    (hsymF : ∀ i, symF i ≤ sF * (1 / Real.sqrt b) ^ 2)
    (hskewF : ∀ i, skewF i ≤ ℓ * (1 / Real.sqrt b) + aF * (1 / Real.sqrt b) ^ 2)
    -- `lem:record:exact-marginal-e`(ii): the two matching records
    (symE skewE : Fin 2 → ℝ) (hsymE0 : ∀ i, 0 ≤ symE i) (hskewE0 : ∀ i, 0 ≤ skewE i)
    (hsymE : ∀ i, symE i ≤ sE * (1 / Real.sqrt b))
    (hskewE : ∀ i, skewE i ≤ aE * (1 / Real.sqrt b))
    -- `lem:merge-repair`: the six merges
    (symN skewN : Fin 2 × Fin 3 → ℝ) (hM : MergeRepairBounds b symN skewN)
    -- `lem:record:accepting-c2`: the total prices of the two two-layer constants
    {constSym constSkew : ℝ}
    (hCs : constSym ≤ 2 * W.w .C / (1 - 1 / (X : ℝ)) ^ 2 * (1 / Real.sqrt b) ^ 5 * sel)
    (hCa : constSkew ≤ 2 * W.w .C / (1 - 1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 4 * sel) :
    (∑ i, W.w .D * (1 / Real.sqrt b) / P * symF i * sel +
        ∑ i, W.w .S * (1 / Real.sqrt b) / P * symE i * sel +
        ∑ j, W.w .R * (1 / Real.sqrt b) ^ 2 / P * symN j * sel + constSym +
        (6 * W.v .R * (1 / Real.sqrt b) ^ 3 +
          2 * W.v .D * (I.f₁ + I.h₁) * (1 / Real.sqrt b) ^ 3 +
          2 * W.v .C * (1 / Real.sqrt b) ^ 4) / P * sel ≤
      (coefS2 W sE * (1 / Real.sqrt b) ^ 2 + coefS3 W I sF * (1 / Real.sqrt b) ^ 3 +
        coefS4 W (gS (1 / (X : ℝ))) * (1 / Real.sqrt b) ^ 4 +
        coefS5 W (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 5) * sel) ∧
    (∑ i, W.w .D * (1 / Real.sqrt b) / P * skewF i * sel +
        ∑ i, W.w .S * (1 / Real.sqrt b) / P * skewE i * sel +
        ∑ j, W.w .R * (1 / Real.sqrt b) ^ 2 / P * skewN j * sel + constSkew ≤
      (coefA2 W ℓ aE * (1 / Real.sqrt b) ^ 2 + coefA3 W aF (gA (1 / (X : ℝ)) (rXof X)) *
          (1 / Real.sqrt b) ^ 3 + coefA4 W (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 4) * sel) := by
  have hX4 : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hb0 : 0 < b := by linarith
  set r := 1 / Real.sqrt b with hr_def
  have hr0 : 0 < r := by positivity
  have hP0 : 0 < P := by linarith
  have hwD := W.w_nonneg .D
  have hwS := W.w_nonneg .S
  have hvR := W.v_nonneg .R
  have hvD := W.v_nonneg .D
  have hvC := W.v_nonneg .C
  have hmD0 : 0 ≤ W.w .D * r / P := by positivity
  have hmD : W.w .D * r / P ≤ W.w .D * r := div_le_self (by positivity) hP
  have hmS0 : 0 ≤ W.w .S * r / P := by positivity
  have hmS : W.w .S * r / P ≤ W.w .S * r := div_le_self (by positivity) hP
  obtain ⟨hMs, hMa⟩ := merge_prices hX hb (W.w_nonneg .R) hP hsel hM
  have hdel0 :
      0 ≤ 6 * W.v .R * r ^ 3 + 2 * W.v .D * (I.f₁ + I.h₁) * r ^ 3 + 2 * W.v .C * r ^ 4 := by
    positivity
  have hdel : (6 * W.v .R * r ^ 3 + 2 * W.v .D * (I.f₁ + I.h₁) * r ^ 3 + 2 * W.v .C * r ^ 4) / P
      * sel ≤
        (6 * W.v .R * r ^ 3 + 2 * W.v .D * (I.f₁ + I.h₁) * r ^ 3 + 2 * W.v .C * r ^ 4) * sel :=
    mul_le_mul_of_nonneg_right (div_le_self hdel0 hP) hsel
  constructor
  · have hF := sum_two_le hmD0 hmD hsel hsymF0 hsymF
    have hE := sum_two_le hmS0 hmS hsel hsymE0 hsymE
    unfold coefS2 coefS3 coefS4 coefS5
    nlinarith
  · have hF := sum_two_le hmD0 hmD hsel hskewF0 hskewF
    have hE := sum_two_le hmS0 hmS hsel hskewE0 hskewE
    unfold coefA2 coefA3 coefA4
    nlinarith

/-- **`lem:middle-comparison-prices`, the auxiliary prices** (`def:cp5`). For each of the two
fold records (weight `w_D r`) with skew change split into a three-arm star of arm norm `≤ r` and
norm `≤ ℓ_t r` and a remainder of norm `≤ a_F r²`, and each of the two matching records (weight
`w_S r`) with a one-arm star of arm norm `≤ r` and norm `≤ r/(1 - q_X)` and a remainder of norm
`≤ r_E r³` (`lem:oct24:matching-star`), the auxiliary prices (weight times norm) summed over the
two records of each kind are at most `2w_D r²`, `2w_D ℓ_t r²`, `2w_D a_F r³` and `2w_S r²`,
`2w_S r²/(1 - q_X)`, `2w_S r_E r⁴`. -/
theorem middle_aux_prices {wD wS ℓ aF rE qX r : ℝ} (hwD : 0 ≤ wD) (hwS : 0 ≤ wS) (hr : 0 ≤ r)
    (armF leadF remF armE leadE remE : Fin 2 → ℝ)
    (harmF : ∀ i, armF i ≤ r) (hleadF : ∀ i, leadF i ≤ ℓ * r) (hremF : ∀ i, remF i ≤ aF * r ^ 2)
    (harmE : ∀ i, armE i ≤ r) (hleadE : ∀ i, leadE i ≤ r / (1 - qX))
    (hremE : ∀ i, remE i ≤ rE * r ^ 3) :
    ∑ i, wD * r * armF i ≤ 2 * wD * r ^ 2 ∧ ∑ i, wD * r * leadF i ≤ 2 * wD * ℓ * r ^ 2 ∧
      ∑ i, wD * r * remF i ≤ 2 * wD * aF * r ^ 3 ∧ ∑ i, wS * r * armE i ≤ 2 * wS * r ^ 2 ∧
      ∑ i, wS * r * leadE i ≤ 2 * wS * r ^ 2 / (1 - qX) ∧
      ∑ i, wS * r * remE i ≤ 2 * wS * rE * r ^ 4 := by
  have key : ∀ (w : ℝ) (n : Fin 2 → ℝ) (B : ℝ), 0 ≤ w → (∀ i, n i ≤ B) →
      ∑ i, w * r * n i ≤ 2 * (w * r * B) := by
    intro w n B hw hn
    simp only [Fin.sum_univ_two]
    have hwr : 0 ≤ w * r := mul_nonneg hw hr
    have := mul_le_mul_of_nonneg_left (hn 0) hwr
    have := mul_le_mul_of_nonneg_left (hn 1) hwr
    linarith
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := key wD armF r hwD harmF; nlinarith
  · have := key wD leadF (ℓ * r) hwD hleadF; nlinarith
  · have := key wD remF (aF * r ^ 2) hwD hremF; nlinarith
  · have := key wS armE r hwS harmE; nlinarith
  · have := key wS leadE (r / (1 - qX)) hwS hleadE
    calc ∑ i, wS * r * leadE i ≤ 2 * (wS * r * (r / (1 - qX))) := this
      _ = 2 * wS * r ^ 2 / (1 - qX) := by ring
  · have := key wS remE (rE * r ^ 3) hwS hremE; nlinarith

end Sarkozy.MiddleRecords

module

public import Sarkozy.MainFinal.MiddlePrices
public import Sarkozy.MiddlePrimeInputs.Data

@[expose] public section

/-!
# The signs of the middle price coefficients `K_d(i)` (E2)

`paper/sections/21_middle_records.tex`, `lem:middle-comparison-prices`: the price polynomial of a
middle block is `K₂ r² + K₃ r³ + K₄ r⁴ + K₅ r⁵` at `r = b_𝔅^{-1/2}`, with
`K₂ = S₂ + A₂`, `K₃ = S₃ + A₃`, `K₄ = S₄ + A₄`, `K₅ = S₅` (K1's `midK2` … `midK5`).

K2's field 37 (`SAParts.hK`) asks `0 ≤ K_d(i)` for the 33 pieces. Here it is **proved**:
* `midK4_nonneg`, `midK5_nonneg`: unconditionally (`K₄`, `K₅` do not depend on the constants
  `κ`), from the nonnegativity of the ALLp completion weights and `X_i ≥ 2²⁴`, which makes the
  denominators `1 − q_X`, `1 − 2q_X`, `1 − 3q_X` of `g_S`, `g_A` (`cor:merge-repair`) positive;
* `midK2_nonneg`, `midK3_nonneg`: whenever the constants `s_F, a_F, ℓ_t, s_E, a_E` of the piece
  (`eq:signed-constants`, `lem:record:exact-marginal-e`(ii)) are nonnegative (`KappaNonneg`), as
  the paper's are (they bound norms);
* `midK_signs`: the field `hK` itself, from `∀ i, KappaNonneg (κ i)`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.NumericalFields

open Sarkozy.MainFinal
open Sarkozy.PartV
open Sarkozy.MiddleRecords (coefS2 coefS3 coefS4 coefS5 coefA2 coefA3 coefA4 gS gA rXof)
open Sarkozy.BlockSpecPaper (allpWeights allpInputs allpInputs_nonneg)

/-- **The constants of a piece are nonnegative** (`eq:signed-constants`,
`lem:record:exact-marginal-e`(ii)): `s_F, a_F, ℓ_t, s_E, a_E ≥ 0`. A side condition on the data
`κ`; the paper's constants are positive (they are norm bounds). -/
def KappaNonneg (κ : MiddleConsts) : Prop :=
  0 ≤ κ.sF ∧ 0 ≤ κ.aF ∧ 0 ≤ κ.ℓ ∧ 0 ≤ κ.sE ∧ 0 ≤ κ.aE

/-- `q_X = 1/X_i` lies in `(0, 2^{-24}]`. -/
theorem qX_mem (i : Fin 33) :
    0 < 1 / (pieceStart i : ℝ) ∧ 1 / (pieceStart i : ℝ) ≤ 1 / 2 ^ 24 := by
  have h : (2 : ℝ) ^ 24 ≤ (pieceStart i : ℝ) := by
    exact_mod_cast MiddlePrimeInputs.pieceStart_ge i
  have hpos : (0 : ℝ) < (pieceStart i : ℝ) := lt_of_lt_of_le (by norm_num) h
  exact ⟨one_div_pos.mpr hpos, one_div_le_one_div_of_le (by norm_num) h⟩

/-- `g_S(q_X) ≥ 0` at a piece start (`cor:merge-repair`). -/
theorem gS_nonneg (i : Fin 33) : 0 ≤ gS (1 / (pieceStart i : ℝ)) := by
  obtain ⟨h0, h1⟩ := qX_mem i
  set q := 1 / (pieceStart i : ℝ)
  have a1 : 0 < 1 - 2 * q := by linarith
  have a2 : 0 < 1 - 3 * q := by linarith
  have a3 : 0 < 1 - q := by linarith
  unfold gS
  have := mul_pos a1 a2
  positivity

/-- `g_A(q_X, r_X) ≥ 0` at a piece start (`cor:merge-repair`). -/
theorem gA_nonneg (i : Fin 33) :
    0 ≤ gA (1 / (pieceStart i : ℝ)) (rXof (pieceStart i)) := by
  obtain ⟨h0, h1⟩ := qX_mem i
  set q := 1 / (pieceStart i : ℝ)
  have a1 : 0 < 1 - 2 * q := by linarith
  have a2 : 0 < 1 - 3 * q := by linarith
  have a3 : 0 < 1 - q := by linarith
  have hr : 0 ≤ rXof (pieceStart i) := by
    unfold rXof
    positivity
  unfold gA
  have := mul_pos a1 a2
  positivity

/-- **`K₄(i) ≥ 0`** (`lem:middle-comparison-prices`): `2 v_C + w_R g_S + 2 w_C/(1 − q_X)`. -/
theorem midK4_nonneg (i : Fin 33) : 0 ≤ midK4 i := by
  have hq := qX_mem i
  have a3 : 0 < 1 - 1 / (pieceStart i : ℝ) := by linarith [hq.2]
  have hv := (allpWeights i).v_nonneg .C
  have hwR := (allpWeights i).w_nonneg .R
  have hwC := (allpWeights i).w_nonneg .C
  have hg := gS_nonneg i
  unfold midK4 coefS4 coefA4
  positivity

/-- **`K₅(i) ≥ 0`** (`lem:middle-comparison-prices`): `2 w_C/(1 − q_X)²`. -/
theorem midK5_nonneg (i : Fin 33) : 0 ≤ midK5 i := by
  have hwC := (allpWeights i).w_nonneg .C
  unfold midK5 coefS5
  positivity

/-- **`K₂(i) ≥ 0`** for nonnegative constants: `2 w_S s_E + 2 w_D ℓ_t + 2 w_S a_E`. -/
theorem midK2_nonneg (κ : Fin 33 → MiddleConsts) (i : Fin 33) (h : KappaNonneg (κ i)) :
    0 ≤ midK2 κ i := by
  obtain ⟨-, -, hℓ, hsE, haE⟩ := h
  have hwS := (allpWeights i).w_nonneg .S
  have hwD := (allpWeights i).w_nonneg .D
  unfold midK2 coefS2 coefA2
  positivity

/-- **`K₃(i) ≥ 0`** for nonnegative constants:
`2 w_D s_F + 6 v_R + 2 v_D (f₁ + h₁) + 2 w_D a_F + w_R g_A`. -/
theorem midK3_nonneg (κ : Fin 33 → MiddleConsts) (i : Fin 33) (h : KappaNonneg (κ i)) :
    0 ≤ midK3 κ i := by
  obtain ⟨hsF, haF, -, -, -⟩ := h
  have hwD := (allpWeights i).w_nonneg .D
  have hwR := (allpWeights i).w_nonneg .R
  have hvR := (allpWeights i).v_nonneg .R
  have hvD := (allpWeights i).v_nonneg .D
  have hf := (allpInputs_nonneg i).2.2.1
  have hh := (allpInputs_nonneg i).2.2.2.2.1
  have hg := gA_nonneg i
  unfold midK3 coefS3 coefA3
  positivity

/-- **K2's field 37, `SAParts.hK`** (`lem:middle-comparison-prices`): the signs of the price
coefficients `K_d(i)`, `d = 2, …, 5`, on all 33 pieces, for nonnegative constants `κ`. -/
theorem midK_signs (κ : Fin 33 → MiddleConsts) (hκ : ∀ i, KappaNonneg (κ i)) :
    ∀ i, 0 ≤ midK2 κ i ∧ 0 ≤ midK3 κ i ∧ 0 ≤ midK4 i ∧ 0 ≤ midK5 i := fun i =>
  ⟨midK2_nonneg κ i (hκ i), midK3_nonneg κ i (hκ i), midK4_nonneg i, midK5_nonneg i⟩

end Sarkozy.NumericalFields

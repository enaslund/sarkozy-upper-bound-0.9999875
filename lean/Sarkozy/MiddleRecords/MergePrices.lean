module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Data.Nat.Sqrt

/-!
# The six merge prices (`cor:merge-repair`)

`paper/sections/21_middle_records.tex`, `subsec:merge-repair`, `cor:merge-repair`, from the
block bounds of `lem:merge-repair`.

**The input** (`lem:merge-repair`, a hypothesis here, `MergeRepairBounds`): on a block with
least prime `b`, the difference between the product replacement and the product source of each
of the six merge records `(s, k) ∈ {0,1} × {0,1,2}` (`def:merge-records`, indexed as in V3's
`Sarkozy.PartVRecords.designated`) has symmetric and skew norms at most
* `s_b = (5b - 6)/((b - 2)(b - 3))` and
  `a_b = b^{-1/2}[1 + 2 b^{-1/2}(4 - 6/b)]/((1 - 2/b)(1 - 3/b))` for the four mirror-edge
  replacements (`k ≠ 2`);
* `d_b + η_b = 2/(b - 2) + 1/(b - 1)` and `γ_b = √b/(b - 1)` for the two first-coordinate
  replacements (`k = 2`).

**The corollary** (`merge_prices`): for a piece starting at `X ≥ 4`, `q_X = 1/X`,
`r_X = 1/⌊√X⌋`, a block of the piece with least prime `b ≥ X`, `r = b^{-1/2}`, each record of
mass `w_R r²/P` (`P ≥ 1` the reference normalizer, which only decreases the prices) and selection
factor `sel ≥ 0`, the total prices by the charging rule `rem:cp:charging`(ii) (mass times norm
times `sel`) are at most `w_R g_S(X) r⁴ sel` (symmetric) and `w_R g_A(X) r³ sel` (skew), with
`g_S(X) = 20/((1 - 2q_X)(1 - 3q_X)) + 4/(1 - 2q_X) + 2/(1 - q_X)` and
`g_A(X) = 4(1 + 8r_X)/((1 - 2q_X)(1 - 3q_X)) + 2/(1 - q_X)`.

The arithmetic: `merge_sym_coeff` (`4 s_b + 2(d_b + η_b) ≤ g_S(X)/b`) and `merge_skew_coeff`
(`4 a_b + 2γ_b ≤ g_A(X) b^{-1/2}`), dropping the negative numerator corrections and using
`1/b ≤ q_X`, `b^{-1/2} ≤ r_X` (`invSqrt_le_rX`), exactly as in the paper's proof. The paper's
`p ≥ 2^{24}` of `lem:merge-repair` is not needed for the corollary's arithmetic, only `b ≥ X ≥ 4`.
The last sentence of the corollary (the norm envelopes are positive reserved diagonals of the
half laws) is the form of the charging rule, `Sarkozy.RecordExpansion.bracket_of_norm_bound`; it
is not restated here.

`cert:merge-coefficients` (not in the brief, a two-line check): `gS_at_Q3`, `gA_at_Q3` bound
`g_S(Q₃)` and `g_A(Q₃)` by the printed decimals, with `⌊√Q₃⌋ = 4466` (`sqrt_Q3`).
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

/-! ## The coefficients -/

/-- `d_p = 2/(p - 2)` (`lem:merge-repair`). -/
noncomputable def dG (p : ℝ) : ℝ := 2 / (p - 2)

/-- `η^G_p = 1/(p - 1)` (`lem:merge-repair`). -/
noncomputable def etaG (p : ℝ) : ℝ := 1 / (p - 1)

/-- `γ^G_p = √p/(p - 1)` (`lem:merge-repair`). -/
noncomputable def gammaG (p : ℝ) : ℝ := Real.sqrt p / (p - 1)

/-- `s^G_p = (5p - 6)/((p - 2)(p - 3))` (`lem:merge-repair`). -/
noncomputable def sG (p : ℝ) : ℝ := (5 * p - 6) / ((p - 2) * (p - 3))

/-- `a^G_p = p^{-1/2}[1 + 2p^{-1/2}(4 - 6/p)]/((1 - 2/p)(1 - 3/p))` (`lem:merge-repair`), with
`p^{-1/2} = 1/√p`. -/
noncomputable def aG (p : ℝ) : ℝ :=
  1 / Real.sqrt p * (1 + 2 * (1 / Real.sqrt p) * (4 - 6 / p)) / ((1 - 2 / p) * (1 - 3 / p))

/-- `g_S(X)` of `cor:merge-repair`, as a function of `q_X`. -/
noncomputable def gS (qX : ℝ) : ℝ :=
  20 / ((1 - 2 * qX) * (1 - 3 * qX)) + 4 / (1 - 2 * qX) + 2 / (1 - qX)

/-- `g_A(X)` of `cor:merge-repair`, as a function of `q_X, r_X`. -/
noncomputable def gA (qX rX : ℝ) : ℝ :=
  4 * (1 + 8 * rX) / ((1 - 2 * qX) * (1 - 3 * qX)) + 2 / (1 - qX)

/-- `r_X = 1/⌊√X⌋`. -/
noncomputable def rXof (X : ℕ) : ℝ := 1 / (Nat.sqrt X : ℝ)

/-! ## The arithmetic -/

/-- `b^{-1/2} ≤ r_X = 1/⌊√X⌋` for `1 ≤ X ≤ b`. -/
theorem invSqrt_le_rX {X : ℕ} {b : ℝ} (hX : 1 ≤ X) (hb : (X : ℝ) ≤ b) :
    1 / Real.sqrt b ≤ rXof X := by
  unfold rXof
  have hs : 0 < Nat.sqrt X := Nat.sqrt_pos.mpr (by omega)
  have hs' : (0 : ℝ) < (Nat.sqrt X : ℝ) := by exact_mod_cast hs
  apply one_div_le_one_div_of_le hs'
  have h1 : ((Nat.sqrt X : ℕ) : ℝ) ^ 2 ≤ (X : ℝ) := by exact_mod_cast Nat.sqrt_le' X
  calc (Nat.sqrt X : ℝ) = Real.sqrt ((Nat.sqrt X : ℝ) ^ 2) := (Real.sqrt_sq hs'.le).symm
    _ ≤ Real.sqrt (X : ℝ) := Real.sqrt_le_sqrt h1
    _ ≤ Real.sqrt b := Real.sqrt_le_sqrt hb

/-- `1/((1 - 2q)(1 - 3q))` is nondecreasing on `0 ≤ q < 1/3`. -/
theorem inv_den_mono {qb qX : ℝ} (h : qb ≤ qX) (hX : qX < 1 / 3) :
    1 / ((1 - 2 * qb) * (1 - 3 * qb)) ≤ 1 / ((1 - 2 * qX) * (1 - 3 * qX)) := by
  apply one_div_le_one_div_of_le
  · have : 0 < 1 - 2 * qX := by linarith
    have : 0 < 1 - 3 * qX := by linarith
    positivity
  · nlinarith

/-- **The symmetric coefficient**: `4 s_b + 2(d_b + η_b) ≤ g_S(X)/b` for `b ≥ X ≥ 4`. -/
theorem merge_sym_coeff {X b : ℝ} (hX : 4 ≤ X) (hb : X ≤ b) :
    4 * sG b + 2 * (dG b + etaG b) ≤ gS (1 / X) * (1 / b) := by
  have hb0 : 0 < b := by linarith
  have hX0 : 0 < X := by linarith
  set qb := 1 / b with hqb
  set qX := 1 / X with hqX
  have hqb0 : 0 ≤ qb := by positivity
  have hle : qb ≤ qX := by rw [hqb, hqX]; exact one_div_le_one_div_of_le hX0 hb
  have hqX4 : qX ≤ 1 / 4 := by rw [hqX]; exact one_div_le_one_div_of_le (by norm_num) hX
  have h1X : 0 < 1 - qX := by linarith
  have h2X : 0 < 1 - 2 * qX := by linarith
  have h3X : 0 < 1 - 3 * qX := by linarith
  have h1b : 0 < 1 - qb := by linarith
  have h2b : 0 < 1 - 2 * qb := by linarith
  have h3b : 0 < 1 - 3 * qb := by linarith
  -- each coefficient in terms of `q_b`
  have eS : sG b ≤ 5 * qb * (1 / ((1 - 2 * qb) * (1 - 3 * qb))) := by
    have e : 5 * qb * (1 / ((1 - 2 * qb) * (1 - 3 * qb))) = 5 * b / ((b - 2) * (b - 3)) := by
      rw [hqb]; field_simp
    rw [e, sG]
    apply div_le_div_of_nonneg_right (by linarith)
    have : 0 < b - 2 := by linarith
    have : 0 < b - 3 := by linarith
    positivity
  have eD : dG b = 2 * qb / (1 - 2 * qb) := by
    rw [dG, hqb]; field_simp
  have eE : etaG b = qb / (1 - qb) := by
    rw [etaG, hqb]; field_simp
  have mS := inv_den_mono hle (by linarith)
  have mD : 2 * qb / (1 - 2 * qb) ≤ 2 * qb / (1 - 2 * qX) :=
    div_le_div_of_nonneg_left (by positivity) h2X (by linarith)
  have mE : qb / (1 - qb) ≤ qb / (1 - qX) := div_le_div_of_nonneg_left hqb0 h1X (by linarith)
  have hgoal : gS qX * qb = 20 * qb * (1 / ((1 - 2 * qX) * (1 - 3 * qX))) +
      2 * (2 * qb / (1 - 2 * qX)) + 2 * (qb / (1 - qX)) := by
    unfold gS; field_simp; ring
  rw [hgoal, eD, eE]
  have := mul_le_mul_of_nonneg_left mS (show 0 ≤ 20 * qb by positivity)
  nlinarith

/-- **The skew coefficient**: `4 a_b + 2γ_b ≤ g_A(X) b^{-1/2}` for `b ≥ X ≥ 4` and
`b^{-1/2} ≤ r_X`. -/
theorem merge_skew_coeff {X b rX : ℝ} (hX : 4 ≤ X) (hb : X ≤ b) (hr : 1 / Real.sqrt b ≤ rX) :
    4 * aG b + 2 * gammaG b ≤ gA (1 / X) rX * (1 / Real.sqrt b) := by
  have hb0 : 0 < b := by linarith
  have hX0 : 0 < X := by linarith
  set qb := 1 / b with hqb
  set qX := 1 / X with hqX
  set r := 1 / Real.sqrt b with hr_def
  have hsb : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  have hr0 : 0 < r := by positivity
  have hr2 : r ^ 2 = qb := by
    rw [hr_def, hqb, div_pow, Real.sq_sqrt hb0.le, one_pow]
  have hqb0 : 0 ≤ qb := by positivity
  have hle : qb ≤ qX := by rw [hqb, hqX]; exact one_div_le_one_div_of_le hX0 hb
  have hqX4 : qX ≤ 1 / 4 := by rw [hqX]; exact one_div_le_one_div_of_le (by norm_num) hX
  have h1X : 0 < 1 - qX := by linarith
  have h2X : 0 < 1 - 2 * qX := by linarith
  have h3X : 0 < 1 - 3 * qX := by linarith
  have h1b : 0 < 1 - qb := by linarith
  have h2b : 0 < 1 - 2 * qb := by linarith
  have h3b : 0 < 1 - 3 * qb := by linarith
  have eA : aG b = r * (1 + 2 * r * (4 - 6 * qb)) * (1 / ((1 - 2 * qb) * (1 - 3 * qb))) := by
    rw [aG, hqb, hr_def]; field_simp
  have hnum : r * (1 + 2 * r * (4 - 6 * qb)) ≤ r * (1 + 8 * rX) := by
    apply mul_le_mul_of_nonneg_left _ hr0.le
    nlinarith
  have hnum0 : 0 ≤ r * (1 + 2 * r * (4 - 6 * qb)) := by
    apply mul_nonneg hr0.le
    nlinarith
  have mS := inv_den_mono hle (by linarith)
  have hA : aG b ≤ r * (1 + 8 * rX) * (1 / ((1 - 2 * qX) * (1 - 3 * qX))) := by
    rw [eA]
    calc r * (1 + 2 * r * (4 - 6 * qb)) * (1 / ((1 - 2 * qb) * (1 - 3 * qb)))
        ≤ r * (1 + 8 * rX) * (1 / ((1 - 2 * qb) * (1 - 3 * qb))) :=
          mul_le_mul_of_nonneg_right hnum (by positivity)
      _ ≤ r * (1 + 8 * rX) * (1 / ((1 - 2 * qX) * (1 - 3 * qX))) :=
          mul_le_mul_of_nonneg_left mS (by nlinarith)
  have eG : gammaG b = r / (1 - qb) := by
    rw [gammaG, hr_def, hqb]
    field_simp
    rw [Real.sq_sqrt hb0.le]
  have mG : r / (1 - qb) ≤ r / (1 - qX) := div_le_div_of_nonneg_left hr0.le h1X (by linarith)
  have hgoal : gA qX rX * r = 4 * (r * (1 + 8 * rX) * (1 / ((1 - 2 * qX) * (1 - 3 * qX)))) +
      2 * (r / (1 - qX)) := by
    unfold gA; field_simp
  rw [hgoal, eG]
  linarith

/-! ## The prices -/

/-- **The norm bounds of `lem:merge-repair`** on a block with least prime `b` (a hypothesis):
`symN i`, `skewN i` are the norms of the symmetric and skew parts of the difference of the merge
record `i = (s, k)`, relative to the product of the actual half laws `m_p`; `k ≠ 2` are the
mirror-edge replacements, `k = 2` the first-coordinate ones (`tab:merge-records`). -/
structure MergeRepairBounds (b : ℝ) (symN skewN : Fin 2 × Fin 3 → ℝ) : Prop where
  sym_nonneg : ∀ i, 0 ≤ symN i
  skew_nonneg : ∀ i, 0 ≤ skewN i
  sym_mirror : ∀ s k, k ≠ 2 → symN (s, k) ≤ sG b
  skew_mirror : ∀ s k, k ≠ 2 → skewN (s, k) ≤ aG b
  sym_first : ∀ s, symN (s, 2) ≤ dG b + etaG b
  skew_first : ∀ s, skewN (s, 2) ≤ gammaG b

/-- Sum over the six merge records: four mirror and two first-coordinate ones. -/
theorem sum_six {f : Fin 2 × Fin 3 → ℝ} {m c : ℝ} (hm : ∀ s k, k ≠ 2 → f (s, k) ≤ m)
    (hc : ∀ s, f (s, 2) ≤ c) : ∑ i, f i ≤ 4 * m + 2 * c := by
  rw [Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two, Fin.sum_univ_three]
  have h00 := hm 0 0 (by decide)
  have h01 := hm 0 1 (by decide)
  have h10 := hm 1 0 (by decide)
  have h11 := hm 1 1 (by decide)
  have h02 := hc 0
  have h12 := hc 1
  linarith

/-- **`cor:merge-repair`.** For a piece starting at `X ≥ 4` and a block of it with least prime
`b ≥ X`, `r = b^{-1/2}`, given the norm bounds of `lem:merge-repair`, the six merge changes, each
of mass `w_R r²/P` with `P ≥ 1`, have total symmetric price at most `w_R g_S(X) r⁴ sel` and
total skew price at most `w_R g_A(X) r³ sel`, where a price is mass times norm times the
selection factor `sel = q_𝔅^{2a} ≥ 0` (`rem:cp:charging`(ii)). -/
theorem merge_prices {X : ℕ} {b wR P sel : ℝ} (hX : 4 ≤ X) (hb : (X : ℝ) ≤ b) (hwR : 0 ≤ wR)
    (hP : 1 ≤ P) (hsel : 0 ≤ sel) {symN skewN : Fin 2 × Fin 3 → ℝ}
    (hB : MergeRepairBounds b symN skewN) :
    ∑ i, wR * (1 / Real.sqrt b) ^ 2 / P * symN i * sel ≤
        wR * gS (1 / (X : ℝ)) * (1 / Real.sqrt b) ^ 4 * sel ∧
      ∑ i, wR * (1 / Real.sqrt b) ^ 2 / P * skewN i * sel ≤
        wR * gA (1 / (X : ℝ)) (rXof X) * (1 / Real.sqrt b) ^ 3 * sel := by
  have hX4 : (4 : ℝ) ≤ X := by exact_mod_cast hX
  have hb0 : 0 < b := by linarith
  set r := 1 / Real.sqrt b with hr_def
  have hr0 : 0 < r := by positivity
  have hr2 : r ^ 2 = 1 / b := by
    rw [hr_def, div_pow, Real.sq_sqrt hb0.le, one_pow]
  have hP0 : 0 < P := by linarith
  set m := wR * r ^ 2 / P with hm
  have hm0 : 0 ≤ m := by positivity
  have hmle : m ≤ wR * r ^ 2 := by
    rw [hm]; exact div_le_self (by positivity) hP
  constructor
  · have hsum : ∑ i, symN i ≤ 4 * sG b + 2 * (dG b + etaG b) :=
      sum_six hB.sym_mirror hB.sym_first
    have hcoef := merge_sym_coeff hX4 hb
    have hS0 : 0 ≤ ∑ i, symN i := Finset.sum_nonneg fun i _ => hB.sym_nonneg i
    have e : ∑ i, m * symN i * sel = m * sel * ∑ i, symN i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc m * sel * ∑ i, symN i ≤ (wR * r ^ 2) * sel * (gS (1 / (X : ℝ)) * (1 / b)) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hmle hsel) (hsum.trans hcoef) hS0
          positivity
      _ = wR * gS (1 / (X : ℝ)) * r ^ 4 * sel := by
          rw [← hr2]; ring
  · have hsum : ∑ i, skewN i ≤ 4 * aG b + 2 * gammaG b :=
      sum_six hB.skew_mirror hB.skew_first
    have hcoef := merge_skew_coeff hX4 hb (invSqrt_le_rX (by omega) hb)
    have hA0 : 0 ≤ ∑ i, skewN i := Finset.sum_nonneg fun i _ => hB.skew_nonneg i
    have e : ∑ i, m * skewN i * sel = m * sel * ∑ i, skewN i := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    calc m * sel * ∑ i, skewN i ≤ (wR * r ^ 2) * sel * (gA (1 / (X : ℝ)) (rXof X) * r) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_right hmle hsel) (hsum.trans hcoef) hA0
          positivity
      _ = wR * gA (1 / (X : ℝ)) (rXof X) * r ^ 3 * sel := by ring

/-! ## `cert:merge-coefficients` at `Q₃` -/

/-- `⌊√Q₃⌋ = 4466` for `Q₃ = 19951586`. -/
theorem sqrt_Q3 : Nat.sqrt 19951586 = 4466 :=
  (Nat.eq_sqrt.mpr ⟨by norm_num, by norm_num⟩).symm

/-- **`cert:merge-coefficients`**: `26.0000055133 < g_S(Q₃) < 26.0000055134`. -/
theorem gS_at_Q3 : 26.0000055133 < gS (1 / 19951586) ∧ gS (1 / 19951586) < 26.0000055134 := by
  unfold gS
  constructor <;> norm_num

/-- **`cert:merge-coefficients`**: `6.0071663530 < g_A(Q₃) < 6.0071663531`, with
`r_X = 1/⌊√Q₃⌋ = 1/4466`. -/
theorem gA_at_Q3 : 6.0071663530 < gA (1 / 19951586) (rXof 19951586) ∧
    gA (1 / 19951586) (rXof 19951586) < 6.0071663531 := by
  unfold gA rXof
  rw [sqrt_Q3]
  constructor <;> norm_num

end Sarkozy.MiddleRecords

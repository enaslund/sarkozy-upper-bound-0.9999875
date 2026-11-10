module

public import Sarkozy.MiddleRecords.AcceptingC2

/-!
# The reference collision matrix (`lem:record:conditional-collision`(d), "The matrix")

`paper/sections/21_middle_records.tex`, `subsec:record:f_remainders`,
`lem:record:conditional-collision`(d), the paragraph "The matrix.". The no-cross parts of the nine
coincidence substitutions of the reference fold record sum to `q V C V^*`, with
`V = (V₀, V₁, V₂, k V₁, h V₁)` and `C` the symmetric nonnegative `5 × 5` matrix with diagonal
`(4, 1, 4, 0, 0)` and entries `1` at the positions `01, 02, 12, 03, 24` and their transposes
(`collMat`). The paper bounds `‖C‖ ≤ 56119/10000` by a positive test vector
`w = (1, 43367/10⁵, 1, 17820/10⁵, 17820/10⁵)` (`collVec`).

**Proved here.**
* `collMat_symm`, `collMat_nonneg`: `C` is symmetric and nonnegative (the entries are those of the
  displayed sum: `4δ₀₀ + 4δ₂₂ + δ₀₂ + δ₂₀ + δ₁₁ + δ₀₁(1 + k(y)) + δ₁₀(1 + k(x)) + δ₁₂(1 + h(x)) +
  δ₂₁(1 + h(y))`, with `δ_{ij} = q V_i V_j^*`; only the matrix is formalized here).
* `collMat_rows`: the five quotients `(Cw)_a/w_a` are exactly `561187/10⁵`, `243367/43367`,
  `561187/10⁵`, `10⁵/17820`, `10⁵/17820`, as printed, and `collMat_quotients_lt`: all are below
  `56119/10000`.
* `schur_weighted` (the **weighted Schur test**, any finite index type): for a nonnegative
  symmetric `C`, a positive `w` and `λ ≥ 0` with `C w ≤ λ w`, `‖C x‖² ≤ λ² ‖x‖²` in `ℓ²`;
  `schur_weighted_form`: `|⟨y, C x⟩| ≤ λ ‖x‖ ‖y‖`.
* **`collMat_norm_le`**: `‖C x‖ ≤ (56119/10000) ‖x‖` for every `x ∈ ℝ⁵`, i.e. `‖C‖ ≤ 56119/10000`,
  and `collMat_form_le`, the bilinear form.
* `gamma5_rows`: the `Γ₅` row bound of the "synthesis maps" step, `1 + 2a₅ + 2b₅` with
  `b₅ ≤ a₅` (`b5_le_a5`), as arithmetic in `(q, r)`, given the entry norms; and the entry norms
  of the displayed table, `(α² + qβ²)^{1/2} ≤ a₅` for `02, 04, 23` and `≤ b₅` for the other seven
  (`gram02_le`, `gram04_le`, `gram01_le`, `gram03_le`, `gram13_le`, at `p = s²`, `s ≥ 4`; the
  table values `(α, β)` themselves are taken from the paper).

* `norm_sq_alpha_beta`: the norm formula `‖(αI + βP) h‖² = (α² + qβ²) ‖h‖²` on `H₀` used for the
  table entries.

**Not formalized here**: the identification of the no-cross parts with `q V C V^*` (operators on
`L²(ν_F)`), the Gram table of the synthesis maps `V_a^* V_b = αI + βP` (the values `(α, β)`), the
centring step and the actual-centring step; the operator inputs enter only through `gamma5_rows`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleRecords

/-! ## The weighted Schur test -/

/-- **The weighted Schur test.** For a nonnegative symmetric kernel `C` on a finite set, a positive
weight `w` and `λ ≥ 0` with `∑_b C(a, b) w(b) ≤ λ w(a)` for every `a`,
`∑_a (∑_b C(a, b) x(b))² ≤ λ² ∑_a x(a)²`. -/
theorem schur_weighted {ι : Type*} [Fintype ι] (C : ι → ι → ℝ) (w : ι → ℝ) {lam : ℝ}
    (hC : ∀ a b, 0 ≤ C a b) (hsym : ∀ a b, C a b = C b a) (hw : ∀ a, 0 < w a)
    (hlam : 0 ≤ lam) (hrow : ∀ a, ∑ b, C a b * w b ≤ lam * w a) (x : ι → ℝ) :
    ∑ a, (∑ b, C a b * x b) ^ 2 ≤ lam ^ 2 * ∑ a, x a ^ 2 := by
  -- Cauchy–Schwarz in each row
  have hrowCS : ∀ a, (∑ b, C a b * x b) ^ 2 ≤
      (∑ b, C a b * w b) * ∑ b, C a b * (x b ^ 2 / w b) := by
    intro a
    have key := Finset.sum_mul_sq_le_sq_mul_sq univ (fun b => Real.sqrt (C a b * w b))
      (fun b => Real.sqrt (C a b / w b) * x b)
    have e1 : ∀ b, Real.sqrt (C a b * w b) * (Real.sqrt (C a b / w b) * x b) = C a b * x b := by
      intro b
      rw [← mul_assoc, ← Real.sqrt_mul (mul_nonneg (hC a b) (hw b).le)]
      have : C a b * w b * (C a b / w b) = C a b ^ 2 := by
        field_simp [(hw b).ne']
      rw [this, Real.sqrt_sq (hC a b)]
    have e2 : ∀ b, Real.sqrt (C a b * w b) ^ 2 = C a b * w b := fun b =>
      Real.sq_sqrt (mul_nonneg (hC a b) (hw b).le)
    have e3 : ∀ b, (Real.sqrt (C a b / w b) * x b) ^ 2 = C a b * (x b ^ 2 / w b) := by
      intro b
      rw [mul_pow, Real.sq_sqrt (div_nonneg (hC a b) (hw b).le)]
      field_simp [(hw b).ne']
    simp only [e1, e2, e3] at key
    exact key
  have hnonneg : ∀ a, 0 ≤ ∑ b, C a b * (x b ^ 2 / w b) := fun a =>
    Finset.sum_nonneg fun b _ => mul_nonneg (hC a b) (div_nonneg (sq_nonneg _) (hw b).le)
  calc ∑ a, (∑ b, C a b * x b) ^ 2
      ≤ ∑ a, (∑ b, C a b * w b) * ∑ b, C a b * (x b ^ 2 / w b) :=
        Finset.sum_le_sum fun a _ => hrowCS a
    _ ≤ ∑ a, lam * w a * ∑ b, C a b * (x b ^ 2 / w b) :=
        Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hrow a) (hnonneg a)
    _ = lam * ∑ b, (x b ^ 2 / w b) * ∑ a, C b a * w a := by
        rw [Finset.mul_sum]
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro b _
        apply Finset.sum_congr rfl
        intro a _
        rw [hsym a b]
        ring
    _ ≤ lam * ∑ b, (x b ^ 2 / w b) * (lam * w b) := by
        apply mul_le_mul_of_nonneg_left _ hlam
        exact Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hrow b) (div_nonneg (sq_nonneg _) (hw b).le)
    _ = lam ^ 2 * ∑ a, x a ^ 2 := by
        rw [Finset.mul_sum, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        field_simp [(hw b).ne']

/-- **The weighted Schur test, bilinear form**: `|⟨y, C x⟩| ≤ λ ‖x‖ ‖y‖`. -/
theorem schur_weighted_form {ι : Type*} [Fintype ι] (C : ι → ι → ℝ) (w : ι → ℝ) {lam : ℝ}
    (hC : ∀ a b, 0 ≤ C a b) (hsym : ∀ a b, C a b = C b a) (hw : ∀ a, 0 < w a)
    (hlam : 0 ≤ lam) (hrow : ∀ a, ∑ b, C a b * w b ≤ lam * w a) (x y : ι → ℝ) :
    |∑ a, y a * ∑ b, C a b * x b| ≤
      lam * Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ a, y a ^ 2) := by
  have hCS := Finset.sum_mul_sq_le_sq_mul_sq univ y (fun a => ∑ b, C a b * x b)
  have hS := schur_weighted C w hC hsym hw hlam hrow x
  have hx0 : 0 ≤ ∑ a, x a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hy0 : 0 ≤ ∑ a, y a ^ 2 := Finset.sum_nonneg fun a _ => sq_nonneg _
  have hsq : (∑ a, y a * ∑ b, C a b * x b) ^ 2 ≤
      (lam * Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ a, y a ^ 2)) ^ 2 := by
    rw [mul_pow, mul_pow, Real.sq_sqrt hx0, Real.sq_sqrt hy0]
    calc (∑ a, y a * ∑ b, C a b * x b) ^ 2
        ≤ (∑ a, y a ^ 2) * ∑ a, (∑ b, C a b * x b) ^ 2 := hCS
      _ ≤ (∑ a, y a ^ 2) * (lam ^ 2 * ∑ a, x a ^ 2) := mul_le_mul_of_nonneg_left hS hy0
      _ = lam ^ 2 * (∑ a, x a ^ 2) * (∑ a, y a ^ 2) := by ring
  have hR : 0 ≤ lam * Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ a, y a ^ 2) := by positivity
  exact abs_le_of_sq_le_sq' hsq hR |> fun h => abs_le.mpr h

/-! ## The matrix `C` and the test vector `w` -/

/-- **The collision matrix `C`** (`lem:record:conditional-collision`(d)): diagonal
`(4, 1, 4, 0, 0)`,
entries `1` at `01, 02, 12, 03, 24` and their transposes. -/
def collMat : Fin 5 → Fin 5 → ℝ :=
  ![![4, 1, 1, 1, 0],
    ![1, 1, 1, 0, 0],
    ![1, 1, 4, 0, 1],
    ![1, 0, 0, 0, 0],
    ![0, 0, 1, 0, 0]]

/-- **The test vector** `w = (1, 43367/10⁵, 1, 17820/10⁵, 17820/10⁵)`. -/
noncomputable def collVec : Fin 5 → ℝ :=
  ![1, 43367 / 100000, 1, 17820 / 100000, 17820 / 100000]

theorem collMat_symm (a b : Fin 5) : collMat a b = collMat b a := by
  fin_cases a <;> fin_cases b <;> rfl

theorem collMat_nonneg (a b : Fin 5) : 0 ≤ collMat a b := by
  fin_cases a <;> fin_cases b <;> simp [collMat]

theorem collVec_pos (a : Fin 5) : 0 < collVec a := by
  fin_cases a <;> norm_num [collVec]

/-- **The five quotients `(Cw)_a/w_a`, exactly as printed**: `561187/10⁵`, `243367/43367`,
`561187/10⁵`, `10⁵/17820`, `10⁵/17820`. -/
theorem collMat_rows :
    (∑ b, collMat 0 b * collVec b) / collVec 0 = 561187 / 100000 ∧
      (∑ b, collMat 1 b * collVec b) / collVec 1 = 243367 / 43367 ∧
      (∑ b, collMat 2 b * collVec b) / collVec 2 = 561187 / 100000 ∧
      (∑ b, collMat 3 b * collVec b) / collVec 3 = 100000 / 17820 ∧
      (∑ b, collMat 4 b * collVec b) / collVec 4 = 100000 / 17820 := by
  simp only [Fin.sum_univ_five, collMat, collVec]
  norm_num

/-- **All five quotients are below `56119/10000`.** -/
theorem collMat_quotients_lt :
    (561187 / 100000 : ℝ) < 56119 / 10000 ∧ (243367 / 43367 : ℝ) < 56119 / 10000 ∧
      (100000 / 17820 : ℝ) < 56119 / 10000 := by
  norm_num

/-- `C w ≤ (56119/10000) w`, row by row. -/
theorem collMat_row_le (a : Fin 5) :
    ∑ b, collMat a b * collVec b ≤ 56119 / 10000 * collVec a := by
  fin_cases a <;> simp only [Fin.sum_univ_five, collMat, collVec] <;> norm_num

/-- **`‖C‖ ≤ 56119/10000`** (`lem:record:conditional-collision`(d)): `‖C x‖² ≤ (56119/10000)² ‖x‖²`
for every `x ∈ ℝ⁵`. -/
theorem collMat_norm_sq_le (x : Fin 5 → ℝ) :
    ∑ a, (∑ b, collMat a b * x b) ^ 2 ≤ (56119 / 10000) ^ 2 * ∑ a, x a ^ 2 :=
  schur_weighted collMat collVec collMat_nonneg collMat_symm collVec_pos (by norm_num)
    collMat_row_le x

/-- **`‖C x‖ ≤ (56119/10000) ‖x‖`** in `ℓ²(Fin 5)`. -/
theorem collMat_norm_le (x : Fin 5 → ℝ) :
    Real.sqrt (∑ a, (∑ b, collMat a b * x b) ^ 2) ≤ 56119 / 10000 * Real.sqrt (∑ a, x a ^ 2) := by
  rw [Real.sqrt_le_left (by positivity), mul_pow,
    Real.sq_sqrt (Finset.sum_nonneg fun a _ => sq_nonneg (x a))]
  exact collMat_norm_sq_le x

/-- **The bilinear form**: `|⟨y, C x⟩| ≤ (56119/10000) ‖x‖ ‖y‖`. -/
theorem collMat_form_le (x y : Fin 5 → ℝ) :
    |∑ a, y a * ∑ b, collMat a b * x b| ≤
      56119 / 10000 * Real.sqrt (∑ a, x a ^ 2) * Real.sqrt (∑ a, y a ^ 2) :=
  schur_weighted_form collMat collVec collMat_nonneg collMat_symm collVec_pos (by norm_num)
    collMat_row_le x y

/-! ## The synthesis bound `Γ₅` (arithmetic) -/

/-- `a₅ = (r + q)/(1 - q)`. -/
noncomputable def a5 (q r : ℝ) : ℝ := (r + q) / (1 - q)

/-- `b₅ = q(1 + r)/((1 - q)(1 - 2q))`. -/
noncomputable def b5 (q r : ℝ) : ℝ := q * (1 + r) / ((1 - q) * (1 - 2 * q))

/-- `Γ₅ = 1 + 2(r + q)/(1 - q) + 2q(1 + r)/((1 - q)(1 - 2q))`. -/
noncomputable def gamma5 (q r : ℝ) : ℝ := 1 + 2 * a5 q r + 2 * b5 q r

/-- **`b₅ ≤ a₅`** for `0 ≤ q ≤ 1/5`, `q ≤ r` (as `q = r² ≤ r` at a prime). -/
theorem b5_le_a5 {q r : ℝ} (hq : 0 ≤ q) (hq5 : q ≤ 1 / 5) (hqr : q ≤ r) : b5 q r ≤ a5 q r := by
  have h1 : 0 < 1 - q := by linarith
  have h2 : 0 < 1 - 2 * q := by linarith
  unfold a5 b5
  rw [div_le_div_iff₀ (mul_pos h1 h2) h1]
  -- the difference is `(1 - q)(r(1 - 3q) - 2q²) ≥ 0`
  have hk : 0 ≤ r * (1 - 3 * q) - 2 * q ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hqr) (by linarith : (0 : ℝ) ≤ 1 - 3 * q),
      mul_nonneg hq (by linarith : (0 : ℝ) ≤ 1 - 5 * q)]
  nlinarith [mul_nonneg h1.le hk]

/-- **The `Γ₅` row bound** (`lem:record:conditional-collision`(d), "The synthesis maps"): the Gram
matrix of `V` on `H₀⁵` has unit diagonal blocks; if each row has its four off-diagonal entries
of norms `n₁, n₂ ≤ a₅` (at most two entries of the first kind) and `n₃, n₄ ≤ b₅`, the row sum,
hence (Schur test) `‖V|_{H₀⁵}‖²`, is at most `Γ₅ = 1 + 2a₅ + 2b₅`. The entry norms are
hypotheses (the displayed table with `‖αI + βP‖ = (α² + qβ²)^{1/2}` on `H₀`). -/
theorem gamma5_rows {q r n₁ n₂ n₃ n₄ : ℝ} (h₁ : n₁ ≤ a5 q r) (h₂ : n₂ ≤ a5 q r)
    (h₃ : n₃ ≤ b5 q r) (h₄ : n₄ ≤ b5 q r) : 1 + n₁ + n₂ + n₃ + n₄ ≤ gamma5 q r := by
  unfold gamma5
  linarith

/-! ### The Gram table of the synthesis maps (arithmetic)

At a prime `p = s²` (`q = 1/p`, `r = 1/s`), the entries `V_a^* V_b = αI + βP` on `H₀` displayed in
the proof of `lem:record:conditional-collision`(d) (`D₀ = (p - 1)(p - 2)`) have the norms
`(α² + qβ²)^{1/2}`; the table values are taken from the paper. Here: the entries `02, 04, 23` are at
most `a₅ = 1/(s - 1)` and the other seven at most `b₅ = s/((s - 1)(s² - 2))`. -/

theorem a5_eq {s : ℝ} (hs : 2 ≤ s) : a5 (1 / s ^ 2) (1 / s) = 1 / (s - 1) := by
  have h0 : s ≠ 0 := by linarith
  have h1 : s - 1 ≠ 0 := by linarith
  have h2 : s ^ 2 - 1 ≠ 0 := by nlinarith
  unfold a5
  field_simp
  ring

theorem b5_eq {s : ℝ} (hs : 2 ≤ s) :
    b5 (1 / s ^ 2) (1 / s) = s / ((s - 1) * (s ^ 2 - 2)) := by
  have h0 : s ≠ 0 := by linarith
  have h1 : s - 1 ≠ 0 := by linarith
  have h2 : s ^ 2 - 2 ≠ 0 := by nlinarith
  have h3 : s ^ 2 - 1 ≠ 0 := by nlinarith
  have h4 : s ^ 2 - 2 * 1 ≠ 0 := by nlinarith
  unfold b5
  field_simp
  ring

/-- **Entry `02`** (`α = -1/(p - 1)`, `β = p/(p - 1)`): norm `≤ a₅`. -/
theorem gram02_le {s : ℝ} (hs : 4 ≤ s) :
    Real.sqrt ((-1 / (s ^ 2 - 1)) ^ 2 + 1 / s ^ 2 * (s ^ 2 / (s ^ 2 - 1)) ^ 2) ≤
      a5 (1 / s ^ 2) (1 / s) := by
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < s ^ 2 - 1 := by nlinarith
  have hs0 : 0 < s := by linarith
  rw [a5_eq (by linarith), Real.sqrt_le_left (by positivity)]
  have e : (-1 / (s ^ 2 - 1)) ^ 2 + 1 / s ^ 2 * (s ^ 2 / (s ^ 2 - 1)) ^ 2 =
      (1 + s ^ 2) / (s ^ 2 - 1) ^ 2 := by
    field_simp
  rw [e, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (s ^ 2 - 1) ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by ring
  rw [this]
  nlinarith [mul_nonneg (sq_nonneg (s - 1)) hs0.le]

/-- **Entries `04`, `23`** (`α = 1/D₀`, `β = ± p/(p - 1)`): norm `≤ a₅`. -/
theorem gram04_le {s : ℝ} (hs : 4 ≤ s) :
    Real.sqrt ((1 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2 + 1 / s ^ 2 * (s ^ 2 / (s ^ 2 - 1)) ^ 2) ≤
      a5 (1 / s ^ 2) (1 / s) := by
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < s ^ 2 - 1 := by nlinarith
  have h3 : 1 ≤ s ^ 2 - 2 := by nlinarith
  have hs0 : 0 < s := by linarith
  rw [a5_eq (by linarith), Real.sqrt_le_left (by positivity)]
  have e : (1 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2 + 1 / s ^ 2 * (s ^ 2 / (s ^ 2 - 1)) ^ 2 =
      (1 + s ^ 2 * (s ^ 2 - 2) ^ 2) / ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2) ^ 2) := by
    field_simp
  rw [e, div_pow, one_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (s ^ 2 - 1) ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by ring
  rw [this]
  have hk : 1 ≤ (s ^ 2 - 2) ^ 2 := by nlinarith
  nlinarith [mul_nonneg (sq_nonneg (s - 1)) hs0.le,
    mul_le_mul_of_nonneg_left hk (mul_nonneg (sq_nonneg (s - 1)) (by linarith : (0 : ℝ) ≤ 2 * s)),
    mul_nonneg (sq_nonneg (s - 1)) (sq_nonneg (s ^ 2 - 2))]

/-- **Entries `01`, `12`** (`α = -1/(p - 1)`, `β = -p/D₀`): norm `≤ b₅`. -/
theorem gram01_le {s : ℝ} (hs : 4 ≤ s) :
    Real.sqrt ((-1 / (s ^ 2 - 1)) ^ 2 + 1 / s ^ 2 * (s ^ 2 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2) ≤
      b5 (1 / s ^ 2) (1 / s) := by
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < s ^ 2 - 1 := by nlinarith
  have h3 : 1 ≤ s ^ 2 - 2 := by nlinarith
  have hs0 : 0 < s := by linarith
  rw [b5_eq (by linarith), Real.sqrt_le_left (by positivity)]
  have e : (-1 / (s ^ 2 - 1)) ^ 2 + 1 / s ^ 2 * (s ^ 2 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2 =
      ((s ^ 2 - 2) ^ 2 + s ^ 2) / ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2) ^ 2) := by
    field_simp
  rw [e, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (s ^ 2 - 1) ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by ring
  rw [this]
  -- `((s² - 2)² + s²)(s - 1)²(s² - 2)² ≤ s²(s - 1)²(s + 1)²(s² - 2)²`
  have key : (s ^ 2 - 2) ^ 2 + s ^ 2 ≤ s ^ 2 * (s + 1) ^ 2 := by nlinarith
  have hpos : 0 ≤ (s - 1) ^ 2 * (s ^ 2 - 2) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hpos]

/-- **Entries `03`, `24`** (`α = 1/D₀`, `β = ± p/D₀`): norm `≤ b₅`. -/
theorem gram03_le {s : ℝ} (hs : 4 ≤ s) :
    Real.sqrt ((1 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2 +
        1 / s ^ 2 * (s ^ 2 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2) ≤
      b5 (1 / s ^ 2) (1 / s) := by
  have h1 : 0 < s - 1 := by linarith
  have h2 : 0 < s ^ 2 - 1 := by nlinarith
  have h3 : 1 ≤ s ^ 2 - 2 := by nlinarith
  have hs0 : 0 < s := by linarith
  rw [b5_eq (by linarith), Real.sqrt_le_left (by positivity)]
  have e : (1 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2 +
      1 / s ^ 2 * (s ^ 2 / ((s ^ 2 - 1) * (s ^ 2 - 2))) ^ 2 =
      (1 + s ^ 2) / ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2) ^ 2) := by
    field_simp
  rw [e, div_pow, div_le_div_iff₀ (by positivity) (by positivity)]
  have : (s ^ 2 - 1) ^ 2 = (s - 1) ^ 2 * (s + 1) ^ 2 := by ring
  rw [this]
  have key : 1 + s ^ 2 ≤ s ^ 2 * (s + 1) ^ 2 := by nlinarith
  have hpos : 0 ≤ (s - 1) ^ 2 * (s ^ 2 - 2) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hpos]

/-- **Entries `13`, `14`, `34`** (`α = ∓1/(p - 2)`, `β = 0`): norm `≤ b₅`. -/
theorem gram13_le {s : ℝ} (hs : 4 ≤ s) :
    Real.sqrt ((1 / (s ^ 2 - 2)) ^ 2 + 1 / s ^ 2 * 0 ^ 2) ≤ b5 (1 / s ^ 2) (1 / s) := by
  have h1 : 0 < s - 1 := by linarith
  have h3 : 1 ≤ s ^ 2 - 2 := by nlinarith
  have hs0 : 0 < s := by linarith
  rw [b5_eq (by linarith), Real.sqrt_le_left (by positivity)]
  rw [show (0 : ℝ) ^ 2 = 0 by norm_num, mul_zero, add_zero, div_pow, div_pow, one_pow,
    div_le_div_iff₀ (by positivity) (by positivity)]
  have key : (s - 1) ^ 2 ≤ s ^ 2 := by nlinarith
  have hpos : 0 ≤ (s ^ 2 - 2) ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left key hpos]

/-- **The norm formula of the Gram table**: on `H₀`, `‖(αI + βP) h‖² = (α² + qβ²) ‖h‖²`, `q = 1/p`,
for the Paley operator `P = paleyOp` over a field with `p ≡ 3 (mod 4)` elements (`P^* = -P` and
`P^*P = qI` on `H₀`); so `‖αI + βP‖ = (α² + qβ²)^{1/2}` there. -/
theorem norm_sq_alpha_beta {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (α β : ℝ) (h : F → ℝ)
    (hh : ∑ s, h s = 0) :
    ∑ s, (α * h s + β * Sarkozy.TraceMixing.paleyOp h s) ^ 2 =
      (α ^ 2 + β ^ 2 / (Fintype.card F : ℝ)) * ∑ s, h s ^ 2 := by
  have hexp : ∀ s, (α * h s + β * Sarkozy.TraceMixing.paleyOp h s) ^ 2 =
      α ^ 2 * h s ^ 2 + 2 * α * β * (h s * Sarkozy.TraceMixing.paleyOp h s) +
        β ^ 2 * Sarkozy.TraceMixing.paleyOp h s ^ 2 := fun s => by ring
  simp only [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, paleyOp_form_self_zero h3 h, paleyOp_norm_sq_meanZero hF h hh]
  ring

end Sarkozy.MiddleRecords

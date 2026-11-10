module

public import Sarkozy.PartVRecords.MergeRecords

@[expose] public section

/-!
# Softened laws (`def:dense-comparison`)

`paper/sections/26_upper_comparison.tex`, paragraph "Dense laws" and `def:dense-comparison`.

For an `LE` or `EL` record of degree two with half graph `H` on `n` labels and half law `μ = λ_H`
(here: any law `μ` on the half configurations `x : Fin n → F`), and a real `n × n` matrix `D` with
entries in `[-1, 1]`:

  `H_D(x, y) = 1{x_i ≠ y_j ∀ i, j} ∏_{i,j} (1 + D_{ij} χ(y_j - x_i))`,
  `K_D = H_D / Z_D`, `Z_D = ∫ H_D d(μ ⊗ μ)` (`Hdense`, `Zdense`, `Kdense`).

The old law is `K_{D₀}` with `D₀` the signed cross-incidence matrix of the record. Given the
*required edges* `req` (the projections of the queries, each from layer `0` to layer `1`), the
**softening** `D₁` of `D₀` with parameters `(β, β̃) ∈ [0, 1]²` (`soften`):
* every required old edge is kept, and every missing required edge is added, with coefficient `1`;
* with `R`, `C` the rows and columns of the added edges, an unrequired old entry `(i, j)` is
  multiplied by `β` if `i ∈ R` or `j ∈ C`, and otherwise by `β̃` if `j ∈ R` or `i ∈ C`;
* all other entries are unchanged.

**Proved** (the last sentence of the definition), when no required edge is an old edge of the
opposite direction (`D₀_{ij} ≠ -1` on `req`):
* every required old edge is kept and every required edge has coefficient one (`soften_req`,
  `soften_keeps`);
* the entries of `D₁` stay in `[-1, 1]` (`soften_mem_Icc`), so `H_{D₁} ≥ 0` (`Hdense_nonneg`);
* the support of `H_{D₁}` satisfies every required query: `H_{D₁}(x, y) ≠ 0` and `(i, j)` required
  give `χ(y_j - x_i) = 1` (`Hdense_support_req`).

The parameters of the paper: the dense `EL` law uses `(β, β̃) = (7/10, 2/5)` (`denseEL_params`); the
`LE` components use `β̃ = 1` and `β ∈ {0, 1/5, 2/5, 1}` (`denseLE_betas`). The required-edge lists
(the projections of `eq:upper-twelve` and of `𝓔₆` under the records' emissions) are not entered.
-/

namespace Sarkozy.PartVRecords

open Finset

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

variable {n : ℕ}

/-- **`H_D(x, y) = 1{x_i ≠ y_j ∀ i, j} ∏_{i,j} (1 + D_{ij} χ(y_j - x_i))`.** -/
noncomputable def Hdense (D : Fin n → Fin n → ℝ) (x y : Fin n → F) : ℝ :=
  (if ∀ i j, x i ≠ y j then 1 else 0) * ∏ i, ∏ j, (1 + D i j * ((χ (y j - x i) : ℤ) : ℝ))

/-- `Z_D = ∫ H_D d(μ ⊗ μ)`. -/
noncomputable def Zdense (μ : FiniteLaw (Fin n → F)) (D : Fin n → Fin n → ℝ) : ℝ :=
  ∑ x, ∑ y, μ.weight x * μ.weight y * Hdense D x y

/-- **The softened law's density** `K_D = H_D / Z_D` relative to `μ ⊗ μ`. -/
noncomputable def Kdense (μ : FiniteLaw (Fin n → F)) (D : Fin n → Fin n → ℝ) (x y : Fin n → F) :
    ℝ :=
  Hdense D x y / Zdense μ D

/-- The added edges: the required edges that are not old edges. -/
noncomputable def addedEdges (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) :
    Finset (Fin n × Fin n) :=
  req.filter fun e => D₀ e.1 e.2 ≠ 1

/-- The rows `R` of the added edges. -/
noncomputable def addedRows (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) :
    Finset (Fin n) :=
  (addedEdges D₀ req).image Prod.fst

/-- The columns `C` of the added edges. -/
noncomputable def addedCols (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) :
    Finset (Fin n) :=
  (addedEdges D₀ req).image Prod.snd

/-- **The softening `D₁` of `D₀`** with parameters `(β, β̃)` and required edges `req`. -/
noncomputable def soften (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) (β βt : ℝ)
    (i j : Fin n) : ℝ :=
  if (i, j) ∈ req then 1
  else if D₀ i j ≠ 0 then
    (if i ∈ addedRows D₀ req ∨ j ∈ addedCols D₀ req then β * D₀ i j
     else if j ∈ addedRows D₀ req ∨ i ∈ addedCols D₀ req then βt * D₀ i j
     else D₀ i j)
  else D₀ i j

/-- **Every required edge has coefficient one.** -/
theorem soften_req (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) (β βt : ℝ)
    {i j : Fin n} (h : (i, j) ∈ req) : soften D₀ req β βt i j = 1 := by
  unfold soften
  rw [ite_eq_left h]

/-- **Every required old edge is kept** (an old edge `x_i → y_j` has `D₀_{ij} = 1`). -/
theorem soften_keeps (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) (β βt : ℝ)
    {i j : Fin n} (h : (i, j) ∈ req) (hold : D₀ i j = 1) :
    soften D₀ req β βt i j = D₀ i j := by
  rw [soften_req D₀ req β βt h, hold]

/-- Entries outside the required edges and the old entries are unchanged. -/
theorem soften_zero (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) (β βt : ℝ)
    {i j : Fin n} (h : (i, j) ∉ req) (h0 : D₀ i j = 0) : soften D₀ req β βt i j = 0 := by
  unfold soften
  simp only [h, ↓reduceIte, h0, ne_eq, not_true_eq_false]

/-- **The entries of the softening stay in `[-1, 1]`** for `β, β̃ ∈ [0, 1]`. -/
theorem soften_mem_Icc (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) {β βt : ℝ}
    (hβ : 0 ≤ β ∧ β ≤ 1) (hβt : 0 ≤ βt ∧ βt ≤ 1) (hD : ∀ i j, -1 ≤ D₀ i j ∧ D₀ i j ≤ 1)
    (i j : Fin n) : -1 ≤ soften D₀ req β βt i j ∧ soften D₀ req β βt i j ≤ 1 := by
  have hscale : ∀ c : ℝ, 0 ≤ c → c ≤ 1 → -1 ≤ c * D₀ i j ∧ c * D₀ i j ≤ 1 := by
    intro c hc0 hc1
    obtain ⟨h1, h2⟩ := hD i j
    constructor <;> nlinarith
  unfold soften
  split_ifs
  · norm_num
  · exact hscale β hβ.1 hβ.2
  · exact hscale βt hβt.1 hβt.2
  · exact hD i j
  · exact hD i j

/-- `H_D ≥ 0` when the entries of `D` are in `[-1, 1]` (each factor `1 + D_{ij} χ ≥ 0`). -/
theorem Hdense_nonneg {D : Fin n → Fin n → ℝ} (hD : ∀ i j, -1 ≤ D i j ∧ D i j ≤ 1)
    (x y : Fin n → F) : 0 ≤ Hdense D x y := by
  unfold Hdense
  refine mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun i _ => prod_nonneg fun j _ => ?_)
  have hχ : ((χ (y j - x i) : ℤ) : ℝ) = 0 ∨ ((χ (y j - x i) : ℤ) : ℝ) = 1 ∨
      ((χ (y j - x i) : ℤ) : ℝ) = -1 := by
    by_cases h0 : y j - x i = 0
    · left
      rw [h0, quadraticChar_zero]
      norm_num
    · rcases quadraticChar_dichotomy h0 with h | h
      · right; left
        rw [h]
        norm_num
      · right; right
        rw [h]
        norm_num
  obtain ⟨h1, h2⟩ := hD i j
  rcases hχ with h | h | h <;> rw [h] <;> linarith

/-- **The support of `H_D` satisfies every edge with coefficient one**: if `H_D(x, y) ≠ 0` and
`D_{ij} = 1`, then `χ(y_j - x_i) = 1`. -/
theorem Hdense_support {D : Fin n → Fin n → ℝ} {x y : Fin n → F} (hH : Hdense D x y ≠ 0)
    {i j : Fin n} (hij : D i j = 1) : χ (y j - x i) = 1 := by
  unfold Hdense at hH
  have hdist : ∀ i j, x i ≠ y j := by
    by_contra h
    apply hH
    rw [ite_eq_right h, zero_mul]
  have hfac : 1 + D i j * ((χ (y j - x i) : ℤ) : ℝ) ≠ 0 := by
    intro h0
    apply hH
    rw [Finset.prod_eq_zero (mem_univ i) (Finset.prod_eq_zero (mem_univ j) h0), mul_zero]
  have hne : y j - x i ≠ 0 := sub_ne_zero.mpr (Ne.symm (hdist i j))
  rcases quadraticChar_dichotomy hne with h | h
  · exact h
  · exfalso
    apply hfac
    rw [hij, h]
    norm_num

/-- **The support of `H_{D₁}` satisfies every required query** (`def:dense-comparison`, last
sentence). -/
theorem Hdense_support_req (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) (β βt : ℝ)
    {x y : Fin n → F} (hH : Hdense (soften D₀ req β βt) x y ≠ 0) {i j : Fin n}
    (hij : (i, j) ∈ req) : χ (y j - x i) = 1 :=
  Hdense_support hH (soften_req D₀ req β βt hij)

/-- **`H_{D₁} ≥ 0`** for the softening of a signed incidence matrix (`def:dense-comparison`). -/
theorem Hdense_soften_nonneg (D₀ : Fin n → Fin n → ℝ) (req : Finset (Fin n × Fin n)) {β βt : ℝ}
    (hβ : 0 ≤ β ∧ β ≤ 1) (hβt : 0 ≤ βt ∧ βt ≤ 1) (hD : ∀ i j, -1 ≤ D₀ i j ∧ D₀ i j ≤ 1)
    (x y : Fin n → F) : 0 ≤ Hdense (soften D₀ req β βt) x y :=
  Hdense_nonneg (soften_mem_Icc D₀ req hβ hβt hD) x y

/-- The parameters `(β, β̃) = (7/10, 2/5)` of the dense `EL` law. -/
def denseEL_params : ℚ × ℚ := (7 / 10, 2 / 5)

/-- The parameters `β ∈ {0, 1/5, 2/5, 1}` (with `β̃ = 1`) of the `LE` components. -/
def denseLE_betas : Finset ℚ := {0, 1 / 5, 2 / 5, 1}

/-- The paper's parameters lie in `[0, 1]`. -/
theorem dense_params_mem :
    (0 ≤ denseEL_params.1 ∧ denseEL_params.1 ≤ 1) ∧ (0 ≤ denseEL_params.2 ∧ denseEL_params.2 ≤ 1) ∧
      ∀ β ∈ denseLE_betas, 0 ≤ β ∧ β ≤ 1 := by
  refine ⟨by norm_num [denseEL_params], by norm_num [denseEL_params], ?_⟩
  intro β hβ
  simp only [denseLE_betas, mem_insert, mem_singleton] at hβ
  rcases hβ with rfl | rfl | rfl | rfl <;> norm_num

end Sarkozy.PartVRecords

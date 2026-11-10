module

public import Sarkozy.MeanCredit.Completion
public import Sarkozy.ClassData.Residuals

@[expose] public section

/-!
# Labelled diagonals aggregated from selections, and the normalization of family (i)

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (family (i): "average the pair
selection over the `C(n,2)` pairs of an `n`-tag term ... coefficient `4/(H_*² C(n,2))` on the
selected pair"; the residual table); `eq:joint-alpha`.

The formal class group indexes the mean credit by finitely many labelled diagonals `Θ_L`
(`|Θ_L| ≤ N` uniformly), with the paper's coefficient `diagB` per label. The comparison and the mean
naturally produce one diagonal per *selection* (a pair of fold arms with its outside factors). This
file aggregates selection diagonals into labelled ones:

* `agg S lab wt f j = ∑_{ω ∈ S, lab ω = j} wt_j f(ω)`, and **`sum_mul_agg`**:
  `∑_j c_j agg_j(f) = ∑_{ω ∈ S} coefOf c wt (lab ω) f(ω)`, i.e. a labelled coefficient `c_j` acts on
  each selection of label `j` with coefficient `c_j wt_j`;
* `agg_le_agg`, `agg_nonneg`: monotonicity;
* **`wtP`**: the paper's aggregation weights, `1/C(j+2,2)` on the `F²` labels (class `10`) with
  `j ≤ 10`, and `1` elsewhere. With them `diagB` on a label means `diagB · wtP` per selection, which
  for the `F²` part `4/H_*²` is exactly family (i)'s `4/(H_*² C(j+2,2))` (**`familyI_coef`**).
* **`familyI_completed`**: the completion of that per-pair coefficient over pairs and outside
  factors is the `j`-th term `4 x² w^j/(H_*² (j+2)!)` of `64 Δ_α` (`eq:joint-alpha`), while
  `4/H_*²` per pair would give `C(j+2,2)` times it (**`familyI_overclaim`**).

**Untrusted numerics** (scratch Python, 50 digits, at E4's capture of the T1 point): the completion
with `4/(H_*² C(j+2,2))` reproduces the closed form `Δ_α = 0.00695984233…` to `10⁻⁴⁸`; with `4/H_*²`
per pair it would be `1.690 Δ_α`, an overclaim of `0.307` in the 64-scaled gate (larger than the
`0.129` spare of `MeanCredit.upperFree_room` at E3's v2 ledger; RG's rebase states the spare as
`12/5`). The tail `j ≥ 11` of family (i) is `1.9·10⁻¹³` (`1.2·10⁻¹¹` in the 64-scaled gate).
-/

open Finset

namespace Sarkozy.MeanCredit

open Sarkozy.ClassData

section Agg

variable {σ : Type*} {K : Type*} [DecidableEq K]

/-- The coefficient that a labelled coefficient `c` gives a selection of label `o`: `c_j wt_j` on
label `j`, `0` for an unlabelled selection. -/
def coefOf (c wt : K → ℝ) (o : Option K) : ℝ := o.elim 0 fun j => c j * wt j

/-- **The aggregated diagonal** `agg_j(f) = ∑_{ω ∈ S, lab ω = j} wt_j f(ω)`. -/
noncomputable def agg (S : Finset σ) (lab : σ → Option K) (wt : K → ℝ) (f : σ → ℝ) (j : K) : ℝ :=
  ∑ ω ∈ S.filter (fun ω => lab ω = some j), wt j * f ω

/-- **Labelled coefficients act on the selections**:
`∑_j c_j agg_j(f) = ∑_ω coefOf c wt (lab ω) f(ω)`. -/
theorem sum_mul_agg [Fintype K] (S : Finset σ) (lab : σ → Option K) (wt c : K → ℝ)
    (g : σ → ℝ) :
    ∑ j, c j * agg S lab wt g j = ∑ ω ∈ S, coefOf c wt (lab ω) * g ω := by
  rw [← sum_fiberwise S lab (fun ω => coefOf c wt (lab ω) * g ω), Fintype.sum_option]
  have h0 : ∑ ω ∈ S with lab ω = none, coefOf c wt (lab ω) * g ω = 0 :=
    sum_eq_zero fun ω hω => by rw [(mem_filter.mp hω).2]; simp [coefOf]
  rw [h0, zero_add]
  refine sum_congr rfl fun j _ => ?_
  unfold agg
  rw [mul_sum]
  refine sum_congr rfl fun ω hω => ?_
  rw [(mem_filter.mp hω).2]
  simp only [coefOf, Option.elim_some]
  ring

theorem agg_le_agg (S : Finset σ) (lab : σ → Option K) {wt : K → ℝ} (hwt : ∀ j, 0 ≤ wt j)
    {f g : σ → ℝ} (h : ∀ ω ∈ S, lab ω ≠ none → f ω ≤ g ω) (j : K) :
    agg S lab wt f j ≤ agg S lab wt g j := by
  refine sum_le_sum fun ω hω => ?_
  have h1 := (mem_filter.mp hω)
  have hl : lab ω ≠ none := by rw [h1.2]; exact Option.some_ne_none j
  exact mul_le_mul_of_nonneg_left (h ω h1.1 hl) (hwt j)

theorem agg_nonneg (S : Finset σ) (lab : σ → Option K) {wt : K → ℝ} (hwt : ∀ j, 0 ≤ wt j)
    {f : σ → ℝ} (h : ∀ ω ∈ S, 0 ≤ f ω) (j : K) : 0 ≤ agg S lab wt f j :=
  sum_nonneg fun ω hω => mul_nonneg (hwt j) (h ω (mem_filter.mp hω).1)

theorem agg_add (S : Finset σ) (lab : σ → Option K) (wt : K → ℝ) (f g : σ → ℝ) (j : K) :
    agg S lab wt (fun ω => f ω + g ω) j = agg S lab wt f j + agg S lab wt g j := by
  unfold agg
  rw [← sum_add_distrib]
  exact sum_congr rfl fun ω _ => by ring

theorem agg_smul (S : Finset σ) (lab : σ → Option K) (wt : K → ℝ) (f : σ → ℝ) (c : ℝ) (j : K) :
    agg S lab wt (fun ω => c * f ω) j = c * agg S lab wt f j := by
  unfold agg
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by ring

omit [DecidableEq K] in
theorem coefOf_nonneg {c wt : K → ℝ} (hc : ∀ j, 0 ≤ c j) (hwt : ∀ j, 0 ≤ wt j) (o : Option K) :
    0 ≤ coefOf c wt o := by
  rcases o with _ | j
  · exact le_rfl
  · exact mul_nonneg (hc j) (hwt j)

end Agg

/-! ## The paper's aggregation weights -/

/-! ## The exact aggregation: weights from the per-selection coefficients -/

/-- **The exact aggregation weights**: for a label `k` with paper type `labK k` and per-selection
mean coefficient `μK k` (the coefficient the paper's family proves on each selection of that label),
`wt_k = μK_k / diagB(labK k)` (and `1` when `diagB = 0`). With them the formal mean coefficient
`diagB` of a label acts on each of its selections with exactly `μK` (`coefOf_wtOf`). -/
noncomputable def wtOf {K : Type*} (labK : K → PaperDiag) (μK : K → ℝ) (k : K) : ℝ :=
  if (diagB (labK k) : ℝ) = 0 then 1 else μK k / diagB (labK k)

theorem wtOf_nonneg {K : Type*} (labK : K → PaperDiag) {μK : K → ℝ} (hμ : ∀ k, 0 ≤ μK k)
    (k : K) : 0 ≤ wtOf labK μK k := by
  unfold wtOf
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (hμ k) (by exact_mod_cast diagB_nonneg (labK k))

/-- **`diagB` with the exact weights is the per-selection coefficient**, on every label of positive
`diagB`; on a label with `diagB = 0` it is `0`. -/
theorem coefOf_wtOf {K : Type*} (labK : K → PaperDiag) (μK : K → ℝ) (k : K) :
    coefOf (fun j => (diagB (labK j) : ℝ)) (wtOf labK μK) (some k) =
      if (diagB (labK k) : ℝ) = 0 then 0 else μK k := by
  simp only [coefOf, Option.elim_some, wtOf]
  split_ifs with h
  · rw [h, zero_mul]
  · field_simp

/-- **The aggregation weights of the paper's labels** (`prop:joint-middle-mean`, family (i)):
`1/C(j+2,2)` on the `F²` labels (class `10`) of outside degree `j ≤ 10`, the average over the
`C(j+2,2)` pairs of a `(j+2)`-tag term; `1` on all other labels. The `F²` tail label `(10, 11)`
also gets `1/C(13,2)`; selections of `F²` type with more than `11` outside factors must therefore be
left unlabelled (booked in `ρ`), since family (i) gives them only `4/(H_*² C(n,2))`, `n ≥ 14`.

`wtP` is right for the family-(i) part `4/H_*²` of `diagB(10, j)` only: the family-(iv) part `σ²ρ^j`
of the same label is then credited `σ²ρ^j/C(j+2,2)` per selection. When the two families sit on
different diagonals, use separate labels with the exact weights `wtOf` instead. -/
def wtP (d : PaperDiag) : ℚ :=
  if d.1.val = 10 then 1 / (Nat.choose (d.2.val + 2) 2 : ℚ) else 1

theorem wtP_pos (d : PaperDiag) : 0 < wtP d := by
  unfold wtP
  split_ifs
  · have : (0 : ℚ) < Nat.choose (d.2.val + 2) 2 := by
      exact_mod_cast Nat.choose_pos (by omega)
    positivity
  · exact one_pos

theorem wtP_le_one (d : PaperDiag) : wtP d ≤ 1 := by
  unfold wtP
  split_ifs
  · have : (1 : ℚ) ≤ Nat.choose (d.2.val + 2) 2 := by
      exact_mod_cast Nat.choose_pos (by omega)
    rw [div_le_one (by linarith)]
    exact this
  · exact le_rfl

/-- **Family (i)'s per-pair coefficient** (`prop:joint-middle-mean`, proof of family (i)): on an
`F²` label of outside degree `j ≤ 10`, the `F²` part `4/H_*²` of `diagB` acts on each selection with
coefficient `4/(H_*² C(j+2,2))`, which is what family (i) proves. -/
theorem familyI_coef (j : Fin 12) :
    4 / hStar ^ 2 * wtP (10, j) = 4 / (hStar ^ 2 * (Nat.choose (j.val + 2) 2 : ℚ)) := by
  have h : ((10 : Fin 16) : ℕ) = 10 := rfl
  unfold wtP
  simp only [h, ↓reduceIte]
  rw [mul_one_div, div_div]

/-- **The completion of family (i)** (`eq:joint-alpha`): the per-pair coefficient
`4/(H² C(j+2,2))`, completed over unordered pairs (`x²/2`) and `j` outside factors (`w^j/j!`), is
`4 x² w^j / (H² (j+2)!)`, the `j`-th term of `64 Δ_α = 4 x²/H² ∑_j w^j/(j+2)!`. -/
theorem familyI_completed (H x w : ℝ) (hH : H ≠ 0) (j : ℕ) :
    4 / (H ^ 2 * (Nat.choose (j + 2) 2 : ℝ)) * (x ^ 2 / 2) * (w ^ j / j.factorial) =
      4 * x ^ 2 * w ^ j / (H ^ 2 * (j + 2).factorial) := by
  have hc : (Nat.choose (j + 2) 2 : ℝ) * 2 * j.factorial = (j + 2).factorial := by
    have h := Nat.choose_mul_factorial_mul_factorial (n := j + 2) (k := 2) (by omega)
    have e : j + 2 - 2 = j := by omega
    rw [e] at h
    have h' : ((Nat.choose (j + 2) 2 * Nat.factorial 2 * j.factorial : ℕ) : ℝ) =
        ((j + 2).factorial : ℝ) := by exact_mod_cast h
    push_cast at h'
    simpa [Nat.factorial] using h'
  have hc0 : (Nat.choose (j + 2) 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  have hf0 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  rw [← hc]
  field_simp

/-- **The overclaim without the normalization**: `4/H²` per pair, completed, is `C(j+2,2)` times the
term of `64 Δ_α`. -/
theorem familyI_overclaim (H x w : ℝ) (hH : H ≠ 0) (j : ℕ) :
    4 / H ^ 2 * (x ^ 2 / 2) * (w ^ j / j.factorial) =
      (Nat.choose (j + 2) 2 : ℝ) * (4 * x ^ 2 * w ^ j / (H ^ 2 * (j + 2).factorial)) := by
  rw [← familyI_completed H x w hH j]
  have hc0 : (Nat.choose (j + 2) 2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.choose_pos (by omega)).ne'
  field_simp

end Sarkozy.MeanCredit

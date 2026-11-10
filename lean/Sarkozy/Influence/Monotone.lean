module

public import Sarkozy.Influence.OpBound

/-!
# Pinned influence, V: monotonicity of `(I - E)^{-1}` under restriction

`lem:mid:allpin` and `prop:middle-negative` (a) (`13_cuts_correlations.tex`) use
`[(I - 𝓔_{F'F'})^{-1}]_ij ≤ [(I - 𝓔)^{-1}]_ij` for `F' ⊆ F`, `𝓔 ≥ 0` and `‖𝓔‖ < 1`.
The paper's proof compares the Neumann series entrywise. Here the series is replaced by its
partial sums `S_n = I + E S_{n-1}`, which are nonnegative and increase with the index set
(`neumannPartial_mono`). The differences `Q - S_n` decay geometrically, column by column
(`dist_le`). Hence `Q' ≤ Q` entrywise (`inverse_restrict_le`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

variable {U : Type*} [DecidableEq U]

/-- The partial sums of the Neumann series of `(I - E)^{-1}` on `F`:
`S_0 = 0`, `S_{n+1} = I + E S_n` (products summed over `F`). -/
def neumannPartial (F : Finset U) (E : U → U → ℝ) : ℕ → U → U → ℝ
  | 0 => fun _ _ => 0
  | n + 1 => fun i j => (if i = j then 1 else 0) + ∑ l ∈ F, E i l * neumannPartial F E n l j

theorem neumannPartial_nonneg (F : Finset U) {E : U → U → ℝ} (hE : ∀ i j, 0 ≤ E i j) :
    ∀ n i j, 0 ≤ neumannPartial F E n i j := by
  intro n
  induction n with
  | zero => intro i j; exact le_refl 0
  | succ n ih =>
    intro i j
    simp only [neumannPartial]
    refine add_nonneg (by split_ifs <;> norm_num) (Finset.sum_nonneg (fun l _ => ?_))
    exact mul_nonneg (hE i l) (ih l j)

theorem neumannPartial_mono {F F' : Finset U} (hF : F' ⊆ F) {E : U → U → ℝ}
    (hE : ∀ i j, 0 ≤ E i j) : ∀ n i j, neumannPartial F' E n i j ≤ neumannPartial F E n i j := by
  intro n
  induction n with
  | zero => intro i j; exact le_refl 0
  | succ n ih =>
    intro i j
    simp only [neumannPartial]
    refine add_le_add (le_refl _) ?_
    calc ∑ l ∈ F', E i l * neumannPartial F' E n l j ≤ ∑ l ∈ F', E i l * neumannPartial F E n l j :=
          Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (ih l j) (hE i l))
      _ ≤ ∑ l ∈ F, E i l * neumannPartial F E n l j :=
          Finset.sum_le_sum_of_subset_of_nonneg hF (fun l _ _ =>
            mul_nonneg (hE i l) (neumannPartial_nonneg F hE n l j))

omit [DecidableEq U] in
theorem abs_le_vnorm {F : Finset U} {v : U → ℝ} {i : U} (hi : i ∈ F) : |v i| ≤ vnorm F v := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Finset.single_le_sum (f := fun l => v l ^ 2)
    (fun l _ => sq_nonneg _) hi)

/-- `|Q_ij - (S_n)_ij| ≤ eⁿ ‖Q_{·j}‖` for `i, j ∈ F`, when `Q = I + E Q` on `F × F` and
`‖E‖ ≤ e`. -/
theorem dist_le (F : Finset U) (E Q : U → U → ℝ) {e : ℝ} (he0 : 0 ≤ e)
    (hE : OpBound F F E e)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j)
    {j : U} (hj : j ∈ F) :
    ∀ n, vnorm F (fun i => Q i j - neumannPartial F E n i j) ≤ e ^ n * vnorm F (fun i => Q i j) := by
  intro n
  induction n with
  | zero =>
    simp only [neumannPartial, sub_zero, pow_zero, one_mul, le_refl]
  | succ n ih =>
    have hrec : ∀ i ∈ F, Q i j - neumannPartial F E (n + 1) i j =
        ∑ l ∈ F, E i l * (Q l j - neumannPartial F E n l j) := by
      intro i hi
      simp only [neumannPartial]
      rw [hQ i hi j hj]
      simp only [mul_sub, Finset.sum_sub_distrib]
      ring
    calc vnorm F (fun i => Q i j - neumannPartial F E (n + 1) i j)
        = vnorm F (fun i => ∑ l ∈ F, E i l * (Q l j - neumannPartial F E n l j)) :=
          vnorm_congr hrec
      _ ≤ e * vnorm F (fun i => Q i j - neumannPartial F E n i j) := hE.vnorm_le he0 _
      _ ≤ e * (e ^ n * vnorm F (fun i => Q i j)) := mul_le_mul_of_nonneg_left ih he0
      _ = e ^ (n + 1) * vnorm F (fun i => Q i j) := by ring

/-- **Monotonicity under restriction**: for `F' ⊆ F`, `E ≥ 0` and `‖E_{FF}‖ ≤ e < 1`,
`[(I - E_{F'F'})^{-1}]_ij ≤ [(I - E_{FF})^{-1}]_ij` for `i, j ∈ F'`. The two inverses are
given by `Q' = I + E Q'` on `F' × F'` and `Q = I + E Q` on `F × F`. -/
theorem inverse_restrict_le {F F' : Finset U} (hF : F' ⊆ F) (E Q Q' : U → U → ℝ)
    (hE0 : ∀ i j, 0 ≤ E i j) {e : ℝ} (he0 : 0 ≤ e) (he1 : e < 1) (hE : OpBound F F E e)
    (hQ : ∀ i ∈ F, ∀ j ∈ F, Q i j = (if i = j then 1 else 0) + ∑ l ∈ F, E i l * Q l j)
    (hQ' : ∀ i ∈ F', ∀ j ∈ F', Q' i j = (if i = j then 1 else 0) + ∑ l ∈ F', E i l * Q' l j)
    {i j : U} (hi : i ∈ F') (hj : j ∈ F') : Q' i j ≤ Q i j := by
  by_contra hlt'
  have hlt : Q i j < Q' i j := lt_of_not_ge hlt'
  set δ := Q' i j - Q i j with hδ
  have hδ0 : 0 < δ := by linarith
  set C := vnorm F (fun i => Q i j) with hC
  set C' := vnorm F' (fun i => Q' i j) with hC'
  have hC0 : 0 ≤ C := vnorm_nonneg _ _
  have hC'0 : 0 ≤ C' := vnorm_nonneg _ _
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / (C + C' + 1) by positivity) he1
  have hE' : OpBound F' F' E e := hE.subset hF hF
  have h1 := dist_le F E Q he0 hE hQ (hF hj) n
  have h2 := dist_le F' E Q' he0 hE' hQ' hj n
  have h3 : |Q i j - neumannPartial F E n i j| ≤ e ^ n * C :=
    (abs_le_vnorm (v := fun i => Q i j - neumannPartial F E n i j) (hF hi)).trans h1
  have h4 : |Q' i j - neumannPartial F' E n i j| ≤ e ^ n * C' :=
    (abs_le_vnorm (v := fun i => Q' i j - neumannPartial F' E n i j) hi).trans h2
  have h5 := neumannPartial_mono hF hE0 n i j
  have hen : 0 ≤ e ^ n := pow_nonneg he0 n
  have h6 : e ^ n * (C + C' + 1) < δ := by
    rwa [lt_div_iff₀ (by positivity)] at hn
  have h7 := (abs_le.mp h3).1
  have h8 := (abs_le.mp h4).2
  nlinarith

end Sarkozy.Influence

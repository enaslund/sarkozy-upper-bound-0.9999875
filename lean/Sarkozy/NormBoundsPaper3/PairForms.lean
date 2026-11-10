module

public import Sarkozy.NormBoundsPaper3.ELaw

@[expose] public section

/-!
# The kernel of `K₁` on ordered pairs and its character forms (NB3)

`paper/sections/21_middle_records.tex`, proof of `lem:record:e-law`(a),(c): "For `a ≠ b`,
`1 + χ(b − a)` is `2` if `a → b` and `0` otherwise, and for `a = b` the factor `1 + 0 − 1`
vanishes"; "Expanding the product and using that transposition maps `𝖢, 𝖣` to `−𝖣, −𝖢` and
exchanges `δ_𝖢, δ_𝖣`, … `z₁ Skew K₁ = 𝖢 + 𝖣 − δ_𝖢 𝖣 − δ_𝖣 𝖢`"; "`‖𝖢 + 𝖣‖ = r/(1 − q)`,
`‖δ_𝖢 𝖣‖, ‖δ_𝖣 𝖢‖ ≤ qr/(1 − q)`".

The density of `K₁` depends on the halves only through the pairs `(x₀, x₁)`, `(y₀, y₁)`:
`g2 a b = [a₁ → b₀][a₀ → b₁]`. With `𝖢 = χ(b₀ − a₁)` (`chC`), `𝖣 = χ(b₁ − a₀)` (`chH`),
`δ_𝖢 = [b₀ = a₁]`, `δ_𝖣 = [b₁ = a₀]` (`z0`):

* `sq1_eq`: `[χ(d) = 1] = (1 + χ(d) − [d = 0])/2`;
* **`g2_skew`**: `g2 a b − g2 b a = (𝖢 + 𝖣 − 𝖢 δ_𝖣 − 𝖣 δ_𝖢)/2`;
  **`g2_sym`**: `g2 a b + g2 b a = (1 − δ_𝖢 − δ_𝖣 + δ_𝖢 δ_𝖣 + 𝖢 𝖣)/2`;
* the forms on `ℓ²(𝔽_p²)`, for `U, V` vanishing on the diagonal with sum zero where stated:
  **`bCD`** (`𝖢 + 𝖣`, `p√p`), `bCz`, `bDz` (`𝖢 δ_𝖣`, `𝖣 δ_𝖢`, `√p`), `bzC`, `bzD` (`δ_𝖢`, `δ_𝖣`,
  `p`), `bzz` (`δ_𝖢 δ_𝖣`, `1`), `bCC` (`𝖢 𝖣`, `p`, NB2's `two_chi_le`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.NormBoundsPaper2 (off OffDiag rowS colS rows_cols_le chi_form_le two_chi_le two_dot_le
  chC chH main_lin1 main_lin2 abs_sum_mul_le)
open Sarkozy.JointRows.PaleyGauss (chiR chiR_neg chiR_zero)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

/-- `[d = 0]`. -/
noncomputable def z0 (d : ZMod p) : ℝ := if d = 0 then 1 else 0

theorem sq1_eq (d : ZMod p) : sq1 d = (1 + chiR p d - z0 d) / 2 := by
  unfold sq1 z0 chiR
  by_cases hd : d = 0
  · simp [hd]
  · rcases quadraticChar_dichotomy hd with h | h <;> simp [h, hd]

theorem sq1_neg (h3 : p % 4 = 3) (d : ZMod p) : sq1 (-d) = (1 - chiR p d - z0 d) / 2 := by
  rw [sq1_eq, chiR_neg h3]
  have : z0 (-d) = z0 d := by unfold z0; simp [neg_eq_zero]
  rw [this]
  ring

/-- The pair kernel of `K₁`: `[a₁ → b₀][a₀ → b₁]`. -/
noncomputable def g2 (a b : ZMod p × ZMod p) : ℝ := sq1 (b.1 - a.2) * sq1 (b.2 - a.1)

/-- **The skew part of the pair kernel** (`lem:record:e-law`(c)). -/
theorem g2_skew (h3 : p % 4 = 3) (a b : ZMod p × ZMod p) :
    g2 a b - g2 b a = (chC a b + chH a b - chC a b * z0 (b.2 - a.1) -
      chH a b * z0 (b.1 - a.2)) / 2 := by
  unfold g2 chC chH
  rw [show a.1 - b.2 = -(b.2 - a.1) by ring, show a.2 - b.1 = -(b.1 - a.2) by ring,
    sq1_neg h3, sq1_neg h3, sq1_eq, sq1_eq]
  ring

/-- **The symmetric part of the pair kernel.** -/
theorem g2_sym (h3 : p % 4 = 3) (a b : ZMod p × ZMod p) :
    g2 a b + g2 b a = (1 - z0 (b.1 - a.2) - z0 (b.2 - a.1) + z0 (b.1 - a.2) * z0 (b.2 - a.1) +
      chC a b * chH a b) / 2 := by
  unfold g2 chC chH
  rw [show a.1 - b.2 = -(b.2 - a.1) by ring, show a.2 - b.1 = -(b.1 - a.2) by ring,
    sq1_neg h3, sq1_neg h3, sq1_eq, sq1_eq]
  ring

/-! ## The character forms on ordered pairs -/

/-- The square norm `∑ U²` on pairs. -/
noncomputable def n2 (U : ZMod p × ZMod p → ℝ) : ℝ := ∑ x, U x ^ 2

theorem n2_nonneg (U : ZMod p × ZMod p → ℝ) : 0 ≤ n2 U := sum_nonneg fun _ _ => sq_nonneg _

theorem sum_z0 (f : ZMod p → ℝ) (a : ZMod p) : ∑ c, f c * z0 (c - a) = f a := by
  unfold z0
  rw [sum_eq_single a]
  · simp
  · intro c _ hc
    simp [sub_eq_zero, hc]
  · exact fun h => absurd (mem_univ _) h

/-- **`𝖢 + 𝖣`** on mean-zero pair functions vanishing on the diagonal: `p√p`
(the paper's `‖𝖢 + 𝖣‖ = r/(1 − q)` in unnormalized form; NB2's `rows_cols_le`). -/
theorem bCD (h3 : p % 4 = 3) {U V : ZMod p × ZMod p → ℝ} (hU : OffDiag U) (hV : OffDiag V)
    (hU0 : ∑ x, U x = 0) (hV0 : ∑ x, V x = 0) :
    |∑ a, ∑ b, U a * V b * (chC a b + chH a b)| ≤
      (p : ℝ) * Real.sqrt p * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hlin : ∑ a, ∑ b, U a * V b * (chC a b + chH a b) =
      ∑ b, colS U b * ∑ c, chiR p (c - b) * rowS V c +
        ∑ a, rowS U a * ∑ d, chiR p (d - a) * colS V d := by
    rw [← main_lin1, ← main_lin2, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun y _ => by ring
  have hRg := rows_cols_le hU hU0
  have hRh := rows_cols_le hV hV0
  set Rg := ∑ a, rowS U a ^ 2
  set Cg := ∑ b, colS U b ^ 2
  set Rh := ∑ a, rowS V a ^ 2
  set Ch := ∑ b, colS V b ^ 2
  have hRg0 : 0 ≤ Rg := sum_nonneg fun a _ => sq_nonneg _
  have hCg0 : 0 ≤ Cg := sum_nonneg fun a _ => sq_nonneg _
  have hRh0 : 0 ≤ Rh := sum_nonneg fun a _ => sq_nonneg _
  have hCh0 : 0 ≤ Ch := sum_nonneg fun a _ => sq_nonneg _
  have hL1 := chi_form_le h3 (colS U) (rowS V)
  have hL2 := chi_form_le h3 (rowS U) (colS V)
  rw [hlin]
  have hd := two_dot_le hCg0 hRg0 hRh0 hCh0
  have hA : Real.sqrt (Cg + Rg) ≤ Real.sqrt p * Real.sqrt (n2 U) := by
    rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt (by unfold n2; linarith)
  have hB : Real.sqrt (Rh + Ch) ≤ Real.sqrt p * Real.sqrt (n2 V) := by
    rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt (by unfold n2; linarith)
  have hsq : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hnU := Real.sqrt_nonneg (n2 U)
  have hnV := Real.sqrt_nonneg (n2 V)
  calc |∑ b, colS U b * ∑ c, chiR p (c - b) * rowS V c +
        ∑ a, rowS U a * ∑ d, chiR p (d - a) * colS V d|
      ≤ Real.sqrt p * Real.sqrt Cg * Real.sqrt Rh + Real.sqrt p * Real.sqrt Rg * Real.sqrt Ch :=
        (abs_add_le _ _).trans (add_le_add hL1 hL2)
    _ = Real.sqrt p * (Real.sqrt Cg * Real.sqrt Rh + Real.sqrt Rg * Real.sqrt Ch) := by ring
    _ ≤ Real.sqrt p * (Real.sqrt (Cg + Rg) * Real.sqrt (Rh + Ch)) :=
        mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)
    _ ≤ Real.sqrt p * ((Real.sqrt p * Real.sqrt (n2 U)) * (Real.sqrt p * Real.sqrt (n2 V))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hA hB (Real.sqrt_nonneg _) (by positivity))
          (Real.sqrt_nonneg _)
    _ = (Real.sqrt p * Real.sqrt p) * Real.sqrt p * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by ring
    _ = _ := by rw [hsq]

/-- Row-by-row character forms: `|∑_w ∑_a G_w(a) ∑_c χ(c − a) H_w(c)| ≤ √p ‖G‖ ‖H‖`. -/
theorem rowwise_le (h3 : p % 4 = 3) (G H : ZMod p → ZMod p → ℝ) :
    |∑ w, ∑ a, G w a * ∑ c, chiR p (c - a) * H w c| ≤
      Real.sqrt p * Real.sqrt (∑ w, ∑ a, G w a ^ 2) * Real.sqrt (∑ w, ∑ c, H w c ^ 2) := by
  have h1 : |∑ w, ∑ a, G w a * ∑ c, chiR p (c - a) * H w c| ≤
      ∑ w, Real.sqrt p * (Real.sqrt (∑ a, G w a ^ 2) * Real.sqrt (∑ c, H w c ^ 2)) :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun w _ =>
      (chi_form_le h3 (G w) (H w)).trans (le_of_eq (by ring)))
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ (fun w => Real.sqrt (∑ a, G w a ^ 2))
    (fun w => Real.sqrt (∑ c, H w c ^ 2))
  have e1 : ∑ w, Real.sqrt (∑ a, G w a ^ 2) ^ 2 = ∑ w, ∑ a, G w a ^ 2 :=
    sum_congr rfl fun w _ => Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  have e2 : ∑ w, Real.sqrt (∑ c, H w c ^ 2) ^ 2 = ∑ w, ∑ c, H w c ^ 2 :=
    sum_congr rfl fun w _ => Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)
  rw [e1, e2] at hcs
  rw [← mul_sum] at h1
  calc _ ≤ _ := h1
    _ ≤ Real.sqrt p * (Real.sqrt (∑ w, ∑ a, G w a ^ 2) * Real.sqrt (∑ w, ∑ c, H w c ^ 2)) :=
        mul_le_mul_of_nonneg_left hcs (Real.sqrt_nonneg _)
    _ = _ := by ring

theorem n2_eq (U : ZMod p × ZMod p → ℝ) : n2 U = ∑ w, ∑ a, U (w, a) ^ 2 := by
  unfold n2; rw [Fintype.sum_prod_type]

theorem n2_eq' (U : ZMod p × ZMod p → ℝ) : n2 U = ∑ w, ∑ a, U (a, w) ^ 2 := by
  unfold n2; rw [Fintype.sum_prod_type, sum_comm]

/-- **`𝖢 δ_𝖣`**: `√p` (the paper's `‖δ_𝖣 𝖢‖ ≤ qr/(1 − q)`). -/
theorem bCz (h3 : p % 4 = 3) (U V : ZMod p × ZMod p → ℝ) :
    |∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1))| ≤
      Real.sqrt p * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by
  have e : ∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1)) =
      ∑ w, ∑ a, U (w, a) * ∑ c, chiR p (c - a) * V (c, w) := by
    have h1 : ∀ a : ZMod p × ZMod p, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1)) =
        U a * ∑ c, chiR p (c - a.2) * V (c, a.1) := by
      intro a
      rw [Fintype.sum_prod_type, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      have := sum_z0 (fun d => U a * (chiR p (c - a.2) * V (c, d))) a.1
      exact (sum_congr rfl fun d _ => by dsimp only [chC]; ring).trans this
    rw [sum_congr rfl fun a _ => h1 a, Fintype.sum_prod_type]
  rw [e, n2_eq U, n2_eq' V]
  exact rowwise_le h3 (fun w a => U (w, a)) (fun w c => V (c, w))

/-- **`𝖣 δ_𝖢`**: `√p`. -/
theorem bDz (h3 : p % 4 = 3) (U V : ZMod p × ZMod p → ℝ) :
    |∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2))| ≤
      Real.sqrt p * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by
  have e : ∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2)) =
      ∑ w, ∑ a, U (a, w) * ∑ c, chiR p (c - a) * V (w, c) := by
    have h1 : ∀ a : ZMod p × ZMod p, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2)) =
        U a * ∑ c, chiR p (c - a.1) * V (a.2, c) := by
      intro a
      rw [Fintype.sum_prod_type, sum_comm, mul_sum]
      refine sum_congr rfl fun c _ => ?_
      have := sum_z0 (fun d => U a * (chiR p (c - a.1) * V (d, c))) a.2
      exact (sum_congr rfl fun d _ => by dsimp only [chH]; ring).trans this
    rw [sum_congr rfl fun a _ => h1 a, Fintype.sum_prod_type, sum_comm]
  rw [e, n2_eq' U, n2_eq V]
  exact rowwise_le h3 (fun w a => U (a, w)) (fun w c => V (w, c))

/-- **`δ_𝖢`**: `p` on mean-zero functions vanishing on the diagonal. -/
theorem bzC {U V : ZMod p × ZMod p → ℝ} (hU : OffDiag U) (hV : OffDiag V)
    (hU0 : ∑ x, U x = 0) (hV0 : ∑ x, V x = 0) :
    |∑ a, ∑ b, U a * V b * z0 (b.1 - a.2)| ≤ (p : ℝ) * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have e : ∑ a, ∑ b, U a * V b * z0 (b.1 - a.2) = ∑ w, colS U w * rowS V w := by
    have h1 : ∀ a : ZMod p × ZMod p, ∑ b, U a * V b * z0 (b.1 - a.2) = U a * rowS V a.2 := by
      intro a
      rw [Fintype.sum_prod_type]
      have := sum_z0 (fun c => U a * rowS V c) a.2
      refine (sum_congr rfl fun c _ => ?_).trans this
      unfold rowS
      rw [mul_sum, sum_mul]
    rw [sum_congr rfl fun a _ => h1 a, Fintype.sum_prod_type, sum_comm]
    unfold colS
    exact sum_congr rfl fun w _ => by rw [sum_mul]
  rw [e]
  have h1 := abs_sum_mul_le univ (colS U) (rowS V)
  have hRg := rows_cols_le hU hU0
  have hRh := rows_cols_le hV hV0
  have hA : Real.sqrt (∑ w, colS U w ^ 2) ≤ Real.sqrt p * Real.sqrt (n2 U) := by
    rw [← Real.sqrt_mul hp0.le]
    have : 0 ≤ ∑ a, rowS U a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    exact Real.sqrt_le_sqrt (by unfold n2; linarith)
  have hB : Real.sqrt (∑ w, rowS V w ^ 2) ≤ Real.sqrt p * Real.sqrt (n2 V) := by
    rw [← Real.sqrt_mul hp0.le]
    have : 0 ≤ ∑ a, colS V a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    exact Real.sqrt_le_sqrt (by unfold n2; linarith)
  have hsq : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  calc _ ≤ _ := h1
    _ ≤ (Real.sqrt p * Real.sqrt (n2 U)) * (Real.sqrt p * Real.sqrt (n2 V)) :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt p * Real.sqrt p) * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by ring
    _ = _ := by rw [hsq]

/-- **`δ_𝖣`**: `p` on mean-zero functions vanishing on the diagonal. -/
theorem bzD {U V : ZMod p × ZMod p → ℝ} (hU : OffDiag U) (hV : OffDiag V)
    (hU0 : ∑ x, U x = 0) (hV0 : ∑ x, V x = 0) :
    |∑ a, ∑ b, U a * V b * z0 (b.2 - a.1)| ≤ (p : ℝ) * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have e : ∑ a, ∑ b, U a * V b * z0 (b.2 - a.1) = ∑ w, rowS U w * colS V w := by
    have h1 : ∀ a : ZMod p × ZMod p, ∑ b, U a * V b * z0 (b.2 - a.1) = U a * colS V a.1 := by
      intro a
      rw [Fintype.sum_prod_type, sum_comm]
      have := sum_z0 (fun c => U a * colS V c) a.1
      refine (sum_congr rfl fun c _ => ?_).trans this
      unfold colS
      rw [mul_sum, sum_mul]
    rw [sum_congr rfl fun a _ => h1 a, Fintype.sum_prod_type]
    unfold rowS
    exact sum_congr rfl fun w _ => by rw [sum_mul]
  rw [e]
  have h1 := abs_sum_mul_le univ (rowS U) (colS V)
  have hRg := rows_cols_le hU hU0
  have hRh := rows_cols_le hV hV0
  have hA : Real.sqrt (∑ w, rowS U w ^ 2) ≤ Real.sqrt p * Real.sqrt (n2 U) := by
    rw [← Real.sqrt_mul hp0.le]
    have : 0 ≤ ∑ a, colS U a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    exact Real.sqrt_le_sqrt (by unfold n2; linarith)
  have hB : Real.sqrt (∑ w, colS V w ^ 2) ≤ Real.sqrt p * Real.sqrt (n2 V) := by
    rw [← Real.sqrt_mul hp0.le]
    have : 0 ≤ ∑ a, rowS V a ^ 2 := sum_nonneg fun a _ => sq_nonneg _
    exact Real.sqrt_le_sqrt (by unfold n2; linarith)
  have hsq : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  calc _ ≤ _ := h1
    _ ≤ (Real.sqrt p * Real.sqrt (n2 U)) * (Real.sqrt p * Real.sqrt (n2 V)) :=
        mul_le_mul hA hB (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt p * Real.sqrt p) * Real.sqrt (n2 U) * Real.sqrt (n2 V) := by ring
    _ = _ := by rw [hsq]

/-- **`δ_𝖢 δ_𝖣`**: `1`. -/
theorem bzz (U V : ZMod p × ZMod p → ℝ) :
    |∑ a, ∑ b, U a * V b * (z0 (b.1 - a.2) * z0 (b.2 - a.1))| ≤
      Real.sqrt (n2 U) * Real.sqrt (n2 V) := by
  have e : ∑ a, ∑ b, U a * V b * (z0 (b.1 - a.2) * z0 (b.2 - a.1)) =
      ∑ a, U a * V (a.2, a.1) := by
    refine sum_congr rfl fun a _ => ?_
    rw [Fintype.sum_prod_type]
    have i1 : ∀ c, ∑ d, U a * V (c, d) * (z0 ((c, d).1 - a.2) * z0 ((c, d).2 - a.1)) =
        U a * V (c, a.1) * z0 (c - a.2) := by
      intro c
      have := sum_z0 (fun d => U a * V (c, d) * z0 (c - a.2)) a.1
      exact (sum_congr rfl fun d _ => by dsimp only; ring).trans this
    rw [sum_congr rfl fun c _ => i1 c]
    exact sum_z0 (fun c => U a * V (c, a.1)) a.2
  rw [e]
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt univ (fun a => |U a|) (fun a => |V (a.2, a.1)|)
  have hsw : ∑ a : ZMod p × ZMod p, |V (a.2, a.1)| ^ 2 = n2 V := by
    unfold n2
    simp only [sq_abs]
    exact Fintype.sum_equiv (Equiv.prodComm _ _) _ _ (fun a => rfl)
  simp only [sq_abs] at h1
  rw [show ∑ a : ZMod p × ZMod p, V (a.2, a.1) ^ 2 = n2 V by
    rw [← hsw]; simp only [sq_abs]] at h1
  calc |∑ a, U a * V (a.2, a.1)| ≤ ∑ a, |U a| * |V (a.2, a.1)| :=
        (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun a _ => abs_mul _ _))
    _ ≤ _ := h1

/-- **`𝖢 𝖣`**: `p` (NB2's `two_chi_le`). -/
theorem bCC (h3 : p % 4 = 3) (U V : ZMod p × ZMod p → ℝ) :
    |∑ a, ∑ b, U a * V b * (chC a b * chH a b)| ≤
      (p : ℝ) * Real.sqrt (n2 U) * Real.sqrt (n2 V) :=
  two_chi_le h3 U V

end Sarkozy.NormBoundsPaper3

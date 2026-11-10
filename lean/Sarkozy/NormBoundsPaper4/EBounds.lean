module

public import Sarkozy.NormBoundsPaper4.EDecomp

@[expose] public section

/-!
# The pieces of `Sym(K₁ − K^E_0)`: the star part `𝒮` and the two-edge kernels (FD)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(d): "The matrix `J₃ − E₁₀ − E₀₁` has
the characteristic polynomial `λ³ − 3λ² + λ + 1`, with roots `1` and `1 ± √2`, and
`‖E₁₀ + E₀₁‖ = 1`; with `‖V‖² = 1/(1 − q)` … `‖𝒮‖ ≤ 𝔰_p`. The kernel `𝖢𝖣` is a two-edge matching
on the pairs …, of norm `q` for independent labels, and `δ_𝖢δ_𝖣` is `qI ⊗ qI` there".

* `q3`, **`q3_le`**: `|∑_{ij} a_i b_j − a₁b₀ − a₀b₁| ≤ (1 + √2)|a||b|` on `ℝ³` (the two
  sums of squares `(√2 x₀ − x₂)² + (√2 x₁ − x₂)²` and `(x₀ + x₂)² + (x₁ + x₂)² + √2|x|²`);
  `q2_le`: `|a₁b₀ + a₀b₁| ≤ |a||b|`;
* **`Sraw_le`**: `|Sraw − Sc| ≤ (1 + √2)√Tu√Tv`, `Sc_le`: `|Sc| ≤ √Tu√Tv`;
* `red_norm`: `√n2(ū) ≤ √((p − 2) Nq u)` (NB3's Jensen `red_sq`);
* **`CHf_le`**: `|CHf| ≤ p(p − 2)√Nq u √Nq v` (NB3's `bCC`); **`ZZf_le`**: `(p − 2)` (`bzz`);
* `CHf_comm` (`𝖢𝖣` is symmetric), `CHf_sub_left`, `CHf_sub_right` (bilinearity).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.NormBoundsPaper2 (off chC chH abs_le_of_scaled)
open Sarkozy.JointRows.PaleyGauss (chiR chiR_neg)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

local notation "T3" => (ZMod p × ZMod p) × ZMod p

/-! ## The `3 × 3` matrix -/

/-- `∑_{ij} a_i b_j − a₁ b₀ − a₀ b₁`. -/
def q3 (a b : Fin 3 → ℝ) : ℝ := (∑ i, a i) * (∑ j, b j) - a 1 * b 0 - a 0 * b 1

/-- **`‖J₃ − E₁₀ − E₀₁‖ = 1 + √2`** as a form bound on `ℝ³`. -/
theorem q3_le (a b : Fin 3 → ℝ) :
    |q3 a b| ≤ (1 + Real.sqrt 2) * Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  set s := Real.sqrt 2 with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr (by norm_num)
  have hs2 : s * s = 2 := Real.mul_self_sqrt (by norm_num)
  refine abs_le_of_scaled (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (by positivity) fun t ht => ?_
  rw [Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _),
    Real.sq_sqrt (sum_nonneg fun i _ => sq_nonneg _)]
  simp only [Fin.sum_univ_three, q3] at *
  set a0 := a 0
  set a1 := a 1
  set a2 := a 2
  set b0 := b 0
  set b1 := b 1
  set b2 := b 2
  -- the quadratic form `Q(x) = |x|² + 2x₀x₂ + 2x₁x₂`
  have psd1 : ∀ x0 x1 x2 : ℝ, x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + 2 * x0 * x2 + 2 * x1 * x2 ≤
      (1 + s) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := fun x0 x1 x2 => by
    have h : 0 ≤ (s * x0 - x2) ^ 2 + (s * x1 - x2) ^ 2 := by positivity
    have e : (s * x0 - x2) ^ 2 + (s * x1 - x2) ^ 2 =
        s * (s * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) - 2 * x0 * x2 - 2 * x1 * x2) := by
      ring_nf; rw [show s ^ 2 = 2 by rw [sq]; exact hs2]; ring
    rw [e] at h
    have := (mul_nonneg_iff_of_pos_left hs0).mp h
    linarith
  have psd2 : ∀ x0 x1 x2 : ℝ, -(x0 ^ 2 + x1 ^ 2 + x2 ^ 2 + 2 * x0 * x2 + 2 * x1 * x2) ≤
      (1 + s) * (x0 ^ 2 + x1 ^ 2 + x2 ^ 2) := fun x0 x1 x2 => by
    nlinarith [sq_nonneg (x0 + x2), sq_nonneg (x1 + x2), sq_nonneg x0, sq_nonneg x1,
      sq_nonneg x2, mul_nonneg hs0.le (sq_nonneg x0), mul_nonneg hs0.le (sq_nonneg x1),
      mul_nonneg hs0.le (sq_nonneg x2)]
  have hq : (a0 + a1 + a2) * (b0 + b1 + b2) - a1 * b0 - a0 * b1 =
      ((t * a0 + b0) ^ 2 + (t * a1 + b1) ^ 2 + (t * a2 + b2) ^ 2 +
        2 * (t * a0 + b0) * (t * a2 + b2) + 2 * (t * a1 + b1) * (t * a2 + b2) -
        ((t * a0 - b0) ^ 2 + (t * a1 - b1) ^ 2 + (t * a2 - b2) ^ 2 +
        2 * (t * a0 - b0) * (t * a2 - b2) + 2 * (t * a1 - b1) * (t * a2 - b2))) / (4 * t) := by
    field_simp
    ring
  have hN : (1 + s) / 2 * (t * (a0 ^ 2 + a1 ^ 2 + a2 ^ 2) + (b0 ^ 2 + b1 ^ 2 + b2 ^ 2) / t) =
      ((1 + s) * ((t * a0 + b0) ^ 2 + (t * a1 + b1) ^ 2 + (t * a2 + b2) ^ 2) +
        (1 + s) * ((t * a0 - b0) ^ 2 + (t * a1 - b1) ^ 2 + (t * a2 - b2) ^ 2)) / (4 * t) := by
    field_simp
    ring
  rw [hq, hN, abs_le]
  have h4 : 0 < 4 * t := by positivity
  constructor
  · rw [neg_div', div_le_div_iff_of_pos_right h4]
    have := psd2 (t * a0 + b0) (t * a1 + b1) (t * a2 + b2)
    have := psd1 (t * a0 - b0) (t * a1 - b1) (t * a2 - b2)
    linarith
  · rw [div_le_div_iff_of_pos_right h4]
    have := psd1 (t * a0 + b0) (t * a1 + b1) (t * a2 + b2)
    have := psd2 (t * a0 - b0) (t * a1 - b1) (t * a2 - b2)
    linarith

theorem q2_le (a b : Fin 3 → ℝ) :
    |a 1 * b 0 + a 0 * b 1| ≤ Real.sqrt (∑ i, a i ^ 2) * Real.sqrt (∑ i, b i ^ 2) := by
  rw [← Real.sqrt_mul (sum_nonneg fun i _ => sq_nonneg _), ← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  simp only [Fin.sum_univ_three]
  nlinarith [sq_nonneg (a 1 * b 1 - a 0 * b 0), sq_nonneg (a 2 * b 0), sq_nonneg (a 2 * b 1),
    sq_nonneg (a 0 * b 2), sq_nonneg (a 1 * b 2), sq_nonneg (a 2 * b 2)]

/-! ## The star part -/

theorem sum_sqrt_le (A B : ZMod p → ℝ) (hA : ∀ t, 0 ≤ A t) (hB : ∀ t, 0 ≤ B t) :
    ∑ t, Real.sqrt (A t) * Real.sqrt (B t) ≤ Real.sqrt (∑ t, A t) * Real.sqrt (∑ t, B t) := by
  have h := Real.sum_mul_le_sqrt_mul_sqrt univ (fun t => Real.sqrt (A t)) (fun t => Real.sqrt (B t))
  simp only [Real.sq_sqrt (hA _), Real.sq_sqrt (hB _)] at h
  exact h

theorem Tu_eq_sum (u : T3 → ℝ) : Tu u = ∑ t, ∑ i, Uc u i t ^ 2 := by
  unfold Tu; exact sum_comm

/-- **`|⟨U, (J₃ − E₁₀ − E₀₁) V⟩| ≤ (1 + √2)‖U‖‖V‖`.** -/
theorem Sraw_le (u v : T3 → ℝ) :
    |Sraw u v - Sc u v| ≤ (1 + Real.sqrt 2) * Real.sqrt (Tu u) * Real.sqrt (Tu v) := by
  have e : Sraw u v - Sc u v = ∑ t, q3 (fun i => Uc u i t) (fun j => Uc v j t) := by
    unfold Sraw Sc ip1 q3
    simp only [sum_mul_sum]
    rw [Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
    simp only [← sum_add_distrib, ← sum_sub_distrib]
    refine sum_congr rfl fun t _ => ?_
    simp only [Fin.sum_univ_three]
    ring
  rw [e, Tu_eq_sum, Tu_eq_sum]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ t, |q3 (fun i => Uc u i t) (fun j => Uc v j t)|
      ≤ ∑ t, (1 + Real.sqrt 2) * (Real.sqrt (∑ i, Uc u i t ^ 2) *
          Real.sqrt (∑ i, Uc v i t ^ 2)) :=
        sum_le_sum fun t _ => (q3_le _ _).trans (le_of_eq (by ring))
    _ = (1 + Real.sqrt 2) * ∑ t, Real.sqrt (∑ i, Uc u i t ^ 2) *
          Real.sqrt (∑ i, Uc v i t ^ 2) := by rw [mul_sum]
    _ ≤ (1 + Real.sqrt 2) * (Real.sqrt (∑ t, ∑ i, Uc u i t ^ 2) *
          Real.sqrt (∑ t, ∑ i, Uc v i t ^ 2)) :=
        mul_le_mul_of_nonneg_left (sum_sqrt_le _ _ (fun t => sum_nonneg fun i _ => sq_nonneg _)
          (fun t => sum_nonneg fun i _ => sq_nonneg _)) (by positivity)
    _ = _ := by ring

theorem Sc_le (u v : T3 → ℝ) : |Sc u v| ≤ Real.sqrt (Tu u) * Real.sqrt (Tu v) := by
  have e : Sc u v = ∑ t, (Uc u 1 t * Uc v 0 t + Uc u 0 t * Uc v 1 t) := by
    unfold Sc ip1
    exact sum_add_distrib.symm
  rw [e, Tu_eq_sum, Tu_eq_sum]
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun t _ =>
    q2_le (fun i => Uc u i t) (fun j => Uc v j t)).trans ?_)
  exact sum_sqrt_le _ _ (fun t => sum_nonneg fun i _ => sq_nonneg _)
    (fun t => sum_nonneg fun i _ => sq_nonneg _)

/-! ## The two-edge kernels -/

theorem red_norm (hp : 3 ≤ p) (u : T3 → ℝ) :
    Real.sqrt (n2 (red u)) ≤ Real.sqrt (((p : ℝ) - 2) * Nq u) :=
  Real.sqrt_le_sqrt (red_sq hp u)

/-- **`‖𝖢𝖣‖`**: `|CHf u v| ≤ p(p − 2)√Nq u √Nq v`. -/
theorem CHf_le (hp : 3 ≤ p) (h3 : p % 4 = 3) (u v : T3 → ℝ) :
    |CHf u v| ≤ (p : ℝ) * ((p : ℝ) - 2) * Real.sqrt (Nq u) * Real.sqrt (Nq v) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  have h := bCC h3 (red u) (red v)
  have e : Real.sqrt (((p : ℝ) - 2) * Nq u) = Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq u) :=
    Real.sqrt_mul h2 _
  have e' : Real.sqrt (((p : ℝ) - 2) * Nq v) = Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq v) :=
    Real.sqrt_mul h2 _
  have hss : Real.sqrt ((p : ℝ) - 2) * Real.sqrt ((p : ℝ) - 2) = (p : ℝ) - 2 :=
    Real.mul_self_sqrt h2
  calc |CHf u v| ≤ (p : ℝ) * Real.sqrt (n2 (red u)) * Real.sqrt (n2 (red v)) := h
    _ ≤ (p : ℝ) * Real.sqrt (((p : ℝ) - 2) * Nq u) * Real.sqrt (((p : ℝ) - 2) * Nq v) := by
        gcongr
        · exact red_sq hp u
        · exact red_sq hp v
    _ = _ := by
        rw [e, e', show (p : ℝ) * (Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq u)) *
          (Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq v)) = (p : ℝ) * (Real.sqrt ((p : ℝ) - 2) *
          Real.sqrt ((p : ℝ) - 2)) * Real.sqrt (Nq u) * Real.sqrt (Nq v) by ring, hss]

/-- **`‖δ_𝖢δ_𝖣‖`**: `|ZZf u v| ≤ (p − 2)√Nq u √Nq v`. -/
theorem ZZf_le (hp : 3 ≤ p) (u v : T3 → ℝ) :
    |ZZf u v| ≤ ((p : ℝ) - 2) * Real.sqrt (Nq u) * Real.sqrt (Nq v) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  have h := bzz (red u) (red v)
  have e : Real.sqrt (((p : ℝ) - 2) * Nq u) = Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq u) :=
    Real.sqrt_mul h2 _
  have e' : Real.sqrt (((p : ℝ) - 2) * Nq v) = Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq v) :=
    Real.sqrt_mul h2 _
  have hss : Real.sqrt ((p : ℝ) - 2) * Real.sqrt ((p : ℝ) - 2) = (p : ℝ) - 2 :=
    Real.mul_self_sqrt h2
  calc |ZZf u v| ≤ Real.sqrt (n2 (red u)) * Real.sqrt (n2 (red v)) := h
    _ ≤ Real.sqrt (((p : ℝ) - 2) * Nq u) * Real.sqrt (((p : ℝ) - 2) * Nq v) := by
        gcongr
        · exact red_sq hp u
        · exact red_sq hp v
    _ = _ := by
        rw [e, e', show Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq u) *
          (Real.sqrt ((p : ℝ) - 2) * Real.sqrt (Nq v)) = (Real.sqrt ((p : ℝ) - 2) *
          Real.sqrt ((p : ℝ) - 2)) * Real.sqrt (Nq u) * Real.sqrt (Nq v) by ring, hss]

/-- `𝖢𝖣` is symmetric. -/
theorem CHf_comm (h3 : p % 4 = 3) (u v : T3 → ℝ) : CHf u v = CHf v u := by
  unfold CHf
  rw [sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  unfold chC chH
  rw [show a.1 - b.2 = -(b.2 - a.1) by ring, show a.2 - b.1 = -(b.1 - a.2) by ring,
    chiR_neg h3, chiR_neg h3]
  ring

theorem red_sub (u u' : T3 → ℝ) : red (u - u') = red u - red u' := by
  funext a
  unfold red
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem CHf_sub_left (u u' v : T3 → ℝ) : CHf (u - u') v = CHf u v - CHf u' v := by
  unfold CHf
  rw [red_sub]
  simp only [Pi.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

theorem CHf_sub_right (u v v' : T3 → ℝ) : CHf u (v - v') = CHf u v - CHf u v' := by
  unfold CHf
  rw [red_sub]
  simp only [Pi.sub_apply, ← sum_sub_distrib]
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring

end Sarkozy.NormBoundsPaper4

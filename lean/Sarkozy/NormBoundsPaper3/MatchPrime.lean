module

public import Sarkozy.NormBoundsPaper3.PairForms

@[expose] public section

/-!
# The prime bounds of the matching replacement (`lem:record:e-law`(c); NB3)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(c): "`Skew(K₁ − K^E_0) = (𝖢 + 𝖣 −
δ_𝖢𝖣 − δ_𝖣𝖢)/z₁`, `‖𝖢 + 𝖣‖ = r/(1 − q)`, `‖δ_𝖢𝖣‖, ‖δ_𝖣𝖢‖ ≤ qr/(1 − q)`, so that
`‖Skew(K₁ − K^E_0)‖ ≤ a^E_p := r(1 + 2q)/((1 − q)(1 − 2q))`"; and `lem:record:exact-marginal-e`(i):
"the centred operator of `K₁` [has] norm at most `κ^E_p`".

On `L²(ν_E)`, `ν_E = m3 p` uniform on the injective triples:

* `red u (a) = ∑_c [(a, c) injective] u(a, c)`: the conditional sum over the third label;
  **`form_red`**: `⟨u, P3 v⟩ = |eSet|⁻¹ ∑_{a,b} red u (a) g2(a, b) red v (b)` (the density of `K₁`
  depends on the halves only through `(x₀, x₁)`, `(y₀, y₁)`); `red_offDiag`, `red_sum`,
  **`red_sq`** (Jensen: `∑ (red u)² ≤ (p − 2) ∑ [inj] u²`);
* **`P3_skew`**: on mean-zero `u, v`, the skew part of `K₁` has form norm at most
  `aEp p = √p (p + 2)/(p² − 3p + 4)`, which is below the paper's
  `a^E_p = √p (p + 2)/((p − 1)(p − 2))` (`Sanity.aEp_le_paper`). Since the old record is symmetric
  at the
  cut, this is the paper's bound on `Skew(K₁ − K^E_0)`;
* **`P3_form`**: on mean-zero `u, v`, `|⟨u, P3 v⟩| ≤ rhoE p ‖u‖ ‖v‖`,
  `rhoE p = (p√p + 3p + 2√p + 1)/(p² − 3p + 4) ≤ 4 p^{-1/2}` (`rhoE_le`); the centred norm
  **`P3_centred`** (a crude form of the paper's `κ^E_p`, enough for the sectors of two or more
  primes).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper2 (off OffDiag chC chH chg1 centredNorm_of_form)
open Sarkozy.SignedGram (CentredNorm)

variable {p : ℕ} [Fact p.Prime]

/-- The conditional sum over the third label. -/
noncomputable def red (u : (ZMod p × ZMod p) × ZMod p → ℝ) (a : ZMod p × ZMod p) : ℝ :=
  ∑ c, ind3 (a, c) * u (a, c)

/-- **The form of `K₁` through the pairs.** -/
theorem form_red (hE : (eSet (F := ZMod p)).Nonempty) (u v : (ZMod p × ZMod p) × ZMod p → ℝ) :
    u ⬝ᵥ (P3 hE *ᵥ v) = (1 / Nk (p := p)) * ∑ a, ∑ b, red u a * g2 a b * red v b := by
  have hR : (1 / Nk (p := p)) * ∑ a, ∑ b, red u a * g2 a b * red v b =
      ∑ a, ∑ c, ∑ b, ∑ d, (1 / Nk (p := p)) * (ind3 (a, c) * u (a, c)) * g2 a b *
        (ind3 (b, d) * v (b, d)) := by
    rw [mul_sum]
    refine sum_congr rfl fun a _ => ?_
    unfold red
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun b _ => ?_
    rw [sum_mul, sum_mul, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [mul_sum, mul_sum]
    exact sum_congr rfl fun d _ => by ring
  rw [hR]
  simp only [dotProduct, Matrix.mulVec, P3_eq]
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
  rw [Fintype.sum_prod_type, mul_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun d _ => ?_
  unfold good g2
  dsimp only
  ring

theorem red_offDiag (u : (ZMod p × ZMod p) × ZMod p → ℝ) : OffDiag (red u) := by
  intro a
  unfold red
  exact sum_eq_zero fun c _ => by rw [ind3_diag (a, a) c rfl, zero_mul]

theorem red_sum (u : (ZMod p × ZMod p) × ZMod p → ℝ) :
    ∑ a, red u a = ∑ x, ind3 x * u x := by
  unfold red
  exact (Fintype.sum_prod_type (f := fun x : (ZMod p × ZMod p) × ZMod p => ind3 x * u x)).symm

theorem m3_sum_eq (hp : 3 ≤ p) (u : (ZMod p × ZMod p) × ZMod p → ℝ) :
    ∑ x, ind3 x * u x = ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)) * ∑ x, m3 p x * u x := by
  unfold m3
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  field_simp

theorem red_sum_zero (hp : 3 ≤ p) {u : (ZMod p × ZMod p) × ZMod p → ℝ}
    (hu : ∑ x, m3 p x * u x = 0) : ∑ a, red u a = 0 := by
  rw [red_sum, m3_sum_eq hp, hu, mul_zero]

/-- **Jensen over the third label.** -/
theorem red_sq (hp : 3 ≤ p) (u : (ZMod p × ZMod p) × ZMod p → ℝ) :
    n2 (red u) ≤ ((p : ℝ) - 2) * ∑ x, ind3 x * u x ^ 2 := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  unfold n2
  rw [Fintype.sum_prod_type (f := fun x => ind3 x * u x ^ 2), mul_sum]
  refine sum_le_sum fun a _ => ?_
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun c => ind3 (a, c))
    (fun c => ind3 (a, c) * u (a, c))
  have e1 : ∑ c, ind3 (a, c) * (ind3 (a, c) * u (a, c)) = red u a := by
    unfold red
    exact sum_congr rfl fun c _ => by rw [← mul_assoc, ind3_mul_self]
  have e2 : ∑ c, ind3 (a, c) ^ 2 = off a * ((p : ℝ) - 2) := by
    have h := sum_ind3_fib (X := ZMod p) a
    rw [ZMod.card] at h
    rw [← h]
    exact sum_congr rfl fun c _ => by rw [sq, ind3_mul_self]
  have e3 : ∑ c, (ind3 (a, c) * u (a, c)) ^ 2 = ∑ c, ind3 (a, c) * u (a, c) ^ 2 :=
    sum_congr rfl fun c _ => by rw [mul_pow, sq (ind3 _), ind3_mul_self]
  rw [e1, e2, e3] at hcs
  have hoff : off a ≤ 1 := by unfold off; split_ifs <;> norm_num
  have hoff0 : 0 ≤ off a := by unfold off; split_ifs <;> norm_num
  have hS : 0 ≤ ∑ c, ind3 (a, c) * u (a, c) ^ 2 :=
    sum_nonneg fun c _ => mul_nonneg (ind3_nonneg _) (sq_nonneg _)
  calc red u a ^ 2 ≤ off a * ((p : ℝ) - 2) * ∑ c, ind3 (a, c) * u (a, c) ^ 2 := hcs
    _ ≤ 1 * ((p : ℝ) - 2) * ∑ c, ind3 (a, c) * u (a, c) ^ 2 := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact mul_le_mul_of_nonneg_right hoff (by linarith)
    _ = _ := by ring

theorem m3_sq_eq (hp : 3 ≤ p) (u : (ZMod p × ZMod p) × ZMod p → ℝ) :
    ∑ x, ind3 x * u x ^ 2 = ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)) * ∑ x, m3 p x * u x ^ 2 :=
  m3_sum_eq hp (fun x => u x ^ 2)

/-- The scaling of the norms: `n2 (red u) ≤ (p − 2) M ‖u‖²_{ν_E}`. -/
theorem red_sq_m3 (hp : 3 ≤ p) (u : (ZMod p × ZMod p) × ZMod p → ℝ) :
    n2 (red u) ≤ (((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) *
      ∑ x, m3 p x * u x ^ 2 := by
  have h := red_sq hp u
  rw [m3_sq_eq hp] at h
  linarith

theorem sqrt_scale {K c A B nU nV : ℝ} (hK : 0 ≤ K) (hc : 0 ≤ c)
    (hU : nU ≤ c * A) (hV : nV ≤ c * B) :
    K * Real.sqrt nU * Real.sqrt nV ≤ K * c * Real.sqrt A * Real.sqrt B := by
  have h1 : Real.sqrt nU ≤ Real.sqrt c * Real.sqrt A := by
    rw [← Real.sqrt_mul hc]; exact Real.sqrt_le_sqrt hU
  have h2 : Real.sqrt nV ≤ Real.sqrt c * Real.sqrt B := by
    rw [← Real.sqrt_mul hc]; exact Real.sqrt_le_sqrt hV
  have hcc : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc
  calc K * Real.sqrt nU * Real.sqrt nV
      ≤ K * (Real.sqrt c * Real.sqrt A) * (Real.sqrt c * Real.sqrt B) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hK) h2 (Real.sqrt_nonneg _) ?_
        exact mul_nonneg hK (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    _ = K * (Real.sqrt c * Real.sqrt c) * Real.sqrt A * Real.sqrt B := by ring
    _ = _ := by rw [hcc]

omit [Fact p.Prime] in
/-- `p² − 3p + 4 > 0`. -/
theorem den_pos (hp : 3 ≤ p) : 0 < (p : ℝ) ^ 2 - 3 * p + 4 := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  nlinarith

/-- **The prime skew constant**: `√p (p + 2)/(p² − 3p + 4)`. -/
noncomputable def aEp (p : ℕ) : ℝ := Real.sqrt p * ((p : ℝ) + 2) / ((p : ℝ) ^ 2 - 3 * p + 4)

/-- **The prime centred constant**: `(p√p + 3p + 2√p + 1)/(p² − 3p + 4)`. -/
noncomputable def rhoE (p : ℕ) : ℝ :=
  ((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) / ((p : ℝ) ^ 2 - 3 * p + 4)

/-- The normalization `|eSet|⁻¹ (p − 2) M = 4/(p² − 3p + 4)`. -/
theorem norm_const (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3) (K : ℝ) :
    1 / Nk (p := p) * ((1 / 4) * (K * (((p : ℝ) - 2) *
      ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))))) = K / ((p : ℝ) ^ 2 - 3 * p + 4) := by
  have hp2 : p ≠ 2 := by omega
  rw [eSet_card hE hp2 h3]
  have hM := M3_pos (p := p) (by omega)
  have hd := den_pos (p := p) (by omega)
  have hp' : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  unfold Rf
  set D := (p : ℝ) ^ 2 - 3 * p + 4
  have hD : D ≠ 0 := hd.ne'
  have h2' := h2.ne'
  field_simp

/-- **`lem:record:e-law`(c) at one prime**: the skew part of `K₁` on mean-zero functions of
`L²(ν_E)` has norm at most `aEp p`. -/
theorem P3_skew (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3)
    (u v : (ZMod p × ZMod p) × ZMod p → ℝ) (hu : ∑ x, m3 p x * u x = 0)
    (hv : ∑ x, m3 p x * v x = 0) :
    |chg1 (P3 hE) (P3 hE) (1 / 2) (-1 / 2) 0 u v| ≤
      aEp p * Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by
  have hp3 : 3 ≤ p := by omega
  set U := red u
  set V := red v
  have hvu : v ⬝ᵥ (P3 hE *ᵥ u) = (1 / Nk (p := p)) * ∑ a, ∑ b, U a * g2 b a * V b := by
    rw [form_red, sum_comm]
    congr 1
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hX : chg1 (P3 hE) (P3 hE) (1 / 2) (-1 / 2) 0 u v = (1 / Nk (p := p)) * ((1 / 4) *
      (∑ a, ∑ b, U a * V b * (chC a b + chH a b) -
        ∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1)) -
        ∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2)))) := by
    unfold chg1
    rw [hvu, form_red]
    have pt : ∀ a b, U a * g2 a b * V b - U a * g2 b a * V b =
        (1 / 2) * (U a * V b * (chC a b + chH a b) - U a * V b * (chC a b * z0 (b.2 - a.1)) -
          U a * V b * (chH a b * z0 (b.1 - a.2))) := by
      intro a b
      have := g2_skew h3 a b
      have e : U a * g2 a b * V b - U a * g2 b a * V b = U a * V b * (g2 a b - g2 b a) := by ring
      rw [e, this]
      ring
    have hsum : ∑ a, ∑ b, U a * g2 a b * V b - ∑ a, ∑ b, U a * g2 b a * V b =
        (1 / 2) * (∑ a, ∑ b, U a * V b * (chC a b + chH a b) -
          ∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1)) -
          ∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2))) := by
      rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
      refine sum_congr rfl fun a _ => ?_
      rw [← sum_sub_distrib, ← sum_sub_distrib, ← sum_sub_distrib, mul_sum]
      exact sum_congr rfl fun b _ => pt a b
    have : 1 / 2 * (1 / Nk (p := p) * ∑ a, ∑ b, U a * g2 a b * V b) +
        -1 / 2 * (1 / Nk (p := p) * ∑ a, ∑ b, U a * g2 b a * V b) -
        0 * (1 / Nk (p := p) * ∑ a, ∑ b, U a * g2 a b * V b) =
        (1 / Nk (p := p)) * ((1 / 2) * (∑ a, ∑ b, U a * g2 a b * V b -
          ∑ a, ∑ b, U a * g2 b a * V b)) := by ring
    rw [this, hsum]
    ring
  have hU := red_offDiag u
  have hV := red_offDiag v
  have hU0 := red_sum_zero hp3 hu
  have hV0 := red_sum_zero hp3 hv
  set S := Real.sqrt (n2 U) * Real.sqrt (n2 V)
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have b1 : |∑ a, ∑ b, U a * V b * (chC a b + chH a b)| ≤ (p : ℝ) * Real.sqrt p * S :=
    (bCD h3 hU hV hU0 hV0).trans (le_of_eq (by ring))
  have b2 : |∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1))| ≤ Real.sqrt p * S :=
    (bCz h3 U V).trans (le_of_eq (by ring))
  have b3 : |∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2))| ≤ Real.sqrt p * S :=
    (bDz h3 U V).trans (le_of_eq (by ring))
  have hT : |∑ a, ∑ b, U a * V b * (chC a b + chH a b) -
        ∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1)) -
        ∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2))| ≤
      (Real.sqrt p * ((p : ℝ) + 2)) * S := by
    rw [abs_le] at b1 b2 b3 ⊢
    constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2]
  have hNk := Nk_pos hE
  have hsc := sqrt_scale (K := Real.sqrt p * ((p : ℝ) + 2))
    (c := ((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)))
    (A := ∑ x, m3 p x * u x ^ 2) (B := ∑ x, m3 p x * v x ^ 2)
    (by positivity) (mul_nonneg (by have : (7 : ℝ) ≤ p := (by exact_mod_cast hp); linarith)
      (M3_pos hp3).le)
    (red_sq_m3 hp3 u) (red_sq_m3 hp3 v)
  rw [hX, abs_mul, abs_of_pos (one_div_pos.mpr hNk), abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
  calc 1 / Nk (p := p) * (1 / 4 * |_|) ≤
        1 / Nk (p := p) * (1 / 4 * ((Real.sqrt p * ((p : ℝ) + 2)) * S)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hT (by norm_num))
          (one_div_pos.mpr hNk).le
    _ ≤ 1 / Nk (p := p) * (1 / 4 * (Real.sqrt p * ((p : ℝ) + 2) *
          (((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) *
          Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ?_ (by norm_num))
          (one_div_pos.mpr hNk).le
        calc Real.sqrt p * ((p : ℝ) + 2) * S = Real.sqrt p * ((p : ℝ) + 2) *
              Real.sqrt (n2 U) * Real.sqrt (n2 V) := by ring
          _ ≤ _ := hsc
    _ = (1 / Nk (p := p) * (1 / 4 * (Real.sqrt p * ((p : ℝ) + 2) *
          (((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)))))) *
          Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by ring
    _ = _ := by rw [norm_const hE hp h3]; rfl

/-- **The form of `K₁` on mean-zero functions**: `rhoE p`. -/
theorem P3_form (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3)
    (u v : (ZMod p × ZMod p) × ZMod p → ℝ) (hu : ∑ x, m3 p x * u x = 0)
    (hv : ∑ x, m3 p x * v x = 0) :
    |u ⬝ᵥ (P3 hE *ᵥ v)| ≤
      rhoE p * Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by
  have hp3 : 3 ≤ p := by omega
  set U := red u
  set V := red v
  have hU := red_offDiag u
  have hV := red_offDiag v
  have hU0 := red_sum_zero hp3 hu
  have hV0 := red_sum_zero hp3 hv
  have pt : ∀ a b, U a * g2 a b * V b =
      (1 / 4) * (U a * V b * 1 - U a * V b * z0 (b.1 - a.2) - U a * V b * z0 (b.2 - a.1) +
        U a * V b * (z0 (b.1 - a.2) * z0 (b.2 - a.1)) + U a * V b * (chC a b * chH a b)) +
      (1 / 4) * (U a * V b * (chC a b + chH a b) - U a * V b * (chC a b * z0 (b.2 - a.1)) -
        U a * V b * (chH a b * z0 (b.1 - a.2))) := by
    intro a b
    have h1 := g2_skew h3 a b
    have h2 := g2_sym h3 a b
    have e : g2 a b = ((g2 a b + g2 b a) + (g2 a b - g2 b a)) / 2 := by ring
    rw [e, h1, h2]
    ring
  have h1s : ∑ a, ∑ b, U a * V b * (1 : ℝ) = 0 := by
    simp only [mul_one, ← mul_sum, ← sum_mul]
    rw [show ∑ i, V i = 0 from hV0, mul_zero]
  have hX : ∑ a, ∑ b, U a * g2 a b * V b =
      (1 / 4) * (∑ a, ∑ b, U a * V b * 1 - ∑ a, ∑ b, U a * V b * z0 (b.1 - a.2) -
        ∑ a, ∑ b, U a * V b * z0 (b.2 - a.1) +
        ∑ a, ∑ b, U a * V b * (z0 (b.1 - a.2) * z0 (b.2 - a.1)) +
        ∑ a, ∑ b, U a * V b * (chC a b * chH a b)) +
      (1 / 4) * (∑ a, ∑ b, U a * V b * (chC a b + chH a b) -
        ∑ a, ∑ b, U a * V b * (chC a b * z0 (b.2 - a.1)) -
        ∑ a, ∑ b, U a * V b * (chH a b * z0 (b.1 - a.2))) := by
    simp only [pt, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  set S := Real.sqrt (n2 U) * Real.sqrt (n2 V)
  have hS : 0 ≤ S := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have b1 := (bCD h3 hU hV hU0 hV0).trans (le_of_eq (show (p : ℝ) * Real.sqrt p *
    Real.sqrt (n2 U) * Real.sqrt (n2 V) = (p : ℝ) * Real.sqrt p * S by ring))
  have b2 := (bCz h3 U V).trans (le_of_eq (show Real.sqrt p * Real.sqrt (n2 U) *
    Real.sqrt (n2 V) = Real.sqrt p * S by ring))
  have b3 := (bDz h3 U V).trans (le_of_eq (show Real.sqrt p * Real.sqrt (n2 U) *
    Real.sqrt (n2 V) = Real.sqrt p * S by ring))
  have b4 := (bzC hU hV hU0 hV0).trans (le_of_eq (show (p : ℝ) * Real.sqrt (n2 U) *
    Real.sqrt (n2 V) = (p : ℝ) * S by ring))
  have b5 := (bzD hU hV hU0 hV0).trans (le_of_eq (show (p : ℝ) * Real.sqrt (n2 U) *
    Real.sqrt (n2 V) = (p : ℝ) * S by ring))
  have b6 := bzz U V
  have b7 := (bCC h3 U V).trans (le_of_eq (show (p : ℝ) * Real.sqrt (n2 U) *
    Real.sqrt (n2 V) = (p : ℝ) * S by ring))
  have hT : |∑ a, ∑ b, U a * g2 a b * V b| ≤
      (1 / 4) * ((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) * S := by
    rw [hX, h1s]
    rw [abs_le] at b1 b2 b3 b4 b5 b6 b7 ⊢
    change -(Real.sqrt (n2 U) * Real.sqrt (n2 V)) ≤ _ ∧ _ ≤ Real.sqrt (n2 U) * Real.sqrt (n2 V)
      at b6
    constructor <;> nlinarith [b1.1, b1.2, b2.1, b2.2, b3.1, b3.2, b4.1, b4.2, b5.1, b5.2, b6.1,
      b6.2, b7.1, b7.2]
  have hNk := Nk_pos hE
  have hK : 0 ≤ (p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1 := by positivity
  have hsc := sqrt_scale (K := (p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1)
    (c := ((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)))
    (A := ∑ x, m3 p x * u x ^ 2) (B := ∑ x, m3 p x * v x ^ 2) hK
    (mul_nonneg (by have : (7 : ℝ) ≤ p := (by exact_mod_cast hp); linarith) (M3_pos hp3).le)
    (red_sq_m3 hp3 u) (red_sq_m3 hp3 v)
  rw [form_red, abs_mul, abs_of_pos (one_div_pos.mpr hNk)]
  calc 1 / Nk (p := p) * |∑ a, ∑ b, U a * g2 a b * V b| ≤
        1 / Nk (p := p) * ((1 / 4) * ((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) * S) :=
        mul_le_mul_of_nonneg_left hT (one_div_pos.mpr hNk).le
    _ ≤ 1 / Nk (p := p) * ((1 / 4) * (((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) *
          (((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) *
          Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2))) := by
        refine mul_le_mul_of_nonneg_left ?_ (one_div_pos.mpr hNk).le
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        calc ((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) * S =
              ((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) *
              Real.sqrt (n2 U) * Real.sqrt (n2 V) := by ring
          _ ≤ _ := hsc
    _ = (1 / Nk (p := p) * ((1 / 4) * (((p : ℝ) * Real.sqrt p + 3 * p + 2 * Real.sqrt p + 1) *
          (((p : ℝ) - 2) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)))))) *
          Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by ring
    _ = _ := by rw [norm_const hE hp h3]; rfl

/-- **The centred norm of `K₁`** at one prime: `rhoE p`. -/
theorem P3_centred (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3) :
    CentredNorm (m3 p) (P3 hE) (rhoE p) := by
  have hp3 : 3 ≤ p := by omega
  have hd := den_pos (p := p) hp3
  refine centredNorm_of_form (m3_nonneg hp3) (P3_nonneg hE) (P3_row hE hp h3) (P3_col hE hp h3)
    (by unfold rhoE; positivity) fun u v hu hv => ?_
  have h := P3_form hE hp h3 u v hu hv
  simpa only [sq] using h

end Sarkozy.NormBoundsPaper3

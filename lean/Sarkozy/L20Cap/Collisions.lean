module

public import Sarkozy.L20Cap.Caps
public import Sarkozy.L20Cap.StarMatrix

/-!
# Balanced pinned collisions of L20 (`prop:l20-collisions`(a)): the row charges and the polynomial

`paper/sections/20_middle_reference.tex`, `prop:l20-collisions`(a). Notation of
`Sarkozy.L20Cap.Kernel`. The proof of (a) applies `cor:incident-weights` with the actual incident
weights; its two paper-specific ingredients are proved here:

* **the row charges** (`charge_pair`, `charges_core_le`, `pair_charge_le`): at a core label `y` of
  `x` distinct from the pair labels, the two products `∏_l (1 - χ(b_l - y))` and
  `∏_l (1 + χ(b_l - y))` are `0` or `4`, and not both `4`; hence `n₋ + n₊ ≤ 4`, the core charges
  add up to at most `32q`, and each pair charge `q(𝖪(b₀, C) + 𝖪(b₁, C))` is at most `32q`;
* **the polynomial** (`Fpoly_eq`, `Pc_eq`, `degree_two_le`): with
  `F(ρ_a, ρ_c) = ∑_{k,l ≤ 2} C(2,k)C(2,l) 2^{kl} ρ_a^k ρ_c^l`, the part of degree at least two of
  `F(ρ_a, ρ_c)(1 + ρ_{b₀})(1 + ρ_{b₁})` is at most its value `P_c - 96q` at `ρ_a = ρ_c = 8q`,
  `ρ_{b_l} = 32q`, when `ρ_a + ρ_c ≤ 16q`, `ρ_{b_l} ≤ 32q`; `P_c = (1 + 32q)² F(8q, 8q) - 1`.
* `Dbal`, the constant `D_bal = (S_c + U_c(P_c - 96q))/Λ_c` of the proposition, and
  `crossD_eq_D20`: the cross matrix of `Rectangle` is the fork's `D20` of `StarMatrix`.

The application to the actual soft L20 kernel is in `BalancedCollision.hD_balanced`,
which proves `‖T_coll‖ ≤ D_bal` and supplies `cutT_lower`/`cutT_upper`'s hypothesis `hD`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two copies of `D₂₀` agree. -/
theorem crossD_eq_D20 : crossD = D20 := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [crossD, D20, D20Z]

/-! ## The row charges -/

/-- At a label `y` distinct from `b₀ ≠ b₁`: `∏_l (1 - χ(b_l - y))` and `∏_l (1 + χ(b_l - y))` lie
in `{0, 4}` and their sum is at most `4`. -/
theorem charge_pair {y b₀ b₁ : F} (h₀ : b₀ ≠ y) (h₁ : b₁ ≠ y) :
    ((1 - chi (b₀ - y)) * (1 - chi (b₁ - y)) = 0 ∨ (1 - chi (b₀ - y)) * (1 - chi (b₁ - y)) = 4) ∧
    ((1 + chi (b₀ - y)) * (1 + chi (b₁ - y)) = 0 ∨ (1 + chi (b₀ - y)) * (1 + chi (b₁ - y)) = 4) ∧
    (1 - chi (b₀ - y)) * (1 - chi (b₁ - y)) + (1 + chi (b₀ - y)) * (1 + chi (b₁ - y)) ≤ 4 := by
  rcases chi_of_ne (sub_ne_zero.mpr h₀) with e0 | e0 <;>
    rcases chi_of_ne (sub_ne_zero.mpr h₁) with e1 | e1 <;> rw [e0, e1] <;> norm_num

/-- **The core charges**: `∑_{y ∈ core} (∏_l(1 - χ(b_l - y)) + ∏_l(1 + χ(b_l - y))) ≤ 16`, i.e.
`4(n₋ + n₊) ≤ 16`; with the factor `2q` of the two coordinates of each side, the core charges
`8(n₋ + n₊)q` add up to at most `32q`. -/
theorem charges_core_le (C : Fin 4 → F) (b₀ b₁ : F) (h₀ : ∀ k, b₀ ≠ C k) (h₁ : ∀ k, b₁ ≠ C k) :
    ∑ k, ((1 - chi (b₀ - C k)) * (1 - chi (b₁ - C k)) +
      (1 + chi (b₀ - C k)) * (1 + chi (b₁ - C k))) ≤ 16 := by
  have : ∀ k, (1 - chi (b₀ - C k)) * (1 - chi (b₁ - C k)) +
      (1 + chi (b₀ - C k)) * (1 + chi (b₁ - C k)) ≤ 4 := fun k =>
    (charge_pair (h₀ k) (h₁ k)).2.2
  calc _ ≤ ∑ _k : Fin 4, (4 : ℝ) := sum_le_sum fun k _ => this k
    _ = 16 := by simp; norm_num

/-- **The pair charge** `ρ_{b_l} = q(𝖪(b₀, C) + 𝖪(b₁, C)) ≤ 32q`. -/
theorem pair_charge_le (hm1 : quadraticChar F (-1) = -1) {C : Fin 4 → F} (hC : Adm C)
    (b₀ b₁ : F) {q : ℝ} (hq : 0 ≤ q) : q * (Kz b₀ C + Kz b₁ C) ≤ 32 * q := by
  have h0 := Kz_le hm1 hC b₀
  have h1 := Kz_le hm1 hC b₁
  nlinarith

/-! ## The balanced polynomial -/

/-- `F(ρ_a, ρ_c) = ∑_{k,l=0}^{2} C(2,k) C(2,l) 2^{kl} ρ_a^k ρ_c^l`. -/
noncomputable def Fpoly (a c : ℝ) : ℝ :=
  ∑ k ∈ range 3, ∑ l ∈ range 3, (Nat.choose 2 k : ℝ) * Nat.choose 2 l * 2 ^ (k * l) * a ^ k * c ^ l

/-- The closed form of `F` in `ρ_a + ρ_c` and `ρ_a ρ_c`. -/
theorem Fpoly_eq (a c : ℝ) :
    Fpoly a c = 1 + 2 * (a + c) + (a + c) ^ 2 + 6 * (a * c) + 8 * (a + c) * (a * c) +
      16 * (a * c) ^ 2 := by
  simp [Fpoly, sum_range_succ, Nat.choose]
  ring

/-- `P_c(q) = 96q + 3712q² + 81920q³ + 1245184q⁴ + 12582912q⁵ + 67108864q⁶`. -/
noncomputable def Pc (q : ℝ) : ℝ :=
  96 * q + 3712 * q ^ 2 + 81920 * q ^ 3 + 1245184 * q ^ 4 + 12582912 * q ^ 5 + 67108864 * q ^ 6

/-- **`P_c = (1 + 32q)² F(8q, 8q) - 1`**. -/
theorem Pc_eq (q : ℝ) : Pc q = (1 + 32 * q) ^ 2 * Fpoly (8 * q) (8 * q) - 1 := by
  rw [Fpoly_eq, Pc]
  ring

/-- The part of degree at least two, in `σ = ρ_a + ρ_c`, `π = ρ_a ρ_c`, `x = ρ_{b₀}`,
`y = ρ_{b₁}` (with `π` of degree two): all its coefficients are nonnegative. -/
noncomputable def degTwo (σ π x y : ℝ) : ℝ :=
  (σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) +
    (2 * σ + σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) * (x + y) +
    (1 + 2 * σ + σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) * (x * y)

/-- `degTwo` is the part of degree at least two of `F(ρ_a, ρ_c)(1 + ρ_{b₀})(1 + ρ_{b₁})`. -/
theorem degTwo_eq (a c x y : ℝ) :
    degTwo (a + c) (a * c) x y = Fpoly a c * (1 + x) * (1 + y) - 1 - 2 * (a + c) - x - y := by
  rw [Fpoly_eq, degTwo]
  ring

/-- **The balanced bound** (proof of `prop:l20-collisions`(a), two or more coincidences): for
`ρ_a, ρ_c ≥ 0` with `ρ_a + ρ_c ≤ 16q` and `0 ≤ ρ_{b_l} ≤ 32q`, the part of degree at least two
of `F(ρ_a, ρ_c)(1 + ρ_{b₀})(1 + ρ_{b₁})` is at most `P_c - 96q`. -/
theorem degree_two_le {q a c x y : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) (hac : a + c ≤ 16 * q)
    (hx : 0 ≤ x) (hx' : x ≤ 32 * q) (hy : 0 ≤ y) (hy' : y ≤ 32 * q) :
    Fpoly a c * (1 + x) * (1 + y) - 1 - 2 * (a + c) - x - y ≤ Pc q - 96 * q := by
  rw [← degTwo_eq]
  have hσ0 : 0 ≤ a + c := add_nonneg ha hc
  have hπ0 : 0 ≤ a * c := mul_nonneg ha hc
  have hq : 0 ≤ q := by linarith
  -- `ρ_a ρ_c ≤ (ρ_a + ρ_c)²/4 ≤ 64q²`
  have hπ : a * c ≤ 64 * q ^ 2 := by nlinarith [sq_nonneg (a - c)]
  have hP : Pc q - 96 * q = degTwo (16 * q) (64 * q ^ 2) (32 * q) (32 * q) := by
    rw [Pc, degTwo]; ring
  rw [hP]
  unfold degTwo
  set σ := a + c
  set π := a * c
  have h1 : σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2 ≤
      (16 * q) ^ 2 + 6 * (64 * q ^ 2) + 8 * (16 * q) * (64 * q ^ 2) + 16 * (64 * q ^ 2) ^ 2 := by
    have e1 : σ ^ 2 ≤ (16 * q) ^ 2 := pow_le_pow_left₀ hσ0 hac 2
    have e2 : σ * π ≤ (16 * q) * (64 * q ^ 2) := mul_le_mul hac hπ hπ0 (by positivity)
    have e3 : π ^ 2 ≤ (64 * q ^ 2) ^ 2 := pow_le_pow_left₀ hπ0 hπ 2
    nlinarith
  have hxy : x + y ≤ 32 * q + 32 * q := by linarith
  have hxy' : x * y ≤ (32 * q) * (32 * q) := mul_le_mul hx' hy' hy (by positivity)
  have hA0 : 0 ≤ σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2 := by positivity
  have hB : 2 * σ + (σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) ≤
      2 * (16 * q) + ((16 * q) ^ 2 + 6 * (64 * q ^ 2) + 8 * (16 * q) * (64 * q ^ 2) +
        16 * (64 * q ^ 2) ^ 2) := by linarith
  have hB0 : 0 ≤ 2 * σ + (σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) := by positivity
  have hC0 : 0 ≤ 1 + 2 * σ + (σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) := by positivity
  have t2 := mul_le_mul hB hxy (add_nonneg hx hy) (by positivity)
  have t3 := mul_le_mul (by linarith : 1 + 2 * σ + (σ ^ 2 + 6 * π + 8 * σ * π + 16 * π ^ 2) ≤
      1 + 2 * (16 * q) + ((16 * q) ^ 2 + 6 * (64 * q ^ 2) + 8 * (16 * q) * (64 * q ^ 2) +
        16 * (64 * q ^ 2) ^ 2)) hxy' (mul_nonneg hx hy) (by positivity)
  nlinarith [t2, t3, h1]

/-- The count errors `E_{c,j} = e_j(p, 12) = ((j/2 - 1)2^j + 1)r + 12·2^j q`. -/
noncomputable def Ec (r q : ℝ) (j : ℕ) : ℝ := (((j : ℝ) / 2 - 1) * 2 ^ j + 1) * r + 12 * 2 ^ j * q

/-- `Λ_c = (1 - r - 24q)⁴(1 - 6q)²`. -/
noncomputable def Lamc (r q : ℝ) : ℝ := (1 - r - 24 * q) ^ 4 * (1 - 6 * q) ^ 2

/-- `U_c = (1 + E_{c,4})⁶`. -/
noncomputable def Uc (r q : ℝ) : ℝ := (1 + Ec r q 4) ^ 6

/-- `S_c = 32q(1 + E_{c,3})²(1 + E_{c,4})³ + 64q(1 + E_{c,2})(1 + E_{c,3})²(1 + E_{c,4})²`. -/
noncomputable def Sc (r q : ℝ) : ℝ :=
  32 * q * (1 + Ec r q 3) ^ 2 * (1 + Ec r q 4) ^ 3 +
    64 * q * (1 + Ec r q 2) * (1 + Ec r q 3) ^ 2 * (1 + Ec r q 4) ^ 2

/-- **`D_bal = (S_c + U_c(P_c - 96q))/Λ_c`** (`prop:l20-collisions`). -/
noncomputable def Dbal (r q : ℝ) : ℝ := (Sc r q + Uc r q * (Pc q - 96 * q)) / Lamc r q

/-- `e₂(p, 6) = r + 24q` and `e₀(p, 6) = 6q`, so `Λ_c = (1 - e₂(p, 6))⁴(1 - e₀(p, 6))²`. -/
theorem Lamc_eq (r q : ℝ) : Lamc r q = (1 - (r + 24 * q)) ^ 4 * (1 - 6 * q) ^ 2 := by
  rw [Lamc]; ring

theorem Ec_two (r q : ℝ) : Ec r q 2 = r + 48 * q := by norm_num [Ec]
theorem Ec_three (r q : ℝ) : Ec r q 3 = 5 * r + 96 * q := by norm_num [Ec]
theorem Ec_four (r q : ℝ) : Ec r q 4 = 17 * r + 192 * q := by norm_num [Ec]

/-- `D_bal ≥ 0` when `r, q ≥ 0` and `Λ_c > 0`. -/
theorem Dbal_nonneg {r q : ℝ} (hr : 0 ≤ r) (hq : 0 ≤ q) (hL : 0 < Lamc r q) : 0 ≤ Dbal r q := by
  unfold Dbal Sc Uc
  rw [Ec_two, Ec_three, Ec_four]
  apply div_nonneg _ hL.le
  have hP : 0 ≤ Pc q - 96 * q := by unfold Pc; ring_nf; positivity
  positivity

end Sarkozy.L20Cap

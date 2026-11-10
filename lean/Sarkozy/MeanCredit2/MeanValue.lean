module

public import Sarkozy.MeanCredit2.Families
public import Sarkozy.ClassData.ExpBounds

@[expose] public section





open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassData Sarkozy.MeanCredit

/-- The raw-arm total `x` (RB's run at `a_G`, rounded up to `10⁻³⁰`). -/
def xq : ℚ := 350402582539780634749838448779 / 1000000000000000000000000000000
/-- The first-stage total `U` (rounded up to `10⁻³⁰`). -/
def Uq : ℚ := 350537160264678909887166023057 / 500000000000000000000000000000
/-- The invariant total `V` (rounded up to `10⁻³⁰`). -/
def Vq : ℚ := 701004908316205330854271372447 / 1000000000000000000000000000000
/-- `ρ_H = 3/(⌊√Q₃⌋(1 − 3/Q₃))`, `Q₃ = 19951586`, `⌊√Q₃⌋ = 4466`. -/
def rhoHq : ℚ := 3 / (4466 * (1 - 3 / 19951586))
/-- `w = U/(1 + ρ_H)`. -/
def wq : ℚ := Uq / (1 + rhoHq)
/-- `y = σ x`. -/
def yq : ℚ := sigmaQ * xq
/-- A lower bound for `e^U`. -/
def eUlo : ℚ := 20159172858624739348756853166796286613019 / 10 ^ 40
/-- A lower bound for `e^w`. -/
def ewlo : ℚ := 4029937535873230491172747492881407678011 / (2 * 10 ^ 39)

theorem isqrt_Q3 : 4466 ^ 2 ≤ 19951586 ∧ 19951586 < 4467 ^ 2 := by norm_num

theorem exp_Uq_ge : (eUlo : ℝ) ≤ Real.exp (Uq : ℝ) :=
  le_exp_of_ps (by norm_num [Uq]) (by norm_num [Uq]) (n := 40) (by norm_num)
    (by decide +kernel)

theorem exp_wq_ge : (ewlo : ℝ) ≤ Real.exp (wq : ℝ) :=
  le_exp_of_ps (by norm_num [wq, Uq, rhoHq]) (by norm_num [wq, Uq, rhoHq]) (n := 40)
    (by norm_num) (by decide +kernel)

/-- A factorial for the kernel. -/
def fac : ℕ → ℕ
  | 0 => 1
  | n + 1 => (n + 1) * fac n

theorem fac_eq (n : ℕ) : fac n = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih => rw [fac, ih, Nat.factorial_succ]

/-- A finite sum for the kernel. -/
def sumTo (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem cast_sumTo (f : ℕ → ℚ) (n : ℕ) :
    ((sumTo f n : ℚ) : ℝ) = ∑ j ∈ range n, (f j : ℝ) := by
  induction n with
  | zero => simp [sumTo]
  | succ n ih => rw [sumTo, sum_range_succ, Rat.cast_add, ih]

/-- The background value in `ℚ`, with a rational `e^U`. -/
def bgQ (a : ℕ → ℚ) (a0 : ℚ) (J : ℕ) (eU V : ℚ) : ℚ :=
  a0 * eU + sumTo (fun j => (a j - a0) * (V ^ j / fac j)) (J + 1)

/-- **The lower evaluation of the completed middle mean** (`meanValue` with `e^U`, `e^w` replaced by
`eUlo`, `ewlo`). -/
def meanLowQ : ℚ :=
  64 * (xq ^ 2 / (16 * hStar ^ 2) * ((ewlo - 1 - wq) / wq ^ 2)) +
  xq ^ 2 / 2 * bgQ (fun j => etaQ (j + 2)) eta0 8 eUlo Vq +
  (xq * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) *
    bgQ (fun j => zetaQ (j + 1)) zeta0 8 eUlo Vq +
  (yq ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720) * bgQ (fun j => rhoQ ^ j) 1 10 eUlo Vq

/-- **The kernel check**: `64 Δ_mid^{ledger} + 4·10⁻¹¹ ≤ meanLowQ` (untrusted margin
`4.63·10⁻¹¹`). -/
theorem meanLowQ_ge : 64 * ledgerMid + 4 / 10 ^ 11 ≤ meanLowQ := by decide +kernel

theorem cast_bgQ (a : ℕ → ℚ) (a0 : ℚ) (J : ℕ) (eU V : ℚ) :
    ((bgQ a a0 J eU V : ℚ) : ℝ) = (a0 : ℝ) * (eU : ℝ) +
      ∑ j ∈ range (J + 1), ((a j : ℝ) - a0) * ((V : ℝ) ^ j / (j.factorial : ℝ)) := by
  unfold bgQ
  rw [Rat.cast_add, Rat.cast_mul, cast_sumTo]
  congr 1
  refine sum_congr rfl fun j _ => ?_
  push_cast [fac_eq]
  ring

/-- **The completed middle mean at the harness's totals** (`prop:joint-middle-mean` at RB's `a_G`
point): `64 Δ_mid^{ledger} + 4·10⁻¹¹ ≤ meanValue xq wq yq Uq Vq`. -/
theorem meanValue_ge :
    64 * (ledgerMid : ℝ) + 4 / 10 ^ 11 ≤ meanValue xq wq yq Uq Vq := by
  have hq : ((64 * ledgerMid + 4 / 10 ^ 11 : ℚ) : ℝ) ≤ (meanLowQ : ℝ) := by
    exact_mod_cast meanLowQ_ge
  have hU := exp_Uq_ge
  have hw := exp_wq_ge
  have hw0 : (0 : ℝ) < (wq : ℝ) := by norm_num [wq, Uq, rhoHq]
  have hx0 : (0 : ℝ) ≤ (xq : ℝ) := by norm_num [xq]
  have hy0 : (0 : ℝ) ≤ (yq : ℝ) := by norm_num [yq, xq, sigmaQ]
  -- the difference is linear in the two exponentials, with nonnegative coefficients
  set eU := Real.exp (Uq : ℝ)
  set ew := Real.exp (wq : ℝ)
  have hcW : 0 ≤ 64 * ((xq : ℝ) ^ 2 / (16 * (hStar : ℝ) ^ 2)) / (wq : ℝ) ^ 2 := by positivity
  have hcU : 0 ≤ (xq : ℝ) ^ 2 / 2 * (eta0 : ℝ) +
      ((xq : ℝ) * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * (zeta0 : ℝ) +
      ((yq : ℝ) ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720) := by
    have : (0 : ℝ) ≤ eta0 := by norm_num [eta0]
    have : (0 : ℝ) ≤ zeta0 := by norm_num [zeta0]
    positivity
  have e : meanValue xq wq yq Uq Vq - (meanLowQ : ℝ) =
      64 * ((xq : ℝ) ^ 2 / (16 * (hStar : ℝ) ^ 2)) / (wq : ℝ) ^ 2 * (ew - ewlo) +
      ((xq : ℝ) ^ 2 / 2 * (eta0 : ℝ) +
        ((xq : ℝ) * yq + xq * (yq ^ 3 / 6) + xq * (yq ^ 5 / 120)) * (zeta0 : ℝ) +
        ((yq : ℝ) ^ 2 / 2 + yq ^ 4 / 24 + yq ^ 6 / 720)) * (eU - eUlo) := by
    unfold meanValue bgVal meanLowQ
    simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_ofNat, Rat.cast_one, cast_bgQ, aEta, aZeta, aRho]
    field_simp
    ring
  have h1 := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hw) hcW
  have h2 := mul_le_mul_of_nonneg_left (sub_nonneg.mpr hU) hcU
  push_cast at hq
  linarith

end Sarkozy.MeanCredit2

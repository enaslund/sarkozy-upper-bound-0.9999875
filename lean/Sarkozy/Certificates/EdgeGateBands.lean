module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The edge-moment gate on the 31 clique bands

`lem:density:clique36`, the band condition; `paper/sections/30_density_moment_upgrade.tex`.

The proof of `lem:density:clique36` uses `lem:density:edge-moment` on each dyadic band
`[2^b, 2^{b+16})`, `b = 16, 32, …, 496`, with the integer `j = j_b` listed there. Its gate
`eq:density:edge-integer-gate` reads
`j^{j+1} ((p + 1)/(p − 1))^{j − 1} / (√p − 1)² ≤ 1`.
* `gate_int`: at `p = 2^b` (`√p = 2^{b/2}`) the gate is the integer inequality
  `j^{j+1} (2^b + 1)^{j-1} ≤ (2^b − 1)^{j-1} (2^{b/2} − 1)²`. It is checked for all 31 bands by
  `decide +kernel`, which uses the kernel's arbitrary-precision arithmetic and no
  `ofReduceBool`.
* `edge_gate_band`: the gate holds for every real `x ≥ 2^b`, by monotonicity in `x`. In
  particular it holds at every prime of the band.

Not formalized here: the bilinear interpolation of `lem:density:edge-moment`, which turns the
gate into the moment bound, and the two finite tests of `lem:density:clique36` (a separate
certificate).
-/

@[expose] public section

namespace Sarkozy.EdgeGate

/-- The integers `j_b` of the proof of `lem:density:clique36`, for `b = 16, 32, …, 496`. -/
def bandJ : Fin 31 → ℕ :=
  ![5, 9, 12, 15, 18, 20, 23, 26, 28, 31, 33, 36, 38, 40, 43, 45, 47, 50, 52, 54, 56, 58, 61,
    63, 65, 67, 69, 71, 73, 75, 77]

/-- The band exponent `b = 16 (i + 1)`. -/
def bandB (i : Fin 31) : ℕ := 16 * (i.val + 1)

/-- **The gate at `p = 2^b`, in integers**, for all 31 bands (`b = 2m`, `m = 8 (i + 1)`). -/
theorem gate_int : ∀ i : Fin 31,
    bandJ i ^ (bandJ i + 1) * (2 ^ (2 * (8 * (i.val + 1))) + 1) ^ (bandJ i - 1) ≤
      (2 ^ (2 * (8 * (i.val + 1))) - 1) ^ (bandJ i - 1) * (2 ^ (8 * (i.val + 1)) - 1) ^ 2 := by
  decide +kernel

/-- **From the integer check at `x₀ = 2^{2m}` to every `x ≥ x₀`**, by monotonicity. -/
theorem edge_gate_of_int {j m : ℕ} (hm : 8 ≤ m)
    (hint : j ^ (j + 1) * (2 ^ (2 * m) + 1) ^ (j - 1) ≤
      (2 ^ (2 * m) - 1) ^ (j - 1) * (2 ^ m - 1) ^ 2)
    {x : ℝ} (hx : (2 : ℝ) ^ (2 * m) ≤ x) :
    (j : ℝ) ^ (j + 1) * ((x + 1) / (x - 1)) ^ (j - 1) * (1 / (Real.sqrt x - 1) ^ 2) ≤ 1 := by
  set x₀ : ℝ := (2 : ℝ) ^ (2 * m) with hx₀
  set s₀ : ℝ := (2 : ℝ) ^ m with hs₀
  have hs₀sq : s₀ ^ 2 = x₀ := by
    rw [hs₀, hx₀, ← pow_mul, mul_comm]
  have hs₀256 : (256 : ℝ) ≤ s₀ := by
    rw [hs₀, show (256 : ℝ) = 2 ^ 8 by norm_num]
    exact pow_le_pow_right₀ (by norm_num) hm
  have hx₀pos : 1 < x₀ := by nlinarith
  have hx1 : 1 < x := lt_of_lt_of_le hx₀pos hx
  have hsqrt : s₀ ≤ Real.sqrt x := by
    rw [← Real.sqrt_sq (by linarith : (0 : ℝ) ≤ s₀), hs₀sq]
    exact Real.sqrt_le_sqrt hx
  have hratio : (x + 1) / (x - 1) ≤ (x₀ + 1) / (x₀ - 1) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hratio0 : 0 ≤ (x + 1) / (x - 1) := div_nonneg (by linarith) (by linarith)
  have hden : 1 / (Real.sqrt x - 1) ^ 2 ≤ 1 / (s₀ - 1) ^ 2 := by
    apply one_div_le_one_div_of_le (by nlinarith)
    nlinarith
  have hstep : (j : ℝ) ^ (j + 1) * ((x + 1) / (x - 1)) ^ (j - 1) * (1 / (Real.sqrt x - 1) ^ 2) ≤
      (j : ℝ) ^ (j + 1) * ((x₀ + 1) / (x₀ - 1)) ^ (j - 1) * (1 / (s₀ - 1) ^ 2) := by
    apply mul_le_mul _ hden (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hratio0 hratio _) (by positivity)
  refine hstep.trans ?_
  have h1 : (1 : ℕ) ≤ 2 ^ (2 * m) := Nat.one_le_two_pow
  have h2 : (1 : ℕ) ≤ 2 ^ m := Nat.one_le_two_pow
  have hcast : ((j : ℝ) ^ (j + 1) * (x₀ + 1) ^ (j - 1)) ≤ (x₀ - 1) ^ (j - 1) * (s₀ - 1) ^ 2 := by
    have := (Nat.cast_le (α := ℝ)).mpr hint
    push_cast [Nat.cast_sub h1, Nat.cast_sub h2] at this
    exact this
  have hA : 0 < x₀ - 1 := by linarith
  have hB : 0 < (s₀ - 1) ^ 2 := by nlinarith
  rw [div_pow, show (j : ℝ) ^ (j + 1) * ((x₀ + 1) ^ (j - 1) / (x₀ - 1) ^ (j - 1)) *
      (1 / (s₀ - 1) ^ 2) = (j : ℝ) ^ (j + 1) * (x₀ + 1) ^ (j - 1) /
        ((x₀ - 1) ^ (j - 1) * (s₀ - 1) ^ 2) by field_simp,
    div_le_one (by positivity)]
  exact hcast

/-- **The edge-moment gate on each band**: for every real `x ≥ 2^b`,
`j_b^{j_b+1} ((x + 1)/(x − 1))^{j_b − 1} / (√x − 1)² ≤ 1`. -/
theorem edge_gate_band (i : Fin 31) {x : ℝ} (hx : (2 : ℝ) ^ bandB i ≤ x) :
    (bandJ i : ℝ) ^ (bandJ i + 1) * ((x + 1) / (x - 1)) ^ (bandJ i - 1) *
      (1 / (Real.sqrt x - 1) ^ 2) ≤ 1 := by
  have hb : bandB i = 2 * (8 * (i.val + 1)) := by
    unfold bandB
    ring
  rw [hb] at hx
  exact edge_gate_of_int (by omega) (gate_int i) hx

end Sarkozy.EdgeGate

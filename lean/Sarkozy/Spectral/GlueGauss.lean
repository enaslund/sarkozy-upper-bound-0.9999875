module

public import Sarkozy.SpectralC.Gauss
public import Sarkozy.Spectral.LocalVariance
public import Sarkozy.ProbabilityConstructions

/-!
# Glue, III: the bound `L_i` from `lem:spec:gauss`

`lem:push:localvariance` (b), the linear part: `f_i = s_i 2^{m_i} C 1_{Φ}` with `C` the Gauss
operator `(Ch)(a) = E_b χ(b - a) h(b)` (WP-K's `SpectralC.gaussOp`, the same convention), and
`lem:spec:gauss` (`SpectralC.l2sq_gaussOp_le`, `‖Ch‖² ≤ r² ‖h‖²` in `L²` of the uniform law)
gives `‖f_i‖² ≤ 4^{m_i} r² |Φ|/p = 2^{m_i} A_i r²` with `A_i = 2^{m_i}|Φ|/p`.

* `glue_gauss_f`: that bound, for the real function `a ↦ s 2^m re (C 1_Φ)(a)` (`C 1_Φ` is real,
  so this is `f_i`), in the norm `Sarkozy.Spectral.l2` of the uniform law on `𝔽_p`; it is the
  hypothesis `hf` of `Sarkozy.Spectral.L_bound` with `G = (2^m A)^{1/2} r`.
* `glue_L_bound`: `L_bound` with this `G`, `‖q_i - A_i‖_{L²(μ)} ≤ κ^{1/2}(2^m A)^{1/2} r + c`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Spectral

open Sarkozy

variable {p : ℕ} [Fact p.Prime]

/-- The uniform law on `𝔽_p`. -/
noncomputable abbrev unifP (p : ℕ) [Fact p.Prime] : FiniteLaw (ZMod p) :=
  FiniteLaw.uniform (ZMod p)

/-- **`lem:spec:gauss` for `f_i`**: `‖s 2^m re(C 1_Φ)‖ ≤ (2^m · 2^m |Φ|/p)^{1/2} r`. -/
theorem glue_gauss_f (hp2 : p ≠ 2) (Φ : Finset (ZMod p)) {s : ℝ} (hs : |s| ≤ 1) (m : ℕ) :
    l2 (unifP p) (fun a => s * 2 ^ m *
        (SpectralC.gaussOp (fun b => if b ∈ Φ then (1 : ℂ) else 0) a).re) ≤
      Real.sqrt (2 ^ m * (2 ^ m * Φ.card / p)) * SpectralC.rp p := by
  set h : ZMod p → ℂ := fun b => if b ∈ Φ then (1 : ℂ) else 0 with hh
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hrp : 0 ≤ SpectralC.rp p := by unfold SpectralC.rp; positivity
  -- `l2sq h = |Φ|/p`
  have hl2h : SpectralC.l2sq h = Φ.card / p := by
    unfold SpectralC.l2sq
    have : ∀ a, ‖h a‖ ^ 2 = if a ∈ Φ then 1 else 0 := fun a => by
      by_cases ha : a ∈ Φ <;> simp [hh, ha]
    rw [Finset.sum_congr rfl fun a _ => this a, Finset.sum_boole, Finset.filter_mem_eq_inter,
      Finset.univ_inter]
    field_simp
  have hG := SpectralC.l2sq_gaussOp_le hp2 h
  rw [hl2h] at hG
  -- the expectation of `f²`
  have hE : (unifP p).expect (fun a => (s * 2 ^ m * (SpectralC.gaussOp h a).re) ^ 2) ≤
      4 ^ m * SpectralC.l2sq (SpectralC.gaussOp h) := by
    rw [FiniteLaw.expect_uniform, hcard, SpectralC.l2sq, div_eq_inv_mul, Finset.mul_sum,
      Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun a _ => ?_
    have h1 : (s * 2 ^ m * (SpectralC.gaussOp h a).re) ^ 2 ≤
        4 ^ m * ‖SpectralC.gaussOp h a‖ ^ 2 := by
      have hre := RCLike.abs_re_le_norm (SpectralC.gaussOp h a)
      have hs2 : s ^ 2 ≤ 1 := by nlinarith [abs_nonneg s, sq_abs s]
      have hre2 : (SpectralC.gaussOp h a).re ^ 2 ≤ ‖SpectralC.gaussOp h a‖ ^ 2 := by
        have := pow_le_pow_left₀ (abs_nonneg _) hre 2
        rwa [sq_abs] at this
      have h4 : ((2 : ℝ) ^ m) ^ 2 = 4 ^ m := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
      calc (s * 2 ^ m * (SpectralC.gaussOp h a).re) ^ 2
          = s ^ 2 * ((2 : ℝ) ^ m) ^ 2 * (SpectralC.gaussOp h a).re ^ 2 := by ring
        _ ≤ 1 * ((2 : ℝ) ^ m) ^ 2 * ‖SpectralC.gaussOp h a‖ ^ 2 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hs2 (by positivity)) hre2
              (sq_nonneg _) (by positivity)
        _ = 4 ^ m * ‖SpectralC.gaussOp h a‖ ^ 2 := by rw [h4, one_mul]
    calc (p : ℝ)⁻¹ * (s * 2 ^ m * (SpectralC.gaussOp h a).re) ^ 2
        ≤ (p : ℝ)⁻¹ * (4 ^ m * ‖SpectralC.gaussOp h a‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = 4 ^ m * ((p : ℝ)⁻¹ * ‖SpectralC.gaussOp h a‖ ^ 2) := by ring
  have hbound : (unifP p).expect (fun a => (s * 2 ^ m * (SpectralC.gaussOp h a).re) ^ 2) ≤
      (Real.sqrt (2 ^ m * (2 ^ m * Φ.card / p)) * SpectralC.rp p) ^ 2 := by
    refine hE.trans ?_
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    have h4 : (4 : ℝ) ^ m = 2 ^ m * 2 ^ m := by rw [← mul_pow]; norm_num
    calc 4 ^ m * SpectralC.l2sq (SpectralC.gaussOp h)
        ≤ 4 ^ m * (SpectralC.rp p ^ 2 * (Φ.card / p)) :=
          mul_le_mul_of_nonneg_left hG (by positivity)
      _ = 2 ^ m * (2 ^ m * Φ.card / p) * SpectralC.rp p ^ 2 := by rw [h4]; ring
  unfold l2
  exact Real.sqrt_le_iff.mpr ⟨by positivity, hbound⟩

/-- **The bound `L_i`** from `lem:spec:gauss` (`Sarkozy.Spectral.L_bound` with `glue_gauss_f`):
if `q = A + s 2^m re(C 1_Φ) - c 1` on `𝔽_p` (the identity of the proof) and the law `μ` has
density at most `κ` relative to the uniform law, then
`‖q - A‖_{L²(μ)} ≤ κ^{1/2} (2^m · 2^m|Φ|/p)^{1/2} r + c`. -/
theorem glue_L_bound (hp2 : p ≠ 2) (μ : FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ a, μ.weight a ≤ κ * (unifP p).weight a) (Φ : Finset (ZMod p)) {s : ℝ}
    (hs : |s| ≤ 1) (m : ℕ) (q ind : ZMod p → ℝ) {A c : ℝ} (hc : 0 ≤ c)
    (hind : ∀ a, |ind a| ≤ 1)
    (hq : ∀ a, q a = A + s * 2 ^ m *
      (SpectralC.gaussOp (fun b => if b ∈ Φ then (1 : ℂ) else 0) a).re - c * ind a) :
    l2 μ (fun a => q a - A) ≤
      √κ * (Real.sqrt (2 ^ m * (2 ^ m * Φ.card / p)) * SpectralC.rp p) + c :=
  L_bound μ (unifP p) hκ hd q _ ind hc hind hq (glue_gauss_f hp2 Φ hs m)

end Sarkozy.Spectral

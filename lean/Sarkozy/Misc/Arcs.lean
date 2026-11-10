module

public import Sarkozy.Misc.WeylEven
public import Sarkozy.Kernel.AdmissibleRates
public import Sarkozy.Kernel.GeneralKernel

@[expose] public section

/-!
# Arcs (`lem:record:arcs`)

`paper/sections/C_kernel.tex`, `lem:record:arcs`. The lemma organizes the circle method of the
paper's Appendix C proof of `prop:record:kernel20`. The formal proof of that proposition
(`Sarkozy.Kernel.prop_kernel20`, WP-K) takes upstream's circle-method scheme instead, with other
arc parameters, so this lemma is not on the formal route; it is formalized here for coverage of
the paper's own argument.

Notation: `‖x‖` is `Sarkozy.Kernel.circleDistance x`, `e(t)` is `expPhase t`,
`V_N(x) = N⁻¹ ∑_{n=1}^N e(xn)` is `normalizedLinearSum N x`. Points of `ℚ/ℤ` are rationals `b`;
"distinct" means `b - c ∉ ℤ`. The major arc of a reduced fraction `a/q`, `q ≤ N^η`, is
`{α : ‖α - a/q‖ ≤ 2 N^{-1+η}}`. "For `N` large" is replaced by the explicit inequalities used in
the proof (the paper derives them from (K0)–(K2)); `eventually_mul_rpow_le_one` turns any of
them into a threshold `N₀`.

**Proved.**
* (i) `majorArcs_disjoint` (two major arcs are disjoint when `4 N^{-1+η} < N^{-2η}`, the form of
  (K0) used; `eventually_majorArcs_disjoint` gives `N₀` from `0 < η`, `3η < 1`) and
  `minorArc_approx` (every `α` off the major arcs has a reduced `a/q` with
  `N^η < q ≤ N^{1-η}` and `|α - a/q| ≤ q⁻²`, by Dirichlet with `Q₀ = ⌊N^{1-η}⌋`).
* (ii) `centre_separation`: for `α = a/q + y`, `|y| ≤ 2 N^{-1+η}`, every fraction `c ≠ a/q` of
  denominator `≤ L` (`L = DH`) has `‖α - c‖ ≥ (2qL)⁻¹`, when `4 q L N^{-1+η} ≤ 1` (the form of (K2)
  used). The first sentence of (ii) — a centre has denominator `≤ DH < N^η`, by (K1), so it is the
  centre of a major arc — is the hypothesis `c.den ≤ N^η` of `minorArc_model_sum`.
* (iii) `minorArc_weighted_sum`: on a minor arc,
  `|∑_{m ≤ √N} (2m/N) e(α m² + λ m)| ≤ 116 N^{-η/2} (log 2N)^{1/2}` (`N ≥ 2`, `0 ≤ η < 1/2`), from
  `lem:record:weyl-even` (`Misc.weyl_even`) and partial summation, with the paper's intermediate
  bound `801 N^{1-η} log(2N)`; `character_twist_sum`: expanding `Φ` as a finite sum of additive
  characters with coefficients of total size `A` multiplies the bound by `A` (so
  `|S(α)| ≤ 116 D'H N^{-η/2} (log 2N)^{1/2}` when `A = D'H`, `def:record:K20-kernels`(c));
  `minorArc_model_sum`: a sum `∑_c c₀(c) V_N(α - c)` over centres at distance `> 2N^{-1+η}` with
  `|c₀| ≤ 1` is at most `#centres/(4N^η)` (so `|S₀(α)| ≤ DH²/(4N^η)` by `lem:record:K20-centres`).
* (iv), model kernel: `majorArc_model_sum`, `S₀(α) = c₀(α₀) V_N(y) + R₀` with
  `|R₀| ≤ #centres · qL/N` (so `≤ q D² H³ / N`).
* (iv), actual kernel: `majorArc_actual_sum`, `S(α) = c(α₀) V_N(y) + R₁` with
  `|R₁| ≤ ∑_u (2T_u + 1) D' (4 + 8π|y|N)/√N`, for `S` written as `∑_u ε_u ∑_m f_y(m) a_u(m)`
  with periodic `a_u` (`a_u = ρ_D w_u e(α₀ m²)`, `ε_u = (-1)^{ω(u)}`). This is WP-K's ported
  `periodic_square_main` summed over `u`, not the paper's Stieltjes computation: the constants
  differ from the paper's `18 q D² H² (1 + |y|N)/√N + 2π|y|H`, the exponents after
  `T_u ≤ D'uq`, `q ≤ N^η`, `|y| ≤ 2N^{-1+η}` are the same (`N^{2η+2κ+β-1/2}`), and the
  statement of (iv) only asks for some constant `C`.
* The exponent arithmetic: `arc_exponents_twentieth` (the five exponents at
  `(1/20, 1/20, 17/100)` are `-1/100, -7/100, -131/200, -1/100, -161/200`, all `< -1/120`) and
  `arc_exponents_admissible` (for an admissible triple the four exponents are the left sides of
  (E1)–(E4), hence `< -β/6`, and `η + β/2 - 1` is below the third). The seven slacks are
  WP-K's `cor_kernel20_slacks`.

* **The tree's model kernel.** For WP-K's model `S₀(α) = ∑_{(j,ξ)} e(jr/D) g(ξ) V_N(α - j/D - ξ)`
  (`Kernel.centre`, `Kernel.centreCoeff`, the form of `lem:record:K20-centres` used by
  `Kernel.general_kernel_rate`): `card_centreIndex_le` (`≤ D H²` centres), `centre_major` ((ii),
  first sentence: every centre is a major-arc centre when `⌈DH⌉ ≤ N^η`),
  `centre_fiber_subsingleton` (the centres are distinct in `ℚ/ℤ`), `minorArc_S0_kernel` ((iii):
  `|S₀(α)| ≤ DH²/(4N^η)` on a minor arc) and `majorArc_S0_kernel` ((iv):
  `S₀(α) = c₀(b) V_N(y) + R₀`, `|R₀| ≤ DH² q⌈DH⌉/N`); and **`arcs_model_kernel`**, (ii)–(iv) for
  this `S₀` in the paper's form: at every admissible triple, for `N` large, `D ≤ C_D N^κ`,
  `1 ≤ H ≤ C_H N^{β/2}`, every centre is a major-arc centre, `|S₀| ≤ C N^{κ+β-η}` on the minor
  arcs and `|R₀| ≤ C N^{η+2κ+3β/2-1}` near every major-arc centre, with `C = 2 C_D² C_H³`.

**The actual kernel.** (iii) and (iv) for the tree's actual kernel
`finiteSquareKernel (termSign …) (termWeight …)` are in `Sarkozy.Misc.ActualKernel`
(`minorArc_S_kernel_rpow`, `majorArc_S_kernel_rpow`), through the expansion of its weights into
additive characters. The constants of (iv) differ from the paper's (the statement asks for some
`C`); the statements use explicit inequalities in place of "`N` large", with
`eventually_mul_rpow_le_one` for the thresholds.
-/

namespace Sarkozy.Misc

open Finset Sarkozy.Kernel

/-! ## Circle distance -/

/-- The triangle inequality on `ℝ/ℤ`. -/
theorem circleDistance_sub_le_add (s t : ℝ) :
    circleDistance (s - t) ≤ circleDistance s + circleDistance t := by
  refine (circleDistance_sub_le s t).trans ?_
  exact abs_sub _ _

theorem circleDistance_le_abs (t : ℝ) : circleDistance t ≤ |t| := by
  have h := circleDistance_le_abs_sub_int t 0
  simpa using h

/-! ## "For `N` large" -/

/-- **`N` large**: for `a < 0`, `C N^a ≤ 1` for all large `N`. -/
theorem eventually_mul_rpow_le_one (C a : ℝ) (ha : a < 0) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → C * (N : ℝ) ^ a ≤ 1 := by
  rcases le_or_gt C 0 with hC | hC
  · refine ⟨0, fun N _ => ?_⟩
    have : 0 ≤ (N : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg N) a
    nlinarith
  · have ht : Filter.Tendsto (fun x : ℝ => x ^ a) Filter.atTop (nhds 0) := by
      have := tendsto_rpow_neg_atTop (y := -a) (by linarith)
      simpa using this
    have ht' := ht.comp tendsto_natCast_atTop_atTop
    have hev : ∀ᶠ N : ℕ in Filter.atTop, (N : ℝ) ^ a < C⁻¹ :=
      ht'.eventually (gt_mem_nhds (inv_pos.mpr hC))
    obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hev
    refine ⟨N₀, fun N hN => ?_⟩
    have := hN₀ N hN
    have h2 : C * (N : ℝ) ^ a ≤ C * C⁻¹ := mul_le_mul_of_nonneg_left this.le hC.le
    rwa [mul_inv_cancel₀ hC.ne'] at h2

/-- `N^{-1+η} = N^{3η-1} N^{-2η}`. -/
theorem rpow_split {N : ℕ} (hN : 1 ≤ N) (η : ℝ) :
    (N : ℝ) ^ (-1 + η) = (N : ℝ) ^ (3 * η - 1) * (N : ℝ) ^ (-(2 * η)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [← Real.rpow_add hN0]
  congr 1
  ring

/-! ## (i) Major and minor arcs -/

/-- **`lem:record:arcs`(i), disjointness.** If `4 N^{-1+η} < N^{-2η}`, two distinct reduced
fractions of denominators at most `N^η` have disjoint major arcs. -/
theorem majorArcs_disjoint {N : ℕ} (hN : 1 ≤ N) {η : ℝ}
    (hK0 : 4 * (N : ℝ) ^ (-1 + η) < (N : ℝ) ^ (-(2 * η)))
    (b c : ℚ) (hb : (b.den : ℝ) ≤ (N : ℝ) ^ η) (hc : (c.den : ℝ) ≤ (N : ℝ) ^ η)
    (hbc : ¬ ∃ k : ℤ, b - c = k) (α : ℝ)
    (hαb : circleDistance (α - b) ≤ 2 * (N : ℝ) ^ (-1 + η)) :
    2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - c) := by
  by_contra h
  push Not at h
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hlow := rational_difference_lower b c hbc
  have htri : circleDistance ((b : ℝ) - c) ≤ circleDistance (α - c) + circleDistance (α - b) := by
    have := circleDistance_sub_le_add (α - c) (α - b)
    rwa [show α - (c : ℝ) - (α - b) = (b : ℝ) - c by ring] at this
  have hbpos : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  have hcpos : (0 : ℝ) < c.den := Nat.cast_pos.mpr c.pos
  have hprod : (b.den : ℝ) * c.den ≤ (N : ℝ) ^ η * (N : ℝ) ^ η :=
    mul_le_mul hb hc hcpos.le (Real.rpow_nonneg hN0.le η)
  have hpow : (N : ℝ) ^ (-(2 * η)) = ((N : ℝ) ^ η * (N : ℝ) ^ η)⁻¹ := by
    rw [Real.rpow_neg hN0.le, ← Real.rpow_add hN0, two_mul]
  have hinv : (N : ℝ) ^ (-(2 * η)) ≤ 1 / ((b.den : ℝ) * c.den) := by
    rw [hpow, one_div]
    exact inv_anti₀ (by positivity) hprod
  linarith

/-- For `0 < η` and `3η < 1` (`(K0)`), the major arcs are pairwise disjoint for `N` large. -/
theorem eventually_majorArcs_disjoint {η : ℝ} (hK0 : 3 * η < 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 1 ≤ N → 4 * (N : ℝ) ^ (-1 + η) < (N : ℝ) ^ (-(2 * η)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_mul_rpow_le_one 8 (3 * η - 1) (by linarith)
  refine ⟨N₀, fun N hN hN1 => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have h := hN₀ N hN
  have hp : 0 < (N : ℝ) ^ (-(2 * η)) := Real.rpow_pos_of_pos hN0 _
  rw [rpow_split hN1]
  nlinarith

/-- **`lem:record:arcs`(i), minor arcs.** If `α` lies on no major arc (every reduced fraction of
denominator at most `N^η` is at distance more than `2N^{-1+η}`), then Dirichlet's theorem with
`Q₀ = ⌊N^{1-η}⌋` gives a reduced fraction `b` with `N^η < q ≤ N^{1-η}` and `|α - b| ≤ q⁻²`. -/
theorem minorArc_approx {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (hη : η ≤ 1) (α : ℝ)
    (hminor : ∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
      2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b)) :
    ∃ b : ℚ, (N : ℝ) ^ η < b.den ∧ (b.den : ℝ) ≤ (N : ℝ) ^ (1 - η) ∧
      |α - b| ≤ 1 / (b.den : ℝ) ^ 2 := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hW : (1 : ℝ) ≤ (N : ℝ) ^ (1 - η) := Real.one_le_rpow hN1 (by linarith)
  set Q₀ : ℕ := ⌊(N : ℝ) ^ (1 - η)⌋₊ with hQ₀
  have hQpos : 0 < Q₀ := Nat.floor_pos.mpr hW
  obtain ⟨b, hbd, hb1, hb2⟩ := dirichlet_fraction α Q₀ hQpos
  have hbpos : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  have hQle : (Q₀ : ℝ) ≤ (N : ℝ) ^ (1 - η) := Nat.floor_le (by linarith)
  have hQlt : (N : ℝ) ^ (1 - η) < (Q₀ : ℝ) + 1 := Nat.lt_floor_add_one _
  refine ⟨b, ?_, (Nat.cast_le.mpr hbd).trans hQle, ?_⟩
  · by_contra hsmall
    push Not at hsmall
    have hfar := hminor b hsmall
    have hclose : circleDistance (α - b) ≤ (N : ℝ) ^ (-1 + η) := by
      refine (circleDistance_le_abs _).trans (hb1.trans ?_)
      have h1 : 1 / (((Q₀ : ℝ) + 1) * b.den) ≤ 1 / ((Q₀ : ℝ) + 1) := by
        apply one_div_le_one_div_of_le (by positivity)
        have : (1 : ℝ) ≤ b.den := by exact_mod_cast b.pos
        nlinarith
      refine h1.trans ?_
      have h2 : (N : ℝ) ^ (-1 + η) = ((N : ℝ) ^ (1 - η))⁻¹ := by
        rw [← Real.rpow_neg hN0.le]
        congr 1
        ring
      rw [h2, one_div]
      exact inv_anti₀ (by positivity) hQlt.le
    have hpos : 0 < (N : ℝ) ^ (-1 + η) := Real.rpow_pos_of_pos hN0 _
    linarith
  · rw [Rat.cast_def]
    exact hb2

/-! ## (ii) Separation of the centres -/

/-- **`lem:record:arcs`(ii).** Let `α = b + y` with `q = b.den`, `|y| ≤ 2 N^{-1+η}`, and let
`4 q L N^{-1+η} ≤ 1`. Every fraction `c` of denominator at most `L` with `c ≠ b` in `ℚ/ℤ`
satisfies `‖α - c‖ ≥ (2 q L)⁻¹`. (With `L = DH`, the bound on the centres' denominators.) -/
theorem centre_separation {N : ℕ} {η L : ℝ} (b : ℚ) (y : ℝ)
    (hy : |y| ≤ 2 * (N : ℝ) ^ (-1 + η)) (hL : 0 < L)
    (hK2 : 4 * (b.den : ℝ) * L * (N : ℝ) ^ (-1 + η) ≤ 1)
    (c : ℚ) (hc : (c.den : ℝ) ≤ L) (hbc : ¬ ∃ k : ℤ, b - c = k) :
    1 / (2 * (b.den : ℝ) * L) ≤ circleDistance ((b : ℝ) + y - c) := by
  have hbpos : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  have hcpos : (0 : ℝ) < c.den := Nat.cast_pos.mpr c.pos
  have hlow := rational_difference_lower b c hbc
  have hlow' : 1 / ((b.den : ℝ) * L) ≤ circleDistance ((b : ℝ) - c) := by
    refine le_trans ?_ hlow
    apply one_div_le_one_div_of_le (by positivity)
    exact mul_le_mul_of_nonneg_left hc hbpos.le
  have hy' : |y| ≤ 1 / (2 * (b.den : ℝ) * L) := by
    rw [le_div_iff₀ (by positivity)]
    have := mul_le_mul_of_nonneg_right hy (by positivity : (0 : ℝ) ≤ 2 * b.den * L)
    nlinarith
  have hlip := circleDistance_lipschitz ((b : ℝ) - c) ((b : ℝ) + y - c)
  rw [show (b : ℝ) - c - ((b : ℝ) + y - c) = -y by ring, abs_neg] at hlip
  have hhalf : 1 / ((b.den : ℝ) * L) = 2 * (1 / (2 * (b.den : ℝ) * L)) := by
    field_simp
  linarith

/-! ## (iii) Minor arcs -/

/-- The partial sums of `z_m = e(α (m+1)² + λ (m+1))` are the sums `∑_{m=1}^{L}` of
`lem:record:weyl-even`. -/
theorem norm_sum_range_succ_eq (α lam : ℝ) (L : ℕ) :
    ‖∑ m ∈ range L, expPhase (α * ((m : ℝ) + 1) ^ 2 + lam * ((m : ℝ) + 1))‖ =
      ‖∑ m ∈ Icc 1 L, expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ := by
  rw [norm_sum_Icc_one_eq, quadratic_sum_shift]

/-- `∑_{m=1}^{M} (2m/N) e(α m² + λ m) = (2/N) ∑_{m<M} (m+1) z_m`. -/
theorem weighted_sum_eq (α lam : ℝ) (N M : ℕ) :
    ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) • expPhase (α * (m : ℝ) ^ 2 + lam * m) =
      (2 / (N : ℝ)) • ∑ m ∈ range M,
        ((m : ℝ) + 1) • expPhase (α * ((m : ℝ) + 1) ^ 2 + lam * ((m : ℝ) + 1)) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range, smul_sum]
  refine sum_congr (by simp) fun m _ => ?_
  rw [smul_smul]
  push_cast
  congr 1
  · ring
  · congr 1
    ring

/-- The bound `M + 200 (M/q + 1)(M + q log 2q) ≤ 801 N^{1-η} log(2N)` of the proof of
`lem:record:arcs`(iii), for `M = ⌊√N⌋`, `N^η < q ≤ N^{1-η}`, `0 ≤ η ≤ 1/2`, `N ≥ 2`. -/
theorem weyl_minor_bound {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2) (q : ℕ)
    (hq1 : (N : ℝ) ^ η < q) (hq2 : (q : ℝ) ≤ (N : ℝ) ^ (1 - η)) :
    (Nat.sqrt N : ℝ) + 200 * ((Nat.sqrt N : ℝ) / q + 1) * (Nat.sqrt N + q * Real.log (2 * q)) ≤
      801 * (N : ℝ) ^ (1 - η) * Real.log (2 * N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  set M : ℝ := (Nat.sqrt N : ℝ) with hM
  set W : ℝ := (N : ℝ) ^ (1 - η) with hWdef
  set ℓ : ℝ := Real.log (2 * N) with hℓ
  have hM0 : 0 ≤ M := Nat.cast_nonneg _
  have hMsq : M ^ 2 ≤ N := by
    rw [hM]
    exact_mod_cast Nat.sqrt_le' N
  have hηpos : (1 : ℝ) ≤ (N : ℝ) ^ η := Real.one_le_rpow hN1 hη0
  have hq0 : (0 : ℝ) < q := lt_of_lt_of_le (by linarith) hq1.le
  have hW1 : 1 ≤ W := Real.one_le_rpow hN1 (by linarith)
  have hWN : W ≤ N := by
    have := Real.rpow_le_rpow_of_exponent_le hN1 (show 1 - η ≤ 1 by linarith)
    simpa [hWdef] using this
  have hsqrtW : M ≤ W := by
    have h1 : M ≤ Real.sqrt N := by
      rw [Real.le_sqrt hM0 hN0.le]
      exact hMsq
    have h2 : Real.sqrt N = (N : ℝ) ^ ((1 : ℝ) / 2) := Real.sqrt_eq_rpow _
    have h3 : (N : ℝ) ^ ((1 : ℝ) / 2) ≤ W :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    linarith
  have hℓ1 : 1 ≤ ℓ := by
    rw [hℓ]
    have he : Real.exp 1 ≤ 2 * N := by
      have := Real.exp_one_lt_d9
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (2 * N) := Real.log_le_log (Real.exp_pos 1) he
  have hlogq : Real.log (2 * q) ≤ ℓ := Real.log_le_log (by positivity) (by linarith)
  have hlogq0 : 0 ≤ Real.log (2 * q) := Real.log_nonneg (by
    have : (1 : ℝ) ≤ q := by linarith
    linarith)
  -- `M²/q ≤ W`
  have hMq : M * M / q ≤ W := by
    have hNW : (N : ℝ) / (N : ℝ) ^ η = W := by
      rw [hWdef, Real.rpow_sub hN0, Real.rpow_one]
    rw [← hNW, div_le_div_iff₀ hq0 (by positivity)]
    have : M * M ≤ N := by nlinarith
    nlinarith
  have e1 : M + 200 * (M / q + 1) * (M + q * Real.log (2 * q)) =
      M + 200 * (M * M / q + M * Real.log (2 * q) + M + q * Real.log (2 * q)) := by
    field_simp
    ring
  rw [e1]
  have t1 : M * M / q ≤ W * ℓ := hMq.trans (by nlinarith)
  have t2 : M * Real.log (2 * q) ≤ W * ℓ := mul_le_mul hsqrtW hlogq hlogq0 (by linarith)
  have t3 : M ≤ W * ℓ := hsqrtW.trans (by nlinarith)
  have t4 : (q : ℝ) * Real.log (2 * q) ≤ W * ℓ := mul_le_mul hq2 hlogq hlogq0 (by linarith)
  nlinarith

/-- **`lem:record:arcs`(iii), the weighted quadratic sum on a minor arc.** For `N ≥ 2`,
`0 ≤ η ≤ 1/2`, and a reduced fraction `b` with `N^η < q ≤ N^{1-η}`, `|α - b| ≤ q⁻²`, uniformly
in `λ`: `|∑_{m ≤ √N} (2m/N) e(α m² + λ m)| ≤ 116 N^{-η/2} (log 2N)^{1/2}`. -/
theorem minorArc_weighted_sum {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (α lam : ℝ) (b : ℚ) (hb1 : (N : ℝ) ^ η < b.den) (hb2 : (b.den : ℝ) ≤ (N : ℝ) ^ (1 - η))
    (hα : |α - b| ≤ 1 / (b.den : ℝ) ^ 2) :
    ‖∑ m ∈ Icc 1 (Nat.sqrt N), (2 * (m : ℝ) / N) • expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ≤
      116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  set M := Nat.sqrt N with hMdef
  set q := b.den with hqdef
  have hq : 1 ≤ q := b.pos
  have hc : IsCoprime b.num (q : ℤ) := b.isCoprime_num_den
  have ha : |α - (b.num : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by rwa [← Rat.cast_def]
  set B : ℝ := Real.sqrt ((M : ℝ) + 200 * ((M : ℝ) / q + 1) * (M + q * Real.log (2 * q))) with hB
  have hpart : ∀ L ≤ M, ‖∑ m ∈ range L,
      expPhase (α * ((m : ℝ) + 1) ^ 2 + lam * ((m : ℝ) + 1))‖ ≤ B := by
    intro L hL
    rw [norm_sum_range_succ_eq]
    apply Real.le_sqrt_of_sq_le
    exact weyl_even α lam b.num q hq hc ha L M hL
  have hlin := norm_linear_weighted_sum
    (fun m => expPhase (α * ((m : ℝ) + 1) ^ 2 + lam * ((m : ℝ) + 1))) M B (Real.sqrt_nonneg _)
    hpart
  rw [weighted_sum_eq, norm_smul, Real.norm_of_nonneg (by positivity)]
  have hstep : 2 / (N : ℝ) * ‖∑ m ∈ range M,
      ((m : ℝ) + 1) • expPhase (α * ((m : ℝ) + 1) ^ 2 + lam * ((m : ℝ) + 1))‖ ≤
      4 * M / N * B := by
    have := mul_le_mul_of_nonneg_left hlin (show 0 ≤ 2 / (N : ℝ) by positivity)
    calc _ ≤ 2 / (N : ℝ) * (2 * M * B) := this
      _ = _ := by ring
  refine hstep.trans ?_
  -- compare squares
  have hB2 : B ^ 2 ≤ 801 * (N : ℝ) ^ (1 - η) * Real.log (2 * N) := by
    rw [hB, Real.sq_sqrt (by
      have : 0 ≤ Real.log (2 * (q : ℝ)) := Real.log_nonneg (by
        have : (1 : ℝ) ≤ q := by exact_mod_cast hq
        linarith)
      positivity)]
    exact weyl_minor_bound hN hη0 hη q hb1 hb2
  have hM2 : ((M : ℝ) / N) ^ 2 ≤ 1 / N := by
    have hMsq : (M : ℝ) ^ 2 ≤ N := by exact_mod_cast Nat.sqrt_le' N
    rw [div_pow, div_le_div_iff₀ (by positivity) hN0]
    nlinarith
  have hℓ0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg (by linarith)
  have hpow : ((N : ℝ) ^ (-(η / 2))) ^ 2 = (N : ℝ) ^ (1 - η) / N := by
    have h1 : ((N : ℝ) ^ (-(η / 2))) ^ 2 = (N : ℝ) ^ (-η) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0.le]
      congr 1
      push_cast
      ring
    have h2 : (N : ℝ) ^ (1 - η) / N = (N : ℝ) ^ (-η) := by
      rw [Real.rpow_sub hN0, Real.rpow_one, Real.rpow_neg hN0.le]
      have : (N : ℝ) ^ η ≠ 0 := (Real.rpow_pos_of_pos hN0 η).ne'
      field_simp
    rw [h1, h2]
  have hlhs0 : 0 ≤ 4 * (M : ℝ) / N * B := by positivity
  have hrhs0 : 0 ≤ 116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)) := by positivity
  refine le_of_pow_le_pow_left₀ (n := 2) (by norm_num) hrhs0 ?_
  · rw [mul_pow, mul_pow, mul_pow, Real.sq_sqrt hℓ0, hpow]
    have e : (4 * (M : ℝ) / N) ^ 2 = 16 * ((M : ℝ) / N) ^ 2 := by ring
    rw [e]
    have hWn : 0 ≤ (N : ℝ) ^ (1 - η) := Real.rpow_nonneg hN0.le _
    calc 16 * ((M : ℝ) / N) ^ 2 * B ^ 2 ≤
          16 * (1 / N) * (801 * (N : ℝ) ^ (1 - η) * Real.log (2 * N)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hM2 (by norm_num)) hB2 (sq_nonneg _)
            (by positivity)
      _ = 12816 * ((N : ℝ) ^ (1 - η) / N) * Real.log (2 * N) := by ring
      _ ≤ (116 : ℝ) ^ 2 * ((N : ℝ) ^ (1 - η) / N) * Real.log (2 * N) := by
          have : 0 ≤ (N : ℝ) ^ (1 - η) / N * Real.log (2 * N) := by positivity
          nlinarith

/-- **Expanding `Φ` (`def:record:K20-kernels`(c) in the proof of `lem:record:arcs`(iii)).** If
`Φ(m) = ∑_i c_i e(λ_i m)` with `∑ |c_i| ≤ A`, and the twisted weighted sums are at most `W`
uniformly in the twist, then `|∑_{m=1}^{M} (2m/N) Φ(m) e(α m²)| ≤ A W`. -/
theorem character_twist_sum {ι : Type*} (s : Finset ι) (coef : ι → ℂ) (freq : ι → ℝ) {A W : ℝ}
    (hA : ∑ i ∈ s, ‖coef i‖ ≤ A) (α : ℝ) (N M : ℕ)
    (hW : ∀ lam : ℝ,
      ‖∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) • expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ≤ W) :
    ‖∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) •
        ((∑ i ∈ s, coef i * expPhase (freq i * m)) * expPhase (α * (m : ℝ) ^ 2))‖ ≤ A * W := by
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  have hswap : ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) •
      ((∑ i ∈ s, coef i * expPhase (freq i * m)) * expPhase (α * (m : ℝ) ^ 2)) =
      ∑ i ∈ s, coef i * ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) •
        expPhase (α * (m : ℝ) ^ 2 + freq i * m) := by
    simp_rw [sum_mul, smul_sum, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => sum_congr rfl fun m _ => ?_
    rw [expPhase_add, mul_smul_comm, mul_assoc, mul_comm (expPhase (freq i * m))]
  rw [hswap]
  calc _ ≤ ∑ i ∈ s, ‖coef i * ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) •
        expPhase (α * (m : ℝ) ^ 2 + freq i * m)‖ := norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ‖coef i‖ * W := by
        refine sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hW (freq i)) (norm_nonneg _)
    _ = (∑ i ∈ s, ‖coef i‖) * W := by rw [sum_mul]
    _ ≤ A * W := mul_le_mul_of_nonneg_right hA hW0

/-- **`lem:record:arcs`(iii), the model kernel on a minor arc.** If every centre `c` is at
distance more than `2N^{-1+η}` from `α` (it is the centre of a major arc, and `α` lies on none)
and the coefficients have modulus at most one, then
`|∑_c c₀(c) V_N(α - c)| ≤ #centres/(4N^η)`. -/
theorem minorArc_model_sum {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (C : Finset ℚ) (coef : ℚ → ℂ)
    (hcoef : ∀ c ∈ C, ‖coef c‖ ≤ 1) (α : ℝ)
    (hfar : ∀ c ∈ C, 2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - c)) :
    ‖∑ c ∈ C, coef c * normalizedLinearSum N (α - c)‖ ≤ C.card / (4 * (N : ℝ) ^ η) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNη : (N : ℝ) * (N : ℝ) ^ (-1 + η) = (N : ℝ) ^ η := by
    conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hterm : ∀ c ∈ C, ‖coef c * normalizedLinearSum N (α - c)‖ ≤ 1 / (4 * (N : ℝ) ^ η) := by
    intro c hc
    have hd : 0 < circleDistance (α - c) :=
      lt_of_le_of_lt (by positivity) (hfar c hc)
    rw [norm_mul]
    have h1 := normalizedLinearSum_distance N (α - c) hd
    have h2 : 1 / (2 * (N : ℝ) * circleDistance (α - c)) ≤ 1 / (4 * (N : ℝ) ^ η) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [← hNη]
      nlinarith [hfar c hc]
    calc ‖coef c‖ * ‖normalizedLinearSum N (α - c)‖ ≤ 1 * (1 / (4 * (N : ℝ) ^ η)) :=
          mul_le_mul (hcoef c hc) (h1.trans h2) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc _ ≤ ∑ c ∈ C, ‖coef c * normalizedLinearSum N (α - c)‖ := norm_sum_le _ _
    _ ≤ ∑ _c ∈ C, 1 / (4 * (N : ℝ) ^ η) := sum_le_sum hterm
    _ = _ := by rw [sum_const, nsmul_eq_mul]; ring

/-- **`lem:record:arcs`(iii) for `S`, from the minor-arc hypothesis.** Let `N ≥ 2`,
`0 ≤ η ≤ 1/2`, and let `α` lie on no major arc. If `Φ(m) = ∑_i c_i e(λ_i m)` with
`∑ |c_i| ≤ A` (`A = D'H` for the kernel of `def:record:K20-kernels`(c)), then
`|∑_{m ≤ √N} (2m/N) Φ(m) e(α m²)| ≤ 116 A N^{-η/2} (log 2N)^{1/2}`. -/
theorem minorArc_S_bound {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (α : ℝ) (hminor : ∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
      2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b))
    {ι : Type*} (s : Finset ι) (coef : ι → ℂ) (freq : ι → ℝ) {A : ℝ}
    (hA : ∑ i ∈ s, ‖coef i‖ ≤ A) :
    ‖∑ m ∈ Icc 1 (Nat.sqrt N), (2 * (m : ℝ) / N) •
        ((∑ i ∈ s, coef i * expPhase (freq i * m)) * expPhase (α * (m : ℝ) ^ 2))‖ ≤
      A * (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N))) := by
  obtain ⟨b, hb1, hb2, hb3⟩ := minorArc_approx (by omega) (by linarith) α hminor
  exact character_twist_sum s coef freq hA α N (Nat.sqrt N)
    (fun lam => minorArc_weighted_sum hN hη0 hη α lam b hb1 hb2 hb3)

/-- **`lem:record:arcs`(iii) for `S₀`, from the minor-arc hypothesis.** If `α` lies on no major
arc and every centre has denominator at most `N^η` (by (K1), `DH < N^η`: the first sentence of
(ii)), then `|∑_c c₀(c) V_N(α - c)| ≤ #centres/(4N^η)` for coefficients of modulus at most one. -/
theorem minorArc_S0_bound {N : ℕ} (hN : 1 ≤ N) {η : ℝ} (α : ℝ)
    (hminor : ∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
      2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b))
    (C : Finset ℚ) (coef : ℚ → ℂ) (hcoef : ∀ c ∈ C, ‖coef c‖ ≤ 1)
    (hden : ∀ c ∈ C, (c.den : ℝ) ≤ (N : ℝ) ^ η) :
    ‖∑ c ∈ C, coef c * normalizedLinearSum N (α - c)‖ ≤ C.card / (4 * (N : ℝ) ^ η) :=
  minorArc_model_sum hN C coef hcoef α (fun c hc => hminor c (hden c hc))

/-! ## (iv) Major arcs, the model kernel -/

/-- **`lem:record:arcs`(iv), the model kernel.** In the setting of (ii), with centres `C` of
denominators at most `L` that are pairwise distinct in `ℚ/ℤ` from `b` (`q = b.den`) and
coefficients of modulus at most one,
`S₀(α) = c₀(b) V_N(y) + R₀` with `|R₀| ≤ #C · q L / N` (`c₀(b) = 0` if `b` is not a centre).
With `#C ≤ DH²` and `L = DH` this is the paper's `|R₀| ≤ q D² H³ / N`. -/
theorem majorArc_model_sum {N : ℕ} (hN : 1 ≤ N) {η L : ℝ} (hL : 0 < L) (C : Finset ℚ)
    (coef : ℚ → ℂ) (hcoef : ∀ c ∈ C, ‖coef c‖ ≤ 1) (hden : ∀ c ∈ C, (c.den : ℝ) ≤ L)
    (b : ℚ) (y : ℝ) (hy : |y| ≤ 2 * (N : ℝ) ^ (-1 + η))
    (hK2 : 4 * (b.den : ℝ) * L * (N : ℝ) ^ (-1 + η) ≤ 1)
    (hdistinct : ∀ c ∈ C, c ≠ b → ¬ ∃ k : ℤ, b - c = k) :
    ‖∑ c ∈ C, coef c * normalizedLinearSum N ((b : ℝ) + y - c) -
        (if b ∈ C then coef b else 0) * normalizedLinearSum N y‖ ≤
      C.card * ((b.den : ℝ) * L / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hbpos : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  have hother : ∀ c ∈ C, c ≠ b →
      ‖coef c * normalizedLinearSum N ((b : ℝ) + y - c)‖ ≤ (b.den : ℝ) * L / N := by
    intro c hc hcb
    have hs := centre_separation b y hy hL hK2 c (hden c hc) (hdistinct c hc hcb)
    have hd : 0 < circleDistance ((b : ℝ) + y - c) := lt_of_lt_of_le (by positivity) hs
    rw [norm_mul]
    have h1 := normalizedLinearSum_distance N ((b : ℝ) + y - c) hd
    have h2 : 1 / (2 * (N : ℝ) * circleDistance ((b : ℝ) + y - c)) ≤ (b.den : ℝ) * L / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (b.den : ℝ) * L)).mp hs
      nlinarith
    calc ‖coef c‖ * ‖normalizedLinearSum N ((b : ℝ) + y - c)‖ ≤ 1 * ((b.den : ℝ) * L / N) :=
          mul_le_mul (hcoef c hc) (h1.trans h2) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  have hR0 : 0 ≤ (b.den : ℝ) * L / N := by positivity
  by_cases hbC : b ∈ C
  · simp only [hbC, ↓reduceIte]
    rw [← sum_erase_add C _ hbC]
    have hself : (b : ℝ) + y - b = y := by ring
    rw [hself, add_sub_cancel_right]
    calc _ ≤ ∑ c ∈ C.erase b, ‖coef c * normalizedLinearSum N ((b : ℝ) + y - c)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _c ∈ C.erase b, (b.den : ℝ) * L / N := by
          refine sum_le_sum fun c hc => ?_
          exact hother c (mem_of_mem_erase hc) (ne_of_mem_erase hc)
      _ = ((C.card : ℝ) - 1) * ((b.den : ℝ) * L / N) := by
          rw [sum_const, nsmul_eq_mul, card_erase_of_mem hbC]
          rw [Nat.cast_sub (card_pos.mpr ⟨b, hbC⟩)]
          simp
      _ ≤ _ := by nlinarith
  · simp only [hbC, ↓reduceIte, zero_mul, sub_zero]
    calc _ ≤ ∑ c ∈ C, ‖coef c * normalizedLinearSum N ((b : ℝ) + y - c)‖ := norm_sum_le _ _
      _ ≤ ∑ _c ∈ C, (b.den : ℝ) * L / N := by
          refine sum_le_sum fun c hc => ?_
          exact hother c hc (fun h => hbC (h ▸ hc))
      _ = _ := by rw [sum_const, nsmul_eq_mul]

/-! ## (iv) Major arcs, the actual kernel -/

/-- The mean over a period is shift invariant: `periodicMean (a ∘ succ) T = periodicMean a T`. -/
theorem periodicMean_succ (a : ℕ → ℂ) (T : ℕ) (hp : Function.Periodic a T) :
    periodicMean (fun m => a (m + 1)) T = periodicMean a T := by
  unfold periodicMean
  congr 1
  have h := sum_range_succ' a T
  have h2 := sum_range_succ a T
  have hT : a T = a 0 := by simpa using hp 0
  rw [hT] at h2
  linear_combination h2 - h

/-- `∑_{m=1}^{M} f_y(m) a(m) = ∑_{m<M} squareWeight N y m · a(m+1)` with
`f_y(m) = (2m/N) e(y m²)`. -/
theorem weighted_periodic_eq (a : ℕ → ℂ) (N M : ℕ) (y : ℝ) :
    ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) • (expPhase (y * (m : ℝ) ^ 2) * a m) =
      ∑ m ∈ range M, squareWeight N y m * a (m + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
  refine sum_congr (by simp) fun m _ => ?_
  unfold squareWeight
  rw [smul_mul_assoc, add_comm 1 m]
  push_cast
  ring_nf

/-- **`lem:record:arcs`(iv), the actual kernel, with upstream's constants.** Let
`S = ∑_u ε_u ∑_{m ≤ √N} f_y(m) a_u(m)` with `|ε_u| ≤ 1`, each `a_u` periodic of period `T_u`
with `|a_u| ≤ B` and mean `A_u` (`a_u = ρ_D w_u e(α₀ m²)`, `ε_u = (-1)^{ω(u)}`, `B = D'`), and
`c = ∑_u ε_u A_u`. Then `S = c V_N(y) + R₁` with
`|R₁| ≤ ∑_u (2T_u + 1) B (4 + 8π|y|N)/√N`. The paper's proof (Stieltjes integration by parts)
gives `|R₁| ≤ 18 q D² H² (1 + |y|N)/√N + 2π|y|H`; the bound here (from WP-K's ported
`periodic_square_main`) has the same exponents after `T_u ≤ D'uq`, `∑_{u ≤ H} u ≤ H²`,
`q ≤ N^η`, `|y| ≤ 2N^{-1+η}`, with larger constants and no separate `|y|H` term; the lemma's
statement only asks for a constant `C`. -/
theorem majorArc_actual_sum {U : Type*} (s : Finset U) (ε : U → ℂ) (hε : ∀ u ∈ s, ‖ε u‖ ≤ 1)
    (a : U → ℕ → ℂ) (T : U → ℕ) (hT : ∀ u ∈ s, 0 < T u)
    (hp : ∀ u ∈ s, Function.Periodic (a u) (T u)) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ u ∈ s, ∀ m, ‖a u m‖ ≤ B) {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    ‖∑ u ∈ s, ε u * ∑ m ∈ Icc 1 (Nat.sqrt N),
          (2 * (m : ℝ) / N) • (expPhase (y * (m : ℝ) ^ 2) * a u m) -
        (∑ u ∈ s, ε u * periodicMean (a u) (T u)) * normalizedLinearSum N y‖ ≤
      ∑ u ∈ s, (2 * (T u : ℝ) + 1) * B * ((4 + 8 * Real.pi * |y| * N) / Real.sqrt N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  set M := Nat.sqrt N with hM
  have hM1 : 1 ≤ M := by rw [hM]; exact Nat.le_sqrt.mpr (by omega)
  have hlo : M ^ 2 ≤ N := Nat.sqrt_le' N
  have hhi : N < (M + 1) ^ 2 := Nat.lt_succ_sqrt' N
  have hMR : (M : ℝ) ≤ Real.sqrt N := by
    rw [Real.le_sqrt (Nat.cast_nonneg _) hN0.le]
    exact_mod_cast hlo
  have hM2 : (M : ℝ) ^ 2 ≤ N := by exact_mod_cast hlo
  have hsq : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hfac : (4 + 8 * Real.pi * |y| * (M : ℝ) ^ 2) * M / N ≤
      (4 + 8 * Real.pi * |y| * N) / Real.sqrt N := by
    have h1 : (4 + 8 * Real.pi * |y| * (M : ℝ) ^ 2) ≤ 4 + 8 * Real.pi * |y| * N := by
      have : 0 ≤ 8 * Real.pi * |y| := by positivity
      nlinarith
    have h2 : (M : ℝ) / N ≤ 1 / Real.sqrt N := by
      rw [div_le_div_iff₀ hN0 hsq, one_mul]
      calc (M : ℝ) * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
            mul_le_mul_of_nonneg_right hMR hsq.le
        _ = N := Real.mul_self_sqrt hN0.le
    calc (4 + 8 * Real.pi * |y| * (M : ℝ) ^ 2) * M / N =
          (4 + 8 * Real.pi * |y| * (M : ℝ) ^ 2) * ((M : ℝ) / N) := by ring
      _ ≤ (4 + 8 * Real.pi * |y| * N) * (1 / Real.sqrt N) :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = _ := by ring
  have hsplit : ∑ u ∈ s, ε u * ∑ m ∈ Icc 1 M,
        (2 * (m : ℝ) / N) • (expPhase (y * (m : ℝ) ^ 2) * a u m) -
      (∑ u ∈ s, ε u * periodicMean (a u) (T u)) * normalizedLinearSum N y =
      ∑ u ∈ s, ε u * ((∑ m ∈ range M, squareWeight N y m * a u (m + 1)) -
        periodicMean (fun m => a u (m + 1)) (T u) * normalizedLinearSum N y) := by
    rw [sum_mul, ← sum_sub_distrib]
    refine sum_congr rfl fun u hu => ?_
    rw [weighted_periodic_eq, periodicMean_succ _ _ (hp u hu)]
    ring
  rw [hsplit]
  refine (norm_sum_le _ _).trans (sum_le_sum fun u hu => ?_)
  rw [norm_mul]
  have hpu : Function.Periodic (fun m => a u (m + 1)) (T u) := fun m => by
    simp only
    rw [show m + T u + 1 = m + 1 + T u by ring]
    exact hp u hu (m + 1)
  have hmain := periodic_square_main (fun m => a u (m + 1)) (T u) (hT u hu) hpu B hB
    (fun m => ha u hu (m + 1)) M N hM1 hlo hhi y
  calc ‖ε u‖ * ‖(∑ m ∈ range M, squareWeight N y m * a u (m + 1)) -
        periodicMean (fun m => a u (m + 1)) (T u) * normalizedLinearSum N y‖ ≤
        1 * ((2 * T u + 1) * B * ((4 + 8 * Real.pi * |y| * (M : ℝ) ^ 2) * M / N)) :=
        mul_le_mul (hε u hu) hmain (norm_nonneg _) (by norm_num)
    _ ≤ (2 * (T u : ℝ) + 1) * B * ((4 + 8 * Real.pi * |y| * N) / Real.sqrt N) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hfac (by positivity)

/-! ## The exponents -/

/-- **The arc exponents at `(β, κ, η) = (1/20, 1/20, 17/100)`** (`lem:record:arcs`, last
sentence; `CERTIFICATE-CHECK record:analytic:arc-exponents`): `κ + β/2 - η/2 = -1/100`,
`κ + β - η = -7/100`, `η + 2κ + 3β/2 - 1 = -131/200`, `2η + 2κ + β - 1/2 = -1/100`,
`η + β/2 - 1 = -161/200`, all below `-1/120`. -/
theorem arc_exponents_twentieth :
    let β : ℚ := 1 / 20
    let κ : ℚ := 1 / 20
    let η : ℚ := 17 / 100
    κ + β / 2 - η / 2 = -1 / 100 ∧ κ + β - η = -7 / 100 ∧
      η + 2 * κ + 3 * β / 2 - 1 = -131 / 200 ∧ 2 * η + 2 * κ + β - 1 / 2 = -1 / 100 ∧
      η + β / 2 - 1 = -161 / 200 ∧
      (-1 / 100 : ℚ) < -1 / 120 ∧ (-7 / 100 : ℚ) < -1 / 120 ∧ (-131 / 200 : ℚ) < -1 / 120 ∧
      (-161 / 200 : ℚ) < -1 / 120 := by
  norm_num

/-- For an admissible triple (`def:kernel-conditions`) the four arc exponents are the left sides
of (E1)–(E4), hence below `-β/6`, and `η + β/2 - 1` is smaller than the third. -/
theorem arc_exponents_admissible {β κ η : ℝ} (h : KernelAdmissible β κ η) :
    κ + β / 2 - η / 2 < -(β / 6) ∧ κ + β - η < -(β / 6) ∧
      η + 2 * κ + 3 * β / 2 - 1 < -(β / 6) ∧ 2 * η + 2 * κ + β - 1 / 2 < -(β / 6) ∧
      η + β / 2 - 1 < η + 2 * κ + 3 * β / 2 - 1 := by
  obtain ⟨hβ, hκ, -, e1, e2, e3, e4, -, -, -⟩ := h
  exact ⟨e1, e2, e3, e4, by linarith⟩

/-! ## The tree's model kernel `S₀` (`lem:record:K20-centres`) in (ii)–(iv)

WP-K's `Sarkozy.Kernel.general_kernel_rate` compares the actual kernel with the model
`S₀(α) = ∑_{(j, ξ)} e(jr/D) g(ξ) V_N(α - j/D - ξ)` over `CentreIndex H D` (`0 ≤ j < D`,
`ξ ∈ Ξ_{H,D}`), with centres `centre H D x = j/D + ξ` and coefficients `centreCoeff H D r x`
(the paper's `ξ - j/D` and `g(ξ) e(-jr/D)`, the same set). The abstract statements above apply
to it. -/

/-- (iii) for a finite family of centres indexed by any finite type. -/
theorem minorArc_model_sum_index {N : ℕ} (hN : 1 ≤ N) {η : ℝ} {I : Type*} [Fintype I]
    (c : I → ℚ) (coef : I → ℂ) (hcoef : ∀ x, ‖coef x‖ ≤ 1) (α : ℝ)
    (hfar : ∀ x, 2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - c x)) :
    ‖∑ x, coef x * normalizedLinearSum N (α - c x)‖ ≤ Fintype.card I / (4 * (N : ℝ) ^ η) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hNη : (N : ℝ) * (N : ℝ) ^ (-1 + η) = (N : ℝ) ^ η := by
    conv_lhs => arg 1; rw [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hN0]
    congr 1
    ring
  have hterm : ∀ x, ‖coef x * normalizedLinearSum N (α - c x)‖ ≤ 1 / (4 * (N : ℝ) ^ η) := by
    intro x
    have hd : 0 < circleDistance (α - c x) := lt_of_le_of_lt (by positivity) (hfar x)
    rw [norm_mul]
    have h1 := normalizedLinearSum_distance N (α - c x) hd
    have h2 : 1 / (2 * (N : ℝ) * circleDistance (α - c x)) ≤ 1 / (4 * (N : ℝ) ^ η) := by
      apply one_div_le_one_div_of_le (by positivity)
      rw [← hNη]
      nlinarith [hfar x]
    calc ‖coef x‖ * ‖normalizedLinearSum N (α - c x)‖ ≤ 1 * (1 / (4 * (N : ℝ) ^ η)) :=
          mul_le_mul (hcoef x) (h1.trans h2) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc _ ≤ ∑ x, ‖coef x * normalizedLinearSum N (α - c x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x : I, 1 / (4 * (N : ℝ) ^ η) := sum_le_sum fun x _ => hterm x
    _ = _ := by rw [sum_const, card_univ, nsmul_eq_mul]; ring

/-- (iv) for a finite family of centres indexed by any finite type: the centres in the class of
`b` in `ℚ/ℤ` give `(∑ their coefficients) V_N(y)`, the others are separated by (ii). -/
theorem majorArc_model_sum_index {N : ℕ} (hN : 1 ≤ N) {η L : ℝ} (hL : 0 < L) {I : Type*}
    [Fintype I] (c : I → ℚ) (coef : I → ℂ) (hcoef : ∀ x, ‖coef x‖ ≤ 1)
    (hden : ∀ x, ((c x).den : ℝ) ≤ L) (b : ℚ) (y : ℝ) (hy : |y| ≤ 2 * (N : ℝ) ^ (-1 + η))
    (hK2 : 4 * (b.den : ℝ) * L * (N : ℝ) ^ (-1 + η) ≤ 1) :
    ‖∑ x, coef x * normalizedLinearSum N ((b : ℝ) + y - c x) -
        (∑ x ∈ univ.filter (fun x => Int.fract (c x) = Int.fract b), coef x) *
          normalizedLinearSum N y‖ ≤
      Fintype.card I * ((b.den : ℝ) * L / N) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hbpos : (0 : ℝ) < b.den := Nat.cast_pos.mpr b.pos
  rw [← sum_filter_add_sum_filter_not univ (fun x => Int.fract (c x) = Int.fract b)]
  have hfib : ∑ x ∈ univ.filter (fun x => Int.fract (c x) = Int.fract b),
      coef x * normalizedLinearSum N ((b : ℝ) + y - c x) =
      (∑ x ∈ univ.filter (fun x => Int.fract (c x) = Int.fract b), coef x) *
        normalizedLinearSum N y := by
    rw [sum_mul]
    refine sum_congr rfl fun x hx => ?_
    obtain ⟨k, hk⟩ := Int.fract_eq_fract.mp (mem_filter.mp hx).2.symm
    have hk' : ((b - c x : ℚ) : ℝ) = ((k : ℚ) : ℝ) := congrArg (fun t : ℚ => (t : ℝ)) hk
    push_cast at hk'
    have he : (b : ℝ) + y - c x = y + (k : ℤ) := by linarith
    rw [he, normalizedLinearSum_add_int]
  rw [hfib, add_sub_cancel_left]
  have hother : ∀ x ∈ univ.filter (fun x => ¬ Int.fract (c x) = Int.fract b),
      ‖coef x * normalizedLinearSum N ((b : ℝ) + y - c x)‖ ≤ (b.den : ℝ) * L / N := by
    intro x hx
    have hnP := (mem_filter.mp hx).2
    have hbc : ¬ ∃ k : ℤ, b - c x = k := fun ⟨k, hk⟩ =>
      hnP (Int.fract_eq_fract.mpr ⟨k, hk⟩).symm
    have hs := centre_separation b y hy hL hK2 (c x) (hden x) hbc
    have hd : 0 < circleDistance ((b : ℝ) + y - c x) := lt_of_lt_of_le (by positivity) hs
    rw [norm_mul]
    have h1 := normalizedLinearSum_distance N ((b : ℝ) + y - c x) hd
    have h2 : 1 / (2 * (N : ℝ) * circleDistance ((b : ℝ) + y - c x)) ≤ (b.den : ℝ) * L / N := by
      rw [div_le_div_iff₀ (by positivity) hN0]
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (b.den : ℝ) * L)).mp hs
      nlinarith
    calc ‖coef x‖ * ‖normalizedLinearSum N ((b : ℝ) + y - c x)‖ ≤
          1 * ((b.den : ℝ) * L / N) :=
          mul_le_mul (hcoef x) (h1.trans h2) (norm_nonneg _) (by norm_num)
      _ = _ := one_mul _
  calc _ ≤ ∑ x ∈ univ.filter (fun x => ¬ Int.fract (c x) = Int.fract b),
        ‖coef x * normalizedLinearSum N ((b : ℝ) + y - c x)‖ := norm_sum_le _ _
    _ ≤ ∑ _x ∈ univ.filter (fun x => ¬ Int.fract (c x) = Int.fract b), (b.den : ℝ) * L / N :=
        sum_le_sum hother
    _ = ((univ.filter (fun x => ¬ Int.fract (c x) = Int.fract b)).card : ℝ) *
        ((b.den : ℝ) * L / N) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card I * ((b.den : ℝ) * L / N) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast card_le_univ _) (by positivity)

/-- The number of centres: `#CentreIndex H D ≤ D H²` (`lem:record:K20-centres`). -/
theorem card_centreIndex_le {H : ℝ} (hH : 0 ≤ H) (D : ℕ) :
    (Fintype.card (CentreIndex H D) : ℝ) ≤ D * H ^ 2 := by
  rw [Fintype.card_coe, card_product, card_range]
  have hsub : frequencySet H D ⊆ boundedRationals ⌊H⌋₊ := by
    unfold frequencySet
    exact filter_subset _ _
  have h1 : (frequencySet H D).card ≤ ⌊H⌋₊ ^ 2 :=
    (card_le_card hsub).trans (boundedRationals_card _)
  have h1' : ((frequencySet H D).card : ℝ) ≤ (⌊H⌋₊ : ℝ) ^ 2 := by exact_mod_cast h1
  have h3 : (⌊H⌋₊ : ℝ) ^ 2 ≤ H ^ 2 := pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.floor_le hH) 2
  have hD0 : (0 : ℝ) ≤ D := Nat.cast_nonneg D
  push_cast
  nlinarith

/-- **`lem:record:arcs`(ii), first sentence, for the tree's model kernel**: every centre `j/D + ξ`
has denominator at most `⌈DH⌉`, so if `⌈DH⌉ ≤ N^η` (the form of (K1) used) it is the centre of a
major arc. -/
theorem centre_major {N : ℕ} {η H : ℝ} (hH : 0 ≤ H) {D : ℕ} (hD : 0 < D)
    (hK1 : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ η) (x : CentreIndex H D) :
    ((centre H D x).den : ℝ) ≤ (N : ℝ) ^ η :=
  (Nat.cast_le.mpr (centre_den_le D H hH hD x)).trans hK1

/-- **The centres are distinct in `ℚ/ℤ`** (`lem:record:K20-centres`): at most one centre lies in
each class, so the fibre sum of `majorArc_S0_kernel` is the coefficient `c₀(b)` of the paper. -/
theorem centre_fiber_subsingleton {H : ℝ} (hH : 0 ≤ H) {D : ℕ} (hD : 0 < D) (b : ℚ)
    (x x' : CentreIndex H D) (hx : Int.fract (centre H D x) = Int.fract b)
    (hx' : Int.fract (centre H D x') = Int.fract b) : x = x' := by
  have hm := mem_product.mp x.2
  have hm' := mem_product.mp x'.2
  obtain ⟨h1, h2⟩ := centre_injective D hD H hH x.1.1 x'.1.1 (mem_range.mp hm.1)
    (mem_range.mp hm'.1) x.1.2 x'.1.2 hm.2 hm'.2 (hx.trans hx'.symm)
  exact Subtype.ext (Prod.ext h1 h2)

/-- **`lem:record:arcs`(iii) for the tree's model kernel**: on a minor arc, with `⌈DH⌉ ≤ N^η`,
`|S₀(α)| = |∑_{(j,ξ)} e(jr/D) g(ξ) V_N(α - j/D - ξ)| ≤ D H²/(4 N^η)`. -/
theorem minorArc_S0_kernel {N : ℕ} (hN : 1 ≤ N) {η H : ℝ} (hH : 0 ≤ H) {D : ℕ} (hD : 0 < D)
    (hK1 : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ η) (r : ℤ) (α : ℝ)
    (hminor : ∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
      2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b)) :
    ‖∑ x : CentreIndex H D, centreCoeff H D r x * normalizedLinearSum N (α - centre H D x)‖ ≤
      D * H ^ 2 / (4 * (N : ℝ) ^ η) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  refine (minorArc_model_sum_index hN (centre H D) (centreCoeff H D r) (norm_centreCoeff H D r)
    α (fun x => hminor _ (centre_major hH hD hK1 x))).trans ?_
  have hpos : 0 < 4 * (N : ℝ) ^ η := by positivity
  exact div_le_div_of_nonneg_right (card_centreIndex_le hH D) hpos.le

/-- **`lem:record:arcs`(iv) for the tree's model kernel**: for `α = b + y` with `q = b.den`,
`|y| ≤ 2N^{-1+η}` and `4 q ⌈DH⌉ N^{-1+η} ≤ 1` (the form of (K2) used),
`S₀(α) = c₀(b) V_N(y) + R₀` with `c₀(b)` the coefficient of the centre in the class of `b`
(`0` if there is none; at most one, `centre_fiber_subsingleton`) and
`|R₀| ≤ D H² · q ⌈DH⌉/N`, the paper's `q D² H³/N` up to `⌈DH⌉` for `DH`. -/
theorem majorArc_S0_kernel {N : ℕ} (hN : 1 ≤ N) {η H : ℝ} (hH : 0 < H) {D : ℕ} (hD : 0 < D)
    (r : ℤ) (b : ℚ) (y : ℝ) (hy : |y| ≤ 2 * (N : ℝ) ^ (-1 + η))
    (hK2 : 4 * (b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ) * (N : ℝ) ^ (-1 + η) ≤ 1) :
    ‖∑ x : CentreIndex H D,
          centreCoeff H D r x * normalizedLinearSum N ((b : ℝ) + y - centre H D x) -
        (∑ x ∈ univ.filter (fun x => Int.fract (centre H D x) = Int.fract b),
          centreCoeff H D r x) * normalizedLinearSum N y‖ ≤
      D * H ^ 2 * ((b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ) / N) := by
  have hDH : (0 : ℝ) < D * H := mul_pos (by exact_mod_cast hD) hH
  have hL : (0 : ℝ) < (⌈(D : ℝ) * H⌉₊ : ℝ) := by exact_mod_cast Nat.ceil_pos.mpr hDH
  refine (majorArc_model_sum_index hN hL (centre H D) (centreCoeff H D r)
    (norm_centreCoeff H D r) (fun x => by exact_mod_cast centre_den_le D H hH.le hD x) b y hy
    hK2).trans ?_
  exact mul_le_mul_of_nonneg_right (card_centreIndex_le hH.le D) (by positivity)

/-! ## (ii)–(iv) for the model kernel at an admissible triple, for `N` large -/

theorem rpow_half_sq {N : ℕ} (β : ℝ) : ((N : ℝ) ^ (β / 2)) ^ 2 = (N : ℝ) ^ β := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg N)]
  congr 1
  push_cast
  ring

/-- **`lem:record:arcs`(ii)–(iv) for the tree's model kernel, in the paper's form**: at a triple
admissible in the sense of `def:kernel-conditions` and for constants `C_D, C_H ≥ 1`, there are
`C` and `N₀` such that for `N ≥ N₀`, `0 < D ≤ C_D N^κ`, `1 ≤ H ≤ C_H N^{β/2}` and every `r`:
* (ii) every centre `j/D + ξ` has denominator at most `N^η`, i.e. is the centre of a major arc;
* (iii) on every minor arc, `|S₀(α)| ≤ C N^{κ+β-η}`;
* (iv) for every major-arc centre `b` (`b.den ≤ N^η`) and `|y| ≤ 2N^{-1+η}`,
  `S₀(b + y) = c₀(b) V_N(y) + R₀` with `|R₀| ≤ C N^{η+2κ+3β/2-1}`, `c₀(b)` the coefficient of the
  centre in the class of `b` (`0` if none).
The paper's `(K1)` and `(K2)` give the thresholds; `C = 2 C_D² C_H³`. -/
theorem arcs_model_kernel {β κ η : ℝ} (hadm : KernelAdmissible β κ η) {CD CH : ℝ}
    (hCD : 1 ≤ CD) (hCH : 1 ≤ CH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ D : ℕ, 0 < D →
      (D : ℝ) ≤ CD * (N : ℝ) ^ κ → ∀ H : ℝ, 1 ≤ H → H ≤ CH * (N : ℝ) ^ (β / 2) → ∀ r : ℤ,
        (∀ x : CentreIndex H D, ((centre H D x).den : ℝ) ≤ (N : ℝ) ^ η) ∧
        (∀ α : ℝ, (∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
            2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b)) →
          ‖∑ x : CentreIndex H D, centreCoeff H D r x * normalizedLinearSum N (α - centre H D x)‖ ≤
            C * (N : ℝ) ^ (κ + β - η)) ∧
        (∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η → ∀ y : ℝ, |y| ≤ 2 * (N : ℝ) ^ (-1 + η) →
          ‖∑ x : CentreIndex H D,
                centreCoeff H D r x * normalizedLinearSum N ((b : ℝ) + y - centre H D x) -
              (∑ x ∈ univ.filter (fun x => Int.fract (centre H D x) = Int.fract b),
                centreCoeff H D r x) * normalizedLinearSum N y‖ ≤
            C * (N : ℝ) ^ (η + 2 * κ + 3 * β / 2 - 1)) := by
  obtain ⟨hβ, hκ, hη, -, -, -, -, -, k1, k2⟩ := hadm
  obtain ⟨N₁, hN₁⟩ := eventually_mul_rpow_le_one (2 * CD * CH) (κ + β / 2 - η) (by linarith)
  obtain ⟨N₂, hN₂⟩ := eventually_mul_rpow_le_one (8 * CD * CH) (2 * η + κ + β / 2 - 1)
    (by linarith)
  refine ⟨2 * CD ^ 2 * CH ^ 3, by positivity, max (max N₁ N₂) 1, ?_⟩
  intro N hN D hD hDle H hH1 hHle r
  have hN1 : 1 ≤ N := le_of_max_le_right hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hpos : ∀ a : ℝ, 0 < (N : ℝ) ^ a := fun a => Real.rpow_pos_of_pos hN0 a
  have hge1 : ∀ a : ℝ, 0 ≤ a → 1 ≤ (N : ℝ) ^ a := fun a ha => Real.one_le_rpow hNR1 ha
  -- `⌈DH⌉ ≤ 2 C_D C_H N^{κ+β/2}`
  have hDH : (D : ℝ) * H ≤ CD * CH * (N : ℝ) ^ (κ + β / 2) := by
    calc (D : ℝ) * H ≤ (CD * (N : ℝ) ^ κ) * (CH * (N : ℝ) ^ (β / 2)) :=
          mul_le_mul hDle hHle (by linarith) (by positivity)
      _ = CD * CH * (N : ℝ) ^ (κ + β / 2) := by rw [Real.rpow_add hN0]; ring
  have hDH1 : 1 ≤ (D : ℝ) * H := one_le_mul_of_one_le_of_one_le hD1 hH1
  have hceil : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ 2 * CD * CH * (N : ℝ) ^ (κ + β / 2) := by
    have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ D * H by linarith)
    linarith
  -- (K1): `⌈DH⌉ ≤ N^η`
  have hK1 : (⌈(D : ℝ) * H⌉₊ : ℝ) ≤ (N : ℝ) ^ η := by
    have h := hN₁ N (le_trans (le_max_left _ _) (le_of_max_le_left hN))
    have he : 2 * CD * CH * (N : ℝ) ^ (κ + β / 2) =
        (2 * CD * CH * (N : ℝ) ^ (κ + β / 2 - η)) * (N : ℝ) ^ η := by
      rw [mul_assoc (2 * CD * CH), ← Real.rpow_add hN0]
      ring_nf
    have : 2 * CD * CH * (N : ℝ) ^ (κ + β / 2) ≤ (N : ℝ) ^ η := by
      rw [he]
      nlinarith [hpos η]
    linarith
  refine ⟨fun x => centre_major (by linarith) hD hK1 x, fun α hminor => ?_, fun b hb y hy => ?_⟩
  · -- (iii)
    refine (minorArc_S0_kernel hN1 (by linarith) hD hK1 r α hminor).trans ?_
    have hH2 : H ^ 2 ≤ CH ^ 2 * (N : ℝ) ^ β := by
      have := pow_le_pow_left₀ (by linarith) hHle 2
      rwa [mul_pow, rpow_half_sq] at this
    have hnum : (D : ℝ) * H ^ 2 ≤ CD * CH ^ 2 * ((N : ℝ) ^ κ * (N : ℝ) ^ β) := by
      calc (D : ℝ) * H ^ 2 ≤ (CD * (N : ℝ) ^ κ) * (CH ^ 2 * (N : ℝ) ^ β) :=
            mul_le_mul hDle hH2 (by positivity) (by positivity)
        _ = _ := by ring
    have hexp : (N : ℝ) ^ κ * (N : ℝ) ^ β / (N : ℝ) ^ η = (N : ℝ) ^ (κ + β - η) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_sub hN0]
    have hη4 : 0 < 4 * (N : ℝ) ^ η := by positivity
    calc (D : ℝ) * H ^ 2 / (4 * (N : ℝ) ^ η) ≤
          CD * CH ^ 2 * ((N : ℝ) ^ κ * (N : ℝ) ^ β) / (4 * (N : ℝ) ^ η) :=
          div_le_div_of_nonneg_right hnum hη4.le
      _ = CD * CH ^ 2 / 4 * ((N : ℝ) ^ κ * (N : ℝ) ^ β / (N : ℝ) ^ η) := by
          field_simp
      _ = CD * CH ^ 2 / 4 * (N : ℝ) ^ (κ + β - η) := by rw [hexp]
      _ ≤ 2 * CD ^ 2 * CH ^ 3 * (N : ℝ) ^ (κ + β - η) := by
          apply mul_le_mul_of_nonneg_right _ (hpos _).le
          have h1 : CD ≤ CD ^ 2 := by nlinarith
          have h2 : CH ^ 2 ≤ CH ^ 3 := by nlinarith
          nlinarith
  · -- (iv)
    have hK2 : 4 * (b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ) * (N : ℝ) ^ (-1 + η) ≤ 1 := by
      have h := hN₂ N (le_trans (le_max_right _ _) (le_of_max_le_left hN))
      have he : 8 * CD * CH * (N : ℝ) ^ (2 * η + κ + β / 2 - 1) =
          4 * (N : ℝ) ^ η * (2 * CD * CH * (N : ℝ) ^ (κ + β / 2)) * (N : ℝ) ^ (-1 + η) := by
        have : (N : ℝ) ^ (2 * η + κ + β / 2 - 1) =
            (N : ℝ) ^ η * (N : ℝ) ^ (κ + β / 2) * (N : ℝ) ^ (-1 + η) := by
          rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
          ring_nf
        rw [this]
        ring
      have hb0 : (0 : ℝ) ≤ b.den := Nat.cast_nonneg _
      calc 4 * (b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ) * (N : ℝ) ^ (-1 + η) ≤
            4 * (N : ℝ) ^ η * (2 * CD * CH * (N : ℝ) ^ (κ + β / 2)) * (N : ℝ) ^ (-1 + η) := by
            apply mul_le_mul_of_nonneg_right _ (hpos _).le
            apply mul_le_mul (by linarith) hceil (Nat.cast_nonneg _) (by positivity)
        _ = 8 * CD * CH * (N : ℝ) ^ (2 * η + κ + β / 2 - 1) := he.symm
        _ ≤ 1 := h
    refine (majorArc_S0_kernel hN1 (by linarith) hD r b y hy hK2).trans ?_
    have hH2 : H ^ 2 ≤ CH ^ 2 * (N : ℝ) ^ β := by
      have := pow_le_pow_left₀ (by linarith) hHle 2
      rwa [mul_pow, rpow_half_sq] at this
    have hb0 : (0 : ℝ) ≤ b.den := Nat.cast_nonneg _
    have hprod : (D : ℝ) * H ^ 2 * ((b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ)) ≤
        (CD * (N : ℝ) ^ κ * (CH ^ 2 * (N : ℝ) ^ β)) *
          ((N : ℝ) ^ η * (2 * CD * CH * (N : ℝ) ^ (κ + β / 2))) := by
      apply mul_le_mul _ _ (by positivity) (by positivity)
      · exact mul_le_mul hDle hH2 (by positivity) (by positivity)
      · exact mul_le_mul hb hceil (Nat.cast_nonneg _) (by positivity)
    have hexp : (N : ℝ) ^ κ * (N : ℝ) ^ β * ((N : ℝ) ^ η * (N : ℝ) ^ (κ + β / 2)) / N =
        (N : ℝ) ^ (η + 2 * κ + 3 * β / 2 - 1) := by
      rw [← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
        ← Real.rpow_sub_one hN0.ne']
      ring_nf
    calc (D : ℝ) * H ^ 2 * ((b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ) / N) =
          (D : ℝ) * H ^ 2 * ((b.den : ℝ) * (⌈(D : ℝ) * H⌉₊ : ℝ)) / N := by ring
      _ ≤ (CD * (N : ℝ) ^ κ * (CH ^ 2 * (N : ℝ) ^ β)) *
            ((N : ℝ) ^ η * (2 * CD * CH * (N : ℝ) ^ (κ + β / 2))) / N :=
          div_le_div_of_nonneg_right hprod hN0.le
      _ = 2 * CD ^ 2 * CH ^ 3 *
            ((N : ℝ) ^ κ * (N : ℝ) ^ β * ((N : ℝ) ^ η * (N : ℝ) ^ (κ + β / 2)) / N) := by ring
      _ = 2 * CD ^ 2 * CH ^ 3 * (N : ℝ) ^ (η + 2 * κ + 3 * β / 2 - 1) := by rw [hexp]

end Sarkozy.Misc

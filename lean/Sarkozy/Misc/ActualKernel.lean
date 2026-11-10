module

public import Sarkozy.Misc.Arcs

@[expose] public section

/-!
# `lem:record:arcs`(iii) for the tree's actual kernel

`paper/sections/C_kernel.tex`, `lem:record:arcs`(iii): on a minor arc,
`|S(α)| ≤ 116 D'H N^{-η/2} (log 2N)^{1/2}`. The proof expands `Φ` "as a finite sum of additive
characters in `m` with coefficients of total absolute value at most `D'H`"
(`def:record:K20-kernels`(c)) and applies the twisted Weyl bound to each character.

The actual kernel of the tree is WP-K's
`S(α) = finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) ⌊√N⌋ N α
= ∑_T (-1)^{|T|} ∑_{m ≤ √N} (2m/N) e(α m²) w_T(m)`, one term for each sieve set `T` with
`∏_{p ∈ T} p ≤ H`, where `w_T(m) = ρ_D(m) ∏_{p ∈ T} w_p(m)` (`classWeight`,
`primeSieveWeight`). This file proves:

* `sum_expPhase_div`: orthogonality, `∑_{k<q} e(kn/q) = q [q ∣ n]`;
* `HasCharExp v A`: `v(n) = ∑_i c_i e(λ_i n)` with `∑ |c_i| ≤ A`; closed under products
  (`HasCharExp.mul`, `HasCharExp.prod`);
* `classWeight_hasCharExp`: `ρ_D` has total `D'` (`def:record:K20-kernels`(a): `ρ_D(m) =
  ∑_{j mod D'} e(j(m - m₀)/D')`); `primeSieveWeight_hasCharExp`: `w_p` has total `1`
  (`def:record:K20-kernels`(b)); hence `termWeight_hasCharExp`: `w_T` has total `D'`;
* `weighted_charExp_sum`: a weighted quadratic sum against a character expansion of total `A` is
  at most `A` times the uniform bound for the twisted sums;
* **`minorArc_S_kernel`**: on a minor arc, `|S(α)| ≤ H D' · 116 N^{-η/2} (log 2N)^{1/2}`, using
  that there are at most `H` sieve sets (`boundedSieveSets_card`). This is the paper's bound with
  the paper's constant; `minorArc_S_kernel_rpow` is the paper's
  `|S(α)| ≤ 116 C_D C_H N^{κ+β/2-η/2} (log 2N)^{1/2}` for `D ≤ C_D N^κ`, `H ≤ C_H N^{β/2}`.

* **`majorArc_S_kernel`**: (iv) for this kernel, `S(b + y) = c(b) V_N(y) + R₁` with
  `|R₁| ≤ ∑_T (2 q t_T + 1) D' (4 + 8π|y|N)/√N` (`Misc.majorArc_actual_sum` at
  `a_T(m) = w_T(m) e(bm²)`), from the periodicity of `w_T` (`t_T = termPeriod ≤ D'H`,
  `termPeriod_le`) and `|w_T| ≤ D'` (`norm_termWeight_le`); **`majorArc_S_kernel_rpow`**: the
  paper's form, `|R₁| ≤ 3(4 + 16π) C_D² C_H² N^{2η+2κ+β-1/2}` for a major-arc centre `b` and
  `|y| ≤ 2N^{-1+η}`. (WP-K's ported `Kernel.finite_square_kernel_major` is the same statement with
  upstream's parametrization.)
-/

namespace Sarkozy.Misc

open Finset Sarkozy.Kernel

/-! ## Additive characters -/

/-- **Orthogonality**: `∑_{k<q} e(k n/q) = q` if `q ∣ n`, and `0` otherwise. -/
theorem sum_expPhase_div (q : ℕ) (hq : 0 < q) (n : ℤ) :
    ∑ k ∈ range q, expPhase ((k : ℝ) * ((n : ℝ) / q)) = if (q : ℤ) ∣ n then (q : ℂ) else 0 := by
  have hqR : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  by_cases h : (q : ℤ) ∣ n
  · rw [ite_eq_left h]
    obtain ⟨m, hm⟩ := h
    have hk : ∀ k : ℕ, expPhase ((k : ℝ) * ((n : ℝ) / q)) = 1 := fun k => by
      have he : (k : ℝ) * ((n : ℝ) / q) = (((k : ℤ) * m : ℤ) : ℝ) := by
        rw [hm]
        push_cast
        field_simp
      rw [he, expPhase_int]
    simp only [hk, sum_const, card_range, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right h]
    have hcd : 0 < circleDistance ((n : ℝ) / q) :=
      lt_of_lt_of_le (by positivity) (rational_circleDistance_lower n q hq h)
    have hne : expPhase ((n : ℝ) / q) ≠ 1 := by
      intro he
      have h4 := expPhase_sub_one_lower ((n : ℝ) / q)
      rw [he, sub_self, norm_zero] at h4
      linarith
    simp_rw [expPhase_nat_mul]
    rw [geom_sum_eq hne, ← expPhase_nat_mul]
    have he : (q : ℝ) * ((n : ℝ) / q) = ((n : ℤ) : ℝ) := by field_simp
    rw [he, expPhase_int, sub_self, zero_div]

/-- `v` is a finite sum of additive characters, `v(n) = ∑_i c_i e(λ_i n)`, with coefficients of
total absolute value `∑ |c_i| ≤ A` (the form of `def:record:K20-kernels`(c)). -/
def HasCharExp (v : ℕ → ℂ) (A : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (lam : ι → ℝ),
    (∀ n : ℕ, v n = ∑ i, c i * expPhase (lam i * n)) ∧ ∑ i, ‖c i‖ ≤ A

theorem HasCharExp.nonneg {v : ℕ → ℂ} {A : ℝ} (h : HasCharExp v A) : 0 ≤ A := by
  obtain ⟨ι, _, c, lam, -, hc⟩ := h
  exact le_trans (sum_nonneg fun i _ => norm_nonneg _) hc

theorem hasCharExp_one : HasCharExp (fun _ => 1) 1 :=
  ⟨Unit, inferInstance, fun _ => 1, fun _ => 0, fun n => by simp, by simp⟩

theorem HasCharExp.mul {v w : ℕ → ℂ} {A B : ℝ} (hv : HasCharExp v A) (hw : HasCharExp w B) :
    HasCharExp (fun n => v n * w n) (A * B) := by
  have hA := hv.nonneg
  obtain ⟨ι, _, c, lam, hv1, hv2⟩ := hv
  obtain ⟨κ, _, d, mu, hw1, hw2⟩ := hw
  refine ⟨ι × κ, inferInstance, fun z => c z.1 * d z.2, fun z => lam z.1 + mu z.2,
    fun n => ?_, ?_⟩
  · show v n * w n = ∑ z : ι × κ, c z.1 * d z.2 * expPhase ((lam z.1 + mu z.2) * n)
    rw [hv1, hw1, sum_mul_sum, ← univ_product_univ, sum_product]
    refine sum_congr rfl fun i _ => sum_congr rfl fun k _ => ?_
    rw [add_mul, expPhase_add]
    ring
  · calc ∑ z : ι × κ, ‖c z.1 * d z.2‖ = (∑ i, ‖c i‖) * ∑ k, ‖d k‖ := by
          rw [sum_mul_sum, ← univ_product_univ, sum_product]
          simp only [norm_mul]
      _ ≤ A * B := mul_le_mul hv2 hw2 (sum_nonneg fun k _ => norm_nonneg _) hA

theorem HasCharExp.prod {J : Type*} [DecidableEq J] (T : Finset J) (v : J → ℕ → ℂ) (A : J → ℝ)
    (h : ∀ j ∈ T, HasCharExp (v j) (A j)) :
    HasCharExp (fun n => ∏ j ∈ T, v j n) (∏ j ∈ T, A j) := by
  induction T using Finset.induction_on with
  | empty => simpa using hasCharExp_one
  | @insert a T ha ih =>
    have h' := (h a (mem_insert_self a T)).mul (ih fun j hj => h j (mem_insert_of_mem hj))
    simp only [prod_insert ha]
    exact h'

/-- **The root-class weight** `ρ_D(m) = D' [m ≡ m₀ (D')] = ∑_{j mod D'} e(j(m - m₀)/D')` has a
character expansion of total `D'` (`def:record:K20-kernels`(a)). -/
theorem classWeight_hasCharExp (D' m₀ : ℕ) (hD : 0 < D') : HasCharExp (classWeight D' m₀) D' := by
  refine ⟨Fin D', inferInstance, fun j => expPhase (-((j : ℝ) * ((m₀ : ℝ) / D'))),
    fun j => (j : ℝ) / D', fun n => ?_, ?_⟩
  · have hs := sum_expPhase_div D' hD ((n : ℤ) - m₀)
    rw [← Fin.sum_univ_eq_sum_range] at hs
    have hiff : n ≡ m₀ [MOD D'] ↔ (D' : ℤ) ∣ ((n : ℤ) - m₀) := by
      rw [Nat.ModEq.comm, Nat.modEq_iff_dvd]
    unfold classWeight
    by_cases hc : n ≡ m₀ [MOD D']
    · rw [ite_eq_left hc]
      rw [ite_eq_left (hiff.mp hc)] at hs
      rw [← hs]
      refine sum_congr rfl fun j _ => ?_
      rw [← expPhase_add]
      congr 1
      push_cast
      ring
    · rw [ite_eq_right hc]
      rw [ite_eq_right (fun h => hc (hiff.mpr h))] at hs
      rw [← hs]
      refine sum_congr rfl fun j _ => ?_
      rw [← expPhase_add]
      congr 1
      push_cast
      ring
  · simp only [norm_expPhase, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact le_rfl

/-- **The prime sieve weight** `w_p(m) = (p [p ∣ m] - 1)/(p - 1) = ∑_{k=1}^{p-1} e(km/p)/(p-1)`
has a character expansion of total `1` (`def:record:K20-kernels`(b)). -/
theorem primeSieveWeight_hasCharExp (p : ℕ) [Fact p.Prime] :
    HasCharExp (fun n => (primeSieveWeight p (n : ZMod p) : ℂ)) 1 := by
  have hp := (Fact.out : p.Prime)
  obtain ⟨k, hk⟩ : ∃ k, p = k + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  have hk1 : 1 ≤ k := by have := hp.two_le; omega
  have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  have hpR : (p : ℝ) = (k : ℝ) + 1 := by rw [hk]; push_cast; ring
  refine ⟨Fin k, inferInstance, fun _ => (k : ℂ)⁻¹, fun j => ((j : ℝ) + 1) / p, fun n => ?_, ?_⟩
  · have hs := sum_expPhase_div (k + 1) (by omega) (n : ℤ)
    rw [sum_range_succ'] at hs
    simp only [Nat.cast_zero, zero_mul, expPhase_zero] at hs
    have hterm : ∀ j : ℕ, expPhase (((j + 1 : ℕ) : ℝ) * (((n : ℤ) : ℝ) / ((k + 1 : ℕ) : ℝ))) =
        expPhase (((j : ℝ) + 1) / p * n) := fun j => by
      congr 1
      rw [hpR]
      push_cast
      ring
    simp only [hterm] at hs
    rw [← Fin.sum_univ_eq_sum_range (fun j => expPhase (((j : ℝ) + 1) / p * n)) k] at hs
    show ((primeSieveWeight p (n : ZMod p) : ℝ) : ℂ) =
      ∑ i : Fin k, (k : ℂ)⁻¹ * expPhase (((i : ℝ) + 1) / p * n)
    rw [← mul_sum]
    have hdvd : (n : ZMod p) = 0 ↔ ((k + 1 : ℕ) : ℤ) ∣ (n : ℤ) := by
      rw [ZMod.natCast_eq_zero_iff, hk]
      exact Int.natCast_dvd_natCast.symm
    unfold primeSieveWeight
    by_cases h : (n : ZMod p) = 0
    · rw [ite_eq_left (hdvd.mp h)] at hs
      have hsum : ∑ j : Fin k, expPhase (((j : ℝ) + 1) / p * n) = (k : ℂ) := by
        push_cast at hs
        linear_combination hs
      rw [hsum, ite_eq_left h]
      rw [inv_mul_cancel₀ hkC]
      have : ((p : ℝ) * 1 - 1) / ((p : ℝ) - 1) = 1 := by
        have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
        rw [hpR, show ((k : ℝ) + 1) * 1 - 1 = k by ring, show (k : ℝ) + 1 - 1 = k by ring,
          div_self hk0]
      rw [this]
      simp
    · rw [ite_eq_right (fun h' => h (hdvd.mpr h'))] at hs
      have hsum : ∑ j : Fin k, expPhase (((j : ℝ) + 1) / p * n) = -1 := by
        linear_combination hs
      rw [hsum, ite_eq_right h]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
      have : ((p : ℝ) * 0 - 1) / ((p : ℝ) - 1) = -(k : ℝ)⁻¹ := by
        rw [hpR, show ((k : ℝ) + 1) * 0 - 1 = -1 by ring, show (k : ℝ) + 1 - 1 = k by ring,
          neg_div, one_div]
      rw [this]
      push_cast
      ring
  · show ∑ _i : Fin k, ‖(k : ℂ)⁻¹‖ ≤ 1
    simp only [norm_inv, Complex.norm_natCast, sum_const, card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    rw [mul_inv_cancel₀ hk0]

/-- **The weight of a kernel term** `w_T(m) = ρ_D(m) ∏_{p ∈ T} w_p(m)` has a character expansion
of total `D'` (`def:record:K20-kernels`(c), for one sieve set `T`). -/
theorem termWeight_hasCharExp (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)
    (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) :
    HasCharExp (termWeight N D r ρ H T) ρ.period := by
  have h1 := classWeight_hasCharExp ρ.period ρ.base ρ.period_pos
  have h2 := HasCharExp.prod T.val
    (fun i n => (primeSieveWeight (i : ℕ) (n : ZMod (i : ℕ)) : ℂ)) (fun _ => 1)
    (fun i _ => primeSieveWeight_hasCharExp (i : ℕ))
  have h := h1.mul h2
  simp only [prod_const_one, mul_one] at h
  have he : termWeight N D r ρ H T = fun n => classWeight ρ.period ρ.base n *
      ∏ i ∈ T.val, (primeSieveWeight (i : ℕ) (n : ZMod (i : ℕ)) : ℂ) := by
    funext n
    simp [termWeight, rootTermWeight, sieveTermWeight, actualRootWeight, actualSieveWeight]
  rw [he]
  exact h

/-- **A weighted quadratic sum against a character expansion**: if `v` has a character expansion
of total `A` and every twisted sum `∑_{m=1}^{M} (2m/N) e(α m² + λ m)` is at most `W`, then
`|∑_{m=1}^{M} (2m/N) e(α m²) v(m)| ≤ A W`. -/
theorem weighted_charExp_sum {v : ℕ → ℂ} {A W : ℝ} (hv : HasCharExp v A) (α : ℝ) (N M : ℕ)
    (hW : ∀ lam : ℝ,
      ‖∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) • expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ≤ W) :
    ‖∑ m ∈ range M, squareWeight N α m * v (m + 1)‖ ≤ A * W := by
  have hW0 : 0 ≤ W := (norm_nonneg _).trans (hW 0)
  obtain ⟨ι, _, c, lam, hv1, hv2⟩ := hv
  have hsw : ∑ m ∈ range M, squareWeight N α m * v (m + 1) =
      ∑ i, c i * ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) • expPhase (α * (m : ℝ) ^ 2 + lam i * m) := by
    simp_rw [hv1, mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun i _ => ?_
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    refine sum_congr (by simp) fun m _ => ?_
    unfold squareWeight
    simp only [Complex.real_smul]
    rw [expPhase_add]
    push_cast
    ring_nf
  rw [hsw]
  calc _ ≤ ∑ i, ‖c i * ∑ m ∈ Icc 1 M, (2 * (m : ℝ) / N) •
        expPhase (α * (m : ℝ) ^ 2 + lam i * m)‖ := norm_sum_le _ _
    _ ≤ ∑ i, ‖c i‖ * W := by
        refine sum_le_sum fun i _ => ?_
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hW (lam i)) (norm_nonneg _)
    _ = (∑ i, ‖c i‖) * W := by rw [sum_mul]
    _ ≤ A * W := mul_le_mul_of_nonneg_right hv2 hW0

/-- **`lem:record:arcs`(iii) for the tree's actual kernel**: for `N ≥ 2`, `0 ≤ η ≤ 1/2` and `α`
on no major arc, `|S(α)| ≤ H D' · 116 N^{-η/2} (log 2N)^{1/2}`, where
`S = finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) ⌊√N⌋ N` is WP-K's actual-square
transform and `D' = ρ.period`; this is the paper's `|S(α)| ≤ 116 D'H N^{-η/2} (log 2N)^{1/2}`. -/
theorem minorArc_S_kernel {N : ℕ} (hN : 2 ≤ N) {η : ℝ} (hη0 : 0 ≤ η) (hη : η ≤ 1 / 2)
    (D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) {H : ℝ} (hH : 0 ≤ H) (α : ℝ)
    (hminor : ∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
      2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b)) :
    ‖finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N α‖ ≤
      H * ρ.period * (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N))) := by
  obtain ⟨b, hb1, hb2, hb3⟩ := minorArc_approx (by omega) (by linarith) α hminor
  have hW : ∀ lam : ℝ, ‖∑ m ∈ Icc 1 (Nat.sqrt N), (2 * (m : ℝ) / N) •
      expPhase (α * (m : ℝ) ^ 2 + lam * m)‖ ≤
      116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)) :=
    fun lam => minorArc_weighted_sum hN hη0 hη α lam b hb1 hb2 hb3
  have hW0 : 0 ≤ 116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)) :=
    (norm_nonneg _).trans (hW 0)
  unfold finiteSquareKernel
  calc _ ≤ ∑ T, ‖termSign N D H T * ∑ m ∈ range N.sqrt,
        squareWeight N α m * termWeight N D r ρ H T (m + 1)‖ := norm_sum_le _ _
    _ ≤ ∑ _T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
        (ρ.period : ℝ) * (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N))) := by
        refine sum_le_sum fun T _ => ?_
        rw [norm_mul]
        have hs : ‖termSign N D H T‖ = 1 := by
          simp [termSign, sieveTermSign]
        rw [hs, one_mul]
        exact weighted_charExp_sum (termWeight_hasCharExp N D r ρ H T) α N _ hW
    _ = (Fintype.card (boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) : ℝ) *
        ((ρ.period : ℝ) * (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)))) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ H * ((ρ.period : ℝ) * (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)))) :=
        mul_le_mul_of_nonneg_right
          (boundedSieveSets_card (fun i : OddFamily N D => (i : ℕ)) Subtype.val_injective H hH)
          (by positivity)
    _ = _ := by ring

/-- **`lem:record:arcs`(iii) for the tree's actual kernel, in the paper's form**: with
`0 < D ≤ C_D N^κ` (so `D' ≤ D`) and `0 ≤ H ≤ C_H N^{β/2}`, on a minor arc
`|S(α)| ≤ 116 C_D C_H N^{κ+β/2-η/2} (log 2N)^{1/2}`. -/
theorem minorArc_S_kernel_rpow {N : ℕ} (hN : 2 ≤ N) {η β κ CD CH : ℝ} (hη0 : 0 ≤ η)
    (hη : η ≤ 1 / 2) (D : ℕ) (hD : 0 < D) (hDle : (D : ℝ) ≤ CD * (N : ℝ) ^ κ) (r : ℤ)
    (ρ : RootClassDatum D r) {H : ℝ} (hH : 0 ≤ H) (hHle : H ≤ CH * (N : ℝ) ^ (β / 2)) (α : ℝ)
    (hminor : ∀ b : ℚ, (b.den : ℝ) ≤ (N : ℝ) ^ η →
      2 * (N : ℝ) ^ (-1 + η) < circleDistance (α - b)) :
    ‖finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N α‖ ≤
      116 * CD * CH * (N : ℝ) ^ (κ + β / 2 - η / 2) * Real.sqrt (Real.log (2 * N)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  refine (minorArc_S_kernel hN hη0 hη D r ρ hH α hminor).trans ?_
  have hper : (ρ.period : ℝ) ≤ CD * (N : ℝ) ^ κ :=
    (Nat.cast_le.mpr (Nat.le_of_dvd hD ρ.period_dvd)).trans hDle
  have hprod : H * ρ.period ≤ (CH * (N : ℝ) ^ (β / 2)) * (CD * (N : ℝ) ^ κ) :=
    mul_le_mul hHle hper (Nat.cast_nonneg _) (by linarith)
  have hsq : 0 ≤ 116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N)) := by positivity
  have hexp : (N : ℝ) ^ (β / 2) * (N : ℝ) ^ κ * (N : ℝ) ^ (-(η / 2)) =
      (N : ℝ) ^ (κ + β / 2 - η / 2) := by
    rw [← Real.rpow_add hN0, ← Real.rpow_add hN0]
    ring_nf
  calc H * ρ.period * (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N))) ≤
        (CH * (N : ℝ) ^ (β / 2)) * (CD * (N : ℝ) ^ κ) *
          (116 * (N : ℝ) ^ (-(η / 2)) * Real.sqrt (Real.log (2 * N))) :=
        mul_le_mul_of_nonneg_right hprod hsq
    _ = 116 * CD * CH * ((N : ℝ) ^ (β / 2) * (N : ℝ) ^ κ * (N : ℝ) ^ (-(η / 2))) *
          Real.sqrt (Real.log (2 * N)) := by ring
    _ = 116 * CD * CH * (N : ℝ) ^ (κ + β / 2 - η / 2) * Real.sqrt (Real.log (2 * N)) := by
        rw [hexp]

/-! ## (iv) for the tree's actual kernel -/

/-- The weight of a kernel term, unfolded: `w_T(m) = ρ_D(m) ∏_{p ∈ T} w_p(m)`. -/
theorem termWeight_eq (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)
    (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) (m : ℕ) :
    termWeight N D r ρ H T m = classWeight ρ.period ρ.base m *
      ∏ i ∈ T.val, (primeSieveWeight (i : ℕ) (m : ZMod (i : ℕ)) : ℂ) := by
  simp [termWeight, rootTermWeight, sieveTermWeight, actualRootWeight, actualSieveWeight]

/-- `|w_T| ≤ D'`. -/
theorem norm_termWeight_le (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)
    (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) (m : ℕ) :
    ‖termWeight N D r ρ H T m‖ ≤ ρ.period := by
  rw [termWeight_eq, norm_mul, norm_prod]
  have h2 : ∏ i ∈ T.val, ‖(primeSieveWeight (i : ℕ) (m : ZMod (i : ℕ)) : ℂ)‖ ≤ 1 :=
    prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => by
      rw [Complex.norm_real, Real.norm_eq_abs]
      exact primeSieveWeight_abs_le _)
  calc _ ≤ (ρ.period : ℝ) * 1 :=
        mul_le_mul (norm_classWeight _ _ m) h2 (by positivity) (Nat.cast_nonneg _)
    _ = _ := mul_one _

/-- The period of a kernel term is at most `D' H`. -/
theorem termPeriod_le (N D : ℕ) (r : ℤ) (ρ : RootClassDatum D r) (H : ℝ)
    (T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) :
    (termPeriod N D r ρ H T : ℝ) ≤ ρ.period * H := by
  have hT : ((∏ i ∈ T.val, (i : ℕ) : ℕ) : ℝ) ≤ H := (mem_filter.mp T.2).2
  unfold termPeriod sieveTermPeriod
  rw [prod_empty, one_mul]
  push_cast
  push_cast at hT
  exact mul_le_mul_of_nonneg_left hT (Nat.cast_nonneg _)

/-- **`lem:record:arcs`(iv) for the tree's actual kernel**: for every `b ∈ ℚ` and `y`,
`S(b + y) = c(b) V_N(y) + R₁` with `c(b) = ∑_T (-1)^{|T|} A_T`, `A_T` the mean of
`w_T(m) e(b m²)` over the period `q t_T` (`q = b.den`, `t_T = termPeriod`), and
`|R₁| ≤ ∑_T (2 q t_T + 1) D' (4 + 8π|y|N)/√N` (`Misc.majorArc_actual_sum` at `a_T(m) =
w_T(m) e(bm²)`, `ε_T = (-1)^{|T|}`). -/
theorem majorArc_S_kernel {N : ℕ} (hN : 1 ≤ N) (D : ℕ) (r : ℤ) (ρ : RootClassDatum D r)
    {H : ℝ} (b : ℚ) (y : ℝ) :
    ‖finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N ((b : ℝ) + y) -
        (∑ T ∈ univ, termSign N D H T *
          periodicMean (fun m => termWeight N D r ρ H T m * expPhase ((b : ℝ) * (m : ℝ) ^ 2))
            (b.den * termPeriod N D r ρ H T)) * normalizedLinearSum N y‖ ≤
      ∑ T ∈ (univ : Finset (boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H)),
        (2 * ((b.den * termPeriod N D r ρ H T : ℕ) : ℝ) + 1) * ρ.period *
          ((4 + 8 * Real.pi * |y| * N) / Real.sqrt N) := by
  have key := majorArc_actual_sum univ (termSign N D H)
    (fun T _ => by simp [termSign, sieveTermSign])
    (fun T m => termWeight N D r ρ H T m * expPhase ((b : ℝ) * (m : ℝ) ^ 2))
    (fun T => b.den * termPeriod N D r ρ H T)
    (fun T _ => Nat.mul_pos b.pos (Nat.mul_pos ρ.period_pos (sieveTermPeriod_pos _ ∅ T.val)))
    (fun T _ => by
      have hw : Function.Periodic (termWeight N D r ρ H T) (termPeriod N D r ρ H T) :=
        rootTermWeight_periodic N D ρ.period ρ.base T.val
      have he : Function.Periodic (fun m : ℕ => expPhase ((b : ℝ) * (m : ℝ) ^ 2)) b.den :=
        expPhase_rat_sq_periodic b
      have h1 := hw.nat_mul b.den
      have h2 := he.nat_mul (termPeriod N D r ρ H T)
      simp only [Nat.cast_id] at h1 h2
      rw [mul_comm] at h2
      exact h1.mul h2)
    (Nat.cast_nonneg ρ.period)
    (fun T _ m => by
      rw [norm_mul, norm_expPhase, mul_one]
      exact norm_termWeight_le N D r ρ H T m) hN y
  have hS : finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N ((b : ℝ) + y) =
      ∑ T ∈ univ, termSign N D H T * ∑ m ∈ Icc 1 N.sqrt, (2 * (m : ℝ) / N) •
        (expPhase (y * (m : ℝ) ^ 2) *
          (termWeight N D r ρ H T m * expPhase ((b : ℝ) * (m : ℝ) ^ 2))) := by
    unfold finiteSquareKernel
    refine sum_congr rfl fun T _ => ?_
    congr 1
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    refine sum_congr (by simp) fun m _ => ?_
    unfold squareWeight
    simp only [Complex.real_smul]
    rw [show ((b : ℝ) + y) * ((m : ℝ) + 1) ^ 2 =
      (b : ℝ) * ((m : ℝ) + 1) ^ 2 + y * ((m : ℝ) + 1) ^ 2 by ring, expPhase_add]
    push_cast
    ring_nf
  rw [hS]
  exact key

/-- **`lem:record:arcs`(iv) for the tree's actual kernel, in the paper's form**: for
`0 < D ≤ C_D N^κ`, `1 ≤ H ≤ C_H N^{β/2}`, a major-arc centre `b` (`b.den ≤ N^η`, `0 ≤ η`) and
`|y| ≤ 2N^{-1+η}`: `|S(b + y) - c(b) V_N(y)| ≤ 3(4 + 16π) C_D² C_H² N^{2η+2κ+β-1/2}`, the paper's
exponent (its `|R₁| ≤ C(N^{2η+2κ+β-1/2} + N^{η+β/2-1})`; the second term is not needed here). -/
theorem majorArc_S_kernel_rpow {N : ℕ} (hN : 1 ≤ N) {η β κ CD CH : ℝ} (hη0 : 0 ≤ η)
    (D : ℕ) (hD : 0 < D) (hDle : (D : ℝ) ≤ CD * (N : ℝ) ^ κ) (r : ℤ) (ρ : RootClassDatum D r)
    {H : ℝ} (hH1 : 1 ≤ H) (hHle : H ≤ CH * (N : ℝ) ^ (β / 2)) (b : ℚ)
    (hb : (b.den : ℝ) ≤ (N : ℝ) ^ η) (y : ℝ) (hy : |y| ≤ 2 * (N : ℝ) ^ (-1 + η)) :
    ‖finiteSquareKernel (termSign N D H) (termWeight N D r ρ H) N.sqrt N ((b : ℝ) + y) -
        (∑ T ∈ univ, termSign N D H T *
          periodicMean (fun m => termWeight N D r ρ H T m * expPhase ((b : ℝ) * (m : ℝ) ^ 2))
            (b.den * termPeriod N D r ρ H T)) * normalizedLinearSum N y‖ ≤
      3 * (4 + 16 * Real.pi) * CD ^ 2 * CH ^ 2 * (N : ℝ) ^ (2 * η + 2 * κ + β - 1 / 2) := by
  refine (majorArc_S_kernel hN D r ρ b y).trans ?_
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1R : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq1 : (1 : ℝ) ≤ b.den := by exact_mod_cast b.pos
  have hD'1 : (1 : ℝ) ≤ ρ.period := by exact_mod_cast ρ.period_pos
  have hD'le : (ρ.period : ℝ) ≤ CD * (N : ℝ) ^ κ :=
    (Nat.cast_le.mpr (Nat.le_of_dvd hD ρ.period_dvd)).trans hDle
  have hNη1 : 1 ≤ (N : ℝ) ^ η := Real.one_le_rpow hN1R hη0
  have hsq0 : 0 < Real.sqrt N := Real.sqrt_pos.mpr hN0
  have hpi := Real.pi_pos
  -- the factor of `y`
  have hyN : 4 + 8 * Real.pi * |y| * N ≤ (4 + 16 * Real.pi) * (N : ℝ) ^ η := by
    have h1 : |y| * N ≤ 2 * (N : ℝ) ^ η := by
      calc |y| * N ≤ 2 * (N : ℝ) ^ (-1 + η) * N := mul_le_mul_of_nonneg_right hy hN0.le
        _ = 2 * (N : ℝ) ^ η := by
            rw [mul_assoc, ← Real.rpow_add_one hN0.ne']
            ring_nf
    nlinarith
  -- each term
  have hterm : ∀ T : boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H,
      (2 * ((b.den * termPeriod N D r ρ H T : ℕ) : ℝ) + 1) * ρ.period *
          ((4 + 8 * Real.pi * |y| * N) / Real.sqrt N) ≤
        (3 * (b.den : ℝ) * ρ.period * H) * ρ.period *
          ((4 + 16 * Real.pi) * (N : ℝ) ^ η / Real.sqrt N) := by
    intro T
    have ht := termPeriod_le N D r ρ H T
    have h1 : 2 * ((b.den * termPeriod N D r ρ H T : ℕ) : ℝ) + 1 ≤
        3 * (b.den : ℝ) * ρ.period * H := by
      push_cast
      have h2 : (b.den : ℝ) * termPeriod N D r ρ H T ≤ b.den * (ρ.period * H) :=
        mul_le_mul_of_nonneg_left ht (by linarith)
      have h3 : 1 ≤ (b.den : ℝ) * ρ.period * H := by
        have := mul_le_mul hq1 hD'1 zero_le_one (by linarith)
        nlinarith
      nlinarith
    apply mul_le_mul (mul_le_mul_of_nonneg_right h1 (by linarith))
      (div_le_div_of_nonneg_right hyN hsq0.le) (by positivity) (by positivity)
  have hcard := boundedSieveSets_card (fun i : OddFamily N D => (i : ℕ)) Subtype.val_injective H
    (by linarith)
  have hκ2 : ((ρ.period : ℝ)) ^ 2 ≤ CD ^ 2 * (N : ℝ) ^ (2 * κ) := by
    have := pow_le_pow_left₀ (by linarith) hD'le 2
    rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ κ), ← Real.rpow_mul hN0.le] at this
    calc _ ≤ _ := this
      _ = CD ^ 2 * (N : ℝ) ^ (2 * κ) := by norm_num [mul_comm κ 2]
  have hβ2 : H ^ 2 ≤ CH ^ 2 * (N : ℝ) ^ β := by
    have := pow_le_pow_left₀ (by linarith) hHle 2
    rwa [mul_pow, rpow_half_sq] at this
  have hexp : (N : ℝ) ^ η * (N : ℝ) ^ (2 * κ) * (N : ℝ) ^ β * (N : ℝ) ^ η / Real.sqrt N =
      (N : ℝ) ^ (2 * η + 2 * κ + β - 1 / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hN0, ← Real.rpow_add hN0, ← Real.rpow_add hN0,
      ← Real.rpow_sub hN0]
    ring_nf
  calc ∑ T ∈ (univ : Finset (boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H)),
        (2 * ((b.den * termPeriod N D r ρ H T : ℕ) : ℝ) + 1) * ρ.period *
          ((4 + 8 * Real.pi * |y| * N) / Real.sqrt N) ≤
        ∑ _T ∈ (univ : Finset (boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H)),
          (3 * (b.den : ℝ) * ρ.period * H) * ρ.period *
            ((4 + 16 * Real.pi) * (N : ℝ) ^ η / Real.sqrt N) :=
        sum_le_sum fun T _ => hterm T
    _ = (Fintype.card (boundedSieveSets (fun i : OddFamily N D => (i : ℕ)) H) : ℝ) *
          ((3 * (b.den : ℝ) * ρ.period * H) * ρ.period *
            ((4 + 16 * Real.pi) * (N : ℝ) ^ η / Real.sqrt N)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ H * ((3 * (b.den : ℝ) * ρ.period * H) * ρ.period *
            ((4 + 16 * Real.pi) * (N : ℝ) ^ η / Real.sqrt N)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 3 * (4 + 16 * Real.pi) * ((b.den : ℝ) * (ρ.period : ℝ) ^ 2 * H ^ 2) *
          ((N : ℝ) ^ η / Real.sqrt N) := by ring
    _ ≤ 3 * (4 + 16 * Real.pi) * ((N : ℝ) ^ η * (CD ^ 2 * (N : ℝ) ^ (2 * κ)) *
          (CH ^ 2 * (N : ℝ) ^ β)) * ((N : ℝ) ^ η / Real.sqrt N) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul (mul_le_mul hb hκ2 (by positivity) (by positivity)) hβ2
          (by positivity) (by positivity)
    _ = 3 * (4 + 16 * Real.pi) * CD ^ 2 * CH ^ 2 *
          ((N : ℝ) ^ η * (N : ℝ) ^ (2 * κ) * (N : ℝ) ^ β * (N : ℝ) ^ η / Real.sqrt N) := by
        ring
    _ = _ := by rw [hexp]

/-- Non-vacuity: root-class data exist (WP-K's `rootClassDatum_of_strict`), e.g. for `D = 8`,
`r = 1`, so the hypotheses of the bounds above are satisfiable. -/
example : Nonempty (RootClassDatum 8 1) := by
  have h := rootClassDatum_of_strict 1 odd_one 1
    ⟨Int.ModEq.refl 1, fun ℓ hℓ hd => absurd hd hℓ.not_dvd_one⟩
  simpa using h

end Sarkozy.Misc

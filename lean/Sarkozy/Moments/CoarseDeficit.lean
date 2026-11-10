module

public import Sarkozy.Moments.PowerGaps
public import Sarkozy.Moments.TypedMixture

/-!
# The coarse norm-deficit cost of the typed-mixture lemma

`lem:density:typed-mixture` (`paper/sections/30_density_moment_upgrade.tex`) charges a
component of exponent `v ∈ (R, d]` by `C_v(Q) ≤ (2d/(κv)) Q^(d/R - d/v)`, where
`Q = |X|` and `κ = s/R` (`eq:density:typed-mixture-coarse`). This module proves the
one-coordinate estimate behind it with the same power of `Q`:

`‖f‖_v^d - 1 ≤ K Q^(d/R - d/v) (1 - ‖f‖_s^d)` whenever `‖f‖_R = 1`,

with `K` depending only on `s, R, v, d`. Our constant `K` is larger than the paper's
`2d/(κv)`: below a fixed threshold we use the curvature comparison
`Sarkozy.powerGap_le_curvature` instead of the paper's monotone-ratio argument. Only
the power of `Q` matters in the application, where the cost is multiplied by masses
`O(p^(-3))`. The estimate is the `hscalar` input of
`Sarkozy.mixedLpBound_typed_mixture`, which this module then specializes.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

/-- The explicit constant of the coarse comparison: the curvature constant at the
threshold `T = max 1 ((2/κ)^(1/(1-κ)))`, or `2/κ` beyond it. -/
noncomputable def coarseGapConstant (κ ℓ : ℝ) : ℝ :=
  max (ℓ * (ℓ - 1) / (κ * (1 - κ)) * (max 1 ((2 / κ) ^ (1 / (1 - κ)))) ^ (ℓ - κ)) (2 / κ)

theorem coarseGapConstant_pos {κ ℓ : ℝ} (hκ : 0 < κ) : 0 < coarseGapConstant κ ℓ :=
  lt_max_of_lt_right (by positivity)

/-- The convex power deficit is controlled by the concave one with the power
`Q^(ℓ-1)` of the alphabet bound. -/
theorem powerGap_le_coarse {κ ℓ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1) (hℓ : 1 < ℓ)
    {Q t : ℝ} (hQ : 1 ≤ Q) (ht : 0 ≤ t) (htQ : t ≤ Q) :
    powerGap ℓ t ≤ coarseGapConstant κ ℓ * Q ^ (ℓ - 1) * concavePowerGap κ t := by
  set T : ℝ := max 1 ((2 / κ) ^ (1 / (1 - κ))) with hTdef
  set c : ℝ := ℓ * (ℓ - 1) / (κ * (1 - κ)) with hcdef
  have hc : 0 ≤ c := by
    rw [hcdef]
    apply div_nonneg (mul_nonneg (by linarith) (by linarith))
    exact mul_nonneg hκ.le (by linarith)
  have hT1 : 1 ≤ T := le_max_left _ _
  set K : ℝ := coarseGapConstant κ ℓ with hKdef
  have hK : 0 < K := coarseGapConstant_pos hκ
  have hψ : 0 ≤ concavePowerGap κ t := concavePowerGap_nonneg hκ.le hκ1.le ht
  have hQpow : 1 ≤ Q ^ (ℓ - 1) := Real.one_le_rpow hQ (by linarith)
  have hKQ : K ≤ K * Q ^ (ℓ - 1) := le_mul_of_one_le_right hK.le hQpow
  by_cases htT : t ≤ T
  · have hQ'1 : 1 ≤ min Q T := le_min hQ hT1
    have h := powerGap_le_curvature hκ hκ1 hℓ hQ'1 ht (le_min htQ htT)
    have hQ'T : (min Q T) ^ (ℓ - κ) ≤ T ^ (ℓ - κ) :=
      Real.rpow_le_rpow (by linarith) (min_le_right _ _) (by linarith)
    calc
      powerGap ℓ t ≤ c * (min Q T) ^ (ℓ - κ) * concavePowerGap κ t := h
      _ ≤ c * T ^ (ℓ - κ) * concavePowerGap κ t :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hQ'T hc) hψ
      _ ≤ K * Q ^ (ℓ - 1) * concavePowerGap κ t :=
        mul_le_mul_of_nonneg_right ((le_max_left _ _).trans hKQ) hψ
  · have hTt : T < t := lt_of_not_ge htT
    have ht1 : 1 ≤ t := hT1.trans hTt.le
    have ht0 : 0 < t := by linarith
    -- `t^(1-κ) ≥ 2/κ`, hence `t^(κ-1) ≤ κ/2`.
    have hbase : (2 / κ) ^ (1 / (1 - κ)) ≤ t := (le_max_right _ _).trans hTt.le
    have hpow : 2 / κ ≤ t ^ (1 - κ) := by
      have h1 := Real.rpow_le_rpow (by positivity) hbase (by linarith : (0 : ℝ) ≤ 1 - κ)
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith),
        Real.rpow_one] at h1
    have hsplit : t ^ κ = t * t ^ (κ - 1) := by
      rw [← Real.rpow_one_add' ht0.le (by linarith)]
      congr 1
      ring
    have hinv : t ^ (κ - 1) * t ^ (1 - κ) = 1 := by
      rw [← Real.rpow_add ht0]
      norm_num
    have hsmall : t ^ (κ - 1) ≤ κ / 2 := by
      have hpos : 0 < t ^ (1 - κ) := Real.rpow_pos_of_pos ht0 _
      have h2 : t ^ (κ - 1) * (2 / κ) ≤ 1 := by
        calc t ^ (κ - 1) * (2 / κ) ≤ t ^ (κ - 1) * t ^ (1 - κ) :=
              mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg ht0.le _)
          _ = 1 := hinv
      have h3 : t ^ (κ - 1) * (2 / κ) = t ^ (κ - 1) * 2 / κ := by ring
      rw [h3, div_le_iff₀ hκ] at h2
      linarith
    have hψ' : κ * t / 2 ≤ concavePowerGap κ t := by
      unfold concavePowerGap
      rw [hsplit]
      nlinarith
    have hφ : powerGap ℓ t ≤ t ^ ℓ := by
      unfold powerGap
      nlinarith
    have htl : t ^ ℓ ≤ Q ^ (ℓ - 1) * t := by
      have hsplit' : t ^ ℓ = t ^ (ℓ - 1) * t := by
        rw [← Real.rpow_add_one ht0.ne']
        congr 1
        ring
      rw [hsplit']
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow ht0.le htQ (by linarith)) ht0.le
    have htψ : t ≤ (2 / κ) * concavePowerGap κ t := by
      calc t = (2 / κ) * (κ * t / 2) := by field_simp
        _ ≤ (2 / κ) * concavePowerGap κ t := mul_le_mul_of_nonneg_left hψ' (by positivity)
    calc
      powerGap ℓ t ≤ Q ^ (ℓ - 1) * t := hφ.trans htl
      _ ≤ Q ^ (ℓ - 1) * ((2 / κ) * concavePowerGap κ t) :=
        mul_le_mul_of_nonneg_left htψ (by linarith)
      _ = (2 / κ) * Q ^ (ℓ - 1) * concavePowerGap κ t := by ring
      _ ≤ K * Q ^ (ℓ - 1) * concavePowerGap κ t := by
        apply mul_le_mul_of_nonneg_right _ hψ
        exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

/-- The tangent-line inequality `x^p - 1 ≤ p x^(p-1) (x - 1)` for `p ≥ 1`, `x > 0`. -/
theorem rpow_sub_one_le_tangent {p x : ℝ} (hp : 1 ≤ p) (hx : 0 < x) :
    x ^ p - 1 ≤ p * x ^ (p - 1) * (x - 1) := by
  have hg := powerGap_nonneg hp (inv_nonneg.mpr hx.le)
  unfold powerGap at hg
  have hxp : 0 < x ^ p := Real.rpow_pos_of_pos hx p
  have hinv : x⁻¹ ^ p = (x ^ p)⁻¹ := Real.inv_rpow hx.le p
  have hm : x ^ (p - 1) = x ^ p * x⁻¹ := by
    rw [Real.rpow_sub_one hx.ne', div_eq_mul_inv]
  rw [hinv] at hg
  have key : 0 ≤ x ^ p * ((x ^ p)⁻¹ - p * x⁻¹ + p - 1) := mul_nonneg hxp.le hg
  have hx1 : x ^ p * (x ^ p)⁻¹ = 1 := mul_inv_cancel₀ hxp.ne'
  rw [hm]
  have hxx : x ^ p * x⁻¹ * x = x ^ p := by rw [mul_assoc, inv_mul_cancel₀ hx.ne', mul_one]
  have e : p * (x ^ p * x⁻¹) * (x - 1) = p * x ^ p - p * (x ^ p * x⁻¹) := by
    calc p * (x ^ p * x⁻¹) * (x - 1) = p * (x ^ p * x⁻¹ * x) - p * (x ^ p * x⁻¹) := by ring
      _ = _ := by rw [hxx]
  have hexp : x ^ p * ((x ^ p)⁻¹ - p * x⁻¹ + p - 1) =
      x ^ p * (x ^ p)⁻¹ - p * (x ^ p * x⁻¹) + (p - 1) * x ^ p := by ring
  rw [hexp, hx1] at key
  rw [e]
  linarith

universe u

/-- The coarse charge `C_v(Q)` of a component of exponent `v` in the typed-mixture
lemma, with alphabet size `Q`, target exponent `R`, low exponent `s` and `d` slots. -/
noncomputable def typedCost (s R v : ℝ) (d Q : ℕ) : ℝ :=
  (d : ℝ) / v * coarseGapConstant (s / R) (v / R) * (Q : ℝ) ^ ((d : ℝ) / R - d / v)

/-- **One-coordinate estimate of `lem:density:typed-mixture`, coarse form.** For
`0 < s < R < v ≤ d`, every `f` with `‖f‖_R = 1` (uniform probability on `X`) satisfies
`‖f‖_v^d - 1 ≤ C_v(|X|) (1 - ‖f‖_s^d)` with `C_v(Q) = K Q^(d/R - d/v)`, where `K`
depends only on `s, R, v, d` (`typedCost`). -/
theorem lpNorm_deficit_coarse {s R v : ℝ} {d : ℕ} (hs : 0 < s) (hsR : s < R) (hRv : R < v)
    (hvd : v ≤ d) {X : Type u} [Fintype X] [Nonempty X] {f : X → ℝ}
    (hn : (FiniteLaw.uniform X).lpNorm R f = 1) :
    (FiniteLaw.uniform X).lpNorm v f ^ d - 1 ≤
      typedCost s R v d (Fintype.card X) * (1 - (FiniteLaw.uniform X).lpNorm s f ^ d) := by
  have hR : 0 < R := hs.trans hsR
  have hv : 0 < v := hR.trans hRv
  set κ : ℝ := s / R with hκdef
  set ℓ : ℝ := v / R with hℓdef
  have hκ : 0 < κ := div_pos hs hR
  have hκ1 : κ < 1 := (div_lt_one hR).mpr hsR
  have hℓ : 1 < ℓ := (one_lt_div hR).mpr hRv
  set p : ℝ := (d : ℝ) / v with hpdef
  have hp : 1 ≤ p := (one_le_div hv).mpr hvd
  set K₀ := coarseGapConstant κ ℓ
  have hK₀ : 0 < K₀ := coarseGapConstant_pos hκ
  have hcomp (Q t : ℝ) (hQ : 1 ≤ Q) (ht : 0 ≤ t) (htQ : t ≤ Q) :=
    powerGap_le_coarse hκ hκ1 hℓ hQ ht htQ
  unfold typedCost
  set μ := FiniteLaw.uniform X
  set Q : ℝ := (Fintype.card X : ℝ) with hQdef
  have hQ : 1 ≤ Q := by
    rw [hQdef]
    exact_mod_cast Fintype.card_pos
  set w : X → ℝ := fun x => |f x| ^ R with hwdef
  have hw0 (x : X) : 0 ≤ w x := Real.rpow_nonneg (abs_nonneg _) _
  -- `E w = 1`.
  have hEw : μ.expect w = 1 := by
    have h := μ.lpNorm_rpow hR.ne' f
    rw [hn, Real.one_rpow] at h
    exact h.symm
  -- `w ≤ Q` pointwise.
  have hwQ (x : X) : w x ≤ Q := by
    have hsum : (∑ y, w y) / Q = 1 := by
      rw [← hEw]
      exact (FiniteLaw.expect_uniform w).symm
    have hsum' : ∑ y, w y = Q := by
      have hQ0 : Q ≠ 0 := by linarith
      field_simp at hsum
      linarith
    rw [← hsum']
    exact Finset.single_le_sum (fun y _ => hw0 y) (Finset.mem_univ x)
  -- Powers of `w` are moments of `f`.
  have hpow (q : ℝ) (x : X) : w x ^ (q / R) = |f x| ^ q := by
    rw [hwdef, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hmv : μ.expect (fun x => w x ^ ℓ) = μ.moment v f := by
    unfold FiniteLaw.moment
    congr 1
    funext x
    exact hpow v x
  have hms : μ.expect (fun x => w x ^ κ) = μ.moment s f := by
    unfold FiniteLaw.moment
    congr 1
    funext x
    exact hpow s x
  -- The averaged deficit inequality.
  have hgap : μ.moment v f - 1 ≤ K₀ * Q ^ (ℓ - 1) * (1 - μ.moment s f) := by
    have hpt (x : X) := hcomp Q (w x) hQ (hw0 x) (hwQ x)
    have hE := μ.expect_mono hpt
    have hl : μ.expect (fun x => powerGap ℓ (w x)) = μ.moment v f - 1 := by
      unfold powerGap
      simp only [FiniteLaw.expect_sub, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
        FiniteLaw.expect_const, hEw, hmv]
      ring
    have hr : μ.expect (fun x => K₀ * Q ^ (ℓ - 1) * concavePowerGap κ (w x)) =
        K₀ * Q ^ (ℓ - 1) * (1 - μ.moment s f) := by
      rw [FiniteLaw.expect_const_mul]
      unfold concavePowerGap
      simp only [FiniteLaw.expect_sub, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
        FiniteLaw.expect_const, hEw, hms]
      ring
    rw [hl, hr] at hE
    exact hE
  -- `1 ≤ ‖f‖_v^v ≤ Q^(ℓ-1)`.
  have hm1 : 1 ≤ μ.moment v f := by
    have hj := μ.expect_rpow_le hℓ.le hw0
    rw [hEw, Real.one_rpow, hmv] at hj
    exact hj
  have hmQ : μ.moment v f ≤ Q ^ (ℓ - 1) := by
    rw [← hmv]
    have hpt (x : X) : w x ^ ℓ ≤ Q ^ (ℓ - 1) * w x := by
      have hsplit : w x ^ ℓ = w x ^ (ℓ - 1) * w x ^ (1 : ℝ) := by
        rw [← Real.rpow_add' (hw0 x) (by linarith)]
        congr 1
        ring
      rw [hsplit, Real.rpow_one]
      exact mul_le_mul_of_nonneg_right
        (Real.rpow_le_rpow (hw0 x) (hwQ x) (by linarith)) (hw0 x)
    have h := μ.expect_mono hpt
    rwa [FiniteLaw.expect_const_mul, hEw, mul_one] at h
  -- `‖f‖_v^d = (‖f‖_v^v)^p` and `‖f‖_s^d ≤ ‖f‖_s^s`.
  have hnorm (q : ℝ) (hq : 0 < q) :
      μ.lpNorm q f ^ d = μ.moment q f ^ ((d : ℝ) / q) := by
    unfold FiniteLaw.lpNorm
    rw [← Real.rpow_natCast, ← Real.rpow_mul (μ.moment_nonneg q f)]
    congr 1
    field_simp
  have hms1 : μ.moment s f ≤ 1 := by
    have hmono := μ.lpNorm_mono hs hsR.le f
    rw [hn] at hmono
    have h := Real.rpow_le_rpow (μ.lpNorm_nonneg s f) hmono hs.le
    rwa [μ.lpNorm_rpow hs.ne', Real.one_rpow] at h
  have hsd : μ.lpNorm s f ^ d ≤ μ.moment s f := by
    rw [hnorm s hs]
    have hds : 1 ≤ (d : ℝ) / s := (one_le_div hs).mpr ((hsR.trans hRv).le.trans hvd)
    rcases (μ.moment_nonneg s f).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]
    · have h := Real.rpow_le_rpow_of_exponent_ge hpos hms1 hds
      rwa [Real.rpow_one] at h
  -- The tangent-line step at `m = ‖f‖_v^v ∈ [1, Q^(ℓ-1)]`.
  set m := μ.moment v f
  have hm0 : 0 < m := by linarith
  have htan := rpow_sub_one_le_tangent hp hm0
  have hmp : m ^ (p - 1) ≤ (Q ^ (ℓ - 1)) ^ (p - 1) :=
    Real.rpow_le_rpow hm0.le hmQ (by linarith)
  have hQl : 0 ≤ Q ^ (ℓ - 1) := Real.rpow_nonneg (by linarith) _
  have hexp : (Q ^ (ℓ - 1)) ^ (p - 1) * Q ^ (ℓ - 1) =
      Q ^ ((d : ℝ) / R - d / v) := by
    rw [← Real.rpow_mul (by linarith), ← Real.rpow_add_of_nonneg (by linarith)
      (mul_nonneg (by linarith) (by linarith)) (by linarith)]
    congr 1
    rw [hℓdef, hpdef]
    field_simp
    ring
  rw [hnorm v hv]
  have hdef : 0 ≤ 1 - μ.moment s f := by linarith
  calc
    m ^ ((d : ℝ) / v) - 1 = m ^ p - 1 := rfl
    _ ≤ p * m ^ (p - 1) * (m - 1) := htan
    _ ≤ p * (Q ^ (ℓ - 1)) ^ (p - 1) * (K₀ * Q ^ (ℓ - 1) * (1 - μ.moment s f)) := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hmp (by linarith)) hgap (by linarith)
      exact mul_nonneg (by linarith) (Real.rpow_nonneg hQl _)
    _ = p * K₀ * ((Q ^ (ℓ - 1)) ^ (p - 1) * Q ^ (ℓ - 1)) * (1 - μ.moment s f) := by ring
    _ = p * K₀ * Q ^ ((d : ℝ) / R - d / v) * (1 - μ.moment s f) := by rw [hexp]
    _ ≤ p * K₀ * Q ^ ((d : ℝ) / R - d / v) * (1 - μ.lpNorm s f ^ d) := by
      apply mul_le_mul_of_nonneg_left (by linarith)
      exact mul_nonneg (mul_nonneg (by linarith) hK₀.le) (Real.rpow_nonneg (by linarith) _)

/-- **The typed-mixture lemma with coarse charges** (`lem:density:typed-mixture` and
`eq:density:typed-mixture-coarse`, with the constant of `typedCost`). A mixture of laws
with unit mixed `L^(r_j)` norms and uniform marginals has unit mixed `L^R` norm if the
charges of the components above `R` (all at most `d = |V|`) are paid by the weight of
the components at most `s`. -/
theorem mixedLpBound_typed_mixture_coarse {V X J : Type*} [Fintype V] [DecidableEq V]
    [Nonempty V] [Fintype X] [Nonempty X] [Fintype J] (weights : FiniteLaw J)
    (laws : J → FiniteLaw (V → X)) (r : J → ℝ) {s R : ℝ} (hs : 0 < s) (hsR : s < R)
    (hr : ∀ j, 0 < r j) (hrd : ∀ j, r j ≤ Fintype.card V)
    (hlocal : ∀ j, MixedLpBound (laws j) (r j) 1)
    (hbalance : (∑ j ∈ Finset.univ.filter (fun j => R < r j),
        weights.weight j * typedCost s R (r j) (Fintype.card V) (Fintype.card X)) ≤
      ∑ j ∈ Finset.univ.filter (fun j => r j ≤ s), weights.weight j) :
    MixedLpBound (FiniteLaw.mixture weights laws) R 1 := by
  apply mixedLpBound_typed_mixture weights laws r
    (fun j => typedCost s R (r j) (Fintype.card V) (Fintype.card X)) hs hsR hr hlocal hbalance
  intro f _ hn j hj
  exact lpNorm_deficit_coarse hs hsR hj (hrd j) hn

end Sarkozy

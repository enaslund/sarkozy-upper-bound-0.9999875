module

public import Sarkozy.Labellings.Extension
public import Sarkozy.FiniteProbability
public import Mathlib.Algebra.BigOperators.Field

/-!
# `lem:spec:stars` (a), (d) and the product identity of `lem:spec:expansion`

`paper/sections/14_spectral.tex`, Section `subsec:spec:perp`, over a finite field `F` of odd
characteristic (`F = 𝔽_p`), with the quadratic character `χ`.

* `starTrace S = p⁻¹ ∑_t χ(∏_{a ∈ S} (t - a))`, the star trace `w_J(x)` of
  `lem:spec:stars` (a) for `S = x(J)`: `starTrace_singleton` (`= 0`), `starTrace_pair`
  (`= -q`, by the two-root identity), and `abs_starTrace_le` (`|w| ≤ (|S| - 1) r`, from Weil's
  bound `Labellings.WeilBound`, i.e. `Target.Weil` by `Labellings.weilBound_of_target`).
* `starFunction` and `star_function_bounds`, `star_function_moments` — `lem:spec:stars` (d):
  the star function `h_⋆ = ∑_k ∑_{∅ ≠ J ⊆ N(k)} (ε_J)_k w_J` (coefficients of modulus at most
  one) is a constant of modulus at most `P_st` plus a function of sup norm at most `W_st`; hence
  `‖h_⋆ - E h_⋆‖ ≤ W_st` and `|E h_⋆| ≤ P_st + W_st` for every law of the labels. Here
  `P_st = q ∑_k #{J ⊆ N(k) : |J| = 2} = r² ∑_k binom(r_k, 2)` and
  `W_st = r ∑_k ∑_{J ⊆ N(k), |J| ≥ 3} (|J| - 1) = r ∑_k ∑_{s ≥ 3} binom(r_k, s)(s - 1)`.
  These are the standard star inputs of `prop:spec2:mucentre` (d).
* `prod_one_add_char`, `prod_one_add_char_eq` — `lem:spec:expansion`, the kernel identity:
  `∏_e (1 + χ(y_e)) = ∑_{S ⊆ E} ∏_{e ∈ S} χ(y_e)`, and `= 2^{|E|} ∏_e [y_e ∈ Q_p]` when all
  `y_e ≠ 0`, i.e. `K₀ = 2^{m_×} K` on pairs of half-labellings with disjoint label sets.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The star trace `p⁻¹ ∑_t χ(∏_{a∈S}(t - a))`. -/
noncomputable def starTrace (S : Finset F) : ℝ :=
  (1 / (Fintype.card F : ℝ)) * ∑ t, (quadraticChar F (∏ a ∈ S, (t - a)) : ℝ)

theorem starTrace_eq_rootSum (S : Finset F) :
    starTrace S = (rootSum S : ℝ) / Fintype.card F := by
  rw [starTrace, rootSum]
  push_cast
  ring

/-- `∏_{j∈J} χ(t - x_j) = χ(∏_{a ∈ x(J)} (t - a))` for `x` injective on `J`. -/
theorem prod_char_eq {ι : Type*} [DecidableEq ι] (J : Finset ι) (x : ι → F)
    (hx : Set.InjOn x J) (t : F) :
    ∏ j ∈ J, quadraticChar F (t - x j) = quadraticChar F (∏ a ∈ J.image x, (t - a)) := by
  rw [Finset.prod_image (fun a ha b hb h => hx ha hb h), map_prod]

/-- `lem:spec:stars` (a), `|J| = 1`: `w = 0`. -/
theorem starTrace_singleton (hF : ringChar F ≠ 2) (a : F) : starTrace {a} = 0 := by
  rw [starTrace_eq_rootSum, rootSum_singleton hF]
  simp

/-- `lem:spec:stars` (a), `|J| = 2`: `w = -q` (the two-root identity). -/
theorem starTrace_pair (hF : ringChar F ≠ 2) {a b : F} (hab : a ≠ b) :
    starTrace {a, b} = -(1 / (Fintype.card F : ℝ)) := by
  rw [starTrace_eq_rootSum, two_root hF hab]
  push_cast
  ring

/-- `lem:spec:stars` (a), `|J| ≥ 3` (and in fact every nonempty `S`): `|w| ≤ (|S| - 1) r`,
by Weil's bound. -/
theorem abs_starTrace_le (hW : WeilBound F) {S : Finset F} (hS : S.Nonempty) :
    |starTrace S| ≤ ((S.card : ℝ) - 1) * (1 / √(Fintype.card F)) := by
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsq : 0 < √(Fintype.card F : ℝ) := Real.sqrt_pos.mpr hq
  rw [starTrace_eq_rootSum, abs_div, abs_of_pos hq, div_le_iff₀ hq]
  have h := hW S hS
  have e : ((S.card : ℝ) - 1) * (1 / √(Fintype.card F)) * (Fintype.card F : ℝ) =
      ((S.card : ℝ) - 1) * √(Fintype.card F) := by
    calc ((S.card : ℝ) - 1) * (1 / √(Fintype.card F)) * (Fintype.card F : ℝ)
        = ((S.card : ℝ) - 1) * ((Fintype.card F : ℝ) / √(Fintype.card F)) := by ring
      _ = ((S.card : ℝ) - 1) * √(Fintype.card F) := by rw [Real.div_sqrt]
  rw [e]
  exact h

section StarFunction

variable {ι κ : Type*} [Fintype κ] [DecidableEq ι]

/-- The star function `h_⋆(x) = ∑_k ∑_{∅ ≠ J ⊆ N(k)} c_{k,J} w_J(x)`, with `w_J(x)` the star
trace of the labels `x(J)`. -/
noncomputable def starFunction (N : κ → Finset ι) (c : κ → Finset ι → ℝ) (x : ι → F) : ℝ :=
  ∑ k, ∑ J ∈ (N k).powerset.filter (fun J => J.Nonempty), c k J * starTrace (J.image x)

/-- The constant part `-q ∑_k ∑_{|J| = 2} c_{k,J}`. -/
noncomputable def starConst (N : κ → Finset ι) (c : κ → Finset ι → ℝ) : ℝ :=
  -(1 / (Fintype.card F : ℝ)) * ∑ k, ∑ J ∈ (N k).powerset.filter (fun J => J.card = 2), c k J

/-- `W_st = r ∑_k ∑_{J ⊆ N(k), |J| ≥ 3} (|J| - 1)`. -/
noncomputable def Wst (N : κ → Finset ι) : ℝ :=
  (1 / √(Fintype.card F : ℝ)) *
    ∑ k, ∑ J ∈ (N k).powerset.filter (fun J => 3 ≤ J.card), ((J.card : ℝ) - 1)

/-- `P_st = q ∑_k #{J ⊆ N(k) : |J| = 2}`. -/
noncomputable def Pst (N : κ → Finset ι) : ℝ :=
  (1 / (Fintype.card F : ℝ)) * ∑ k, (((N k).powerset.filter (fun J => J.card = 2)).card : ℝ)

omit [Field F] [DecidableEq F] [DecidableEq ι] in
theorem Pst_eq_binom (N : κ → Finset ι) :
    Pst (F := F) N = (1 / (Fintype.card F : ℝ)) * ∑ k, ((N k).card.choose 2 : ℝ) := by
  rw [Pst]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← Finset.powersetCard_eq_filter, Finset.card_powersetCard]

/-- **`lem:spec:stars` (d), pointwise**: `h_⋆(x)` is the constant `starConst` plus a term of
modulus at most `W_st`, for every injective `x`, when `|c_{k,J}| ≤ 1`. -/
theorem star_function_bounds (hF : ringChar F ≠ 2) (hW : WeilBound F) (N : κ → Finset ι)
    (c : κ → Finset ι → ℝ) (hc : ∀ k J, |c k J| ≤ 1) (x : ι → F) (hx : Function.Injective x) :
    |starFunction N c x - starConst (F := F) N c| ≤ Wst (F := F) N := by
  set r := 1 / √(Fintype.card F : ℝ) with hr
  have hr0 : 0 ≤ r := by rw [hr]; positivity
  -- split each inner sum into `|J| = 1`, `|J| = 2` and `|J| ≥ 3`
  have hsplit : ∀ k, ∑ J ∈ (N k).powerset.filter (fun J => J.Nonempty),
      c k J * starTrace (J.image x) =
      ∑ J ∈ (N k).powerset.filter (fun J => J.card = 2), c k J * (-(1 / (Fintype.card F : ℝ))) +
      ∑ J ∈ (N k).powerset.filter (fun J => 3 ≤ J.card), c k J * starTrace (J.image x) := by
    intro k
    set s := (N k).powerset.filter (fun J => J.Nonempty)
    have h1 : ∑ J ∈ s, c k J * starTrace (J.image x) =
        ∑ J ∈ s.filter (fun J => J.card = 1), c k J * starTrace (J.image x) +
        ∑ J ∈ s.filter (fun J => ¬ J.card = 1), c k J * starTrace (J.image x) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have h2 : ∑ J ∈ s.filter (fun J => ¬ J.card = 1), c k J * starTrace (J.image x) =
        ∑ J ∈ (s.filter (fun J => ¬ J.card = 1)).filter (fun J => J.card = 2),
          c k J * starTrace (J.image x) +
        ∑ J ∈ (s.filter (fun J => ¬ J.card = 1)).filter (fun J => ¬ J.card = 2),
          c k J * starTrace (J.image x) :=
      (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    have hzero : ∑ J ∈ s.filter (fun J => J.card = 1), c k J * starTrace (J.image x) = 0 := by
      refine Finset.sum_eq_zero fun J hJ => ?_
      obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (Finset.mem_filter.mp hJ).2
      rw [Finset.image_singleton, starTrace_singleton hF, mul_zero]
    have hset2 : (s.filter (fun J => ¬ J.card = 1)).filter (fun J => J.card = 2) =
        (N k).powerset.filter (fun J => J.card = 2) := by
      ext J
      simp only [s, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨⟨h1, -⟩, -⟩, h2⟩
        exact ⟨h1, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨⟨⟨h1, ?_⟩, by omega⟩, h2⟩
        rw [← Finset.card_pos]
        omega
    have hset3 : (s.filter (fun J => ¬ J.card = 1)).filter (fun J => ¬ J.card = 2) =
        (N k).powerset.filter (fun J => 3 ≤ J.card) := by
      ext J
      simp only [s, Finset.mem_filter, Finset.mem_powerset]
      constructor
      · rintro ⟨⟨⟨h1, h0⟩, h1'⟩, h2⟩
        refine ⟨h1, ?_⟩
        have := Finset.card_pos.mpr h0
        omega
      · rintro ⟨h1, h3⟩
        refine ⟨⟨⟨h1, ?_⟩, by omega⟩, by omega⟩
        rw [← Finset.card_pos]
        omega
    have hpair : ∀ J ∈ (N k).powerset.filter (fun J => J.card = 2),
        c k J * starTrace (J.image x) = c k J * (-(1 / (Fintype.card F : ℝ))) := by
      intro J hJ
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp (Finset.mem_filter.mp hJ).2
      rw [Finset.image_insert, Finset.image_singleton,
        starTrace_pair hF (fun h => hab (hx h))]
    rw [h1, hzero, zero_add, h2, hset2, hset3, Finset.sum_congr rfl hpair]
  have hrest : ∀ k, |∑ J ∈ (N k).powerset.filter (fun J => 3 ≤ J.card),
      c k J * starTrace (J.image x)| ≤
      r * ∑ J ∈ (N k).powerset.filter (fun J => 3 ≤ J.card), ((J.card : ℝ) - 1) := by
    intro k
    rw [Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun J hJ => ?_)
    have hJ3 := (Finset.mem_filter.mp hJ).2
    have hne : (J.image x).Nonempty := by
      rw [Finset.image_nonempty, ← Finset.card_pos]
      omega
    have hcard : (J.image x).card = J.card := Finset.card_image_of_injective _ hx
    have hw := abs_starTrace_le hW hne
    rw [hcard] at hw
    rw [abs_mul]
    calc |c k J| * |starTrace (J.image x)| ≤ 1 * (((J.card : ℝ) - 1) * r) :=
          mul_le_mul (hc k J) hw (abs_nonneg _) zero_le_one
      _ = r * ((J.card : ℝ) - 1) := by ring
  have hdecomp : starFunction N c x - starConst (F := F) N c =
      ∑ k, ∑ J ∈ (N k).powerset.filter (fun J => 3 ≤ J.card), c k J * starTrace (J.image x) := by
    rw [starFunction, starConst, Finset.sum_congr rfl fun k _ => hsplit k, Finset.sum_add_distrib,
      Finset.mul_sum]
    have : ∀ k, ∑ J ∈ (N k).powerset.filter (fun J => J.card = 2),
        c k J * (-(1 / (Fintype.card F : ℝ))) =
        -(1 / (Fintype.card F : ℝ)) * ∑ J ∈ (N k).powerset.filter (fun J => J.card = 2), c k J :=
      fun k => by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun J _ => by ring
    rw [Finset.sum_congr rfl fun k _ => this k]
    ring
  rw [hdecomp, Wst, ← hr, Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => hrest k)

omit [DecidableEq F] [DecidableEq ι] in
/-- `|starConst| ≤ P_st` when `|c_{k,J}| ≤ 1`. -/
theorem abs_starConst_le (N : κ → Finset ι) (c : κ → Finset ι → ℝ)
    (hc : ∀ k J, |c k J| ≤ 1) : |starConst (F := F) N c| ≤ Pst (F := F) N := by
  have hq : (0 : ℝ) ≤ 1 / (Fintype.card F : ℝ) := by positivity
  rw [starConst, Pst, abs_mul, abs_neg, abs_of_nonneg hq]
  refine mul_le_mul_of_nonneg_left ?_ hq
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ J ∈ (N k).powerset.filter (fun J => J.card = 2), |c k J| ≤
      ∑ J ∈ (N k).powerset.filter (fun J => J.card = 2), (1 : ℝ) :=
        Finset.sum_le_sum fun J _ => hc k J
    _ = (((N k).powerset.filter (fun J => J.card = 2)).card : ℝ) := by simp

/-- **`lem:spec:stars` (d)**: for every law `μ` of injective labellings `X ω`,
`‖h_⋆ - E h_⋆‖_μ² ≤ W_st²` and `|E_μ h_⋆| ≤ P_st + W_st`. -/
theorem star_function_moments (hF : ringChar F ≠ 2) (hW : WeilBound F) {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (X : Ω → ι → F) (hX : ∀ ω, Function.Injective (X ω)) (N : κ → Finset ι)
    (c : κ → Finset ι → ℝ) (hc : ∀ k J, |c k J| ≤ 1) :
    μ.expect (fun ω => (starFunction N c (X ω) - μ.expect (fun ω => starFunction N c (X ω))) ^ 2)
      ≤ Wst (F := F) N ^ 2 ∧
    |μ.expect (fun ω => starFunction N c (X ω))| ≤ Pst (F := F) N + Wst (F := F) N := by
  set h := fun ω => starFunction N c (X ω) with hh
  set c0 := starConst (F := F) N c with hc0
  have hpt : ∀ ω, |h ω - c0| ≤ Wst (F := F) N := fun ω =>
    star_function_bounds hF hW N c hc (X ω) (hX ω)
  constructor
  · -- the variance is at most the second moment of `h - c₀`
    have hvar : μ.expect (fun ω => (h ω - μ.expect h) ^ 2) ≤
        μ.expect (fun ω => (h ω - c0) ^ 2) := by
      have e : ∀ ω, (h ω - c0) ^ 2 = (h ω - μ.expect h) ^ 2 + 2 * (μ.expect h - c0) *
          (h ω - μ.expect h) + (μ.expect h - c0) ^ 2 := fun ω => by ring
      rw [μ.expect_congr e, FiniteLaw.expect_add, FiniteLaw.expect_add,
        FiniteLaw.expect_const_mul, FiniteLaw.expect_sub, FiniteLaw.expect_const,
        FiniteLaw.expect_const]
      nlinarith [sq_nonneg (μ.expect h - c0)]
    refine hvar.trans (μ.expect_le_const fun ω => ?_)
    have h2 := pow_le_pow_left₀ (abs_nonneg _) (hpt ω) 2
    rwa [sq_abs] at h2
  · have h1 : |μ.expect h - c0| ≤ Wst (F := F) N := by
      rw [show μ.expect h - c0 = μ.expect (fun ω => h ω - c0) by
        rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]]
      exact (μ.abs_expect_le _).trans (μ.expect_le_const hpt)
    have h2 := abs_starConst_le (F := F) N c hc
    calc |μ.expect h| = |(μ.expect h - c0) + c0| := by ring_nf
      _ ≤ |μ.expect h - c0| + |c0| := abs_add_le _ _
      _ ≤ Pst (F := F) N + Wst (F := F) N := by linarith

end StarFunction

/-- **`lem:spec:expansion`, the character expansion**: `∏_{e∈E} (1 + χ(y_e)) =
∑_{S ⊆ E} ∏_{e∈S} χ(y_e)`. -/
theorem prod_one_add_char {ε : Type*} (E : Finset ε) (y : ε → F) :
    ∏ e ∈ E, (1 + (quadraticChar F (y e) : ℝ)) = ∑ S ∈ E.powerset, ∏ e ∈ S,
      (quadraticChar F (y e) : ℝ) :=
  Finset.prod_one_add E

/-- **`lem:spec:expansion`, `K₀ = 2^{m_×} K`**: if every `y_e ≠ 0`, then
`∏_{e∈E} (1 + χ(y_e)) = 2^{|E|} ∏_{e∈E} [y_e is a nonzero square]`. -/
theorem prod_one_add_char_eq {ε : Type*} (hF : ringChar F ≠ 2) (E : Finset ε) (y : ε → F)
    (hy : ∀ e ∈ E, y e ≠ 0) :
    ∏ e ∈ E, (1 + (quadraticChar F (y e) : ℝ)) =
      2 ^ E.card * ∏ e ∈ E, (if IsSquare (y e) then (1 : ℝ) else 0) := by
  have _ := hF
  rw [← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun e he => ?_
  by_cases hs : IsSquare (y e)
  · rw [quadraticChar_one_iff_isSquare (hy e he) |>.mpr hs, ite_eq_left hs]
    norm_num
  · rw [quadraticChar_neg_one_iff_not_isSquare.mpr hs, ite_eq_right hs]
    norm_num

end Sarkozy.Spectral

module

public import Sarkozy.RecordExpansion.Bound

/-!
# Classes and completion of the reserved cost

Section 10 of the paper, `lem:record:record-expansion` (ii) (complete
polynomials, in the evaluated form used by the closing) and (iv)
(completion), for a completion polynomial `𝒟` with finitely many monomials.

## The power series `e^{S(x)} cosh A(x) - 1`

The price variables are `x^ε_{b,t}` (`PriceVar T`). For a multi-index
`n : PriceVar T → ℕ`, `mono x n = ∏_v x_v^{n_v}`, `mfact n = ∏_v n_v!` and
`skewDeg n` is the degree in the skew variables. The coefficient of `x^n` in
`e^{S(x)} cosh A(x) - 1` is `expCoeff n = 1/n!` for nonconstant monomials of
even skew degree and `0` otherwise, as in the paper. We do not use formal power
series: `truncExp K x`, the sum of the terms with all exponents below `K`, is
computed in closed form (`truncExp_eq`), tends to `e^{S(x)} cosh A(x) - 1`
(`tendsto_truncExp`) and increases with `K` for `x ≥ 0`; hence every finite
partial sum of the series is at most `e^{S(x)} cosh A(x) - 1`
(`sum_expCoeff_le`). The monomial of a selection `ω` is `selMono ω`, squarefree
with coefficient one (`expCoeff_selMono`); distinct selections have distinct
monomials (`selMono_injective`), and `mono (priceVec π) (selMono ω) = π_ω`.

## Results

* `sum_cost_add_poly_le`, `sum_cost_le_completion`: **completion**
  (`lem:record:record-expansion` (iv)) for a polynomial
  `𝒟(x) = ∑_{n ∈ supp} d_n x^n` with `d_n ≥ 0`, `d_n ≤ B' - c_ω` on the monomial
  of every selection and `d_n ≤ B' c_n` on every other monomial:
  `∑_ω c_ω π_ω ≤ B'(e^S cosh A - 1) - 𝒟(π)`, and, if the costs are
  nonnegative, the same at upper prices `π̂ ≥ π`
  (`completion_mono`, `sum_cost_le_completion_upper`).
* `sum_abs_le_of_classes`: the class sums of (CP5): if every class
  `𝒞` satisfies `∑_{ω ∈ 𝒞} |I_ω| ≤ ∑_{ω ∈ 𝒞} ((φ_ω + z π_ω) Y + r_ω)` and every
  selection in no class satisfies `|I_ω| ≤ (B + z) π_ω Y + r_ω`, then
  `∑_ω |I_ω| ≤ ∑_ω ((b_ω + z π_ω) Y + r_ω)` with `b_ω = φ_ω` on the classes
  and `b_ω = B π_ω` elsewhere (proof of `lem:record:record-expansion` (ii)).
* `abs_energy_sub_le_of_complete`: (ii) in evaluated form: for any number
  `Ψ ≥ ∑_ω b_ω` (for instance the value of a complete polynomial),
  `|Y_ν - Y_λ| ≤ (Ψ + z (e^S cosh A - 1)) Y + ∑_ω r_ω`.
* `abs_energy_sub_le_completion`: (ii) and (iv) combined for class costs
  `0 ≤ c_𝒞`, at upper prices:
  `|Y_ν - Y_λ| ≤ (B'(e^Ŝ cosh Â - 1) - 𝒟(π̂) + z(e^Ŝ cosh Â - 1)) Y + ∑_ω r_ω`.

* `exp_cosh_mono`, `completion_mono`, `exists_upper_prices`: the monotonicity
  and distribution statements of (iii) used to pass to upper prices.

The paper allows `𝒟` to be any power series convergent at `π̂`; the version
here requires `𝒟` to have finitely many monomials (a polynomial). The classes of
Part V have at most six atoms, but this package does not check that every
discount used there is a polynomial. The class bounds in auxiliary prices of
(CP5) enter (ii) only through the number `Ψ ≥ ∑_ω b_ω`; the degree-class
replacement (v) is in `Sarkozy/RecordExpansion/Replacement.lean`.
-/

@[expose] public section

open Finset Filter
open scoped BigOperators Topology Nat

namespace Sarkozy.RecordExpansion

open Choice

section Series

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)]

/-- The price variables `x^ε_{b,t}`: one for every atom, record and type. -/
abbrev PriceVar (T : J → Type*) := Σ b : J, T b × ChangeType

/-- The point of the price variables given by prices `π^ε_{b,t}`. -/
def priceVec (π : ∀ b, T b → ChangeType → ℝ) (v : PriceVar T) : ℝ := π v.1 v.2.1 v.2.2

/-- The sign of a variable: `-1` for a skew variable, `1` for a symmetric one. -/
def varSign (v : PriceVar T) : ℝ := if v.2.2 = .skew then -1 else 1

/-- The monomial `x^n = ∏_v x_v^{n_v}`. -/
def mono (x : PriceVar T → ℝ) (n : PriceVar T → ℕ) : ℝ := ∏ v, x v ^ n v

/-- `n! = ∏_v n_v!`. -/
def mfact (n : PriceVar T → ℕ) : ℕ := ∏ v, (n v)!

/-- The degree of a monomial in the skew variables. -/
def skewDeg (n : PriceVar T → ℕ) : ℕ := ∑ v, if v.2.2 = .skew then n v else 0

/-- The coefficient of `x^n` in `e^{S(x)} cosh A(x) - 1`: `1/n!` on the nonconstant
monomials of even skew degree, `0` on the others. -/
noncomputable def expCoeff (n : PriceVar T → ℕ) : ℝ :=
  if n ≠ 0 ∧ Even (skewDeg n) then 1 / (mfact n : ℝ) else 0

/-- `S(x) = ∑ x^s_{b,t}`. -/
def symSum (x : PriceVar T → ℝ) : ℝ := ∑ v, if v.2.2 = .skew then 0 else x v

/-- `A(x) = ∑ x^a_{b,t}`. -/
def skewSum (x : PriceVar T → ℝ) : ℝ := ∑ v, if v.2.2 = .skew then x v else 0

/-- The multi-indices with all exponents below `K`. -/
def box (K : ℕ) : Finset (PriceVar T → ℕ) := Fintype.piFinset fun _ => range K

/-- The truncation of `e^{S(x)} cosh A(x) - 1` to exponents below `K`. -/
noncomputable def truncExp (K : ℕ) (x : PriceVar T → ℝ) : ℝ :=
  ∑ n ∈ box K, expCoeff n * mono x n

/-- The partial sum `∑_{k < K} y^k / k!` of the exponential series. -/
noncomputable def expPartial (K : ℕ) (y : ℝ) : ℝ := ∑ k ∈ range K, y ^ k / (k ! : ℝ)

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem expCoeff_nonneg (n : PriceVar T → ℕ) : 0 ≤ expCoeff n := by
  unfold expCoeff
  split_ifs
  · positivity
  · exact le_rfl

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem mono_nonneg {x : PriceVar T → ℝ} (hx : ∀ v, 0 ≤ x v) (n : PriceVar T → ℕ) :
    0 ≤ mono x n :=
  prod_nonneg fun v _ => pow_nonneg (hx v) _

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem mono_le_mono {x y : PriceVar T → ℝ} (hx : ∀ v, 0 ≤ x v) (hxy : ∀ v, x v ≤ y v)
    (n : PriceVar T → ℕ) : mono x n ≤ mono y n :=
  Finset.prod_le_prod₀ (fun v _ => pow_nonneg (hx v) _)
    (fun v _ => pow_le_pow_left₀ (hx v) (hxy v) _)

theorem prod_expPartial (K : ℕ) (s x : PriceVar T → ℝ) :
    ∏ v, expPartial K (s v * x v) =
      ∑ n ∈ box K, (∏ v, s v ^ n v) * mono x n / (mfact n : ℝ) := by
  unfold expPartial box
  rw [Finset.prod_univ_sum]
  apply Finset.sum_congr rfl
  intro n _
  unfold mono mfact
  rw [Nat.cast_prod, ← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro v _
  rw [mul_pow]

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem prod_varSign_pow (n : PriceVar T → ℕ) :
    ∏ v, varSign v ^ n v = (-1 : ℝ) ^ skewDeg n := by
  unfold varSign skewDeg
  rw [← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro v _
  split_ifs
  · rfl
  · rw [one_pow, pow_zero]

/-- **Closed form of the truncation**: for `K ≥ 1`,
`truncExp K x = ½[∏_v P_K(x_v) + ∏_v P_K(±x_v)] - 1`, the sign being `-` on the
skew variables and `P_K` the partial sum of the exponential series. -/
theorem truncExp_eq (K : ℕ) (hK : 1 ≤ K) (x : PriceVar T → ℝ) :
    truncExp K x =
      (∏ v, expPartial K (x v) + ∏ v, expPartial K (varSign v * x v)) / 2 - 1 := by
  have h1 := prod_expPartial K (fun _ => 1) x
  simp only [one_mul, one_pow, prod_const_one] at h1
  have h2 := prod_expPartial K varSign x
  simp_rw [prod_varSign_pow] at h2
  rw [h1, h2, ← sum_add_distrib, sum_div]
  have h0 : (0 : PriceVar T → ℕ) ∈ box K := by
    simp only [box, Fintype.mem_piFinset, mem_range, Pi.zero_apply]
    intro _
    omega
  have hterm (n : PriceVar T → ℕ) :
      (mono x n / (mfact n : ℝ) + (-1 : ℝ) ^ skewDeg n * mono x n / (mfact n : ℝ)) / 2 =
        expCoeff n * mono x n + if n = 0 then 1 else 0 := by
    unfold expCoeff
    by_cases hn : n = 0
    · subst hn
      simp [mono, mfact, skewDeg]
    · by_cases he : Even (skewDeg n)
      · rw [he.neg_one_pow]
        simp only [ne_eq, hn, not_false_eq_true, he, and_self, ↓reduceIte, add_zero]
        ring
      · rw [(Nat.not_even_iff_odd.mp he).neg_one_pow]
        simp only [ne_eq, hn, not_false_eq_true, he, and_false, ↓reduceIte, add_zero]
        ring
  simp_rw [hterm]
  rw [sum_add_distrib, Finset.sum_ite_eq' (box K) 0 (fun _ => (1 : ℝ))]
  simp only [h0, ↓reduceIte]
  unfold truncExp
  ring

theorem tendsto_expPartial (y : ℝ) :
    Tendsto (fun K => expPartial K y) atTop (𝓝 (Real.exp y)) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) y
  rw [← Real.exp_eq_exp_ℝ] at h
  exact h.tendsto_sum_nat

/-- The truncations converge to `e^{S(x)} cosh A(x) - 1`. -/
theorem tendsto_truncExp (x : PriceVar T → ℝ) :
    Tendsto (fun K => truncExp K x) atTop
      (𝓝 (Real.exp (symSum x) * Real.cosh (skewSum x) - 1)) := by
  have hP : Tendsto (fun K => ∏ v, expPartial K (x v)) atTop (𝓝 (∏ v, Real.exp (x v))) :=
    tendsto_finsetProd _ fun v _ => tendsto_expPartial (x v)
  have hM : Tendsto (fun K => ∏ v, expPartial K (varSign v * x v)) atTop
      (𝓝 (∏ v, Real.exp (varSign v * x v))) :=
    tendsto_finsetProd _ fun v _ => tendsto_expPartial _
  have hlim := ((hP.add hM).div_const 2).sub_const 1
  have h1 : ∑ v, x v = symSum x + skewSum x := by
    unfold symSum skewSum
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    split_ifs <;> ring
  have h2 : ∑ v, varSign v * x v = symSum x + -skewSum x := by
    unfold symSum skewSum varSign
    rw [← sum_neg_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro v _
    split_ifs <;> ring
  have he : (∏ v, Real.exp (x v) + ∏ v, Real.exp (varSign v * x v)) / 2 - 1 =
      Real.exp (symSum x) * Real.cosh (skewSum x) - 1 := by
    rw [← Real.exp_sum, ← Real.exp_sum, h1, h2, Real.exp_add, Real.exp_add, Real.cosh_eq]
    ring
  rw [he] at hlim
  apply hlim.congr'
  filter_upwards [eventually_ge_atTop 1] with K hK
  exact (truncExp_eq K hK x).symm

theorem box_mono {K L : ℕ} (h : K ≤ L) : (box K : Finset (PriceVar T → ℕ)) ⊆ box L := by
  intro n hn
  simp only [box, Fintype.mem_piFinset, mem_range] at hn ⊢
  intro v
  exact lt_of_lt_of_le (hn v) h

theorem truncExp_mono {x : PriceVar T → ℝ} (hx : ∀ v, 0 ≤ x v) :
    Monotone fun K => truncExp K x := by
  intro K L hKL
  apply sum_le_sum_of_subset_of_nonneg (box_mono hKL)
  intro n _ _
  exact mul_nonneg (expCoeff_nonneg n) (mono_nonneg hx n)

theorem truncExp_le {x : PriceVar T → ℝ} (hx : ∀ v, 0 ≤ x v) (K : ℕ) :
    truncExp K x ≤ Real.exp (symSum x) * Real.cosh (skewSum x) - 1 :=
  (truncExp_mono hx).ge_of_tendsto (tendsto_truncExp x) K

theorem exists_box (G : Finset (PriceVar T → ℕ)) : ∃ K, G ⊆ box K := by
  refine ⟨∑ n ∈ G, ∑ v, n v + 1, ?_⟩
  intro n hn
  simp only [box, Fintype.mem_piFinset, mem_range]
  intro v
  have h1 : n v ≤ ∑ w, n w := Finset.single_le_sum (fun w _ => Nat.zero_le _) (mem_univ v)
  have h2 : ∑ w, n w ≤ ∑ m ∈ G, ∑ w, m w :=
    Finset.single_le_sum (f := fun m : PriceVar T → ℕ => ∑ w, m w) (fun m _ => Nat.zero_le _) hn
  omega

/-- **Finite partial sums of `e^{S(x)} cosh A(x) - 1`**: for `x ≥ 0` and any finite
set `G` of monomials, `∑_{n ∈ G} c_n x^n ≤ e^{S(x)} cosh A(x) - 1`. -/
theorem sum_expCoeff_le {x : PriceVar T → ℝ} (hx : ∀ v, 0 ≤ x v)
    (G : Finset (PriceVar T → ℕ)) :
    ∑ n ∈ G, expCoeff n * mono x n ≤ Real.exp (symSum x) * Real.cosh (skewSum x) - 1 := by
  obtain ⟨K, hK⟩ := exists_box G
  calc ∑ n ∈ G, expCoeff n * mono x n ≤ truncExp K x :=
        sum_le_sum_of_subset_of_nonneg hK
          (fun n _ _ => mul_nonneg (expCoeff_nonneg n) (mono_nonneg hx n))
    _ ≤ _ := truncExp_le hx K

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem symSum_priceVec (π : ∀ b, T b → ChangeType → ℝ) :
    symSum (priceVec π) = ∑ b, symTotal π b := by
  unfold symSum priceVec symTotal
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro t _
  rw [sum_changeType]
  simp

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
theorem skewSum_priceVec (π : ∀ b, T b → ChangeType → ℝ) :
    skewSum (priceVec π) = ∑ b, skewTotal π b := by
  unfold skewSum priceVec skewTotal
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  rw [Fintype.sum_prod_type]
  apply sum_congr rfl
  intro t _
  rw [sum_changeType]
  simp

end Series

/-! ### Monomials of selections -/

section SelectionMonomials

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)]

/-- The monomial `x^{n(ω)}` of a choice: exponent one at the variables
`x^{ε_b}_{b,t_b}` of its atoms, zero elsewhere. -/
def selMono (ω : Choice T) : PriceVar T → ℕ := fun v => if ω v.1 = some v.2 then 1 else 0

omit [DecidableEq J] in
theorem mono_selMono (π : ∀ b, T b → ChangeType → ℝ) (ω : Choice T) :
    mono (priceVec π) (selMono ω) = monomial π ω := by
  unfold mono monomial selMono priceVec
  rw [Fintype.prod_sigma]
  apply prod_congr rfl
  intro b _
  change (∏ p : T b × ChangeType, π b p.1 p.2 ^ (if ω b = some p then 1 else 0)) =
    entryPrice (π b) (ω b)
  rcases ω b with _ | ⟨t, e⟩
  · simp [entryPrice]
  · have he : ∀ q : T b × ChangeType,
        π b q.1 q.2 ^ (if some (t, e) = some q then 1 else 0) =
          if (t, e) = q then π b q.1 q.2 else 1 := by
      intro q
      by_cases hq : (t, e) = q
      · subst hq
        simp
      · have hq' : some (t, e) ≠ some q := fun h => hq (Option.some.inj h)
        simp [hq, hq']
    rw [Finset.prod_congr rfl (fun q _ => he q), Fintype.prod_ite_eq]
    rfl

omit [DecidableEq J] in
theorem mfact_selMono (ω : Choice T) : mfact (selMono ω) = 1 := by
  unfold mfact selMono
  apply prod_eq_one
  intro v _
  split_ifs <;> rfl

omit [DecidableEq J] in
theorem skewDeg_selMono (ω : Choice T) : skewDeg (selMono ω) = skewCount ω := by
  unfold skewDeg selMono skewCount
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  change (∑ p : T b × ChangeType,
      if p.2 = ChangeType.skew then (if ω b = some p then 1 else 0) else 0) =
    if isSkewEntry (ω b) = true then 1 else 0
  rcases ω b with _ | ⟨t, e⟩
  · simp [isSkewEntry]
  · rw [Finset.sum_eq_single (t, e)]
    · cases e <;> simp [isSkewEntry]
    · intro q _ hq
      have hq' : some (t, e) ≠ some q := fun h => hq (Option.some.inj h).symm
      simp [hq']
    · intro h'
      exact absurd (mem_univ _) h'

omit [Fintype J] [DecidableEq J] [∀ b, Fintype (T b)] in
theorem selMono_eq_zero_iff (ω : Choice T) : selMono ω = 0 ↔ ω = Choice.empty := by
  constructor
  · intro h
    funext b
    rcases hb : ω b with _ | p
    · rfl
    · have h1 := congrFun h ⟨b, p⟩
      simp [selMono, hb] at h1
  · rintro rfl
    funext v
    simp [selMono, Choice.empty]

omit [Fintype J] [DecidableEq J] [∀ b, Fintype (T b)] in
theorem selMono_injective : Function.Injective (selMono (T := T)) := by
  intro ω ω' h
  funext b
  have key : ∀ p : T b × ChangeType, ω b = some p ↔ ω' b = some p := by
    intro p
    have h1 := congrFun h ⟨b, p⟩
    simp only [selMono] at h1
    by_cases hp : ω b = some p <;> by_cases hp' : ω' b = some p <;> simp_all
  rcases hb : ω b with _ | p
  · rcases hb' : ω' b with _ | p'
    · rfl
    · have h2 := (key p').mpr hb'
      rw [hb] at h2
      exact absurd h2 (by simp)
  · exact ((key p).mp hb).symm

omit [DecidableEq J] in
theorem expCoeff_selMono {ω : Choice T} (hω : IsSelection ω) : expCoeff (selMono ω) = 1 := by
  have hne : selMono ω ≠ 0 := fun h => hω.1 ((selMono_eq_zero_iff ω).mp h)
  have hev : Even (skewDeg (selMono ω)) := by
    rw [skewDeg_selMono]
    exact hω.2
  unfold expCoeff
  simp only [ne_eq, hne, not_false_eq_true, hev, and_self, ↓reduceIte, mfact_selMono,
    Nat.cast_one, div_one]

end SelectionMonomials

/-! ### Completion (`lem:record:record-expansion` (iv)) -/

section Completion

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)]

/-- The coefficient conditions of (iv) give `d_n ≤ B' c_n` on every monomial when the
costs of the selections are nonnegative. -/
theorem coeff_le_of_completion {B' : ℝ} (cost : Choice T → ℝ)
    (hcost : ∀ ω, IsSelection ω → 0 ≤ cost ω) (d : (PriceVar T → ℕ) → ℝ)
    (hsel : ∀ ω, IsSelection ω → d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ n, (∀ ω, IsSelection ω → selMono ω ≠ n) → d n ≤ B' * expCoeff n)
    (n : PriceVar T → ℕ) : d n ≤ B' * expCoeff n := by
  by_cases hn : ∃ ω, IsSelection ω ∧ selMono ω = n
  · obtain ⟨ω, hω, rfl⟩ := hn
    rw [expCoeff_selMono hω, mul_one]
    linarith [hsel ω hω, hcost ω hω]
  · simp only [not_exists, not_and] at hn
    exact hoth n hn

/-- **Completion at the actual prices** (`lem:record:record-expansion` (iv)). Let
`𝒟(x) = ∑_{n ∈ supp} d_n x^n` with `d_n ≥ 0`, `d_n ≤ B' - c_ω` on the monomial of
every selection `ω` and `d_n ≤ B' c_n` on every other monomial (`c_n` the
coefficient of `e^{S(x)} cosh A(x) - 1`). Then for nonnegative prices
`∑_ω c_ω π_ω + 𝒟(π) ≤ B'(e^S cosh A - 1)`. -/
theorem sum_cost_add_poly_le {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (cost : Choice T → ℝ) {B' : ℝ} (hB' : 0 ≤ B') (supp : Finset (PriceVar T → ℕ))
    (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hsel : ∀ ω, IsSelection ω → d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ n, (∀ ω, IsSelection ω → selMono ω ≠ n) → d n ≤ B' * expCoeff n) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), cost ω * monomial π ω +
        ∑ n ∈ supp, d n * mono (priceVec π) n ≤
      B' * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) := by
  rw [← symSum_priceVec, ← skewSum_priceVec]
  set x := priceVec π with hxdef
  have hx : ∀ v, 0 ≤ x v := fun v => hπ _ _ _
  set sel := univ.filter (fun ω : Choice T => IsSelection ω) with hseldef
  set M := sel.image selMono with hMdef
  set G := supp ∪ M with hGdef
  have hinj : Set.InjOn selMono (sel : Set (Choice T)) :=
    fun a _ b _ h => selMono_injective h
  have hMG : M ⊆ G := subset_union_right
  have h1 : ∑ n ∈ supp, d n * mono x n ≤ ∑ n ∈ G, d n * mono x n :=
    sum_le_sum_of_subset_of_nonneg subset_union_left
      (fun n _ _ => mul_nonneg (hd n) (mono_nonneg hx n))
  have h2 : ∑ n ∈ G, d n * mono x n =
      ∑ n ∈ G \ M, d n * mono x n + ∑ n ∈ M, d n * mono x n := (sum_sdiff hMG).symm
  have h3 : ∑ n ∈ M, d n * mono x n = ∑ ω ∈ sel, d (selMono ω) * monomial π ω := by
    rw [hMdef, sum_image hinj]
    apply sum_congr rfl
    intro ω _
    rw [hxdef, mono_selMono]
  have h4 : ∑ n ∈ G, expCoeff n * mono x n =
      ∑ n ∈ G \ M, expCoeff n * mono x n + ∑ ω ∈ sel, monomial π ω := by
    rw [← sum_sdiff hMG, hMdef, sum_image hinj]
    congr 1
    apply sum_congr rfl
    intro ω hω
    rw [expCoeff_selMono (mem_filter.mp hω).2, hxdef, mono_selMono, one_mul]
  have h5 : ∑ n ∈ G \ M, d n * mono x n ≤ ∑ n ∈ G \ M, B' * (expCoeff n * mono x n) := by
    apply sum_le_sum
    intro n hn
    have hnM : ∀ ω, IsSelection ω → selMono ω ≠ n := by
      intro ω hω heq
      apply (mem_sdiff.mp hn).2
      rw [← heq, hMdef]
      exact mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, hω⟩)
    have h := hoth n hnM
    calc d n * mono x n ≤ B' * expCoeff n * mono x n :=
          mul_le_mul_of_nonneg_right h (mono_nonneg hx n)
      _ = B' * (expCoeff n * mono x n) := by ring
  have h6 : ∑ ω ∈ sel, (cost ω * monomial π ω + d (selMono ω) * monomial π ω) ≤
      ∑ ω ∈ sel, B' * monomial π ω := by
    apply sum_le_sum
    intro ω hω
    have h := hsel ω (mem_filter.mp hω).2
    have hm := monomial_nonneg hπ ω
    have h' : (cost ω + d (selMono ω)) * monomial π ω ≤ B' * monomial π ω :=
      mul_le_mul_of_nonneg_right (by linarith) hm
    linarith
  have h7 := sum_expCoeff_le hx G
  calc ∑ ω ∈ sel, cost ω * monomial π ω + ∑ n ∈ supp, d n * mono x n
      ≤ ∑ ω ∈ sel, cost ω * monomial π ω + ∑ n ∈ G, d n * mono x n := by linarith
    _ = ∑ n ∈ G \ M, d n * mono x n +
          ∑ ω ∈ sel, (cost ω * monomial π ω + d (selMono ω) * monomial π ω) := by
        rw [h2, h3, sum_add_distrib]
        ring
    _ ≤ ∑ n ∈ G \ M, B' * (expCoeff n * mono x n) + ∑ ω ∈ sel, B' * monomial π ω :=
        add_le_add h5 h6
    _ = B' * ∑ n ∈ G, expCoeff n * mono x n := by
        rw [h4, mul_add, mul_sum, mul_sum]
    _ ≤ B' * (Real.exp (symSum x) * Real.cosh (skewSum x) - 1) :=
        mul_le_mul_of_nonneg_left h7 hB'

/-- Completion at the actual prices, in the form `∑_ω c_ω π_ω ≤ B'(e^S cosh A - 1) - 𝒟(π)`. -/
theorem sum_cost_le_completion {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (cost : Choice T → ℝ) {B' : ℝ} (hB' : 0 ≤ B') (supp : Finset (PriceVar T → ℕ))
    (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hsel : ∀ ω, IsSelection ω → d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ n, (∀ ω, IsSelection ω → selMono ω ≠ n) → d n ≤ B' * expCoeff n) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), cost ω * monomial π ω ≤
      B' * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) -
        ∑ n ∈ supp, d n * mono (priceVec π) n := by
  have h := sum_cost_add_poly_le hπ cost hB' supp d hd hsel hoth
  linarith

/-- **Monotonicity of the completed polynomial** (`lem:record:record-expansion` (iii)):
if every coefficient satisfies `d_n ≤ B' c_n`, then
`Ψ(x) = B'(e^{S(x)} cosh A(x) - 1) - 𝒟(x)` is nondecreasing on `x ≥ 0`, its power
series having nonnegative coefficients. -/
theorem completion_mono {B' : ℝ} (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ)
    (hd : ∀ n, 0 ≤ d n) (hcoeff : ∀ n, d n ≤ B' * expCoeff n) {x y : PriceVar T → ℝ} (hx : ∀ v, 0 ≤ x v)
    (hxy : ∀ v, x v ≤ y v) :
    B' * (Real.exp (symSum x) * Real.cosh (skewSum x) - 1) - ∑ n ∈ supp, d n * mono x n ≤
      B' * (Real.exp (symSum y) * Real.cosh (skewSum y) - 1) - ∑ n ∈ supp, d n * mono y n := by
  obtain ⟨K0, hK0⟩ := exists_box supp
  have hy : ∀ v, 0 ≤ y v := fun v => (hx v).trans (hxy v)
  have hlim (z : PriceVar T → ℝ) :
      Tendsto (fun K => B' * truncExp K z - ∑ n ∈ supp, d n * mono z n) atTop
        (𝓝 (B' * (Real.exp (symSum z) * Real.cosh (skewSum z) - 1) -
          ∑ n ∈ supp, d n * mono z n)) :=
    ((tendsto_truncExp z).const_mul B').sub_const _
  apply le_of_tendsto_of_tendsto (hlim x) (hlim y)
  filter_upwards [eventually_ge_atTop K0] with K hK
  have hsub : supp ⊆ box K := hK0.trans (box_mono hK)
  have hexp (z : PriceVar T → ℝ) : B' * truncExp K z - ∑ n ∈ supp, d n * mono z n =
      ∑ n ∈ box K, (B' * expCoeff n - if n ∈ supp then d n else 0) * mono z n := by
    have hs : ∑ n ∈ supp, d n * mono z n =
        ∑ n ∈ box K, (if n ∈ supp then d n else 0) * mono z n := by
      simp_rw [ite_mul, zero_mul]
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hsub]
    rw [hs, truncExp, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    ring
  rw [hexp x, hexp y]
  apply sum_le_sum
  intro n _
  have hc : 0 ≤ B' * expCoeff n - if n ∈ supp then d n else 0 := by
    have h1 := hcoeff n
    have h2 := hd n
    split_ifs <;> linarith
  exact mul_le_mul_of_nonneg_left (mono_le_mono hx hxy n) hc


/-- **Completion at upper prices** (`lem:record:record-expansion` (iv)): for
nonnegative costs `c_ω` of the selections and upper prices `π̂ ≥ π ≥ 0`,
`∑_ω c_ω π_ω ≤ B'(e^Ŝ cosh Â - 1) - 𝒟(π̂)`, with `Ŝ`, `Â` the totals of `π̂`. -/
theorem sum_cost_le_completion_upper {π πu : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (hle : ∀ b t e, π b t e ≤ πu b t e)
    (cost : Choice T → ℝ) (hcost : ∀ ω, IsSelection ω → 0 ≤ cost ω) {B' : ℝ} (hB' : 0 ≤ B')
    (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hsel : ∀ ω, IsSelection ω → d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ n, (∀ ω, IsSelection ω → selMono ω ≠ n) → d n ≤ B' * expCoeff n) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), cost ω * monomial π ω ≤
      B' * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) -
        ∑ n ∈ supp, d n * mono (priceVec πu) n := by
  have h1 := sum_cost_le_completion hπ cost hB' supp d hd hsel hoth
  have h2 := completion_mono supp d hd (coeff_le_of_completion cost hcost d hsel hoth)
    (x := priceVec π) (y := priceVec πu) (fun v => hπ _ _ _) (fun v => hle _ _ _)
  rw [symSum_priceVec, skewSum_priceVec, symSum_priceVec, skewSum_priceVec] at h2
  linarith

end Completion

/-! ### Classes (`lem:record:record-expansion` (ii)) -/

section Classes

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]

/-- The bound `b_ω` of (ii): the class bound `φ_ω` of a selection in a class,
and `B π_ω` for a selection in no class. -/
def classBound {ι : Type*} (cls : Choice T → Option ι) (phi : Choice T → ℝ) (Bf : ℝ)
    (π : ∀ b, T b → ChangeType → ℝ) (ω : Choice T) : ℝ :=
  (cls ω).elim (Bf * monomial π ω) fun _ => phi ω

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
/-- **Class sums** (proof of `lem:record:record-expansion` (ii)). The classes are
the fibres of `cls : Choice T → Option ι` (`none`: in no class), hence pairwise
disjoint. If every class satisfies the class bound of (CP5),
`∑_{ω ∈ 𝒞} |I_ω| ≤ ∑_{ω ∈ 𝒞} ((φ_ω + z π_ω) Y + r_ω)`, and every selection in no
class satisfies `|I_ω| ≤ (B + z) π_ω Y + r_ω`, then
`∑_ω |I_ω| ≤ ∑_ω ((b_ω + z π_ω) Y + r_ω)` over all selections. -/
theorem sum_abs_le_of_classes [DecidableEq J] [∀ b, DecidableEq (T b)] {ι : Type*} [Fintype ι]
    [DecidableEq ι] (cls : Choice T → Option ι) (I phi : Choice T → ℝ)
    {π : ∀ b, T b → ChangeType → ℝ} {Bf z Y : ℝ} (r : Choice T → ℝ)
    (hfree : ∀ ω, IsSelection ω → cls ω = none →
      |I ω| ≤ (Bf + z) * monomial π ω * Y + r ω)
    (hclass : ∀ i, ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter
        (fun ω => cls ω = some i), |I ω| ≤
      ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter (fun ω => cls ω = some i),
        ((phi ω + z * monomial π ω) * Y + r ω)) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), |I ω| ≤
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω),
        ((classBound cls phi Bf π ω + z * monomial π ω) * Y + r ω) := by
  rw [← Finset.sum_fiberwise _ cls, ← Finset.sum_fiberwise _ cls, Fintype.sum_option,
    Fintype.sum_option]
  apply add_le_add
  · apply sum_le_sum
    intro ω hω
    rw [mem_filter] at hω
    have h := hfree ω (mem_filter.mp hω.1).2 hω.2
    have he : classBound cls phi Bf π ω = Bf * monomial π ω := by
      rw [classBound, hω.2]
      rfl
    rw [he]
    calc |I ω| ≤ (Bf + z) * monomial π ω * Y + r ω := h
      _ = (Bf * monomial π ω + z * monomial π ω) * Y + r ω := by ring
  · apply sum_le_sum
    intro i _
    refine (hclass i).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro ω hω
    rw [mem_filter] at hω
    have he : classBound cls phi Bf π ω = phi ω := by
      rw [classBound, hω.2]
      rfl
    rw [he]

/-- **Complete bound, evaluated** (`lem:record:record-expansion` (ii)): if the
terms satisfy `∑_ω |I_ω| ≤ ∑_ω ((b_ω + z π_ω) Y + r_ω)` and `Ψ ≥ ∑_ω b_ω` (for
instance the value at upper prices of a complete polynomial), then
`|Y_ν - Y_λ| ≤ (Ψ + z (e^S cosh A - 1)) Y + ∑_ω r_ω`. -/
theorem abs_energy_sub_le_of_complete (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ)
    {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e) {z Y Ψ : ℝ}
    (hz : 0 ≤ z) (hY : 0 ≤ Y) (bω r : Choice T → ℝ)
    (hsum : ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), |term lam ζ F ω| ≤
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω),
        ((bω ω + z * monomial π ω) * Y + r ω))
    (hΨ : ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), bω ω ≤ Ψ) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (Ψ + z * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1)) * Y +
        ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), r ω := by
  rw [energy_sub_eq_sum_selections c hν hlam hs ha F]
  set sel := univ.filter (fun ω : Choice T => IsSelection ω)
  have hmono := sum_monomial_selections_le (T := T) hπ
  have he : ∑ ω ∈ sel, ((bω ω + z * monomial π ω) * Y + r ω) =
      (∑ ω ∈ sel, bω ω) * Y + z * (∑ ω ∈ sel, monomial π ω) * Y + ∑ ω ∈ sel, r ω := by
    rw [sum_add_distrib, ← sum_mul, sum_add_distrib, ← mul_sum]
    ring
  have h1 := mul_le_mul_of_nonneg_right hΨ hY
  have h2 := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmono hz) hY
  calc |∑ ω ∈ sel, term lam ζ F ω| ≤ ∑ ω ∈ sel, |term lam ζ F ω| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := hsum
    _ = _ := he
    _ ≤ _ := by nlinarith

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
/-- `e^S cosh A` is nondecreasing in the prices. -/
theorem exp_cosh_mono {π πu : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (hle : ∀ b t e, π b t e ≤ πu b t e) :
    Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) ≤
      Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) := by
  have hS : ∑ b, symTotal π b ≤ ∑ b, symTotal πu b :=
    sum_le_sum fun b _ => sum_le_sum fun t _ => hle b t _
  have hA0 : 0 ≤ ∑ b, skewTotal π b := sum_nonneg fun b _ => sum_nonneg fun t _ => hπ b t _
  have hA : ∑ b, skewTotal π b ≤ ∑ b, skewTotal πu b :=
    sum_le_sum fun b _ => sum_le_sum fun t _ => hle b t _
  have hc : Real.cosh (∑ b, skewTotal π b) ≤ Real.cosh (∑ b, skewTotal πu b) := by
    rw [Real.cosh_le_cosh, abs_of_nonneg hA0, abs_of_nonneg (hA0.trans hA)]
    exact hA
  exact mul_le_mul (Real.exp_le_exp.mpr hS) hc (Real.cosh_pos _).le (Real.exp_pos _).le

/-- **Reserved cost with class costs and completion** (`lem:record:record-expansion`
(ii) and (iv) combined). Selections in no class satisfy
`|I_ω| ≤ (B + z) π_ω Y + r_ω`; the class `i` (the fibre `cls ω = some i`) has the
class cost `0 ≤ c_i` and satisfies `∑_{ω ∈ 𝒞_i} |I_ω| ≤ ∑_{ω ∈ 𝒞_i}((c_i + z) π_ω Y + r_ω)`.
Let `c_ω` be the cost of `ω` (`c_i` in class `i`, `B` in no class) and let `𝒟` be a
polynomial with `0 ≤ d_n`, `d_n ≤ B' - c_ω` on the monomial of every selection and
`d_n ≤ B' c_n` on every other monomial. Then for upper prices `π̂ ≥ π ≥ 0`,
`|Y_ν - Y_λ| ≤ (B'(e^Ŝ cosh Â - 1) - 𝒟(π̂) + z (e^Ŝ cosh Â - 1)) Y + ∑_ω r_ω`. -/
theorem abs_energy_sub_le_completion (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ)
    {π πu : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (hle : ∀ b t e, π b t e ≤ πu b t e)
    {ι : Type*} [Fintype ι] [DecidableEq ι] (cls : Choice T → Option ι) (cc : ι → ℝ)
    (hcc : ∀ i, 0 ≤ cc i) {Bf z Y B' : ℝ} (hBf : 0 ≤ Bf) (hz : 0 ≤ z) (hY : 0 ≤ Y)
    (hB' : 0 ≤ B') (r : Choice T → ℝ)
    (hfree : ∀ ω, IsSelection ω → cls ω = none →
      |term lam ζ F ω| ≤ (Bf + z) * monomial π ω * Y + r ω)
    (hclass : ∀ i, ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter
        (fun ω => cls ω = some i), |term lam ζ F ω| ≤
      ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter (fun ω => cls ω = some i),
        ((cc i + z) * monomial π ω * Y + r ω))
    (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ n, 0 ≤ d n)
    (hsel : ∀ ω, IsSelection ω → d (selMono ω) ≤ B' - (cls ω).elim Bf cc)
    (hoth : ∀ n, (∀ ω, IsSelection ω → selMono ω ≠ n) → d n ≤ B' * expCoeff n) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (B' * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) -
          ∑ n ∈ supp, d n * mono (priceVec πu) n +
        z * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1)) * Y +
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), r ω := by
  set cost : Choice T → ℝ := fun ω => (cls ω).elim Bf cc with hcostdef
  have hcost : ∀ ω, IsSelection ω → 0 ≤ cost ω := by
    intro ω _
    rcases h : cls ω with _ | i
    · simp only [hcostdef, h]
      exact hBf
    · simp only [hcostdef, h]
      exact hcc i
  set phi : Choice T → ℝ := fun ω => cost ω * monomial π ω with hφdef
  have hsum := sum_abs_le_of_classes cls (term lam ζ F) phi r hfree (by
    intro i
    refine (hclass i).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro ω hω
    rw [mem_filter] at hω
    have hc : cost ω = cc i := by
      simp only [hcostdef, hω.2]
      rfl
    simp only [hφdef, hc]
    ring)
  have hb : ∀ ω, classBound cls phi Bf π ω = cost ω * monomial π ω := by
    intro ω
    rcases h : cls ω with _ | i
    · rw [classBound, h]
      simp only [hcostdef, h]
      rfl
    · rw [classBound, h]
      rfl
  have hcompl := sum_cost_le_completion_upper hπ hle cost hcost hB' supp d hd hsel hoth
  have hmain := abs_energy_sub_le_of_complete c hν hlam hs ha F hπ hz hY
    (fun ω => classBound cls phi Bf π ω) r hsum (le_refl _)
  have hmono := exp_cosh_mono hπ hle
  simp only [hb] at hmain
  have h3 : z * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) * Y ≤
      z * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) * Y := by
    apply mul_le_mul_of_nonneg_right _ hY
    apply mul_le_mul_of_nonneg_left _ hz
    linarith
  have h4 := mul_le_mul_of_nonneg_right hcompl hY
  nlinarith

/-! ### Distributing an upper total (`lem:record:record-expansion` (iii)) -/

/-- **Distribution of an upper total** (`lem:record:record-expansion` (iii)): an
upper bound `P` for the total of a nonempty finite group of nonnegative prices
`p_g` is the total of nonnegative upper prices `q_g ≥ p_g`: take
`q_g = p_g P / ∑ p` when the actual total is positive, and put `P` on one
variable when it is zero. -/
theorem exists_upper_prices {α : Type*} (G : Finset α) (hG : G.Nonempty) (p : α → ℝ)
    (hp : ∀ g ∈ G, 0 ≤ p g) {P : ℝ} (hP : ∑ g ∈ G, p g ≤ P) :
    ∃ q : α → ℝ, (∀ g ∈ G, p g ≤ q g) ∧ (∀ g ∈ G, 0 ≤ q g) ∧ ∑ g ∈ G, q g = P := by
  classical
  by_cases h0 : ∑ g ∈ G, p g = 0
  · have hz : ∀ g ∈ G, p g = 0 := (Finset.sum_eq_zero_iff_of_nonneg hp).mp h0
    have hP0 : 0 ≤ P := by linarith
    obtain ⟨g0, hg0⟩ := hG
    refine ⟨fun g => if g = g0 then P else 0, ?_, ?_, ?_⟩
    · intro g hg
      rw [hz g hg]
      show (0 : ℝ) ≤ if g = g0 then P else 0
      split_ifs
      · exact hP0
      · exact le_rfl
    · intro g _
      show (0 : ℝ) ≤ if g = g0 then P else 0
      split_ifs
      · exact hP0
      · exact le_rfl
    · rw [Finset.sum_ite_eq' G g0 (fun _ => P)]
      simp [hg0]
  · have hpos : 0 < ∑ g ∈ G, p g := lt_of_le_of_ne (sum_nonneg hp) (Ne.symm h0)
    have h1 : 1 ≤ P / ∑ g ∈ G, p g := by
      rw [le_div_iff₀ hpos]
      linarith
    refine ⟨fun g => p g * (P / ∑ g ∈ G, p g), ?_, ?_, ?_⟩
    · intro g hg
      have := hp g hg
      nlinarith
    · intro g hg
      exact mul_nonneg (hp g hg) (by linarith)
    · rw [← Finset.sum_mul]
      field_simp

end Classes

end Sarkozy.RecordExpansion

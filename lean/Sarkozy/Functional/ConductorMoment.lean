module

public import Sarkozy.Functional.SquareStep
public import Sarkozy.ProbabilityProducts
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.Ring.GeomSum

@[expose] public section

/-!
# Random depths and the conductor moment

This file formalizes the depth law of `def:hyb:coupled`(e), the one-query
conductor moment of `def:hyb:coupled`(g), and `lem:hyb:moment`
(`09_comparison_theorem.tex`).

* `depthLaw h δ`: for tails `1 = δ 0 ≥ δ 1 ≥ ⋯ ≥ δ h ≥ 0` (and `δ_{h+1} = 0`),
  the law on depths `{0, …, h}` with `Pr(J = j) = δ j - δ (j+1)`; then
  `Pr(J ≥ j) = δ j` (`depthTail_depthLaw`).
* `expect_pow_ceil_half`: the finite summation-by-parts identity
  `E z^⌈J/2⌉ = 1 + (z - 1) ∑_{l ≥ 1} z^(l-1) Pr(J ≥ 2l - 1)`, for every law of a
  depth bounded by `h` (the sum stops at `l = ⌈h/2⌉`).
* `conductorMoment_eq`: with independent depths at distinct primes `p_i`
  (the product law `FiniteLaw.pi`), `D_J = ∏ p_i^{J_i}` and `sq` the least square
  step of `SquareStep.lean`,
  `E (K sq(D_J))^w = K^w ∏_i [1 + (p_i^{2w} - 1) ∑_{l=1}^{⌈h_i/2⌉} p_i^{2w(l-1)} δ_{i,2l-1}]`.
  The identity holds for every real `w` and `K ≥ 0`; the paper states it for `w ≥ 0`.
* `conductorMoment_queries`, `conductorMoment_query`: independent identically
  distributed depth vectors at `k` queries give the `k`-th power, and the moment at
  each single query is the same expression (it does not depend on the query).
* `momentFactor_mono_exponent`, `momentFactor_mono_tails`, `one_le_momentFactor`:
  for `w ≥ 0` every factor is at least one and nondecreasing in `w` and in the tails.
* `conductorMoment_bernoulli`: the squarefree specialization of the lemma's last
  sentence, `(16K)^w ∏_{p ∣ d₀} (1 + δ_p (p^{2w} - 1))`, when the coordinate `8` is
  always fully revealed and the odd primes have Bernoulli depths.
* `isDepthTail_bernoulli_full`, `momentFactor_bernoulli_full`: Bernoulli inclusion of a
  full coordinate of depth `h` (tails `1, δ, …, δ`) contributes `1 + δ (sq(p^h)^w - 1)`;
  `depthModulus_dvd`: `D_J ∣ M₀ = ∏ p^{h_p}`.
* `depthLaw_pi_revealed`: the envelope `∏_p δ_{p,j_p}` is exactly the probability
  that all the depths `j_p` are revealed (the remark after `def:hyb:coupled`).

The transition-norm meaning of the tails (they bound the transition on the
exact-conductor spaces) is not used in these identities and is not formalized here.
No upstream code is adapted.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Functional

/-! ## Finite sums -/

theorem sum_Icc_one_sub_one {M : Type*} [AddCommMonoid M] (f : ℕ → M) (c : ℕ) :
    (∑ l ∈ Icc 1 c, f (l - 1)) = ∑ i ∈ range c, f i := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [sum_Icc_succ_top (by omega), ih, sum_range_succ]
    simp

theorem lawExpect_finset_sum {Ω ι : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (s : Finset ι) (f : ι → Ω → ℝ) :
    μ.expect (fun ω => ∑ i ∈ s, f i ω) = ∑ i ∈ s, μ.expect (f i) := by
  unfold FiniteLaw.expect
  simp_rw [mul_sum]
  exact sum_comm

/-! ## Tails and the summation-by-parts identity -/

/-- `Pr(J ≥ j)` for a law `μ` of a depth `J ∈ {0, …, h}`. -/
noncomputable def depthTail {h : ℕ} (μ : FiniteLaw (Fin (h + 1))) (j : ℕ) : ℝ :=
  μ.expect (fun J => if j ≤ (J : ℕ) then 1 else 0)

/-- The pointwise identity `z^⌈j/2⌉ = 1 + (z-1) ∑_{l=1}^{⌈h/2⌉} z^(l-1) 1[j ≥ 2l-1]`
for `j ≤ h`; here `⌈j/2⌉ = (j+1)/2`. -/
theorem pow_ceil_half_eq (z : ℝ) {h j : ℕ} (hj : j ≤ h) :
    z ^ ((j + 1) / 2) = 1 + (z - 1) *
      ∑ l ∈ Icc 1 ((h + 1) / 2), z ^ (l - 1) * (if 2 * l - 1 ≤ j then 1 else 0) := by
  have hfilter : ((Icc 1 ((h + 1) / 2)).filter fun l => 2 * l - 1 ≤ j) = Icc 1 ((j + 1) / 2) := by
    ext l
    simp only [mem_filter, mem_Icc]
    omega
  have hs : (∑ l ∈ Icc 1 ((h + 1) / 2), z ^ (l - 1) * (if 2 * l - 1 ≤ j then 1 else 0)) =
      ∑ i ∈ range ((j + 1) / 2), z ^ i := by
    simp_rw [mul_ite, mul_one, mul_zero]
    rw [← sum_filter, hfilter, sum_Icc_one_sub_one (fun i => z ^ i)]
  rw [hs, mul_comm, geom_sum_mul]
  ring

/-- `lem:hyb:moment`, the finite summation-by-parts identity: for every law of a
depth `J ≤ h` and every real `z`,
`E z^⌈J/2⌉ = 1 + (z - 1) ∑_{l=1}^{⌈h/2⌉} z^(l-1) Pr(J ≥ 2l - 1)`. The terms with
`l > ⌈h/2⌉` of the paper's sum over `l ≥ 1` vanish, since then `2l - 1 > h`. -/
theorem expect_pow_ceil_half {h : ℕ} (μ : FiniteLaw (Fin (h + 1))) (z : ℝ) :
    μ.expect (fun J => z ^ (((J : ℕ) + 1) / 2)) =
      1 + (z - 1) * ∑ l ∈ Icc 1 ((h + 1) / 2), z ^ (l - 1) * depthTail μ (2 * l - 1) := by
  have hpt : ∀ J : Fin (h + 1), z ^ (((J : ℕ) + 1) / 2) = 1 + (z - 1) *
      ∑ l ∈ Icc 1 ((h + 1) / 2), z ^ (l - 1) * (if 2 * l - 1 ≤ (J : ℕ) then 1 else 0) :=
    fun J => pow_ceil_half_eq z (Nat.lt_succ_iff.mp J.isLt)
  rw [μ.expect_congr hpt, FiniteLaw.expect_add, FiniteLaw.expect_const,
    FiniteLaw.expect_const_mul, lawExpect_finset_sum]
  congr 2
  apply sum_congr rfl
  intro l _
  rw [FiniteLaw.expect_const_mul]
  rfl

/-- The paper's terms beyond `⌈h/2⌉` vanish: `Pr(J ≥ j) = 0` for `j > h`. -/
theorem depthTail_eq_zero {h : ℕ} (μ : FiniteLaw (Fin (h + 1))) {j : ℕ} (hj : h < j) :
    depthTail μ j = 0 := by
  unfold depthTail
  have : ∀ J : Fin (h + 1), (if j ≤ (J : ℕ) then (1 : ℝ) else 0) = 0 := by
    intro J
    have := J.isLt
    rw [ite_eq_right (by omega)]
  rw [μ.expect_congr this, FiniteLaw.expect_const]

/-! ## The depth law of `def:hyb:coupled`(e) -/

/-- Admissible tails: `1 = δ 0 ≥ δ 1 ≥ ⋯ ≥ δ h ≥ 0` (`def:hyb:coupled`(e)). -/
structure IsDepthTail (h : ℕ) (δ : ℕ → ℝ) : Prop where
  zero : δ 0 = 1
  anti : ∀ j, j < h → δ (j + 1) ≤ δ j
  nonneg : 0 ≤ δ h

/-- The tails with the convention `δ_{h+1} = 0` (and `0` beyond). -/
noncomputable def extendedTail (h : ℕ) (δ : ℕ → ℝ) (j : ℕ) : ℝ := if j ≤ h then δ j else 0

theorem IsDepthTail.nonneg_le {h : ℕ} {δ : ℕ → ℝ} (hδ : IsDepthTail h δ) :
    ∀ j, j ≤ h → 0 ≤ δ j := by
  have key : ∀ k j, j + k = h → 0 ≤ δ j := by
    intro k
    induction k with
    | zero =>
      intro j hj
      have : j = h := by omega
      subst this; exact hδ.nonneg
    | succ k ih =>
      intro j hj
      exact (ih (j + 1) (by omega)).trans (hδ.anti j (by omega))
  intro j hj
  exact key (h - j) j (by omega)

theorem IsDepthTail.le_one {h : ℕ} {δ : ℕ → ℝ} (hδ : IsDepthTail h δ) :
    ∀ j, j ≤ h → δ j ≤ 1 := by
  intro j hj
  induction j with
  | zero => exact hδ.zero.le
  | succ j ih => exact (hδ.anti j (by omega)).trans (ih (by omega))

theorem extendedTail_anti {h : ℕ} {δ : ℕ → ℝ} (hδ : IsDepthTail h δ) (j : ℕ) :
    extendedTail h δ (j + 1) ≤ extendedTail h δ j := by
  unfold extendedTail
  by_cases hj : j + 1 ≤ h
  · rw [ite_eq_left hj, ite_eq_left (by omega)]
    exact hδ.anti j (by omega)
  · rw [ite_eq_right hj]
    split_ifs with hj'
    · exact hδ.nonneg_le j hj'
    · exact le_rfl

/-- The depth law: `Pr(J = j) = δ j - δ (j+1)` on `{0, …, h}`, with `δ_{h+1} = 0`. -/
noncomputable def depthLaw (h : ℕ) (δ : ℕ → ℝ) (hδ : IsDepthTail h δ) :
    FiniteLaw (Fin (h + 1)) where
  weight J := extendedTail h δ J - extendedTail h δ (J + 1)
  nonneg J := sub_nonneg.mpr (extendedTail_anti hδ J)
  total := by
    rw [Fin.sum_univ_eq_sum_range (fun j => extendedTail h δ j - extendedTail h δ (j + 1)),
      sum_range_sub']
    simp [extendedTail, hδ.zero]

/-- The depth law has the prescribed tails: `Pr(J ≥ j) = δ j` for `j ≤ h`. -/
theorem depthTail_depthLaw (h : ℕ) (δ : ℕ → ℝ) (hδ : IsDepthTail h δ) {j : ℕ} (hj : j ≤ h) :
    depthTail (depthLaw h δ hδ) j = δ j := by
  unfold depthTail FiniteLaw.expect
  simp only [mul_ite, mul_one, mul_zero]
  set t := extendedTail h δ
  have hsum : (∑ J : Fin (h + 1), if j ≤ (J : ℕ) then (depthLaw h δ hδ).weight J else 0) =
      ∑ i ∈ range (h + 1), (t (max i j) - t (max (i + 1) j)) := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => t (max i j) - t (max (i + 1) j))]
    apply sum_congr rfl
    intro J _
    by_cases hJ : j ≤ (J : ℕ)
    · rw [ite_eq_left hJ, max_eq_left hJ, max_eq_left (by omega)]
      rfl
    · rw [ite_eq_right hJ, max_eq_right (by omega), max_eq_right (by omega), sub_self]
  rw [hsum, sum_range_sub']
  simp only [Nat.zero_max, t, extendedTail]
  rw [ite_eq_left hj, max_eq_left (by omega : j ≤ h + 1), ite_eq_right (by omega), sub_zero]

/-- `lem:hyb:moment` for one prime and the depth law:
`E z^⌈J/2⌉ = 1 + (z - 1) ∑_{l=1}^{⌈h/2⌉} z^(l-1) δ_{2l-1}`. -/
theorem expect_depthLaw_pow_ceil_half (h : ℕ) (δ : ℕ → ℝ) (hδ : IsDepthTail h δ) (z : ℝ) :
    (depthLaw h δ hδ).expect (fun J => z ^ (((J : ℕ) + 1) / 2)) =
      1 + (z - 1) * ∑ l ∈ Icc 1 ((h + 1) / 2), z ^ (l - 1) * δ (2 * l - 1) := by
  rw [expect_pow_ceil_half]
  congr 2
  apply sum_congr rfl
  intro l hl
  rw [depthTail_depthLaw]
  have := mem_Icc.mp hl
  omega

/-! ## The product over primes -/

/-- One factor of `lem:hyb:moment`:
`1 + (p^{2w} - 1) ∑_{l=1}^{⌈h/2⌉} p^{2w(l-1)} δ_{2l-1}`, where `p^{2w(l-1)}` is written
`(p^{2w})^(l-1)`. -/
noncomputable def momentFactor (p h : ℕ) (δ : ℕ → ℝ) (w : ℝ) : ℝ :=
  1 + ((p : ℝ) ^ (2 * w) - 1) *
    ∑ l ∈ Icc 1 ((h + 1) / 2), ((p : ℝ) ^ (2 * w)) ^ (l - 1) * δ (2 * l - 1)

theorem rpow_two_mul_pow (x : ℝ) (hx : 0 ≤ x) (n : ℕ) (w : ℝ) :
    (x ^ (2 * n)) ^ w = (x ^ (2 * w)) ^ n := by
  rw [← Real.rpow_natCast x (2 * n), ← Real.rpow_mul hx, ← Real.rpow_mul_natCast hx]
  congr 1
  push_cast
  ring

variable {P : Type*} [Fintype P] [DecidableEq P]

/-- `D_J = ∏_p p^{J_p}` for a depth vector `J`. -/
def depthModulus (p : P → ℕ) {h : P → ℕ} (J : ∀ i, Fin (h i + 1)) : ℕ :=
  ∏ i, p i ^ (J i : ℕ)

/-- The least square step of `D_J` is `∏_p p^{2⌈J_p/2⌉}`. -/
theorem leastSquare_depthModulus (p : P → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) {h : P → ℕ} (J : ∀ i, Fin (h i + 1)) :
    leastSquare (depthModulus p J) = ∏ i, p i ^ (2 * (((J i : ℕ) + 1) / 2)) :=
  leastSquare_prod_univ_prime_pow p (fun i => (J i : ℕ)) hp hinj

/-- For independent depths at distinct primes,
`E (K sq(D_J))^w = K^w ∏_p E (p^{2w})^⌈J_p/2⌉`, for every real `w` and `K ≥ 0`. -/
theorem expect_leastSquare_rpow (p : P → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (h : P → ℕ) (μ : ∀ i, FiniteLaw (Fin (h i + 1)))
    {K : ℝ} (hK : 0 ≤ K) (w : ℝ) :
    (FiniteLaw.pi μ).expect (fun J => (K * (leastSquare (depthModulus p J) : ℝ)) ^ w) =
      K ^ w * ∏ i, (μ i).expect (fun j => ((p i : ℝ) ^ (2 * w)) ^ (((j : ℕ) + 1) / 2)) := by
  have hpt : ∀ J : ∀ i, Fin (h i + 1),
      (K * (leastSquare (depthModulus p J) : ℝ)) ^ w =
        K ^ w * ∏ i, ((p i : ℝ) ^ (2 * w)) ^ (((J i : ℕ) + 1) / 2) := by
    intro J
    rw [leastSquare_depthModulus p hp hinj J]
    push_cast
    rw [Real.mul_rpow hK (prod_nonneg fun i _ => by positivity),
      ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
    congr 1
    apply prod_congr rfl
    intro i _
    exact rpow_two_mul_pow _ (Nat.cast_nonneg _) _ w
  rw [FiniteLaw.expect_congr _ hpt, FiniteLaw.expect_const_mul,
    FiniteLaw.expect_pi_product μ
      (fun i (j : Fin (h i + 1)) => ((p i : ℝ) ^ (2 * w)) ^ (((j : ℕ) + 1) / 2))]

/-- `lem:hyb:moment` (the displayed formula). With independent depths with tails
`δ_i` at the distinct primes `p_i` (depth bounds `h_i`),
`E (K sq(D_J))^w = K^w ∏_p [1 + (p^{2w} - 1) ∑_{l=1}^{⌈h_p/2⌉} p^{2w(l-1)} δ_{p,2l-1}]`. -/
theorem conductorMoment_eq (p : P → ℕ) (hp : ∀ i, (p i).Prime)
    (hinj : Function.Injective p) (h : P → ℕ) (δ : P → ℕ → ℝ)
    (hδ : ∀ i, IsDepthTail (h i) (δ i)) {K : ℝ} (hK : 0 ≤ K) (w : ℝ) :
    (FiniteLaw.pi fun i => depthLaw (h i) (δ i) (hδ i)).expect
        (fun J => (K * (leastSquare (depthModulus p J) : ℝ)) ^ w) =
      K ^ w * ∏ i, momentFactor (p i) (h i) (δ i) w := by
  rw [expect_leastSquare_rpow p hp hinj h _ hK w]
  congr 1
  apply prod_congr rfl
  intro i _
  rw [expect_depthLaw_pow_ceil_half]
  rfl

/-- The one-query moment `E_J (K sq(D_J))^w` of `def:hyb:coupled`(g)
(the paper takes `w = 2a/d`). -/
noncomputable def oneQueryMoment (p : P → ℕ) (h : P → ℕ) (δ : P → ℕ → ℝ)
    (hδ : ∀ i, IsDepthTail (h i) (δ i)) (K w : ℝ) : ℝ :=
  (FiniteLaw.pi fun i => depthLaw (h i) (δ i) (hδ i)).expect
    (fun J => (K * (leastSquare (depthModulus p J) : ℝ)) ^ w)

/-- The depth law of `k` queries: independent copies of the per-query depth vector. -/
noncomputable def queryDepthLaw (E : Type*) [Fintype E] [DecidableEq E]
    (h : P → ℕ) (δ : P → ℕ → ℝ) (hδ : ∀ i, IsDepthTail (h i) (δ i)) :
    FiniteLaw (E → ∀ i, Fin (h i + 1)) :=
  FiniteLaw.pi fun _ : E => FiniteLaw.pi fun i => depthLaw (h i) (δ i) (hδ i)

/-- The moment at each single query `e` is the one-query moment: it does not depend
on `e` (`def:hyb:coupled`(g)). -/
theorem conductorMoment_query {E : Type*} [Fintype E] [DecidableEq E] (p : P → ℕ)
    (h : P → ℕ) (δ : P → ℕ → ℝ) (hδ : ∀ i, IsDepthTail (h i) (δ i)) (K w : ℝ) (e : E) :
    (queryDepthLaw E h δ hδ).expect
        (fun J => (K * (leastSquare (depthModulus p (J e)) : ℝ)) ^ w) =
      oneQueryMoment p h δ hδ K w :=
  FiniteLaw.expect_pi_coordinate _ e
    (fun J => (K * (leastSquare (depthModulus p J) : ℝ)) ^ w)

/-- `lem:hyb:moment`: the expectation of the product over `k = |E|` queries is the
`k`-th power of the one-query expression. -/
theorem conductorMoment_queries {E : Type*} [Fintype E] [DecidableEq E] (p : P → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (h : P → ℕ) (δ : P → ℕ → ℝ)
    (hδ : ∀ i, IsDepthTail (h i) (δ i)) {K : ℝ} (hK : 0 ≤ K) (w : ℝ) :
    (queryDepthLaw E h δ hδ).expect
        (fun J => ∏ e, (K * (leastSquare (depthModulus p (J e)) : ℝ)) ^ w) =
      (K ^ w * ∏ i, momentFactor (p i) (h i) (δ i) w) ^ Fintype.card E := by
  unfold queryDepthLaw
  rw [FiniteLaw.expect_pi_product (fun _ : E => FiniteLaw.pi fun i => depthLaw (h i) (δ i) (hδ i))
    (fun _ J => (K * (leastSquare (depthModulus p J) : ℝ)) ^ w)]
  rw [prod_const, card_univ, conductorMoment_eq p hp hinj h δ hδ hK w]

/-! ## Monotonicity -/

theorem momentFactor_eq_sum (p h : ℕ) (δ : ℕ → ℝ) (w : ℝ) :
    momentFactor p h δ w = 1 + ∑ l ∈ Icc 1 ((h + 1) / 2),
      (((p : ℝ) ^ (2 * w) - 1) * ((p : ℝ) ^ (2 * w)) ^ (l - 1)) * δ (2 * l - 1) := by
  unfold momentFactor
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro l _
  ring

theorem one_le_prime_rpow {p : ℕ} (hp : 1 ≤ p) {w : ℝ} (hw : 0 ≤ w) :
    1 ≤ (p : ℝ) ^ (2 * w) :=
  Real.one_le_rpow (by exact_mod_cast hp) (by linarith)

/-- For `w ≥ 0` and nonnegative tails, every factor is at least one. -/
theorem one_le_momentFactor {p h : ℕ} (hp : 1 ≤ p) {δ : ℕ → ℝ}
    (hδ : ∀ j, j ≤ h → 0 ≤ δ j) {w : ℝ} (hw : 0 ≤ w) : 1 ≤ momentFactor p h δ w := by
  rw [momentFactor_eq_sum]
  have hz := one_le_prime_rpow hp hw
  have : 0 ≤ ∑ l ∈ Icc 1 ((h + 1) / 2),
      (((p : ℝ) ^ (2 * w) - 1) * ((p : ℝ) ^ (2 * w)) ^ (l - 1)) * δ (2 * l - 1) := by
    apply sum_nonneg
    intro l hl
    have := mem_Icc.mp hl
    apply mul_nonneg (mul_nonneg (by linarith) (pow_nonneg (by linarith) _))
    exact hδ _ (by omega)
  linarith

/-- `lem:hyb:moment`: every factor is nondecreasing in the exponent `w ≥ 0`. -/
theorem momentFactor_mono_exponent {p h : ℕ} (hp : 1 ≤ p) {δ : ℕ → ℝ}
    (hδ : ∀ j, j ≤ h → 0 ≤ δ j) {w w' : ℝ} (hw : 0 ≤ w) (hww : w ≤ w') :
    momentFactor p h δ w ≤ momentFactor p h δ w' := by
  rw [momentFactor_eq_sum, momentFactor_eq_sum]
  have hz := one_le_prime_rpow hp hw
  have hzz : (p : ℝ) ^ (2 * w) ≤ (p : ℝ) ^ (2 * w') :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp) (by linarith)
  apply add_le_add le_rfl
  apply sum_le_sum
  intro l hl
  have := mem_Icc.mp hl
  apply mul_le_mul_of_nonneg_right _ (hδ _ (by omega))
  apply mul_le_mul (by linarith) (pow_le_pow_left₀ (by linarith) hzz _)
    (pow_nonneg (by linarith) _) (by linarith)

/-- `lem:hyb:moment`: every factor is nondecreasing in the tails (for `w ≥ 0`). -/
theorem momentFactor_mono_tails {p h : ℕ} (hp : 1 ≤ p) {δ δ' : ℕ → ℝ}
    (hδδ : ∀ j, j ≤ h → δ j ≤ δ' j) {w : ℝ} (hw : 0 ≤ w) :
    momentFactor p h δ w ≤ momentFactor p h δ' w := by
  rw [momentFactor_eq_sum, momentFactor_eq_sum]
  have hz := one_le_prime_rpow hp hw
  apply add_le_add le_rfl
  apply sum_le_sum
  intro l hl
  have := mem_Icc.mp hl
  apply mul_le_mul_of_nonneg_left (hδδ _ (by omega))
  exact mul_nonneg (by linarith) (pow_nonneg (by linarith) _)

omit [DecidableEq P] in
/-- The product of the factors is nondecreasing in the tails (for `w ≥ 0`). -/
theorem prod_momentFactor_mono_tails (p : P → ℕ) (hp : ∀ i, 1 ≤ p i) (h : P → ℕ)
    {δ δ' : P → ℕ → ℝ} (hδ : ∀ i j, j ≤ h i → 0 ≤ δ i j)
    (hδδ : ∀ i j, j ≤ h i → δ i j ≤ δ' i j) {w : ℝ} (hw : 0 ≤ w) :
    ∏ i, momentFactor (p i) (h i) (δ i) w ≤ ∏ i, momentFactor (p i) (h i) (δ' i) w :=
  prod_le_prod₀ (fun i _ => (zero_le_one.trans (one_le_momentFactor (hp i) (hδ i) hw)))
    (fun i _ => momentFactor_mono_tails (hp i) (hδδ i) hw)

omit [DecidableEq P] in
/-- The product of the factors is nondecreasing in `w ≥ 0`. -/
theorem prod_momentFactor_mono_exponent (p : P → ℕ) (hp : ∀ i, 1 ≤ p i) (h : P → ℕ)
    {δ : P → ℕ → ℝ} (hδ : ∀ i j, j ≤ h i → 0 ≤ δ i j) {w w' : ℝ} (hw : 0 ≤ w)
    (hww : w ≤ w') :
    ∏ i, momentFactor (p i) (h i) (δ i) w ≤ ∏ i, momentFactor (p i) (h i) (δ i) w' :=
  prod_le_prod₀ (fun i _ => (zero_le_one.trans (one_le_momentFactor (hp i) (hδ i) hw)))
    (fun i _ => momentFactor_mono_exponent (hp i) (hδ i) hw hww)

/-! ## The squarefree (Bernoulli) specialization -/

/-- The coordinate `8` always fully revealed (`h = 3`, all tails one) contributes
`sq(8)^w = 16^w`. -/
theorem momentFactor_eight (w : ℝ) : momentFactor 2 3 (fun _ => 1) w = (16 : ℝ) ^ w := by
  unfold momentFactor
  have hI : Icc 1 ((3 + 1) / 2) = ({1, 2} : Finset ℕ) := by decide
  rw [hI, sum_pair (by norm_num)]
  have h16 : (16 : ℝ) ^ w = ((2 : ℝ) ^ (2 * w)) ^ 2 := by
    rw [← Real.rpow_mul_natCast (by norm_num : (0 : ℝ) ≤ 2),
      show (16 : ℝ) = 2 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    push_cast
    ring
  rw [h16]
  push_cast
  ring

/-- A Bernoulli depth (`h = 1`, `Pr(J ≥ 1) = δ 1`) contributes `1 + δ_1 (p^{2w} - 1)`. -/
theorem momentFactor_bernoulli (p : ℕ) (δ : ℕ → ℝ) (w : ℝ) :
    momentFactor p 1 δ w = 1 + δ 1 * ((p : ℝ) ^ (2 * w) - 1) := by
  unfold momentFactor
  have hI : Icc 1 ((1 + 1) / 2) = ({1} : Finset ℕ) := by decide
  rw [hI, sum_singleton]
  simp only [Nat.sub_self, pow_zero, one_mul, mul_one, Nat.reduceSub]
  ring

/-- The constant tails of a coordinate that is always fully revealed. -/
theorem isDepthTail_const_one (h : ℕ) : IsDepthTail h (fun _ => 1) :=
  ⟨rfl, fun _ _ => le_rfl, zero_le_one⟩

/-- Bernoulli tails `1, δ` for a depth in `{0, 1}`. -/
noncomputable def bernoulliTail (δ : ℝ) (j : ℕ) : ℝ := if j = 0 then 1 else δ

theorem isDepthTail_bernoulli {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    IsDepthTail 1 (bernoulliTail δ) := by
  refine ⟨by simp [bernoulliTail], ?_, by simpa [bernoulliTail] using h0⟩
  intro j hj
  have : j = 0 := by omega
  subst this
  simpa [bernoulliTail] using h1

/-- Bernoulli inclusion of a full coordinate (`def:hyb:coupled`(e), last sentence: a chain
with only the constant and the full-coordinate projections): tails `1, δ, …, δ` on
`{0, …, h}`. -/
theorem isDepthTail_bernoulli_full (h : ℕ) {δ : ℝ} (h0 : 0 ≤ δ) (h1 : δ ≤ 1) :
    IsDepthTail h (bernoulliTail δ) := by
  refine ⟨by simp [bernoulliTail], ?_, ?_⟩
  · intro j _
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · simpa [bernoulliTail] using h1
    · simp [bernoulliTail, Nat.pos_iff_ne_zero.mp hj]
  · unfold bernoulliTail
    split_ifs
    · exact zero_le_one
    · exact h0

/-- The factor of a Bernoulli-included full coordinate of depth `h`:
`1 + δ ((p^{2w})^⌈h/2⌉ - 1) = 1 + δ (sq(p^h)^w - 1)`. -/
theorem momentFactor_bernoulli_full (p h : ℕ) (δ w : ℝ) :
    momentFactor p h (bernoulliTail δ) w =
      1 + δ * (((p : ℝ) ^ (2 * w)) ^ ((h + 1) / 2) - 1) := by
  unfold momentFactor
  have hs : (∑ l ∈ Icc 1 ((h + 1) / 2), ((p : ℝ) ^ (2 * w)) ^ (l - 1) * bernoulliTail δ (2 * l - 1)) =
      δ * ∑ i ∈ range ((h + 1) / 2), ((p : ℝ) ^ (2 * w)) ^ i := by
    rw [mul_sum, ← sum_Icc_one_sub_one (fun i => δ * ((p : ℝ) ^ (2 * w)) ^ i)]
    apply sum_congr rfl
    intro l hl
    have := mem_Icc.mp hl
    rw [bernoulliTail, ite_eq_right (by omega)]
    ring
  rw [hs, ← mul_assoc, mul_comm _ δ, mul_assoc, mul_comm _ (∑ i ∈ range _, _), geom_sum_mul]

omit [DecidableEq P] in
/-- `D_J` divides the external modulus `M₀ = ∏_p p^{h_p}`. -/
theorem depthModulus_dvd (p : P → ℕ) {h : P → ℕ} (J : ∀ i, Fin (h i + 1)) :
    depthModulus p J ∣ ∏ i, p i ^ h i :=
  prod_dvd_prod_of_dvd _ _ fun i _ => pow_dvd_pow (p i) (Nat.lt_succ_iff.mp (J i).isLt)

section Bernoulli

variable {P' : Type*} [Fintype P'] [DecidableEq P']

/-- The primes `2` and `q_i` (`i ∈ P'`) of `M₀ = 8 d₀`, `d₀ = ∏ q_i`. -/
def bernoulliPrimes (q : P' → ℕ) : Option P' → ℕ := fun i => i.elim 2 q

/-- The depth bounds `3` at `2` and `1` at the odd primes. -/
def bernoulliBounds : Option P' → ℕ := fun i => i.elim 3 (fun _ => 1)

/-- The tails: `8` always revealed, Bernoulli probabilities `δ_i` at the odd primes. -/
noncomputable def bernoulliTails (δ : P' → ℝ) : Option P' → ℕ → ℝ :=
  fun i => i.elim (fun _ => 1) (fun k => bernoulliTail (δ k))

omit [Fintype P'] [DecidableEq P'] in
theorem isDepthTail_bernoulliTails {δ : P' → ℝ} (hδ : ∀ i, 0 ≤ δ i ∧ δ i ≤ 1) :
    ∀ i : Option P', IsDepthTail (bernoulliBounds i) (bernoulliTails δ i)
  | none => isDepthTail_const_one 3
  | some k => isDepthTail_bernoulli (hδ k).1 (hδ k).2

omit [Fintype P'] [DecidableEq P'] in
theorem bernoulliPrimes_prime {q : P' → ℕ} (hq : ∀ i, (q i).Prime) :
    ∀ i : Option P', (bernoulliPrimes q i).Prime
  | none => Nat.prime_two
  | some k => hq k

omit [Fintype P'] [DecidableEq P'] in
theorem bernoulliPrimes_injective {q : P' → ℕ} (hodd : ∀ i, q i ≠ 2)
    (hinj : Function.Injective q) : Function.Injective (bernoulliPrimes q) := by
  intro i j hij
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some l => exact absurd hij.symm (hodd l)
  | some k =>
    cases j with
    | none => exact absurd hij (hodd k)
    | some l => exact congrArg some (hinj hij)

/-- `lem:hyb:moment`, last sentence: for the squarefree law `M₀ = 8 d₀` with `8`
always revealed and Bernoulli probabilities `δ_p` at the odd primes `p ∣ d₀`,
`E (K sq(D_J))^w = (16K)^w ∏_{p ∣ d₀} (1 + δ_p (p^{2w} - 1))`. -/
theorem conductorMoment_bernoulli (q : P' → ℕ) (hq : ∀ i, (q i).Prime)
    (hodd : ∀ i, q i ≠ 2) (hinj : Function.Injective q) (δ : P' → ℝ)
    (hδ : ∀ i, 0 ≤ δ i ∧ δ i ≤ 1) {K : ℝ} (hK : 0 ≤ K) (w : ℝ) :
    (FiniteLaw.pi fun i => depthLaw (bernoulliBounds i) (bernoulliTails δ i)
        (isDepthTail_bernoulliTails hδ i)).expect
        (fun J => (K * (leastSquare (depthModulus (bernoulliPrimes q) J) : ℝ)) ^ w) =
      (16 * K) ^ w * ∏ i, (1 + δ i * ((q i : ℝ) ^ (2 * w) - 1)) := by
  rw [conductorMoment_eq (bernoulliPrimes q) (bernoulliPrimes_prime hq)
    (bernoulliPrimes_injective hodd hinj) bernoulliBounds (bernoulliTails δ)
    (isDepthTail_bernoulliTails hδ) hK w, Fintype.prod_option]
  change K ^ w * (momentFactor 2 3 (fun _ => 1) w *
    ∏ i, momentFactor (q i) 1 (bernoulliTail (δ i)) w) = _
  rw [momentFactor_eight, Real.mul_rpow (by norm_num) hK]
  simp_rw [momentFactor_bernoulli]
  simp only [bernoulliTail, one_ne_zero, ite_false]
  ring

end Bernoulli

/-! ## The revealed envelope -/

/-- The probability that every depth `J_p` is at least `j_p` under independent depth
laws is `∏_p δ_{p,j_p}`: the envelope of the remark after `def:hyb:coupled`. -/
theorem depthLaw_pi_revealed (h : P → ℕ) (δ : P → ℕ → ℝ)
    (hδ : ∀ i, IsDepthTail (h i) (δ i)) (j : P → ℕ) (hj : ∀ i, j i ≤ h i) :
    (FiniteLaw.pi fun i => depthLaw (h i) (δ i) (hδ i)).expect
        (fun J => ∏ i, if j i ≤ (J i : ℕ) then 1 else 0) = ∏ i, δ i (j i) := by
  rw [FiniteLaw.expect_pi_product _ (fun i (J : Fin (h i + 1)) => if j i ≤ (J : ℕ) then 1 else 0)]
  apply prod_congr rfl
  intro i _
  exact depthTail_depthLaw (h i) (δ i) (hδ i) (hj i)

end Sarkozy.Functional

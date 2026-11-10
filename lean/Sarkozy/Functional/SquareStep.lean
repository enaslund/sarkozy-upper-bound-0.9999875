module

public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.Data.Nat.GCD.BigOperators
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Tactic.NormNum.GCD
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# The least square step `sq(d)`

The paper (`04_notation.tex`, equation `eq:sq`) puts, for a positive integer `d`,
`sq(d) = ∏_{p ∣ d} p ^ (2 ⌈v_p(d)/2⌉)`, the least positive square divisible by `d`.
Here `leastSquare d` is that product, written with the prime factorization of `d`;
`⌈k/2⌉` is `(k + 1) / 2` in natural-number division. For `d = 0` the empty product
gives `leastSquare 0 = 1`; the paper uses only positive `d`.

Proved here: the factorization of `leastSquare d`; `d ∣ sq(d) ∣ d²`; `sq(d)` is a
perfect square and divides every square divisible by `d` (so it is the least one);
multiplicativity on coprime factors; the prime-power and finite-product formulas;
`sq(1) = 1`, `sq(p) = p²`, `sq(8) = 16`, `sq(24) = 144`; `4 ≤ sq(d)` for `d > 1`;
coprimality is inherited from `d`; and `sq(q) = q²` for squarefree `q`, `sq(d) = d`
for a positive square `d`, `sq(p^{2m}) = p^{2m}` (the ingredients of the second form of
`eq:square-step`). No upstream code is adapted here.
-/

namespace Sarkozy.Functional

open Finset

/-- The exponent map `k ↦ 2⌈k/2⌉` of `eq:sq`. -/
def ceilEven (k : ℕ) : ℕ := 2 * ((k + 1) / 2)

@[simp] theorem ceilEven_zero : ceilEven 0 = 0 := rfl

theorem le_ceilEven (k : ℕ) : k ≤ ceilEven k := by unfold ceilEven; omega

theorem ceilEven_le_two_mul (k : ℕ) : ceilEven k ≤ 2 * k := by unfold ceilEven; omega

theorem ceilEven_eq_zero_iff (k : ℕ) : ceilEven k = 0 ↔ k = 0 := by unfold ceilEven; omega

/-- `eq:sq`: the least positive square divisible by `d`,
`sq(d) = ∏_{p ∣ d} p ^ (2 ⌈v_p(d)/2⌉)`. -/
noncomputable def leastSquare (d : ℕ) : ℕ :=
  d.factorization.prod fun p k => p ^ (2 * ((k + 1) / 2))

/-- The root `∏_{p ∣ d} p ^ ⌈v_p(d)/2⌉` of `sq(d)`. -/
noncomputable def leastSquareRoot (d : ℕ) : ℕ :=
  d.factorization.prod fun p k => p ^ ((k + 1) / 2)

theorem leastSquare_eq_root_sq (d : ℕ) : leastSquare d = leastSquareRoot d ^ 2 := by
  unfold leastSquare leastSquareRoot Finsupp.prod
  rw [← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro p _
  rw [← pow_mul, mul_comm]

/-- `sq(d)` is a perfect square. -/
theorem exists_sq_eq_leastSquare (d : ℕ) : ∃ r : ℕ, leastSquare d = r ^ 2 :=
  ⟨leastSquareRoot d, leastSquare_eq_root_sq d⟩

theorem isSquare_leastSquare (d : ℕ) : IsSquare (leastSquare d) :=
  ⟨leastSquareRoot d, by rw [leastSquare_eq_root_sq, sq]⟩

/-- The exponent vector of `sq(d)` as a finitely supported function. -/
noncomputable def leastSquareExponents (d : ℕ) : ℕ →₀ ℕ :=
  Finsupp.mapRange ceilEven ceilEven_zero d.factorization

theorem leastSquare_eq_prod_exponents (d : ℕ) :
    leastSquare d = (leastSquareExponents d).prod (· ^ ·) := by
  unfold leastSquareExponents
  rw [Finsupp.prod_mapRange_index (fun a => pow_zero a)]
  rfl

theorem leastSquareExponents_support_prime (d : ℕ) :
    ∀ p ∈ (leastSquareExponents d).support, p.Prime := by
  intro p hp
  have hs : p ∈ d.factorization.support := Finsupp.support_mapRange hp
  exact Nat.prime_of_mem_primeFactors hs

/-- The factorization of `sq(d)`: its exponent at `p` is `2 ⌈v_p(d)/2⌉`. -/
theorem factorization_leastSquare (d : ℕ) :
    (leastSquare d).factorization = leastSquareExponents d := by
  rw [leastSquare_eq_prod_exponents]
  exact Nat.prod_pow_factorization_eq_self (leastSquareExponents_support_prime d)

theorem factorization_leastSquare_apply (d p : ℕ) :
    (leastSquare d).factorization p = 2 * ((d.factorization p + 1) / 2) := by
  rw [factorization_leastSquare]
  simp only [leastSquareExponents, Finsupp.mapRange_apply, ceilEven]

theorem leastSquare_ne_zero (d : ℕ) : leastSquare d ≠ 0 := by
  rw [leastSquare_eq_prod_exponents, Finsupp.prod_ne_zero_iff]
  intro p hp
  exact pow_ne_zero _ (leastSquareExponents_support_prime d p hp).ne_zero

theorem leastSquare_pos (d : ℕ) : 0 < leastSquare d :=
  Nat.pos_of_ne_zero (leastSquare_ne_zero d)

@[simp] theorem leastSquare_zero : leastSquare 0 = 1 := by
  simp [leastSquare]

@[simp] theorem leastSquare_one : leastSquare 1 = 1 := by
  simp [leastSquare]

/-- `d ∣ sq(d)`. -/
theorem dvd_leastSquare {d : ℕ} (hd : d ≠ 0) : d ∣ leastSquare d := by
  rw [← Nat.factorization_le_iff_dvd hd (leastSquare_ne_zero d)]
  intro p
  rw [factorization_leastSquare_apply]
  omega

theorem le_leastSquare {d : ℕ} (hd : d ≠ 0) : d ≤ leastSquare d :=
  Nat.le_of_dvd (leastSquare_pos d) (dvd_leastSquare hd)

/-- `sq(d) ∣ d²`. -/
theorem leastSquare_dvd_sq (d : ℕ) : leastSquare d ∣ d ^ 2 := by
  rcases eq_or_ne d 0 with rfl | hd
  · simp
  rw [← Nat.factorization_le_iff_dvd (leastSquare_ne_zero d) (pow_ne_zero 2 hd)]
  intro p
  rw [factorization_leastSquare_apply, Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  omega

theorem leastSquare_le_sq {d : ℕ} (hd : d ≠ 0) : leastSquare d ≤ d ^ 2 :=
  Nat.le_of_dvd (by positivity) (leastSquare_dvd_sq d)

/-- Minimality: `sq(d)` divides every square divisible by `d`. -/
theorem leastSquare_dvd_of_dvd_sq {d r : ℕ} (hd : d ≠ 0) (h : d ∣ r ^ 2) :
    leastSquare d ∣ r ^ 2 := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  have hr2 : r ^ 2 ≠ 0 := pow_ne_zero 2 hr
  rw [← Nat.factorization_le_iff_dvd hd hr2] at h
  rw [← Nat.factorization_le_iff_dvd (leastSquare_ne_zero d) hr2]
  intro p
  have hp := h p
  rw [Nat.factorization_pow] at hp ⊢
  simp only [Finsupp.smul_apply, smul_eq_mul] at hp ⊢
  rw [factorization_leastSquare_apply]
  omega

/-- `sq(d)` is the least positive square divisible by `d`. -/
theorem leastSquare_le_of_dvd_sq {d r : ℕ} (hd : d ≠ 0) (hr : r ≠ 0) (h : d ∣ r ^ 2) :
    leastSquare d ≤ r ^ 2 :=
  Nat.le_of_dvd (by positivity) (leastSquare_dvd_of_dvd_sq hd h)

/-- Two numbers with the same factorization of `sq` agree. -/
theorem leastSquare_eq_of_factorization {d n : ℕ} (hn : n ≠ 0)
    (h : ∀ p, n.factorization p = 2 * ((d.factorization p + 1) / 2)) : leastSquare d = n := by
  apply Nat.eq_of_factorization_eq (leastSquare_ne_zero d) hn
  intro p
  rw [factorization_leastSquare_apply, h p]

/-- `sq(de) = sq(d) sq(e)` for coprime `d`, `e`. -/
theorem leastSquare_mul {d e : ℕ} (h : d.Coprime e) :
    leastSquare (d * e) = leastSquare d * leastSquare e := by
  apply leastSquare_eq_of_factorization
    (mul_ne_zero (leastSquare_ne_zero d) (leastSquare_ne_zero e))
  intro p
  rw [Nat.factorization_mul (leastSquare_ne_zero d) (leastSquare_ne_zero e),
    Finsupp.add_apply, factorization_leastSquare_apply, factorization_leastSquare_apply,
    Nat.factorization_mul_apply_of_coprime h]
  rcases Nat.eq_zero_or_pos (d.factorization p) with hd | hd
  · rw [hd]; omega
  · have he : e.factorization p = 0 := by
      have hpd : p ∣ d := Nat.dvd_of_factorization_pos (Nat.pos_iff_ne_zero.mp hd)
      have hpe : ¬ p ∣ e := by
        intro hpe
        have hp : p.Prime := Nat.prime_of_mem_primeFactors
          (Finsupp.mem_support_iff.mpr (Nat.pos_iff_ne_zero.mp hd))
        exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hpd h) hpe)
      exact Nat.factorization_eq_zero_of_not_dvd hpe
    rw [he]; omega

/-- `sq(p^k) = p ^ (2 ⌈k/2⌉)` for a prime `p`. -/
theorem leastSquare_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    leastSquare (p ^ k) = p ^ (2 * ((k + 1) / 2)) := by
  rw [leastSquare, hp.factorization_pow, Finsupp.prod_single_index]
  simp

/-- `sq(p) = p²` for a prime `p`. -/
theorem leastSquare_prime {p : ℕ} (hp : p.Prime) : leastSquare p = p ^ 2 := by
  simpa using leastSquare_prime_pow hp 1

/-- `sq(8) = 16`. -/
theorem leastSquare_eight : leastSquare 8 = 16 := by
  have h := leastSquare_prime_pow Nat.prime_two 3
  norm_num at h
  exact h

/-- `sq(24) = 144`. -/
theorem leastSquare_twentyFour : leastSquare 24 = 144 := by
  have h := leastSquare_mul (d := 8) (e := 3) (by norm_num [Nat.coprime_iff_gcd_eq_one])
  rw [leastSquare_eight, leastSquare_prime Nat.prime_three] at h
  norm_num at h
  exact h

/-- A perfect square bigger than one is at least four: `4 ≤ sq(d)` when `d > 1`. -/
theorem four_le_leastSquare {d : ℕ} (hd : 1 < d) : 4 ≤ leastSquare d := by
  obtain ⟨r, hr⟩ := exists_sq_eq_leastSquare d
  have hr0 : r ≠ 0 := by
    rintro rfl
    exact leastSquare_ne_zero d (by simpa using hr)
  have hr1 : r ≠ 1 := by
    rintro rfl
    have h1 : d ∣ 1 := by
      have := dvd_leastSquare (show d ≠ 0 by omega)
      simpa [hr] using this
    have := Nat.le_of_dvd one_pos h1
    omega
  have hr2 : 2 ≤ r := by omega
  rw [hr]
  nlinarith

/-- The primes of `sq(d)` are those of `d`: coprimality with `d` is inherited. -/
theorem coprime_leastSquare_of_coprime {d m : ℕ} (h : d.Coprime m) :
    (leastSquare d).Coprime m :=
  Nat.Coprime.coprime_dvd_left (leastSquare_dvd_sq d) (Nat.Coprime.pow_left 2 h)

/-- Divisibility is preserved: `d ∣ e`, `e ≠ 0` imply `sq(d) ∣ sq(e)`. -/
theorem leastSquare_dvd_leastSquare {d e : ℕ} (he : e ≠ 0) (h : d ∣ e) :
    leastSquare d ∣ leastSquare e := by
  have hd : d ≠ 0 := by rintro rfl; exact he (zero_dvd_iff.mp h)
  rw [← Nat.factorization_le_iff_dvd (leastSquare_ne_zero d) (leastSquare_ne_zero e)]
  have hle := (Nat.factorization_le_iff_dvd hd he).mpr h
  intro p
  have hp := hle p
  rw [factorization_leastSquare_apply, factorization_leastSquare_apply]
  omega

/-- The finite product formula: for distinct primes `p i` (`i ∈ s`),
`sq(∏ p_i^{k_i}) = ∏ p_i ^ (2 ⌈k_i/2⌉)`. -/
theorem leastSquare_prod_prime_pow {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (p : ι → ℕ) (k : ι → ℕ) (hp : ∀ i ∈ s, (p i).Prime) (hinj : Set.InjOn p s) :
    leastSquare (∏ i ∈ s, p i ^ k i) = ∏ i ∈ s, p i ^ (2 * ((k i + 1) / 2)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have hps : ∀ i ∈ s, (p i).Prime := fun i hi => hp i (mem_insert_of_mem hi)
    have hinjs : Set.InjOn p s := hinj.mono (by simp [Set.subset_def]; tauto)
    rw [prod_insert ha, prod_insert ha]
    have hcop : (p a ^ k a).Coprime (∏ i ∈ s, p i ^ k i) := by
      apply Nat.Coprime.prod_right
      intro i hi
      apply Nat.Coprime.pow
      rw [Nat.coprime_primes (hp a (mem_insert_self a s)) (hps i hi)]
      intro hai
      have := hinj (mem_insert_self a s) (mem_insert_of_mem hi) hai
      exact ha (this ▸ hi)
    rw [leastSquare_mul hcop, leastSquare_prime_pow (hp a (mem_insert_self a s)),
      ih hps hinjs]

/-- Version over a `Fintype` with an injective prime-valued index map. -/
theorem leastSquare_prod_univ_prime_pow {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → ℕ) (k : ι → ℕ) (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) :
    leastSquare (∏ i, p i ^ k i) = ∏ i, p i ^ (2 * ((k i + 1) / 2)) :=
  leastSquare_prod_prime_pow univ p k (fun i _ => hp i) hinj.injOn

/-- `sq(q) = q²` for squarefree `q` (used in `eq:square-step` for `q_E`). -/
theorem leastSquare_of_squarefree {q : ℕ} (hq : Squarefree q) : leastSquare q = q ^ 2 := by
  have hq0 : q ≠ 0 := by rintro rfl; exact not_squarefree_zero hq
  apply leastSquare_eq_of_factorization (pow_ne_zero 2 hq0)
  intro p
  have h1 := hq.natFactorization_le_one p
  rw [Nat.factorization_pow]
  simp only [Finsupp.smul_apply, smul_eq_mul]
  omega

/-- `sq(d) = d` for a positive perfect square `d`. -/
theorem leastSquare_of_isSquare {d : ℕ} (hd : d ≠ 0) (h : IsSquare d) : leastSquare d = d := by
  apply leastSquare_eq_of_factorization hd
  intro p
  by_cases hp : p.Prime
  · obtain ⟨k, hk⟩ := Nat.isSquare_iff_even_factorization.mp h p hp
    omega
  · simp [Nat.factorization_eq_zero_of_not_prime _ hp]

/-- `sq(r²) = r²` for `r ≠ 0`. -/
theorem leastSquare_sq {r : ℕ} (hr : r ≠ 0) : leastSquare (r ^ 2) = r ^ 2 :=
  leastSquare_of_isSquare (pow_ne_zero 2 hr) ⟨r, sq r⟩

/-- `sq(p^{2m}) = p^{2m}` for a prime `p` (the clique coordinates, `e_p = 2 m_p`). -/
theorem leastSquare_prime_pow_two_mul {p : ℕ} (hp : p.Prime) (m : ℕ) :
    leastSquare (p ^ (2 * m)) = p ^ (2 * m) := by
  rw [leastSquare_prime_pow hp]
  congr 1
  omega

end Sarkozy.Functional

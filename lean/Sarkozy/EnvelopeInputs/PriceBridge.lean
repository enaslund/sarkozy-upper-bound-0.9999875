module

public import Sarkozy.EnvelopeInputs.LiftMixed





@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.Structured Sarkozy.Functional

/-- **`sq` is multiplicative over pairwise coprime moduli**:
`sq(∏_{j ∈ E} m_j) = ∏_{j ∈ E} sq(m_j)`. -/
theorem leastSquare_prod_coprime {ι : Type*} [DecidableEq ι] (m : ι → ℕ)
    (hpair : Pairwise fun i j => (m i).Coprime (m j)) (E : Finset ι) :
    leastSquare (∏ j ∈ E, m j) = ∏ j ∈ E, leastSquare (m j) := by
  induction E using Finset.induction_on with
  | empty => simp [leastSquare_one]
  | insert i E hi ih =>
    have hcop : (m i).Coprime (∏ j ∈ E, m j) :=
      Nat.Coprime.prod_right fun j hj => hpair fun h => hi (h ▸ hj)
    rw [prod_insert hi, prod_insert hi, leastSquare_mul hcop, ih]

/-- **The price `R_E^a` for pairwise coprime moduli** (the hypothesis `hpair` of the envelope
theorems): `sq(D_E)^a = ∏_{j ∈ E} sq(m_j)^a`. -/
theorem stepR_rpow_eq_prod_coprime {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    [∀ j, NeZero (m j)] (hpair : Pairwise fun i j => (m i).Coprime (m j)) (E : Finset ι)
    (a : ℝ) :
    ((stepR m E 1 : ℕ) : ℝ) ^ a = ∏ j ∈ E, ((leastSquare (m j) : ℕ) : ℝ) ^ a := by
  unfold stepR
  rw [one_mul, leastSquare_prod_coprime m hpair E, Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun j _ => by positivity)]

/-- **`sq` of a product of distinct primes** is the product of their squares. -/
theorem leastSquare_prod_primes {ι : Type*} [DecidableEq ι] (p : ι → ℕ)
    (hp : ∀ i, (p i).Prime) (hinj : Function.Injective p) (E : Finset ι) :
    leastSquare (∏ j ∈ E, p j) = ∏ j ∈ E, p j ^ 2 := by
  induction E using Finset.induction_on with
  | empty => simp [leastSquare_one]
  | insert i E hi ih =>
    have hcop : (p i).Coprime (∏ j ∈ E, p j) :=
      Nat.Coprime.prod_right fun j hj =>
        (Nat.coprime_primes (hp i) (hp j)).mpr fun h => hi (hinj h ▸ hj)
    rw [prod_insert hi, prod_insert hi, leastSquare_mul hcop, leastSquare_prime (hp i), ih]

/-- **The price `R_E^a` for distinct prime moduli**: `sq(D_E)^a = ∏_{j ∈ E} p_j^{2a}`, the
product of the selection factors of the selected atoms. -/
theorem stepR_rpow_eq_prod {ι : Type*} [Fintype ι] [DecidableEq ι] (m : ι → ℕ)
    [∀ j, NeZero (m j)] (hm : ∀ j, (m j).Prime) (hinj : Function.Injective m) (E : Finset ι)
    (a : ℝ) :
    ((stepR m E 1 : ℕ) : ℝ) ^ a = ∏ j ∈ E, ((m j : ℕ) : ℝ) ^ (2 * a) := by
  unfold stepR
  rw [one_mul, leastSquare_prod_primes m hm hinj E, Nat.cast_prod,
    ← Real.finsetProd_rpow _ _ (fun j _ => by positivity)]
  refine prod_congr rfl fun j _ => ?_
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

end Sarkozy.EnvelopeInputs

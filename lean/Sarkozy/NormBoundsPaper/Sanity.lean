module

public import Sarkozy.NormBoundsPaper.Constructor

@[expose] public section

/-!
# Non-vacuity and sharpness checks for `Sarkozy.NormBoundsPaper`

* The hypotheses of the block eigenvalue bounds are satisfiable: the block `{7, 11}` with
  `b = 7` (`sanity_eig`), and `paper_numbers` at `b = 7` (`sanity_numbers`).
* The kernels are probability kernels: `∑ K_D = ∑ K_P = 1` on every block of primes
  `≡ 3 (4)` (`sum_KD`, `sanity_sum_KP`), so `oldC` and `newC` are the laws of the paper and not
  degenerate.
* **The skew constant is sharp**: at the prime `b` itself the Paley eigenvalue at `ξ = 1` has
  imaginary part of modulus exactly `γ_b` (`sanity_sharp`), so `r/(1 − 1/b)` cannot be lowered on
  a block whose least prime is `b`.
* `NormBoundsRest` has the same field statements as B8's `NormBounds` minus `Cs`, `Ca`, `Ma₂`
  (definitional copy), so it adds no hypothesis that `NormBounds` did not have; the new theorems
  `const_sym_paper`, `const_skew_paper`, `merge2_skew_paper` have no hypotheses beyond the block's
  and the paper's scale `r = b^{-1/2}`, all discharged at the paper's partition in `hN_of_rest`.
-/

namespace Sarkozy.NormBoundsPaper

open Finset

instance fact_prime_7 : Fact (Nat.Prime 7) := ⟨by norm_num⟩
instance fact_prime_11 : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-- The primes `7, 11`. -/
def pr711 : Fin 2 → ℕ := ![7, 11]

instance fact_pr711 : ∀ i, Fact (Nat.Prime (pr711 i)) := by
  intro i
  fin_cases i
  · exact fact_prime_7
  · exact fact_prime_11

/-- The hypotheses of `eig_bounds` hold on the block `{7, 11}` with `b = 7`. -/
theorem sanity_eig (ξ : ∀ i, ZMod (pr711 i)) :
    ‖khat (Ksym pr711) ξ‖ ≤ gam 7 ^ 2 ∧ ‖khat (Kskew pr711) ξ‖ ≤ gam 7 :=
  eig_bounds (fun i => by fin_cases i <;> rfl) le_rfl
    (fun i => by fin_cases i <;> norm_num [pr711]) ξ

/-- `paper_numbers` at `b = 7`. -/
theorem sanity_numbers :
    0 ≤ rho 7 ∧ 0 ≤ eta 7 ∧ rho 7 ≤ 1 ∧ eta 7 ≤ 1 ∧ rho 7 ^ 2 ≤ gam 7 ∧
      rho 7 ^ 3 + eta 7 ^ 3 ≤ gam 7 ^ 2 :=
  paper_numbers le_rfl

/-- The replacement kernel is a probability kernel on every block of primes `≡ 3 (4)`. -/
theorem sanity_sum_KP {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] (hp2 : ∀ i, pr i ≠ 2) : ∑ d : ∀ i, ZMod (pr i), KP pr d = 1 := by
  unfold KP
  rw [← Fintype.prod_sum (fun i x => kP (pr i) x)]
  exact prod_eq_one fun i _ => sum_kP (hp2 i)

/-- **The skew constant is attained** at the least prime: `|Im k̂_P(1)| = γ_b` at `p = b`. -/
theorem sanity_sharp {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (h3 : p % 4 = 3) :
    |(hat1 (kP p) 1).im| = gam p :=
  hatP_im hp2 h3 one_ne_zero

end Sarkozy.NormBoundsPaper

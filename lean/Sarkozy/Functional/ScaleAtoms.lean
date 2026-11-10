module

public import Sarkozy.Functional.ScaleConditions
public import Sarkozy.Functional.PrefixModel

@[expose] public section

/-!
# The full order `D_E` of a selection (`lem:scale-conditions`, `eq:square-step`)

`08_scale_comparison.tex` writes the full order of a set `E` of atoms as
`D_E = q_E ∏_{p ∈ E_cl} p^{e_p}`: `q_E` is the product of the primes of `E` with
`e_p = 1`, and the clique part has even exponents, so it is at most `Q_cl` and a
perfect square. `ScaleConditions.scaleConsequences` takes this factorization as
hypotheses. This module proves it for the paper's groups, with coordinates
indexed by `J₀ ⊕ J`: a prefix of prime powers `P₀ i ^ e₀ i` with `e₀ i` even,
and a tail of primes `p j`, all primes distinct.

`scaleConsequences_selection` combines the two results: for the paper's groups
the consequences of `lem:scale-conditions` hold for every selection `E` with
`q_E ≤ N^τ`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

variable {J₀ J : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]

/-- The clique part `∏_{p ∈ E_cl} p^{e_p}` of `D_E`. -/
def cliquePart (P₀ e₀ : J₀ → ℕ) (E : Finset (J₀ ⊕ J)) : ℕ := ∏ i ∈ E.toLeft, P₀ i ^ e₀ i

/-- The squarefree part `q_E` of `D_E`: the product of the tail primes of `E`. -/
def tailPart (p : J → ℕ) (E : Finset (J₀ ⊕ J)) : ℕ := ∏ j ∈ E.toRight, p j

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- `D_E = q_E · ∏_{p ∈ E_cl} p^{e_p}` (`eq:square-step`). -/
theorem prod_joinModuli_eq (P₀ e₀ : J₀ → ℕ) (p : J → ℕ) (E : Finset (J₀ ⊕ J)) :
    ∏ k ∈ E, joinModuli (fun i => P₀ i ^ e₀ i) p k = tailPart p E * cliquePart P₀ e₀ E := by
  rw [prod_sum_eq_prod_toLeft_mul_prod_toRight, mul_comm]
  rfl

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- `q_E` is squarefree (distinct primes). -/
theorem tailPart_squarefree {p : J → ℕ} (hp : ∀ j, (p j).Prime) (hinj : Function.Injective p)
    (E : Finset (J₀ ⊕ J)) : Squarefree (tailPart p E) := by
  unfold tailPart
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i _ j _ hij
    exact Nat.coprime_iff_isRelPrime.mp
      ((Nat.coprime_primes (hp i) (hp j)).mpr (fun h => hij (hinj h)))
  · intro j _
    exact (hp j).squarefree

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- The clique part is a perfect square (even exponents). -/
theorem cliquePart_isSquare {P₀ e₀ : J₀ → ℕ} (he : ∀ i, Even (e₀ i)) (E : Finset (J₀ ⊕ J)) :
    IsSquare (cliquePart P₀ e₀ E) :=
  isSquare_prod _ fun i _ => (he i).isSquare_pow (P₀ i)

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] in
theorem cliquePart_ne_zero {P₀ e₀ : J₀ → ℕ} (hP : ∀ i, (P₀ i).Prime) (E : Finset (J₀ ⊕ J)) :
    cliquePart P₀ e₀ E ≠ 0 :=
  prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (hP i).ne_zero

omit [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- The clique part is at most `Q_cl = ∏_{p ∈ 𝒫₁} p^{e_p}`. -/
theorem cliquePart_le {P₀ e₀ : J₀ → ℕ} (hP : ∀ i, (P₀ i).Prime) (E : Finset (J₀ ⊕ J)) :
    cliquePart P₀ e₀ E ≤ ∏ i, P₀ i ^ e₀ i := by
  unfold cliquePart
  apply prod_le_prod_of_subset_of_one_le (subset_univ _)
  intro i _ _
  exact Nat.one_le_pow _ _ (hP i).pos

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- `q_E` is coprime to the clique part (the primes are distinct). -/
theorem tailPart_coprime_cliquePart {P₀ e₀ : J₀ → ℕ} {p : J → ℕ} (hP : ∀ i, (P₀ i).Prime)
    (hp : ∀ j, (p j).Prime) (hdist : ∀ i j, P₀ i ≠ p j) (E : Finset (J₀ ⊕ J)) :
    (tailPart p E).Coprime (cliquePart P₀ e₀ E) := by
  unfold tailPart cliquePart
  apply Nat.Coprime.prod_left
  intro j _
  apply Nat.Coprime.prod_right
  intro i _
  apply Nat.Coprime.pow_right
  exact (Nat.coprime_primes (hp j) (hP i)).mpr (fun h => hdist i j h.symm)

omit [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- `D₀` is coprime to `D_E` when it is coprime to every coordinate modulus. -/
theorem coprime_selection {P₀ e₀ : J₀ → ℕ} {p : J → ℕ} {D0 : ℕ}
    (hcop : ∀ k, D0.Coprime (joinModuli (fun i => P₀ i ^ e₀ i) p k)) (E : Finset (J₀ ⊕ J)) :
    D0.Coprime (tailPart p E * cliquePart P₀ e₀ E) := by
  rw [← prod_joinModuli_eq]
  exact Nat.Coprime.prod_right fun k _ => hcop k

omit [DecidableEq J₀] [Fintype J] [DecidableEq J] in
/-- `lem:scale-conditions`, consequences, for the paper's groups. The
coordinates are a prefix of prime powers `P₀ i ^ e₀ i` with even exponents and a
tail of primes, all distinct, and `D₀ ∣ M₀` is coprime to every modulus. For
every selection `E` with `q_E ≤ N^τ`, conditions (ii)–(iv) imply the
consequences, with `D_E = ∏_{k ∈ E} m_k`, `R = sq(D₀ D_E)`,
`n = K⌈M/(KR)⌉`, `λ = Rn/M` and `Q_cl = ∏_i P₀ i ^ e₀ i`. -/
theorem scaleConsequences_selection {P₀ e₀ : J₀ → ℕ} {p : J → ℕ}
    (hP : ∀ i, (P₀ i).Prime) (he : ∀ i, Even (e₀ i)) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (hdist : ∀ i j, P₀ i ≠ p j)
    {K L N M D0 M0 : ℕ} {β τ Q H : ℝ} (hK : 1 ≤ K) (hL : 1 ≤ L) (hN : N = K * L)
    (hM : M = N ∨ M = L) (hD0 : D0 ∣ M0) (hM0 : 1 ≤ M0)
    (hcop : ∀ k, D0.Coprime (joinModuli (fun i => P₀ i ^ e₀ i) p k))
    (E : Finset (J₀ ⊕ J)) (hqN : (tailPart p E : ℝ) ≤ (N : ℝ) ^ τ) (hβ : 0 ≤ β) (hH : 0 ≤ H)
    (hii : H * (∏ i, P₀ i ^ e₀ i : ℕ) * (N : ℝ) ^ τ ≤ Q)
    (hiii : H ≤ scaleN0 K M0 (∏ i, P₀ i ^ e₀ i) τ N ^ β ∧
      10 * (N : ℝ) ^ (6 * β) ≤ scaleN0 K M0 (∏ i, P₀ i ^ e₀ i) τ N)
    (hiv : (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (∏ i, P₀ i ^ e₀ i : ℕ) * (N : ℝ) ^ (2 * τ - 1) ≤ 1) :
    let DE := ∏ k ∈ E, joinModuli (fun i => P₀ i ^ e₀ i) p k
    let R := leastSquare (D0 * DE)
    let n := K * stepScale K M R
    (R : ℝ) ≤ (M0 : ℝ) ^ 2 * (∏ i, P₀ i ^ e₀ i : ℕ) * (N : ℝ) ^ (2 * τ) ∧
      H * (DE : ℝ) ≤ Q ∧
      (scaleN0 K M0 (∏ i, P₀ i ^ e₀ i) τ N ≤ n ∧ n ≤ N) ∧
      H ≤ (n : ℝ) ^ β ∧
      10 * (n : ℝ) ^ (6 * β) ≤ n ∧
      (1 ≤ (R * n : ℝ) / M ∧ (R * n : ℝ) / M ≤ 2) ∧
      ((R * n : ℝ) / M) ^ 72 ≤ 1 + scaleU K M0 (∏ i, P₀ i ^ e₀ i) τ L := by
  dsimp only
  have h := scaleConsequences (K := K) (L := L) (N := N) (M := M) (D0 := D0) (M0 := M0)
    (qE := tailPart p E) (cE := cliquePart P₀ e₀ E) (Qcl := ∏ i, P₀ i ^ e₀ i)
    hK hL hN hM hD0 hM0 (tailPart_squarefree hp hinj E) (cliquePart_isSquare he E)
    (cliquePart_ne_zero hP E) (cliquePart_le hP E) (coprime_selection hcop E)
    (tailPart_coprime_cliquePart hP hp hdist E) hqN hβ hH hii hiii hiv
  rw [prod_joinModuli_eq P₀ e₀ p E]
  exact h

end Sarkozy.Functional

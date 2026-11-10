module

public import Sarkozy.TheoremC.Main
public import Sarkozy.Functional.ScaleConditions

/-!
# The group and scale facts of the density-dc application (gap 5)

WP-R's density-dc theorems (`DensityDC/ThetaChain.lean`) take, besides the analytic inputs:

* `hpair`: the prefix moduli and the tail primes are pairwise coprime;
* `ScaleConditionsAt … L` at the scale of the counterexample.

`eventually_scaleConditions` gives the second one eventually in `L`, from WP-FI's
`Functional.scaleConditions_assembled`. The first one is **not derivable** from WP-FI's
`TheoremC.StandingData`, which does not say that the prefix primes `pp i` are distinct or that they
differ from the tail primes. `joinModuli_pairwise_coprime` shows that these two conditions
suffice; `standing_pairwise_coprime` is the statement for the comparison data, with them as
hypotheses (the suggested new fields of `StandingData`; see the report).
-/

@[expose] public section

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.TheoremC Sarkozy.Functional Sarkozy.PaperFrame

/-- **The scale conditions hold eventually** (WP-FI's `scaleConditions_assembled`). -/
theorem eventually_scaleConditions (K M0 Qcl Qpre N0 N0' : ℕ) (hK : 1 ≤ K) (hM0 : 1 ≤ M0)
    (hQcl : 1 ≤ Qcl) : ∀ᶠ L in atTop, ScaleConditionsAt K M0 Qcl Qpre N0 N0' L := by
  obtain ⟨⟨Lstar, _, h⟩, _⟩ := scaleConditions_assembled K M0 Qcl Qpre N0 N0' hK hM0 hQcl
  exact eventually_atTop.mpr ⟨Lstar, fun L hL => (h L hL).1⟩

/-- **Pairwise coprimality of the prefix moduli and the tail primes** from distinct primes:
`m₀ i = pp_i^{e_i}` with distinct prefix primes `pp_i`, distinct tail primes `p_j`, and no prefix
prime equal to a tail prime. -/
theorem joinModuli_pairwise_coprime {J₀ Jt : Type*} (m₀ : J₀ → ℕ) (p : Jt → ℕ) (pp ep : J₀ → ℕ)
    (hpp : ∀ i, (pp i).Prime) (hm₀ : ∀ i, m₀ i = pp i ^ ep i) (hp : ∀ j, (p j).Prime)
    (hppinj : Injective pp) (hpinj : Injective p) (hne : ∀ i j, pp i ≠ p j) :
    Pairwise fun k k' => (joinModuli m₀ p k).Coprime (joinModuli m₀ p k') := by
  intro k k' hkk
  rcases k with i | j <;> rcases k' with i' | j'
  · have hii : i ≠ i' := fun h => hkk (by rw [h])
    simp only [joinModuli, Sum.elim_inl, hm₀]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes (hpp i) (hpp i')).mpr
      (fun h => hii (hppinj h)))
  · simp only [joinModuli, Sum.elim_inl, Sum.elim_inr, hm₀]
    exact Nat.Coprime.pow_left _ ((Nat.coprime_primes (hpp i) (hp j')).mpr (hne i j'))
  · simp only [joinModuli, Sum.elim_inl, Sum.elim_inr, hm₀]
    exact Nat.Coprime.pow_right _ ((Nat.coprime_primes (hp j) (hpp i')).mpr
      (fun h => hne i' j h.symm))
  · have hjj : j ≠ j' := fun h => hkk (by rw [h])
    simp only [joinModuli, Sum.elim_inr]
    exact (Nat.coprime_primes (hp j) (hp j')).mpr (fun h => hjj (hpinj h))

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] [DecidableEq P] in
/-- **`hpair` for the comparison data**, given the two conditions that `StandingData` lacks:
distinct prefix primes, and no prefix prime among the tail primes. -/
theorem standing_pairwise_coprime (S : StandingData m₀ p pr h E)
    (hppinj : Injective S.pp) (hne : ∀ L i j, S.pp i ≠ p L j) (L : ℕ) :
    Pairwise fun k k' => (joinModuli m₀ (p L) k).Coprime (joinModuli m₀ (p L) k') :=
  joinModuli_pairwise_coprime m₀ (p L) S.pp S.ep S.pp_prime S.m₀_eq (S.p_prime L) hppinj
    (S.p_inj L) (hne L)

end Sarkozy.EnvelopeInputs

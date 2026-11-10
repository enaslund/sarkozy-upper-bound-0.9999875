module

public import Sarkozy.PartV.PositiveRoot
public import Sarkozy.PartV.UpperReference

@[expose] public section

/-!
# Non-vacuity of the Part V definitions

The reference laws of `Sarkozy.PartV` need nonempty labelling sets `Inj_p(G)` for the graphs
they use (`MiddleNonempty`, `UpperNonempty`, `TailNonempty`). Under Weil's bound (H1,
`Target.Weil`) these hold at every large prime (`exists_injLabellings_nonempty`), with one
threshold for all the graphs of a law:

* `middleNonempty_of_large`: every block of primes `≥ p₀` carries the six middle field laws, so
  `middleBlockReference` (with the uniform or the individual-square root) is defined on it;
* `upperNonempty_of_large`: the same for the eighteen graphs `G_{φ₀φ₁,j}` of the upper
  reference;
* `tailNonempty_of_large`: the tail law `tailLaw p` is defined at every prime `p ≥ p₀`; with
  `tailLawFamily` it is packaged as a family `∀ q [NeZero q], FiniteLaw (Slot → ZMod q)` in the
  shape of `TheoremC.Reference.μp`, with uniform one-slot marginals at every prime `q ≥ p₀`
  (`tailLawFamily_uniform`).

The thresholds `p₀` are not explicit: they come from the limit `lowerProd/p^{|W|} → ∏ 2^{-t_i}`.
The paper's ranges start at `Q₃ ≈ 2·10⁷` (middle) and `P₄ = 2⁵¹²` (tail); an explicit threshold
below `Q₃` would follow from the explicit sequential counts (`lem:graphs:sequential`) and is not
derived here. The tail datum's weights satisfy all 105 of their conditions (`tailDatum_gates`),
so the conditions on `UpperWeights` used by the reflection-positivity lemma of the upper
reference (section 25) are not vacuous either.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-- **The six middle graphs have labellings at every prime of a block of large primes.** -/
theorem middleNonempty_of_large (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime],
      (∀ i, p₀ ≤ pr i) → MiddleNonempty pr := by
  obtain ⟨a, ha⟩ := exists_injLabellings_nonempty hW (recordGraph (Fin 2))
  obtain ⟨b, hb⟩ := exists_injLabellings_nonempty hW (foldGraph (Fin 2))
  obtain ⟨c, hc⟩ := exists_injLabellings_nonempty hW (matchGraph (Fin 2))
  obtain ⟨d, hd⟩ := exists_injLabellings_nonempty hW (recordGraph (Fin 1))
  obtain ⟨e, he⟩ := exists_injLabellings_nonempty hW (foldGraph (Fin 1))
  obtain ⟨f, hf⟩ := exists_injLabellings_nonempty hW (matchGraph (Fin 1))
  refine ⟨a + b + c + d + e + f, fun pr _ hpr => ⟨?_, ?_, ?_, ?_, ?_, ?_⟩⟩ <;> intro i <;>
    have := hpr i
  · exact ha (pr i) (by omega)
  · exact hb (pr i) (by omega)
  · exact hc (pr i) (by omega)
  · exact hd (pr i) (by omega)
  · exact he (pr i) (by omega)
  · exact hf (pr i) (by omega)

/-- One threshold for the eighteen graphs `G_{φ₀φ₁,j}`. -/
theorem fieldGraphs_nonempty_of_large (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p → ∀ f₀ f₁ : FType,
      (injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 2))).Nonempty ∧
        (injLabellings (ZMod p) (fieldGraph f₀ f₁ (Fin 1))).Nonempty := by
  have h2 := fun f₀ f₁ : FType => exists_injLabellings_nonempty hW (fieldGraph f₀ f₁ (Fin 2))
  have h1 := fun f₀ f₁ : FType => exists_injLabellings_nonempty hW (fieldGraph f₀ f₁ (Fin 1))
  choose q2 hq2 using h2
  choose q1 hq1 using h1
  refine ⟨∑ t : FType × FType, (q2 t.1 t.2 + q1 t.1 t.2), fun p _ hp f₀ f₁ => ?_⟩
  have hle : q2 f₀ f₁ + q1 f₀ f₁ ≤ ∑ t : FType × FType, (q2 t.1 t.2 + q1 t.1 t.2) :=
    single_le_sum (f := fun t : FType × FType => q2 t.1 t.2 + q1 t.1 t.2)
      (fun _ _ => Nat.zero_le _) (mem_univ (f₀, f₁))
  exact ⟨hq2 f₀ f₁ p (by omega), hq1 f₀ f₁ p (by omega)⟩

/-- **The eighteen upper graphs have labellings at every prime of a block of large primes.** -/
theorem upperNonempty_of_large (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime],
      (∀ i, p₀ ≤ pr i) → UpperNonempty pr := by
  obtain ⟨p₀, hp₀⟩ := fieldGraphs_nonempty_of_large hW
  exact ⟨p₀, fun pr _ hpr => ⟨fun f₀ f₁ i => (hp₀ (pr i) (hpr i) f₀ f₁).1,
    fun f₀ f₁ i => (hp₀ (pr i) (hpr i) f₀ f₁).2⟩⟩

/-- **The tail law is defined at every large prime.** -/
theorem tailNonempty_of_large (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p → TailNonempty p := by
  obtain ⟨p₀, hp₀⟩ := fieldGraphs_nonempty_of_large hW
  exact ⟨p₀, fun p _ hp => ⟨fun f₀ f₁ => (hp₀ p hp f₀ f₁).1, fun f₀ f₁ => (hp₀ p hp f₀ f₁).2⟩⟩

/-- **The tail laws as a family over all moduli** (the shape of `TheoremC.Reference.μp`): the tail
law at a prime with nonempty labelling sets, the uniform law otherwise. -/
noncomputable def tailLawFamily (q : ℕ) [NeZero q] : FiniteLaw (Slot → ZMod q) :=
  if h : q.Prime then
    haveI : Fact q.Prime := ⟨h⟩
    haveI := Classical.propDecidable (TailNonempty q)
    if h' : TailNonempty q then tailLaw q h' else FiniteLaw.uniform _
  else FiniteLaw.uniform _

theorem tailLawFamily_eq (q : ℕ) [NeZero q] [hq : Fact q.Prime] (h' : TailNonempty q) :
    tailLawFamily q = tailLaw q h' := by
  unfold tailLawFamily
  rw [dite_eq_left hq.out]
  exact dite_eq_left h'

/-- **The tail family has uniform one-slot marginals at every large prime** (`(R3)` of
`hyp:record:reference` for the tail atoms, `Reference.unifp`). -/
theorem tailLawFamily_uniform (hW : Target.Weil) :
    ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → HasUniformMarginals (tailLawFamily q) := by
  obtain ⟨p₀, hp₀⟩ := tailNonempty_of_large hW
  refine ⟨p₀, fun q _ hq hle => ?_⟩
  have : Fact q.Prime := ⟨hq⟩
  rw [tailLawFamily_eq q (hp₀ q hle)]
  exact tailLaw_uniform q _

end Sarkozy.PartV

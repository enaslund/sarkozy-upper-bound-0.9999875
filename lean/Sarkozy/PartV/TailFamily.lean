module

public import Sarkozy.PartV.Acceptance

@[expose] public section

/-!
# The tail family against the fields of `TheoremC.Reference`

`Sarkozy.TheoremC.Reference` asks for one law `μp q` per modulus `q`. `tailLawFamily` is the tail
law at the primes with nonempty labelling sets (every large prime, `tailNonempty_of_large`) and
the uniform law elsewhere. This file proves two of the fields of `Reference` for it in full:
* `invp` at every modulus (`tailLawFamily_invp`): invariance under `z_v ↦ a z_v + b` for a unit
  square `a`;
* `unifp` at every prime (`tailLawFamily_unifp`): uniform one-slot marginals.

The field `rpp` needs the tail law's reflection positivity at the chamber cuts (open; `ι` is
`tailLaw_reserved_positive`, given the caps), and `mixing` needs `lem:record:tail-mixing`.
-/

namespace Sarkozy.PartV

open Finset

/-- The uniform law is invariant under every bijection of the sample space. -/
theorem uniform_expect_equiv {Ω : Type*} [Fintype Ω] [Nonempty Ω] (e : Ω ≃ Ω) (f : Ω → ℝ) :
    (FiniteLaw.uniform Ω).expect (fun ω => f (e ω)) = (FiniteLaw.uniform Ω).expect f := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- **`Reference.invp` for the tail family**, at every modulus. -/
theorem tailLawFamily_invp (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q)
    (ha : IsSquare (a : ZMod q)) (F : (Slot → ZMod q) → ℝ) :
    (tailLawFamily q).expect (fun z => F (fun v => PaperFrame.affineEquiv a b (z v))) =
      (tailLawFamily q).expect F := by
  unfold tailLawFamily
  split_ifs with hq h'
  · have : Fact q.Prime := ⟨hq⟩
    exact tailLaw_invp q h' a b ha F
  · exact uniform_expect_equiv
      (Equiv.piCongrRight fun _ => PaperFrame.affineEquiv a b) F
  · exact uniform_expect_equiv
      (Equiv.piCongrRight fun _ => PaperFrame.affineEquiv a b) F

/-- **`Reference.unifp` for the tail family**, at every prime. -/
theorem tailLawFamily_unifp (q : ℕ) [NeZero q] (hq : q.Prime) :
    HasUniformMarginals (tailLawFamily q) := by
  have : Fact q.Prime := ⟨hq⟩
  unfold tailLawFamily
  rw [dite_eq_left hq]
  split_ifs with h'
  · exact tailLaw_uniform q h'
  · intro v g
    exact vertex_uniform_of_translation (FiniteLaw.uniform (Slot → ZMod q)) (fun _ _ => rfl) v g

end Sarkozy.PartV

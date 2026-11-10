module

public import Sarkozy.Construction.CliqueInvariance
public import Sarkozy.TensorMarginals

/-!
# The clique part of the prefix law

`paper/sections/19_prefix.tex` and `def:record:parameters`(c): every prime `p ≡ 1 (mod 4)` below
`P₄` is an atom `{p}` with label group `ℤ/p^{e_p}ℤ`, `e_p = 2ℓ`, and reference law the
square-clique law. `cliquePrefixLaw` is their product over a finite set of primes; it is
reflection positive at the seven sorting cuts and has uniform one-slot marginals
(`cliquePrefixLaw_slotReflectionPositive`, `cliquePrefixLaw_uniformMarginals`), the parts of
hypothesis 2 of the main theorem contributed by the clique atoms.
-/

@[expose] public section

namespace Sarkozy

/-- A finite set of primes, each carrying its `Fact`. -/
structure PrimeSet where
  primes : Finset ℕ
  prime : ∀ p ∈ primes, p.Prime

variable (P : PrimeSet) (ℓ : ℕ)

instance (q : P.primes) : Fact (q : ℕ).Prime := ⟨P.prime q q.2⟩

/-- The product of the square-clique laws over the primes of `P`. -/
noncomputable def cliquePrefixLaw :
    FiniteLaw (Slot → ∀ q : P.primes, ZMod ((q : ℕ) ^ (2 * ℓ))) :=
  FiniteLaw.tensor fun q : P.primes => cliqueLaw (q : ℕ) ℓ

theorem cliquePrefixLaw_slotReflectionPositive :
    SlotReflectionPositive (signedIntegral (cliquePrefixLaw P ℓ).weight) :=
  tensor_slot_reflection_positive _ fun q => cliqueLaw_slotReflectionPositive (q : ℕ) ℓ

theorem cliquePrefixLaw_uniformMarginals : HasUniformMarginals (cliquePrefixLaw P ℓ) :=
  tensor_uniform_marginals _ fun q => cliqueLaw_uniformMarginals (q : ℕ) ℓ

end Sarkozy

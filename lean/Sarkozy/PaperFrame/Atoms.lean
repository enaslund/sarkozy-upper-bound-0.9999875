module

public import Sarkozy.Functional.PrefixModel

@[expose] public section

/-!
# The paper's atoms for the closing frame

The concrete energies of `Sarkozy.Comparison.ConcreteFrame` are built from per-atom laws
on labellings `Slot → Xb L b` of an atom alphabet. For the paper's functional with the
prefix/tail splitting of `Sarkozy.Functional.PrefixModel` (the group
`G_N = X₀ × ∏_{j ∈ J L} ℤ/p_j ℤ`, `X₀ = ∏_{i ∈ J₀} ℤ/m₀ᵢℤ`), the atoms at the scale `L` are
`Option (J L)`:

* `none`: the fixed prefix `X₀` (one atom; the comparison worker's reference law
  `paperLaw = μ₀ ⊗ ⊗_p μ_p` has a single factor `μ₀` there, which is the product of the
  clique and block laws but is not assumed to factor further);
* `some j`: the tail prime `p_j`, with alphabet `ℤ/p_jℤ`.

`atomEquiv` is the explicit equivalence `(∀ b, Xb L b) ≃ X₀ × X_tail`, and `atomGroupEquiv`
continues it to the joined group `ResidueSpace (joinModuli m₀ (p L))` on which the lift of
`def:record:functional` lives. `atomLift` is the paper's `F_A` read on the atom labels.
-/

open Finset

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The atoms at the scale `L`: the prefix (`none`) and the tail primes (`some j`). -/
abbrev PaperAtom (J : ℕ → Type) (L : ℕ) : Type := Option (J L)

/-- The alphabet of an atom: the prefix group, or `ℤ/p_jℤ` at a tail prime. -/
abbrev AtomLabel (L : ℕ) : PaperAtom J L → Type
  | none => ResidueSpace m₀
  | some j => ZMod (p L j)

instance atomLabelFintype (L : ℕ) : ∀ b, Fintype (AtomLabel m₀ p L b)
  | none => inferInstanceAs (Fintype (ResidueSpace m₀))
  | some j => inferInstanceAs (Fintype (ZMod (p L j)))

instance atomLabelDecidableEq (L : ℕ) : ∀ b, DecidableEq (AtomLabel m₀ p L b)
  | none => inferInstanceAs (DecidableEq (ResidueSpace m₀))
  | some j => inferInstanceAs (DecidableEq (ZMod (p L j)))

instance atomLabelNonempty (L : ℕ) : ∀ b, Nonempty (AtomLabel m₀ p L b)
  | none => inferInstanceAs (Nonempty (ResidueSpace m₀))
  | some j => inferInstanceAs (Nonempty (ZMod (p L j)))

/-- The atom labels are the prefix-tail product group. -/
def atomEquiv (L : ℕ) : (∀ b, AtomLabel m₀ p L b) ≃ ResidueSpace m₀ × ResidueSpace (p L) :=
  Equiv.piOptionEquivProd

/-- The atom labels are the joined group `G_N` of `def:record:functional`. -/
noncomputable def atomGroupEquiv (L : ℕ) :
    (∀ b, AtomLabel m₀ p L b) ≃ ResidueSpace (joinModuli m₀ (p L)) :=
  (atomEquiv m₀ p L).trans (splitEquiv m₀ (p L)).symm.toEquiv

/-- The paper's lift `F_A = 𝓛_{[N],N} 1_A` (`N = K L`, `K = blockScale`, `Q = N^{1/20}`),
read on the atom labels. -/
noncomputable def atomLift (L : ℕ) (A : Finset ℤ) (x : ∀ b, AtomLabel m₀ p L b) : ℝ :=
  (wholeLift (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) (blockScale * L) A
    (atomGroupEquiv m₀ p L x)).re

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
theorem atomGroupEquiv_apply (L : ℕ) (x : ∀ b, AtomLabel m₀ p L b) :
    atomGroupEquiv m₀ p L x = (splitEquiv m₀ (p L)).symm (atomEquiv m₀ p L x) := rfl

/-- `atomLift` is the transported lift of `Sarkozy.Functional.prefixedFunctional`. -/
theorem atomLift_eq (L : ℕ) (A : Finset ℤ) (x : ∀ b, AtomLabel m₀ p L b) :
    atomLift m₀ p L A x = (wholeLift (joinModuli m₀ (p L)) (paperCutoff (blockScale * L))
      (blockScale * L) A ((splitEquiv m₀ (p L)).symm (atomEquiv m₀ p L x))).re := rfl

end Sarkozy.PaperFrame

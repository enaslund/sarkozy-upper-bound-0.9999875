module

public import Sarkozy.DensityDC.Restoration
public import Sarkozy.RecordExpansion.Multilinear

/-!
# One prefix atom versus the prefix coordinates as atoms (gap 1)

WP-FI's laws on the paper's atoms are `tensorLaw` over `PaperAtom J L = Option (J L)`: the
prefix is the atom `none`, with alphabet `ResidueSpace m₀`, and the tail primes are the
atoms `some j` (`Sarkozy/PaperFrame/Atoms.lean`). The WP-R density-dc theorems take every
prefix coordinate as an atom (`J₀ ⊕ J L`, alphabets `ZMod (joinModuli m₀ (p L) k)`). This
file transports a law of the first kind to the second, under the hypothesis that the prefix
factor is itself a tensor over the prefix coordinates, `Λ_none = ⊗_i lam0_i`.

* `lawDensity_tensorLaw`: the density of a tensor law at a point is the product of the
  densities.
* `joinLaws`: the family on `J₀ ⊕ J L`, with `lam0_i` at the prefix coordinates and `Λ_{some j}`
  at the tail primes.
* `tensorLaw_atoms_transport`: **the transport**:
  `(⊗_{b : Option (J L)} Λ_b) G = (⊗_{k : J₀ ⊕ J L} joinLaws_k) (G ∘ atomGroupEquiv⁻¹)` for
  every integrand `G`, if `Λ_none = ⊗_i lam0_i`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.DensityDC

open Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-- The density of a tensor law at a point is the product of the densities. -/
theorem lawDensity_tensorLaw {Jt V : Type*} [Fintype Jt] [DecidableEq Jt] [Fintype V]
    [DecidableEq V] {X : Jt → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]
    (Λ : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (x : V → ∀ j, X j) :
    lawDensity (tensorLaw Λ) x = ∏ j, lawDensity (Λ j) (fun v => x v j) := by
  unfold lawDensity
  rw [tensorLaw_apply]
  rw [Finset.sum_eq_single (fun j v => x v j)]
  · simp only [ite_true, mul_one]
    rfl
  · intro z _ hz
    have hne : (fun v j => z j v) ≠ x := by
      intro h
      apply hz
      funext j v
      exact congrFun (congrFun h v) j
    simp only [hne, ite_false, mul_zero]
  · intro h
    exact absurd (mem_univ _) h

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The family on `J₀ ⊕ J L`: `lam0_i` at the prefix coordinates, `Λ_{some j}` at the tail
primes. -/
noncomputable def joinLaws (L : ℕ)
    (Λ : ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (lam0 : ∀ i, ((Slot → ZMod (m₀ i)) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ k : J₀ ⊕ J L, ((Slot → ZMod (joinModuli m₀ (p L) k)) → ℝ) →ₗ[ℝ] ℝ
  | Sum.inl i => lam0 i
  | Sum.inr j => Λ (some j)

/-- The configurations of the two atom structures. -/
def atomConfigEquiv (L : ℕ) :
    (∀ k : J₀ ⊕ J L, Slot → ZMod (joinModuli m₀ (p L) k)) ≃
      (∀ b : PaperAtom J L, Slot → AtomLabel m₀ p L b) where
  toFun w b := match b with
    | none => fun v i => w (Sum.inl i) v
    | some j => w (Sum.inr j)
  invFun z k := match k with
    | Sum.inl i => fun v => z none v i
    | Sum.inr j => z (some j)
  left_inv w := by
    funext k
    cases k <;> rfl
  right_inv z := by
    funext b
    cases b <;> rfl

/-- **The transport from one prefix atom to the prefix coordinates** (gap 1): if the prefix
factor is a tensor over the prefix coordinates, `Λ_none = ⊗_i lam0_i`, then for every integrand
`G` the tensor law over the paper's atoms equals the tensor law over `J₀ ⊕ J L` of
`joinLaws`, read through `atomGroupEquiv`. -/
theorem tensorLaw_atoms_transport (L : ℕ)
    (Λ : ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (lam0 : ∀ i, ((Slot → ZMod (m₀ i)) → ℝ) →ₗ[ℝ] ℝ) (h0 : Λ none = tensorLaw lam0)
    (G : (Slot → ∀ b, AtomLabel m₀ p L b) → ℝ) :
    tensorLaw Λ G =
      tensorLaw (joinLaws m₀ p L Λ lam0)
        (fun x => G (fun v => (atomGroupEquiv m₀ p L).symm (x v))) := by
  rw [tensorLaw_apply, tensorLaw_apply]
  rw [← (atomConfigEquiv m₀ p L).sum_comp]
  refine sum_congr rfl fun w _ => ?_
  congr 1
  · rw [Fintype.prod_option, Fintype.prod_sum_type]
    congr 1
    change lawDensity (Λ none) (fun v i => w (Sum.inl i) v) = _
    rw [h0]
    exact lawDensity_tensorLaw lam0 (fun v i => w (Sum.inl i) v)
  · congr 1
    funext v b
    cases b <;> rfl

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- The hypothesis `Λ_none = ⊗_i λ0_i` for WP-FI's reference laws with a product prefix law:
`refLaws m₀ p (⊗_i μ0_i) μp L none = ⊗_i μ0_i` as signed functionals
(`FiniteLaw.signedIntegral_tensor`). The same holds for every envelope law of a selection
that does not select the prefix atom, since its prefix factor is the reference one. -/
theorem refLaws_none_tensor (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    refLaws m₀ p (FiniteLaw.tensor μ0) μp L none =
      tensorLaw (fun i => signedIntegral (μ0 i).weight) :=
  FiniteLaw.signedIntegral_tensor μ0

end Sarkozy.DensityDC

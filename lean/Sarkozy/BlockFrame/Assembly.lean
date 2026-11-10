module

public import Sarkozy.BlockFrame.Merge
public import Sarkozy.PartVLaws.PrefixAssembly

@[expose] public section

/-!
# The prefix law assembled from the block laws

`paper/sections/09_comparison_theorem.tex`, `def:cp1` (the reference `μ = ⊗_𝔟 μ_𝔟` is the product
of the atom laws); `paper/sections/18_design.tex`, `def:construction`(b) (the atom laws of the
prefix: square-clique primes, middle blocks, upper blocks); `def:record:functional`(d),(e).

For block laws `μ₀ β` on `Slot → BlockRes m₀ blk β` (`Atoms.lean`):

* `blockAssembly μ₀ = (⊗_β μ₀ β)` carried to the merged prefix `X₀ = ResidueSpace m₀` along
  `prefixRegroup` (the law `μ₀` of `TheoremC.Reference` built from its atoms; V2's
  `PartVLaws.prefixAssembly` is the same construction for `J₀ = Σ_a I a`);
* `mergeLaws_blockRefLaws`: the merged family of the block reference laws is `PaperFrame`'s
  `refLaws` with prefix law `blockAssembly μ₀`;
* **`energyFirst_blockRefLaws`**: the reference energy over the block atoms with the lift
  `blockLift` is the paper's functional `Y(L, A) = prefixedFunctional … (paperLaw …)` with
  prefix law `blockAssembly μ₀` (`def:record:functional`(e));
* `blockAssembly_unif`, `blockAssembly_rp`, `blockAssembly_inv`: uniform marginals, reflection
  positivity at every cut of `𝔉`, and square-affine invariance pass from the block laws to
  `blockAssembly μ₀` (the fields `unif₀`, `rp₀`, `inv₀` of `TheoremC.Reference`).
-/

open Finset Function

namespace Sarkozy.BlockFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.Comparison Sarkozy.PaperFrame

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {B : Type} [Fintype B] [DecidableEq B] (blk : J₀ → B)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The prefix law assembled from the block laws** (`def:cp1`, `def:construction`(b)):
`μ₀ = ⊗_β μ_β`, carried to `X₀ = ResidueSpace m₀` along `prefixRegroup`. -/
noncomputable def blockAssembly (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β)) :
    FiniteLaw (Slot → ResidueSpace m₀) :=
  (FiniteLaw.tensor μ₀).map (slotRegroupPrefix m₀ blk)

theorem blockAssembly_expect (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (F : (Slot → ResidueSpace m₀) → ℝ) :
    (blockAssembly m₀ blk μ₀).expect F =
      (FiniteLaw.tensor μ₀).expect (fun z => F (slotRegroupPrefix m₀ blk z)) := by
  unfold blockAssembly
  rw [FiniteLaw.expect_map]
  rfl

/-- The functional of the assembled law is the merged prefix functional of the block laws. -/
theorem signedIntegral_blockAssembly (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β)) :
    signedIntegral (blockAssembly m₀ blk μ₀).weight =
      prefixMerge m₀ blk (fun β => signedIntegral (μ₀ β).weight) := by
  refine LinearMap.ext fun F => ?_
  rw [← FiniteLaw.expect_eq_signedIntegral, blockAssembly_expect, prefixMerge_apply,
    FiniteLaw.expect_eq_signedIntegral, FiniteLaw.signedIntegral_tensor]

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- **The merged family of the block reference laws is `PaperFrame`'s reference family**, with
prefix law `blockAssembly μ₀` (`def:cp1`). -/
theorem mergeLaws_blockRefLaws (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    mergeLaws m₀ blk p L (blockRefLaws m₀ blk p μ₀ μp L) =
      refLaws m₀ p (blockAssembly m₀ blk μ₀) μp L := by
  funext b
  cases b with
  | none => exact (signedIntegral_blockAssembly m₀ blk μ₀).symm
  | some j => rfl

/-- The reference energy over the block atoms is the reference energy over the merged atoms with
the assembled prefix law, as functions of `(L, A)`. -/
theorem energyFirst_blockRefLaws_eq (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) :
    energyFirst (Atom := BlockAtom B J) (Xb := BlockLabel m₀ blk p) (blockRefLaws m₀ blk p μ₀ μp)
        (blockLift m₀ blk p) =
      energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p)
        (refLaws m₀ p (blockAssembly m₀ blk μ₀) μp) (atomLift m₀ p) := by
  funext L A
  rw [energyFirst_mergeLaws]
  have h : (fun L => mergeLaws m₀ blk p L (blockRefLaws m₀ blk p μ₀ μp L)) =
      refLaws m₀ p (blockAssembly m₀ blk μ₀) μp :=
    funext (mergeLaws_blockRefLaws m₀ blk p μ₀ μp)
  rw [h]

/-- **`def:record:functional`(e) over the block atoms.** The `energyFirst` of the block
reference laws with the paper's lift `blockLift` is the paper's functional
`Y(L, A) = prefixedFunctional … (paperLaw …)`, the prefix law being `blockAssembly μ₀`. -/
theorem energyFirst_blockRefLaws (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) (A : Finset ℤ) :
    energyFirst (Atom := BlockAtom B J) (Xb := BlockLabel m₀ blk p) (blockRefLaws m₀ blk p μ₀ μp)
        (blockLift m₀ blk p) L A =
      prefixedFunctional m₀ p (paperLaw m₀ p (blockAssembly m₀ blk μ₀) μp) L A := by
  rw [energyFirst_blockRefLaws_eq]
  exact energyFirst_refLaws m₀ p (blockAssembly m₀ blk μ₀) μp L A

/-- **`Reference.unif₀` from the blocks**: uniform one-slot marginals pass from the block laws to
the assembled prefix law. -/
theorem blockAssembly_unif (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (hμ : ∀ β, HasUniformMarginals (μ₀ β)) : HasUniformMarginals (blockAssembly m₀ blk μ₀) := by
  intro v f
  rw [blockAssembly_expect]
  have h := tensor_uniform_marginals μ₀ hμ v (fun x => f (prefixRegroup m₀ blk x))
  exact h.trans (PartVLaws.uniform_expect_equiv' (prefixRegroup m₀ blk) f)

/-- **`Reference.rp₀` from the blocks**: reflection positivity at every cut of the family `𝔉`
passes from the block laws to the assembled prefix law. -/
theorem blockAssembly_rp (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (hμ : ∀ β, TheoremC.FamilyReflectionPositive (signedIntegral (μ₀ β).weight)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (blockAssembly m₀ blk μ₀).weight) := by
  intro c hc
  have ht := FiniteLaw.tensor_positive μ₀ c (fun β => hμ β c hc)
  have heq : signedIntegral (blockAssembly m₀ blk μ₀).weight =
      pushFunctional (signedIntegral (FiniteLaw.tensor μ₀).weight) (slotRegroupPrefix m₀ blk) := by
    refine LinearMap.ext fun F => ?_
    rw [← FiniteLaw.expect_eq_signedIntegral, blockAssembly_expect]
    rfl
  rw [heq]
  exact FiveType.TwoCoord.positive_push_halfLocal c ht _ (fun x w => prefixRegroup m₀ blk (x w))
    (fun _ => rfl) (fun _ => rfl)

/-- The slot form of `blockAssembly_rp` (reflection positivity at the seven sorting cuts). -/
theorem blockAssembly_slotPositive (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (hμ : ∀ β, TheoremC.FamilyReflectionPositive (signedIntegral (μ₀ β).weight)) :
    SlotReflectionPositive (signedIntegral (blockAssembly m₀ blk μ₀).weight) :=
  (blockAssembly_rp m₀ blk μ₀ hμ).slot

/-- **`Reference.inv₀` from the blocks** ((R3)): invariance of every block law under the
square-affine maps `z_{v,i} ↦ a_i z_{v,i} + b_i` of its coordinates gives the invariance of the
assembled prefix law under the square-affine maps of all prefix coordinates. -/
theorem blockAssembly_inv (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (hμ : ∀ β (a : ∀ i, (ZMod (blockModuli m₀ blk β i))ˣ) (b : BlockRes m₀ blk β),
      (∀ i, IsSquare (a i : ZMod (blockModuli m₀ blk β i))) →
      ∀ F : (Slot → BlockRes m₀ blk β) → ℝ,
        (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli m₀ blk β) a b (z v))) =
          (μ₀ β).expect F)
    (a : ∀ i, (ZMod (m₀ i))ˣ) (b : ResidueSpace m₀) (ha : ∀ i, IsSquare ((a i : ZMod (m₀ i))))
    (F : (Slot → ResidueSpace m₀) → ℝ) :
    (blockAssembly m₀ blk μ₀).expect (fun z => F (fun v => piAffineEquiv m₀ a b (z v))) =
      (blockAssembly m₀ blk μ₀).expect F := by
  rw [blockAssembly_expect, blockAssembly_expect]
  let T : ∀ β, (Slot → BlockRes m₀ blk β) ≃ (Slot → BlockRes m₀ blk β) := fun β =>
    Equiv.piCongrRight fun _ : Slot =>
      piAffineEquiv (blockModuli m₀ blk β) (fun i => a i.1) (fun i => b i.1)
  have hT : ∀ β y, (μ₀ β).weight (T β y) = (μ₀ β).weight y := fun β y =>
    PartV.weight_comp_of_expect (μ₀ β) (T β)
      (fun H => hμ β (fun i => a i.1) (fun i => b i.1) (fun i => ha i.1) H) y
  have h := PartV.expect_tensor_comp μ₀ T hT (fun z => F (slotRegroupPrefix m₀ blk z))
  refine Eq.trans ?_ h
  rfl

end Sarkozy.BlockFrame

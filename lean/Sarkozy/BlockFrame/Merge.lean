module

public import Sarkozy.BlockFrame.Atoms

@[expose] public section

/-!
# Merging the block atoms into the prefix atom

`paper/sections/09_comparison_theorem.tex`, `def:cp1` (the reference is the product
`μ = ⊗_𝔟 μ_𝔟` over the atoms); `def:record:functional`(d),(e) (the functional is the cut form of
the lift under the product law).

A family `ν` of per-atom functionals on the block atoms `BlockAtom B J L` (`Atoms.lean`) induces
the family `mergeLaws ν` on the atoms `PaperAtom J L` of `Sarkozy.PaperFrame`: at the merged
prefix atom it is the tensor product of the block functionals `ν (inl β)`, carried to
`X₀ = ResidueSpace m₀` by `prefixRegroup`; at a tail prime it is unchanged.

* `tensorLaw_mergeLaws`: the tensor product over the merged atoms of `mergeLaws ν` is the
  tensor product over the block atoms of `ν`, read through `regroup`;
* `energyFirst_mergeLaws`, `energyComparison_mergeLaws`, `energyMean_mergeLaws`: hence every
  frame energy over the block atoms with the lift `blockLift` is the same energy over the merged
  atoms with the lift `atomLift`;
* `multilinearIntegral_mergeLaws`: the same identity for multilinear integrals of slot inputs.

So the block frame and the merged frame have the same energies; they differ only in how the
prefix is cut into atoms, i.e. in the prices (`def:price`).
-/

open Finset Function

namespace Sarkozy.BlockFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {B : Type} [Fintype B] [DecidableEq B] (blk : J₀ → B)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The slotwise regrouping of the block labels into the prefix group `X₀`. -/
def slotRegroupPrefix (z : Slot → ∀ β, BlockRes m₀ blk β) : Slot → ResidueSpace m₀ :=
  fun v => prefixRegroup m₀ blk (z v)

/-- **The merged prefix functional** (`def:cp1`): the tensor product `⊗_β ν_β` of block
functionals, carried to the merged prefix `X₀` along `prefixRegroup`. -/
noncomputable def prefixMerge (νB : ∀ β : B, ((Slot → BlockRes m₀ blk β) → ℝ) →ₗ[ℝ] ℝ) :
    ((Slot → ResidueSpace m₀) → ℝ) →ₗ[ℝ] ℝ :=
  (tensorLaw νB).comp (LinearMap.funLeft ℝ ℝ (slotRegroupPrefix m₀ blk))

theorem prefixMerge_apply (νB : ∀ β : B, ((Slot → BlockRes m₀ blk β) → ℝ) →ₗ[ℝ] ℝ)
    (G : (Slot → ResidueSpace m₀) → ℝ) :
    prefixMerge m₀ blk νB G = tensorLaw νB (fun z => G (slotRegroupPrefix m₀ blk z)) := rfl

/-- **The merged family** of a family of functionals on the block atoms: the merged prefix
functional `prefixMerge` at `none`, the same functional at a tail prime. -/
noncomputable def mergeLaws (L : ℕ)
    (ν : ∀ b : BlockAtom B J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ
  | none => prefixMerge m₀ blk (fun β => ν (.inl β))
  | some j => ν (.inr j)

omit [∀ L j, NeZero (p L j)] in
/-- The density of the merged prefix functional at a merged labelling `z₀` is the sum of the
block densities over the block labellings that regroup to `z₀`. -/
theorem lawDensity_prefixMerge (νB : ∀ β : B, ((Slot → BlockRes m₀ blk β) → ℝ) →ₗ[ℝ] ℝ)
    (z₀ : Slot → ResidueSpace m₀) :
    lawDensity (prefixMerge m₀ blk νB) z₀ =
      ∑ w : ∀ β, Slot → BlockRes m₀ blk β, (∏ β, lawDensity (νB β) (w β)) *
        (if slotRegroupPrefix m₀ blk (fun v β => w β v) = z₀ then 1 else 0) := rfl

/-- **The tensor product over the merged atoms is the tensor product over the block atoms**:
for every function `H` of the merged labels,
`(⊗_{b ∈ PaperAtom} (mergeLaws ν)_b)(H) = (⊗_{b ∈ BlockAtom} ν_b)(H ∘ regroup)`. -/
theorem tensorLaw_mergeLaws (L : ℕ)
    (ν : ∀ b : BlockAtom B J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (H : (Slot → ∀ b : PaperAtom J L, AtomLabel m₀ p L b) → ℝ) :
    tensorLaw (mergeLaws m₀ blk p L ν) H =
      tensorLaw ν (fun z => H (fun v => regroup m₀ blk p L (z v))) := by
  change (∑ z : ∀ b : PaperAtom J L, Slot → AtomLabel m₀ p L b,
      (∏ b, lawDensity (mergeLaws m₀ blk p L ν b) (z b)) * H (fun v b => z b v)) =
    ∑ x : ∀ b : BlockAtom B J L, Slot → BlockLabel m₀ blk p L b,
      (∏ b, lawDensity (ν b) (x b)) * H (fun v => regroup m₀ blk p L (fun b => x b v))
  -- the left side: split along `Option`
  rw [← (Equiv.piOptionEquivProd
    (β := fun b : PaperAtom J L => Slot → AtomLabel m₀ p L b)).symm.sum_comp,
    Fintype.sum_prod_type]
  -- the right side: split along `⊕`
  rw [← (Equiv.sumPiEquivProdPi
    (fun b : BlockAtom B J L => Slot → BlockLabel m₀ blk p L b)).symm.sum_comp,
    Fintype.sum_prod_type]
  simp only [Fintype.prod_option, Fintype.prod_sum_type]
  change (∑ z₀ : Slot → ResidueSpace m₀, ∑ zt : ∀ j : J L, Slot → ZMod (p L j),
      lawDensity (prefixMerge m₀ blk (fun β => ν (.inl β))) z₀ *
        (∏ j, lawDensity (ν (.inr j)) (zt j)) *
        H (fun v b => (Equiv.piOptionEquivProd
          (β := fun b : PaperAtom J L => Slot → AtomLabel m₀ p L b)).symm (z₀, zt) b v)) =
    ∑ w : ∀ β : B, Slot → BlockRes m₀ blk β, ∑ zt : ∀ j : J L, Slot → ZMod (p L j),
      (∏ β, lawDensity (ν (.inl β)) (w β)) * (∏ j, lawDensity (ν (.inr j)) (zt j)) *
        H (fun v => regroup m₀ blk p L (fun b => (Equiv.sumPiEquivProdPi
          (fun b : BlockAtom B J L => Slot → BlockLabel m₀ blk p L b)).symm (w, zt) b v))
  simp_rw [lawDensity_prefixMerge, sum_mul]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro zt _
  rw [sum_comm]
  apply sum_congr rfl
  intro w _
  simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul, sum_ite_eq, mem_univ, ↓reduceIte]
  congr 1
  congr 1
  funext v b
  cases b with
  | none => rfl
  | some j => rfl

/-- **The frame energies agree** (`def:record:functional`(e)): `energyFirst` over the block atoms
with `blockLift` is `energyFirst` over the merged atoms of `mergeLaws` with `atomLift`. -/
theorem energyFirst_mergeLaws
    (lam : ∀ L (b : BlockAtom B J L), ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (L : ℕ) (A : Finset ℤ) :
    energyFirst (Atom := BlockAtom B J) (Xb := BlockLabel m₀ blk p) lam (blockLift m₀ blk p) L A =
      energyFirst (Atom := PaperAtom J) (Xb := AtomLabel m₀ p)
        (fun L => mergeLaws m₀ blk p L (lam L)) (atomLift m₀ p) L A := by
  unfold energyFirst
  rw [form_barHalf, form_barHalf, tensorLaw_mergeLaws]
  rfl

/-- The same identity for `energyComparison`. -/
theorem energyComparison_mergeLaws
    (ν : ∀ L (b : BlockAtom B J L), ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (L : ℕ) (A : Finset ℤ) :
    energyComparison (Atom := BlockAtom B J) (Xb := BlockLabel m₀ blk p) ν (blockLift m₀ blk p)
        L A =
      energyComparison (Atom := PaperAtom J) (Xb := AtomLabel m₀ p)
        (fun L => mergeLaws m₀ blk p L (ν L)) (atomLift m₀ p) L A :=
  energyFirst_mergeLaws m₀ blk p ν L A

/-- The same identity for `energyMean`. -/
theorem energyMean_mergeLaws
    (M : ∀ L (b : BlockAtom B J L), ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (L : ℕ) (A : Finset ℤ) :
    energyMean (Atom := BlockAtom B J) (Xb := BlockLabel m₀ blk p) (blockLift m₀ blk p) M L A =
      energyMean (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (atomLift m₀ p)
        (fun L => mergeLaws m₀ blk p L (M L)) L A :=
  energyFirst_mergeLaws m₀ blk p M L A

/-- **Multilinear integrals agree**: the multilinear integral over the block atoms of slot inputs
`G v` is the multilinear integral over the merged atoms of the inputs `G v ∘ regroup⁻¹`. -/
theorem multilinearIntegral_mergeLaws (L : ℕ)
    (ν : ∀ b : BlockAtom B J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (G : Slot → (∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) → ℝ) :
    multilinearIntegral (tensorLaw ν) G =
      multilinearIntegral (tensorLaw (mergeLaws m₀ blk p L ν))
        (fun v y => G v ((regroup m₀ blk p L).symm y)) := by
  unfold multilinearIntegral
  rw [tensorLaw_mergeLaws]
  simp only [Equiv.symm_apply_apply]

end Sarkozy.BlockFrame

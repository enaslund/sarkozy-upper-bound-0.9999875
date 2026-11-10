module

public import Sarkozy.Spectral.GlueSupport
public import Sarkozy.Spectral.GlueRoute

/-!
# Glue, IX: `cor:spectral-criterion-blocks` for the cut laws, in WP-P's kernel form

`cut_blocks` takes a block of primes `p_i`, one per index `i`, with the cut operator
`Op_i = cutOp D (hne i)` at each. Suppose each satisfies the two bounds that
`thm:spectral-criterion` (a), (d) give:
`-g p_i^{-1/2} ‖v‖² ≤ ⟪v, Op_i v⟫ ≤ (1 + c⁺/p_i)‖v‖²`. Then the tensor product of the cut
operators satisfies
`⊗_i Op_i ⪰ -g b^{-1/2} ∏_i (1 + c⁺/p_i)`. The tensor product is the kernel
`∏_i K_i/Z_i` relative to `⊗_i μ_i` (WP-P's `block_cut_form`).

The proof uses:
* `cutForm_bounds_of_op`, which turns the operator bounds into kernel-form bounds;
* `tensorcomp_block_supp`, which is WP-P's `tensorcomp_block` without full support.

The half laws `λ(G⁺)` are used as they are.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.InfluenceGlue Sarkozy.Cuts

/-- **`cor:spectral-criterion-blocks` for the cut laws** (kernel form, WP-P's tensor step). -/
theorem cut_blocks {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) D.G).Nonempty) {g cplus bmin : ℝ}
    (hg : 0 ≤ g) (hcplus : 0 ≤ cplus) (hbmin : 0 < bmin) (hbp : ∀ i, bmin ≤ p i)
    (hgp : ∀ i, g * (√(p i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, cutOp D (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, cutOp D (hne i) v⟫_ℝ ≤ (1 + cplus / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, D.cut.Half → ZMod (p i)) → ℝ) :
    -(g * (√bmin)⁻¹ * ∏ i, (1 + cplus / p i)) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hne i)) Fn Fn :=
  tensorcomp_block_supp (fun i => D.halfLaw (hne i)) (fun i x y => D.cutK x y / D.cutZ (hne i))
    (fun i x y => by rw [D.cutK_symm]) (fun i => (p i : ℝ)) hg hcplus hbmin hbp hgp
    (fun i f => (cutForm_bounds_of_op D (hne i) (hlow i) (hup i) f).1)
    (fun i f => (cutForm_bounds_of_op D (hne i) (hlow i) (hup i) f).2) Fn

end Sarkozy.Spectral

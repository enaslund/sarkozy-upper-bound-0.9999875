module

public import Sarkozy.TheoremCBlock.Defs
public import Sarkozy.TheoremCBlock.Cancellation
public import Sarkozy.BlockFrame.Assembly
public import Sarkozy.TheoremC.Cancellation
public import Sarkozy.CancellationSteps.Paper

@[expose] public section

/-!
# `lem:record:density-can` on the block atoms, from the merged statement

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`; `def:cp1` (the reference is
a product over the atoms).

`TheoremC.DensityCancellation` is `lem:record:density-can` over the atoms of `PaperFrame` (the
whole prefix one atom). Over the block atoms the hypothesis of the lemma is weaker in one place
only: the law `ϱ` is a product over the blocks, so its prefix part is the product of the block
laws. This file merges a family of block laws into a family over `PaperFrame`'s atoms and checks
that every hypothesis of the merged statement holds:

* `mergeFiniteLaws ϱ`: the prefix law `blockAssembly` of the block laws, and the tail laws;
* `signedIntegral_mergeFiniteLaws`: its functionals are `mergeLaws` of the block functionals,
  so multilinear integrals agree (`multilinearIntegral_mergeFiniteLaws`);
* `mergeFiniteLaws_unif`: uniform one-slot marginals;
* `blockAssembly_support`, `mergeFiniteLaws_accept`: acceptance on the support, from acceptance
  at every block (`AcceptedPair` at a block is the merged condition restricted to its
  coordinates);
* `blockLift_regroup_symm`, `indexInputAt_regroup_symm`: the inputs read through `regroup⁻¹`
  are the merged inputs.

Hence **`densityCancellation_block`**: `TheoremC.DensityCancellation` (over `PaperFrame`'s
atoms) implies `TheoremCBlock.DensityCancellation` (over the block atoms), for every block
assignment; and **`densityCancellation_paper_block`**: D1's `densityCancellation_paper` gives the
block statement for the paper's data with no further hypothesis. Nothing about the tail atoms
changes: their laws, the (R4) clauses and the CRT structure are the same in both frames.
-/

open Finset Function

namespace Sarkozy.TheoremCBlock

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.BlockFrame

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- **The merged family of a family of block laws** (`def:cp1`): at the merged prefix the
product of the block laws (`blockAssembly`), at a tail prime the same law. -/
noncomputable def mergeFiniteLaws (L : ℕ)
    (ϱ : ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b)) :
    ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b)
  | none => blockAssembly m₀ blk (fun β => ϱ (.inl β))
  | some j => ϱ (.inr j)

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- The functionals of the merged family are the merged functionals. -/
theorem signedIntegral_mergeFiniteLaws (L : ℕ)
    (ϱ : ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b)) :
    (fun b => signedIntegral (mergeFiniteLaws m₀ blk p L ϱ b).weight) =
      mergeLaws m₀ blk p L (fun b => signedIntegral (ϱ b).weight) := by
  funext b
  cases b with
  | none => exact signedIntegral_blockAssembly m₀ blk (fun β => ϱ (.inl β))
  | some j => rfl

/-- **Multilinear integrals over the block product are multilinear integrals over the merged
product**, with the slot inputs read through `regroup⁻¹`. -/
theorem multilinearIntegral_mergeFiniteLaws (L : ℕ)
    (ϱ : ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b))
    (G : Slot → (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b) → ℝ) :
    multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b).weight) G =
      multilinearIntegral
        (tensorLaw fun b => signedIntegral (mergeFiniteLaws m₀ blk p L ϱ b).weight)
        (fun v y => G v ((regroup m₀ blk p L).symm y)) := by
  rw [signedIntegral_mergeFiniteLaws, multilinearIntegral_mergeLaws]

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- The merged family has uniform one-slot marginals when the block laws do. -/
theorem mergeFiniteLaws_unif (L : ℕ)
    (ϱ : ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b))
    (hϱ : ∀ b, HasUniformMarginals (ϱ b)) :
    ∀ b, HasUniformMarginals (mergeFiniteLaws m₀ blk p L ϱ b)
  | none => blockAssembly_unif m₀ blk (fun β => ϱ (.inl β)) (fun β => hϱ (.inl β))
  | some j => hϱ (.inr j)

/-- **The support of the assembled prefix law**: a merged labelling charged by `blockAssembly`
is the regrouping of block labellings each charged by its block law. -/
theorem blockAssembly_support (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    {z : Slot → ResidueSpace m₀} (hz : (blockAssembly m₀ blk μ₀).weight z ≠ 0) :
    ∃ y : Slot → ∀ β, BlockRes m₀ blk β, slotRegroupPrefix m₀ blk y = z ∧
      ∀ β, (μ₀ β).weight (fun v => y v β) ≠ 0 := by
  unfold blockAssembly at hz
  rw [PartV.map_weight_eq] at hz
  obtain ⟨y, hy, hy0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hz
  refine ⟨y, (Finset.mem_filter.mp hy).2, fun β => ?_⟩
  rw [PartV.tensor_weight] at hy0
  exact (Finset.prod_ne_zero_iff.mp hy0) β (Finset.mem_univ β)

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- **Acceptance on the support of the merged family** (hypothesis (b) of
`lem:record:density-can`): if every block law and every tail law below `P₅` accepts the pair
`(u, v)` on its support, the merged prefix law accepts it at every prefix coordinate. -/
theorem mergeFiniteLaws_accept (pp ep : J₀ → ℕ) (P5 : ℕ) (L : ℕ)
    (ϱ : ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b)) (u v : Slot)
    (hacc : ∀ b : BlockAtom Bk J L, (∀ j, b = Sum.inr j → p L j < P5) → ∀ z,
      (ϱ b).weight z ≠ 0 → AcceptedPair m₀ blk p pp ep L b (z u) (z v)) :
    ∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z,
      (mergeFiniteLaws m₀ blk p L ϱ b).weight z ≠ 0 →
        TheoremC.AcceptedPair m₀ p pp ep L b (z u) (z v)
  | none, _, z, hz => by
      obtain ⟨y, rfl, hy⟩ := blockAssembly_support m₀ blk (fun β => ϱ (.inl β)) hz
      intro i
      exact hacc (.inl (blk i)) (fun _ h => absurd h Sum.inl_ne_inr) (fun v => y v (blk i))
        (hy (blk i)) ⟨i, rfl⟩
  | some j, hb, z, hz => hacc (.inr j) (fun j' h => hb j' (congrArg some (Sum.inr.inj h))) z hz

omit [Fintype Bk] [DecidableEq Bk] in
/-- The lift read on the block labels of `regroup⁻¹ y` is the lift at `y`. -/
theorem blockLift_regroup_symm (L : ℕ) (A : Finset ℤ)
    (y : ∀ b : PaperAtom J L, AtomLabel m₀ p L b) :
    blockLift m₀ blk p L A ((regroup m₀ blk p L).symm y) = atomLift m₀ p L A y := by
  unfold blockLift
  rw [Equiv.apply_symm_apply]

section Transfer

variable {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

omit [Fintype Bk] [DecidableEq Bk] [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- The input `g^{I_b, M₀, s}` read on the block labels of `regroup⁻¹ y` is the merged input at
`y`. -/
theorem indexInputAt_regroup_symm (L : ℕ) (A : Finset ℤ)
    (ω : ZMod blockScale × ZMod (modulus pr h)) (y : ∀ b : PaperAtom J L, AtomLabel m₀ p L b) :
    indexInputAt m₀ blk p pr h L A ω ((regroup m₀ blk p L).symm y) =
      TheoremC.indexInputAt m₀ p pr h L A ω y := by
  change TheoremC.indexInputAt m₀ p pr h L A ω
    (regroup m₀ blk p L ((regroup m₀ blk p L).symm y)) = _
  rw [Equiv.apply_symm_apply]

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- **`lem:record:density-can` on the block atoms**, from the statement over `PaperFrame`'s
atoms (the prefix merged into one atom). The block product `ϱ` is merged into `mergeFiniteLaws ϱ`
(prefix law `blockAssembly` of the block laws, the same tail laws); its uniform marginals, the
tail clauses (a) and the acceptance (b) hold, the inputs are the merged inputs read through
`regroup`, and the multilinear integral is the same (`multilinearIntegral_mergeFiniteLaws`). -/
theorem densityCancellation_block (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hDC : TheoremC.DensityCancellation m₀ p pr h P5 pp ep) :
    DensityCancellation m₀ blk p pr h P5 pp ep := by
  obtain ⟨Ccan, hC, Lstar, hDC⟩ := hDC
  refine ⟨Ccan, hC, Lstar, fun L hL A hA ϱ hϱ u v huv htail hacc bI s r hbI hr G hGu hGv hGw => ?_⟩
  rw [multilinearIntegral_mergeFiniteLaws]
  refine hDC L hL A hA (mergeFiniteLaws m₀ blk p L ϱ) (mergeFiniteLaws_unif m₀ blk p L ϱ hϱ) u v
    huv htail (mergeFiniteLaws_accept m₀ blk p pp ep P5 L ϱ u v hacc) bI s r hbI hr _ ?_ ?_ ?_
  · funext y
    rw [hGu]
    exact indexInputAt_regroup_symm m₀ blk p pr h L A _ y
  · funext y
    rw [hGv]
    exact indexInputAt_regroup_symm m₀ blk p pr h L A _ y
  · intro w hwu hwv
    rcases hGw w hwu hwv with hw | ⟨ω, hw⟩
    · left
      funext y
      rw [hw]
      exact blockLift_regroup_symm m₀ blk p L A y
    · right
      refine ⟨ω, ?_⟩
      funext y
      rw [hw]
      exact indexInputAt_regroup_symm m₀ blk p pr h L A ω y

end Transfer

/-- **`lem:record:density-can` for the paper's data on the block atoms** (D1's
`CancellationSteps.densityCancellation_paper`, transferred by `densityCancellation_block`):
for every block assignment `blk` of the fixed primes `𝒫₁ ∪ 𝒫₃`, with no hypothesis. -/
theorem densityCancellation_paper_block {Bk : Type} [Fintype Bk] [DecidableEq Bk]
    (blk : CancellationSteps.PaperJ0 → Bk) :
    DensityCancellation CancellationSteps.paperM0 blk CancellationSteps.paperTail
      CancellationSteps.paperPr CancellationSteps.paperH PartV.P5 CancellationSteps.paperPP
      CancellationSteps.paperEP :=
  densityCancellation_block _ blk _ _ _ _ _ _ CancellationSteps.densityCancellation_paper

end Sarkozy.TheoremCBlock

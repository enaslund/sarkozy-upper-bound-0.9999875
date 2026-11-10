module

public import Sarkozy.PaperFrame.Inputs
public import Sarkozy.PaperFrame.Reference

@[expose] public section

/-!
# The paper's prefix atoms: blocks of the fixed coordinates

`paper/sections/09_comparison_theorem.tex`, `def:cp0`(b) and `def:price`;
`paper/sections/18_design.tex`, `def:construction`(b).

In `Sarkozy.PaperFrame` the whole fixed prefix `X₀ = ∏_{i ∈ J₀} ℤ/m₀ᵢℤ` is one atom (`none`).
The paper's atoms of the prefix are smaller: each square-clique prime `{p}` of `𝒫₁`, and the
middle and upper blocks of `𝒫₃` (`def:record:exact-blocks`, `def:record:upper-bands`(b)). Each
atom is priced separately by its own selection factor `q_𝔟^{2a}` (`def:price`).

Here the fixed coordinates `J₀` are partitioned by a *block assignment* `blk : J₀ → B` into the
fibres `BlockIdx blk β = {i // blk i = β}`, and the atoms at the scale `L` are
`BlockAtom B J L = B ⊕ J L`:

* `Sum.inl β`: the block `β`, with alphabet `BlockRes m₀ blk β = ∏_{blk i = β} ℤ/m₀ᵢℤ`;
* `Sum.inr j`: the tail prime `p_j`, with alphabet `ℤ/p_jℤ`, as in `PaperFrame`.

The group `G_N`, the lift `F_A` and the inputs are unchanged: `regroup` is the explicit
equivalence between the block labels and the labels of `PaperFrame`'s atoms (it regroups the
prefix coordinates by block), and `blockLift`, `blockInput` are `atomLift`, `atomInput` read
through it. The merged frame of `PaperFrame` is the case `B = Unit`.
-/

open Finset Function

namespace Sarkozy.BlockFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {B : Type} [Fintype B] [DecidableEq B] (blk : J₀ → B)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The fixed coordinates of the block `β`: the fibre `{i // blk i = β}`. -/
abbrev BlockIdx (β : B) : Type := {i : J₀ // blk i = β}

/-- The moduli `m₀ᵢ` of the coordinates of the block `β`. -/
abbrev blockModuli (β : B) (i : BlockIdx blk β) : ℕ := m₀ i.1

instance blockModuli_neZero (β : B) (i : BlockIdx blk β) : NeZero (blockModuli m₀ blk β i) :=
  inferInstanceAs (NeZero (m₀ i.1))

/-- The alphabet `∏_{blk i = β} ℤ/m₀ᵢℤ` of the block `β`. -/
abbrev BlockRes (β : B) : Type := ResidueSpace (blockModuli m₀ blk β)

/-- The atoms at the scale `L`: the prefix blocks (`Sum.inl β`) and the tail primes
(`Sum.inr j`). -/
abbrev BlockAtom (B : Type) (J : ℕ → Type) (L : ℕ) : Type := B ⊕ J L

/-- The alphabet of an atom: the residues of a block, or `ℤ/p_jℤ` at a tail prime. -/
abbrev BlockLabel (L : ℕ) : BlockAtom B J L → Type
  | .inl β => BlockRes m₀ blk β
  | .inr j => ZMod (p L j)

instance blockLabelFintype (L : ℕ) : ∀ b, Fintype (BlockLabel m₀ blk p L b)
  | .inl β => inferInstanceAs (Fintype (BlockRes m₀ blk β))
  | .inr j => inferInstanceAs (Fintype (ZMod (p L j)))

instance blockLabelDecidableEq (L : ℕ) : ∀ b, DecidableEq (BlockLabel m₀ blk p L b)
  | .inl β => inferInstanceAs (DecidableEq (BlockRes m₀ blk β))
  | .inr j => inferInstanceAs (DecidableEq (ZMod (p L j)))

instance blockLabelNonempty (L : ℕ) : ∀ b, Nonempty (BlockLabel m₀ blk p L b)
  | .inl β => inferInstanceAs (Nonempty (BlockRes m₀ blk β))
  | .inr j => inferInstanceAs (Nonempty (ZMod (p L j)))

/-- The prefix residues regrouped by block: `∏_β ∏_{blk i = β} ℤ/m₀ᵢℤ ≃ ∏_i ℤ/m₀ᵢℤ`. -/
def prefixRegroup : (∀ β, BlockRes m₀ blk β) ≃ ResidueSpace m₀ where
  toFun x i := x (blk i) ⟨i, rfl⟩
  invFun y _ i := y i.1
  left_inv x := by
    funext β i
    obtain ⟨i, rfl⟩ := i
    rfl
  right_inv _ := rfl

/-- **The block labels are the labels of `PaperFrame`'s atoms**: the blocks are regrouped into
the merged prefix `X₀`, the tail primes are unchanged. -/
def regroup (L : ℕ) : (∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) ≃
    (∀ b : PaperAtom J L, AtomLabel m₀ p L b) where
  toFun x
    | none => prefixRegroup m₀ blk (fun β => x (.inl β))
    | some j => x (.inr j)
  invFun y
    | .inl β => (prefixRegroup m₀ blk).symm (y none) β
    | .inr j => y (some j)
  left_inv x := by
    funext b
    cases b with
    | inl β =>
        change (prefixRegroup m₀ blk).symm (prefixRegroup m₀ blk (fun β => x (.inl β))) β = x
            (.inl β)
        rw [Equiv.symm_apply_apply]
    | inr j => rfl
  right_inv y := by
    funext b
    cases b with
    | none =>
        change prefixRegroup m₀ blk (fun β => (prefixRegroup m₀ blk).symm (y none) β) = y none
        exact Equiv.apply_symm_apply _ _
    | some j => rfl

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [Fintype B] [DecidableEq B]
  [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
theorem regroup_apply_none (L : ℕ) (x : ∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) (i : J₀) :
    regroup m₀ blk p L x none i = x (.inl (blk i)) ⟨i, rfl⟩ := rfl

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [Fintype B] [DecidableEq B]
  [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
theorem regroup_apply_some (L : ℕ) (x : ∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) (j : J L) :
    regroup m₀ blk p L x (some j) = x (.inr j) := rfl

/-- The block labels are the joined group `G_N` of `def:record:functional`. -/
noncomputable def blockGroupEquiv (L : ℕ) :
    (∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) ≃ ResidueSpace (joinModuli m₀ (p L)) :=
  (regroup m₀ blk p L).trans (atomGroupEquiv m₀ p L)

/-- The paper's lift `F_A = 𝓛_{[N],N} 1_A`, read on the block labels: `atomLift` through
`regroup`. -/
noncomputable def blockLift (L : ℕ) (A : Finset ℤ)
    (x : ∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) :
    ℝ :=
  atomLift m₀ p L A (regroup m₀ blk p L x)

omit [Fintype B] [DecidableEq B] in
theorem blockLift_eq (L : ℕ) (A : Finset ℤ) (x : ∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) :
    blockLift m₀ blk p L A x = (wholeLift (joinModuli m₀ (p L)) (paperCutoff (blockScale * L))
      (blockScale * L) A (blockGroupEquiv m₀ blk p L x)).re := rfl

section Inputs

variable {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The input `g^{I_b, M₀, s}` (`def:record:functional`(f)) at the query index `η`, read on the
block labels: `atomInput` through `regroup`. -/
noncomputable def blockInput (L : ℕ) (A : Finset ℤ) {E : Type} (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) (x : ∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) :
    ℝ :=
  atomInput m₀ p pr h hcop L A e η (regroup m₀ blk p L x)

omit [Fintype B] [DecidableEq B] in
/-- The mean identities `E_η g^{I_b,M₀,s} = F_A` on the block labels (`expect_atomInput`). -/
theorem expect_blockInput (L : ℕ) (A : Finset ℤ) {E : Type} (e : E)
    (x : ∀ b : BlockAtom B J L, BlockLabel m₀ blk p L b) :
    (FiniteLaw.uniform (∀ j, CoordSpace blockScale pr h j)).expect
        (fun η => blockInput m₀ blk p pr h hcop L A e η x) = blockLift m₀ blk p L A x :=
  expect_atomInput m₀ p pr h hcop L A e (regroup m₀ blk p L x)

end Inputs

/-! ## The reference laws on the block atoms -/

/-- The per-atom reference functionals: the block laws `μ_β` at the prefix blocks, `μ_p` at the
tail prime `p` (`def:record:functional`(d), `def:cp1`). -/
noncomputable def blockRefLaws (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    ∀ b : BlockAtom B J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ
  | .inl β => signedIntegral (μ₀ β).weight
  | .inr j => signedIntegral (μp (p L j)).weight

end Sarkozy.BlockFrame

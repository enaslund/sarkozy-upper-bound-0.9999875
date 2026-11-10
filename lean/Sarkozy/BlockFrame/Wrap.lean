module

public import Sarkozy.BlockFrame.Atoms
public import Sarkozy.PaperFrame.WrapSplit

@[expose] public section

/-!
# The expansion and the wrap split on the block atoms (`lem:record:wrap-expansion`)

`paper/sections/10_comparison_lemmas.tex`, `eq:record:expansion` and `lem:record:wrap-expansion`.
`PaperFrame`'s `paper_signedIndexForm_sub_eq`, `wrapForm`, `paper_wrap_hexp` and `paper_wrap_bound`
restated for the block atoms of `Sarkozy.BlockFrame.Atoms`, with the inputs `blockInput` and the
lift `blockLift`. The proofs are those of `PaperFrame` (the expansion is generic in the atoms; the
mean identity is `expect_blockInput`).
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.BlockFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {B : Type} [Fintype B] [DecidableEq B] (blk : J₀ → B)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- `eq:record:expansion` for the paper's objects: with the paper's coupled index, inputs
`g^{I_b,M₀,s}` at both ends and lift `F_A`, for every comparison law `ν`,
`J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} I_{ν,𝒮}`. -/
theorem block_signedIndexForm_sub_eq (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ) :
    signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => blockInput m₀ blk p pr h hcop L A e)
        (fun L A e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p) L A -
        2 ^ Fintype.card E * energyComparison ν (blockLift m₀ blk p) L A =
      ∑ S ∈ (univ : Finset E).powerset.filter (fun S => S ≠ ∅),
        (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
          (FiniteLaw.uniform (E → ∀ j, CoordSpace blockScale pr h j)).expect (fun ω =>
            reservedCut.form (tensorLaw (ν L))
              (productHalf u (fun e => blockInput m₀ blk p pr h hcop L A e)
                  (blockLift m₀ blk p L A) ω)
              (act (piKron (fun e => if e ∈ S then
                  piKron (coordTransition blockScale pr h (μ e))
                else meanMatrix (∀ j, CoordSpace blockScale pr h j)))
                (productHalf w (fun e => blockInput m₀ blk p pr h hcop L A e)
                    (blockLift m₀ blk p L A)) ω)) :=
  signedIndexForm_sub_eq (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
    (fun L A e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p)
    (fun L A e y => expect_blockInput m₀ blk p pr h hcop L A e y) L A

/-- The coupled form `I_{ν,𝒮,𝒲}` with the wrapping queries `𝒲 ⊆ 𝒮` (WP-S operator form). -/
noncomputable def blockWrapForm (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (u w : E → reservedCut.Half)
    (ν : ∀ L b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ)
    (S W : Finset E) : ℝ :=
  (FiniteLaw.uniform (E → ∀ j, CoordSpace blockScale pr h j)).expect (fun ω =>
    reservedCut.form (tensorLaw (ν L))
      (productHalf u (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A) ω)
      (act (piKron (fun e => if e ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (μ e))
          else if e ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (μ e))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)))
        (productHalf w (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A)) ω))

/-- **The hypothesis `hexp` of `wrap_summation` for the paper's objects**:
`J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} ∑_{𝒲 ⊆ 𝒮} I_{ν,𝒮,𝒲}`. -/
theorem block_wrap_hexp (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ) :
    signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => blockInput m₀ blk p pr h hcop L A e)
        (fun L A e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p) L A -
        2 ^ Fintype.card E * energyComparison ν (blockLift m₀ blk p) L A =
      ∑ S ∈ (univ : Finset E).powerset.filter (fun S => S ≠ ∅),
        (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
          ∑ W ∈ S.powerset, blockWrapForm m₀ blk p pr h hcop μ u w ν L A S W := by
  rw [block_signedIndexForm_sub_eq m₀ blk p pr h hcop μ hμ hμ1 t hnorm u w hu hw ν L A]
  apply sum_congr rfl
  intro S _
  congr 1
  unfold blockWrapForm
  rw [← expect_finset_sum]
  apply FiniteLaw.expect_congr
  intro ω
  have hsplit : piKron (fun e => if e ∈ S then piKron (coordTransition blockScale pr h (μ e))
      else meanMatrix (∀ j, CoordSpace blockScale pr h j)) =
      ∑ W ∈ S.powerset, piKron (fun e => if e ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (μ e))
        else if e ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (μ e))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) := by
    simp_rw [piKron_coordTransition_split]
    exact piKron_active_split _ _ _ S
  rw [hsplit, act_sum_left, Finset.sum_apply, ← cutBilin_apply, map_sum]
  simp only [cutBilin_apply]

/-- **The wrap summation for the paper's objects** (`lem:record:wrap-expansion`): if every
non-wrapping coupled form `I_{ν,𝒮,𝒲}` (`𝒲 ≠ 𝒮`) is at most `r` in absolute value and every
fully wrapping one `I_{ν,𝒮,𝒮}` at most `(B' x^{|𝒮|} + ε) Y + r'`, then
`|J_ν − 2^k Y_ν| ≤ B'[(2 + x)^k − 2^k] Y + 3^k ε Y + 4^k r + 3^k r'`
(`Sarkozy.Comparison.wrap_summation` with `block_wrap_hexp`). -/
theorem block_wrap_bound (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ)
    {Y B' x ε r r' : ℝ} (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hnon : ∀ S W, W ⊆ S → W ≠ S → |blockWrapForm m₀ blk p pr h hcop μ u w ν L A S W| ≤ r)
    (hwrap : ∀ S, S ≠ ∅ → |blockWrapForm m₀ blk p pr h hcop μ u w ν L A S S| ≤
      (B' * x ^ S.card + ε) * Y + r') :
    |signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => blockInput m₀ blk p pr h hcop L A e)
        (fun L A e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p) L A -
        2 ^ Fintype.card E * energyComparison ν (blockLift m₀ blk p) L A| ≤
      B' * ((2 + x) ^ Fintype.card E - 2 ^ Fintype.card E) * Y +
        3 ^ Fintype.card E * ε * Y + 4 ^ Fintype.card E * r + 3 ^ Fintype.card E * r' :=
  wrap_summation (blockWrapForm m₀ blk p pr h hcop μ u w ν L A) hY hε hr hr'
    (block_wrap_hexp m₀ blk p pr h hcop μ hμ hμ1 t hnorm u w hu hw ν L A) hnon hwrap

end Sarkozy.BlockFrame

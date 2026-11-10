module

public import Sarkozy.Spectral.GlueBlocks
public import Sarkozy.Spectral.Blocks

/-!
# Block caps from per-prime envelopes

`paper/sections/25_upper_reference.tex`. Three statements of the upper reference end with the
same step: a cut operator satisfies `-g p^{-1/2} ⪯ Op ⪯ (1 + B/p)` at every prime of a block
`𝔅` of primes `p ≥ X > 1` with `log q_𝔅 = ∑_{p∈𝔅} log p ≤ L`, and the normalized block
operator `⊗_{p∈𝔅} Op` is then at least `-d b_𝔅^{-1/2}`, `d = g exp(B L/(X log X))`. These are
the "Consequently" parts of `lem:record:monotone-endpoint` and `lem:upper-completed-root` and
the block statement of `prop:observed-caps`; the paper cites `lem:spec:tensorcomp` and
`lem:majorant`(c) for it.

* `prod_one_add_le_exp`: `∏_{p∈𝔅} (1 + c/p) ≤ exp(c L/(X log X))` (`lem:majorant`(c)).
* `cut_block_cap`: the block step for the actual cut operators `cutOp D` of spectral data `D`
  (for instance the root cuts LL20 and LL22), in the kernel form of WP-P's tensor step
  (`Sarkozy.Spectral.cut_blocks`).
* `matrix_block_cap`: the same for real symmetric matrices (`Sarkozy.Spectral.blocks_lower`),
  with `X` in place of the least prime.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.UpperReference

open Sarkozy Sarkozy.InfluenceGlue Sarkozy.Cuts Sarkozy.Spectral

/-- **`lem:majorant`(c), block inflation**: if every `p_i ≥ X > 1` and `∑ log p_i ≤ L`, then
`∏ (1 + c/p_i) ≤ exp(c L/(X log X))` for `c ≥ 0`. -/
theorem prod_one_add_le_exp {ι : Type*} [Fintype ι] (p : ι → ℝ) {c X L : ℝ} (hc : 0 ≤ c)
    (hX : 1 < X) (hXp : ∀ i, X ≤ p i) (hL : ∑ i, Real.log (p i) ≤ L) :
    ∏ i, (1 + c / p i) ≤ Real.exp (c * L / (X * Real.log X)) := by
  have hpos : ∀ i, 0 < p i := fun i => by linarith [hXp i]
  calc ∏ i, (1 + c / p i) ≤ ∏ i, Real.exp (c / p i) :=
        Finset.prod_le_prod₀ (fun i _ => by
          have := div_nonneg hc (hpos i).le
          linarith) (fun i _ => by
          have := Real.add_one_le_exp (c / p i)
          linarith)
    _ = Real.exp (∑ i, c / p i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (c * L / (X * Real.log X)) := by
        apply Real.exp_le_exp.mpr
        have h1 := sum_inv_le_of_sum_log_le p hX hXp hL
        calc ∑ i, c / p i = c * ∑ i, 1 / p i := by
              rw [Finset.mul_sum]
              exact Finset.sum_congr rfl fun i _ => by ring
          _ ≤ c * (L / (X * Real.log X)) := mul_le_mul_of_nonneg_left h1 hc
          _ = c * L / (X * Real.log X) := by ring

/-- **The block cap of a cut** (the block step of `lem:record:monotone-endpoint`,
`lem:upper-completed-root` and `prop:observed-caps`; `lem:spec:tensorcomp`(b),(c)). Let `D`
be spectral data, and let the block consist of the primes `p_i ≥ b ≥ X > 1` (`b` the least
prime, or any lower bound) with `∑ log p_i ≤ L`. If at every `p_i` the cut operator satisfies
`-g p_i^{-1/2} ⪯ Op ⪯ (1 + B/p_i)` and `g p_i^{-1/2} < 1`, then the normalized block operator
`⊗_i Op_i` (the kernel `∏_i K_i/Z_i` relative to `⊗_i λ(G⁺)`) is at least
`-g exp(B L/(X log X)) b^{-1/2}`. -/
theorem cut_block_cap {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) D.G).Nonempty) {g B X L b : ℝ}
    (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i)
    (hL : ∑ i, Real.log (p i) ≤ L) (hgp : ∀ i, g * (√(p i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, cutOp D (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, cutOp D (hne i) v⟫_ℝ ≤ (1 + B / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, D.cut.Half → ZMod (p i)) → ℝ) :
    -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hne i)) Fn Fn := by
  have hb : 0 < b := by linarith
  have h := cut_blocks D p hne hg hB hb hbp hgp hlow hup Fn
  have hprod := prod_one_add_le_exp (fun i => (p i : ℝ)) hB hX (fun i => hXb.trans (hbp i)) hL
  have hn : 0 ≤ Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 := sq_nonneg _
  have hsb : 0 ≤ (√b)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hcmp : g * (√b)⁻¹ * ∏ i, (1 + B / (p i : ℝ)) ≤
      g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹ := by
    calc g * (√b)⁻¹ * ∏ i, (1 + B / (p i : ℝ)) ≤
          g * (√b)⁻¹ * Real.exp (B * L / (X * Real.log X)) :=
          mul_le_mul_of_nonneg_left hprod (mul_nonneg hg hsb)
      _ = g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹ := by ring
  calc -(g * Real.exp (B * L / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      -(g * (√b)⁻¹ * ∏ i, (1 + B / (p i : ℝ))) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 :=
        mul_le_mul_of_nonneg_right (by linarith) hn
    _ ≤ _ := h

/-- **The block cap for matrices** (`cor:spectral-criterion-blocks` with the threshold `X`):
for real symmetric `A_j` with `-g p_j^{-1/2} ⪯ A_j ⪯ (1 + B/p_j)` at primes `p_j ≥ b ≥ X > 1`
with `∑ log p_j ≤ L`, `⊗_j A_j ⪰ -g exp(B L/(X log X)) b^{-1/2}`. -/
theorem matrix_block_cap {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*}
    [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hA : ∀ j, (A j).transpose = A j) (p : K → ℝ)
    {g B L X b : ℝ} (hg0 : 0 ≤ g) (hB0 : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hpb : ∀ j, b ≤ p j) (hL : ∑ j, Real.log (p j) ≤ L) (hgr : ∀ j, g / √(p j) ≤ 1)
    (hlow : ∀ j x, -(g / √(p j)) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A j).mulVec x))
    (hup : ∀ j x, x ⬝ᵥ ((A j).mulVec x) ≤ (1 + B / p j) * (x ⬝ᵥ x)) (x : (∀ j, Ω j) → ℝ) :
    -(g * Real.exp (B * L / (X * Real.log X)) / √b) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ ((Sarkozy.IndexSupport.piKron A).mulVec x) :=
  blocks_lower A hA p hg0 hB0 hX hXb hpb hL hgr hlow hup x

end Sarkozy.UpperReference

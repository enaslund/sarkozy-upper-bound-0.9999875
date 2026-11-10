module

public import Sarkozy.Spectral.GlueBlocks
public import Sarkozy.L20Cap.Caps





@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Cuts Sarkozy.Spectral

/-- **`lem:layer12-caps`(b)**: the block cap
`𝖠_𝔅 ⪰ -g_X exp(c⁺_X L_loc/(X log X)) b^{-1/2}` from the prime caps (a). -/
theorem layer12_block_cap {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U) {ι : Type*}
    [Fintype ι] [DecidableEq ι] (p : ι → ℕ) [∀ i, Fact (p i).Prime]
    (hne : ∀ i, (Labellings.injLabellings (ZMod (p i)) D.G).Nonempty) {g cplus X Lloc b : ℝ}
    (hg : 0 ≤ g) (hcplus : 0 ≤ cplus) (hX : 1 < X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ p i)
    (hL : ∑ i, Real.log (p i) ≤ Lloc) (hgp : ∀ i, g * (√(p i : ℝ))⁻¹ < 1)
    (hlow : ∀ i v, -(g * (√(p i : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ ⟪v, cutOp D (hne i) v⟫_ℝ)
    (hup : ∀ i v, ⟪v, cutOp D (hne i) v⟫_ℝ ≤ (1 + cplus / p i) * ‖v‖ ^ 2)
    (Fn : (∀ i, D.cut.Half → ZMod (p i)) → ℝ) :
    -(g * Real.exp (cplus * Lloc / (X * Real.log X)) * (√b)⁻¹) *
        Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (FiniteLaw.pi fun i => D.halfLaw (hne i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hne i)) Fn Fn := by
  have hb : 0 < b := by linarith
  have h := cut_blocks D p hne hg hcplus hb hbp hgp hlow hup Fn
  have hprod := prod_one_add_le_exp (fun i => (p i : ℝ)) hcplus hX
    (fun i => hXb.trans (hbp i)) hL
  have hN : 0 ≤ Recentering.nrm (FiniteLaw.pi fun i => D.halfLaw (hne i)) Fn ^ 2 := sq_nonneg _
  have hsb : 0 ≤ (√b)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hcmp : g * (√b)⁻¹ * ∏ i, (1 + cplus / (p i : ℝ)) ≤
      g * Real.exp (cplus * Lloc / (X * Real.log X)) * (√b)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hprod (mul_nonneg hg hsb)
    linarith
  have := mul_le_mul_of_nonneg_right hcmp hN
  linarith

end Sarkozy.L20Cap

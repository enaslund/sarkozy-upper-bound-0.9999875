module

public import Sarkozy.SpectralD.TailErrorBounds
public import Sarkozy.SpectralD.CollisionOperators
public import Sarkozy.F3Kernel.ProductionOperators

/-!
# The root character-expansion allowances in the tail range

The star estimates, complete nonstar certificates, and collision theorem
supply all four character-expansion bounds of the root spectral criteria.
The remaining coupling and degree-one estimates are separate inputs.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Sarkozy.Labellings Sarkozy.SecondOrder Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

theorem LL20_tail_expansion_bounds (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) Root.LL20.G).Nonempty)
    (he : ∀ i, graphCountError (p := p) Root.LL20.halfGraph i < 1) :
    let r := (Real.sqrt p)⁻¹
    let a := 2⁻¹ ^ 200 * r
    let L := graphPinned hW Root.LL20.halfGraph (Root.LL20.half_nonempty hne) he
    (∀ v, ‖Cx.nsOp Root.LL20 hne v‖ ≤ a * ‖v‖) ∧
    (∀ v, ‖Cx.collOp Root.LL20 hne v‖ ≤ a * ‖v‖) ∧
    2 * Spectral.starZstar L Root.LL20.Nset (Spectral.starCoef (p := p) Root.LL20) +
      a + a ≤ 1 / 100 ∧
    (a + a) / (1 - 1 / 100) +
      ((Spectral.starMstar L Root.LL20.Nset (Spectral.starCoef (p := p) Root.LL20) +
        a + a) / (1 - 1 / 100)) ^ 2 ≤ 1 / 4 * r := by
  dsimp only
  refine ⟨F3Kernel.LL20_nsOp_tail hW h4 hp hne, LL20_collOp_tail hW hp hne, ?_, ?_⟩
  · apply tail_normalizer_scalar (by positivity) (tail_rp_le hp) _ le_rfl le_rfl
    simpa only [one_div] using LL20_starZstar hW (by omega) (Root.LL20.half_nonempty hne) he
  · apply tail_perpendicular_scalar (by positivity) (tail_rp_le hp)
      (Real.sqrt_nonneg _) (by positivity) (by positivity) _ le_rfl le_rfl
    simpa only [Spectral.starMstar, one_div] using
      LL20_starMstar hW (by omega) (Root.LL20.half_nonempty hne) he

theorem LL22_tail_expansion_bounds (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hne : (injLabellings (ZMod p) Root.LL22.G).Nonempty)
    (he : ∀ i, graphCountError (p := p) Root.LL22.halfGraph i < 1) :
    let r := (Real.sqrt p)⁻¹
    let a := 2⁻¹ ^ 200 * r
    let L := graphPinned hW Root.LL22.halfGraph (Root.LL22.half_nonempty hne) he
    (∀ v, ‖Cx.nsOp Root.LL22 hne v‖ ≤ a * ‖v‖) ∧
    (∀ v, ‖Cx.collOp Root.LL22 hne v‖ ≤ a * ‖v‖) ∧
    2 * Spectral.starZstar L Root.LL22.Nset (Spectral.starCoef (p := p) Root.LL22) +
      a + a ≤ 1 / 100 ∧
    (a + a) / (1 - 1 / 100) +
      ((Spectral.starMstar L Root.LL22.Nset (Spectral.starCoef (p := p) Root.LL22) +
        a + a) / (1 - 1 / 100)) ^ 2 ≤ 1 / 4 * r := by
  dsimp only
  refine ⟨F3Kernel.LL22_nsOp_tail hW h4 hp hne, LL22_collOp_tail hW hp hne, ?_, ?_⟩
  · apply tail_normalizer_scalar (by positivity) (tail_rp_le hp) _ le_rfl le_rfl
    simpa only [one_div] using LL22_starZstar hW (by omega) (Root.LL22.half_nonempty hne) he
  · apply tail_perpendicular_scalar (by positivity) (tail_rp_le hp)
      (Real.sqrt_nonneg _) (by positivity) (by positivity) _ le_rfl le_rfl
    simpa only [Spectral.starMstar, one_div] using
      LL22_starMstar hW (by omega) (Root.LL22.half_nonempty hne) he

end Sarkozy.SpectralD

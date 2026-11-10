module

public import Sarkozy.PositiveRoots.CoherentCubeKernel
public import Sarkozy.Cuts.Projection

/-! The paper's full score bound `‖H‖ ≤ D₆ r / 3` on the actual chamber law. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.Cuts Sarkozy.Recentering
open Sarkozy.Labellings Sarkozy.PartV Sarkozy.PartV.CoherentDictionary
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime]

noncomputable def chamberCubeRatio
    (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty) (x : Fin 6 → ZMod p) : ℝ :=
  (graphLaw L20Cap.G6 hne).weight x * (p : ℝ) ^ 6

theorem chamberCubeRatio_nonneg (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (x : Fin 6 → ZMod p) : 0 ≤ chamberCubeRatio hne x :=
  mul_nonneg ((graphLaw L20Cap.G6 hne).nonneg x) (by positivity)

theorem chamberCubeRatio_density (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (x : Fin 6 → ZMod p) :
    (graphLaw L20Cap.G6 hne).weight x = chamberCubeRatio hne x * (cubeLaw p).weight x := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  rw [cubeLaw_weight, chamberCubeRatio, inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hp),
    mul_one]

theorem chamberCubeRatio_le (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty) (x : Fin 6 → ZMod p) :
    chamberCubeRatio hne x ≤ L20Cap.chamberCubeDensity p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact (le_div_iff₀ (pow_pos hp 6)).mp (L20Cap.G6_density hp3 hp7 hne x)

/-- This is a full bilinear norm estimate; neither argument is required to be centered. -/
theorem chamber_score_norm (hp3 : p % 4 = 3) (hp7 : 7 < p)
    (hne : (injLabellings (ZMod p) L20Cap.G6).Nonempty)
    (f g : (Fin 6 → ZMod p) → ℝ) :
    |kernelForm (graphLaw L20Cap.G6 hne) (graphLaw L20Cap.G6 hne)
      (fun x y => coherentScore p dictionary39 (chamberConfiguration x y)) f g| ≤
        (L20Cap.chamberCubeDensity p * rp p / 3) *
          nrm (graphLaw L20Cap.G6 hne) f * nrm (graphLaw L20Cap.G6 hne) g := by
  have h := density_norm_le (graphLaw L20Cap.G6 hne) (cubeLaw p)
    (fun x y => coherentScore p dictionary39 (chamberConfiguration x y))
    (div_nonneg (rp_nonneg (p := p)) (by norm_num : (0 : ℝ) ≤ 3))
    (chamberCubeRatio_density hne) (chamberCubeRatio_nonneg hne)
    (chamberCubeRatio_le hp3 hp7 hne) (cube_score_norm hp3) f g
  convert h using 1
  ring

end Sarkozy.PositiveRoots.CoherentFrame

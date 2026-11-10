module

public import Sarkozy.PositiveRoots.CoherentEndpointModel

/-!
# The common coherent parameter interval

The exact mass factorization proves `0 ≤ α(t) ≤ 1` on `[0, 12/5]`.
The leading matrix is the corresponding affine combination of its old and
endpoint matrices, as in `imp:local:coherent-parameter`.
-/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentParameters

open Finset Sarkozy.SpectralD

noncomputable def mass (t : ℝ) : ℝ := 1 + 1 / 100 + 13 / 75 * t ^ 2
noncomputable def strength (t : ℝ) : ℝ := 2 * t / mass t
noncomputable def alpha (t : ℝ) : ℝ := strength t / (12000 / 5021)

theorem mass_pos (t : ℝ) : 0 < mass t := by
  unfold mass
  nlinarith [sq_nonneg t]

theorem mass_endpoint : mass (12 / 5) = 5021 / 2500 := by norm_num [mass]

theorem strength_endpoint : strength (12 / 5) = 12000 / 5021 := by
  norm_num [strength, mass]

theorem mass_factorization (t : ℝ) :
    (12 / 5) * mass t - t * mass (12 / 5) =
      (12 / 5 - t) * (1 + 1 / 100 - 13 / 75 * t * (12 / 5)) := by
  unfold mass
  ring

theorem endpoint_gap : (1 : ℝ) + 1 / 100 - 13 / 75 * (12 / 5) ^ 2 = 29 / 2500 := by
  norm_num

theorem strength_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ strength t :=
  div_nonneg (mul_nonneg (by norm_num) ht) (mass_pos t).le

theorem strength_le_endpoint {t : ℝ} (ht : t ≤ 12 / 5) :
    strength t ≤ 12000 / 5021 := by
  have hg : 0 ≤ (1 : ℝ) + 1 / 100 - 13 / 75 * t * (12 / 5) := by linarith
  have h := mul_nonneg (sub_nonneg.mpr ht) hg
  rw [← mass_factorization, mass_endpoint] at h
  rw [strength, div_le_iff₀ (mass_pos t)]
  linarith

theorem alpha_bounds {t : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ 12 / 5) :
    0 ≤ alpha t ∧ alpha t ≤ 1 := by
  constructor
  · exact div_nonneg (strength_nonneg h0) (by norm_num)
  · exact (div_le_one (by norm_num : (0 : ℝ) < 12000 / 5021)).mpr
      (strength_le_endpoint h1)

theorem strength_eq_alpha (t : ℝ) : strength t = alpha t * (12000 / 5021) := by
  unfold alpha
  field_simp

noncomputable def old (c : CoherentEndpoint.Cut) (i j : Fin 64) : ℂ :=
  gaussian (CoherentEndpoint.starReal c i j) (CoherentEndpoint.starImag c i j)

noncomputable def leading (c : CoherentEndpoint.Cut) (t : ℝ) (i j : Fin 64) : ℂ :=
  old c i j + (strength t : ℂ) * (CoherentEndpoint.numerator c i j : ℂ) / 15

theorem interpolation (c : CoherentEndpoint.Cut) (t : ℝ) (i j : Fin 64) :
    leading c t i j = ((1 - alpha t : ℝ) : ℂ) * old c i j +
      (alpha t : ℂ) * CoherentEndpoint.fullLeading c i j := by
  unfold leading CoherentEndpoint.fullLeading
  rw [strength_eq_alpha]
  push_cast
  change _ = (1 - (alpha t : ℂ)) * old c i j +
    (alpha t : ℂ) * (old c i j + _)
  ring

theorem selected_values : mass (67 / 40) = 179557 / 120000 ∧
    strength (67 / 40) = 402000 / 179557 := by
  norm_num [mass, strength]

end Sarkozy.PositiveRoots.CoherentParameters

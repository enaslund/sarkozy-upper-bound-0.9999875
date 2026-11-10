module

public import Sarkozy.MiddleCertificates.Defs

/-!
# Kernel checks of the class-three grid tests of L10 and L21 (`cert:layer12-grid`)

* `models`: the generated tables `ς`, `𝐇` are those of the actual spectral data (B6's
  `recordData (Fin 1)` and `recordLayer`), through the Boolean edge test;
* `scalars`: the rational side conditions at every piece start (`10⁸ τ = linear`, `ε̄_V < 1`,
  `(c̄_⊥ + τ)/(1 - ε̄_V) ≤ g₃ ≤ allpG`);
* `residuals`: for every piece and each of the three Fourier coefficients, the residual
  `10¹² M - B^*B` of the scaled test matrix `M` of `eq:spectral-test` is Hermitian and diagonally
  dominant, so `M ⪰ 0` (`SpectralD.qform_nonneg_of_gaussian_factor`).

All by `decide +kernel`.
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open MidCut

theorem models_l10 : ModelChecks .l10 := by
  unfold ModelChecks
  decide +kernel

theorem models_l21 : ModelChecks .l21 := by
  unfold ModelChecks
  decide +kernel

theorem scalars_l10 : ∀ i, ScalarChecks .l10 i := by
  unfold ScalarChecks
  decide +kernel

theorem scalars_l21 : ∀ i, ScalarChecks .l21 i := by
  unfold ScalarChecks
  decide +kernel

theorem residuals_l10 : ∀ i, ResidualChecks .l10 i := by
  unfold ResidualChecks
  decide +kernel

theorem residuals_l21 : ∀ i, ResidualChecks .l21 i := by
  unfold ResidualChecks
  decide +kernel

theorem models (c : MidCut) : ModelChecks c := by
  cases c
  · exact models_l10
  · exact models_l21

theorem scalars (c : MidCut) (i : Fin 33) : ScalarChecks c i := by
  cases c
  · exact scalars_l10 i
  · exact scalars_l21 i

theorem residuals (c : MidCut) (i : Fin 33) : ResidualChecks c i := by
  cases c
  · exact residuals_l10 i
  · exact residuals_l21 i

end Sarkozy.MiddleCertificates

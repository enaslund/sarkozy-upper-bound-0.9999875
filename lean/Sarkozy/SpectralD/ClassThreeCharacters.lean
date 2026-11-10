module

public import Sarkozy.SpectralD.ClassOneCharacters

/-! The three imaginary Fourier coefficients at primes congruent to three modulo four. -/

@[expose] public section

namespace Sarkozy.SpectralD

open Sarkozy.SpectralC Sarkozy.Characters

variable {p : ℕ} [Fact p.Prime]

theorem chi_eps_three (hp3 : p % 4 = 3) (ξ : ZMod p) :
    ∃ e : Fin 3, chiC p ξ * epsG p = (((e.val : ℤ) - 1 : ℤ) : ℂ) * Complex.I := by
  by_cases hξ : ξ = 0
  · refine ⟨1, ?_⟩
    norm_num [hξ, chiC_zero]
  · rcases quadraticChar_dichotomy hξ with hc | hc <;>
      rcases (epsG_cases (p := p) (by omega)).2 hp3 with he | he
    · refine ⟨2, ?_⟩; norm_num [chiC_apply, hc, he]
    · refine ⟨0, ?_⟩; norm_num [chiC_apply, hc, he]
    · refine ⟨0, ?_⟩; norm_num [chiC_apply, hc, he]
    · refine ⟨2, ?_⟩; norm_num [chiC_apply, hc, he]

end Sarkozy.SpectralD

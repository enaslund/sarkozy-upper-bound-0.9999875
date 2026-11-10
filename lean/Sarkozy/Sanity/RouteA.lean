module

public import Sarkozy.Spectral.RouteA



@[expose] public section

namespace Sarkozy.Sanity

open Sarkozy.Spectral

/-- `RouteAInputs` holds for the identity on `ℝ` with `V = Sp = Sm = ⊥` and no modes. -/
theorem routeAInputs_inhabited :
    RouteAInputs (𝕜 := ℝ) (H := ℝ) LinearMap.id 1 ⊥ ⊥ ⊥ (Ξ := Empty) (n := Empty)
      (fun _ => False) (fun _ _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) 0 0 0 0 0 0 := by
  refine
    { symm := LinearMap.IsSymmetric.id
      norm_one := by simp
      V_perp_one := ?_
      sectors_ortho := Submodule.isOrtho_bot_left
      rho_mean := by simp
      rho_V := ?_
      rho_bound := by simp
      perp_bound := ?_
      degone_lower := ?_
      degone_upper := ?_
      degone_norm := ?_
      coupling := ?_ }
  · intro v hv
    rw [Submodule.mem_bot] at hv
    simp [hv]
  · intro v hv
    rw [Submodule.mem_bot] at hv
    simp [hv]
  · intro h h1 _
    have : h = 0 := by simpa using h1
    simp [this]
  · intro v hv
    rw [Submodule.mem_bot] at hv
    simp [hv]
  · intro v hv
    rw [Submodule.mem_bot] at hv
    simp [hv]
  · intro v hv
    rw [Submodule.mem_bot] at hv
    simp [hv, sqn]
  · intro v hv
    rw [Submodule.mem_bot] at hv
    refine ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp [hv], ?_, ?_, ?_, ?_⟩ <;>
      simp

end Sarkozy.Sanity

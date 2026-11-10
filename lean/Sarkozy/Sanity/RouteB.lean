module

public import Sarkozy.Spectral.RouteB



@[expose] public section

namespace Sarkozy.Sanity

open Sarkozy.Spectral

/-- The hypotheses of `routeB_cde` hold for the identity on `ℝ`, with zero perturbations. -/
theorem routeB_cde_satisfiable : |(1 : ℝ) - 1| ≤ 0 + 0 + 0 :=
  (routeB_cde (𝕜 := ℝ) (H := ℝ) LinearMap.id LinearMap.id 0 0 0 0 1 0 (by simp)
    (Z₀ := 1) (gr := 0) (εsoft := 0) (Mstar := 0) (zstar := 0) (Zstar := 0) (Nns := 0)
    (Dcol := 0) (fun x => by simp) (by simp) LinearMap.IsSymmetric.id
    (fun x => by simp) (fun f => by simp) (by simp) (by simp) (fun x => by simp)
    (fun x => by simp) (fun x => by simp) (by simp) (by simp) (by simp) (by norm_num)).1

end Sarkozy.Sanity

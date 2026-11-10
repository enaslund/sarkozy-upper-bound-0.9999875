module

public import Sarkozy.DensityMoments.DigitBijection
public import Sarkozy.DensityMoments.IidPrefix
public import Sarkozy.Interpolation.SquarePairEndpoints

/-!
# `lem:density:clique36` and `thm:density:iid-prefix`(b) without named inputs

`paper/sections/30_density_moment_upgrade.tex`. The only named input of `clique36` and of
`cliqueIidLaw_moment` was the interpolated centred bound of `lem:density:edge-moment`
(`SquarePairInterpolation`). Worker I1 proved it by bilinear Riesz–Thorin
(`Interpolation.square_pair_interp`, `Sarkozy/Interpolation/SquarePairEndpoints.lean`), so the
theorems here have no hypotheses beyond the range of the prime:

* `squarePairInterpolation_proved`: `SquarePairInterpolation p hp2 j` for every odd prime and
  every `j ≥ 1`;
* `clique36_proved`, `clique36_zmod_proved`: **`lem:density:clique36`** at every odd prime
  `2^16 ≤ p < 2^512`;
* `cliqueCopyLaw_moment_proved`, `cliqueIidLaw_moment_proved`,
  `tensor_cliqueIidLaw_moment_proved`: **`thm:density:iid-prefix`(b)**.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies

variable (p : ℕ) [hp : Fact p.Prime]

/-- The interpolated centred bound of `lem:density:edge-moment`, proved by I1. -/
theorem squarePairInterpolation_proved (hp2 : p ≠ 2) {j : ℕ} (hj : 1 ≤ j) :
    SquarePairInterpolation p hp2 j :=
  Interpolation.square_pair_interp hp2 (Or.inl rfl) hj

theorem bandInterpolation_proved (hp2 : p ≠ 2) :
    ∀ i : Fin 31, 2 ^ Certificates.clique36Band i ≤ p →
      p < 2 ^ (Certificates.clique36Band i + 16) →
      SquarePairInterpolation p hp2 (Certificates.clique36J i) :=
  fun i _ _ => squarePairInterpolation_proved p hp2 (le_trans (by norm_num) (two_le_clique36J i))

/-- **`lem:density:clique36`**, unconditional: at every odd prime `2^16 ≤ p < 2^512`, 36
conditionally independent uniform draws from the digit pair `{B, A}` have unit mixed
`L^{600/17}` norm (density endpoint `51/50`). -/
theorem clique36_proved (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512) :
    MixedLpBound (drawLaw (digitPairLaw p) (pairB p) (pairA p) (Fin 36)) (600 / 17) 1 :=
  clique36 hp2 h16 h512 (bandInterpolation_proved p hp2)

/-- **`lem:density:clique36` on `ℤ/p²ℤ`**, unconditional: the labels `A = a + p k`,
`B = b + p k'`. -/
theorem clique36_zmod_proved (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512) :
    MixedLpBound (drawLaw (digitPairLaw p) (fun ω => digitEquivOne p (pairB p ω))
      (fun ω => digitEquivOne p (pairA p ω)) (Fin 36)) (600 / 17) 1 :=
  clique36_zmod hp2 h16 h512 (bandInterpolation_proved p hp2)

variable (ℓ : ℕ)

/-- **`thm:density:iid-prefix`(b), copies**, unconditional: any filling of the 72 slots from
independent clique draws, each used at most twice, after the common square-affine map, has unit
mixed `L^{1200/17}`. -/
theorem cliqueCopyLaw_moment_proved (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512)
    {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T)
    (hσ : ∀ t, (univ.filter (fun v => σ v = t)).card ≤ 2) :
    MixedLpBound (cliqueCopyLaw p ℓ σ) (1200 / 17) 1 :=
  cliqueCopyLaw_moment p ℓ hp2 h16 h512 (bandInterpolation_proved p hp2) σ hσ

/-- **`thm:density:iid-prefix`(b), the reference**, unconditional: at every odd prime
`2^16 ≤ p < 2^512` and for every number `ℓ` of digit pairs, `cliqueIidLaw p ℓ` has unit mixed
`L^{1200/17}`. -/
theorem cliqueIidLaw_moment_proved (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512) :
    MixedLpBound (cliqueIidLaw p ℓ) (1200 / 17) 1 :=
  cliqueIidLaw_moment p ℓ hp2 h16 h512 (bandInterpolation_proved p hp2)

/-- **`thm:density:iid-prefix`(b), tensoring over prefix atoms**, unconditional. -/
theorem tensor_cliqueIidLaw_moment_proved {J : Type*} [Fintype J] [DecidableEq J] (P : J → ℕ)
    [∀ j, Fact (P j).Prime] (L : J → ℕ) (hp2 : ∀ j, P j ≠ 2) (h16 : ∀ j, 2 ^ 16 ≤ P j)
    (h512 : ∀ j, P j < 2 ^ 512) :
    MixedLpBound (FiniteLaw.tensor (fun j => cliqueIidLaw (P j) (L j))) (1200 / 17) 1 :=
  tensor_cliqueIidLaw_moment P L hp2 h16 h512 (fun j => bandInterpolation_proved (P j) (hp2 j))

end Sarkozy.DensityMoments

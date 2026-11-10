module

public import Sarkozy.Interpolation.SquarePairEndpoints
public import Sarkozy.DensityUpgrade.MiddleCatalog

/-!
# `lem:density:invariant-pair` and the middle catalog with the pair input proved

`paper/sections/30_density_moment_upgrade.tex`, `lem:density:invariant-pair`: "For `p ≥ 64`, any
probability law on ordered distinct pairs in `𝔽_p` which is invariant under simultaneous
square-affine maps has unit mixed `L^{3/2}` norm." Proof: the law is a mixture of the two class
laws (`InvariantPair.invariant_pair_mixedLpBound`); the gate at `j = 2` holds for `p ≥ 64`
(`InvariantPair.edge_gate_two`); apply `lem:density:edge-moment`.

* `class_three_halves`: both class laws have unit mixed `L^{3/2}` for `p ≥ 64`
  (`square_pair_moment_proved` at `j = 2`). These are the hypotheses `hsq`, `hnsq` of
  `InvariantPair.invariant_pair_mixedLpBound` and of the theorems of
  `DensityUpgrade.MiddleCatalog`;
* `invariant_pair_three_halves`: `lem:density:invariant-pair` as stated;
* `middleCatalog_component_proved`, `middleCatalog_root_proved`, `upperDiagonal_L70_proved`:
  WP-P's `lem:density:middle-catalog` / `lem:density:packets` theorems without `hsq`, `hnsq`,
  for `p ≥ 64`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Interpolation

open Sarkozy.InvariantPair Sarkozy.DensityUpgrade

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The class laws at `j = 2`**: for `p ≥ 64` the uniform strict square pair (`c = 1`) and
nonsquare pair (`c = −1`) have unit mixed `L^{3/2}` (`lem:density:edge-moment`,
`lem:density:invariant-pair`). -/
theorem class_three_halves (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) {c : ℤ} (hc : c = 1 ∨ c = -1) :
    MixedLpBound (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)) (3 / 2) 1 := by
  have hgate := edge_gate_two hp64
  have hgate' : ((2 : ℕ) : ℝ) ^ (2 + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (2 - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1 := by
    rw [one_div_pow]
    norm_num at hgate ⊢
    exact hgate
  have h := square_pair_moment_proved hp2 hc (j := 2) (by norm_num) hgate'
  have e : (1 : ℝ) + 1 / ((2 : ℕ) : ℝ) = 3 / 2 := by norm_num
  rwa [e] at h

/-- **`lem:density:invariant-pair`**: for `p ≥ 64`, every law on ordered distinct pairs of `𝔽_p`
invariant under the simultaneous square-affine maps has unit mixed `L^{3/2}`. -/
theorem invariant_pair_three_halves (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p)
    (μ : FiniteLaw (Fin 2 → ZMod p)) (hdist : ∀ z, z 0 = z 1 → μ.weight z = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ z,
      μ.weight (fun k => s * z k + u) = μ.weight z) :
    MixedLpBound μ (3 / 2) 1 :=
  invariant_pair_mixedLpBound hp2 μ hdist hinv (class_three_halves hp2 hp64 (Or.inl rfl))
    (class_three_halves hp2 hp64 (Or.inr rfl))

/-- `DensityUpgrade.middleCatalog_component` (`lem:density:middle-catalog`, a nonroot
component) for `p ≥ 64`, without the pair hypotheses `hsq`, `hnsq`. Only part of the lemma: the
configuration hypotheses `hdist`, `hinv`, `hz` remain. -/
theorem middleCatalog_component_proved (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) {Ω : Type*}
    [Fintype Ω] (μ : FiniteLaw Ω) (x y : Ω → ZMod p) (z : Fin 8 → Ω → ZMod p)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw μ x y).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw μ x y).weight (fun k => s * w k + u) = (pairLaw μ x y).weight w)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := Fin 2) x y z)) 11 1 :=
  middleCatalog_component hp2 μ x y z hdist hinv (class_three_halves hp2 hp64 (Or.inl rfl))
    (class_three_halves hp2 hp64 (Or.inr rfl)) hz

/-- `DensityUpgrade.middleCatalog_root` (`lem:density:middle-catalog`, the two-layer root) for
`p ≥ 64`, without the pair hypotheses `hsq`, `hnsq`. Only part of the lemma: the configuration
hypotheses `hdist`, `hinv`, `hz` remain. -/
theorem middleCatalog_root_proved (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (x y : Ω → ZMod p) (z : Fin 10 → Ω → ZMod p)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw μ x y).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw μ x y).weight (fun k => s * w k + u) = (pairLaw μ x y).weight w)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := Fin 1) x y z)) (23 / 2) 1 :=
  middleCatalog_root hp2 μ x y z hdist hinv (class_three_halves hp2 hp64 (Or.inl rfl))
    (class_three_halves hp2 hp64 (Or.inr rfl)) hz

/-- `DensityUpgrade.upperDiagonal_L70` (`lem:density:packets`, upper selected diagonals) for
`p ≥ 64`, without the pair hypotheses `hsq`, `hnsq`. Only part of the lemma: the configuration
hypotheses `hdist`, `hinv`, `hz` remain. -/
theorem upperDiagonal_L70_proved (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) {Ω : Type*} [Fintype Ω]
    (μ : FiniteLaw Ω) (x y : Ω → ZMod p) (z : Fin 64 → Ω → ZMod p)
    (hdist : ∀ w, w 0 = w 1 → (pairLaw μ x y).weight w = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ w,
      (pairLaw μ x y).weight (fun k => s * w k + u) = (pairLaw μ x y).weight w)
    (hz : ∀ k f, μ.expect (fun ω => f (z k ω)) = (FiniteLaw.uniform (ZMod p)).expect f) :
    MixedLpBound (μ.map (repeatedConfiguration (I := Fin 4) x y z)) 70 1 :=
  upperDiagonal_L70 hp2 μ x y z hdist hinv (class_three_halves hp2 hp64 (Or.inl rfl))
    (class_three_halves hp2 hp64 (Or.inr rfl)) hz

end Sarkozy.Interpolation

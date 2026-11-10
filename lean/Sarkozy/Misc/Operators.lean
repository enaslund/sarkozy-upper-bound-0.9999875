module

public import Sarkozy.ProbabilityConstructions
public import Sarkozy.Moments.Basic
public import Sarkozy.Comparison.Recentering
public import Sarkozy.Misc.TripleBlock

@[expose] public section

/-!
# Finite probability spaces and operator order (`def:prelim:operators`)

`paper/sections/04_notation.tex`, `def:prelim:operators`. The definition is notation; most of it
is already in the tree under other names. This file is the citation point: it says where each
notion lives, adds the few that had no Lean counterpart, and proves the two facts that make the
conventions agree.

Paper notion, then its Lean counterpart:

* finite probability space `(X, μ)`: `Sarkozy.FiniteLaw X` (`FiniteProbability.lean`;
  `weight ≥ 0`, `∑ weight = 1`);
* `E_μ f = ∑_x μ(x) f(x)`: `FiniteLaw.expect`;
* `‖f‖_{L^r(μ)} = (E_μ |f|^r)^{1/r}`: `FiniteLaw.lpNorm` (`Moments/Basic.lean`; defined for
  every real `r`, the paper uses `1 ≤ r < ∞`);
* `⟨f, g⟩_μ = E_μ f̄ g`: real case `Sarkozy.Recentering.ip`; complex case, uniform on `ZMod p`,
  `Sarkozy.SpectralC.ip`;
* `L²_0(μ)`, the mean-zero functions: `meanZero` below; the centring `Recentering.center`
  (`center_mem_meanZero`);
* unqualified averages are uniform: `FiniteLaw.uniform` (`ProbabilityConstructions.lean`);
* `ν` has density `h` with respect to `μ`, and its mass `ν(X)`: `HasDensity`, `mass` below
  (`mass_eq_expect`);
* `δ_x`: `pointMass` below (`expect_pointMass`);
* `T ⪰ 0` iff `⟨f, T f⟩ ≥ 0` for all `f`, and `S ⪯ T` iff `T - S ⪰ 0` (Loewner order):
  `LoewnerNonneg` below; for matrices `Matrix.PosSemidef` (`loewnerNonneg_uniform_iff`); at a
  reflection cut `ReflectionCut.Positive`, `ReflectionCut.Below` (`Reflection/CommonCut.lean`);
  on a real inner-product space mathlib's order on `E →L[ℝ] E` (`Envelopes/PurePair.lean`);
* `‖T‖ = sup_{‖f‖₂=1} ‖T f‖₂`: mathlib's operator norm, or the bound `‖T f‖₂ ≤ c ‖f‖₂` written
  out (e.g. `Mixing.markov_tensor_max`, `Misc.triple_block_norm`); for a symmetric matrix it
  follows from the two-sided Loewner bound `-c I ⪯ T ⪯ c I` (`Misc.mulVec_sq_le_of_two_sided`);
* numerical matrices with Euclidean norms and no probability normalization: `Matrix` with
  `dotProduct` (the counting inner product);
* Markov operator, which preserves `f ≥ 0` and `1`: `IsMarkovOp` below;
  `isMarkovOp_mulVec_iff` for matrices; `tripleMatrix_isMarkov`.

Two remarks on fidelity.

* **Loewner order and the law.** The paper's `T ⪰ 0` is relative to `⟨·,·⟩_μ`. For the uniform
  law this is the counting-measure form scaled by `1/|X|`, so it is `Matrix.PosSemidef` of a
  symmetric matrix (`loewnerNonneg_uniform_iff`). This is the convention of
  `Misc/TripleBlock.lean` and of `IndexSupport/Kronecker.lean`.
* **Self-adjointness.** The paper defines `T ⪰ 0` for self-adjoint `T` only; `LoewnerNonneg`
  is the quadratic-form condition alone, and `Matrix.PosSemidef` adds the symmetry.
-/

namespace Sarkozy.Misc

open Finset Matrix
open scoped BigOperators Matrix

variable {X : Type*} [Fintype X]

/-! ## Measures -/

/-- The point mass `δ_x` (`def:prelim:operators`). -/
noncomputable def pointMass [DecidableEq X] (x : X) : FiniteLaw X where
  weight y := if y = x then 1 else 0
  nonneg y := by split_ifs <;> norm_num
  total := by simp

theorem expect_pointMass [DecidableEq X] (x : X) (f : X → ℝ) : (pointMass x).expect f = f x := by
  simp [FiniteLaw.expect, pointMass]

/-- `ν` has density `h` with respect to `μ`: `ν(x) = h(x) μ(x)` at each point
(`def:prelim:operators`). Measures are weight functions. -/
def HasDensity (ν : X → ℝ) (μ : FiniteLaw X) (h : X → ℝ) : Prop := ∀ x, ν x = h x * μ.weight x

/-- The mass `ν(X)` of a measure. -/
noncomputable def mass (ν : X → ℝ) : ℝ := ∑ x, ν x

/-- A measure with density `h` has mass `E_μ h`. -/
theorem mass_eq_expect {ν : X → ℝ} {μ : FiniteLaw X} {h : X → ℝ} (hν : HasDensity ν μ h) :
    mass ν = μ.expect h := by
  simp only [mass, FiniteLaw.expect]
  exact sum_congr rfl fun x _ => by rw [hν x, mul_comm]

/-- `L²_0(μ)`: the mean-zero functions (`def:prelim:operators`). -/
def meanZero (μ : FiniteLaw X) : Submodule ℝ (X → ℝ) where
  carrier := {f | μ.expect f = 0}
  add_mem' {f g} hf hg := by
    simp only [Set.mem_ofPred_eq] at hf hg ⊢
    rw [show f + g = fun x => f x + g x from rfl, FiniteLaw.expect_add, hf, hg, add_zero]
  zero_mem' := by
    simp only [Set.mem_ofPred_eq]
    exact (FiniteLaw.expect_const _ 0)
  smul_mem' c f hf := by
    simp only [Set.mem_ofPred_eq] at hf ⊢
    rw [show c • f = fun x => c * f x from rfl, FiniteLaw.expect_const_mul, hf, mul_zero]

/-- The centring `f - E_μ f` lies in `L²_0(μ)`. -/
theorem center_mem_meanZero (μ : FiniteLaw X) (f : X → ℝ) :
    Recentering.center μ f ∈ meanZero μ := by
  change μ.expect (fun x => f x - μ.expect f) = 0
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]

/-! ## Operator order and Markov operators -/

/-- `T ⪰ 0` for the inner product of `μ`: `⟨f, T f⟩_μ ≥ 0` for every `f`
(`def:prelim:operators`, Loewner order; `S ⪯ T` is `LoewnerNonneg μ (T - S)`). -/
def LoewnerNonneg (μ : FiniteLaw X) (T : (X → ℝ) → (X → ℝ)) : Prop :=
  ∀ f, 0 ≤ Recentering.ip μ f (T f)

/-- For the uniform law, `⟨f, M f⟩ ≥ 0` for all `f` is the counting-measure condition, so for a
symmetric matrix it is `Matrix.PosSemidef`. -/
theorem loewnerNonneg_uniform_iff [Nonempty X] (M : Matrix X X ℝ) (hM : Mᵀ = M) :
    LoewnerNonneg (FiniteLaw.uniform X) (fun f => M *ᵥ f) ↔ M.PosSemidef := by
  have hc : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  have hform (f : X → ℝ) :
      Recentering.ip (FiniteLaw.uniform X) f (M *ᵥ f) = f ⬝ᵥ (M *ᵥ f) / Fintype.card X := by
    rw [Recentering.ip, FiniteLaw.expect_uniform]
    rfl
  rw [posSemidef_iff_dotProduct_mulVec]
  constructor
  · intro h
    refine ⟨isHermitian_of_transpose hM, fun f => ?_⟩
    have := h f
    rw [hform, div_nonneg_iff] at this
    simp only [star_trivial]
    rcases this with h1 | h1
    · exact h1.1
    · linarith [h1.2]
  · rintro ⟨-, h⟩ f
    rw [hform]
    exact div_nonneg (by simpa using h f) hc.le

/-- **A Markov operator** preserves nonnegative functions and the constant function `1`
(`def:prelim:operators`). -/
def IsMarkovOp (T : (X → ℝ) → (X → ℝ)) : Prop :=
  (∀ f, (∀ x, 0 ≤ f x) → ∀ x, 0 ≤ T f x) ∧ T (fun _ => 1) = fun _ => 1

/-- A matrix acts as a Markov operator iff its entries are nonnegative and its rows sum to one. -/
theorem isMarkovOp_mulVec_iff [DecidableEq X] (M : Matrix X X ℝ) :
    IsMarkovOp (fun f => M *ᵥ f) ↔ (∀ x y, 0 ≤ M x y) ∧ ∀ x, ∑ y, M x y = 1 := by
  constructor
  · rintro ⟨hpos, hone⟩
    refine ⟨fun x y => ?_, fun x => ?_⟩
    · have h := hpos (Pi.single y 1) (fun z => by
        by_cases hz : z = y
        · subst hz; simp
        · simp [hz]) x
      simpa [mulVec_single] using h
    · have h := congrFun hone x
      simpa [mulVec, dotProduct] using h
  · rintro ⟨hpos, hrow⟩
    refine ⟨fun f hf x => ?_, ?_⟩
    · exact sum_nonneg fun y _ => mul_nonneg (hpos x y) (hf y)
    · funext x
      simpa [mulVec, dotProduct] using hrow x

/-- The disjoint-triple operator of `sec:frontier:empty-triple-negative` is a Markov operator on
`L²(𝒯)` (`|F| ≥ 6`). -/
theorem tripleMatrix_isMarkov (F : Type*) [Fintype F] [DecidableEq F] (hn : 6 ≤ Fintype.card F) :
    IsMarkovOp (fun f => tripleMatrix F *ᵥ f) := by
  rw [isMarkovOp_mulVec_iff]
  refine ⟨fun x y => ?_, tripleMatrix_row hn⟩
  unfold tripleMatrix
  split_ifs
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact le_rfl

end Sarkozy.Misc

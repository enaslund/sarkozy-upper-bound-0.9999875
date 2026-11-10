module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real








@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Target

/-- The chosen representative of a point of `ℙ¹(𝔽_p) = 𝔽_p ∪ {∞}` (`subsec:dl:K`): the finite
point `u` (`some u`) is represented by the column vector `(u, 1)ᵀ`, and `∞` (`none`) by
`(1, 0)ᵀ`. -/
def projRep (p : ℕ) : Option (ZMod p) → ZMod p × ZMod p
  | some u => (u, 1)
  | none => (1, 0)

/-- `a ∧ b = a₀ b₁ - a₁ b₀` for column vectors `a = (a₀, a₁)ᵀ`, `b = (b₀, b₁)ᵀ`. -/
def wedge {p : ℕ} (a b : ZMod p × ZMod p) : ZMod p := a.1 * b.2 - a.2 * b.1

/-- `𝒳 = {(x₁, x₂) ∈ ℙ¹ × ℙ¹ : x₁ ≠ x₂}`, the ordered pairs of distinct points of `ℙ¹(𝔽_p)`. -/
def distinctPairs (p : ℕ) [Fact p.Prime] : Finset (Option (ZMod p) × Option (ZMod p)) :=
  univ.filter (fun x => x.1 ≠ x.2)

/-- The four-cycle matrix of `eq:dl:M`: `M(x, z) = χ(∏_{i, j ∈ {1, 2}} (z_i ∧ x_j))`, with the
representatives of `projRep`. For finite points `z_i ∧ x_j = z_i - x_j`. -/
def fourCycleMatrix (p : ℕ) [Fact p.Prime] (x z : Option (ZMod p) × Option (ZMod p)) : ℤ :=
  quadraticChar (ZMod p)
    (wedge (projRep p z.1) (projRep p x.1) * wedge (projRep p z.1) (projRep p x.2) *
      (wedge (projRep p z.2) (projRep p x.1) * wedge (projRep p z.2) (projRep p x.2)))

/-- **H6, the four-cycle operator norm** (`thm:dl:K`, assumed together with the `GL₂(𝔽_p)`
character table behind its proof): for every odd prime `p`, every eigenvalue of the real symmetric
`p(p + 1) × p(p + 1)` matrix `M` (`fourCycleMatrix`, indexed by `𝒳 = distinctPairs p`) lies in
`[-2p, 2p]`. Stated as the equivalent quadratic-form bound: for every real vector `v` on `𝒳`,
`|∑_{x, z ∈ 𝒳} v(x) M(x, z) v(z)| ≤ 2p ∑_{x ∈ 𝒳} v(x)²`. -/
def FourCycle : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∀ v : Option (ZMod p) × Option (ZMod p) → ℝ,
    |∑ x ∈ distinctPairs p, ∑ z ∈ distinctPairs p, v x * (fourCycleMatrix p x z : ℝ) * v z| ≤
      2 * (p : ℝ) * ∑ x ∈ distinctPairs p, v x ^ 2

end Sarkozy.Target

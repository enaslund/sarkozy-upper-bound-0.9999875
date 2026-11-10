module

public import Sarkozy.TraceMixing.SeventyTwoPair

/-!
# The mixing hypothesis (R4) for graph laws

`paper/sections/06_lifts_sectors.tex`, `it:record:R4`, for the graph laws `λ_p(G)` of
`paper/sections/12_labellings.tex`, as a consequence of `lem:trace-mixing`(d): assuming Weil's
bound (`Sarkozy.Target.Weil`), for every prime `p ≥ 2^512` and every oriented graph with `72`
vertices and degrees at most `20`, with `γ = 255/1024`,

* `λ_p(G)` is `(γ, v)`-mixing at every slot `v`;
* for every edge `(u, v)`, the `(u, v)`-marginal is `Unif(Ω)` and `λ_p(G)` is
  `(γ, (u, v))`-mixing.

(R4) itself is stated for the tail laws `μ_p` and the accepted parts `ν̄_p` of the record, which
are mixtures of graph laws; `Sarkozy.Mixing.IsMixing.mixture` (`lem:mixture`) transfers the
bounds to mixtures with a common marginal. The tail primes of (R4) satisfy `p ≥ P₅ = 2^{65536}`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

/-- **(R4) for graph laws.** -/
theorem graphLaw_R4 (hWeil : Target.Weil) {p : ℕ} [Fact p.Prime] (hp : (2 : ℝ) ^ 512 ≤ p)
    {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hne : (injLabellings (ZMod p) G).Nonempty) :
    (∀ v, IsGammaMixing p (255 / 1024) (graphLaw G hne) {v}) ∧
      ∀ u v, (u, v) ∈ G.E →
        (∀ x x' : ZMod p, srcWeight (pairJoint (graphLaw G hne) u v) (x, x') =
          if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0) ∧
        IsGammaMixing p (255 / 1024) (graphLaw G hne) {u, v} := by
  have h2512 : (2 : ℝ) < 2 ^ 512 := lt_self_pow₀ (by norm_num) (by norm_num)
  have hp2R : (2 : ℝ) < p := lt_of_lt_of_le h2512 hp
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp2R
    push_cast at hp2R
    exact lt_irrefl _ hp2R
  refine ⟨fun v => isGammaMixing_graphLaw_slot hWeil p hp G hn hdeg hne v,
    fun u v huv => ⟨fun x x' => srcWeight_pairJoint G hne hp2 huv x x',
      isGammaMixing_graphLaw_pair hWeil hp G hn hdeg hne huv⟩⟩

end Sarkozy.TraceMixing

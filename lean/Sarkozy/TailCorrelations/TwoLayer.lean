module

public import Sarkozy.TailCorrelations.Layer
public import Sarkozy.Influence.Bridge
public import Sarkozy.F7Repair.TwoLayer
public import Sarkozy.F7Repair.Support

@[expose] public section

/-!
# The layer correlation of a two-layer graph law, in the two forms (F7) reads

`25_upper_reference.tex`, `it:record:upper-F2`, applied "between its two layers" as in (F7)
(`26_upper_comparison.tex`): for a graph `G` on the two layers `O₀ × O₁ × {0, 1}` (at most `72`
vertices) and an odd prime `p ≥ 2⁵¹²` with Weil's bound,

* **`layer_maxCorr_le`**: `ρ(y_X; y_Y) ≤ 2⁸¹ p^{-1/2}` under `λ_p(G)`, for the two layers
  `X = O₀ × O₁ × {0}`, `Y = O₀ × O₁ × {1}` (from `graphLaw_maxCorr_le`; the two graph-law
  conventions agree by `Influence.graphLaw_ofLabellings`);
* **`centredBound_of_corrLe`**: the bound as F7Repair's `CentredBound` of the pair law of the two
  halves, relative to its own marginals (the form of `ρ_new` in (F7));
* **`oldCorr_of_corrLe`**: the bound relative to the layer-`0` marginal `μ^old` on both halves,
  when the two layers have one law (the form of `ρ_old` in (F7)).
-/

open scoped BigOperators

namespace Sarkozy.TailCorrelations

open Sarkozy Sarkozy.Peyre Sarkozy.Influence Sarkozy.Recentering Sarkozy.F7Repair
  Sarkozy.UpperComparison

section Layers

variable {O₀ O₁ : Type*} [Fintype O₀] [Fintype O₁]

/-- The vertices of layer `k`. -/
def layerSet (k : Fin 2) : Finset (O₀ × O₁ × Fin 2) := Finset.univ.filter (fun v => v.2.2 = k)

theorem layerSet_disjoint :
    Disjoint (layerSet (O₀ := O₀) (O₁ := O₁) 0) (layerSet 1) := by
  unfold layerSet
  rw [Finset.disjoint_filter]
  intro v _ h0 h1
  rw [h0] at h1
  exact absurd h1 (by decide)

/-- The half `layerOf y k` and the restriction of `y` to `layerSet k` have the same level sets. -/
theorem layer_level {Z : Type*} (k : Fin 2) (ω ω' : O₀ × O₁ × Fin 2 → Z) :
    layerOf ω k = layerOf ω' k ↔
      (fun v : layerSet (O₀ := O₀) (O₁ := O₁) k => ω v) =
        (fun v : layerSet (O₀ := O₀) (O₁ := O₁) k => ω' v) := by
  constructor
  · intro h
    funext v
    obtain ⟨⟨a, b, c⟩, hv⟩ := v
    have hc : c = k := (Finset.mem_filter.mp hv).2
    subst hc
    exact congrFun h (a, b)
  · intro h
    funext o
    exact congrFun h ⟨(o.1, o.2, k), by simp [layerSet]⟩

/-- **(F2) between the two layers of a two-layer graph at a large prime**:
`ρ(y_X; y_Y) ≤ 2⁸¹ p^{-1/2}` under `λ_p(G)` (`it:record:upper-F2`, `cor:influence-schur`). -/
theorem layer_maxCorr_le [DecidableEq O₀] [DecidableEq O₁] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : Labellings.WeilBound (ZMod p)) (hp : (2 : ℝ) ^ 512 ≤ p)
    (G : Labellings.OrientedGraph (O₀ × O₁ × Fin 2)) (hU : Fintype.card (O₀ × O₁ × Fin 2) ≤ 72)
    (hInj : (Labellings.injLabellings (ZMod p) G).Nonempty) :
    maxCorr (Labellings.graphLaw G hInj) (fun y => layerOf y 0) (fun y => layerOf y 1) ≤
      2 ^ 81 * rp p := by
  have h : (Influence.injLabellings (ofLabellings G) p).Nonempty := by
    rw [injLabellings_ofLabellings]; exact hInj
  rw [← graphLaw_ofLabellings G h hInj,
    maxCorr_congr _ (fun ω ω' => layer_level 0 ω ω') (fun ω ω' => layer_level 1 ω ω')]
  exact graphLaw_maxCorr_le hp2 hW hp (ofLabellings G) hU h _ _ layerSet_disjoint

end Layers

section Forms

variable {Ω X Y : Type*} [Fintype Ω] [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem margX_pairLaw_expect (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) (φ : X → ℝ) :
    (margX (pairLaw lam a b)).expect φ = lam.expect (fun ω => φ (a ω)) := by
  rw [← expect_fst, pairLaw_expect]

theorem margY_pairLaw_expect (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) (ψ : Y → ℝ) :
    (margY (pairLaw lam a b)).expect ψ = lam.expect (fun ω => ψ (b ω)) := by
  rw [← expect_snd, pairLaw_expect]

/-- **The `CentredBound` form**: a maximal-correlation bound between `a` and `b` under `lam` is the
centred correlation bound of their pair law relative to its own marginals. -/
theorem centredBound_of_corrLe (lam : FiniteLaw Ω) (a : Ω → X) (b : Ω → Y) {ρ : ℝ}
    (h : CorrLe lam a b ρ) :
    CentredBound (pairLaw lam a b) (margX (pairLaw lam a b)) (margY (pairLaw lam a b)) ρ := by
  intro f g hf hg
  rw [margX_pairLaw_expect] at hf
  rw [margY_pairLaw_expect] at hg
  have h1 := h f g hf hg
  rw [pairLaw_expect]
  unfold nrm ip
  rw [margX_pairLaw_expect, margY_pairLaw_expect]
  simpa only [sq] using h1

end Forms

section Old

variable {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Z] [DecidableEq Z]

/-- **The `ρ_old` form**: if the two layers of `lamO` have one law, a maximal-correlation bound
between them is the centred bound relative to `μ^old` on both halves. -/
theorem oldCorr_of_corrLe (lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) {ρ : ℝ}
    (hsym : ∀ φ : (O₀ × O₁ → Z) → ℝ,
      lamO.expect (fun y => φ (lay1 y)) = lamO.expect (fun y => φ (lay0 y)))
    (h : CorrLe lamO lay0 lay1 ρ) :
    ∀ hh kk, (oldHalf lamO).expect hh = 0 → (oldHalf lamO).expect kk = 0 →
      |lamO.expect (fun y => hh (lay0 y) * kk (lay1 y))| ≤
        ρ * nrm (oldHalf lamO) hh * nrm (oldHalf lamO) kk := by
  intro hh kk h0 k0
  rw [oldHalf_expect] at h0 k0
  have k1 : lamO.expect (fun y => kk (lay1 y)) = 0 := by rw [hsym]; exact k0
  have h1 := h hh kk h0 k1
  unfold nrm ip
  rw [oldHalf_expect, oldHalf_expect, ← hsym (fun x => kk x * kk x)]
  simpa only [sq] using h1

end Old

end Sarkozy.TailCorrelations

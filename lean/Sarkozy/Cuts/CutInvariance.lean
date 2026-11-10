module

public import Sarkozy.Cuts.CutKernel
public import Sarkozy.Cuts.Swapped

/-!
# Cuts, IX′: invariance of the cut laws (`lem:spec:cutkernel` (d))

`13_cuts_correlations.tex`, `lem:spec:cutkernel` (d), for a finite field `F` (the paper:
`F = 𝔽_p`).

* `affine_mem_inj`, `graphLaw_affine`: every graph law `λ(G)` is invariant under the diagonal
  maps `z ↦ (a z_u + c)_u` with `a ∈ Q` (`χ(a) = 1`) and `c ∈ F`. This applies to `λ = λ(G)` and to
  the half law `μ = λ(G⁺)`.
* `halfMarginal_affine`: the actual half marginal `m_p` (the law of `x` under `λ`) is invariant
  too.
* `graphLaw_vertex_uniform`: every one-vertex marginal of a graph law is uniform. This covers
  `λ`, `μ`, and `m_p` (whose one-vertex marginals are those of `λ` at vertices of `U⁺`).
* `expect_halves_swap`: `λ` is invariant under `(x, x') ↦ (x', x)`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Affine

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- The diagonal map `z ↦ (a z_u + c)_u`. -/
def affineMap (a c : F) (y : W → F) : W → F := fun u => a * y u + c

/-- Square-affine maps preserve `Inj(G)`. -/
theorem affine_mem_inj (G : OrientedGraph W) {a : F} (ha : quadraticChar F a = 1) (c : F)
    (y : W → F) : affineMap a c y ∈ injLabellings F G ↔ y ∈ injLabellings F G := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at ha
    exact zero_ne_one ha
  rw [SpecData.mem_inj, SpecData.mem_inj]
  have hdiff : ∀ u w, affineMap a c y w - affineMap a c y u = a * (y w - y u) := fun u w => by
    unfold affineMap
    ring
  have hchar : ∀ u w, quadraticChar F (affineMap a c y w - affineMap a c y u) =
      quadraticChar F (y w - y u) := fun u w => by
    rw [hdiff, map_mul, ha, one_mul]
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun u hu w hw h => hinj u hu w hw ?_, fun e he h1 h2 => ?_⟩
    · unfold affineMap
      rw [h]
    · rw [← hchar]
      exact hedge e he h1 h2
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun u hu w hw h => hinj u hu w hw ?_, fun e he h1 h2 => ?_⟩
    · unfold affineMap at h
      have := add_right_cancel h
      exact mul_left_cancel₀ ha0 this
    · rw [hchar]
      exact hedge e he h1 h2

/-- **`lem:spec:cutkernel` (d).** A graph law is invariant under `z ↦ (a z_u + c)_u`,
`a ∈ Q`, `c ∈ F`. -/
theorem graphLaw_affine (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) {a : F}
    (ha : quadraticChar F a = 1) (c : F) (Φ : (W → F) → ℝ) :
    (graphLaw G hne).expect (fun y => Φ (affineMap a c y)) = (graphLaw G hne).expect Φ := by
  have ha0 : a ≠ 0 := by
    intro h
    rw [h, quadraticChar_zero] at ha
    exact zero_ne_one ha
  rw [SpecData.graphLaw_expect', SpecData.graphLaw_expect']
  congr 1
  refine Finset.sum_nbij' (affineMap a c) (fun y u => a⁻¹ * (y u - c)) ?_ ?_ ?_ ?_ ?_
  · intro y hy
    exact (affine_mem_inj G ha c y).2 hy
  · intro y hy
    rw [← affine_mem_inj G ha c]
    have : affineMap a c (fun u => a⁻¹ * (y u - c)) = y := by
      funext u
      unfold affineMap
      field_simp
      ring
    rw [this]
    exact hy
  · intro y _
    funext u
    unfold affineMap
    field_simp
    ring
  · intro y _
    funext u
    unfold affineMap
    field_simp
    ring
  · intro y _
    rfl

/-- **`lem:spec:cutkernel` (d).** Every one-vertex marginal of a graph law is uniform. -/
theorem graphLaw_vertex_uniform [Nonempty F] (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) (v : W) (φ : F → ℝ) :
    (graphLaw G hne).expect (fun y => φ (y v)) = (FiniteLaw.uniform F).expect φ := by
  have htrans : ∀ c : F, (graphLaw G hne).expect (fun y => φ (y v)) =
      (graphLaw G hne).expect (fun y => φ (y v + c)) := by
    intro c
    have h := graphLaw_affine G hne (a := 1) (MulChar.map_one (quadraticChar F)) c
      (fun y => φ (y v))
    simp only [affineMap, one_mul] at h
    exact h.symm
  have havg : (graphLaw G hne).expect (fun y => φ (y v)) =
      (graphLaw G hne).expect (fun y => (∑ c : F, φ (y v + c)) / Fintype.card F) := by
    rw [Sarkozy.Peyre.expect_div_const, Sarkozy.Peyre.expect_sum, ← Finset.sum_congr rfl
      (fun c _ => htrans c), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    have hF : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    field_simp
  rw [havg, FiniteLaw.expect_uniform]
  have hshift : ∀ y : W → F, ∑ c : F, φ (y v + c) = ∑ b : F, φ b := fun y =>
    Fintype.sum_equiv (Equiv.addLeft (y v)) _ _ (fun c => rfl)
  simp only [hshift]
  exact FiniteLaw.expect_const _ _

end Affine

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

omit [Fintype F] [DecidableEq F] in
theorem halfL_affine (a c : F) (y : U → F) :
    D.halfL (affineMap a c y) = affineMap a c (D.halfL y) := rfl

/-- **`lem:spec:cutkernel` (d).** The actual half marginal `m_p` is square-affine invariant. -/
theorem halfMarginal_affine (hne : (injLabellings F D.G).Nonempty) {a : F}
    (ha : quadraticChar F a = 1) (c : F) (Fn : (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => Fn (affineMap a c (D.halfL y))) =
      (graphLaw D.G hne).expect (fun y => Fn (D.halfL y)) := by
  have h := graphLaw_affine D.G hne ha c (fun y => Fn (D.halfL y))
  simp only [halfL_affine] at h
  exact h

/-- **`lem:spec:cutkernel` (d).** `λ` is invariant under `(x, x') ↦ (x', x)`. -/
theorem expect_halves_swap (hne : (injLabellings F D.G).Nonempty)
    (Φ : (D.cut.Half → F) → (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => Φ (D.halfR y) (D.halfL y)) =
      (graphLaw D.G hne).expect (fun y => Φ (D.halfL y) (D.halfR y)) := by
  rw [D.expect_halves hne (fun x x' => Φ x' x), D.expect_halves hne Φ]
  congr 1
  rw [FiniteLaw.expect_product, FiniteLaw.expect_product, expect_comm]
  refine (D.halfLaw hne).expect_congr (fun x => (D.halfLaw hne).expect_congr (fun x' => ?_))
  rw [D.cutK_symm]

end SpecData

end Sarkozy.Cuts

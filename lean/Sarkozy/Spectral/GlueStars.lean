module

public import Sarkozy.SecondOrder.StarMean
public import Sarkozy.SecondOrder.GraphPinned
public import Sarkozy.InfluenceGlue.L2
public import Sarkozy.Spectral.Centring






@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.Spectral

open Sarkozy Sarkozy.InfluenceGlue

variable {p : ℕ} [Fact p.Prime] {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

/-- A pinned half law, as a finite law. -/
noncomputable def pinnedLaw (L : SecondOrder.PinnedHalfLaw p U) : FiniteLaw (U → ZMod p) where
  weight := L.μ
  nonneg := L.μ_nonneg
  total := L.μ_sum

/-- `M_⋆` of `lem:star-mean`, the square root of the ordered-star bound. -/
noncomputable def starMstar [LinearOrder U] (L : SecondOrder.PinnedHalfLaw p U)
    (N : K → Finset U) (c : K → Finset U → ℝ) : ℝ :=
  Real.sqrt ((1 / Real.sqrt p) ^ 2 *
    (∑ i, SecondOrder.pivotD2 L SecondOrder.supports3 (SecondOrder.starCoeff N c) i +
      2 * (1 / Real.sqrt p) * ∑ i, SecondOrder.pivotK L SecondOrder.supports3
        (SecondOrder.starCoeff N c) i * ∑ j ∈ univ.filter (· < i),
          Real.sqrt (SecondOrder.pivotD2 L SecondOrder.supports3 (SecondOrder.starCoeff N c) j)))

/-- `z_⋆` of `lem:star-mean`. -/
noncomputable def starZstar [LinearOrder U] (L : SecondOrder.PinnedHalfLaw p U)
    (N : K → Finset U) (c : K → Finset U → ℝ) : ℝ :=
  (1 / Real.sqrt p) ^ 2 *
    (∑ i, SecondOrder.pivotK L SecondOrder.supports3 (SecondOrder.starCoeff N c) i +
      |SecondOrder.starBEven N c|)

/-- **The star inputs from `lem:star-mean`**, in the `L²(μ)` realization `l2Map`. -/
theorem glue_star_inputs [LinearOrder U] (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp2 : p ≠ 2) (L : SecondOrder.PinnedHalfLaw p U) (N : K → Finset U)
    (c : K → Finset U → ℝ) :
    ‖l2Map (pinnedLaw L) (fun _ => 1)‖ = 1 ∧
    ⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ =
      ∑ x, L.μ x * starFunction N c x ∧
    ‖l2Map (pinnedLaw L) (starFunction N c) -
        ⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ •
          l2Map (pinnedLaw L) (fun _ => 1)‖ ≤ starMstar L N c ∧
    ‖⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ‖ ≤
      starZstar L N c ∧
    2 * ‖⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ‖ ≤
      2 * starZstar L N c := by
  set μ := pinnedLaw L with hμ
  set h : (U → ZMod p) → ℝ := starFunction N c with hh
  obtain ⟨hvar, hmean⟩ := SecondOrder.star_mean hW hMR hp2 L N c
  have hone : ‖l2Map μ (fun _ => 1)‖ = 1 := by
    have h1 := norm_l2Map_sq μ (fun _ => (1 : ℝ))
    simp only [one_pow, FiniteLaw.expect_const] at h1
    have h0 := norm_nonneg (l2Map μ (fun _ => (1 : ℝ)))
    nlinarith [h1, h0]
  have hin : ⟪l2Map μ (fun _ => 1), l2Map μ h⟫_ℝ = ∑ x, L.μ x * h x := by
    rw [inner_l2Map]
    simp only [one_mul, FiniteLaw.expect]
    rfl
  set m := ∑ x, L.μ x * h x with hm
  have hdiff : l2Map μ h - m • l2Map μ (fun _ => 1) = l2Map μ (fun x => h x - m) := by
    rw [← map_smul, ← map_sub]
    congr 1
    funext x
    simp
  have hsq : ‖l2Map μ (fun x => h x - m)‖ ^ 2 = ∑ x, L.μ x * (h x - m) ^ 2 := by
    rw [norm_l2Map_sq]
    rfl
  have hM : ‖l2Map μ h - m • l2Map μ (fun _ => 1)‖ ≤ starMstar L N c := by
    rw [hdiff, starMstar]
    refine Real.le_sqrt_of_sq_le ?_
    rw [hsq]
    exact hvar
  have hz : ‖m‖ ≤ starZstar L N c := by
    rw [Real.norm_eq_abs, starZstar]
    exact hmean
  refine ⟨hone, hin, ?_, ?_, ?_⟩
  · rw [hin]
    exact hM
  · rw [hin]
    exact hz
  · rw [hin]
    linarith

/-- **The star inputs for the graph law `λ_p(G⁺)`** (`SecondOrder.graphPinned`). -/
theorem glue_star_inputs_graph [LinearOrder U] (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp2 : p ≠ 2) (G : Labellings.OrientedGraph U)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    (he : ∀ i, SecondOrder.graphCountError (p := p) G i < 1) (N : K → Finset U)
    (c : K → Finset U → ℝ) :
    let L := SecondOrder.graphPinned (Labellings.weilBound_of_target hW p hp2) G hne he
    (pinnedLaw L).weight = (Labellings.graphLaw G hne).weight ∧
    ‖l2Map (pinnedLaw L) (starFunction N c) -
        ⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ •
          l2Map (pinnedLaw L) (fun _ => 1)‖ ≤ starMstar L N c ∧
    ‖⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ‖ ≤
      starZstar L N c := by
  intro L
  obtain ⟨-, -, h3, h4, -⟩ := glue_star_inputs hW hMR hp2 L N c
  exact ⟨rfl, h3, h4⟩

end Sarkozy.Spectral

module

public import Sarkozy.Labellings.GraphAutomorphism
public import Sarkozy.Labellings.TargetBridge
public import Sarkozy.ProbabilityProducts
public import Sarkozy.Energy

@[expose] public section

/-!
# Block graph laws `λ_𝔅(G) = ⊗_{p ∈ 𝔅} λ_p(G)`

`def:graphs:labeling`, `subsec:push:layer12spectral`.

On a block `𝔅` of primes the label alphabet is `X_𝔅 = ∏_{p ∈ 𝔅} 𝔽_p` (`BlockLabel pr`, the primes
indexed by a finite type `ι`, `pr : ι → ℕ`), and for an oriented graph `G` the block law is the
product over the primes of the uniform laws on the injective strict-square labellings
(`blockGraphLaw`, through `FiniteLaw.tensor`).

Proved here:
* square-affine invariance of one graph law: `z ↦ αz + β` with `χ(α) = 1` preserves
  `Inj_p(G)` (`feasible_affine_iff`) and the graph law (`graphLaw_expect_affine`); hence every
  vertex marginal of `λ_p(G)` is uniform (`graphLaw_vertex_uniform`, the argument of
  `lem:marginals`: translations act transitively);
* the expectation of a tensor as an explicit sum (`expect_tensor_eq_sum`), and invariance of a
  tensor under factorwise bijections that preserve each factor (`expect_tensor_comp`);
* for the block law: invariance under the square-affine maps acting independently at each prime
  ((R3) of `hyp:record:reference`, `blockGraphLaw_expect_affine`), under graph automorphisms
  (`blockGraphLaw_expect_auto`), and uniform vertex marginals on `X_𝔅`
  (`blockGraphLaw_vertex_uniform`);
* **non-vacuity**: under Weil's bound (H1, `Target.Weil`) every finite oriented graph has
  injective strict-square labellings at every prime `p ≥ p₀(G)` (`exists_injLabellings_nonempty`),
  so the block laws of `Part V` are defined on blocks of large primes.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## Square-affine invariance of one graph law -/

section Field

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem ne_zero_of_quadraticChar_eq_one {α : F} (hα : quadraticChar F α = 1) : α ≠ 0 := by
  intro h
  rw [h, quadraticChar_zero] at hα
  exact zero_ne_one hα

omit [DecidableEq W] in
/-- **Square-affine maps preserve feasibility**: for `χ(α) = 1`, the labelling
`w ↦ α z_w + β` is an injective strict-square labelling of `G` iff `z` is. -/
theorem feasible_affine_iff (G : OrientedGraph W) {α : F} (hα : quadraticChar F α = 1) (β : F)
    (z : W → F) : Feasible F G univ (fun w => α * z w + β) ↔ Feasible F G univ z := by
  have hα0 := ne_zero_of_quadraticChar_eq_one hα
  have hdiff : ∀ a b : W, (α * z b + β) - (α * z a + β) = α * (z b - z a) := fun a b => by ring
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a ha b hb hab => hinj a ha b hb (by simp only [hab]), fun e he h1 h2 => ?_⟩
    have := hedge e he h1 h2
    rw [hdiff, map_mul, hα, one_mul] at this
    exact this
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a ha b hb hab => hinj a ha b hb ?_, fun e he h1 h2 => ?_⟩
    · have h' : α * z a = α * z b := add_right_cancel hab
      exact mul_left_cancel₀ hα0 h'
    · change quadraticChar F ((α * z e.2 + β) - (α * z e.1 + β)) = 1
      rw [hdiff, map_mul, hα, one_mul]
      exact hedge e he h1 h2

/-- The affine bijection `x ↦ αx + β` of `F` (`α ≠ 0`). -/
noncomputable def affineMap (α : F) (hα : α ≠ 0) (β : F) : F ≃ F :=
  (Equiv.mulLeft₀ α hα).trans (Equiv.addRight β)

omit [Fintype F] [DecidableEq F] in
theorem affineMap_apply (α : F) (hα : α ≠ 0) (β x : F) : affineMap α hα β x = α * x + β := rfl

/-- **The graph law is invariant under the square-affine maps** `z ↦ αz + β`, `χ(α) = 1`. -/
theorem graphLaw_expect_affine (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    {α : F} (hα : quadraticChar F α = 1) (β : F) (f : (W → F) → ℝ) :
    (graphLaw G hne).expect (fun z => f (fun w => α * z w + β)) = (graphLaw G hne).expect f := by
  have hα0 := ne_zero_of_quadraticChar_eq_one hα
  let T : (W → F) ≃ (W → F) := Equiv.piCongrRight fun _ => affineMap α hα0 β
  have hw : ∀ z : W → F, (graphLaw G hne).weight (T z) = (graphLaw G hne).weight z := by
    intro z
    have hmem : T z ∈ injLabellings F G ↔ z ∈ injLabellings F G := by
      rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
      exact feasible_affine_iff G hα β z
    simp only [graphLaw, hmem]
  unfold FiniteLaw.expect
  calc ∑ z, (graphLaw G hne).weight z * f (fun w => α * z w + β)
      = ∑ z, (graphLaw G hne).weight (T z) * f (T z) :=
        sum_congr rfl fun z _ => by rw [hw z]; rfl
    _ = ∑ y, (graphLaw G hne).weight y * f y :=
        Fintype.sum_equiv T _ _ fun _ => rfl

/-- **Every vertex marginal of a graph law is uniform** (translations act transitively;
`lem:marginals`). -/
theorem graphLaw_vertex_uniform (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    (w : W) (f : F → ℝ) :
    (graphLaw G hne).expect (fun z => f (z w)) = (FiniteLaw.uniform F).expect f := by
  have htr : ∀ c : F, (graphLaw G hne).expect (fun z => f (z w + c)) =
      (graphLaw G hne).expect (fun z => f (z w)) := by
    intro c
    have h := graphLaw_expect_affine G hne (α := 1) (by simp) c (fun z => f (z w))
    simpa only [one_mul] using h
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ c : F, (graphLaw G hne).expect (fun z => f (z w + c)) =
      (graphLaw G hne).expect (fun _ => ∑ y : F, f y) := by
    unfold FiniteLaw.expect
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [← mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.addLeft (z w)) _ _ fun _ => rfl
  rw [sum_congr rfl fun c _ => htr c, sum_const, card_univ, nsmul_eq_mul,
    FiniteLaw.expect_const] at hsum
  rw [FiniteLaw.expect_uniform]
  field_simp
  linarith [hsum]

end Field

/-! ## Tensors as explicit sums, and their invariance -/

section Tensor

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ j, Fintype (X j)] [∀ j, DecidableEq (X j)]

theorem lawDensity_signedIntegral' {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (w : Ω → ℝ)
    (x : Ω) : lawDensity (signedIntegral w) x = w x := by
  unfold lawDensity
  change (∑ y, w y * if y = x then (1 : ℝ) else 0) = w x
  simp

/-- The expectation under a tensor of slot laws, as an explicit sum over the factor labellings. -/
theorem expect_tensor_eq_sum (μ : ∀ j, FiniteLaw (V → X j)) (H : (V → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ).expect H =
      ∑ z : ∀ j, V → X j, (∏ j, (μ j).weight (z j)) * H (fun v j => z j v) := by
  unfold FiniteLaw.tensor
  rw [FiniteLaw.expect_ofFunctional]
  change (∑ z : ∀ j, V → X j, (∏ j, lawDensity (signedIntegral (μ j).weight) (z j)) *
    H (fun v j => z j v)) = _
  simp only [lawDensity_signedIntegral']

/-- **A tensor is invariant under factorwise bijections that preserve each factor.** -/
theorem expect_tensor_comp (μ : ∀ j, FiniteLaw (V → X j)) (T : ∀ j, (V → X j) ≃ (V → X j))
    (hT : ∀ j y, (μ j).weight (T j y) = (μ j).weight y) (H : (V → ∀ j, X j) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun z => H (fun v j => T j (fun v' => z v' j) v)) =
      (FiniteLaw.tensor μ).expect H := by
  rw [expect_tensor_eq_sum, expect_tensor_eq_sum]
  let E : (∀ j, V → X j) ≃ (∀ j, V → X j) := Equiv.piCongrRight T
  calc ∑ z : ∀ j, V → X j, (∏ j, (μ j).weight (z j)) * H (fun v j => T j (z j) v)
      = ∑ z : ∀ j, V → X j, (∏ j, (μ j).weight (E z j)) * H (fun v j => E z j v) :=
        sum_congr rfl fun z _ => by
          congr 1
          exact prod_congr rfl fun j _ => (hT j (z j)).symm
    _ = ∑ z : ∀ j, V → X j, (∏ j, (μ j).weight (z j)) * H (fun v j => z j v) :=
        Fintype.sum_equiv E _ _ fun _ => rfl

end Tensor

/-! ## Block laws -/

section Block

variable {W : Type*} [Fintype W] [DecidableEq W]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The label alphabet `X_𝔅 = ∏_{p ∈ 𝔅} 𝔽_p` of a block (primes `pr i`, `i ∈ ι`). -/
abbrev BlockLabel : Type _ := ∀ i, ZMod (pr i)

/-- **The block graph law** `λ_𝔅(G) = ⊗_{p ∈ 𝔅} λ_p(G)` (`subsec:push:layer12spectral`): at every
prime of the block independently, the uniform law on the injective strict-square labellings. -/
noncomputable def blockGraphLaw (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) : FiniteLaw (W → BlockLabel pr) :=
  FiniteLaw.tensor fun i => graphLaw G (hne i)

/-- **(R3) for block laws**: invariance under the square-affine maps `z_{w,p} ↦ α_p z_{w,p} + β_p`
with `χ_p(α_p) = 1`, independently at each prime. -/
theorem blockGraphLaw_expect_affine (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (α β : BlockLabel pr)
    (hα : ∀ i, quadraticChar (ZMod (pr i)) (α i) = 1) (H : (W → BlockLabel pr) → ℝ) :
    (blockGraphLaw pr G hne).expect (fun z => H (fun w i => α i * z w i + β i)) =
      (blockGraphLaw pr G hne).expect H := by
  have hα0 : ∀ i, α i ≠ 0 := fun i => ne_zero_of_quadraticChar_eq_one (hα i)
  let T : ∀ i, (W → ZMod (pr i)) ≃ (W → ZMod (pr i)) := fun i =>
    Equiv.piCongrRight fun _ => affineMap (α i) (hα0 i) (β i)
  have hT : ∀ i y, (graphLaw G (hne i)).weight (T i y) = (graphLaw G (hne i)).weight y := by
    intro i y
    have hmem : T i y ∈ injLabellings (ZMod (pr i)) G ↔ y ∈ injLabellings (ZMod (pr i)) G := by
      rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
      exact feasible_affine_iff G (hα i) (β i) y
    simp only [graphLaw, hmem]
  exact expect_tensor_comp (fun i => graphLaw G (hne i)) T hT H

/-- **Block laws are invariant under graph automorphisms**, factorwise. -/
theorem blockGraphLaw_expect_auto (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (π : W ≃ W) (hπ : IsAutomorphism G π)
    (H : (W → BlockLabel pr) → ℝ) :
    (blockGraphLaw pr G hne).expect (fun z => H (z ∘ π)) = (blockGraphLaw pr G hne).expect H := by
  let T : ∀ i, (W → ZMod (pr i)) ≃ (W → ZMod (pr i)) := fun _ => relabel π
  have hT : ∀ i y, (graphLaw G (hne i)).weight (T i y) = (graphLaw G (hne i)).weight y := by
    intro i y
    simp only [graphLaw, T, relabel, Equiv.coe_fn_mk, mem_injLabellings_comp_iff G π hπ y]
  exact expect_tensor_comp (fun i => graphLaw G (hne i)) T hT H

/-- **Every vertex marginal of a block law is uniform on `X_𝔅`.** -/
theorem blockGraphLaw_vertex_uniform (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (w : W) (f : BlockLabel pr → ℝ) :
    (blockGraphLaw pr G hne).expect (fun z => f (z w)) =
      (FiniteLaw.uniform (BlockLabel pr)).expect f := by
  have htr : ∀ c : BlockLabel pr, (blockGraphLaw pr G hne).expect (fun z => f (z w + c)) =
      (blockGraphLaw pr G hne).expect (fun z => f (z w)) := by
    intro c
    have h := blockGraphLaw_expect_affine pr G hne 1 c (fun i => by simp) (fun z => f (z w))
    simp only [Pi.one_apply, one_mul] at h
    exact h
  have hq : (0 : ℝ) < Fintype.card (BlockLabel pr) := by exact_mod_cast Fintype.card_pos
  have hsum : ∑ c : BlockLabel pr, (blockGraphLaw pr G hne).expect (fun z => f (z w + c)) =
      (blockGraphLaw pr G hne).expect (fun _ => ∑ y : BlockLabel pr, f y) := by
    unfold FiniteLaw.expect
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [← mul_sum]
    congr 1
    exact Fintype.sum_equiv (Equiv.addLeft (z w)) _ _ fun _ => rfl
  rw [sum_congr rfl fun c _ => htr c, sum_const, card_univ, nsmul_eq_mul,
    FiniteLaw.expect_const] at hsum
  rw [FiniteLaw.expect_uniform]
  field_simp
  linarith [hsum]

end Block

/-! ## Non-vacuity: labellings exist at every large prime (under H1) -/

section NonVacuity

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- **Under Weil's bound (H1), every finite oriented graph has injective strict-square
labellings at every prime `p ≥ p₀(G)`.** The count `|Inj_p(G)|` is at least the lower product
of `lem:graphs:sequential` (`lowerProd_le_card_inj`), which is positive for large `p` because
`lowerProd/p^{|W|}` tends to `∏ 2^{-t_i} > 0` (`tendsto_lowerProd`). -/
theorem exists_injLabellings_nonempty (hW : Target.Weil) (G : OrientedGraph W) :
    ∃ p₀ : ℕ, ∀ (p : ℕ) [Fact p.Prime], p₀ ≤ p → (injLabellings (ZMod p) G).Nonempty := by
  classical
  set l : List W := (univ : Finset W).toList with hl
  have hnd : l.Nodup := Finset.nodup_toList _
  have hcov : ∀ w, w ∈ l := fun w => (Finset.mem_toList).mpr (mem_univ w)
  have hlim := tendsto_lowerProd G (Fintype.card W) l ∅
  have hpos := powProd_pos G l ∅
  have hev : ∀ᶠ q : ℝ in Filter.atTop, 0 < lowerProd G q (Fintype.card W) ∅ l / q ^ l.length :=
    hlim.eventually (lt_mem_nhds hpos)
  obtain ⟨q₀, hq₀⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 3 ⌈q₀⌉₊, fun p _ hp => ?_⟩
  have hp3 : 3 ≤ p := le_trans (le_max_left _ _) hp
  have hp2 : p ≠ 2 := by omega
  have hq : q₀ ≤ (p : ℝ) := by
    have := le_trans (le_max_right 3 ⌈q₀⌉₊) hp
    exact le_trans (Nat.le_ceil q₀) (by exact_mod_cast this)
  have hdiv := hq₀ p hq
  have hppos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (show 0 < p by omega)
  have hlow : 0 < lowerProd G (p : ℝ) (Fintype.card W) ∅ l := by
    have hden : (0 : ℝ) < (p : ℝ) ^ l.length := pow_pos hppos _
    exact (div_pos_iff_of_pos_right hden).mp hdiv
  have hcard := lowerProd_le_card_inj (weilBound_of_target hW p hp2) G (le_refl _) l hnd hcov
  rw [ZMod.card] at hcard
  have : 0 < (injLabellings (ZMod p) G).card := by exact_mod_cast hlow.trans_le hcard
  exact Finset.card_pos.mp this

end NonVacuity

end Sarkozy.PartV

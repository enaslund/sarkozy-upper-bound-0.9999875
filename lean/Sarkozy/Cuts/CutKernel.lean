module

public import Sarkozy.Cuts.SpecData
public import Sarkozy.Cuts.Envelope
public import Sarkozy.Labellings.GraphLaw

/-!
# Cuts, IX: the cut kernel (`lem:spec:cutkernel` (a), (b))

`13_cuts_correlations.tex`, `subsec:cuts:data`. Fix spectral data `D` on `U` and a finite field
`F` (the paper: `F = 𝔽_p`). A labelling `y` of `G` has halves `x = y|_{U⁺}` (`halfL`) and
`x' = (y ∘ ϑ)|_{U⁺}` (`halfR`). The half graph `G⁺ = G[U⁺]` is `halfGraph`.

* `mem_inj_iff`, `glue_mem_iff`, `halves_glue`, `glue_halves`, `cutK_symm`, `cutK_eq_prod`:
  part (a). `y ↦ (x, x')` is a bijection of `Inj(G)` onto
  `{(x, x') ∈ I⁺ × I⁺ : K(x, x') = 1}`, where
  `K(x, x') = 1{x(U⁺) ∩ x'(U⁺) = ∅} ∏_{(j,k) ∈ E_×} 1_Q(ς_{jk}(x'_k - x_j))`, and `K` is
  symmetric.
* `sum_inj_halves`, `expect_halves`, `cutZ_pos`, `expect_cut_form`, `cutForm_symm`,
  `expect_halfL`, `expect_halfL_eq_halfR`: part (b). Under `λ = λ(G)` the pair `(x, x')` has law
  `μ ⊗ μ · K/Z` with `Z = E_{μ⊗μ} K > 0`. The cut operator `A = T_{K/Z}` on `L²(μ)` is
  self-adjoint, with `E_λ[F(x) H(x')] = ⟨F, A H⟩_μ`. Also `A1 = dm/dμ`, and `x`, `x'` have the
  same law.

Here the nonemptiness of `Inj(G)` is a hypothesis `hne`, and `I⁺ ≠ ∅` follows
(`half_nonempty`). `Sarkozy.Cuts.SpecData.inj_nonempty` derives `hne` from `e_Δ(p, 2n) < 1`.
The rest of the lemma is in other files:
* (c): `Sarkozy.Cuts.CutCount` (`N(x)` and `ϱ`) and `Sarkozy.Cuts.CutMass` (`Z`);
* (d): `Sarkozy.Cuts.CutInvariance`;
* (e) and the block clause of (f): `Sarkozy.Cuts.CutBlock`;
* the one-prime part of (f): below (`expect_halves_w`, `expect_cut_form_w`, `expect_halfL_w`,
  `cutFormW_symm`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The half graph `G⁺ = G[U⁺]`, on the vertex type `U⁺`. -/
def halfGraph : OrientedGraph D.cut.Half where
  E := Finset.univ.filter (fun e : D.cut.Half × D.cut.Half => (e.1.1, e.2.1) ∈ D.G.E)
  loopless u h := D.G.loopless u.1 (Finset.mem_filter.mp h).2
  oriented u v huv hvu := D.G.oriented u.1 v.1 (Finset.mem_filter.mp huv).2
    (Finset.mem_filter.mp hvu).2

theorem mem_halfGraph (e : D.cut.Half × D.cut.Half) :
    e ∈ D.halfGraph.E ↔ (e.1.1, e.2.1) ∈ D.G.E := by
  simp only [halfGraph, Finset.mem_filter, Finset.mem_univ, true_and]

/-- `x = y|_{U⁺}`. -/
def halfL (y : U → F) : D.cut.Half → F := fun k => y k.1

/-- `x' = (y ∘ ϑ)|_{U⁺}`. -/
def halfR (y : U → F) : D.cut.Half → F := fun k => y (D.cut.flip k.1)

/-- The labelling of `U` with halves `(x, x')`. -/
def glue (x x' : D.cut.Half → F) : U → F := fun u =>
  if h : u ∈ D.cut.half then x ⟨u, h⟩ else x' ⟨D.cut.flip u, (D.cut.crosses u).2 h⟩

omit [Field F] [Fintype F] [DecidableEq F] in
theorem glue_halves (y : U → F) : D.glue (D.halfL y) (D.halfR y) = y := by
  funext u
  unfold glue halfL halfR
  by_cases h : u ∈ D.cut.half
  · rw [dite_eq_left h]
  · rw [dite_eq_right h, D.cut.flip_flip]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem halves_glue (x x' : D.cut.Half → F) :
    D.halfL (D.glue x x') = x ∧ D.halfR (D.glue x x') = x' := by
  constructor
  · funext k
    simp only [halfL, glue, dite_eq_left k.2]
  · funext k
    simp only [halfR, glue, dite_eq_right (D.cut.flip_not_mem k.2), D.cut.flip_flip]

/-- The cross constraints and injectivity across the cut. -/
def CutOK (x x' : D.cut.Half → F) : Prop :=
  Disjoint (Finset.univ.image x) (Finset.univ.image x') ∧
    ∀ q ∈ D.crossPairs, quadraticChar F ((D.sgn q.1 q.2 : F) * (x' q.2 - x q.1)) = 1

/-- The cut kernel `K(x, x')` of `eq:spec:K`. -/
noncomputable def cutK (x x' : D.cut.Half → F) : ℝ := by
  classical exact if D.CutOK x x' then 1 else 0

/-- `eq:spec:K` in product form. -/
theorem cutK_eq_prod (x x' : D.cut.Half → F) :
    D.cutK x x' = (if Disjoint (Finset.univ.image x) (Finset.univ.image x') then 1 else 0) *
      ∏ q ∈ D.crossPairs,
        (if quadraticChar F ((D.sgn q.1 q.2 : F) * (x' q.2 - x q.1)) = 1 then (1 : ℝ) else 0) := by
  classical
  rw [Finset.prod_boole]
  unfold cutK CutOK
  by_cases h1 : Disjoint (Finset.univ.image x) (Finset.univ.image x')
  · by_cases h2 : ∀ q ∈ D.crossPairs,
        quadraticChar F ((D.sgn q.1 q.2 : F) * (x' q.2 - x q.1)) = 1
    · rw [ite_eq_left ⟨h1, h2⟩, ite_eq_left h1, ite_eq_left h2, mul_one]
    · rw [ite_eq_right (fun h => h2 h.2), ite_eq_left h1, ite_eq_right h2, mul_zero]
  · rw [ite_eq_right (fun h => h1 h.1), ite_eq_right h1, zero_mul]

theorem mem_inj (G : OrientedGraph U) (y : U → F) :
    y ∈ injLabellings F G ↔ Feasible F G Finset.univ y := by
  unfold injLabellings
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem mem_inj_half (x : D.cut.Half → F) :
    x ∈ injLabellings F D.halfGraph ↔ Feasible F D.halfGraph Finset.univ x := by
  unfold injLabellings
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

/-- A cross pair's constraint is the constraint of its cross edge. -/
theorem cross_char {y : U → F} (hcross : ∀ q ∈ D.crossPairs,
    quadraticChar F ((D.sgn q.1 q.2 : F) * (D.halfR y q.2 - D.halfL y q.1)) = 1)
    (q : D.cut.Half × D.cut.Half) (hq : q ∈ D.crossPairs) (e : U × U)
    (hqe : D.crossEdge q = e) : quadraticChar F (y e.2 - y e.1) = 1 := by
  have h := hcross q hq
  rw [crossPairs, Finset.mem_filter] at hq
  unfold crossEdge at hqe
  by_cases h1 : (q.1.1, D.cut.flip q.2.1) ∈ D.G.E
  · rw [ite_eq_left h1] at hqe
    rw [D.sgn_eq_one h1, Int.cast_one, one_mul] at h
    rw [← hqe]
    exact h
  · rw [ite_eq_right h1] at hqe
    have h2 : (D.cut.flip q.2.1, q.1.1) ∈ D.G.E := by
      by_contra h2
      exact hq.2 (D.sgn_eq_zero h1 h2)
    rw [D.sgn_eq_neg_one h2, Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub] at h
    rw [← hqe]
    exact h

/-- **`lem:spec:cutkernel` (a).** `y ∈ Inj(G)` iff its halves lie in `I⁺ = Inj(G⁺)` and
`K(x, x') = 1`. -/
theorem mem_inj_iff (y : U → F) :
    y ∈ injLabellings F D.G ↔ D.halfL y ∈ injLabellings F D.halfGraph ∧
      D.halfR y ∈ injLabellings F D.halfGraph ∧ D.CutOK (D.halfL y) (D.halfR y) := by
  rw [mem_inj, mem_inj_half, mem_inj_half]
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨⟨fun a _ b _ h => Subtype.ext (hinj a.1 (Finset.mem_univ _) b.1 (Finset.mem_univ _) h),
      fun e he _ _ => ?_⟩, ⟨fun a _ b _ h => Subtype.ext (D.cut.flip.injective
        (hinj _ (Finset.mem_univ _) _ (Finset.mem_univ _) h)), fun e he _ _ => ?_⟩, ?_, ?_⟩
    · exact hedge (e.1.1, e.2.1) ((D.mem_halfGraph e).1 he) (Finset.mem_univ _)
        (Finset.mem_univ _)
    · exact hedge (D.cut.flip e.1.1, D.cut.flip e.2.1) ((D.aut _ _).1 ((D.mem_halfGraph e).1 he))
        (Finset.mem_univ _) (Finset.mem_univ _)
    · rw [Finset.disjoint_left]
      intro a ha ha'
      obtain ⟨j, _, hj⟩ := Finset.mem_image.mp ha
      obtain ⟨k, _, hk⟩ := Finset.mem_image.mp ha'
      have := hinj j.1 (Finset.mem_univ _) (D.cut.flip k.1) (Finset.mem_univ _)
        (by simp only [halfL, halfR] at hj hk; rw [hj, hk])
      exact D.cut.flip_not_mem k.2 (this ▸ j.2)
    · intro q hq
      rw [crossPairs, Finset.mem_filter] at hq
      by_cases h1 : (q.1.1, D.cut.flip q.2.1) ∈ D.G.E
      · rw [D.sgn_eq_one h1, Int.cast_one, one_mul]
        exact hedge _ h1 (Finset.mem_univ _) (Finset.mem_univ _)
      · have h2 : (D.cut.flip q.2.1, q.1.1) ∈ D.G.E := by
          by_contra h2
          exact hq.2 (D.sgn_eq_zero h1 h2)
        rw [D.sgn_eq_neg_one h2, Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub]
        exact hedge _ h2 (Finset.mem_univ _) (Finset.mem_univ _)
  · rintro ⟨⟨hinjL, hedgeL⟩, ⟨hinjR, hedgeR⟩, hdisj, hcross⟩
    have hval : ∀ u (hu : u ∉ D.cut.half),
        D.halfR y ⟨D.cut.flip u, (D.cut.crosses u).2 hu⟩ = y u := fun u _ => by
      simp only [halfR, D.cut.flip_flip]
    have hmix : ∀ u w, u ∈ D.cut.half → w ∉ D.cut.half → y u ≠ y w := by
      intro u w hu hw h
      rw [Finset.disjoint_left] at hdisj
      apply hdisj (Finset.mem_image.mpr ⟨⟨u, hu⟩, Finset.mem_univ _, rfl⟩)
      exact Finset.mem_image.mpr ⟨⟨D.cut.flip w, (D.cut.crosses w).2 hw⟩, Finset.mem_univ _,
        by rw [hval w hw]; exact h.symm⟩
    refine ⟨fun u _ w _ h => ?_, fun e he _ _ => ?_⟩
    · by_cases hu : u ∈ D.cut.half
      · by_cases hw : w ∈ D.cut.half
        · have := hinjL ⟨u, hu⟩ (Finset.mem_univ _) ⟨w, hw⟩ (Finset.mem_univ _) h
          exact congrArg Subtype.val this
        · exact absurd h (hmix u w hu hw)
      · by_cases hw : w ∈ D.cut.half
        · exact absurd h.symm (hmix w u hw hu)
        · have := hinjR ⟨D.cut.flip u, (D.cut.crosses u).2 hu⟩ (Finset.mem_univ _)
            ⟨D.cut.flip w, (D.cut.crosses w).2 hw⟩ (Finset.mem_univ _)
            (by rw [hval u hu, hval w hw]; exact h)
          exact D.cut.flip.injective (congrArg Subtype.val this)
    · by_cases hu : e.1 ∈ D.cut.half
      · by_cases hw : e.2 ∈ D.cut.half
        · exact hedgeL (⟨e.1, hu⟩, ⟨e.2, hw⟩) ((D.mem_halfGraph _).2 he) (Finset.mem_univ _)
            (Finset.mem_univ _)
        · obtain ⟨q, hq, hqe⟩ := D.crossEdge_surj e
            (Finset.mem_filter.mpr ⟨he, Or.inl ⟨hu, hw⟩⟩)
          exact D.cross_char hcross q hq e hqe
      · by_cases hw : e.2 ∈ D.cut.half
        · obtain ⟨q, hq, hqe⟩ := D.crossEdge_surj e
            (Finset.mem_filter.mpr ⟨he, Or.inr ⟨hu, hw⟩⟩)
          exact D.cross_char hcross q hq e hqe
        · have hu' := (D.cut.crosses e.1).2 hu
          have hw' := (D.cut.crosses e.2).2 hw
          have := hedgeR (⟨D.cut.flip e.1, hu'⟩, ⟨D.cut.flip e.2, hw'⟩)
            ((D.mem_halfGraph _).2 ((D.aut _ _).1 he)) (Finset.mem_univ _) (Finset.mem_univ _)
          simpa only [halfR, D.cut.flip_flip] using this

/-- **`lem:spec:cutkernel` (a), the image.** `glue x x' ∈ Inj(G)` iff `x, x' ∈ I⁺` and
`K(x, x') = 1`. -/
theorem glue_mem_iff (x x' : D.cut.Half → F) :
    D.glue x x' ∈ injLabellings F D.G ↔ x ∈ injLabellings F D.halfGraph ∧
      x' ∈ injLabellings F D.halfGraph ∧ D.CutOK x x' := by
  rw [D.mem_inj_iff, (D.halves_glue x x').1, (D.halves_glue x x').2]

/-- **`lem:spec:cutkernel` (a), symmetry.** `K(x, x') = K(x', x)`. -/
theorem cutOK_symm (x x' : D.cut.Half → F) : D.CutOK x x' ↔ D.CutOK x' x := by
  have key : ∀ x x' : D.cut.Half → F, D.CutOK x x' → D.CutOK x' x := by
    intro x x' ⟨hd, hc⟩
    refine ⟨hd.symm, fun q hq => ?_⟩
    have hq' : (q.2, q.1) ∈ D.crossPairs := (D.mem_crossPairs_swap q.1 q.2).1 hq
    have h := hc (q.2, q.1) hq'
    simp only at h
    rw [D.sgn_antisymm q.1 q.2, Int.cast_neg, neg_mul, ← mul_neg, neg_sub] at h
    exact h
  exact ⟨key x x', key x' x⟩

theorem cutK_symm (x x' : D.cut.Half → F) : D.cutK x x' = D.cutK x' x := by
  classical
  unfold cutK
  by_cases h : D.CutOK x x'
  · rw [ite_eq_left h, ite_eq_left ((D.cutOK_symm x x').1 h)]
  · rw [ite_eq_right h, ite_eq_right (fun h' => h ((D.cutOK_symm x x').2 h'))]

theorem cutK_nonneg (x x' : D.cut.Half → F) : 0 ≤ D.cutK x x' := by
  classical
  unfold cutK
  split_ifs <;> norm_num

/-- `I⁺ ≠ ∅` when `Inj(G) ≠ ∅`. -/
theorem half_nonempty (hne : (injLabellings F D.G).Nonempty) :
    (injLabellings F D.halfGraph).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  exact ⟨D.halfL y, ((D.mem_inj_iff y).1 hy).1⟩

/-- The sum over `Inj(G)` is the `K`-weighted sum over `I⁺ × I⁺`. -/
theorem sum_inj_halves (Φ : (D.cut.Half → F) → (D.cut.Half → F) → ℝ) :
    ∑ y ∈ injLabellings F D.G, Φ (D.halfL y) (D.halfR y) =
      ∑ x ∈ injLabellings F D.halfGraph, ∑ x' ∈ injLabellings F D.halfGraph,
        D.cutK x x' * Φ x x' := by
  classical
  rw [← Finset.sum_product' (f := fun x x' => D.cutK x x' * Φ x x')]
  have e : ∑ q ∈ injLabellings F D.halfGraph ×ˢ injLabellings F D.halfGraph,
      D.cutK q.1 q.2 * Φ q.1 q.2 =
      ∑ q ∈ (injLabellings F D.halfGraph ×ˢ injLabellings F D.halfGraph).filter
        (fun q => D.CutOK q.1 q.2), Φ q.1 q.2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    unfold cutK
    split_ifs <;> ring
  rw [e]
  refine Finset.sum_nbij' (fun y => (D.halfL y, D.halfR y)) (fun q => D.glue q.1 q.2)
    ?_ ?_ ?_ ?_ ?_
  · intro y hy
    obtain ⟨h1, h2, h3⟩ := (D.mem_inj_iff y).1 hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨h1, h2⟩, h3⟩
  · intro q hq
    obtain ⟨hq1, hq2⟩ := Finset.mem_filter.mp hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq1
    exact (D.glue_mem_iff q.1 q.2).2 ⟨h1, h2, hq2⟩
  · intro y _
    exact D.glue_halves y
  · intro q _
    obtain ⟨h1, h2⟩ := D.halves_glue q.1 q.2
    exact Prod.ext h1 h2
  · intro y _
    rfl

theorem graphLaw_expect' {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) (Φ : (W → F) → ℝ) :
    (graphLaw G hne).expect Φ = (∑ z ∈ injLabellings F G, Φ z) / (injLabellings F G).card := by
  simp only [FiniteLaw.expect, graphLaw, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun z _ => by ring)

/-- The half law `μ = λ(G⁺)`. -/
noncomputable def halfLaw (hne : (injLabellings F D.G).Nonempty) : FiniteLaw (D.cut.Half → F) :=
  graphLaw D.halfGraph (D.half_nonempty hne)

/-- `Z = E_{μ⊗μ} K`. -/
noncomputable def cutZ (hne : (injLabellings F D.G).Nonempty) : ℝ :=
  ((D.halfLaw hne).product (D.halfLaw hne)).expect (fun q => D.cutK q.1 q.2)

theorem expect_product_cutK (hne : (injLabellings F D.G).Nonempty)
    (Φ : (D.cut.Half → F) → (D.cut.Half → F) → ℝ) :
    ((D.halfLaw hne).product (D.halfLaw hne)).expect (fun q => D.cutK q.1 q.2 * Φ q.1 q.2) =
      (∑ y ∈ injLabellings F D.G, Φ (D.halfL y) (D.halfR y)) /
        ((injLabellings F D.halfGraph).card : ℝ) ^ 2 := by
  rw [FiniteLaw.expect_product, D.sum_inj_halves]
  unfold halfLaw
  rw [graphLaw_expect']
  simp only [graphLaw_expect']
  rw [← Finset.sum_div, div_div, sq]

/-- **`lem:spec:cutkernel` (b).** `Z = |Inj(G)|/|I⁺|² > 0`. -/
theorem cutZ_eq (hne : (injLabellings F D.G).Nonempty) :
    D.cutZ hne = ((injLabellings F D.G).card : ℝ) /
      ((injLabellings F D.halfGraph).card : ℝ) ^ 2 := by
  have h := D.expect_product_cutK hne (fun _ _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  unfold cutZ
  rw [h]

theorem cutZ_pos (hne : (injLabellings F D.G).Nonempty) : 0 < D.cutZ hne := by
  rw [D.cutZ_eq hne]
  have h1 : (0 : ℝ) < (injLabellings F D.G).card := by exact_mod_cast Finset.card_pos.mpr hne
  have h2 : (0 : ℝ) < (injLabellings F D.halfGraph).card := by
    exact_mod_cast Finset.card_pos.mpr (D.half_nonempty hne)
  positivity

/-- **`lem:spec:cutkernel` (b), the law of the halves.** Under `λ = λ(G)` the pair `(x, x')` has
law `μ ⊗ μ · K/Z`: `E_λ Φ(x, x') = E_{μ⊗μ}[K Φ]/Z`. -/
theorem expect_halves (hne : (injLabellings F D.G).Nonempty)
    (Φ : (D.cut.Half → F) → (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => Φ (D.halfL y) (D.halfR y)) =
      ((D.halfLaw hne).product (D.halfLaw hne)).expect (fun q => D.cutK q.1 q.2 * Φ q.1 q.2) /
        D.cutZ hne := by
  rw [D.expect_product_cutK, D.cutZ_eq, graphLaw_expect']
  have h2 : (0 : ℝ) < (injLabellings F D.halfGraph).card := by
    exact_mod_cast Finset.card_pos.mpr (D.half_nonempty hne)
  field_simp

/-- The normalized cut operator `A = T_{K/Z}` on `L²(μ)`, as a form. -/
noncomputable def cutForm (hne : (injLabellings F D.G).Nonempty) :
    ((D.cut.Half → F) → ℝ) →ₗ[ℝ] ((D.cut.Half → F) → ℝ) →ₗ[ℝ] ℝ :=
  kernelForm (D.halfLaw hne) (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne)

/-- **`lem:spec:cutkernel` (b).** `E_λ[F(x) H(x')] = ⟨F, A H⟩_μ`. -/
theorem expect_cut_form (hne : (injLabellings F D.G).Nonempty) (Fn Hn : (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => Fn (D.halfL y) * Hn (D.halfR y)) =
      D.cutForm hne Fn Hn := by
  rw [D.expect_halves hne (fun x x' => Fn x * Hn x'), cutForm, kernelForm_apply,
    FiniteLaw.expect_product, ← Sarkozy.Peyre.expect_div_const]
  refine (D.halfLaw hne).expect_congr (fun x => ?_)
  rw [← Sarkozy.Peyre.expect_div_const, ← FiniteLaw.expect_const_mul]
  refine (D.halfLaw hne).expect_congr (fun x' => ?_)
  ring

/-- **`lem:spec:cutkernel` (b).** `A` is self-adjoint. -/
theorem cutForm_symm (hne : (injLabellings F D.G).Nonempty) (Fn Hn : (D.cut.Half → F) → ℝ) :
    D.cutForm hne Fn Hn = D.cutForm hne Hn Fn :=
  kernelForm_symm _ _ (fun x x' => by rw [D.cutK_symm]) Fn Hn

/-- **`lem:spec:cutkernel` (b).** `A1 = ϱ = dm/dμ`: the law `m` of `x` under `λ` has density
`A1` relative to `μ`. -/
theorem expect_halfL (hne : (injLabellings F D.G).Nonempty) (Fn : (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => Fn (D.halfL y)) =
      (D.halfLaw hne).expect (fun x => Fn x *
        rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x) := by
  have h := D.expect_cut_form hne Fn (fun _ => 1)
  simp only [mul_one] at h
  rw [h, cutForm, kernelForm_one_right]
  rfl

/-- **`lem:spec:cutkernel` (b).** `x` and `x'` have the same law. -/
theorem expect_halfL_eq_halfR (hne : (injLabellings F D.G).Nonempty)
    (Fn : (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => Fn (D.halfL y)) =
      (graphLaw D.G hne).expect (fun y => Fn (D.halfR y)) := by
  have h1 := D.expect_cut_form hne Fn (fun _ => 1)
  have h2 := D.expect_cut_form hne (fun _ => 1) Fn
  simp only [mul_one, one_mul] at h1 h2
  rw [h1, h2, D.cutForm_symm]

/-! ### `lem:spec:cutkernel` (f), positive reweightings

For `w ≥ 0` on labellings with `E_λ w > 0`, `λ^w = wλ/E_λ w`; its expectations are
`E_{λ^w} Φ = E_λ[w Φ]/E_λ w`. We write `w(x, x') = w(glue x x')`. -/

/-- The reweighted cut operator `A^w`, with kernel `w K/(Z E_λ w)` relative to `μ ⊗ μ`. -/
noncomputable def cutFormW (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ) :
    ((D.cut.Half → F) → ℝ) →ₗ[ℝ] ((D.cut.Half → F) → ℝ) →ₗ[ℝ] ℝ :=
  kernelForm (D.halfLaw hne) (D.halfLaw hne)
    (fun x x' => w (D.glue x x') * D.cutK x x' / (D.cutZ hne * (graphLaw D.G hne).expect w))

/-- **`lem:spec:cutkernel` (f).** Under `λ^w` the pair `(x, x')` has law
`μ ⊗ μ · wK/(Z E_λ w)`. -/
theorem expect_halves_w (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ)
    (Φ : (D.cut.Half → F) → (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => w y * Φ (D.halfL y) (D.halfR y)) /
        (graphLaw D.G hne).expect w =
      ((D.halfLaw hne).product (D.halfLaw hne)).expect
        (fun q => w (D.glue q.1 q.2) * D.cutK q.1 q.2 * Φ q.1 q.2) /
        (D.cutZ hne * (graphLaw D.G hne).expect w) := by
  have h := D.expect_halves hne (fun x x' => w (D.glue x x') * Φ x x')
  simp only [D.glue_halves] at h
  rw [h, div_div]
  congr 1
  refine ((D.halfLaw hne).product (D.halfLaw hne)).expect_congr (fun q => ?_)
  ring

/-- **`lem:spec:cutkernel` (f).** `E_{λ^w}[F(x) H(x')] = ⟨F, A^w H⟩_μ`. -/
theorem expect_cut_form_w (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ)
    (Fn Hn : (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => w y * (Fn (D.halfL y) * Hn (D.halfR y))) /
        (graphLaw D.G hne).expect w = D.cutFormW hne w Fn Hn := by
  rw [D.expect_halves_w hne w (fun x x' => Fn x * Hn x'), cutFormW, kernelForm_apply]
  set c := D.cutZ hne * (graphLaw D.G hne).expect w with hc
  rw [FiniteLaw.expect_product, ← Sarkozy.Peyre.expect_div_const]
  refine (D.halfLaw hne).expect_congr (fun x => ?_)
  rw [← Sarkozy.Peyre.expect_div_const, ← FiniteLaw.expect_const_mul]
  refine (D.halfLaw hne).expect_congr (fun x' => ?_)
  ring

/-- **`lem:spec:cutkernel` (f).** `A^w 1 = dm^w/dμ`, where `m^w` is the law of `x` under `λ^w`. -/
theorem expect_halfL_w (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ)
    (Fn : (D.cut.Half → F) → ℝ) :
    (graphLaw D.G hne).expect (fun y => w y * Fn (D.halfL y)) / (graphLaw D.G hne).expect w =
      (D.halfLaw hne).expect (fun x => Fn x * rowFun (D.halfLaw hne)
        (fun x x' => w (D.glue x x') * D.cutK x x' /
          (D.cutZ hne * (graphLaw D.G hne).expect w)) x) := by
  have h := D.expect_cut_form_w hne w Fn (fun _ => 1)
  simp only [mul_one] at h
  rw [h, cutFormW, kernelForm_one_right]
  rfl

/-- **`lem:spec:cutkernel` (f).** `A^w` is self-adjoint if `w(x, x') = w(x', x)`. -/
theorem cutFormW_symm (hne : (injLabellings F D.G).Nonempty) (w : (U → F) → ℝ)
    (hw : ∀ x x', w (D.glue x x') = w (D.glue x' x)) (Fn Hn : (D.cut.Half → F) → ℝ) :
    D.cutFormW hne w Fn Hn = D.cutFormW hne w Hn Fn :=
  kernelForm_symm _ _ (fun x x' => by rw [D.cutK_symm, hw]) Fn Hn

end SpecData

end Sarkozy.Cuts

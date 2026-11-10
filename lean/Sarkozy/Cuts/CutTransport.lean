module

public import Sarkozy.Cuts.CutKernel

/-!
# Cuts, X: transport along isomorphisms (`lem:cut-transport`)

`13_cuts_correlations.tex`, `lem:cut-transport`. Let `D`, `D'` be spectral data, and let
`φ : U ≃ U'` be an isomorphism of oriented graphs with `φ(U⁺) = U'⁺` and `φ ∘ ϑ = ϑ' ∘ φ`.

* `inj_iso`, `graphLaw_iso`: an isomorphism of oriented graphs `e` gives a bijection
  `y ↦ y ∘ e⁻¹` of the injective strict-square labellings, so the graph laws correspond.
* `halfEquiv`, `halfL_transport`, `halfR_transport`: the halves of `y ∘ φ⁻¹` are
  `(x ∘ φ⁻¹, x' ∘ φ⁻¹)`.
* `transport_unitary`, `transport_cutForm`, `transport_density`: `Φ F(ξ) = F(ξ ∘ φ)` is unitary
  `L²(μ) → L²(μ')`, with `Φ A Φ* = A'` and `Φ ϱ = ϱ'` (both in weak form).

* `tdeg_transport`, `Rcut_transport`: if `φ` maps `𝔬` to `𝔬'`, the row ratios agree.

The clauses on label subspaces and on blocks of primes are in `Sarkozy.Cuts.CutTransportBlock`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

section Iso

variable {W W' : Type*} [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']

/-- An isomorphism of oriented graphs maps `Inj(G)` onto `Inj(G')` by `y ↦ y ∘ e⁻¹`. -/
theorem inj_iso (G : OrientedGraph W) (G' : OrientedGraph W') (e : W ≃ W')
    (he : ∀ u w, (u, w) ∈ G.E ↔ (e u, e w) ∈ G'.E) (y : W → F) :
    y ∈ injLabellings F G ↔ (fun w' => y (e.symm w')) ∈ injLabellings F G' := by
  rw [SpecData.mem_inj, SpecData.mem_inj]
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a _ b _ h => e.symm.injective (hinj _ (Finset.mem_univ _) _ (Finset.mem_univ _) h),
      fun q hq _ _ => ?_⟩
    have : (e.symm q.1, e.symm q.2) ∈ G.E := by
      rw [he, e.apply_symm_apply, e.apply_symm_apply]
      exact hq
    exact hedge _ this (Finset.mem_univ _) (Finset.mem_univ _)
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a _ b _ h => ?_, fun q hq _ _ => ?_⟩
    · have := hinj (e a) (Finset.mem_univ _) (e b) (Finset.mem_univ _)
        (by simp only [e.symm_apply_apply]; exact h)
      exact e.injective this
    · have := hedge (e q.1, e q.2) ((he _ _).1 hq) (Finset.mem_univ _) (Finset.mem_univ _)
      simpa only [e.symm_apply_apply] using this

/-- The graph laws correspond: `E_{λ(G')} Ψ = E_{λ(G)} Ψ(y ∘ e⁻¹)`. -/
theorem graphLaw_iso (G : OrientedGraph W) (G' : OrientedGraph W') (e : W ≃ W')
    (he : ∀ u w, (u, w) ∈ G.E ↔ (e u, e w) ∈ G'.E) (hne : (injLabellings F G).Nonempty)
    (hne' : (injLabellings F G').Nonempty) (Ψ : (W' → F) → ℝ) :
    (graphLaw G' hne').expect Ψ = (graphLaw G hne).expect (fun y => Ψ (fun w' => y (e.symm w'))) := by
  rw [SpecData.graphLaw_expect', SpecData.graphLaw_expect']
  have hmap : ∀ y ∈ injLabellings F G, (fun w' => y (e.symm w')) ∈ injLabellings F G' :=
    fun y hy => (inj_iso G G' e he y).1 hy
  have hmap' : ∀ y' ∈ injLabellings F G', (fun w => y' (e w)) ∈ injLabellings F G := by
    intro y' hy'
    rw [inj_iso G G' e he]
    simpa only [e.apply_symm_apply] using hy'
  have hcard : (injLabellings F G').card = (injLabellings F G).card :=
    (Finset.card_bij' (fun y _ => fun w' => y (e.symm w')) (fun y' _ => fun w => y' (e w)) hmap hmap'
      (fun y _ => by funext w; simp only [e.symm_apply_apply])
      (fun y' _ => by funext w'; simp only [e.apply_symm_apply])).symm
  rw [hcard]
  congr 1
  symm
  exact Finset.sum_nbij' (fun y => fun w' => y (e.symm w')) (fun y' => fun w => y' (e w)) hmap hmap'
    (fun y _ => by funext w; simp only [e.symm_apply_apply])
    (fun y' _ => by funext w'; simp only [e.apply_symm_apply]) (fun y _ => rfl)

end Iso

namespace SpecData

variable {U U' : Type*} [Fintype U] [DecidableEq U] [Fintype U'] [DecidableEq U']
  (D : SpecData U) (D' : SpecData U')

/-- The hypotheses of `lem:cut-transport`. -/
structure Transport (φ : U ≃ U') : Prop where
  edges : ∀ u w, (u, w) ∈ D.G.E ↔ (φ u, φ w) ∈ D'.G.E
  half : ∀ u, u ∈ D.cut.half ↔ φ u ∈ D'.cut.half
  flip : ∀ u, φ (D.cut.flip u) = D'.cut.flip (φ u)

variable {D D'} {φ : U ≃ U'}

/-- `φ` restricted to `U⁺ → U'⁺`. -/
def halfEquiv (hφ : D.Transport D' φ) : D.cut.Half ≃ D'.cut.Half where
  toFun k := ⟨φ k.1, (hφ.half k.1).1 k.2⟩
  invFun k' := ⟨φ.symm k'.1, (hφ.half _).2 (by rw [φ.apply_symm_apply]; exact k'.2)⟩
  left_inv k := Subtype.ext (φ.symm_apply_apply k.1)
  right_inv k' := Subtype.ext (φ.apply_symm_apply k'.1)

theorem flip_symm (hφ : D.Transport D' φ) (v' : U') :
    φ.symm (D'.cut.flip v') = D.cut.flip (φ.symm v') := by
  apply φ.injective
  rw [φ.apply_symm_apply, hφ.flip, φ.apply_symm_apply]

theorem halfGraph_iso (hφ : D.Transport D' φ) (j k : D.cut.Half) :
    (j, k) ∈ D.halfGraph.E ↔ (halfEquiv hφ j, halfEquiv hφ k) ∈ D'.halfGraph.E := by
  rw [mem_halfGraph, mem_halfGraph]
  exact hφ.edges j.1 k.1

omit [Field F] [Fintype F] [DecidableEq F] in
/-- **`lem:cut-transport`.** The halves of `y ∘ φ⁻¹` are `x ∘ φ⁻¹`. -/
theorem halfL_transport (hφ : D.Transport D' φ) (y : U → F) :
    D'.halfL (fun u' => y (φ.symm u')) = fun k' => D.halfL y ((halfEquiv hφ).symm k') := rfl

omit [Field F] [Fintype F] [DecidableEq F] in
/-- **`lem:cut-transport`.** … and `x' ∘ φ⁻¹`. -/
theorem halfR_transport (hφ : D.Transport D' φ) (y : U → F) :
    D'.halfR (fun u' => y (φ.symm u')) = fun k' => D.halfR y ((halfEquiv hφ).symm k') := by
  funext k'
  simp only [halfR, halfEquiv, Equiv.coe_fn_symm_mk]
  rw [flip_symm hφ]

theorem nonempty_transport (hφ : D.Transport D' φ) (hne : (injLabellings F D.G).Nonempty) :
    (injLabellings F D'.G).Nonempty := by
  obtain ⟨y, hy⟩ := hne
  exact ⟨_, (inj_iso D.G D'.G φ hφ.edges y).1 hy⟩

/-- `Φ F(ξ) = F(ξ ∘ φ)`. -/
def transportFun (hφ : D.Transport D' φ) (Fn : (D.cut.Half → F) → ℝ) :
    (D'.cut.Half → F) → ℝ := fun ξ => Fn (fun k => ξ (halfEquiv hφ k))

omit [Field F] [Fintype F] [DecidableEq F] in
theorem transportFun_comp (hφ : D.Transport D' φ) (Fn : (D.cut.Half → F) → ℝ)
    (x : D.cut.Half → F) :
    transportFun hφ Fn (fun k' => x ((halfEquiv hφ).symm k')) = Fn x := by
  simp only [transportFun, Equiv.symm_apply_apply]

/-- **`lem:cut-transport`.** `Φ` is unitary `L²(μ) → L²(μ')`:
`⟨Φ F, Φ H⟩_{μ'} = ⟨F, H⟩_μ`. -/
theorem transport_unitary (hφ : D.Transport D' φ) (hne : (injLabellings F D.G).Nonempty)
    (Fn Hn : (D.cut.Half → F) → ℝ) :
    ip (D'.halfLaw (nonempty_transport hφ hne)) (transportFun hφ Fn) (transportFun hφ Hn) =
      ip (D.halfLaw hne) Fn Hn := by
  unfold ip halfLaw
  rw [graphLaw_iso D.halfGraph D'.halfGraph (halfEquiv hφ) (halfGraph_iso hφ)
    (D.half_nonempty hne)]
  refine (graphLaw D.halfGraph (D.half_nonempty hne)).expect_congr (fun x => ?_)
  rw [transportFun_comp, transportFun_comp]

/-- **`lem:cut-transport`.** `Φ A Φ* = A'`: `⟨Φ F, A' Φ H⟩_{μ'} = ⟨F, A H⟩_μ`. -/
theorem transport_cutForm (hφ : D.Transport D' φ) (hne : (injLabellings F D.G).Nonempty)
    (Fn Hn : (D.cut.Half → F) → ℝ) :
    D'.cutForm (nonempty_transport hφ hne) (transportFun hφ Fn) (transportFun hφ Hn) =
      D.cutForm hne Fn Hn := by
  rw [← D'.expect_cut_form, ← D.expect_cut_form,
    graphLaw_iso D.G D'.G φ hφ.edges hne]
  refine (graphLaw D.G hne).expect_congr (fun y => ?_)
  rw [halfL_transport hφ, halfR_transport hφ, transportFun_comp, transportFun_comp]

/-- **`lem:cut-transport`.** `Φ ϱ = ϱ'`, in weak form: `⟨Φ F, ϱ'⟩_{μ'} = ⟨F, ϱ⟩_μ`. -/
theorem transport_density (hφ : D.Transport D' φ) (hne : (injLabellings F D.G).Nonempty)
    (Fn : (D.cut.Half → F) → ℝ) :
    (D'.halfLaw (nonempty_transport hφ hne)).expect (fun ξ => transportFun hφ Fn ξ *
        rowFun (D'.halfLaw (nonempty_transport hφ hne))
          (fun ξ ξ' => D'.cutK ξ ξ' / D'.cutZ (nonempty_transport hφ hne)) ξ) =
      (D.halfLaw hne).expect (fun x => Fn x *
        rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x) := by
  rw [← D'.expect_halfL, ← D.expect_halfL, graphLaw_iso D.G D'.G φ hφ.edges hne]
  refine (graphLaw D.G hne).expect_congr (fun y => ?_)
  rw [halfL_transport hφ, transportFun_comp]

theorem card_half_eq (hφ : D.Transport D' φ) : D.cut.half.card = D'.cut.half.card := by
  have := Fintype.card_congr (halfEquiv hφ)
  simpa only [Fintype.card_coe] using this

/-- **`lem:cut-transport`, row ratios.** If `φ` maps the deletion order `𝔬` to `𝔬'`, the
deletion degrees agree. -/
theorem tdeg_transport (hφ : D.Transport D' φ)
    (horder : ∀ i, (D'.order (Fin.cast (card_half_eq hφ) i)).1 = φ (D.order i).1)
    (i : Fin D.cut.half.card) : D'.tdeg (Fin.cast (card_half_eq hφ) i) = D.tdeg i := by
  unfold tdeg
  symm
  refine Finset.card_nbij' (fun w => φ w) (fun w' => φ.symm w') ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw ⊢
    obtain ⟨hadj, hnot⟩ := hw
    refine ⟨?_, fun j hj hjw => ?_⟩
    · rw [horder]
      unfold Adj at hadj ⊢
      rw [← hφ.edges, ← hφ.edges]
      exact hadj
    · have hj' : Fin.cast (card_half_eq hφ).symm j < i := by
        rw [Fin.lt_def] at hj ⊢
        simpa using hj
      apply hnot _ hj'
      apply φ.injective
      rw [hjw]
      have := horder (Fin.cast (card_half_eq hφ).symm j)
      simp only [Fin.cast_cast, Fin.cast_eq_self] at this
      exact this
  · intro w' hw'
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw' ⊢
    obtain ⟨hadj, hnot⟩ := hw'
    refine ⟨?_, fun j hj hjw => ?_⟩
    · rw [horder] at hadj
      unfold Adj at hadj ⊢
      have hw : w' = φ (φ.symm w') := (φ.apply_symm_apply w').symm
      rw [hw, ← hφ.edges, ← hφ.edges] at hadj
      exact hadj
    · apply hnot (Fin.cast (card_half_eq hφ) j) (by rw [Fin.lt_def] at hj ⊢; simpa using hj)
      rw [horder, ← hjw, φ.apply_symm_apply]
  · intro w _
    exact φ.symm_apply_apply w
  · intro w' _
    exact φ.apply_symm_apply w'

/-- **`lem:cut-transport`, row ratios.** If `φ` maps `𝔬` to `𝔬'`, then `R_cut = R'_cut` for every
error function `e`. -/
theorem Rcut_transport (hφ : D.Transport D' φ)
    (horder : ∀ i, (D'.order (Fin.cast (card_half_eq hφ) i)).1 = φ (D.order i).1)
    (e : ℕ → ℝ) : D'.Rcut e = D.Rcut e := by
  unfold Rcut
  symm
  exact Fintype.prod_equiv (finCongr (card_half_eq hφ)) _ _ (fun i => by
    simp only [finCongr_apply]
    rw [tdeg_transport hφ horder i])

end SpecData

end Sarkozy.Cuts

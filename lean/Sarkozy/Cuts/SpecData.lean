module

public import Sarkozy.Labellings.Sequential
public import Sarkozy.Reflection.Basic

/-!
# Cuts, VI: spectral data (`def:spec:data`, `lem:spec:elementary`)

`13_cuts_correlations.tex`, `subsec:cuts:data`. Spectral data `(G, ϑ, U⁺, 𝔬)` consist of:
* an oriented graph `G` on `U` (`Sarkozy.Labellings.OrientedGraph`);
* a reflection cut `(U⁺, ϑ)` (`Sarkozy.ReflectionCut`: `ϑ` is an involution with
  `ϑ(U⁺) = U ∖ U⁺`) such that `ϑ` is an orientation-preserving automorphism of `G`;
* a deletion order `𝔬 = (v_1, …, v_n)` of `U⁺`.

The notation of `def:spec:data`: `deg0` (`d⁰_k`), `DeltaPlus` (`Δ⁺`), `edgesIn` (`e(L)`),
`sgn` (the cross signs `ς_{jk}`), `Nset`, `rdeg` (`N(k)`, `r_k`), `dk`, `Delta`, `crossPairs`
(`E_×`), `mcross` (`m_×`), `tdeg` (the deletion degrees `t_i`), `Rcut` (`eq:spec:Rcut`) and `S1`.

`Rcut` and `S1` take the count-error function `t ↦ e_t(p, 2n)` as an argument `e`. The paper's
`e_t(p, n) = 2^t (h_t r + n r²)` of `eq:graphs:et` is `Sarkozy.TraceMixing.coarseErr` (used in
`Sarkozy.Cuts.CutCount`).

`lem:spec:elementary` is `sgn_not_both`, `sgn_antisymm`, `sgn_self`, `mem_crossPairs_swap`,
`card_sgn_ne_zero`, `crossPairs_bijOn`/`mcross_eq`, `degree_eq_dk`, `degree_flip`,
`maxDegree_eq_Delta` and `flip_isom`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy

/-- **`def:spec:data`, (S0).** Spectral data: an oriented graph with an orientation-preserving
involutive automorphism exchanging `U⁺` and `U⁻`, and a deletion order of `U⁺`. -/
structure SpecData (U : Type*) [Fintype U] [DecidableEq U] where
  G : Labellings.OrientedGraph U
  cut : ReflectionCut U
  aut : ∀ u w, (u, w) ∈ G.E ↔ (cut.flip u, cut.flip w) ∈ G.E
  order : Fin cut.half.card ≃ cut.Half

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- Adjacency in `G`, in either orientation. -/
def Adj (u w : U) : Prop := (u, w) ∈ D.G.E ∨ (w, u) ∈ D.G.E

instance (u w : U) : Decidable (D.Adj u w) := inferInstanceAs (Decidable (_ ∨ _))

theorem adj_symm {u w : U} : D.Adj u w ↔ D.Adj w u := Or.comm

theorem adj_flip (u w : U) : D.Adj (D.cut.flip u) (D.cut.flip w) ↔ D.Adj u w := by
  unfold Adj
  rw [← D.aut, ← D.aut]

/-- `n = |U⁺|`. -/
def n : ℕ := D.cut.half.card

/-- `d⁰_k`, the degree of `k` in `G⁺ = G[U⁺]`. -/
def deg0 (k : D.cut.Half) : ℕ := (Finset.univ.filter (fun j : D.cut.Half => D.Adj j.1 k.1)).card

/-- `Δ⁺ = max_k d⁰_k`. -/
def DeltaPlus : ℕ := Finset.univ.sup D.deg0

/-- `e(L)`, the number of edges of `G⁺` inside `L ⊆ U⁺`. -/
def edgesIn (L : Finset U) : ℕ := (D.G.E.filter (fun e => e.1 ∈ L ∧ e.2 ∈ L)).card

/-- The cross sign `ς_{jk}`: `+1` if `(j, ϑk) ∈ E`, `-1` if `(ϑk, j) ∈ E`, else `0`. -/
def sgn (j k : D.cut.Half) : ℤ :=
  if (j.1, D.cut.flip k.1) ∈ D.G.E then 1 else if (D.cut.flip k.1, j.1) ∈ D.G.E then -1 else 0

/-- `N(k) = {j ∈ U⁺ : ς_{jk} ≠ 0}`. -/
def Nset (k : D.cut.Half) : Finset D.cut.Half := Finset.univ.filter (fun j => D.sgn j k ≠ 0)

/-- `r_k = |N(k)|`. -/
def rdeg (k : D.cut.Half) : ℕ := (D.Nset k).card

/-- `d_k = d⁰_k + r_k`. -/
def dk (k : D.cut.Half) : ℕ := D.deg0 k + D.rdeg k

/-- `Δ = max_k d_k`. -/
def Delta : ℕ := Finset.univ.sup D.dk

/-- The cross pairs `E_× = {(j, k) : ς_{jk} ≠ 0}`. -/
def crossPairs : Finset (D.cut.Half × D.cut.Half) :=
  Finset.univ.filter (fun q => D.sgn q.1 q.2 ≠ 0)

/-- `m_× = |E_×|`. -/
def mcross : ℕ := D.crossPairs.card

/-- The deletion degree `t_i`: the number of `G`-neighbours of `v_i` in
`U ∖ {v_1, …, v_{i-1}}`. -/
def tdeg (i : Fin D.cut.half.card) : ℕ :=
  (Finset.univ.filter (fun w : U => D.Adj (D.order i).1 w ∧
    ∀ j : Fin D.cut.half.card, j < i → w ≠ (D.order j).1)).card

/-- The row ratio `R_cut(p) = ∏_i (1 + e_{t_i}(p, 2n))/(1 - e_{t_i}(p, 2n))`
(`eq:spec:Rcut`), for the error function `e t = e_t(p, 2n)`. -/
noncomputable def Rcut (e : ℕ → ℝ) : ℝ := ∏ i, (1 + e (D.tdeg i)) / (1 - e (D.tdeg i))

/-- **(S1)**, the threshold hypothesis at `p₀`: `e_Δ(p₀, 2n) < 1` and `p₀ > 4n²`, for the
error function `e t = e_t(p₀, 2n)`. -/
def S1 (e : ℕ → ℝ) (p₀ : ℝ) : Prop := e D.Delta < 1 ∧ 4 * (D.n : ℝ) ^ 2 < p₀

/-! ### `lem:spec:elementary` -/

/-- `ς` is well defined: `G` does not contain both `(j, ϑk)` and `(ϑk, j)`. -/
theorem sgn_not_both (j k : D.cut.Half) :
    ¬((j.1, D.cut.flip k.1) ∈ D.G.E ∧ (D.cut.flip k.1, j.1) ∈ D.G.E) :=
  fun h => D.G.oriented _ _ h.1 h.2

theorem sgn_eq_one {j k : D.cut.Half} (h : (j.1, D.cut.flip k.1) ∈ D.G.E) : D.sgn j k = 1 := by
  simp only [sgn, h, ↓reduceIte]

theorem sgn_eq_neg_one {j k : D.cut.Half} (h : (D.cut.flip k.1, j.1) ∈ D.G.E) :
    D.sgn j k = -1 := by
  have hn : (j.1, D.cut.flip k.1) ∉ D.G.E := fun h' => D.sgn_not_both j k ⟨h', h⟩
  simp only [sgn, hn, h, ↓reduceIte]

theorem sgn_eq_zero {j k : D.cut.Half} (h1 : (j.1, D.cut.flip k.1) ∉ D.G.E)
    (h2 : (D.cut.flip k.1, j.1) ∉ D.G.E) : D.sgn j k = 0 := by
  simp only [sgn, h1, h2, ↓reduceIte]

theorem flip_mem_iff (j k : D.cut.Half) :
    (k.1, D.cut.flip j.1) ∈ D.G.E ↔ (D.cut.flip k.1, j.1) ∈ D.G.E := by
  rw [D.aut, D.cut.flip_flip]

theorem flip_mem_iff' (j k : D.cut.Half) :
    (D.cut.flip j.1, k.1) ∈ D.G.E ↔ (j.1, D.cut.flip k.1) ∈ D.G.E := by
  rw [D.aut, D.cut.flip_flip]

/-- `ς_{kj} = -ς_{jk}`. -/
theorem sgn_antisymm (j k : D.cut.Half) : D.sgn k j = -D.sgn j k := by
  by_cases h1 : (j.1, D.cut.flip k.1) ∈ D.G.E
  · rw [D.sgn_eq_one h1, D.sgn_eq_neg_one ((D.flip_mem_iff' j k).2 h1)]
  · by_cases h2 : (D.cut.flip k.1, j.1) ∈ D.G.E
    · rw [D.sgn_eq_neg_one h2, D.sgn_eq_one ((D.flip_mem_iff j k).2 h2), neg_neg]
    · rw [D.sgn_eq_zero h1 h2, D.sgn_eq_zero (fun h => h2 ((D.flip_mem_iff j k).1 h))
        (fun h => h1 ((D.flip_mem_iff' j k).1 h)), neg_zero]

/-- `ς_{kk} = 0`. -/
theorem sgn_self (k : D.cut.Half) : D.sgn k k = 0 := by
  have := D.sgn_antisymm k k
  omega

/-- `(j, k) ∈ E_×` iff `(k, j) ∈ E_×`. -/
theorem mem_crossPairs_swap (j k : D.cut.Half) :
    (j, k) ∈ D.crossPairs ↔ (k, j) ∈ D.crossPairs := by
  simp only [crossPairs, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [D.sgn_antisymm j k]
  omega

/-- `#{k : ς_{jk} ≠ 0} = r_j`. -/
theorem card_sgn_ne_zero (j : D.cut.Half) :
    (Finset.univ.filter (fun k => D.sgn j k ≠ 0)).card = D.rdeg j := by
  unfold rdeg Nset
  congr 1
  ext k
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [D.sgn_antisymm k j]
  omega

/-- The cross edges: the edges of `G` with one end in each half. -/
def crossEdges : Finset (U × U) :=
  D.G.E.filter (fun e => (e.1 ∈ D.cut.half ∧ e.2 ∉ D.cut.half) ∨
    (e.1 ∉ D.cut.half ∧ e.2 ∈ D.cut.half))

/-- The edge of `G` between `j` and `ϑk`. -/
def crossEdge (q : D.cut.Half × D.cut.Half) : U × U :=
  if (q.1.1, D.cut.flip q.2.1) ∈ D.G.E then (q.1.1, D.cut.flip q.2.1)
  else (D.cut.flip q.2.1, q.1.1)

theorem crossEdge_maps (q : D.cut.Half × D.cut.Half) (hq : q ∈ D.crossPairs) :
    D.crossEdge q ∈ D.crossEdges := by
  rw [crossPairs, Finset.mem_filter] at hq
  have hj := q.1.2
  have hk := D.cut.flip_not_mem q.2.2
  rw [crossEdges, Finset.mem_filter]
  by_cases h1 : (q.1.1, D.cut.flip q.2.1) ∈ D.G.E
  · rw [crossEdge, ite_eq_left h1]
    exact ⟨h1, Or.inl ⟨hj, hk⟩⟩
  · rw [crossEdge, ite_eq_right h1]
    have h2 : (D.cut.flip q.2.1, q.1.1) ∈ D.G.E := by
      by_contra h2
      exact hq.2 (D.sgn_eq_zero h1 h2)
    exact ⟨h2, Or.inr ⟨hk, hj⟩⟩

theorem crossEdge_inj (q q' : D.cut.Half × D.cut.Half) (hqq : D.crossEdge q = D.crossEdge q') :
    q = q' := by
  have hj := q.1.2
  have hj' := q'.1.2
  have hk := D.cut.flip_not_mem q.2.2
  have hk' := D.cut.flip_not_mem q'.2.2
  have hinj : ∀ a b : D.cut.Half, D.cut.flip a.1 = D.cut.flip b.1 → a = b := fun a b h =>
    Subtype.ext (D.cut.flip.injective h)
  unfold crossEdge at hqq
  split_ifs at hqq with h1 h2 h2
  · obtain ⟨e1, e2⟩ := Prod.mk.inj hqq
    exact Prod.ext (Subtype.ext e1) (hinj _ _ e2)
  · obtain ⟨e1, _⟩ := Prod.mk.inj hqq
    exact absurd (e1 ▸ hj) hk'
  · obtain ⟨e1, _⟩ := Prod.mk.inj hqq
    exact absurd (e1 ▸ hj') hk
  · obtain ⟨e1, e2⟩ := Prod.mk.inj hqq
    exact Prod.ext (Subtype.ext e2) (hinj _ _ e1)

theorem crossEdge_surj (e : U × U) (he : e ∈ D.crossEdges) :
    ∃ q ∈ D.crossPairs, D.crossEdge q = e := by
  rw [crossEdges, Finset.mem_filter] at he
  obtain ⟨hE, hcr⟩ := he
  rcases hcr with ⟨hu, hw⟩ | ⟨hu, hw⟩
  · have hk : D.cut.flip e.2 ∈ D.cut.half := (D.cut.crosses e.2).2 hw
    have hE' : ((⟨e.1, hu⟩ : D.cut.Half).1,
        D.cut.flip (⟨D.cut.flip e.2, hk⟩ : D.cut.Half).1) ∈ D.G.E := by
      simp only [D.cut.flip_flip]
      exact hE
    refine ⟨(⟨e.1, hu⟩, ⟨D.cut.flip e.2, hk⟩), ?_, ?_⟩
    · rw [crossPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [D.sgn_eq_one hE']
      omega
    · rw [crossEdge, ite_eq_left hE']
      simp only [D.cut.flip_flip]
  · have hk : D.cut.flip e.1 ∈ D.cut.half := (D.cut.crosses e.1).2 hu
    have hnot : (e.2, e.1) ∉ D.G.E := D.G.oriented _ _ hE
    have hE' : (D.cut.flip (⟨D.cut.flip e.1, hk⟩ : D.cut.Half).1,
        (⟨e.2, hw⟩ : D.cut.Half).1) ∈ D.G.E := by
      simp only [D.cut.flip_flip]
      exact hE
    have hnot' : ((⟨e.2, hw⟩ : D.cut.Half).1,
        D.cut.flip (⟨D.cut.flip e.1, hk⟩ : D.cut.Half).1) ∉ D.G.E := by
      simp only [D.cut.flip_flip]
      exact hnot
    refine ⟨(⟨e.2, hw⟩, ⟨D.cut.flip e.1, hk⟩), ?_, ?_⟩
    · rw [crossPairs, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [D.sgn_eq_neg_one hE']
      omega
    · rw [crossEdge, ite_eq_right hnot']
      simp only [D.cut.flip_flip]

/-- **`lem:spec:elementary`, the bijection.** `(j, k) ↦` (the edge between `j` and `ϑk`) maps
`E_×` bijectively onto the cross edges. -/
theorem crossPairs_bijOn :
    Set.BijOn D.crossEdge (D.crossPairs : Set _) (D.crossEdges : Set _) := by
  refine ⟨fun q hq => D.crossEdge_maps q (Finset.mem_coe.mp hq),
    fun q _ q' _ h => D.crossEdge_inj q q' h, fun e he => ?_⟩
  obtain ⟨q, hq, hqe⟩ := D.crossEdge_surj e (Finset.mem_coe.mp he)
  exact ⟨q, Finset.mem_coe.mpr hq, hqe⟩

/-- `m_×` is the number of cross edges. -/
theorem mcross_eq : D.mcross = D.crossEdges.card :=
  Finset.card_nbij D.crossEdge (fun q hq => D.crossEdge_maps q hq)
    D.crossPairs_bijOn.injOn D.crossPairs_bijOn.surjOn

/-- The degree of a vertex of `G`. -/
def degree (v : U) : ℕ := (Finset.univ.filter (fun w => D.Adj v w)).card

theorem sgn_ne_zero_iff (k k' : D.cut.Half) :
    D.sgn k k' ≠ 0 ↔ D.Adj k.1 (D.cut.flip k'.1) := by
  unfold Adj
  by_cases h1 : (k.1, D.cut.flip k'.1) ∈ D.G.E
  · rw [D.sgn_eq_one h1]
    exact ⟨fun _ => Or.inl h1, fun _ => by omega⟩
  · by_cases h2 : (D.cut.flip k'.1, k.1) ∈ D.G.E
    · rw [D.sgn_eq_neg_one h2]
      exact ⟨fun _ => Or.inr h2, fun _ => by omega⟩
    · rw [D.sgn_eq_zero h1 h2]
      exact ⟨fun h => absurd rfl h, fun h => h.elim h1 h2 |>.elim⟩

/-- **`lem:spec:elementary`, degrees.** A vertex `k ∈ U⁺` has degree `d_k` in `G`. -/
theorem degree_eq_dk (k : D.cut.Half) : D.degree k.1 = D.dk k := by
  unfold degree dk
  rw [← Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun w => D.Adj k.1 w)) (fun w => w ∈ D.cut.half)]
  congr 1
  · -- neighbours inside `U⁺`
    unfold deg0
    rw [Finset.filter_filter]
    refine Finset.card_bij' (fun w hw => ⟨w, (Finset.mem_filter.mp hw).2.2⟩)
      (fun j _ => j.1) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      exact (D.adj_symm).1 hw.1
    · intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨(D.adj_symm).1 hj, j.2⟩
    · intro w _
      rfl
    · intro j _
      rfl
  · -- neighbours in `U⁻`, through `ϑ`
    rw [← D.card_sgn_ne_zero k, Finset.filter_filter]
    refine Finset.card_bij'
      (fun w hw => ⟨D.cut.flip w, (D.cut.crosses w).2 (Finset.mem_filter.mp hw).2.2⟩)
      (fun k' _ => D.cut.flip k'.1) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
      rw [D.sgn_ne_zero_iff, D.cut.flip_flip]
      exact hw.1
    · intro k' hk'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
      exact ⟨(D.sgn_ne_zero_iff k k').1 hk', D.cut.flip_not_mem k'.2⟩
    · intro w _
      exact D.cut.flip_flip w
    · intro k' _
      exact Subtype.ext (D.cut.flip_flip k'.1)

/-- **`lem:spec:elementary`, degrees.** `ϑk` has the same degree as `k`. -/
theorem degree_flip (v : U) : D.degree (D.cut.flip v) = D.degree v := by
  unfold degree
  refine Finset.card_bij' (fun w _ => D.cut.flip w) (fun w _ => D.cut.flip w) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [← D.adj_flip v (D.cut.flip w), D.cut.flip_flip]
    exact hw
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    exact (D.adj_flip v w).2 hw
  · intro w _
    exact D.cut.flip_flip w
  · intro w _
    exact D.cut.flip_flip w

/-- **`lem:spec:elementary`, degrees.** `Δ` is the maximum degree of `G`. -/
theorem maxDegree_eq_Delta : Finset.univ.sup D.degree = D.Delta := by
  apply le_antisymm
  · refine Finset.sup_le (fun v _ => ?_)
    by_cases hv : v ∈ D.cut.half
    · rw [show v = (⟨v, hv⟩ : D.cut.Half).1 from rfl, D.degree_eq_dk]
      exact Finset.le_sup (f := D.dk) (Finset.mem_univ _)
    · have hf : D.cut.flip v ∈ D.cut.half := (D.cut.crosses v).2 hv
      have e : D.degree v = D.degree (D.cut.flip v) := by
        rw [← D.degree_flip (D.cut.flip v), D.cut.flip_flip]
      rw [e, show D.cut.flip v = (⟨D.cut.flip v, hf⟩ : D.cut.Half).1 from rfl, D.degree_eq_dk]
      exact Finset.le_sup (f := D.dk) (Finset.mem_univ _)
  · refine Finset.sup_le (fun k _ => ?_)
    rw [← D.degree_eq_dk]
    exact Finset.le_sup (f := D.degree) (Finset.mem_univ _)

/-- **`lem:spec:elementary`, last claim.** `ϑ` maps `G⁺` isomorphically, with orientations,
onto `G[U⁻]`. -/
theorem flip_isom (j k : D.cut.Half) :
    ((j.1, k.1) ∈ D.G.E ↔ (D.cut.flip j.1, D.cut.flip k.1) ∈ D.G.E) ∧
      D.cut.flip j.1 ∉ D.cut.half ∧ D.cut.flip k.1 ∉ D.cut.half :=
  ⟨D.aut j.1 k.1, D.cut.flip_not_mem j.2, D.cut.flip_not_mem k.2⟩

end SpecData

end Sarkozy.Cuts

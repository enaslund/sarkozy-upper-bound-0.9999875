module

public import Sarkozy.ExtractionK.Grouped
public import Sarkozy.ExtractionK.KernelBridge
public import Sarkozy.Extraction.CoverOrder

@[expose] public section

/-!
# Compressed classes, log-linear form (`cor:extraction-compressed`)

`paper/sections/16_extraction.tex`, `cor:extraction-compressed`, from `lem:matching:extractionk`
(`grouped_extraction`) and `lem:cover:order` (`exists_order_weighted_le'`).

* `cmp_sum_ordT`: `t_V = e(V) + e(V, C_x)` (`edgesIn`, `edgesBetween`) for an order in which
  `C_x` comes before `V` and the other vertices after it; so the exponent of the record is the
  order-free `ex(𝒞) = t_V + t_W + f_V + f_W` of `def:extraction:records` (`cmpEx`).
* `cmp_exists_rank`, `cmp_exists_order` (`lem:cover:order` on each of the four sets
  `C_x, U_x, C_z, U_z`, with the weights `2^{h_i}` on the cover and
  `2^{h_i + d⁰_i - |Adj(i) ∩ U_x|}` on `U_x`): block orders `cmpOrd` (cover, then the witness
  set, then the integrated set) with `∑_v 2^{s_v} ≤ oc(𝒞)` (`cmpOc`).
* `cmp_intF_le`, `cmp_coverRowF_le`: every vertex factor satisfies
  `F_v ≤ exp(2γ_cmp 2^{s_v} + r² sp_v)/(1 - e_{d⁰_v}(q, n))`, `γ_cmp = n r² + (Δ/4) r`
  (`cmpGamma`), `sp_v` (`cmpSp`); `cmp_recordFactor_le`:
  `∏_v F_v ≤ (exp(γ_cmp oc(𝒞) + r² J_sp)/∏_i (1 - e_{d⁰_i}(q, n)))²` (`cmpJsp`; each vertex of
  `U⁺` occurs at most twice among the non-witness vertices).
* `extraction_compressed_class`: **the class bound**
  `|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} Λ₀ exp(γ_cmp oc(𝒞)) ‖f‖_μ ‖h‖_μ`,
  `Λ₀ = R_full² exp(r² J_sp)/((1 - ê)^k ∏_i (1 - e_{d⁰_i}(q, n)))` (`cmpLambda0`; `k = 2` in the
  paper); `extraction_compressed_class_two`: the same over `𝔽_p` for a witness of size two with
  `c_ker = 2^{β(𝒞)} ∈ {1, 2}` (`cmp_twoCycleCount_le_one`), from `lem:matching:kernel`
  (`KernelBridge.lean`, hypothesis `FourCycleBound p` = `cor:dl:normalized`(a)).
* `extraction_compressed_buckets` (and `extraction_compressed_buckets_two`): **the bucket sum**
  over an exact partition of the nonstar subsets,
  `|∑_{S nonstar} ⟨f, T_S h⟩_μ| ≤ r^k Λ₀ ∑_𝔟 S_𝔟 exp(γ_cmp 𝔟 2^𝔮) ‖f‖_μ ‖h‖_μ`,
  `S_𝔟 = ∑_{𝒞 ↦ 𝔟} c_ker(𝒞) 2^{ex(𝒞)/2}` (the paper's `𝖺_𝔟 + 𝖻_𝔟 √2`), for buckets with
  `oc(𝒞) ≤ 𝔟 2^𝔮`.

## Conventions and deviations

* Formal setting of `Grouped.lean` (finite field `F`, `q = |F|`, `WeilBound F`, oriented half
  graph `G⁺` on `U`, signs `ς ∈ {0, ±1}` with `ς_{kj} = -ς_{jk}`, `n ≥ |U⁺|`); (S1) enters
  through `e_{d⁰_i}(q, n) ≤ ê < 1` (the paper's `ê = e_{Δ⁺}(p, n)` is such a bound) and
  `d_i = d⁰_i + |N(i)| ≤ Δ` for all `i` (`cmpDeg`).
* `J_sp` is the paper's `∑_{i,j} 2^{d_i + |Adj(i) ∩ N(j)| + |Adj(j) ∩ N(i)|}`; with the symmetric
  support it is `∑_i sp_i` (`cmp_Jsp_eq`), using `mg(j, i) = |Adj(i) ∩ N(j)|` (`cmp_rowsMg_eq`).
* The paper's statement is for `k = 2`; the general statements carry `(1 - ê)^k` in `Λ₀`.
* The bound of `grouped_extraction` has no factor `(R̃_{U_x} R̃_{U_z})^{1/2}`, so the factor
  `R_full² ≥ 1` of `Λ₀` is not needed; it is kept to match the paper.
* Not formalized: the admissibility sentence (`lem:majorant`) at the end of the corollary.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## The exponent without orders: `t_V = e(V) + e(V, C_x)` -/

section EdgeCount

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `e(L)`: the number of edges of `G⁺` inside `L`. -/
def edgesIn (G : OrientedGraph U) (L : Finset U) : ℕ :=
  (G.E.filter (fun e => e.1 ∈ L ∧ e.2 ∈ L)).card

/-- `e(L, L')`: the number of edges of `G⁺` between `L` and `L'`. -/
def edgesBetween (G : OrientedGraph U) (L L' : Finset U) : ℕ :=
  (G.E.filter (fun e => (e.1 ∈ L ∧ e.2 ∈ L') ∨ (e.1 ∈ L' ∧ e.2 ∈ L))).card

omit [Fintype U] in
theorem cmp_sum_card_in (G : OrientedGraph U) (S V : Finset U) (P : U → U → Prop)
    [DecidableRel P] :
    ∑ v ∈ V, (S.filter (fun u => (u, v) ∈ G.E ∧ P u v)).card =
      (G.E.filter (fun e => e.1 ∈ S ∧ e.2 ∈ V ∧ P e.1 e.2)).card := by
  have h : ∑ v ∈ V, (S.filter (fun u => (u, v) ∈ G.E ∧ P u v)).card =
      ((S ×ˢ V).filter (fun e => e ∈ G.E ∧ P e.1 e.2)).card := by
    rw [card_filter, sum_product_right]
    exact sum_congr rfl fun v _ => card_filter _ _
  rw [h]
  congr 1
  ext e
  simp only [mem_filter, mem_product]
  tauto

omit [Fintype U] in
theorem cmp_sum_card_out (G : OrientedGraph U) (S V : Finset U) (P : U → U → Prop)
    [DecidableRel P] :
    ∑ v ∈ V, (S.filter (fun u => (v, u) ∈ G.E ∧ P u v)).card =
      (G.E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ S ∧ P e.2 e.1)).card := by
  have h : ∑ v ∈ V, (S.filter (fun u => (v, u) ∈ G.E ∧ P u v)).card =
      ((V ×ˢ S).filter (fun e => e ∈ G.E ∧ P e.2 e.1)).card := by
    rw [card_filter, sum_product]
    exact sum_congr rfl fun v _ => card_filter _ _
  rw [h]
  congr 1
  ext e
  simp only [mem_filter, mem_product]
  tauto

omit [Fintype U] in
/-- The neighbours of `v` in `S`, split by the orientation of the edge. -/
theorem cmp_nbrCount_split (G : OrientedGraph U) (S : Finset U) (v : U) (P : U → Prop)
    [DecidablePred P] :
    (S.filter (fun u => P u ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E))).card =
      (S.filter (fun u => (u, v) ∈ G.E ∧ P u)).card +
        (S.filter (fun u => (v, u) ∈ G.E ∧ P u)).card := by
  rw [← card_union_of_disjoint]
  · congr 1
    ext u
    simp only [mem_filter, mem_union]
    tauto
  · rw [disjoint_left]
    intro u hu hu'
    exact G.oriented u v (mem_filter.mp hu).2.1 (mem_filter.mp hu').2.1

/-- **`t_V = e(V) + e(V, C_x)`** (`def:extraction:records`): for an injective order in which `C_x`
comes before `V` and every other vertex after `V`, the vertices of `V` have together
`e(V) + e(V, C_x)` earlier neighbours. -/
theorem cmp_sum_ordT (G : OrientedGraph U) (V Cx : Finset U) (ord : U → ℕ)
    (hord : Function.Injective ord) (hVC : ∀ u ∈ V, u ∉ Cx)
    (h1 : ∀ a ∈ Cx, ∀ v ∈ V, ord a < ord v)
    (h2 : ∀ w, w ∉ V → w ∉ Cx → ∀ v ∈ V, ord v < ord w) :
    ∑ v ∈ V, ordT G ord v = edgesIn G V + edgesBetween G V Cx := by
  -- the earlier neighbours of `v ∈ V` lie in `C_x` or earlier in `V`
  have hT : ∀ v ∈ V, ordT G ord v =
      (Cx.filter (fun u => True ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E))).card +
        (V.filter (fun u => ord u < ord v ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E))).card := by
    intro v hv
    unfold ordT coverRowT nbrCount coverRowEarlier
    rw [← card_union_of_disjoint]
    · congr 1
      ext u
      simp only [mem_filter, mem_univ, true_and, mem_union]
      constructor
      · rintro ⟨hlt, hadj⟩
        by_cases huC : u ∈ Cx
        · exact Or.inl ⟨huC, hadj⟩
        · by_cases huV : u ∈ V
          · exact Or.inr ⟨huV, hlt, hadj⟩
          · exact absurd (h2 u huV huC v hv) (by omega)
      · rintro (⟨huC, hadj⟩ | ⟨_, hlt, hadj⟩)
        · exact ⟨h1 u huC v hv, hadj⟩
        · exact ⟨hlt, hadj⟩
    · rw [disjoint_left]
      intro u hu hu'
      exact hVC u (mem_filter.mp hu').1 (mem_filter.mp hu).1
  rw [sum_congr rfl hT, sum_add_distrib]
  simp only [cmp_nbrCount_split]
  rw [sum_add_distrib, sum_add_distrib]
  rw [cmp_sum_card_in G Cx V (fun _ _ => True), cmp_sum_card_out G Cx V (fun _ _ => True),
    cmp_sum_card_in G V V (fun u v => ord u < ord v),
    cmp_sum_card_out G V V (fun u v => ord u < ord v)]
  -- the edges between `V` and `C_x`
  have hB : edgesBetween G V Cx = (G.E.filter (fun e => e.1 ∈ Cx ∧ e.2 ∈ V ∧ True)).card +
      (G.E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ Cx ∧ True)).card := by
    unfold edgesBetween
    rw [← card_union_of_disjoint]
    · congr 1
      ext e
      simp only [mem_filter, mem_union, and_true]
      tauto
    · rw [disjoint_left]
      intro e he he'
      exact hVC e.2 (mem_filter.mp he).2.2.1 (mem_filter.mp he').2.2.1
  -- the edges inside `V`
  have hI : edgesIn G V = (G.E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ V ∧ ord e.1 < ord e.2)).card +
      (G.E.filter (fun e => e.1 ∈ V ∧ e.2 ∈ V ∧ ord e.2 < ord e.1)).card := by
    unfold edgesIn
    rw [← card_union_of_disjoint]
    · congr 1
      ext e
      simp only [mem_filter, mem_union]
      constructor
      · rintro ⟨he, h1', h2'⟩
        have hne : e.1 ≠ e.2 := by
          intro h
          have he' : (e.1, e.1) ∈ G.E := by
            have hee : (e.1, e.1) = e := Prod.ext rfl h
            rw [hee]
            exact he
          exact G.loopless e.1 he'
        have hne' : ord e.1 ≠ ord e.2 := fun h => hne (hord h)
        rcases lt_or_gt_of_ne hne' with h | h
        · exact Or.inl ⟨he, h1', h2', h⟩
        · exact Or.inr ⟨he, h1', h2', h⟩
      · rintro (⟨he, h1', h2', -⟩ | ⟨he, h1', h2', -⟩)
        · exact ⟨he, h1', h2'⟩
        · exact ⟨he, h1', h2'⟩
    · rw [disjoint_left]
      intro e he he'
      have := (mem_filter.mp he).2.2.2
      have := (mem_filter.mp he').2.2.2
      omega
  rw [hB, hI]
  ring

end EdgeCount

/-! ## Orders from `lem:cover:order` -/

section Orders

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The graph `G⁺[S]` induced on `S`, as a simple graph on the subtype `S`. -/
def cmpInduced (G : OrientedGraph U) (S : Finset U) : SimpleGraph S :=
  SimpleGraph.fromRel (fun a b : S => (a.1, b.1) ∈ G.E)

instance (G : OrientedGraph U) (S : Finset U) : DecidableRel (cmpInduced G S).Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromRel (fun a b : S => (a.1, b.1) ∈ G.E)).Adj)

omit [Fintype U] [DecidableEq U] in
theorem cmp_adj_ne {G : OrientedGraph U} {u v : U} (h : (u, v) ∈ G.E ∨ (v, u) ∈ G.E) :
    u ≠ v := by
  rintro rfl
  rcases h with h | h <;> exact G.loopless u h

/-- **`lem:cover:order` on a vertex set `S`**: for any weights `ω`, some ranking `rk` of `S`
(injective on `S`, with values below `|U| + 1`) has
`∑_{v ∈ S} ω_v 2^{t_v} ≤ ∑_{v ∈ S} ω_v av(g_v)`, `t_v` the number of neighbours of `v` in `S`
of smaller rank and `g_v = |Adj(v) ∩ S|`. -/
theorem cmp_exists_rank (G : OrientedGraph U) (S : Finset U) (ω : U → ℝ) :
    ∃ rk : U → ℕ, Set.InjOn rk S ∧ (∀ u, rk u < Fintype.card U + 1) ∧
      ∑ v ∈ S, ω v * 2 ^ nbrCount G (S.filter (fun w => rk w < rk v)) v ≤
        ∑ v ∈ S, ω v * av (nbrCount G S v) := by
  classical
  obtain ⟨σ, hσ⟩ := exists_order_weighted_le' (cmpInduced G S) (fun a => ω a.1)
  let rk : U → ℕ := fun u => if h : u ∈ S then (σ ⟨u, h⟩ : ℕ) else 0
  have hrk : ∀ a : S, rk a.1 = (σ a : ℕ) := fun a => by simp [rk, a.2]
  refine ⟨rk, ?_, ?_, ?_⟩
  · intro a ha b hb hab
    have h1 := hrk ⟨a, ha⟩
    have h2 := hrk ⟨b, hb⟩
    have : σ ⟨a, ha⟩ = σ ⟨b, hb⟩ := Fin.ext (by rw [← h1, ← h2]; exact hab)
    exact congrArg Subtype.val (σ.injective this)
  · intro u
    by_cases h : u ∈ S
    · have h1 : (σ ⟨u, h⟩ : ℕ) < Fintype.card S := (σ ⟨u, h⟩).2
      have h2 : Fintype.card S ≤ Fintype.card U := Fintype.card_subtype_le _
      simp only [rk, h, ↓reduceDIte]
      omega
    · simp [rk, h]
  · have hE : ∀ v : S, earlier (cmpInduced G S) σ v =
        nbrCount G (S.filter (fun w => rk w < rk v.1)) v.1 := by
      intro v
      unfold earlier nbrCount
      rw [card_filter, filter_filter, card_filter]
      rw [← sum_coe_sort S (fun w => if rk w < rk v.1 ∧
        ((w, v.1) ∈ G.E ∨ (v.1, w) ∈ G.E) then 1 else 0)]
      refine sum_congr rfl fun i _ => ?_
      have hiff : ((cmpInduced G S).Adj i v ∧ σ i < σ v) ↔
          (rk i.1 < rk v.1 ∧ ((i.1, v.1) ∈ G.E ∨ (v.1, i.1) ∈ G.E)) := by
        rw [hrk i, hrk v]
        simp only [cmpInduced, SimpleGraph.fromRel_adj, Fin.lt_def]
        constructor
        · rintro ⟨⟨_, h⟩, hlt⟩
          exact ⟨hlt, h⟩
        · rintro ⟨hlt, h⟩
          exact ⟨⟨fun he => by rw [he] at hlt; exact lt_irrefl _ hlt, h⟩, hlt⟩
      simp only [hiff]
    have hD : ∀ v : S, (cmpInduced G S).degree v = nbrCount G S v.1 := by
      intro v
      rw [← SimpleGraph.card_neighborFinset_eq_degree, SimpleGraph.neighborFinset_eq_filter]
      unfold nbrCount
      rw [card_filter, card_filter]
      rw [← sum_coe_sort S (fun w => if ((w, v.1) ∈ G.E ∨ (v.1, w) ∈ G.E) then 1 else 0)]
      refine sum_congr rfl fun i _ => ?_
      have hiff : (cmpInduced G S).Adj v i ↔ ((i.1, v.1) ∈ G.E ∨ (v.1, i.1) ∈ G.E) := by
        simp only [cmpInduced, SimpleGraph.fromRel_adj]
        constructor
        · rintro ⟨_, h⟩
          exact h.symm
        · intro h
          refine ⟨fun he => ?_, h.symm⟩
          rw [he] at h
          exact cmp_adj_ne h rfl
      simp only [hiff]
    have h1 : ∑ v : S, ω v.1 * 2 ^ earlier (cmpInduced G S) σ v =
        ∑ v ∈ S, ω v * 2 ^ nbrCount G (S.filter (fun w => rk w < rk v)) v := by
      rw [← sum_coe_sort S (fun v => ω v * 2 ^ nbrCount G (S.filter (fun w => rk w < rk v)) v)]
      exact sum_congr rfl fun v _ => by rw [hE v]
    have h2 : ∑ v : S, ω v.1 * av ((cmpInduced G S).degree v) =
        ∑ v ∈ S, ω v * av (nbrCount G S v) := by
      rw [← sum_coe_sort S (fun v => ω v * av (nbrCount G S v))]
      exact sum_congr rfl fun v _ => by rw [hD v]
    rw [← h1, ← h2]
    exact hσ

/-- The block order of a copy of `U⁺`: `C` (ranked by `rkC`), then `V` (by `rkV`), then the
integrated vertices (by `rkU`). -/
def cmpOrd (C V : Finset U) (rkC rkV rkU : U → ℕ) (u : U) : ℕ :=
  if u ∈ C then rkC u else if u ∈ V then (Fintype.card U + 1) + rkV u
  else 2 * (Fintype.card U + 1) + rkU u

theorem cmp_nbrCount_compl (G : OrientedGraph U) (S : Finset U) (u : U) :
    nbrCount G (univ \ S) u = rowsDeg0 G u - nbrCount G S u := by
  have h : nbrCount G (univ \ S) u + nbrCount G S u = rowsDeg0 G u := by
    unfold nbrCount rowsDeg0 rowsAdj
    rw [← card_union_of_disjoint]
    · congr 1
      ext w
      simp only [mem_union, mem_filter, mem_sdiff, mem_univ, true_and]
      tauto
    · rw [disjoint_left]
      intro w hw hw'
      exact (mem_sdiff.mp (mem_filter.mp hw).1).2 (mem_filter.mp hw').1
  omega

section BlockOrder

variable {C V : Finset U} {rkC rkV rkU : U → ℕ}

theorem cmpOrd_of_mem_C {u : U} (hu : u ∈ C) : cmpOrd C V rkC rkV rkU u = rkC u := by
  simp [cmpOrd, hu]

theorem cmpOrd_of_mem_V (hVC : ∀ u ∈ V, u ∉ C) {u : U} (hu : u ∈ V) :
    cmpOrd C V rkC rkV rkU u = (Fintype.card U + 1) + rkV u := by
  simp [cmpOrd, hu, hVC u hu]

theorem cmpOrd_of_mem_U {u : U} (hu : u ∈ univ \ (V ∪ C)) :
    cmpOrd C V rkC rkV rkU u = 2 * (Fintype.card U + 1) + rkU u := by
  simp only [mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu
  simp [cmpOrd, hu.1, hu.2]

theorem cmp_mem_cases (u : U) : u ∈ C ∨ u ∈ V ∨ u ∈ univ \ (V ∪ C) := by
  by_cases h1 : u ∈ C
  · exact Or.inl h1
  · by_cases h2 : u ∈ V
    · exact Or.inr (Or.inl h2)
    · refine Or.inr (Or.inr ?_)
      simp [h1, h2]

theorem cmpOrd_injective (hVC : ∀ u ∈ V, u ∉ C) (hC : ∀ u, rkC u < Fintype.card U + 1)
    (hV : ∀ u, rkV u < Fintype.card U + 1) (hU : ∀ u, rkU u < Fintype.card U + 1)
    (hiC : Set.InjOn rkC C) (hiV : Set.InjOn rkV V)
    (hiU : Set.InjOn rkU ((univ \ (V ∪ C) : Finset U) : Set U)) :
    Function.Injective (cmpOrd C V rkC rkV rkU) := by
  intro a b hab
  have hCa := hC a
  have hCb := hC b
  have hVa := hV a
  have hVb := hV b
  have hUa := hU a
  have hUb := hU b
  rcases cmp_mem_cases (C := C) (V := V) a with ha | ha | ha <;>
    rcases cmp_mem_cases (C := C) (V := V) b with hb | hb | hb
  · rw [cmpOrd_of_mem_C ha, cmpOrd_of_mem_C hb] at hab
    exact hiC ha hb hab
  · rw [cmpOrd_of_mem_C ha, cmpOrd_of_mem_V hVC hb] at hab
    omega
  · rw [cmpOrd_of_mem_C ha, cmpOrd_of_mem_U hb] at hab
    omega
  · rw [cmpOrd_of_mem_V hVC ha, cmpOrd_of_mem_C hb] at hab
    omega
  · rw [cmpOrd_of_mem_V hVC ha, cmpOrd_of_mem_V hVC hb] at hab
    exact hiV ha hb (by omega)
  · rw [cmpOrd_of_mem_V hVC ha, cmpOrd_of_mem_U hb] at hab
    omega
  · rw [cmpOrd_of_mem_U ha, cmpOrd_of_mem_C hb] at hab
    omega
  · rw [cmpOrd_of_mem_U ha, cmpOrd_of_mem_V hVC hb] at hab
    omega
  · rw [cmpOrd_of_mem_U ha, cmpOrd_of_mem_U hb] at hab
    exact hiU ha hb (by omega)

/-- The cover comes first. -/
theorem cmpOrd_C_lt (hVC : ∀ u ∈ V, u ∉ C) (hC : ∀ u, rkC u < Fintype.card U + 1) :
    ∀ a ∈ C, ∀ b, b ∉ C → cmpOrd C V rkC rkV rkU a < cmpOrd C V rkC rkV rkU b := by
  intro a ha b hb
  have := hC a
  rw [cmpOrd_of_mem_C ha]
  rcases cmp_mem_cases (C := C) (V := V) b with hb' | hb' | hb'
  · exact absurd hb' hb
  · rw [cmpOrd_of_mem_V hVC hb']
    omega
  · rw [cmpOrd_of_mem_U hb']
    omega

/-- The integrated vertices come last. -/
theorem cmpOrd_lt_U (hVC : ∀ u ∈ V, u ∉ C) (hC : ∀ u, rkC u < Fintype.card U + 1)
    (hV : ∀ u, rkV u < Fintype.card U + 1) : ∀ a, a ∉ univ \ (V ∪ C) → ∀ b ∈ univ \ (V ∪ C),
    cmpOrd C V rkC rkV rkU a < cmpOrd C V rkC rkV rkU b := by
  intro a ha b hb
  have := hC a
  have := hV a
  rw [cmpOrd_of_mem_U hb]
  rcases cmp_mem_cases (C := C) (V := V) a with ha' | ha' | ha'
  · rw [cmpOrd_of_mem_C ha']
    omega
  · rw [cmpOrd_of_mem_V hVC ha']
    omega
  · exact absurd ha' ha

/-- `V` comes before the integrated vertices. -/
theorem cmpOrd_V_lt (hVC : ∀ u ∈ V, u ∉ C) (hC : ∀ u, rkC u < Fintype.card U + 1)
    (hV : ∀ u, rkV u < Fintype.card U + 1) : ∀ w, w ∉ V → w ∉ C → ∀ v ∈ V,
    cmpOrd C V rkC rkV rkU v < cmpOrd C V rkC rkV rkU w := by
  intro w hw1 hw2 v hv
  have hwU : w ∈ univ \ (V ∪ C) := by simp [hw1, hw2]
  have hvU : v ∉ univ \ (V ∪ C) := by simp [hv]
  exact cmpOrd_lt_U hVC hC hV v hvU w hwU

/-- `t_a` of a cover vertex: its neighbours of smaller rank in `C`. -/
theorem cmp_coverRowT_eq (G : OrientedGraph U) {a : U} (ha : a ∈ C) :
    coverRowT G C (cmpOrd C V rkC rkV rkU) a =
      nbrCount G (C.filter (fun w => rkC w < rkC a)) a := by
  unfold coverRowT coverRowEarlier
  congr 1
  refine filter_congr fun w hw => ?_
  rw [cmpOrd_of_mem_C hw, cmpOrd_of_mem_C ha]

/-- `t_u` of an integrated vertex: its `d⁰_u - |Adj(u) ∩ U_x|` neighbours outside `U_x` and its
neighbours of smaller rank in `U_x`. -/
theorem cmp_ordT_U (hVC : ∀ u ∈ V, u ∉ C) (hC : ∀ u, rkC u < Fintype.card U + 1)
    (hV : ∀ u, rkV u < Fintype.card U + 1) (G : OrientedGraph U) {u : U}
    (hu : u ∈ univ \ (V ∪ C)) :
    ordT G (cmpOrd C V rkC rkV rkU) u = (rowsDeg0 G u - nbrCount G (univ \ (V ∪ C)) u) +
      nbrCount G ((univ \ (V ∪ C)).filter (fun w => rkU w < rkU u)) u := by
  rw [← cmp_nbrCount_compl G]
  unfold ordT coverRowT coverRowEarlier nbrCount
  rw [← card_union_of_disjoint]
  · congr 1
    ext w
    have hord : cmpOrd C V rkC rkV rkU w < cmpOrd C V rkC rkV rkU u ↔
        (w ∉ univ \ (V ∪ C) ∨ (w ∈ univ \ (V ∪ C) ∧ rkU w < rkU u)) := by
      constructor
      · intro hlt
        by_cases hw : w ∈ univ \ (V ∪ C)
        · rw [cmpOrd_of_mem_U hw, cmpOrd_of_mem_U hu] at hlt
          exact Or.inr ⟨hw, by omega⟩
        · exact Or.inl hw
      · rintro (hw | ⟨hw, hlt⟩)
        · exact cmpOrd_lt_U hVC hC hV w hw u hu
        · rw [cmpOrd_of_mem_U hw, cmpOrd_of_mem_U hu]
          omega
    have hcompl : w ∈ univ \ (univ \ (V ∪ C)) ↔ w ∉ univ \ (V ∪ C) := by
      simp only [mem_sdiff, mem_univ, true_and]
    simp only [mem_filter, mem_univ, true_and, mem_union]
    rw [hord, hcompl]
    tauto
  · rw [disjoint_left]
    intro w hw hw'
    have h1 := (mem_filter.mp hw).1
    have h2 := (mem_filter.mp (mem_filter.mp hw').1).1
    exact (mem_sdiff.mp h1).2 h2

end BlockOrder

end Orders

/-! ## The vertex factors in exponential form -/

section Factors

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `γ_cmp = n r² + (Δ/4) r`, `r = q^{-1/2}`. -/
noncomputable def cmpGamma (q : ℝ) (n Δ : ℕ) : ℝ :=
  (n : ℝ) * (Real.sqrt q)⁻¹ ^ 2 + (Δ : ℝ) / 4 * (Real.sqrt q)⁻¹

/-- `d_i = d⁰_i + r_i`, `r_i = |N(i)|`. -/
def cmpDeg (G : OrientedGraph U) (ς : U → U → ℤ) (i : U) : ℕ := rowsDeg0 G i + (rowsN ς i).card

/-- `sp_v = ∑_{j ∈ U⁺} 2^{d_v + mg(j,v) + c^U(j,v)}`. -/
noncomputable def cmpSp (G : OrientedGraph U) (ς : U → U → ℤ) (v : U) : ℝ :=
  ∑ j, (2 : ℝ) ^ (cmpDeg G ς v + rowsMg G ς j v + rowsCU G ς j v)

/-- `J_sp = ∑_{i,j ∈ U⁺} 2^{d_i + |Adj(i) ∩ N(j)| + |Adj(j) ∩ N(i)|}`. -/
noncomputable def cmpJsp (G : OrientedGraph U) (ς : U → U → ℤ) : ℝ :=
  ∑ i, ∑ j, (2 : ℝ) ^ (cmpDeg G ς i + rowsCU G ς i j + rowsCU G ς j i)

/-- With a symmetric support, `mg(j, i) = |Adj(i) ∩ N(j)| = c^U(i, j)`. -/
theorem cmp_rowsMg_eq (G : OrientedGraph U) (ς : U → U → ℤ)
    (hsym : ∀ a b, ς a b ≠ 0 ↔ ς b a ≠ 0) (j i : U) : rowsMg G ς j i = rowsCU G ς i j := by
  unfold rowsMg rowsCU rowsN
  congr 1
  refine filter_congr fun i' _ => ?_
  simp only [mem_filter, mem_univ, true_and]
  exact hsym j i'

theorem cmp_Jsp_eq (G : OrientedGraph U) (ς : U → U → ℤ)
    (hsym : ∀ a b, ς a b ≠ 0 ↔ ς b a ≠ 0) : cmpJsp G ς = ∑ i, cmpSp G ς i := by
  unfold cmpJsp cmpSp
  refine sum_congr rfl fun i _ => sum_congr rfl fun j _ => ?_
  rw [cmp_rowsMg_eq G ς hsym j i]

theorem cmpSp_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (v : U) : 0 ≤ cmpSp G ς v :=
  sum_nonneg fun _ _ => by positivity

/-- `e_s(q, 2n) ≤ 2^s · 2γ_cmp` for `s ≤ Δ` (`h_s ≤ s/2`, `it:et:mono`). -/
theorem cmp_coarseError_le {q : ℝ} (n Δ : ℕ) {s : ℕ} (hs : s ≤ Δ) :
    coarseError s q (2 * n) ≤ 2 ^ s * (2 * cmpGamma q n Δ) := by
  unfold coarseError cmpGamma coarseH
  have hr : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h1 : (2 : ℝ)⁻¹ ^ s ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : (s : ℝ) ≤ Δ := by exact_mod_cast hs
  have h3 : ((s : ℝ) / 2 - 1 + (2 : ℝ)⁻¹ ^ s) * (Real.sqrt q)⁻¹ ≤ (Δ : ℝ) / 2 * (Real.sqrt q)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hr
  have h4 : (0 : ℝ) < 2 ^ s := by positivity
  nlinarith [h3, h4]

/-- **The vertex factor of an integrated vertex in exponential form**
(`cor:extraction-compressed`): `F_u ≤ exp(2γ_cmp 2^{s_u} + r² sp_u)/(1 - e_{d⁰_u}(q, n))`. -/
theorem cmp_intF_le (G : OrientedGraph U) (ς : U → U → ℤ)
    (hsym : ∀ a b, ς a b ≠ 0 ↔ ς b a ≠ 0) {q : ℝ} (n Δ : ℕ)
    (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (ord : U → ℕ) (Fr : Finset (U × U)) (Cz : Finset U) (u : U)
    (hH : (intH Fr u).card ≤ (rowsN ς u).card) (he : coarseError (rowsDeg0 G u) q n < 1) :
    intF G ς q n ord Fr Cz u ≤
      Real.exp (2 * cmpGamma q n Δ * 2 ^ intS G ord Fr u + (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς u) /
        (1 - coarseError (rowsDeg0 G u) q n) := by
  unfold intF intNum
  set s := intS G ord Fr u with hsdef
  have hs : s ≤ cmpDeg G ς u := by
    have := ordT_le_deg G ord u
    simp only [hsdef, intS, cmpDeg]
    omega
  have hsΔ : s ≤ Δ := hs.trans (hΔ u)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : coarseError s q n ≤ 2 ^ s * (2 * cmpGamma q n Δ) :=
    (coverRow_coarseError_mono_n s (by linarith : (n : ℝ) ≤ 2 * n)).trans
      (cmp_coarseError_le n Δ hsΔ)
  have h2 : (2 : ℝ) ^ s * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b ≤ cmpSp G ς u := by
    rw [mul_sum]
    refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg (subset_univ Cz)
      fun _ _ _ => by positivity)
    refine sum_le_sum fun b _ => ?_
    have hexp : intExp G ς Fr u b ≤ ((rowsMg G ς b u : ℕ) : ℤ) := by
      unfold intExp
      rw [← cmp_rowsMg_eq G ς hsym b u]
      split_ifs <;> omega
    have e1 : (2 : ℝ) ^ intExp G ς Fr u b ≤ 2 ^ rowsMg G ς b u := by
      rw [← zpow_natCast]
      exact zpow_le_zpow_right₀ (by norm_num) hexp
    have e2 : (2 : ℝ) ^ s ≤ 2 ^ cmpDeg G ς u := pow_le_pow_right₀ (by norm_num) hs
    have e3 : (1 : ℝ) ≤ 2 ^ rowsCU G ς b u := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) ^ s * (2 : ℝ) ^ intExp G ς Fr u b
        ≤ 2 ^ cmpDeg G ς u * 2 ^ rowsMg G ς b u :=
          mul_le_mul e2 e1 (by positivity) (by positivity)
      _ ≤ 2 ^ cmpDeg G ς u * 2 ^ rowsMg G ς b u * 2 ^ rowsCU G ς b u :=
          le_mul_of_one_le_right (by positivity) e3
      _ = _ := by rw [← pow_add, ← pow_add]
  have hr2 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 := sq_nonneg _
  have hnum : 1 + coarseError s q n +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b ≤
      Real.exp (2 * cmpGamma q n Δ * 2 ^ s + (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς u) := by
    have h3 : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b ≤
        (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς u := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hr2
    have h4 := Real.add_one_le_exp (2 * cmpGamma q n Δ * 2 ^ s + (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς u)
    nlinarith [h1, h3, h4]
  have hnum0 : 0 ≤ 1 + coarseError s q n +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b := by
    have := coarseError_nonneg (q := q) hn0 s
    have : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b :=
      mul_nonneg (by positivity) (sum_nonneg fun _ _ => by positivity)
    linarith
  have hden : coarseError (ordT G ord u) q n ≤ coarseError (rowsDeg0 G u) q n :=
    coarseError_mono hn0 (ordT_le_deg G ord u)
  have hden0 : 0 < 1 - coarseError (rowsDeg0 G u) q n := by linarith
  exact div_le_div₀ (Real.exp_pos _).le hnum hden0 (by linarith)

/-- **The vertex factor of a cover vertex in exponential form** (`cor:extraction-compressed`):
`F_b ≤ exp(2γ_cmp 2^{s_b} + r² sp_b)/(1 - e_{d⁰_b}(q, n))`. -/
theorem cmp_coverRowF_le (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n Δ : ℕ)
    (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (b : U)
    (hH : (coverRowH H b).card ≤ (rowsN ς b).card) (he : coarseError (rowsDeg0 G b) q n < 1) :
    coverRowF G ς q n C ord H b ≤
      Real.exp (2 * cmpGamma q n Δ * 2 ^ coverRowS G C ord H b +
        (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς b) / (1 - coarseError (rowsDeg0 G b) q n) := by
  unfold coverRowF
  set s := coverRowS G C ord H b with hsdef
  have hs : s ≤ cmpDeg G ς b := by
    have := coverRow_nbrCount_le G (coverRowEarlier C ord b) b
    simp only [hsdef, coverRowS, coverRowT, cmpDeg]
    omega
  have hsΔ : s ≤ Δ := hs.trans (hΔ b)
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : coarseError s q (2 * n) ≤ 2 ^ s * (2 * cmpGamma q n Δ) :=
    cmp_coarseError_le n Δ hsΔ
  have h2 : (2 : ℝ) ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤ cmpSp G ς b := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have hexp : coverRowExp G ς H j b ≤ ((rowsMg G ς j b + rowsCU G ς j b : ℕ) : ℤ) := by
      unfold coverRowExp
      split_ifs <;> omega
    have e1 : (2 : ℝ) ^ coverRowExp G ς H j b ≤ 2 ^ (rowsMg G ς j b + rowsCU G ς j b) := by
      rw [← zpow_natCast]
      exact zpow_le_zpow_right₀ (by norm_num) hexp
    have e2 : (2 : ℝ) ^ s ≤ 2 ^ cmpDeg G ς b := pow_le_pow_right₀ (by norm_num) hs
    calc (2 : ℝ) ^ s * (2 : ℝ) ^ coverRowExp G ς H j b
        ≤ 2 ^ cmpDeg G ς b * 2 ^ (rowsMg G ς j b + rowsCU G ς j b) :=
          mul_le_mul e2 e1 (by positivity) (by positivity)
      _ = _ := by rw [← pow_add, add_assoc]
  have hr2 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 := sq_nonneg _
  have hnum : 1 + coarseError s q (2 * n) +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤
      Real.exp (2 * cmpGamma q n Δ * 2 ^ s + (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς b) := by
    have h3 : (Real.sqrt q)⁻¹ ^ 2 * 2 ^ s * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b ≤
        (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς b := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_left h2 hr2
    have h4 := Real.add_one_le_exp (2 * cmpGamma q n Δ * 2 ^ s + (Real.sqrt q)⁻¹ ^ 2 * cmpSp G ς b)
    nlinarith [h1, h3, h4]
  have hden : coarseError (coverRowT G C ord b) q n ≤ coarseError (rowsDeg0 G b) q n :=
    coarseError_mono hn0 (coverRow_nbrCount_le G _ b)
  have hden0 : 0 < 1 - coarseError (rowsDeg0 G b) q n := by linarith
  exact div_le_div₀ (Real.exp_pos _).le hnum hden0 (by linarith)

end Factors

/-! ## Free degrees, `oc(𝒞)` and the orders -/

section Occupancy

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The number of free pairs `(i, b)` at an `x`-vertex `i`. -/
def cmpHx (Fr : Finset (U × U)) (i : U) : ℕ := (univ.filter (fun b => (i, b) ∈ Fr)).card

/-- The number of free pairs `(a, i)` at an `x'`-vertex `i`. -/
def cmpHz (Fr : Finset (U × U)) (i : U) : ℕ := (univ.filter (fun a => (a, i) ∈ Fr)).card

theorem cmp_intH_card (Fr : Finset (U × U)) (u : U) : (intH Fr u).card = cmpHx Fr u := rfl

theorem cmp_intH_swap_card (Fr : Finset (U × U)) (u : U) :
    (intH (Fr.image Prod.swap) u).card = cmpHz Fr u := by
  unfold intH cmpHz
  congr 1
  refine filter_congr fun a _ => ?_
  constructor
  · intro h
    obtain ⟨e, he, hee⟩ := mem_image.mp h
    have : e = (a, u) := by
      rw [← Prod.swap_swap e, hee]
      rfl
    rw [← this]
    exact he
  · intro h
    exact mem_image.mpr ⟨(a, u), h, rfl⟩

theorem cmp_coverRowH_card (Fr : Finset (U × U)) (Cz : Finset U) {b : U} (hb : b ∈ Cz) :
    (coverRowH (Fr.filter (fun e => e.2 ∈ Cz)) b).card = cmpHz Fr b := by
  unfold coverRowH cmpHz
  congr 1
  refine filter_congr fun a _ => ?_
  rw [mem_filter]
  exact ⟨fun h => h.1, fun h => ⟨h, hb⟩⟩

theorem cmp_coverRowH_swap_card (Fr : Finset (U × U)) (Cx : Finset U) {a : U} (ha : a ∈ Cx) :
    (coverRowH ((Fr.image Prod.swap).filter (fun e => e.2 ∈ Cx)) a).card = cmpHx Fr a := by
  unfold coverRowH cmpHx
  congr 1
  refine filter_congr fun b _ => ?_
  rw [mem_filter]
  constructor
  · rintro ⟨h, -⟩
    obtain ⟨e, he, hee⟩ := mem_image.mp h
    have : e = (a, b) := by
      rw [← Prod.swap_swap e, hee]
      rfl
    rw [← this]
    exact he
  · intro h
    exact ⟨mem_image.mpr ⟨(a, b), h, rfl⟩, ha⟩

/-- `oc(𝒞)` of `cor:extraction-compressed`: with `U_x = U⁺ \ (V ∪ C_x)`, `U_z = U⁺ \ (W ∪ C_z)`
and `h_i` the number of free pairs at `i`,
`∑_{C_x} 2^{h_i} av(|Adj(i) ∩ C_x|) + ∑_{U_x} 2^{h_i + d⁰_i - |Adj(i) ∩ U_x|} av(|Adj(i) ∩ U_x|)`
plus the same two sums for `C_z`, `U_z`. -/
noncomputable def cmpOc (G : OrientedGraph U) (Fr : Finset (U × U)) (V W Cx Cz : Finset U) :
    ℝ :=
  ∑ i ∈ Cx, (2 : ℝ) ^ cmpHx Fr i * av (nbrCount G Cx i) +
    ∑ i ∈ univ \ (V ∪ Cx), (2 : ℝ) ^ (cmpHx Fr i +
      (rowsDeg0 G i - nbrCount G (univ \ (V ∪ Cx)) i)) * av (nbrCount G (univ \ (V ∪ Cx)) i) +
    ∑ i ∈ Cz, (2 : ℝ) ^ cmpHz Fr i * av (nbrCount G Cz i) +
    ∑ i ∈ univ \ (W ∪ Cz), (2 : ℝ) ^ (cmpHz Fr i +
      (rowsDeg0 G i - nbrCount G (univ \ (W ∪ Cz)) i)) * av (nbrCount G (univ \ (W ∪ Cz)) i)

/-- The exponent `ex(𝒞) = t_V + t_W + f_V + f_W` with `t_V = e(V) + e(V, C_x)`,
`t_W = e(W) + e(W, C_z)` (`def:extraction:records`), independent of the orders. -/
def cmpEx (G : OrientedGraph U) (Fr : Finset (U × U)) (V W Cx Cz : Finset U) : ℕ :=
  (Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
    (edgesIn G V + edgesBetween G V Cx) + (edgesIn G W + edgesBetween G W Cz)

/-- **The orders of `cor:extraction-compressed`** (by `lem:cover:order`): for the cover `C`, the
witness set `V` and the integrated set `U' = U⁺ \ (V ∪ C)` of one copy and any free degrees
`hh`, there is an injective order (`C`, then `V`, then `U'`) with
`∑_{a ∈ C} 2^{t_a + h_a} + ∑_{u ∈ U'} 2^{t_u + h_u} ≤
∑_{C} 2^{h_i} av(|Adj(i) ∩ C|) + ∑_{U'} 2^{h_i + d⁰_i - |Adj(i) ∩ U'|} av(|Adj(i) ∩ U'|)`. -/
theorem cmp_exists_order (G : OrientedGraph U) (V C : Finset U) (hVC : ∀ u ∈ V, u ∉ C)
    (hh : U → ℕ) :
    ∃ ord : U → ℕ, Function.Injective ord ∧ (∀ a ∈ C, ∀ b, b ∉ C → ord a < ord b) ∧
      (∀ a, a ∉ univ \ (V ∪ C) → ∀ b ∈ univ \ (V ∪ C), ord a < ord b) ∧
      (∀ w, w ∉ V → w ∉ C → ∀ v ∈ V, ord v < ord w) ∧
      ∑ a ∈ C, (2 : ℝ) ^ (coverRowT G C ord a + hh a) +
          ∑ u ∈ univ \ (V ∪ C), (2 : ℝ) ^ (ordT G ord u + hh u) ≤
        ∑ i ∈ C, (2 : ℝ) ^ hh i * av (nbrCount G C i) +
          ∑ i ∈ univ \ (V ∪ C), (2 : ℝ) ^ (hh i +
            (rowsDeg0 G i - nbrCount G (univ \ (V ∪ C)) i)) *
              av (nbrCount G (univ \ (V ∪ C)) i) := by
  obtain ⟨rkC, hiC, hbC, hsC⟩ := cmp_exists_rank G C (fun i => (2 : ℝ) ^ hh i)
  obtain ⟨rkU, hiU, hbU, hsU⟩ := cmp_exists_rank G (univ \ (V ∪ C))
    (fun i => (2 : ℝ) ^ (hh i + (rowsDeg0 G i - nbrCount G (univ \ (V ∪ C)) i)))
  obtain ⟨rkV, hiV, hbV, -⟩ := cmp_exists_rank G V (fun _ => (0 : ℝ))
  refine ⟨cmpOrd C V rkC rkV rkU, cmpOrd_injective hVC hbC hbV hbU hiC hiV hiU,
    cmpOrd_C_lt hVC hbC, cmpOrd_lt_U hVC hbC hbV, cmpOrd_V_lt hVC hbC hbV, ?_⟩
  refine add_le_add (le_trans (le_of_eq ?_) hsC) (le_trans (le_of_eq ?_) hsU)
  · refine sum_congr rfl fun a ha => ?_
    rw [cmp_coverRowT_eq G ha, pow_add, mul_comm]
  · refine sum_congr rfl fun u hu => ?_
    rw [cmp_ordT_U hVC hbC hbV G hu, pow_add, pow_add, pow_add]
    ring

end Occupancy

/-! ## The class bound -/

section ClassBound

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `Λ₀ = R_full² exp(r² J_sp)/((1 - ê)^k ∏_{i ∈ U⁺} (1 - e_{d⁰_i}(q, n)))`
(`cor:extraction-compressed`, where `k = 2`). -/
noncomputable def cmpLambda0 (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ehat : ℝ)
    (k : ℕ) : ℝ :=
  rowsR G q n univ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * cmpJsp G ς) /
    ((1 - ehat) ^ k * ∏ i, (1 - coarseError (rowsDeg0 G i) q n))

omit [Fintype U] [DecidableEq U] in
theorem cmp_prod_le_exp {S : Finset U} {a x D : U → ℝ} (ha : ∀ v ∈ S, 0 ≤ a v)
    (h : ∀ v ∈ S, a v ≤ Real.exp (x v) / D v) :
    ∏ v ∈ S, a v ≤ Real.exp (∑ v ∈ S, x v) / ∏ v ∈ S, D v := by
  calc ∏ v ∈ S, a v ≤ ∏ v ∈ S, Real.exp (x v) / D v := prod_le_prod₀ ha h
    _ = _ := by rw [prod_div_distrib, Real.exp_sum]

/-- The product of factors in `(0, 1]` over two disjoint sets is at least the product over all
of `U⁺`. -/
theorem cmp_prod_two_ge {S T : Finset U} (hST : ∀ u ∈ S, u ∉ T) {D : U → ℝ}
    (hD0 : ∀ u, 0 ≤ D u) (hD1 : ∀ u, D u ≤ 1) :
    ∏ u, D u ≤ (∏ u ∈ S, D u) * ∏ u ∈ T, D u := by
  rw [← prod_union (disjoint_left.mpr hST), ← prod_sdiff (subset_univ (S ∪ T))]
  exact mul_le_of_le_one_left (prod_nonneg fun u _ => hD0 u)
    (prod_le_one₀ (fun u _ => hD0 u) (fun u _ => hD1 u))

theorem cmp_sum_two_le {S T : Finset U} (hST : ∀ u ∈ S, u ∉ T) {g : U → ℝ}
    (hg : ∀ u, 0 ≤ g u) : (∑ u ∈ S, g u) + ∑ u ∈ T, g u ≤ ∑ u, g u := by
  rw [← sum_union (disjoint_left.mpr hST)]
  exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun u _ _ => hg u

theorem cmp_intF_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U)
    (he : coarseError (rowsDeg0 G u) q n < 1) : 0 ≤ intF G ς q n ord Fr Cz u := by
  unfold intF intNum
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := coarseError_nonneg (q := q) hn0 (intS G ord Fr u)
  have h2 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
      ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b :=
    mul_nonneg (by positivity) (sum_nonneg fun _ _ => by positivity)
  have h3 : coarseError (ordT G ord u) q n ≤ coarseError (rowsDeg0 G u) q n :=
    coarseError_mono hn0 (ordT_le_deg G ord u)
  exact div_nonneg (by linarith) (by linarith)

theorem cmp_coverRowF_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (n : ℕ)
    (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (b : U)
    (he : coarseError (rowsDeg0 G b) q n < 1) : 0 ≤ coverRowF G ς q n C ord H b := by
  unfold coverRowF
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) (coverRowS G C ord H b)
  have h2 : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
      ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b :=
    mul_nonneg (by positivity) (sum_nonneg fun _ _ => by positivity)
  have h3 : coarseError (coverRowT G C ord b) q n ≤ coarseError (rowsDeg0 G b) q n :=
    coarseError_mono hn0 (coverRow_nbrCount_le G _ b)
  exact div_nonneg (by linarith) (by linarith)

theorem cmpGamma_nonneg (q : ℝ) (n Δ : ℕ) : 0 ≤ cmpGamma q n Δ := by
  unfold cmpGamma
  have : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  positivity

theorem cmp_rowsR_ge_one (G : OrientedGraph U) {q : ℝ} {n : ℕ}
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) : 1 ≤ rowsR G q n univ := by
  unfold rowsR
  refine one_le_prod₀ fun i _ => ?_
  have h0 := coarseError_nonneg (q := q) (Nat.cast_nonneg n) (rowsDeg0 G i)
  have h1 := he i
  rw [one_le_div (by linarith)]
  linarith

/-- **The record factor in exponential form**: with the orders of `cmp_exists_order`,
`∏_v F_v ≤ (exp(γ_cmp oc(𝒞) + r² J_sp) / ∏_{i ∈ U⁺} (1 - e_{d⁰_i}(q, n)))²`. -/
theorem cmp_recordFactor_le (G : OrientedGraph U) (ς : U → U → ℤ)
    (hsym : ∀ a b, ς a b ≠ 0 ↔ ς b a ≠ 0) {q : ℝ} {n Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ)
    (he : ∀ i, coarseError (rowsDeg0 G i) q n < 1) (Fr : Finset (U × U))
    (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V W Cx Cz : Finset U) (ordX ordZ : U → ℕ)
    (hX : ∑ a ∈ Cx, (2 : ℝ) ^ (coverRowT G Cx ordX a + cmpHx Fr a) +
          ∑ u ∈ univ \ (V ∪ Cx), (2 : ℝ) ^ (ordT G ordX u + cmpHx Fr u) ≤
        ∑ i ∈ Cx, (2 : ℝ) ^ cmpHx Fr i * av (nbrCount G Cx i) +
          ∑ i ∈ univ \ (V ∪ Cx), (2 : ℝ) ^ (cmpHx Fr i +
            (rowsDeg0 G i - nbrCount G (univ \ (V ∪ Cx)) i)) *
              av (nbrCount G (univ \ (V ∪ Cx)) i))
    (hZ : ∑ a ∈ Cz, (2 : ℝ) ^ (coverRowT G Cz ordZ a + cmpHz Fr a) +
          ∑ u ∈ univ \ (W ∪ Cz), (2 : ℝ) ^ (ordT G ordZ u + cmpHz Fr u) ≤
        ∑ i ∈ Cz, (2 : ℝ) ^ cmpHz Fr i * av (nbrCount G Cz i) +
          ∑ i ∈ univ \ (W ∪ Cz), (2 : ℝ) ^ (cmpHz Fr i +
            (rowsDeg0 G i - nbrCount G (univ \ (W ∪ Cz)) i)) *
              av (nbrCount G (univ \ (W ∪ Cz)) i)) :
    recordFactor G ς q n Fr V W Cx Cz ordX ordZ ≤
      (Real.exp (cmpGamma q n Δ * cmpOc G Fr V W Cx Cz + (Real.sqrt q)⁻¹ ^ 2 * cmpJsp G ς) /
        ∏ i, (1 - coarseError (rowsDeg0 G i) q n)) ^ 2 := by
  set γ := cmpGamma q n Δ
  set r2 := (Real.sqrt q)⁻¹ ^ 2
  set D : U → ℝ := fun i => 1 - coarseError (rowsDeg0 G i) q n with hDdef
  set H := Fr.filter (fun e => e.2 ∈ Cz)
  set FT := Fr.image Prod.swap
  set HT := FT.filter (fun e => e.2 ∈ Cx)
  set Ux := univ \ (V ∪ Cx)
  set Uz := univ \ (W ∪ Cz)
  have hD0 : ∀ i, 0 < D i := fun i => by simp only [hDdef]; linarith [he i]
  have hD1 : ∀ i, D i ≤ 1 := fun i => by
    simp only [hDdef]
    linarith [coarseError_nonneg (q := q) (Nat.cast_nonneg n) (rowsDeg0 G i)]
  have hγ : 0 ≤ γ := cmpGamma_nonneg q n Δ
  have hr2 : 0 ≤ r2 := sq_nonneg _
  -- the four products
  have hP1 : ∏ u ∈ Ux, intF G ς q n ordX Fr Cz u ≤
      Real.exp (∑ u ∈ Ux, (2 * γ * 2 ^ (ordT G ordX u + cmpHx Fr u) + r2 * cmpSp G ς u)) /
        ∏ u ∈ Ux, D u := by
    refine cmp_prod_le_exp (fun u _ => cmp_intF_nonneg G ς n ordX Fr Cz u (he u))
      fun u _ => ?_
    have := cmp_intF_le G ς hsym n Δ hΔ ordX Fr Cz u (by
      refine card_le_card fun b hb => ?_
      simp only [intH, mem_filter, mem_univ, true_and] at hb
      simp only [rowsN, mem_filter, mem_univ, true_and]
      exact (hsym u b).mp (hFr _ hb)) (he u)
    exact this
  have hP2 : ∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b ≤
      Real.exp (∑ b ∈ Cz, (2 * γ * 2 ^ (coverRowT G Cz ordZ b + cmpHz Fr b) +
        r2 * cmpSp G ς b)) / ∏ b ∈ Cz, D b := by
    refine cmp_prod_le_exp (fun b _ => cmp_coverRowF_nonneg G ς n Cz ordZ H b (he b))
      fun b hb => ?_
    have := cmp_coverRowF_le G ς n Δ hΔ Cz ordZ H b (by
      refine card_le_card fun a ha => ?_
      simp only [coverRowH, mem_filter, mem_univ, true_and, H] at ha
      simp only [rowsN, mem_filter, mem_univ, true_and]
      exact hFr _ ha.1) (he b)
    rw [show coverRowS G Cz ordZ H b = coverRowT G Cz ordZ b + cmpHz Fr b from by
      rw [← cmp_coverRowH_card Fr Cz hb]; rfl] at this
    exact this
  have hP3 : ∏ u ∈ Uz, intF G ς q n ordZ FT Cx u ≤
      Real.exp (∑ u ∈ Uz, (2 * γ * 2 ^ (ordT G ordZ u + cmpHz Fr u) + r2 * cmpSp G ς u)) /
        ∏ u ∈ Uz, D u := by
    refine cmp_prod_le_exp (fun u _ => cmp_intF_nonneg G ς n ordZ FT Cx u (he u))
      fun u _ => ?_
    have := cmp_intF_le G ς hsym n Δ hΔ ordZ FT Cx u (by
      refine card_le_card fun a ha => ?_
      simp only [intH, mem_filter, mem_univ, true_and, FT] at ha
      obtain ⟨e, he', hee⟩ := mem_image.mp ha
      have : e = (a, u) := by
        rw [← Prod.swap_swap e, hee]
        rfl
      rw [this] at he'
      simp only [rowsN, mem_filter, mem_univ, true_and]
      exact hFr _ he') (he u)
    rw [show intS G ordZ FT u = ordT G ordZ u + cmpHz Fr u from by
      rw [← cmp_intH_swap_card Fr u]; rfl] at this
    exact this
  have hP4 : ∏ a ∈ Cx, coverRowF G ς q n Cx ordX HT a ≤
      Real.exp (∑ a ∈ Cx, (2 * γ * 2 ^ (coverRowT G Cx ordX a + cmpHx Fr a) +
        r2 * cmpSp G ς a)) / ∏ a ∈ Cx, D a := by
    refine cmp_prod_le_exp (fun a _ => cmp_coverRowF_nonneg G ς n Cx ordX HT a (he a))
      fun a ha => ?_
    have := cmp_coverRowF_le G ς n Δ hΔ Cx ordX HT a (by
      refine card_le_card fun b hb => ?_
      simp only [coverRowH, mem_filter, mem_univ, true_and, HT, FT] at hb
      obtain ⟨e, he', hee⟩ := mem_image.mp hb.1
      have : e = (a, b) := by
        rw [← Prod.swap_swap e, hee]
        rfl
      rw [this] at he'
      simp only [rowsN, mem_filter, mem_univ, true_and]
      exact (hsym a b).mp (hFr _ he')) (he a)
    rw [show coverRowS G Cx ordX HT a = coverRowT G Cx ordX a + cmpHx Fr a from by
      rw [← cmp_coverRowH_swap_card Fr Cx ha]; rfl] at this
    exact this
  -- combine the four products
  have hRF : recordFactor G ς q n Fr V W Cx Cz ordX ordZ =
      (∏ u ∈ Ux, intF G ς q n ordX Fr Cz u) * (∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b) *
        (∏ u ∈ Uz, intF G ς q n ordZ FT Cx u) * ∏ a ∈ Cx, coverRowF G ς q n Cx ordX HT a := rfl
  rw [hRF]
  set A1 := ∑ u ∈ Ux, (2 : ℝ) ^ (ordT G ordX u + cmpHx Fr u)
  set A2 := ∑ b ∈ Cz, (2 : ℝ) ^ (coverRowT G Cz ordZ b + cmpHz Fr b)
  set A3 := ∑ u ∈ Uz, (2 : ℝ) ^ (ordT G ordZ u + cmpHz Fr u)
  set A4 := ∑ a ∈ Cx, (2 : ℝ) ^ (coverRowT G Cx ordX a + cmpHx Fr a)
  set B1 := ∑ u ∈ Ux, cmpSp G ς u
  set B2 := ∑ b ∈ Cz, cmpSp G ς b
  set B3 := ∑ u ∈ Uz, cmpSp G ς u
  set B4 := ∑ a ∈ Cx, cmpSp G ς a
  have hx1 : ∑ u ∈ Ux, (2 * γ * 2 ^ (ordT G ordX u + cmpHx Fr u) + r2 * cmpSp G ς u) =
      2 * γ * A1 + r2 * B1 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hx2 : ∑ b ∈ Cz, (2 * γ * 2 ^ (coverRowT G Cz ordZ b + cmpHz Fr b) + r2 * cmpSp G ς b) =
      2 * γ * A2 + r2 * B2 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hx3 : ∑ u ∈ Uz, (2 * γ * 2 ^ (ordT G ordZ u + cmpHz Fr u) + r2 * cmpSp G ς u) =
      2 * γ * A3 + r2 * B3 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  have hx4 : ∑ a ∈ Cx, (2 * γ * 2 ^ (coverRowT G Cx ordX a + cmpHx Fr a) + r2 * cmpSp G ς a) =
      2 * γ * A4 + r2 * B4 := by rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  rw [hx1] at hP1
  rw [hx2] at hP2
  rw [hx3] at hP3
  rw [hx4] at hP4
  set d1 := ∏ u ∈ Ux, D u
  set d2 := ∏ b ∈ Cz, D b
  set d3 := ∏ u ∈ Uz, D u
  set d4 := ∏ a ∈ Cx, D a
  have hd1 : 0 < d1 := prod_pos fun u _ => hD0 u
  have hd2 : 0 < d2 := prod_pos fun u _ => hD0 u
  have hd3 : 0 < d3 := prod_pos fun u _ => hD0 u
  have hd4 : 0 < d4 := prod_pos fun u _ => hD0 u
  have hn1 : 0 ≤ ∏ u ∈ Ux, intF G ς q n ordX Fr Cz u :=
    prod_nonneg fun u _ => cmp_intF_nonneg G ς n ordX Fr Cz u (he u)
  have hn2 : 0 ≤ ∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b :=
    prod_nonneg fun b _ => cmp_coverRowF_nonneg G ς n Cz ordZ H b (he b)
  have hn3 : 0 ≤ ∏ u ∈ Uz, intF G ς q n ordZ FT Cx u :=
    prod_nonneg fun u _ => cmp_intF_nonneg G ς n ordZ FT Cx u (he u)
  have hstep : (∏ u ∈ Ux, intF G ς q n ordX Fr Cz u) * (∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b) *
      (∏ u ∈ Uz, intF G ς q n ordZ FT Cx u) * ∏ a ∈ Cx, coverRowF G ς q n Cx ordX HT a ≤
      (Real.exp (2 * γ * A1 + r2 * B1) / d1) * (Real.exp (2 * γ * A2 + r2 * B2) / d2) *
        (Real.exp (2 * γ * A3 + r2 * B3) / d3) * (Real.exp (2 * γ * A4 + r2 * B4) / d4) := by
    refine mul_le_mul (mul_le_mul (mul_le_mul hP1 hP2 hn2 (by positivity)) hP3 hn3
      (by positivity)) hP4
      (prod_nonneg fun a _ => cmp_coverRowF_nonneg G ς n Cx ordX HT a (he a)) (by positivity)
  have hcomb : (Real.exp (2 * γ * A1 + r2 * B1) / d1) * (Real.exp (2 * γ * A2 + r2 * B2) / d2) *
        (Real.exp (2 * γ * A3 + r2 * B3) / d3) * (Real.exp (2 * γ * A4 + r2 * B4) / d4) =
      Real.exp (2 * γ * (A1 + A2 + A3 + A4) + r2 * (B1 + B2 + B3 + B4)) /
        (d1 * d2 * d3 * d4) := by
    have : 2 * γ * (A1 + A2 + A3 + A4) + r2 * (B1 + B2 + B3 + B4) =
        (2 * γ * A1 + r2 * B1) + (2 * γ * A2 + r2 * B2) + (2 * γ * A3 + r2 * B3) +
          (2 * γ * A4 + r2 * B4) := by ring
    rw [this]
    generalize 2 * γ * A1 + r2 * B1 = y1
    generalize 2 * γ * A2 + r2 * B2 = y2
    generalize 2 * γ * A3 + r2 * B3 = y3
    generalize 2 * γ * A4 + r2 * B4 = y4
    rw [Real.exp_add, Real.exp_add, Real.exp_add]
    field_simp
  -- the occupancy, the special sums and the denominators
  have hA : A1 + A2 + A3 + A4 ≤ cmpOc G Fr V W Cx Cz := by
    unfold cmpOc
    linarith [hX, hZ]
  have hJ := cmp_Jsp_eq G ς hsym
  have hUxCx : ∀ u ∈ Ux, u ∉ Cx := fun u hu => by
    simp only [Ux, mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu
    exact hu.2
  have hCzUz : ∀ u ∈ Cz, u ∉ Uz := fun u hu hu' => by
    simp only [Uz, mem_sdiff, mem_univ, true_and, mem_union, not_or] at hu'
    exact hu'.2 hu
  have hB14 : B1 + B4 ≤ cmpJsp G ς := by
    rw [hJ]
    exact cmp_sum_two_le hUxCx (cmpSp_nonneg G ς)
  have hB23 : B2 + B3 ≤ cmpJsp G ς := by
    rw [hJ]
    exact cmp_sum_two_le hCzUz (cmpSp_nonneg G ς)
  have hd14 : ∏ i, D i ≤ d1 * d4 := cmp_prod_two_ge hUxCx (fun u => (hD0 u).le) hD1
  have hd23 : ∏ i, D i ≤ d2 * d3 := cmp_prod_two_ge hCzUz (fun u => (hD0 u).le) hD1
  have hDU : 0 < ∏ i, D i := prod_pos fun i _ => hD0 i
  have hexp : 2 * γ * (A1 + A2 + A3 + A4) + r2 * (B1 + B2 + B3 + B4) ≤
      2 * (γ * cmpOc G Fr V W Cx Cz + r2 * cmpJsp G ς) := by
    have h1 := mul_le_mul_of_nonneg_left hA (by positivity : (0 : ℝ) ≤ 2 * γ)
    have h2 : r2 * (B1 + B2 + B3 + B4) ≤ r2 * (2 * cmpJsp G ς) :=
      mul_le_mul_of_nonneg_left (by linarith) hr2
    linarith
  have hden : (∏ i, D i) ^ 2 ≤ d1 * d2 * d3 * d4 := by
    have := mul_le_mul hd14 hd23 hDU.le (by positivity)
    calc (∏ i, D i) ^ 2 = (∏ i, D i) * ∏ i, D i := sq _
      _ ≤ d1 * d4 * (d2 * d3) := this
      _ = d1 * d2 * d3 * d4 := by ring
  calc (∏ u ∈ Ux, intF G ς q n ordX Fr Cz u) * (∏ b ∈ Cz, coverRowF G ς q n Cz ordZ H b) *
        (∏ u ∈ Uz, intF G ς q n ordZ FT Cx u) * ∏ a ∈ Cx, coverRowF G ς q n Cx ordX HT a
      ≤ Real.exp (2 * γ * (A1 + A2 + A3 + A4) + r2 * (B1 + B2 + B3 + B4)) /
          (d1 * d2 * d3 * d4) := hstep.trans (le_of_eq hcomb)
    _ ≤ Real.exp (2 * (γ * cmpOc G Fr V W Cx Cz + r2 * cmpJsp G ς)) / (∏ i, D i) ^ 2 :=
        div_le_div₀ (Real.exp_pos _).le (Real.exp_le_exp.mpr hexp) (by positivity) hden
    _ = _ := by
        rw [div_pow, two_mul, Real.exp_add]
        ring

end ClassBound

section Main

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

/-- **`cor:extraction-compressed`, the class bound.** Assume `e_{d⁰_i}(q, n) ≤ ê < 1` (from
(S1) at `p`), `n ≥ |U⁺|`, and `d_i = d⁰_i + r_i ≤ Δ` for all `i`. Let `𝒞 = 𝒞(P, A)` be a class with
a witness `w` of size `k` (`k = 2` in the paper) and a cover `(C_x, C_z)`, and let `c_ker` bound
its rectangle kernel on injective tuples as in `grouped_extraction` (`c_ker ∈ {1, 2}` for a
witness of size two, `KernelBridge.lean`). Then, with orders of the record chosen by
`lem:cover:order` (`cmp_exists_order`),
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex(𝒞)/2} Λ₀ exp(γ_cmp oc(𝒞)) ‖f‖_μ ‖h‖_μ`,
where `ex(𝒞) = t_V + t_W + f_V + f_W` with `t_V = e(V) + e(V, C_x)`, `t_W = e(W) + e(W, C_z)`
(`cmpEx`), `oc(𝒞)` is `cmpOc`, `γ_cmp = n r² + (Δ/4) r` and
`Λ₀ = R_full² exp(r² J_sp)/((1 - ê)^k ∏_i (1 - e_{d⁰_i}(q, n)))`. Literature input:
`WeilBound F`. -/
theorem extraction_compressed_class (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    {k : ℕ} (w : Fin k → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        cmpLambda0 G ς (Fintype.card F) n ehat k *
        Real.exp (cmpGamma (Fintype.card F) n Δ *
          cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hsym : ∀ a b, ς a b ≠ 0 ↔ ς b a ≠ 0 := fun a b => by
    rw [hanti a b, neg_ne_zero]
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  obtain ⟨ordX, hiX, hX0, hX1, hX2, hXs⟩ :=
    cmp_exists_order G (witV w) Cx hVC (cmpHx (Ex \ (P ∪ A)))
  obtain ⟨ordZ, hiZ, hZ0, hZ1, hZ2, hZs⟩ :=
    cmp_exists_order G (witW w) Cz hWC (cmpHz (Ex \ (P ∪ A)))
  have hmain := grouped_extraction hW G ς hς hanti hne hn hehat hehat1 Ex P A hEx hcls w hw Cx Cz
    hcov ordX ordZ hiX hiZ hX0 hZ0 hX1 hZ1 hcker hker f h
  have hex : recordExp G (Ex \ (P ∪ A)) (witV w) (witW w) ordX ordZ =
      cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz := by
    unfold recordExp cmpEx
    rw [cmp_sum_ordT G (witV w) Cx ordX hiX hVC (fun a ha v hv => hX0 a ha v (hVC v hv)) hX2,
      cmp_sum_ordT G (witW w) Cz ordZ hiZ hWC (fun a ha v hv => hZ0 a ha v (hWC v hv)) hZ2]
  rw [hex] at hmain
  have he : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1 := fun i =>
    lt_of_le_of_lt (hehat i) hehat1
  have hRF := cmp_recordFactor_le G ς hsym hΔ he (Ex \ (P ∪ A))
    (fun e he' => hEx e (mem_sdiff.mp he').1) (witV w) (witW w) Cx Cz ordX ordZ hXs hZs
  refine hmain.trans ?_
  set X := Real.exp (cmpGamma (Fintype.card F) n Δ *
      cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * cmpJsp G ς) /
    ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) with hXdef
  have hD : 0 < ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) :=
    prod_pos fun i _ => by linarith [he i]
  have hXnn : 0 ≤ X := div_nonneg (Real.exp_pos _).le hD.le
  have hsq : Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w)
      Cx Cz ordX ordZ) ≤ X := by
    rw [← Real.sqrt_sq hXnn]
    exact Real.sqrt_le_sqrt hRF
  have h1e : 0 < 1 - ehat := by linarith
  have hR : 1 ≤ rowsR G (Fintype.card F) n univ ^ 2 :=
    one_le_pow₀ (cmp_rowsR_ge_one G he)
  have hXL : X / (1 - ehat) ^ k ≤ cmpLambda0 G ς (Fintype.card F) n ehat k *
      Real.exp (cmpGamma (Fintype.card F) n Δ * cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) := by
    unfold cmpLambda0
    rw [hXdef, Real.exp_add, div_div]
    have hpos : 0 < (1 - ehat) ^ k * ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) :=
      mul_pos (pow_pos h1e k) hD
    rw [div_mul_eq_mul_div, mul_comm (∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n))]
    apply div_le_div_of_nonneg_right _ hpos.le
    have e1 := Real.exp_pos (cmpGamma (Fintype.card F) n Δ *
      cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz)
    have e2 := Real.exp_pos ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * cmpJsp G ς)
    nlinarith [mul_pos e1 e2]
  have hcr : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := mul_nonneg hcker (by positivity)
  have hE : 0 ≤ Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
      Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by positivity
  rw [Real.sqrt_mul (by positivity)]
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        (Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w)
            Cx Cz ordX ordZ)) / (1 - ehat) ^ k *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))
      = cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          (Real.sqrt (recordFactor G ς (Fintype.card F) n (Ex \ (P ∪ A)) (witV w) (witW w)
            Cx Cz ordX ordZ) / (1 - ehat) ^ k) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
            Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by ring
    _ ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          (X / (1 - ehat) ^ k) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
            Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by
        gcongr
    _ ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
          Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
          (cmpLambda0 G ς (Fintype.card F) n ehat k *
            Real.exp (cmpGamma (Fintype.card F) n Δ *
              cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz)) *
          (Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
            Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2))) := by
        gcongr
    _ = _ := by ring

end Main

/-! ## The buckets -/

section Buckets

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

theorem cmp_expect_sum {Ω ι : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (s : Finset ι)
    (g : ι → Ω → ℝ) : μ.expect (fun ω => ∑ c ∈ s, g c ω) = ∑ c ∈ s, μ.expect (g c) := by
  unfold FiniteLaw.expect
  simp_rw [mul_sum]
  exact sum_comm

/-- **`cor:extraction-compressed`, the buckets.** Let `𝔓` be an exact partition of the nonstar
subsets of `Ex` (`IsExactPartition`; e.g. the compressed partition,
`isExactPartition_compressedPartition`), every class `c` with a record: a witness `wit c` of size
`k` (`k = 2` in the paper), a cover `(cx c, cz c)`, a kernel constant `ck c` (the kernel
hypothesis of `grouped_extraction`), and a bucket `𝔟(c) ∈ ℕ` with `oc(c) ≤ 𝔟(c) 2^𝔮`. Then
`|∑_{S nonstar} ⟨f, T_S h⟩_μ| ≤ r^k Λ₀ ∑_𝔟 S_𝔟 exp(γ_cmp 𝔟 2^𝔮) ‖f‖_μ ‖h‖_μ` with
`S_𝔟 = ∑_{c ↦ 𝔟} c_ker(c) 2^{ex(c)/2}` (the paper writes `S_𝔟 = 𝖺_𝔟 + 𝖻_𝔟 √2`). The
admissibility statement of the corollary (`lem:majorant`) is not formalized here. -/
theorem extraction_compressed_buckets (hW : WeilBound F) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hne : (injLabellings F G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n ≤ ehat) (hehat1 : ehat < 1)
    {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (Ex : Finset (U × U))
    (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex)) {k : ℕ}
    (wit : Finset (U × U) × Finset (U × U) → Fin k → U × U)
    (cx cz : Finset (U × U) × Finset (U × U) → Finset U)
    (ck : Finset (U × U) × Finset (U × U) → ℝ)
    (bucket : Finset (U × U) × Finset (U × U) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, OpBound (injTuples F (witV (wit c))) (injTuples F (witW (wit c)))
      (rectKer ς c.1 (witV (wit c)) (witW (wit c))) (ck c * Real.sqrt (Fintype.card F) ^ k))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (f h : (U → F) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ k * cmpLambda0 G ς (Fintype.card F) n ehat k *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
            (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card F) n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨hdat, hdisj, hunion⟩ := h𝔓
  set μ := graphLaw G hne
  set r := (Real.sqrt (Fintype.card F))⁻¹
  set L := cmpLambda0 G ς (Fintype.card F) n ehat k
  set γ := cmpGamma (Fintype.card F) n Δ
  set Nf := Real.sqrt (μ.expect (fun x => f x ^ 2))
  set Nh := Real.sqrt (μ.expect (fun x => h x ^ 2))
  set exc := fun c : Finset (U × U) × Finset (U × U) =>
    Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c))
  -- the nonstar sum splits over the classes
  have hsplit : ∀ x x' : U → F, (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x' := by
    intro x x'
    rw [← hunion, sum_biUnion hdisj]
  have hform : μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x')) =
      ∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x') * h x')) := by
    rw [← cmp_expect_sum]
    refine μ.expect_congr fun x => ?_
    rw [← mul_sum, ← cmp_expect_sum]
    congr 1
    refine μ.expect_congr fun x' => ?_
    rw [hsplit, sum_mul]
  rw [hform]
  -- the class bounds
  have hclass : ∀ c ∈ 𝔓, |μ.expect (fun x => f x * μ.expect (fun x' =>
      (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      r ^ k * L * (ck c * exc c * Real.exp (γ * (bucket c * 2 ^ 𝔮))) * Nf * Nh := by
    intro c hc
    have hb := extraction_compressed_class hW G ς hς hanti hne hn hehat hehat1 hΔ Ex c.1 c.2 hEx
      (hdat c hc) (wit c) (hwit c hc) (cx c) (cz c) (hcov c hc) (hck c hc) (hker c hc) f h
    refine hb.trans ?_
    have hγ : 0 ≤ γ := cmpGamma_nonneg _ n Δ
    have hexp : Real.exp (γ * cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
        (cz c)) ≤ Real.exp (γ * (bucket c * 2 ^ 𝔮)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbucket c hc) hγ)
    have hL : 0 ≤ L := by
      have he : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1 := fun i =>
        lt_of_le_of_lt (hehat i) hehat1
      have hD : 0 < ∏ i, (1 - coarseError (rowsDeg0 G i) (Fintype.card F) n) :=
        prod_pos fun i _ => by linarith [he i]
      have h1e : 0 < 1 - ehat := by linarith
      simp only [L, cmpLambda0]
      positivity
    have h0 : 0 ≤ ck c * r ^ k * exc c * L := by
      have := hck c hc
      positivity
    have hN : 0 ≤ Nf * Nh := by positivity
    calc ck c * r ^ k * exc c * L *
          Real.exp (γ * cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c)) *
          Nf * Nh
        = (ck c * r ^ k * exc c * L) *
          Real.exp (γ * cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c)) *
          (Nf * Nh) := by ring
      _ ≤ (ck c * r ^ k * exc c * L) * Real.exp (γ * (bucket c * 2 ^ 𝔮)) * (Nf * Nh) := by
          gcongr
      _ = _ := by ring
  calc |∑ c ∈ 𝔓, μ.expect (fun x => f x * μ.expect (fun x' =>
        (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x x') * h x'))|
      ≤ ∑ c ∈ 𝔓, r ^ k * L * (ck c * exc c * Real.exp (γ * (bucket c * 2 ^ 𝔮))) * Nf * Nh :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hclass)
    _ = r ^ k * L * (∑ c ∈ 𝔓, ck c * exc c * Real.exp (γ * (bucket c * 2 ^ 𝔮))) * Nf * Nh := by
        rw [mul_sum, sum_mul, sum_mul]
    _ = r ^ k * L * (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * exc c) * Real.exp (γ * (b * 2 ^ 𝔮))) * Nf * Nh := by
        congr 3
        rw [← sum_fiberwise_of_maps_to (fun c hc => mem_image_of_mem bucket hc)]
        refine sum_congr rfl fun b _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun c hc => ?_
        rw [(mem_filter.mp hc).2]

end Buckets

/-! ## Witnesses of size two over `𝔽_p`: `c_ker = 2^{β(𝒞)} ∈ {1, 2}` -/

section TwoWitness

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

open Sarkozy.Influence (OpBound)

/-- For a witness of size two every strongly connected component of `D_𝒞` has at most two
vertices. -/
theorem cmp_component_card_le_two (𝒦 : Finset (Fin 2 × Fin 2)) (i : Fin 2) :
    (twoCycleComponent 𝒦 i).card ≤ 2 := by
  have := card_le_univ (twoCycleComponent 𝒦 i)
  simpa using this

/-- `β(𝒞) ≤ 1` for a witness of size two, so `c_ker(𝒞) = 2^{β(𝒞)} ∈ {1, 2}`. -/
theorem cmp_twoCycleCount_le_one (𝒦 : Finset (Fin 2 × Fin 2)) : twoCycleCount 𝒦 ≤ 1 := by
  unfold twoCycleCount
  have hsub : ((univ.image (twoCycleComponent 𝒦)).filter (fun C => C.card = 2)) ⊆
      ({univ} : Finset (Finset (Fin 2))) := by
    intro C hC
    rw [mem_filter] at hC
    rw [mem_singleton]
    exact eq_univ_of_card C (by simpa using hC.2)
  calc _ ≤ ({univ} : Finset (Finset (Fin 2))).card := card_le_card hsub
    _ = 1 := card_singleton _

/-- **`cor:extraction-compressed` for a witness of size two over `𝔽_p`**, with the kernel
constant `c_ker(𝒞) = 2^{β(𝒞)} ∈ {1, 2}` of `lem:matching:kernel` (`cmp_twoCycleCount_le_one`;
`β = 1` exactly for the complete rectangle). Hypotheses: `WeilBound (ZMod p)` (Weil's theorem)
and `FourCycleBound p` (`cor:dl:normalized`(a), used for the complete rectangle). -/
theorem extraction_compressed_class_two (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hW : WeilBound (ZMod p)) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat)
    (hehat1 : ehat < 1) {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ)
    (Ex P A : Finset (U × U)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (hcls : IsClassDatum Ex (P, A))
    (w : Fin 2 → U × U) (hw : IsWitness Ex P A w) (Cx Cz : Finset U)
    (hcov : IsCover Ex P A w Cx Cz) (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      2 ^ twoCycleCount (witnessIdx P w) * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        Real.sqrt (2 ^ cmpEx G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        cmpLambda0 G ς (Fintype.card (ZMod p)) n ehat 2 *
        Real.exp (cmpGamma (Fintype.card (ZMod p)) n Δ *
          cmpOc G (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hςP : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 :=
    sign_pm_of_ne_zero hς fun e he => hEx e (hcls.1 he)
  have hker := Sarkozy.ExtractionK.IsWitness.rectKer_opBound_twoCycles hw hp2 h4 ς hςP
    (cmp_component_card_le_two (witnessIdx P w))
  have hker' : OpBound (injTuples (ZMod p) (witV w)) (injTuples (ZMod p) (witW w))
      (rectKer ς P (witV w) (witW w))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt (Fintype.card (ZMod p)) ^ 2) := by
    rw [ZMod.card]
    exact hker
  exact extraction_compressed_class hW G ς hς hanti hne hn hehat hehat1 hΔ Ex P A hEx hcls w hw
    Cx Cz hcov (by positivity) hker' f h

/-- **`cor:extraction-compressed`, the buckets, for witnesses of size two over `𝔽_p`**: the
bucket bound of `extraction_compressed_buckets` with `c_ker(𝒞) = 2^{β(𝒞)}`. Hypotheses:
`WeilBound (ZMod p)` and `FourCycleBound p` (`cor:dl:normalized`(a)). -/
theorem extraction_compressed_buckets_two (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hW : WeilBound (ZMod p)) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hne : (injLabellings (ZMod p) G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) {ehat : ℝ}
    (hehat : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card (ZMod p)) n ≤ ehat)
    (hehat1 : ehat < 1) {Δ : ℕ} (hΔ : ∀ i, cmpDeg G ς i ≤ Δ) (Ex : Finset (U × U))
    (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0) (𝔓 : Finset (Finset (U × U) × Finset (U × U)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (U × U) × Finset (U × U) → Fin 2 → U × U)
    (cx cz : Finset (U × U) × Finset (U × U) → Finset U)
    (bucket : Finset (U × U) × Finset (U × U) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hbucket : ∀ c ∈ 𝔓, cmpOc G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        cmpLambda0 G ς (Fintype.card (ZMod p)) n ehat 2 *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c)) *
            Real.sqrt (2 ^ cmpEx G (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
              (cx c) (cz c))) * Real.exp (cmpGamma (Fintype.card (ZMod p)) n Δ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  refine extraction_compressed_buckets hW G ς hς hanti hne hn hehat hehat1 hΔ Ex hEx 𝔓 h𝔓 wit cx
    cz (fun c => (2 : ℝ) ^ twoCycleCount (witnessIdx c.1 (wit c))) bucket 𝔮 hwit hcov
    (fun c _ => by positivity) (fun c hc => ?_) hbucket f h
  have hςP : ∀ e ∈ c.1, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 :=
    sign_pm_of_ne_zero hς fun e he => hEx e (h𝔓.1 c hc |>.1 he)
  have hker := Sarkozy.ExtractionK.IsWitness.rectKer_opBound_twoCycles (hwit c hc) hp2 h4 ς hςP
    (cmp_component_card_le_two (witnessIdx c.1 (wit c)))
  rw [ZMod.card]
  exact hker

end TwoWitness

end Sarkozy.ExtractionK

module

public import Sarkozy.Extraction.MergedCount
public import Sarkozy.Labellings.GraphLaw
public import Sarkozy.Cuts.CutKernel

@[expose] public section

/-!
# Cover rows (`lem:extraction-rows`)

`paper/sections/16_extraction.tex`, `lem:extraction-rows` and its labelled equation
`eq:extraction:onevertex`, in the setting of the paragraph *Setting* of
`subsec:extraction:partition` (`R_Y`, `e_t(p, n')`, `μ = λ_p(G⁺)`), with the merge counts
`mg(j, i)`, `c^U(j, i)` and the vertex factor `F_b` of `def:extraction:records`. Inputs:
`lem:extraction-merged-count` (`merged_count_le_fintype'`), `lem:extension`(b), (c)
(`card_vertexAdmissible`), `lem:graphs:sequential`(a) (`extCount_bounds`) and `it:et:compare`,
`it:et:poly` (`upperError_le_coarseError`, `coarseError_mono`).

## Formal setting

`F` is a finite field with `q` elements (`F = 𝔽_p` in the paper), `χ = quadraticChar F`,
`r = q^{-1/2}`, and `WeilBound F` is Weil's theorem (`thm:weil`(a)), the literature input of
`lem:extension`; it is the only hypothesis taken from outside the paper. The half graph `G⁺` is
an oriented graph `G` on a finite type `U` (the vertex set `U⁺`), and `n ≥ |U|` (the paper takes
`n = |U⁺|`). The cross signs are a function `ς : U → U → ℤ` with values in `{0, ±1}`, with
`N(k) = {j : ς_{jk} ≠ 0}` (`rowsN`) and `E_× = {(j, k) : ς_{jk} ≠ 0}`. For spectral data `D`
(`def:spec:data`) these are `U = U⁺`, `G = D.halfGraph`, `ς = D.sgn`, `n = D.n`
(`coverRows_le_specData`). The order of `C` is a function `ord : U → ℕ`, injective on `C`;
`b'` is earlier than `b` when `ord b' < ord b`.

The definitions of the lemma: `rowsAdj` (`Adj(i)`), `rowsDeg0` (`d⁰_i`), `rowsMg` (`mg(j, i)`),
`rowsCU` (`c^U(j, i)`), `rowsR` (`R_Y = ∏_{i ∈ Y} (1 + e_{d⁰_i}(q, n))/(1 - e_{d⁰_i}(q, n))`),
`coverRowEarlier` (the vertices of `C` earlier than `b`), `coverRowT` (`t_b`), `coverRowH`
(`H_b = {a : (a, b) ∈ H}`), `coverRowS` (`s_b = t_b + h_b`), `coverRowExp`
(`mg(j,b) + c^U(j,b) - [j ∈ H_b]`, an integer), `coverRowF` (`F_b(H)`), `coverRowKappa`
(`κ_C(x, c')`), `coverRowIntegrand` (`∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')}`)
and `coverRowMarginal` (`μ_C`, the law of `x'_C` for `x' ∼ μ`).

## Results

* `coverRows_le` is `lem:extraction-rows`:
  `E_{c' ∼ μ_C}[∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')}] ≤
  R_{U⁺ \ C} ∏_{b ∈ C} F_b(H)`, assuming `e_{d⁰_i}(q, n) < 1` for every vertex `i` (implied by
  (S1) at `p`: `d⁰_i ≤ Δ` and `n ≤ 2n`). `coverRows_le_graphLaw` is the same bound with the
  expectation written over `x' ∼ μ`; `coverRows_le_specData` is the statement for spectral data
  under (S1) at `p` (`SpecData.S1`).
* `coverRows_oneVertex` is `eq:extraction:onevertex` (Step 4).

## Proof

As in the paper. Step 3 is `coverRow_integrand_le` (with the merge count
`coverRow_merges_le`); Step 4 is `coverRows_oneVertex`; Step 5 is the sequential summation
`coverRow_seq_upper` over `Inj_p(G⁺)` (labelling `C` in its order first). Steps 1 and 2 are
merged: instead of passing through `λ_p(G⁺[C])`, the numerator `∑_{x' ∈ Inj_p(G⁺)} Π(x'_C)` and
the denominator `|Inj_p(G⁺)|` are both computed by labelling `C` first and then `U⁺ \ C`; the
completions of a labelling of `C` number between `lowerProd` and `upperProd` along an ordering of
`U⁺ \ C` (`lem:graphs:sequential`(a)), whose ratio is at most `R_{U⁺ \ C}`
(`coverRow_upperProd_le`; this is the density statement of `lem:graphs:vertex`(subset)), and the
labellings of `C` are counted from below by `coverRow_seq_lower` with the one-step bound
`q 2^{-t_b}(1 - e_{t_b}(q, n))` (`lem:extension`(c), `it:et:compare`).

## Deviations from the paper

* Only the coarse error `e_t(p, n')` is used (the paragraph *Graded errors* is not formalized).
* `x` is only assumed injective (the paper: `x ∈ 𝓘⁺`), `n` may be any `n ≥ |U⁺|`, and of (S1)
  only `e_{d⁰_i}(p, n) < 1` is used (`coverRows_le_specData` assumes (S1) itself).
* `Inj_p(G⁺) ≠ ∅` is a hypothesis (`hne`), needed to form `μ`; the paper derives it from (S1).
* In `coverRows_le` a labelling `c'` of `C` enters the integrand through its extension by `0`
  (`extendLabel`); the integrand reads only the labels on `C` (`coverRowIntegrand_congr`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Labellings

/-! ## The data of the lemma -/

section Defs

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `Adj(i) = {j ∈ U⁺ : j ∼ i}`, the `G⁺`-neighbours of `i` (either orientation). -/
def rowsAdj (G : OrientedGraph U) (i : U) : Finset U :=
  univ.filter fun j => (j, i) ∈ G.E ∨ (i, j) ∈ G.E

/-- `d⁰_i = |Adj(i)|`, the degree of `i` in `G⁺`. -/
def rowsDeg0 (G : OrientedGraph U) (i : U) : ℕ := (rowsAdj G i).card

/-- `N(k) = {j : ς_{jk} ≠ 0}`. -/
def rowsN (ς : U → U → ℤ) (k : U) : Finset U := univ.filter fun j => ς j k ≠ 0

/-- The merge count `mg(j, i) = #{i' ∈ Adj(i) : j ∈ N(i')}` (`def:extraction:records`). -/
def rowsMg (G : OrientedGraph U) (ς : U → U → ℤ) (j i : U) : ℕ :=
  ((rowsAdj G i).filter fun i' => j ∈ rowsN ς i').card

/-- The count `c^U(j, i) = #{u ∈ Adj(j) : u ∈ N(i)}` (`def:extraction:records`). -/
def rowsCU (G : OrientedGraph U) (ς : U → U → ℤ) (j i : U) : ℕ :=
  ((rowsAdj G j).filter fun u => u ∈ rowsN ς i).card

/-- The completion ratio `R_Y = ∏_{i ∈ Y} (1 + e_{d⁰_i}(q, n))/(1 - e_{d⁰_i}(q, n))`. -/
noncomputable def rowsR (G : OrientedGraph U) (q : ℝ) (n : ℕ) (Y : Finset U) : ℝ :=
  ∏ i ∈ Y, (1 + coarseError (rowsDeg0 G i) q n) / (1 - coarseError (rowsDeg0 G i) q n)

/-- The vertices of `C` earlier than `b` for the order `ord` of `C`. -/
def coverRowEarlier (C : Finset U) (ord : U → ℕ) (b : U) : Finset U :=
  C.filter fun b' => ord b' < ord b

/-- `t_b`, the number of `G⁺`-neighbours of `b` earlier in `C`. -/
noncomputable def coverRowT (G : OrientedGraph U) (C : Finset U) (ord : U → ℕ) (b : U) : ℕ :=
  nbrCount G (coverRowEarlier C ord b) b

/-- `H_b = {a : (a, b) ∈ H}`. -/
def coverRowH (H : Finset (U × U)) (b : U) : Finset U := univ.filter fun a => (a, b) ∈ H

/-- `s_b = t_b + h_b`, `h_b = |H_b|`. -/
noncomputable def coverRowS (G : OrientedGraph U) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) (b : U) : ℕ :=
  coverRowT G C ord b + (coverRowH H b).card

/-- The exponent `mg(j, b) + c^U(j, b) - [j ∈ H_b]` (an integer). -/
def coverRowExp (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U)) (j b : U) : ℤ :=
  ((rowsMg G ς j b + rowsCU G ς j b : ℕ) : ℤ) - if j ∈ coverRowH H b then 1 else 0

/-- The vertex factor `F_b(H)` of `def:extraction:records` with the counts `t_b`, `s_b` and the
sets `H_b` of `lem:extraction-rows`:
`(1 + e_{s_b}(q, 2n) + r² 2^{s_b} ∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]}) /
(1 - e_{t_b}(q, n))`, `r = q^{-1/2}`. -/
noncomputable def coverRowF (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ)
    (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (b : U) : ℝ :=
  (1 + coarseError (coverRowS G C ord H b) q (2 * n) +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) /
    (1 - coarseError (coverRowT G C ord b) q n)

end Defs

section Integrand

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `κ_C(x, c') = ∑_{b ∈ C} ∑_{i ∈ U⁺} c^U(i, b) 1[c'_b = x_i]`. -/
def coverRowKappa (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U) (x c' : U → F) : ℕ :=
  ∑ b ∈ C, ∑ i, if c' b = x i then rowsCU G ς i b else 0

/-- The integrand `Π(c') = ∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')}`. When every
`(a, b) ∈ H` has `b ∈ C`, it reads `c'` only on `C` (`coverRowIntegrand_congr`). -/
noncomputable def coverRowIntegrand (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U)
    (H : Finset (U × U)) (x c' : U → F) : ℝ :=
  (∏ e ∈ H, (1 + (quadraticChar F ((ς e.1 e.2 : F) * (c' e.2 - x e.1)) : ℝ))) *
    2 ^ coverRowKappa G ς C x c'

/-- The marginal `μ_C` of `μ = λ_p(G⁺)`: the law of `x'_C` for `x' ∼ μ`. -/
noncomputable def coverRowMarginal (G : OrientedGraph U) (hne : (injLabellings F G).Nonempty)
    (C : Finset U) : Sarkozy.FiniteLaw (C → F) :=
  (graphLaw G hne).map fun y (b : C) => y b

end Integrand

/-! ## Weighted sequential sums -/

section Sequential

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `∑_{y ∈ Inj_p(G), y|_A = x|_A} f(y)`. -/
noncomputable def coverRowExtSum (G : OrientedGraph U) (A : Finset U) (x : U → F)
    (f : (U → F) → ℝ) : ℝ :=
  ∑ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ A, y a = x a), f y

theorem coverRowExtSum_one (G : OrientedGraph U) (A : Finset U) (x : U → F) :
    coverRowExtSum G A x (fun _ => 1) = extCount G A x := by
  unfold coverRowExtSum extCount
  rw [sum_const, nsmul_eq_mul, mul_one]

theorem coverRowExtSum_empty (G : OrientedGraph U) (x : U → F) (f : (U → F) → ℝ) :
    coverRowExtSum G ∅ x f = ∑ y ∈ injLabellings F G, f y := by
  unfold coverRowExtSum
  congr 1
  exact filter_true_of_mem fun _ _ => by simp

/-- Labelling one more vertex: `∑_{y ⊇ x|_A} f(y) = ∑_{c ∈ Φ_v(x)} ∑_{y ⊇ x[v ↦ c]|_{A ∪ v}} f(y)`
(the weighted form of `extCount_insert`). -/
theorem coverRowExtSum_insert (G : OrientedGraph U) {A : Finset U} (x : U → F) {v : U}
    (hv : v ∉ A) (f : (U → F) → ℝ) :
    coverRowExtSum G A x f = ∑ c ∈ vertexAdmissible G A x v,
      coverRowExtSum G (insert v A) (Function.update x v c) f := by
  unfold coverRowExtSum
  rw [← sum_fiberwise_of_maps_to (g := fun y => y v) (t := univ) (fun _ _ => mem_univ _)]
  have hfib : ∀ c : F, ((injLabellings F G).filter fun y => ∀ a ∈ A, y a = x a).filter
      (fun y => y v = c) = (injLabellings F G).filter
        (fun y => ∀ a ∈ insert v A, y a = Function.update x v c a) := by
    intro c
    ext y
    simp only [mem_filter, mem_insert, forall_eq_or_imp, Function.update_self]
    constructor
    · rintro ⟨⟨hy, hA⟩, hyv⟩
      refine ⟨hy, hyv, fun a ha => ?_⟩
      rw [Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha))]
      exact hA a ha
    · rintro ⟨hy, hyv, hA⟩
      refine ⟨⟨hy, fun a ha => ?_⟩, hyv⟩
      rw [hA a ha, Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha))]
  simp_rw [hfib]
  symm
  apply sum_subset (subset_univ _)
  intro c _ hc
  rw [filter_eq_empty_iff.mpr, sum_empty]
  intro y hy hagree
  apply hc
  simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
  have hyv : y v = c := by simpa using hagree v (mem_insert_self v A)
  have hyA : ∀ a ∈ A, y a = x a := fun a ha => by
    rw [hagree a (mem_insert_of_mem ha), Function.update_of_ne (fun (h : a = v) => hv (h ▸ ha))]
  simp only [vertexAdmissible, mem_filter, mem_univ, true_and, mem_image, not_exists, not_and]
  refine ⟨fun a ha hxa => ?_, fun u hu he => ?_, fun u hu he => ?_⟩
  · have : y a = y v := by rw [hyA a ha, hxa, hyv]
    exact hv (hy.1 a (mem_univ _) v (mem_univ _) this ▸ ha)
  · have := hy.2 (u, v) he (mem_univ _) (mem_univ _)
    simpa [hyv, hyA u hu] using this
  · have := hy.2 (v, u) he (mem_univ _) (mem_univ _)
    simpa [hyv, hyA u hu] using this

omit [Fintype U] in
/-- The first remaining vertex `b₀` of a final segment `S` of the ordered set `C`: the labelled
set `C \ S` is the set of vertices earlier than `b₀`. -/
theorem coverRow_first {C S : Finset U} {ord : U → ℕ} (hord : Set.InjOn ord C) (hSC : S ⊆ C)
    (hseg : ∀ b ∈ S, ∀ b' ∈ C, b' ∉ S → ord b' < ord b) (hS : S.Nonempty) :
    ∃ b₀ ∈ S, C \ S = coverRowEarlier C ord b₀ ∧ insert b₀ (C \ S) = C \ S.erase b₀ ∧
      (∀ b ∈ S.erase b₀, ∀ b' ∈ C, b' ∉ S.erase b₀ → ord b' < ord b) ∧
      (∀ a ∈ C, ord a ≤ ord b₀ → a ∈ insert b₀ (C \ S)) := by
  obtain ⟨b₀, hb₀, hmin⟩ := S.exists_min_image ord hS
  refine ⟨b₀, hb₀, ?_, ?_, ?_, ?_⟩
  · ext a
    simp only [mem_sdiff, coverRowEarlier, mem_filter]
    constructor
    · rintro ⟨haC, haS⟩
      exact ⟨haC, hseg b₀ hb₀ a haC haS⟩
    · rintro ⟨haC, hlt⟩
      exact ⟨haC, fun haS => absurd (hmin a haS) (not_le.mpr hlt)⟩
  · ext a
    simp only [mem_insert, mem_sdiff, mem_erase]
    constructor
    · rintro (rfl | ⟨haC, haS⟩)
      · exact ⟨hSC hb₀, fun h => h.1 rfl⟩
      · exact ⟨haC, fun h => haS h.2⟩
    · rintro ⟨haC, ha⟩
      by_cases hab : a = b₀
      · exact Or.inl hab
      · exact Or.inr ⟨haC, fun haS => ha ⟨hab, haS⟩⟩
  · intro b hb b' hb'C hb'
    rw [mem_erase] at hb
    by_cases h : b' = b₀
    · subst h
      have hle := hmin b hb.2
      have hne : ord b' ≠ ord b := fun heq => hb.1 (hord (hSC hb.2) hb'C heq.symm)
      omega
    · exact hseg b hb.2 b' hb'C (fun hS' => hb' (mem_erase.mpr ⟨h, hS'⟩))
  · intro a haC hle
    by_cases hab : a = b₀
    · rw [hab]
      exact mem_insert_self _ _
    · refine mem_insert_of_mem (mem_sdiff.mpr ⟨haC, fun haS => ?_⟩)
      have heq : ord a = ord b₀ := le_antisymm hle (hmin a haS)
      exact hab (hord haC (hSC hb₀) heq)

/-- **Sequential upper bound** (Step 5 of `lem:extraction-rows`). Let the weights `φ_b`
(`b ∈ C`) be nonnegative, `φ_b(y)` depending only on the labels of `b` and of the earlier
vertices, and let `∑_{c ∈ Φ_b(x')} φ_b(x'[b ↦ c]) ≤ M_b` for every `x'` feasible on the earlier
vertices. If every completion count of a feasible labelling of `C` is at most `K`, then for every
final segment `S` of `C` and `x'` feasible on `C \ S`,
`∑_{y ⊇ x'|_{C \ S}} ∏_{b ∈ S} φ_b(y) ≤ K ∏_{b ∈ S} M_b`. -/
theorem coverRow_seq_upper (G : OrientedGraph U) {C : Finset U} {ord : U → ℕ}
    (hord : Set.InjOn ord C) (φ : U → (U → F) → ℝ) (M : U → ℝ) (K : ℝ) (hφ0 : ∀ b y, 0 ≤ φ b y)
    (hM0 : ∀ b, 0 ≤ M b) (hK0 : 0 ≤ K)
    (hloc : ∀ b ∈ C, ∀ y y' : U → F, (∀ a ∈ C, ord a ≤ ord b → y a = y' a) → φ b y = φ b y')
    (hstep : ∀ b ∈ C, ∀ x' : U → F, Feasible F G (coverRowEarlier C ord b) x' →
      ∑ c ∈ vertexAdmissible G (coverRowEarlier C ord b) x' b, φ b (Function.update x' b c) ≤
        M b)
    (hK : ∀ y : U → F, Feasible F G C y → (extCount G C y : ℝ) ≤ K) :
    ∀ (k : ℕ) (S : Finset U), S.card = k → S ⊆ C →
      (∀ b ∈ S, ∀ b' ∈ C, b' ∉ S → ord b' < ord b) → ∀ x' : U → F, Feasible F G (C \ S) x' →
        coverRowExtSum G (C \ S) x' (fun y => ∏ b ∈ S, φ b y) ≤ K * ∏ b ∈ S, M b := by
  intro k
  induction k with
  | zero =>
    intro S hS _ _ x' hx'
    rw [card_eq_zero] at hS
    subst hS
    simp only [prod_empty, sdiff_empty, mul_one]
    rw [sdiff_empty] at hx'
    rw [coverRowExtSum_one]
    exact hK x' hx'
  | succ k ih =>
    intro S hS hSC hseg x' hx'
    have hSne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨b₀, hb₀, hearl, hins, hseg', hloc'⟩ := coverRow_first hord hSC hseg hSne
    have hb₀A : b₀ ∉ C \ S := fun h => (mem_sdiff.mp h).2 hb₀
    rw [coverRowExtSum_insert G x' hb₀A]
    have hterm : ∀ c ∈ vertexAdmissible G (C \ S) x' b₀,
        coverRowExtSum G (insert b₀ (C \ S)) (Function.update x' b₀ c)
            (fun y => ∏ b ∈ S, φ b y) ≤
          φ b₀ (Function.update x' b₀ c) * (K * ∏ b ∈ S.erase b₀, M b) := by
      intro c hc
      have hfeas : Feasible F G (insert b₀ (C \ S)) (Function.update x' b₀ c) :=
        feasible_insert hx' hb₀A hc
      have heq : coverRowExtSum G (insert b₀ (C \ S)) (Function.update x' b₀ c)
            (fun y => ∏ b ∈ S, φ b y) =
          φ b₀ (Function.update x' b₀ c) * coverRowExtSum G (insert b₀ (C \ S))
            (Function.update x' b₀ c) (fun y => ∏ b ∈ S.erase b₀, φ b y) := by
        unfold coverRowExtSum
        rw [mul_sum]
        refine sum_congr rfl fun y hy => ?_
        beta_reduce
        rw [← mul_prod_erase S _ hb₀]
        congr 1
        apply hloc b₀ (hSC hb₀)
        intro a haC hle
        exact (mem_filter.mp hy).2 a (hloc' a haC hle)
      rw [heq]
      refine mul_le_mul_of_nonneg_left ?_ (hφ0 _ _)
      rw [hins] at hfeas ⊢
      exact ih (S.erase b₀) (by rw [card_erase_of_mem hb₀]; omega)
        ((erase_subset _ _).trans hSC) hseg' _ hfeas
    calc ∑ c ∈ vertexAdmissible G (C \ S) x' b₀, coverRowExtSum G (insert b₀ (C \ S))
            (Function.update x' b₀ c) (fun y => ∏ b ∈ S, φ b y)
        ≤ ∑ c ∈ vertexAdmissible G (C \ S) x' b₀,
            φ b₀ (Function.update x' b₀ c) * (K * ∏ b ∈ S.erase b₀, M b) := sum_le_sum hterm
      _ = (∑ c ∈ vertexAdmissible G (C \ S) x' b₀, φ b₀ (Function.update x' b₀ c)) *
            (K * ∏ b ∈ S.erase b₀, M b) := by rw [sum_mul]
      _ ≤ M b₀ * (K * ∏ b ∈ S.erase b₀, M b) := by
          refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hK0 (prod_nonneg fun b _ => hM0 b))
          rw [hearl] at hx' ⊢
          exact hstep b₀ (hSC hb₀) x' hx'
      _ = K * ∏ b ∈ S, M b := by rw [← mul_prod_erase S M hb₀]; ring

/-- **Sequential lower count** (Step 2 of `lem:extraction-rows`): if every admissible set
`Φ_b(x')` of a vertex `b ∈ C` given labels `x'` of the earlier vertices has at least `ℓ_b ≥ 0`
elements, and every feasible labelling of `C` has at least `L ≥ 0` completions, then
`extCount(C \ S, x') ≥ L ∏_{b ∈ S} ℓ_b` for every final segment `S` of `C`. -/
theorem coverRow_seq_lower (G : OrientedGraph U) {C : Finset U} {ord : U → ℕ}
    (hord : Set.InjOn ord C) (ℓ : U → ℝ) (L : ℝ) (hℓ0 : ∀ b, 0 ≤ ℓ b) (hL0 : 0 ≤ L)
    (hstep : ∀ b ∈ C, ∀ x' : U → F, Feasible F G (coverRowEarlier C ord b) x' →
      ℓ b ≤ (vertexAdmissible G (coverRowEarlier C ord b) x' b).card)
    (hL : ∀ y : U → F, Feasible F G C y → L ≤ extCount G C y) :
    ∀ (k : ℕ) (S : Finset U), S.card = k → S ⊆ C →
      (∀ b ∈ S, ∀ b' ∈ C, b' ∉ S → ord b' < ord b) → ∀ x' : U → F, Feasible F G (C \ S) x' →
        L * ∏ b ∈ S, ℓ b ≤ extCount G (C \ S) x' := by
  intro k
  induction k with
  | zero =>
    intro S hS _ _ x' hx'
    rw [card_eq_zero] at hS
    subst hS
    rw [sdiff_empty] at hx' ⊢
    simpa using hL x' hx'
  | succ k ih =>
    intro S hS hSC hseg x' hx'
    have hSne : S.Nonempty := card_pos.mp (by omega)
    obtain ⟨b₀, hb₀, hearl, hins, hseg', -⟩ := coverRow_first hord hSC hseg hSne
    have hb₀A : b₀ ∉ C \ S := fun h => (mem_sdiff.mp h).2 hb₀
    have hrec : (extCount G (C \ S) x' : ℝ) = ∑ c ∈ vertexAdmissible G (C \ S) x' b₀,
        (extCount G (insert b₀ (C \ S)) (Function.update x' b₀ c) : ℝ) := by
      exact_mod_cast extCount_insert G x' hb₀A
    rw [hrec]
    have hterm : ∀ c ∈ vertexAdmissible G (C \ S) x' b₀, L * ∏ b ∈ S.erase b₀, ℓ b ≤
        (extCount G (insert b₀ (C \ S)) (Function.update x' b₀ c) : ℝ) := by
      intro c hc
      have hfeas := feasible_insert hx' hb₀A hc
      rw [hins] at hfeas ⊢
      exact ih _ (by rw [card_erase_of_mem hb₀]; omega) ((erase_subset _ _).trans hSC) hseg' _
        hfeas
    have hcard : ℓ b₀ ≤ (vertexAdmissible G (C \ S) x' b₀).card := by
      rw [hearl] at hx' ⊢
      exact hstep b₀ (hSC hb₀) x' hx'
    calc L * ∏ b ∈ S, ℓ b = ℓ b₀ * (L * ∏ b ∈ S.erase b₀, ℓ b) := by
          rw [← mul_prod_erase S ℓ hb₀]; ring
      _ ≤ (vertexAdmissible G (C \ S) x' b₀).card * (L * ∏ b ∈ S.erase b₀, ℓ b) :=
          mul_le_mul_of_nonneg_right hcard (mul_nonneg hL0 (prod_nonneg fun b _ => hℓ0 b))
      _ = ∑ c ∈ vertexAdmissible G (C \ S) x' b₀, L * ∏ b ∈ S.erase b₀, ℓ b := by
          rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum hterm

end Sequential

/-! ## One-step bounds and completion ratios (Steps 1 and 2) -/

section Steps

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `r² = q⁻¹` for `q > 0`. -/
theorem coverRow_r_sq {q : ℝ} (hq : 0 < q) : (Real.sqrt q)⁻¹ ^ 2 = q⁻¹ := by
  rw [inv_pow, Real.sq_sqrt hq.le]

/-- `𝔈_t + 2^t n ≤ q e_t(q, n)`: the graded errors are at most the coarse one
(`it:et:compare`), `q e^+_t + 2^t n = q e^-_t(n) ≤ q e_t(q, n)`. -/
theorem coverRow_softError_le {q : ℝ} (hq : 1 ≤ q) (n t : ℕ) :
    softError q t + 2 ^ t * n ≤ q * coarseError t q n := by
  have hq0 : 0 < q := by linarith
  have h1 : q * (1 + upperError t q) = q + softError q t := by
    rw [mul_one_add_upperError hq0]
    rfl
  have h2 := upperError_le_coarseError hq (le_refl (0 : ℝ)) t
  have h3 : q * coarseError t q n = q * coarseError t q 0 + 2 ^ t * n := by
    unfold coarseError
    rw [coverRow_r_sq hq0]
    field_simp
    ring
  have h4 : softError q t = q * upperError t q := by linarith
  rw [h3, h4]
  have := mul_le_mul_of_nonneg_left h2 hq0.le
  linarith

/-- The one-step bounds in coarse form: `q 2^{-t}(1 - e_t(q, n)) ≤ stepLower` and
`stepUpper ≤ q 2^{-t}(1 + e_t(q, n))`. -/
theorem coverRow_step_bounds {q : ℝ} (hq : 1 ≤ q) (n t : ℕ) :
    q / 2 ^ t * (1 - coarseError t q n) ≤ stepLower q n t ∧
      stepUpper q t ≤ q / 2 ^ t * (1 + coarseError t q n) := by
  have h := coverRow_softError_le hq n t
  have hpos : (0 : ℝ) < 2 ^ t := by positivity
  have hn : (0 : ℝ) ≤ 2 ^ t * n := by positivity
  constructor
  · unfold stepLower
    refine le_max_of_le_right ?_
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    linarith
  · unfold stepUpper
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right hpos]
    linarith

theorem coverRow_nbrCount_le (G : OrientedGraph U) (A : Finset U) (v : U) :
    nbrCount G A v ≤ rowsDeg0 G v := by
  unfold nbrCount rowsDeg0 rowsAdj
  exact card_le_card (filter_subset_filter _ (subset_univ A))

/-- **Completion ratios** (the content of `lem:graphs:vertex`(subset) used in Step 1): along any
ordering `l`, `upperProd(A, l) ≤ ∏_{i ∈ l} (1 + e_{d⁰_i})/(1 - e_{d⁰_i}) · lowerProd(A, l)` and
`lowerProd(A, l) > 0`, when every `e_{d⁰_i}(q, n) < 1`. -/
theorem coverRow_upperProd_le {q : ℝ} (hq : 1 ≤ q) {n : ℕ} (G : OrientedGraph U)
    (hS1 : ∀ i, coarseError (rowsDeg0 G i) q n < 1) :
    ∀ (l : List U) (A : Finset U), upperProd G q A l ≤
        (l.map fun i => (1 + coarseError (rowsDeg0 G i) q n) /
          (1 - coarseError (rowsDeg0 G i) q n)).prod * lowerProd G q n A l ∧
      0 < lowerProd G q n A l
  | [], A => by simp [upperProd, lowerProd]
  | v :: l, A => by
      obtain ⟨ih1, ih2⟩ := coverRow_upperProd_le hq G hS1 l (insert v A)
      have hq0 : 0 < q := by linarith
      set t := nbrCount G A v
      set d := rowsDeg0 G v
      have htd : t ≤ d := coverRow_nbrCount_le G A v
      have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      have het : coarseError t q n ≤ coarseError d q n := coarseError_mono hn0 htd
      have he0 : 0 ≤ coarseError t q n := coarseError_nonneg hn0 t
      have hd1 := hS1 v
      obtain ⟨hlo, hup⟩ := coverRow_step_bounds hq n t
      have hpos : (0 : ℝ) < q / 2 ^ t := by positivity
      have hsL : 0 < stepLower q n t := lt_of_lt_of_le (mul_pos hpos (by linarith)) hlo
      have hsU : 0 ≤ stepUpper q t := by
        unfold stepUpper
        exact div_nonneg (add_nonneg hq0.le (softError_nonneg _ _)) (by positivity)
      have hratio : stepUpper q t ≤ (1 + coarseError d q n) / (1 - coarseError d q n) *
          stepLower q n t := by
        have hden : 0 < 1 - coarseError d q n := by linarith
        calc stepUpper q t ≤ q / 2 ^ t * (1 + coarseError t q n) := hup
          _ ≤ q / 2 ^ t * (1 + coarseError d q n) :=
              mul_le_mul_of_nonneg_left (by linarith) hpos.le
          _ = (1 + coarseError d q n) / (1 - coarseError d q n) *
                (q / 2 ^ t * (1 - coarseError d q n)) := by
              field_simp
          _ ≤ (1 + coarseError d q n) / (1 - coarseError d q n) *
                (q / 2 ^ t * (1 - coarseError t q n)) := by
              refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (by linarith) hden.le)
              exact mul_le_mul_of_nonneg_left (by linarith) hpos.le
          _ ≤ (1 + coarseError d q n) / (1 - coarseError d q n) * stepLower q n t :=
              mul_le_mul_of_nonneg_left hlo (div_nonneg (by linarith) hden.le)
      have hU' := upperProd_nonneg G hq0.le l (insert v A)
      simp only [upperProd, lowerProd, List.map_cons, List.prod_cons]
      refine ⟨?_, mul_pos hsL ih2⟩
      calc stepUpper q t * upperProd G q (insert v A) l
          ≤ ((1 + coarseError d q n) / (1 - coarseError d q n) * stepLower q n t) *
              ((l.map fun i => (1 + coarseError (rowsDeg0 G i) q n) /
                (1 - coarseError (rowsDeg0 G i) q n)).prod * lowerProd G q n (insert v A) l) :=
            mul_le_mul hratio ih1 hU' (mul_nonneg (div_nonneg (by linarith) (by linarith)) hsL.le)
        _ = _ := by ring

end Steps

/-! ## Merge weights (Step 3) -/

section MergeWeights

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `ω_b(z) = ∏_{a ∈ H_b} (1 + χ(ς_{ab}(z - x_a))) · 2^{∑_i c^U(i,b) 1[z = x_i]}`. -/
noncomputable def coverRowOmega (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U))
    (x : U → F) (b : U) (z : F) : ℝ :=
  (∏ a ∈ coverRowH H b, (1 + (quadraticChar F ((ς a b : F) * (z - x a)) : ℝ))) *
    2 ^ (∑ i, if z = x i then rowsCU G ς i b else 0)

/-- `∑_j mg(j, b) 1[z = x_j]`, the merge count `mg(j, b)` of a label `z = x_j`. -/
def coverRowMgAt (G : OrientedGraph U) (ς : U → U → ℤ) (x : U → F) (b : U) (z : F) : ℕ :=
  ∑ j, if z = x j then rowsMg G ς j b else 0

/-- `ω̂_b(z) = ω_b(z) 2^{mg(j, b)}` if `z = x_j`, and `ω̂_b(z) = ω_b(z)` if `z ∉ x(U⁺)` (for
injective `x`). -/
noncomputable def coverRowOmegaHat (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U))
    (x : U → F) (b : U) (z : F) : ℝ :=
  coverRowOmega G ς H x b z * 2 ^ coverRowMgAt G ς x b z

/-- The number `μ_b(y)` of merges at `b`: pairs `(b', a)` with `b'` a `G⁺`-neighbour of `b`
earlier in `C`, `a ∈ H_b` and `y_{b'} = x_a`. -/
def coverRowMerges (G : OrientedGraph U) (C : Finset U) (ord : U → ℕ) (H : Finset (U × U))
    (x y : U → F) (b : U) : ℕ :=
  ∑ b' ∈ (coverRowEarlier C ord b).filter (fun b' => (b', b) ∈ G.E ∨ (b, b') ∈ G.E),
    ∑ a ∈ coverRowH H b, if y b' = x a then 1 else 0

/-- `φ_b(y) = ω̂_b(y_b) 2^{-μ_b(y)}`. -/
noncomputable def coverRowPhi (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (x : U → F) (b : U) (y : U → F) : ℝ :=
  coverRowOmegaHat G ς H x b (y b) * ((2 : ℝ) ^ coverRowMerges G C ord H x y b)⁻¹

theorem coverRow_one_add_chi (z : F) :
    0 ≤ 1 + (quadraticChar F z : ℝ) ∧ 1 + (quadraticChar F z : ℝ) ≤ 2 := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rcases quadraticChar_dichotomy hz with h | h <;> rw [h] <;> norm_num

theorem coverRow_omega_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U))
    (x : U → F) (b : U) (z : F) : 0 ≤ coverRowOmega G ς H x b z :=
  mul_nonneg (prod_nonneg fun _ _ => (coverRow_one_add_chi _).1) (by positivity)

theorem coverRow_omegaHat_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U))
    (x : U → F) (b : U) (z : F) : 0 ≤ coverRowOmegaHat G ς H x b z :=
  mul_nonneg (coverRow_omega_nonneg G ς H x b z) (by positivity)

theorem coverRow_phi_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) (x : U → F) (b : U) (y : U → F) :
    0 ≤ coverRowPhi G ς C ord H x b y :=
  mul_nonneg (coverRow_omegaHat_nonneg G ς H x b _) (by positivity)

/-- `Π(c') = ∏_{b ∈ C} ω_b(c'_b)`. -/
theorem coverRowIntegrand_eq_prod (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U)
    (H : Finset (U × U)) (hHC : ∀ e ∈ H, e.2 ∈ C) (x y : U → F) :
    coverRowIntegrand G ς C H x y = ∏ b ∈ C, coverRowOmega G ς H x b (y b) := by
  unfold coverRowIntegrand coverRowOmega coverRowKappa
  rw [prod_mul_distrib, prod_pow_eq_pow_sum]
  congr 1
  apply prod_finset_product_right H C (fun b => coverRowH H b)
  intro p
  simp only [coverRowH, mem_filter, mem_univ, true_and]
  constructor
  · intro hp
    exact ⟨hHC p hp, hp⟩
  · rintro ⟨_, hp⟩
    exact hp

omit [Field F] [Fintype F] in
/-- **Step 3, the merge count**: `∑_{b ∈ C} μ_b(y) ≤ ∑_{b ∈ C} mg(j(b), b)`, the sum over the
coincident `b` (`y_b = x_{j(b)}`); `H_b ⊆ N(b)` since `H ⊆ E_×`. -/
theorem coverRow_merges_le (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) (hHς : ∀ e ∈ H, ς e.1 e.2 ≠ 0) (x y : U → F) :
    ∑ b ∈ C, coverRowMerges G C ord H x y b ≤ ∑ b ∈ C, coverRowMgAt G ς x b (y b) := by
  set T : U → U → U → ℕ := fun b' b a =>
    if ((b', b) ∈ G.E ∨ (b, b') ∈ G.E) ∧ ς a b ≠ 0 ∧ y b' = x a then 1 else 0 with hT
  have ha : ∀ b, coverRowMerges G C ord H x y b ≤ ∑ b' ∈ C, ∑ a, T b' b a := by
    intro b
    unfold coverRowMerges
    calc ∑ b' ∈ (coverRowEarlier C ord b).filter (fun b' => (b', b) ∈ G.E ∨ (b, b') ∈ G.E),
          ∑ a ∈ coverRowH H b, (if y b' = x a then 1 else 0)
        = ∑ b' ∈ (coverRowEarlier C ord b).filter (fun b' => (b', b) ∈ G.E ∨ (b, b') ∈ G.E),
          ∑ a ∈ coverRowH H b, T b' b a := by
          refine sum_congr rfl fun b' hb' => sum_congr rfl fun a ha => ?_
          have hadj := (mem_filter.mp hb').2
          have hς' : ς a b ≠ 0 := hHς (a, b) (by simpa [coverRowH] using ha)
          simp only [hT, hadj, hς', ne_eq, not_false_eq_true, true_and]
      _ ≤ ∑ b' ∈ (coverRowEarlier C ord b).filter (fun b' => (b', b) ∈ G.E ∨ (b, b') ∈ G.E),
          ∑ a, T b' b a :=
          sum_le_sum fun b' _ => sum_le_sum_of_subset (subset_univ _)
      _ ≤ ∑ b' ∈ C, ∑ a, T b' b a :=
          sum_le_sum_of_subset ((filter_subset _ _).trans (filter_subset _ _))
  have hc : ∀ b' a, ∑ b, T b' b a = if y b' = x a then rowsMg G ς a b' else 0 := by
    intro b' a
    split_ifs with hy
    · unfold rowsMg rowsAdj rowsN
      rw [filter_filter, card_filter]
      refine sum_congr rfl fun b _ => ?_
      simp only [hT, hy, mem_filter, mem_univ, true_and, and_true, ne_eq]
      by_cases h1 : (b', b) ∈ G.E ∨ (b, b') ∈ G.E
      · have h1' : (b, b') ∈ G.E ∨ (b', b) ∈ G.E := h1.symm
        simp only [h1, h1', true_and]
      · have h1' : ¬((b, b') ∈ G.E ∨ (b', b) ∈ G.E) := fun h => h1 h.symm
        simp only [h1, h1', false_and, ↓reduceIte]
    · refine sum_eq_zero fun b _ => ?_
      simp only [hT, hy, and_false, ↓reduceIte]
  calc ∑ b ∈ C, coverRowMerges G C ord H x y b ≤ ∑ b ∈ C, ∑ b' ∈ C, ∑ a, T b' b a :=
        sum_le_sum fun b _ => ha b
    _ = ∑ b' ∈ C, ∑ b ∈ C, ∑ a, T b' b a := sum_comm
    _ ≤ ∑ b' ∈ C, ∑ b, ∑ a, T b' b a :=
        sum_le_sum fun b' _ => sum_le_sum_of_subset (subset_univ _)
    _ = ∑ b' ∈ C, ∑ a, ∑ b, T b' b a := sum_congr rfl fun b' _ => sum_comm
    _ = ∑ b' ∈ C, coverRowMgAt G ς x b' (y b') := by
        refine sum_congr rfl fun b' _ => ?_
        unfold coverRowMgAt
        exact sum_congr rfl fun a _ => hc b' a

/-- **Step 3**: `Π(c') ≤ ∏_{b ∈ C} ω̂_b(c'_b) 2^{-μ_b(c'_{<b})}`. -/
theorem coverRow_integrand_le (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U)
    (ord : U → ℕ) (H : Finset (U × U)) (hH : ∀ e ∈ H, e.2 ∈ C ∧ ς e.1 e.2 ≠ 0) (x y : U → F) :
    coverRowIntegrand G ς C H x y ≤ ∏ b ∈ C, coverRowPhi G ς C ord H x b y := by
  rw [coverRowIntegrand_eq_prod G ς C H (fun e he => (hH e he).1) x y]
  unfold coverRowPhi coverRowOmegaHat
  rw [prod_mul_distrib, prod_mul_distrib, prod_inv_distrib, prod_pow_eq_pow_sum,
    prod_pow_eq_pow_sum]
  have hle := coverRow_merges_le G ς C ord H (fun e he => (hH e he).2) x y
  have hω : 0 ≤ ∏ b ∈ C, coverRowOmega G ς H x b (y b) :=
    prod_nonneg fun b _ => coverRow_omega_nonneg G ς H x b _
  have h2 : (1 : ℝ) ≤ 2 ^ (∑ b ∈ C, coverRowMgAt G ς x b (y b)) *
      ((2 : ℝ) ^ (∑ b ∈ C, coverRowMerges G C ord H x y b))⁻¹ := by
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), one_mul]
    exact pow_le_pow_right₀ (by norm_num) hle
  calc ∏ b ∈ C, coverRowOmega G ς H x b (y b)
      = (∏ b ∈ C, coverRowOmega G ς H x b (y b)) * 1 := (mul_one _).symm
    _ ≤ (∏ b ∈ C, coverRowOmega G ς H x b (y b)) * (2 ^ (∑ b ∈ C, coverRowMgAt G ς x b (y b)) *
          ((2 : ℝ) ^ (∑ b ∈ C, coverRowMerges G C ord H x y b))⁻¹) :=
        mul_le_mul_of_nonneg_left h2 hω
    _ = _ := by ring

end MergeWeights

/-! ## The one-vertex bound (Step 4, `eq:extraction:onevertex`) -/

section OneVertex

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]}` as a real number. -/
theorem coverRow_two_zpow_exp (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U))
    (j b : U) : (2 : ℝ) ^ coverRowExp G ς H j b =
      2 ^ (rowsMg G ς j b + rowsCU G ς j b) * if j ∈ coverRowH H b then (2 : ℝ)⁻¹ else 1 := by
  unfold coverRowExp
  split_ifs
  · rw [zpow_sub₀ two_ne_zero, zpow_natCast, zpow_one, div_eq_mul_inv]
  · rw [sub_zero, zpow_natCast, mul_one]

/-- At a label `x_j`: `ω̂_b(x_j) ≤ 2^{h_b} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]}`; the factor of
`a = j` is `1 + χ(0) = 1` and `x` is injective. -/
theorem coverRow_omegaHat_at_le (G : OrientedGraph U) (ς : U → U → ℤ) (H : Finset (U × U))
    (x : U → F) (hx : Function.Injective x) (b j : U) :
    coverRowOmegaHat G ς H x b (x j) ≤
      2 ^ (coverRowH H b).card * (2 : ℝ) ^ coverRowExp G ς H j b := by
  rw [coverRow_two_zpow_exp]
  unfold coverRowOmegaHat coverRowOmega coverRowMgAt
  simp only [hx.eq_iff, sum_ite_eq, mem_univ, ↓reduceIte]
  have hg0 : ∀ a ∈ coverRowH H b,
      0 ≤ 1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ) :=
    fun a _ => (coverRow_one_add_chi _).1
  have hg2 : ∀ a ∈ coverRowH H b,
      1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ) ≤ 2 :=
    fun a _ => (coverRow_one_add_chi _).2
  have hP : (∏ a ∈ coverRowH H b, (1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ))) ≤
      2 ^ (coverRowH H b).card * if j ∈ coverRowH H b then (2 : ℝ)⁻¹ else 1 := by
    split_ifs with hj
    · rw [← mul_prod_erase _ _ hj]
      simp only [sub_self, mul_zero, quadraticChar_zero, Int.cast_zero, add_zero, one_mul]
      have hcard : (coverRowH H b).card = ((coverRowH H b).erase j).card + 1 := by
        rw [card_erase_of_mem hj]
        have := card_pos.mpr ⟨j, hj⟩
        omega
      rw [hcard, pow_succ, mul_assoc, mul_inv_cancel₀ two_ne_zero, mul_one]
      calc ∏ a ∈ (coverRowH H b).erase j,
            (1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ))
          ≤ ∏ _a ∈ (coverRowH H b).erase j, (2 : ℝ) :=
            prod_le_prod₀ (fun a ha => hg0 a (mem_of_mem_erase ha))
              (fun a ha => hg2 a (mem_of_mem_erase ha))
        _ = 2 ^ ((coverRowH H b).erase j).card := prod_const 2
    · rw [mul_one]
      calc ∏ a ∈ coverRowH H b, (1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ))
          ≤ ∏ _a ∈ coverRowH H b, (2 : ℝ) := prod_le_prod₀ hg0 hg2
        _ = 2 ^ (coverRowH H b).card := prod_const 2
  have hpos : (0 : ℝ) ≤ 2 ^ rowsCU G ς j b * 2 ^ rowsMg G ς j b := by positivity
  calc (∏ a ∈ coverRowH H b, (1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ))) *
        2 ^ rowsCU G ς j b * 2 ^ rowsMg G ς j b
      = (∏ a ∈ coverRowH H b, (1 + (quadraticChar F ((ς a b : F) * (x j - x a)) : ℝ))) *
          (2 ^ rowsCU G ς j b * 2 ^ rowsMg G ς j b) := by ring
    _ ≤ (2 ^ (coverRowH H b).card * if j ∈ coverRowH H b then (2 : ℝ)⁻¹ else 1) *
          (2 ^ rowsCU G ς j b * 2 ^ rowsMg G ς j b) := mul_le_mul_of_nonneg_right hP hpos
    _ = _ := by rw [pow_add]; ring

/-- **`eq:extraction:onevertex`** (Step 4 of `lem:extraction-rows`). Fix `b` and labels `x'` of
the vertices of `C` earlier than `b` (feasible there), and let `Adm_b = Φ_b(x')` be the labels
distinct from the earlier ones satisfying the `t_b` constraints of `G⁺` with the earlier
neighbours of `b`. Then
`∑_{y ∈ Adm_b} ω̂_b(y) 2^{-μ_b} ≤ q 2^{-t_b}(1 + e_{s_b}(q, 2n) + r² 2^{s_b}
∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`. The labels `y ∉ x(U⁺)` are counted by
`lem:extraction-merged-count` (`merged_count_le_fintype'`), with the `μ_b` merges; the labels
`y = x_j` by `coverRow_omegaHat_at_le`. `WeilBound F` is Weil's theorem (literature input). -/
theorem coverRows_oneVertex (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) (hHς : ∀ e ∈ H, ς e.1 e.2 ≠ 0) (x : U → F) (hx : Function.Injective x)
    (n : ℕ) (b : U) (x' : U → F) (hx' : Feasible F G (coverRowEarlier C ord b) x') :
    ∑ y ∈ vertexAdmissible G (coverRowEarlier C ord b) x' b,
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ coverRowMerges G C ord H x x' b)⁻¹ ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
        (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n) +
          (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
            ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) := by
  set A := coverRowEarlier C ord b with hA
  set Hb := coverRowH H b with hHb
  set μ := coverRowMerges G C ord H x x' b with hμ
  set X : Finset F := univ.image x with hX
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hμinv0 : (0 : ℝ) ≤ ((2 : ℝ) ^ μ)⁻¹ := by positivity
  have hμinv1 : ((2 : ℝ) ^ μ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  rw [← sum_filter_add_sum_filter_not (vertexAdmissible G A x' b) (fun y => y ∈ X)]
  -- the labels `x_j`
  have hii : ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
      coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ ≤
        ∑ j, 2 ^ Hb.card * (2 : ℝ) ^ coverRowExp G ς H j b := by
    calc ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
          coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹
        ≤ ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
            coverRowOmegaHat G ς H x b y :=
          sum_le_sum fun y _ => mul_le_of_le_one_right (coverRow_omegaHat_nonneg G ς H x b y)
            hμinv1
      _ ≤ ∑ y ∈ X, coverRowOmegaHat G ς H x b y :=
          sum_le_sum_of_subset_of_nonneg (fun y hy => (mem_filter.mp hy).2)
            (fun y _ _ => coverRow_omegaHat_nonneg G ς H x b y)
      _ = ∑ j, coverRowOmegaHat G ς H x b (x j) := sum_image fun j _ k _ h => hx h
      _ ≤ _ := sum_le_sum fun j _ => coverRow_omegaHat_at_le G ς H x hx b j
  -- the other labels: `lem:extraction-merged-count`
  set NA := A.filter (fun u => (u, b) ∈ G.E ∨ (b, u) ∈ G.E) with hNA
  let β : NA → F := fun u => x' u
  have hβ : Function.Injective β := fun u w h =>
    Subtype.ext (hx'.1 u (mem_filter.mp u.2).1 w (mem_filter.mp w.2).1 h)
  let γ : Hb → F := fun a => x a
  have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hx h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun u => if (u.1, b) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Hb → ℤ := fun a => quadraticChar F (ς a.1 b : F)
  have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
    have ha : ς a.1 b ≠ 0 := hHς (a.1, b) (by simpa [hHb, coverRowH] using a.2)
    rcases hς a.1 b with h | h | h
    · exact absurd h ha
    · left
      simp [s', h]
    · simp only [s', h, Int.cast_neg, Int.cast_one]
      exact hm1
  set 𝒳 : Finset F := A.image x' ∪ X with h𝒳
  have hβX : ∀ u, β u ∈ 𝒳 := fun u =>
    mem_union_left _ (mem_image_of_mem x' (mem_filter.mp u.2).1)
  have hγX : ∀ a, γ a ∈ 𝒳 := fun a => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype' hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
    (n' := 2 * (n : ℝ)) (by positivity)
  have hset : (vertexAdmissible G A x' b).filter (fun y => y ∉ X) =
      univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun u => ?_⟩
      have hu := (mem_filter.mp u.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin u (mem_filter.mp u.2).1 h
      · have hvu : (b, u.1) ∈ G.E := hu.resolve_left h
        have h1 := hout u (mem_filter.mp u.2).1 hvu
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun u hu he => ?_, fun u hu he => ?_⟩, hcX⟩
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inl he⟩
        have := hall ⟨u, hmem⟩
        simpa [s, β, he] using this
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inr he⟩
        have hnot : (u, b) ∉ G.E := G.oriented b u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      coverRowOmegaHat G ς H x b y = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) := by
    intro y hy
    have hyX : y ∉ X := fun h => (mem_filter.mp hy).2.1 (mem_union_right _ h)
    have hne : ∀ i, y ≠ x i := fun i h => hyX (h ▸ mem_image_of_mem x (mem_univ i))
    unfold coverRowOmegaHat coverRowOmega coverRowMgAt
    simp only [hne, ↓reduceIte, sum_const_zero, pow_zero, mul_one]
    rw [← prod_coe_sort Hb]
    refine prod_congr rfl fun a _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = coverRowT G C ord b := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Hb = Hb.card := Fintype.card_coe _
  have hmerge : mergedCount β γ = μ := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Hb => β il.1 = γ il.2).card
        = ∑ il : NA × Hb, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ u : NA, ∑ a : Hb, if β u = γ a then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ u : NA, ∑ a ∈ Hb, if x' u = x a then 1 else 0 :=
          sum_congr rfl fun u _ => sum_coe_sort Hb (fun a => if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, ∑ a ∈ Hb, if x' u = x a then 1 else 0 :=
          sum_coe_sort NA (fun u => ∑ a ∈ Hb, if x' u = x a then 1 else 0)
      _ = μ := rfl
  have hS : coverRowS G C ord H b = coverRowT G C ord b + Hb.card := rfl
  have hi : ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∉ X),
      coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ ≤
        Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
          (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n)) := by
    rw [← sum_mul, hset, sum_congr rfl hsummand]
    rw [hcardι, hcardκ, hmerge, ← hS] at hmc
    calc (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) * ((2 : ℝ) ^ μ)⁻¹
        ≤ (Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ μ *
            (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n))) *
            ((2 : ℝ) ^ μ)⁻¹ := mul_le_mul_of_nonneg_right hmc hμinv0
      _ = _ := by field_simp
  have hid : (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
      ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) =
      ∑ j, 2 ^ Hb.card * (2 : ℝ) ^ coverRowExp G ς H j b := by
    rw [coverRow_r_sq hq0, ← mul_sum, hS, pow_add]
    have h2 : (2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ coverRowT G C ord b = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
    calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
          ((Fintype.card F : ℝ)⁻¹ * (2 ^ coverRowT G C ord b * 2 ^ Hb.card) *
            ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b)
        = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹) *
            ((2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ coverRowT G C ord b) *
            (2 ^ Hb.card * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hq0.ne', h2, one_mul, one_mul]
  calc ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∈ X),
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ +
      ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∉ X),
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹
      ≤ ∑ j, 2 ^ Hb.card * (2 : ℝ) ^ coverRowExp G ς H j b +
          Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
            (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n)) :=
        add_le_add hii hi
    _ = _ := by rw [← hid]; ring

end OneVertex

/-! ## Cover rows (`lem:extraction-rows`) -/

section Main

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `E_{λ_p(G)} f = |Inj_p(G)|⁻¹ ∑_{y ∈ Inj_p(G)} f(y)`. -/
theorem coverRow_expect_graphLaw (G : OrientedGraph U) (hne : (injLabellings F G).Nonempty)
    (f : (U → F) → ℝ) :
    (graphLaw G hne).expect f = (∑ y ∈ injLabellings F G, f y) / (injLabellings F G).card := by
  unfold FiniteLaw.expect graphLaw
  simp only [ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, ← mul_sum]
  ring

theorem coverRowIntegrand_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U)
    (H : Finset (U × U)) (x c' : U → F) : 0 ≤ coverRowIntegrand G ς C H x c' :=
  mul_nonneg (prod_nonneg fun _ _ => (coverRow_one_add_chi _).1) (by positivity)

/-- The integrand reads `c'` only on `C`. -/
theorem coverRowIntegrand_congr (G : OrientedGraph U) (ς : U → U → ℤ) (C : Finset U)
    (H : Finset (U × U)) (hHC : ∀ e ∈ H, e.2 ∈ C) (x : U → F) {c' c'' : U → F}
    (h : ∀ b ∈ C, c' b = c'' b) :
    coverRowIntegrand G ς C H x c' = coverRowIntegrand G ς C H x c'' := by
  unfold coverRowIntegrand coverRowKappa
  congr 1
  · exact prod_congr rfl fun e he => by rw [h e.2 (hHC e he)]
  · congr 1
    exact sum_congr rfl fun b hb => by rw [h b hb]

/-- **`lem:extraction-rows`, over `μ`.** The expectation over `x' ∼ μ = λ_p(G⁺)` of the
integrand `Π(x'_C)` (`coverRowIntegrand`, a function of `x'_C`) is at most
`R_{U⁺ \ C} ∏_{b ∈ C} F_b(H)`. -/
theorem coverRows_le_graphLaw (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1)
    (C : Finset U) (ord : U → ℕ) (hord : Set.InjOn ord C) (x : U → F)
    (hx : Function.Injective x) (H : Finset (U × U)) (hH : ∀ e ∈ H, e.2 ∈ C ∧ ς e.1 e.2 ≠ 0) :
    (graphLaw G hne).expect (coverRowIntegrand G ς C H x) ≤
      rowsR G (Fintype.card F) n (univ \ C) *
        ∏ b ∈ C, coverRowF G ς (Fintype.card F) n C ord H b := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hq0 : (0 : ℝ) < Fintype.card F := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- Step 1: the completions of a labelling of `C`, along an ordering `l` of `U⁺ \ C`
  set l := (univ \ C).toList with hl
  have hlnd : l.Nodup := nodup_toList _
  have hlcov : ∀ w, w ∈ C ∨ w ∈ l := fun w => by
    by_cases h : w ∈ C
    · exact Or.inl h
    · exact Or.inr (mem_toList.mpr (mem_sdiff.mpr ⟨mem_univ w, h⟩))
  have hldisj : ∀ w ∈ l, w ∉ C := fun w hw => (mem_sdiff.mp (mem_toList.mp hw)).2
  set K := upperProd G (Fintype.card F) C l
  set L := lowerProd G (Fintype.card F) n C l
  obtain ⟨hKL, hL0⟩ := coverRow_upperProd_le hq1 G hS1 l C
  rw [hl, prod_map_toList] at hKL
  have hKL' : K ≤ rowsR G (Fintype.card F) n (univ \ C) * L := hKL
  have hcompl := fun (y : U → F) (hy : Feasible F G C y) =>
    extCount_bounds hW G hn l C y hlnd hlcov hldisj hy
  have hK0 : 0 ≤ K := upperProd_nonneg G hq0.le l C
  -- the per-vertex factors
  have het : ∀ b, coarseError (coverRowT G C ord b) (Fintype.card F) n < 1 := fun b =>
    lt_of_le_of_lt (coarseError_mono hn0 (coverRow_nbrCount_le G _ b)) (hS1 b)
  set ℓ : U → ℝ := fun b => Fintype.card F / 2 ^ coverRowT G C ord b *
    (1 - coarseError (coverRowT G C ord b) (Fintype.card F) n) with hℓ
  set M : U → ℝ := fun b => Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
    (1 + coarseError (coverRowS G C ord H b) (Fintype.card F) (2 * n) +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) with hM
  have hℓpos : ∀ b, 0 < ℓ b := fun b => mul_pos (by positivity) (by linarith [het b])
  have hMnn : ∀ b, 0 ≤ M b := fun b => by
    have he := coarseError_nonneg (q := (Fintype.card F : ℝ))
      (by positivity : (0 : ℝ) ≤ 2 * n) (coverRowS G C ord H b)
    exact mul_nonneg (by positivity) (add_nonneg (add_nonneg zero_le_one he) (by positivity))
  have hFb : ∀ b, M b / ℓ b = coverRowF G ς (Fintype.card F) n C ord H b := by
    intro b
    have h1 : 0 < 1 - coarseError (coverRowT G C ord b) (Fintype.card F) n := by
      linarith [het b]
    simp only [hM, hℓ, coverRowF, inv_pow]
    field_simp
  -- merges only read the earlier labels
  have hmerges_loc : ∀ b, ∀ y y' : U → F, (∀ a ∈ coverRowEarlier C ord b, y a = y' a) →
      coverRowMerges G C ord H x y b = coverRowMerges G C ord H x y' b := by
    intro b y y' h
    unfold coverRowMerges
    refine sum_congr rfl fun b' hb' => ?_
    rw [h b' (mem_filter.mp hb').1]
  have hphi_loc : ∀ b ∈ C, ∀ y y' : U → F, (∀ a ∈ C, ord a ≤ ord b → y a = y' a) →
      coverRowPhi G ς C ord H x b y = coverRowPhi G ς C ord H x b y' := by
    intro b hb y y' hyy
    unfold coverRowPhi
    rw [hyy b hb le_rfl, hmerges_loc b y y' (fun a ha =>
      hyy a (mem_filter.mp ha).1 (mem_filter.mp ha).2.le)]
  -- Step 4 for each vertex
  have hphi_step : ∀ b ∈ C, ∀ x' : U → F, Feasible F G (coverRowEarlier C ord b) x' →
      ∑ c ∈ vertexAdmissible G (coverRowEarlier C ord b) x' b,
        coverRowPhi G ς C ord H x b (Function.update x' b c) ≤ M b := by
    intro b _ x' hx'
    have hupd : ∀ c, coverRowPhi G ς C ord H x b (Function.update x' b c) =
        coverRowOmegaHat G ς H x b c * ((2 : ℝ) ^ coverRowMerges G C ord H x x' b)⁻¹ := by
      intro c
      unfold coverRowPhi
      rw [Function.update_self, hmerges_loc b _ x' (fun a ha => by
        have hab : a ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp ha).2
        exact Function.update_of_ne hab _ _)]
    rw [sum_congr rfl fun c _ => hupd c]
    exact coverRows_oneVertex hW G ς hς C ord H (fun e he => (hH e he).2) x hx n b x' hx'
  -- Step 2 for each vertex
  have hℓstep : ∀ b ∈ C, ∀ x' : U → F, Feasible F G (coverRowEarlier C ord b) x' →
      ℓ b ≤ (vertexAdmissible G (coverRowEarlier C ord b) x' b).card := by
    intro b _ x' hx'
    obtain ⟨-, hlo⟩ := card_vertexAdmissible hW G hx' b
    have hsoft := coverRow_softError_le hq1 n (nbrCount G (coverRowEarlier C ord b) b)
    have hA : ((coverRowEarlier C ord b).card : ℝ) ≤ n := by
      have := (card_le_univ (coverRowEarlier C ord b)).trans hn
      exact_mod_cast this
    have hpos : (0 : ℝ) < 2 ^ nbrCount G (coverRowEarlier C ord b) b := by positivity
    have h2A := mul_le_mul_of_nonneg_left hA hpos.le
    simp only [hℓ, coverRowT]
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  have hfe : Feasible F G (C \ C) x := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have hseg : ∀ b ∈ C, ∀ b' ∈ C, b' ∉ C → ord b' < ord b :=
    fun _ _ _ hb'C hb' => absurd hb'C hb'
  -- Steps 3 and 5: the sum of the integrand over `Inj_p(G⁺)`
  have hupper : ∑ y ∈ injLabellings F G, coverRowIntegrand G ς C H x y ≤ K * ∏ b ∈ C, M b := by
    have h := coverRow_seq_upper G hord (coverRowPhi G ς C ord H x) M K
      (fun b y => coverRow_phi_nonneg G ς C ord H x b y) hMnn hK0 hphi_loc hphi_step
      (fun y hy => (hcompl y hy).2) C.card C rfl subset_rfl hseg x hfe
    rw [Finset.sdiff_self, coverRowExtSum_empty] at h
    exact (sum_le_sum fun y _ => coverRow_integrand_le G ς C ord H hH x y).trans h
  -- Step 2: the number of labellings
  have hlower : L * ∏ b ∈ C, ℓ b ≤ (injLabellings F G).card := by
    have h := coverRow_seq_lower G hord ℓ L (fun b => (hℓpos b).le) hL0.le hℓstep
      (fun y hy => (hcompl y hy).1) C.card C rfl subset_rfl hseg x hfe
    rw [Finset.sdiff_self] at h
    have he : extCount G ∅ x = (injLabellings F G).card := by
      unfold extCount
      congr 1
      exact filter_true_of_mem fun _ _ => by simp
    rwa [he] at h
  -- conclusion
  rw [coverRow_expect_graphLaw]
  have hℓprod : 0 < ∏ b ∈ C, ℓ b := prod_pos fun b _ => hℓpos b
  have hFnn : 0 ≤ ∏ b ∈ C, coverRowF G ς (Fintype.card F) n C ord H b :=
    prod_nonneg fun b _ => by rw [← hFb b]; exact div_nonneg (hMnn b) (hℓpos b).le
  have hKL'' : K / L ≤ rowsR G (Fintype.card F) n (univ \ C) := by
    rw [div_le_iff₀ hL0]
    exact hKL'
  calc (∑ y ∈ injLabellings F G, coverRowIntegrand G ς C H x y) / (injLabellings F G).card
      ≤ (K * ∏ b ∈ C, M b) / (L * ∏ b ∈ C, ℓ b) :=
        div_le_div₀ (mul_nonneg hK0 (prod_nonneg fun b _ => hMnn b)) hupper
          (mul_pos hL0 hℓprod) hlower
    _ = K / L * ∏ b ∈ C, (M b / ℓ b) := by
        rw [prod_div_distrib]
        field_simp
    _ = K / L * ∏ b ∈ C, coverRowF G ς (Fintype.card F) n C ord H b := by
        simp only [hFb]
    _ ≤ rowsR G (Fintype.card F) n (univ \ C) *
          ∏ b ∈ C, coverRowF G ς (Fintype.card F) n C ord H b :=
        mul_le_mul_of_nonneg_right hKL'' hFnn

/-- **`lem:extraction-rows` (Cover rows).** Assume `e_{d⁰_i}(p, n) < 1` for every vertex (a
consequence of (S1) at `p`). Let `C ⊆ U⁺` be ordered by `ord` (injective on `C`), `x` injective
(e.g. `x ∈ 𝓘⁺`) and `H ⊆ {(a, b) ∈ E_× : b ∈ C}`. With `μ_C` the law of `x'_C` for
`x' ∼ μ = λ_p(G⁺)`,
`E_{c' ∼ μ_C}[∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')}] ≤
R_{U⁺ \ C} ∏_{b ∈ C} F_b(H)`. A labelling `c'` of `C` enters the integrand through its
extension by `0` (`extendLabel`; the integrand reads only `C`). `WeilBound F` is Weil's theorem,
the literature input of `lem:extension`. -/
theorem coverRows_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ i, coarseError (rowsDeg0 G i) (Fintype.card F) n < 1)
    (C : Finset U) (ord : U → ℕ) (hord : Set.InjOn ord C) (x : U → F)
    (hx : Function.Injective x) (H : Finset (U × U)) (hH : ∀ e ∈ H, e.2 ∈ C ∧ ς e.1 e.2 ≠ 0) :
    (coverRowMarginal G hne C).expect
        (fun c' => coverRowIntegrand G ς C H x (extendLabel C c')) ≤
      rowsR G (Fintype.card F) n (univ \ C) *
        ∏ b ∈ C, coverRowF G ς (Fintype.card F) n C ord H b := by
  unfold coverRowMarginal
  rw [FiniteLaw.expect_map]
  have hcomp : (fun c' : C → F => coverRowIntegrand G ς C H x (extendLabel C c')) ∘
      (fun y (b : C) => y b) = coverRowIntegrand G ς C H x := by
    funext y
    simp only [Function.comp]
    refine coverRowIntegrand_congr G ς C H (fun e he => (hH e he).1) x fun b hb => ?_
    simp [extendLabel, hb]
  rw [hcomp]
  exact coverRows_le_graphLaw hW G ς hς hne hn hS1 C ord hord x hx H hH

end Main

/-! ## Spectral data -/

section SpecDataForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `e_t(q, n)` is nondecreasing in `n`. -/
theorem coverRow_coarseError_mono_n {q : ℝ} (t : ℕ) {n n' : ℝ} (hnn : n ≤ n') :
    coarseError t q n ≤ coarseError t q n' := by
  unfold coarseError
  gcongr

/-- In spectral data, `d⁰_i` (`SpecData.deg0`) is the degree of `i` in the half graph `G⁺`
(`SpecData.halfGraph`). -/
theorem coverRow_rowsDeg0_halfGraph (D : Cuts.SpecData V) (i : D.cut.Half) :
    rowsDeg0 D.halfGraph i = D.deg0 i := by
  unfold rowsDeg0 rowsAdj Cuts.SpecData.deg0
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro j _
  simp only [Cuts.SpecData.mem_halfGraph, Cuts.SpecData.Adj]

/-- **`lem:extraction-rows` for spectral data** (`def:spec:data`, the paragraph *Setting* of
`subsec:extraction:partition`): `G⁺ = D.halfGraph` on `U⁺`, cross signs `ς = D.sgn`,
`n = |U⁺|`, (S1) at `p` (`D.S1` with `e_t = e_t(p, 2n)`), `x ∈ 𝓘⁺`, and
`H ⊆ {(a, b) ∈ E_× : b ∈ C}`. `WeilBound F` is Weil's theorem (literature input). -/
theorem coverRows_le_specData (hW : WeilBound F) (D : Cuts.SpecData V)
    (hne : (injLabellings F D.halfGraph).Nonempty)
    (hS1 : D.S1 (fun t => coarseError t (Fintype.card F) (2 * D.n)) (Fintype.card F))
    (C : Finset D.cut.Half) (ord : D.cut.Half → ℕ) (hord : Set.InjOn ord C)
    (x : D.cut.Half → F) (hx : x ∈ injLabellings F D.halfGraph)
    (H : Finset (D.cut.Half × D.cut.Half)) (hH : ∀ e ∈ H, e ∈ D.crossPairs ∧ e.2 ∈ C) :
    (coverRowMarginal D.halfGraph hne C).expect
        (fun c' => coverRowIntegrand D.halfGraph D.sgn C H x (extendLabel C c')) ≤
      rowsR D.halfGraph (Fintype.card F) D.n (univ \ C) *
        ∏ b ∈ C, coverRowF D.halfGraph D.sgn (Fintype.card F) D.n C ord H b := by
  refine coverRows_le hW D.halfGraph D.sgn ?_ hne ?_ ?_ C ord hord x ?_ H ?_
  · intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp
  · exact le_of_eq (Fintype.card_coe _)
  · intro i
    have hdeg : rowsDeg0 D.halfGraph i ≤ D.Delta := by
      rw [coverRow_rowsDeg0_halfGraph]
      exact (Nat.le_add_right _ _).trans (Finset.le_sup (f := D.dk) (mem_univ i))
    have hn0 : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
    calc coarseError (rowsDeg0 D.halfGraph i) (Fintype.card F) D.n
        ≤ coarseError D.Delta (Fintype.card F) D.n := coarseError_mono hn0 hdeg
      _ ≤ coarseError D.Delta (Fintype.card F) (2 * D.n) :=
          coverRow_coarseError_mono_n _ (by linarith)
      _ < 1 := hS1.1
  · intro a b h
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  · intro e he
    obtain ⟨h1, h2⟩ := hH e he
    exact ⟨h2, (mem_filter.mp h1).2⟩

end SpecDataForm

end Sarkozy.Extraction

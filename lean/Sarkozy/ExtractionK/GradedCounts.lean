module

public import Sarkozy.ExtractionK.Grouped

@[expose] public section

/-!
# Graded errors, I: the counts with an abstract error function

`paper/sections/16_extraction.tex`, the paragraph *Graded errors* of
`subsec:extraction:partition`: every statement of the section holds with the coarse error
`e_t(p, n')` replaced by the graded error `e^-_t(n')` of `eq:graphs:graded`; the proofs use only
that the error bounds the relative error of the counts of `lem:extension` from above whatever the
excluded set, and from below with at most `n` excluded labels, and that it is nondecreasing in
`t`. This file states these properties for an abstract error function and re-proves the counting
inputs of `lem:matching:extractionk` with it.

* `GrErr q n e` (one error pair of the setting, `def:graphs:error-pair`): `e^+_t ≤ e t n'` for
  `n' ≥ 0` (upper counts), `𝔈_t + 2^t n ≤ q e t n` (lower counts, at most `n` exclusions),
  monotone in `t`, nonnegative. Instances: `grErr_coarse` (`e_t(q, n')`), `grErr_graded`
  (`grGraded q t n' = (𝔈_t + 2^t n')/q = e^-_t(n')`; `gr_gradedA_succ`, `gr_gradedB_succ`,
  `gr_softError_mono`: `a_t`, `b_t`, `𝔈_t` are nondecreasing in `t`).
* `gr_merged_count_le`: `lem:extraction-merged-count` with any `E ≥ e^+_{t+h−μ_m}`.
* `grIntNum`, `grIntF`, `grCoverF`: the vertex factors `F_u`, `F_b` of `def:extraction:records`
  with the error function `e`.
* `gr_coverRows_oneVertex` (`eq:extraction:onevertex`), `gr_partLab_coverRows_le` (Steps 2–5 of
  `lem:extraction-rows` over the labellings of `C`), `gr_card_injLabellings_ge` (the lower count
  of `lem:graphs:sequential`(a)), `gr_integrated_oneVertex`, `gr_integrated_extSum_le`
  (`eq:extraction:mbound`): the coarse statements of `Extraction/CoverRows.lean`,
  `PartialLabellings.lean`, `IntegratedVertex.lean` with `e` in place of `e_t(q, n')`; the proofs
  are those files' proofs, the error entering only through `GrErr`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## Abstract error functions -/

/-- An error function `e t n'` for the counts of `lem:extension` with `q` elements and at most
`n` excluded labels in the lower counts (the error pair of the setting, `def:graphs:error-pair`):
`e^+_t ≤ e t n'` for every `n' ≥ 0` (upper counts), `𝔈_t + 2^t n ≤ q e t n` (lower counts),
nondecreasing in `t` and nonnegative. The coarse error `e_t(q, n')` (`grErr_coarse`) and the
graded error `e^-_t(n') = (𝔈_t + 2^t n')/q` (`grErr_graded`) are error functions. -/
structure GrErr (q : ℝ) (n : ℕ) (e : ℕ → ℝ → ℝ) : Prop where
  upper : ∀ (t : ℕ) (n' : ℝ), 0 ≤ n' → upperError t q ≤ e t n'
  lower : ∀ t : ℕ, softError q t + 2 ^ t * n ≤ q * e t n
  mono : ∀ (n' : ℝ), 0 ≤ n' → ∀ t t' : ℕ, t ≤ t' → e t n' ≤ e t' n'
  nonneg : ∀ (t : ℕ) (n' : ℝ), 0 ≤ n' → 0 ≤ e t n'

theorem gr_upperError_nonneg {q : ℝ} (t : ℕ) : 0 ≤ upperError t q := by
  unfold upperError
  have h1 := gradedA_nonneg t
  have h2 := gradedB_nonneg t
  have h3 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  positivity

/-- **`lem:extraction-merged-count`** with the upper error `e^+_{t+h−μ_m} ≤ E`: the bound
`q 2^{-t} 2^{μ_m} (1 + E)` (`merged_count_le_fintype` with `E` in place of the coarse error). -/
theorem gr_merged_count_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hW : WeilBound F) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (β : ι → F) (hβ : Function.Injective β) (γ : κ → F) (hγ : Function.Injective γ)
    (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (s' : κ → ℤ) (hs' : ∀ l, s' l = 1 ∨ s' l = -1)
    (𝒳 : Finset F) (hβX : ∀ i, β i ∈ 𝒳) (hγX : ∀ l, γ l ∈ 𝒳) {E : ℝ}
    (hE : upperError (Fintype.card ι + Fintype.card κ - mergedCount β γ) (Fintype.card F) ≤ E) :
    (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
        ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ * (1 + E) := by
  have hpt : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) =
        if ∀ l, quadraticChar F (y - γ l) = s' l then (2 : ℝ) ^ Fintype.card κ else 0 := by
    intro y hy
    have hyX : y ∉ 𝒳 := (mem_filter.mp hy).2.1
    have hne : ∀ l, y ≠ γ l := fun l h => hyX (h ▸ hγX l)
    have h := prod_soft_eq γ s' hs' hne
    have hR : ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) =
        (((if ∀ l, quadraticChar F (y - γ l) = s' l then 2 ^ Fintype.card κ else 0 : ℤ)) : ℝ) := by
      rw [← h]
      norm_cast
    rw [hR]
    split_ifs <;> simp
  rw [sum_congr rfl hpt, ← sum_filter, sum_const, nsmul_eq_mul]
  have hE0 : 0 ≤ E := le_trans (gr_upperError_nonneg _) hE
  by_cases hbad : ∃ i l, β i = γ l ∧ s i ≠ s' l
  · obtain ⟨i, l, hil, hsl⟩ := hbad
    have hΨ0 : ((univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i)).filter
        fun y => ∀ l, quadraticChar F (y - γ l) = s' l) = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => hsl ?_
      simp only [mem_filter, mem_univ, true_and] at hy
      rw [← hy.1.2 i, ← hy.2 l, hil]
    rw [hΨ0, card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (by positivity) (by linarith)
  · push Not at hbad
    have hρ : Function.Injective
        (Sum.elim β fun l : {l : κ // ∀ i, β i ≠ γ l} => γ l.1) :=
      hβ.sumElim (fun l l' h => Subtype.ext (hγ h)) fun i l => l.2 i
    have hσ : ∀ j, (Sum.elim s fun l : {l : κ // ∀ i, β i ≠ γ l} => s' l.1) j = 1 ∨
        (Sum.elim s fun l : {l : κ // ∀ i, β i ≠ γ l} => s' l.1) j = -1 := by
      rintro (i | l)
      · exact hs i
      · exact hs' l.1
    have hρX : ∀ j, (Sum.elim β fun l : {l : κ // ∀ i, β i ≠ γ l} => γ l.1) j ∈ 𝒳 := by
      rintro (i | l)
      · exact hβX i
      · exact hγX l.1
    have hΨeq : ((univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i)).filter
        fun y => ∀ l, quadraticChar F (y - γ l) = s' l) =
          admissible (Sum.elim β fun l : {l : κ // ∀ i, β i ≠ γ l} => γ l.1)
            (Sum.elim s fun l : {l : κ // ∀ i, β i ≠ γ l} => s' l.1) 𝒳 := by
      ext y
      simp only [admissible, mem_filter, mem_univ, true_and, Sum.forall, Sum.elim_inl,
        Sum.elim_inr]
      constructor
      · rintro ⟨⟨hy, hb⟩, hg⟩
        exact ⟨hy, hb, fun l => hg l.1⟩
      · rintro ⟨hy, hb, hg⟩
        refine ⟨⟨hy, hb⟩, fun l => ?_⟩
        by_cases hl : ∀ i, β i ≠ γ l
        · exact hg ⟨l, hl⟩
        · push Not at hl
          obtain ⟨i, hil⟩ := hl
          rw [← hil, hb i, hbad i l hil]
    have hcardU : Fintype.card {l : κ // ∀ i, β i ≠ γ l} + mergedCount β γ = Fintype.card κ := by
      rw [Fintype.card_subtype]
      exact card_unmerged_add_mergedCount β hβ γ
    have hk : Fintype.card (ι ⊕ {l : κ // ∀ i, β i ≠ γ l}) =
        Fintype.card ι + Fintype.card κ - mergedCount β γ := by
      rw [Fintype.card_sum]
      omega
    have hext := two_pow_mul_card_admissible_le hW _ hρ _ hσ 𝒳 hρX
    rw [← hΨeq, hk] at hext
    have hpow_k : (2 : ℝ) ^ (Fintype.card ι + Fintype.card κ - mergedCount β γ) =
        2 ^ Fintype.card ι * 2 ^ Fintype.card {l : κ // ∀ i, β i ≠ γ l} := by
      rw [← hk, Fintype.card_sum, pow_add]
    have hpow_h : (2 : ℝ) ^ Fintype.card κ =
        2 ^ Fintype.card {l : κ // ∀ i, β i ≠ γ l} * 2 ^ mergedCount β γ := by
      rw [← pow_add, hcardU]
    have hinv : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ)⁻¹ ^ Fintype.card ι = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
    have hfac : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ := by positivity
    have hq0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
    set N : ℝ := ((((univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i)).filter
        fun y => ∀ l, quadraticChar F (y - γ l) = s' l)).card : ℝ)
    calc N * 2 ^ Fintype.card κ
        = (2 ^ Fintype.card ι * (2 : ℝ)⁻¹ ^ Fintype.card ι) *
            (N * (2 ^ Fintype.card {l : κ // ∀ i, β i ≠ γ l} * 2 ^ mergedCount β γ)) := by
          rw [hinv, one_mul, hpow_h]
      _ = (2 ^ (Fintype.card ι + Fintype.card κ - mergedCount β γ) * N) *
            ((2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ) := by
          rw [hpow_k]
          ring
      _ ≤ (Fintype.card F * (1 + upperError (Fintype.card ι + Fintype.card κ - mergedCount β γ)
              (Fintype.card F))) * ((2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ) :=
          mul_le_mul_of_nonneg_right hext hfac
      _ ≤ (Fintype.card F * (1 + E)) * ((2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) hq0) hfac
      _ = _ := by ring

/-! ## Vertex factors with an error function -/

section GrDefs

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The numerator of `F_u` (`u ∈ U_x`, `def:extraction:records`) with the error function `e`:
`1 + e_{s_u}(n) + r² 2^{s_u} ∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]}`. -/
noncomputable def grIntNum (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ) (ord : U → ℕ) (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : ℝ :=
  1 + e (intS G ord Fr u) n +
    (Real.sqrt q)⁻¹ ^ 2 * 2 ^ intS G ord Fr u * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b

/-- `F_u` with the error function `e`: `grIntNum / (1 - e_{t_u}(n))`. -/
noncomputable def grIntF (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ) (ord : U → ℕ) (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : ℝ :=
  grIntNum G ς e q n ord Fr Cz u / (1 - e (ordT G ord u) n)

/-- `F_b(H)` (cover vertex, `def:extraction:records`) with the error function `e`:
`(1 + e_{s_b}(2n) + r² 2^{s_b} ∑_j 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})/(1 - e_{t_b}(n))`. -/
noncomputable def grCoverF (G : OrientedGraph U) (ς : U → U → ℤ) (e : ℕ → ℝ → ℝ) (q : ℝ)
    (n : ℕ) (C : Finset U) (ord : U → ℕ) (H : Finset (U × U)) (b : U) : ℝ :=
  (1 + e (coverRowS G C ord H b) (2 * n) +
      (Real.sqrt q)⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b * ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) /
    (1 - e (coverRowT G C ord b) n)

end GrDefs

section GrRows

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`eq:extraction:onevertex`** (Step 4 of `lem:extraction-rows`) for an error function `e`
(*Graded errors*). Fix `b` and labels `x'` of
the vertices of `C` earlier than `b` (feasible there), and let `Adm_b = Φ_b(x')` be the labels
distinct from the earlier ones satisfying the `t_b` constraints of `G⁺` with the earlier
neighbours of `b`. Then
`∑_{y ∈ Adm_b} ω̂_b(y) 2^{-μ_b} ≤ q 2^{-t_b}(1 + e_{s_b}(q, 2n) + r² 2^{s_b}
∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`. The labels `y ∉ x(U⁺)` are counted by
`lem:extraction-merged-count` (`gr_merged_count_le`), with the `μ_b` merges; the labels
`y = x_j` by `coverRow_omegaHat_at_le`. `WeilBound F` is Weil's theorem (literature input). -/
theorem gr_coverRows_oneVertex (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (C : Finset U) (ord : U → ℕ)
    (H : Finset (U × U)) (hHς : ∀ e ∈ H, ς e.1 e.2 ≠ 0) (x : U → F) (hx : Function.Injective x)
    (n : ℕ) (e : ℕ → ℝ → ℝ) (he : GrErr (Fintype.card F) n e) (b : U) (x' : U → F)
    (hx' : Feasible F G (coverRowEarlier C ord b) x') :
    ∑ y ∈ vertexAdmissible G (coverRowEarlier C ord b) x' b,
        coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ coverRowMerges G C ord H x x' b)⁻¹ ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
        (1 + e (coverRowS G C ord H b) (2 * n) +
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
  have h2n : (0 : ℝ) ≤ 2 * n := by positivity
  have hE : upperError (Fintype.card NA + Fintype.card Hb - mergedCount β γ) (Fintype.card F) ≤
      e (coverRowS G C ord H b) (2 * n) := by
    refine (he.upper _ _ h2n).trans (he.mono _ h2n _ _ ?_)
    rw [hcardι, hcardκ, hS]
    exact Nat.sub_le _ _
  have hmc := gr_merged_count_le hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hE
  have hi : ∑ y ∈ (vertexAdmissible G A x' b).filter (fun y => y ∉ X),
      coverRowOmegaHat G ς H x b y * ((2 : ℝ) ^ μ)⁻¹ ≤
        Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
          (1 + e (coverRowS G C ord H b) (2 * n)) := by
    rw [← sum_mul, hset, sum_congr rfl hsummand]
    rw [hcardι, hmerge] at hmc
    calc (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) * ((2 : ℝ) ^ μ)⁻¹
        ≤ (Fintype.card F * (2 : ℝ)⁻¹ ^ coverRowT G C ord b * 2 ^ μ *
            (1 + e (coverRowS G C ord H b) (2 * n))) *
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
            (1 + e (coverRowS G C ord H b) (2 * n)) :=
        add_le_add hii hi
    _ = _ := by rw [← hid]; ring


/-- **Steps 2–5 of `lem:extraction-rows`, summed over the labellings of `C`**, for an error
function `e` (*Graded errors*) (the form used in
Step 7 of `lem:matching:extractionk`, without the marginal comparison of Step 1). Let `C ⊆ U⁺` be
ordered by `ord` (injective on `C`), `x` injective and `H ⊆ {(a, b) ∈ E_× : b ∈ C}`. Then
`∑_{c' ∈ Inj(G⁺[C])} ∏_{(a,b) ∈ H} (1 + χ(ς_{ab}(c'_b - x_a))) 2^{κ_C(x, c')} ≤
∏_{b ∈ C} q 2^{-t_b} (1 + e_{s_b}(q, 2n) + r² 2^{s_b} ∑_{j ∈ U⁺} 2^{mg(j,b) + c^U(j,b) - [j ∈ H_b]})`
for every `n`; the factor of `b` is the numerator of `F_b(H)` times `q 2^{-t_b}`. Proof: Step 3
(`coverRow_integrand_le`), Step 4 (`coverRows_oneVertex`, `eq:extraction:onevertex`) and Step 5
(`partLab_seq_upper`). `WeilBound F` is Weil's theorem (literature input). -/
theorem gr_partLab_coverRows_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e) (C : Finset U) (ord : U → ℕ) (hord : Set.InjOn ord C) (x : U → F)
    (hx : Function.Injective x) (H : Finset (U × U)) (hH : ∀ e ∈ H, e.2 ∈ C ∧ ς e.1 e.2 ≠ 0) :
    ∑ c' ∈ partLab F G C, coverRowIntegrand G ς C H x c' ≤
      ∏ b ∈ C, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
        (1 + e (coverRowS G C ord H b) (2 * n) +
          (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
            ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b)) := by
  set M : U → ℝ := fun b => (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ coverRowT G C ord b *
    (1 + e (coverRowS G C ord H b) (2 * n) +
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ coverRowS G C ord H b *
        ∑ j, (2 : ℝ) ^ coverRowExp G ς H j b) with hM
  have hMnn : ∀ b, 0 ≤ M b := fun b => by
    have he0 := he.nonneg (coverRowS G C ord H b) (2 * n) (by positivity)
    exact mul_nonneg (by positivity) (add_nonneg (add_nonneg zero_le_one he0) (by positivity))
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
    exact gr_coverRows_oneVertex hW G ς hς C ord H (fun e' he' => (hH e' he').2) x hx n e he b x'
      hx'
  calc ∑ c' ∈ partLab F G C, coverRowIntegrand G ς C H x c'
      ≤ ∑ c' ∈ partLab F G C, ∏ b ∈ C, coverRowPhi G ς C ord H x b c' :=
        sum_le_sum fun c' _ => coverRow_integrand_le G ς C ord H hH x c'
    _ ≤ ∏ b ∈ C, M b :=
        partLab_seq_upper G C ord hord (coverRowPhi G ς C ord H x) M
          (fun b y => coverRow_phi_nonneg G ς C ord H x b y) hMnn hphi_loc hphi_step

/-! ## The lower count of `Inj_p(G⁺)` -/

/-- **The lower count of `lem:graphs:sequential`(a) along an order of all vertices**, for an
error function `e` (*Graded errors*): labelling
`U⁺` in the order `ord` (injective), `|Inj_p(G⁺)| ≥ ∏_v q 2^{-t_v} (1 - e_{t_v}(q, n))`, `t_v` the
number of `G⁺`-neighbours of `v` earlier in the order (`ordT`), for `n ≥ |U⁺|`. The hypothesis
`e_{t_v}(q, n) ≤ 1` makes every factor nonnegative (under (S1), `e_t(p, n) < 1` for `t ≤ Δ`).
`WeilBound F` is Weil's theorem (literature input, through `card_vertexAdmissible`). -/
theorem gr_card_injLabellings_ge (hW : WeilBound F) (G : OrientedGraph U) {n : ℕ}
    (hn : Fintype.card U ≤ n) (ord : U → ℕ) (hord : Function.Injective ord)
    (e : ℕ → ℝ → ℝ) (he : GrErr (Fintype.card F) n e) (he1 : ∀ v, e (ordT G ord v) n ≤ 1) :
    ∏ v, ((Fintype.card F : ℝ) / 2 ^ ordT G ord v *
      (1 - e (ordT G ord v) n)) ≤ (injLabellings F G).card := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  set ℓ : U → ℝ := fun v => (Fintype.card F : ℝ) / 2 ^ ordT G ord v *
    (1 - e (ordT G ord v) n) with hℓ
  have hℓ0 : ∀ v, 0 ≤ ℓ v := fun v => mul_nonneg (by positivity) (by linarith [he1 v])
  have hℓstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord b) x' →
      ℓ b ≤ (vertexAdmissible G (coverRowEarlier univ ord b) x' b).card := by
    intro b _ x' hx'
    obtain ⟨-, hlo⟩ := card_vertexAdmissible hW G hx' b
    have hsoft := he.lower (nbrCount G (coverRowEarlier univ ord b) b)
    have hA : ((coverRowEarlier univ ord b).card : ℝ) ≤ n := by
      have := (card_le_univ (coverRowEarlier univ ord b)).trans hn
      exact_mod_cast this
    have hpos : (0 : ℝ) < 2 ^ nbrCount G (coverRowEarlier univ ord b) b := by positivity
    have h2A := mul_le_mul_of_nonneg_left hA hpos.le
    simp only [hℓ, ordT, coverRowT]
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  have hfe : Feasible F G (univ \ univ) (fun _ : U => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have hseg : ∀ b ∈ (univ : Finset U), ∀ b' ∈ (univ : Finset U), b' ∉ univ → ord b' < ord b :=
    fun _ _ _ _ hb' => absurd (mem_univ _) hb'
  have h := coverRow_seq_lower G (C := univ) (ord := ord) (fun a _ b _ hab => hord hab) ℓ 1
    hℓ0 zero_le_one hℓstep (fun y hy => by rw [extCount_univ G hy]; norm_num) _ univ rfl
    subset_rfl hseg _ hfe
  rw [Finset.sdiff_self, one_mul] at h
  have hext : extCount G ∅ (fun _ : U => (0 : F)) = (injLabellings F G).card := by
    unfold extCount
    congr 1
    exact filter_true_of_mem fun _ _ => by simp
  rw [hext] at h
  exact h

end GrRows

section GrIntegrated

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The one-vertex bound of Step 6**, for an error function `e` (*Graded errors*). Let `u ∈ U_x` and let `y` be feasible on the vertices
earlier than `u`. Summing `ŵ_u(z) 2^{-κ_u(y)}` over the admissible labels `z` of `u` gives at most
`q 2^{-t_u}(1 + e_{s_u}(q, n) + r² 2^{s_u} ∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]})`. The generic
labels `z ∉ c'(C_z)` are counted by `lem:extraction-merged-count` (`gr_merged_count_le`,
with the `κ_u` merged roots), the special labels `z = c'_b` by `intWHat_special_le`.
`WeilBound F` is Weil's theorem (literature input). -/
theorem gr_integrated_oneVertex (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e) (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (Ux Cz : Finset U) (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz) (ord : U → ℕ)
    (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (u : U) (hu : u ∈ Ux) (y : U → F) (hy : Feasible F G (coverRowEarlier univ ord u) y) :
    ∑ z ∈ vertexAdmissible G (coverRowEarlier univ ord u) y u,
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ intMerges G ord Fr c' y u)⁻¹ ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
        grIntNum G ς e (Fintype.card F) n ord Fr Cz u := by
  set A := coverRowEarlier univ ord u with hA
  set μ := intMerges G ord Fr c' y u with hμ
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hμinv0 : (0 : ℝ) ≤ ((2 : ℝ) ^ μ)⁻¹ := by positivity
  have hμinv1 : ((2 : ℝ) ^ μ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num))
  have hHbFr : ∀ b ∈ intH Fr u, (u, b) ∈ Fr := fun b hb => by simpa [intH] using hb
  rw [← sum_filter_add_sum_filter_not (vertexAdmissible G A y u) (fun z => z ∈ Cz.image c')]
  -- the special labels `c'_b`, `b ∈ C_z`
  have hii : ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
      intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ ≤
        ∑ b ∈ Cz, 2 ^ (intH Fr u).card * (2 : ℝ) ^ intExp G ς Fr u b := by
    calc ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
          intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹
        ≤ ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
            intWHat G ς Fr Cz c' u z :=
          sum_le_sum fun z _ => mul_le_of_le_one_right (intWHat_nonneg G ς Fr Cz c' u z) hμinv1
      _ ≤ ∑ z ∈ Cz.image c', intWHat G ς Fr Cz c' u z :=
          sum_le_sum_of_subset_of_nonneg (fun z hz => (mem_filter.mp hz).2)
            (fun z _ _ => intWHat_nonneg G ς Fr Cz c' u z)
      _ = ∑ b ∈ Cz, intWHat G ς Fr Cz c' u (c' b) :=
          sum_image fun a ha b hb h => hc' a ha b hb h
      _ ≤ _ := sum_le_sum fun b hb => intWHat_special_le G ς Fr Cz c' hc' u b hb
  -- the other labels: `lem:extraction-merged-count`
  set NA := A.filter (fun i => (i, u) ∈ G.E ∨ (u, i) ∈ G.E) with hNA
  set Hb := intH Fr u with hHb
  let β : NA → F := fun i => y i
  have hβ : Function.Injective β := fun i j h =>
    Subtype.ext (hy.1 i (mem_filter.mp i.2).1 j (mem_filter.mp j.2).1 h)
  let γ : Hb → F := fun b => c' b
  have hγ : Function.Injective γ := fun a b h =>
    Subtype.ext (hc' a (hH (u, a) (hHbFr a a.2) hu) b (hH (u, b) (hHbFr b b.2) hu) h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun i => if (i.1, u) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Hb → ℤ := fun b => quadraticChar F (-(ς u b.1 : F))
  have hs' : ∀ b, s' b = 1 ∨ s' b = -1 := fun b => by
    have hb : ς u b.1 ≠ 0 := hFr (u, b.1) (hHbFr b.1 b.2)
    have hne : -(ς u b.1 : F) ≠ 0 := by
      rcases hς u b.1 with h | h | h
      · exact absurd h hb
      · rw [h]; simp
      · rw [h]; simp
    exact quadraticChar_dichotomy hne
  set 𝒳 : Finset F := A.image y ∪ Cz.image c' with h𝒳
  have hβX : ∀ i, β i ∈ 𝒳 := fun i =>
    mem_union_left _ (mem_image_of_mem y (mem_filter.mp i.2).1)
  have hγX : ∀ b, γ b ∈ 𝒳 := fun b =>
    mem_union_right _ (mem_image_of_mem c' (hH (u, b.1) (hHbFr b.1 b.2) hu))
  have hset : (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c') =
      univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun i => ?_⟩
      have hi := (mem_filter.mp i.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin i (mem_filter.mp i.2).1 h
      · have hvu : (u, i.1) ∈ G.E := hi.resolve_left h
        have h1 := hout i (mem_filter.mp i.2).1 hvu
        have : y i - c = -1 * (c - y i) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun i hi he => ?_, fun i hi he => ?_⟩, hcX⟩
      · have hmem : i ∈ NA := mem_filter.mpr ⟨hi, Or.inl he⟩
        have := hall ⟨i, hmem⟩
        simpa [s, β, he] using this
      · have hmem : i ∈ NA := mem_filter.mpr ⟨hi, Or.inr he⟩
        have hnot : (i, u) ∉ G.E := G.oriented u i he
        have h1 := hall ⟨i, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : y i - c = -1 * (c - y i) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ z ∈ univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i),
      intWHat G ς Fr Cz c' u z = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (z - γ l)) := by
    intro z hz
    have hzX : z ∉ Cz.image c' := fun h => (mem_filter.mp hz).2.1 (mem_union_right _ h)
    have hne : ∀ b ∈ Cz, z ≠ c' b := fun b hb h => hzX (mem_image.mpr ⟨b, hb, h.symm⟩)
    unfold intWHat
    rw [sum_eq_zero fun b hb => by simp only [hne b hb, ↓reduceIte], pow_zero, mul_one]
    unfold intW
    rw [← prod_coe_sort Hb]
    refine prod_congr rfl fun b _ => ?_
    have : (ς u b.1 : F) * (c' b.1 - z) = (-(ς u b.1 : F)) * (z - c' b.1) := by ring
    simp only [s', γ, this, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = ordT G ord u := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Hb = Hb.card := Fintype.card_coe _
  have hmerge : mergedCount β γ = μ := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Hb => β il.1 = γ il.2).card
        = ∑ il : NA × Hb, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ i : NA, ∑ b : Hb, if β i = γ b then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ i : NA, ∑ b ∈ Hb, if y i = c' b then 1 else 0 :=
          sum_congr rfl fun i _ => sum_coe_sort Hb (fun b => if y i = c' b then 1 else 0)
      _ = ∑ i ∈ NA, ∑ b ∈ Hb, if y i = c' b then 1 else 0 :=
          sum_coe_sort NA (fun i => ∑ b ∈ Hb, if y i = c' b then 1 else 0)
      _ = μ := rfl
  have hS : intS G ord Fr u = ordT G ord u + Hb.card := rfl
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hE : upperError (Fintype.card NA + Fintype.card Hb - mergedCount β γ) (Fintype.card F) ≤
      e (intS G ord Fr u) n := by
    refine (he.upper _ _ hn0).trans (he.mono _ hn0 _ _ ?_)
    rw [hcardι, hcardκ, hS]
    exact Nat.sub_le _ _
  have hmc := gr_merged_count_le hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hE
  have hi : ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c'),
      intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ ≤
        Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
          (1 + e (intS G ord Fr u) n) := by
    rw [← sum_mul, hset, sum_congr rfl hsummand]
    rw [hcardι, hmerge] at hmc
    calc (∑ z ∈ univ.filter (fun z => z ∉ 𝒳 ∧ ∀ i, quadraticChar F (z - β i) = s i),
          ∏ l, ((1 : ℝ) + s' l * quadraticChar F (z - γ l))) * ((2 : ℝ) ^ μ)⁻¹
        ≤ (Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ μ *
            (1 + e (intS G ord Fr u) n)) *
            ((2 : ℝ) ^ μ)⁻¹ := mul_le_mul_of_nonneg_right hmc hμinv0
      _ = _ := by field_simp
  have hid : (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
      ((Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
        ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b) =
      ∑ b ∈ Cz, 2 ^ Hb.card * (2 : ℝ) ^ intExp G ς Fr u b := by
    rw [coverRow_r_sq hq0, ← mul_sum, hS, pow_add]
    have h2 : (2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ ordT G ord u = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
    calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
          ((Fintype.card F : ℝ)⁻¹ * (2 ^ ordT G ord u * 2 ^ Hb.card) *
            ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b)
        = ((Fintype.card F : ℝ) * (Fintype.card F : ℝ)⁻¹) *
            ((2 : ℝ)⁻¹ ^ ordT G ord u * 2 ^ ordT G ord u) *
            (2 ^ Hb.card * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b) := by ring
      _ = _ := by rw [mul_inv_cancel₀ hq0.ne', h2, one_mul, one_mul]
  have hnum : grIntNum G ς e (Fintype.card F) n ord Fr Cz u =
      1 + e (intS G ord Fr u) n +
        (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * 2 ^ intS G ord Fr u *
          ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b := rfl
  rw [hnum]
  calc ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∈ Cz.image c'),
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹ +
      ∑ z ∈ (vertexAdmissible G A y u).filter (fun z => z ∉ Cz.image c'),
        intWHat G ς Fr Cz c' u z * ((2 : ℝ) ^ μ)⁻¹
      ≤ ∑ b ∈ Cz, 2 ^ Hb.card * (2 : ℝ) ^ intExp G ς Fr u b +
          Fintype.card F * (2 : ℝ)⁻¹ ^ ordT G ord u *
            (1 + e (intS G ord Fr u) n) :=
        add_le_add hii hi
    _ = _ := by rw [← hid]; ring


/-- **`eq:extraction:mbound`** (Step 6 of `lem:matching:extractionk`), in summed form, for an
error function `e` (*Graded errors*). Let the
labels `x₀` of `V ∪ C_x = X \ U_x` be feasible, the labels `c'` of `C_z` injective on `C_z`, and
`H_u ⊆ C_z` for `u ∈ U_x`. Label `U_x` along `ord` (after all other vertices). Then the sum over
the completions `x ∈ 𝓘⁺` of `x₀` of `Θ⁺_U(x, c') = ∏_{(u,b) ∈ Fr, u ∈ U_x} (1 + χ_{ub}(x, c'))` is
at most `2^{κ^f} ∏_{u ∈ U_x} q 2^{-t_u}(1 + e_{s_u}(q, n) + r² 2^{s_u}
∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]})`. `WeilBound F` is Weil's theorem (literature input). -/
theorem gr_integrated_extSum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (n : ℕ) (e : ℕ → ℝ → ℝ)
    (he : GrErr (Fintype.card F) n e) (Fr : Finset (U × U)) (hFr : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0)
    (Ux Cz : Finset U) (hH : ∀ e ∈ Fr, e.1 ∈ Ux → e.2 ∈ Cz)
    (ord : U → ℕ) (hord : Function.Injective ord)
    (hseg : ∀ a, a ∉ Ux → ∀ b ∈ Ux, ord a < ord b)
    (c' : U → F) (hc' : ∀ a ∈ Cz, ∀ b ∈ Cz, c' a = c' b → a = b)
    (x₀ : U → F) (hx₀ : Feasible F G (univ \ Ux) x₀) :
    coverRowExtSum G (univ \ Ux) x₀
        (fun x => ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c')) ≤
      2 ^ kappaFixed G Fr Ux x₀ c' *
        ∏ u ∈ Ux, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
          grIntNum G ς e (Fintype.card F) n ord Fr Cz u) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  set M : U → ℝ := fun b => if b ∈ Ux then (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord b *
      grIntNum G ς e (Fintype.card F) n ord Fr Cz b else Fintype.card F with hM
  have hnum0 : ∀ b, 0 ≤ grIntNum G ς e (Fintype.card F) n ord Fr Cz b := fun b => by
    unfold grIntNum
    have he0 := he.nonneg (intS G ord Fr b) n (Nat.cast_nonneg n)
    have hs : 0 ≤ ∑ b' ∈ Cz, (2 : ℝ) ^ intExp G ς Fr b b' :=
      sum_nonneg fun _ _ => by positivity
    exact add_nonneg (add_nonneg zero_le_one he0) (mul_nonneg (by positivity) hs)
  have hM0 : ∀ b, 0 ≤ M b := fun b => by
    simp only [hM]
    split_ifs
    · exact mul_nonneg (by positivity) (hnum0 b)
    · exact hq0.le
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord a ≤ ord b → y a = y' a) →
        intPhi G ς ord Fr Ux Cz c' b y = intPhi G ς ord Fr Ux Cz c' b y' := by
    intro b _ y y' hyy
    unfold intPhi
    split_ifs
    · have hm : intMerges G ord Fr c' y b = intMerges G ord Fr c' y' b := by
        unfold intMerges
        refine sum_congr rfl fun i hi => ?_
        have hi' : ord i < ord b := by
          simpa [coverRowEarlier] using (mem_filter.mp hi).1
        rw [hyy i (mem_univ i) hi'.le]
      rw [hyy b (mem_univ b) le_rfl, hm]
    · rfl
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord b) x' b,
          intPhi G ς ord Fr Ux Cz c' b (Function.update x' b c) ≤ M b := by
    intro b _ x' hx'
    by_cases hb : b ∈ Ux
    · have hupd : ∀ c, intPhi G ς ord Fr Ux Cz c' b (Function.update x' b c) =
          intWHat G ς Fr Cz c' b c * ((2 : ℝ) ^ intMerges G ord Fr c' x' b)⁻¹ := by
        intro c
        have hm : intMerges G ord Fr c' (Function.update x' b c) b =
            intMerges G ord Fr c' x' b := by
          unfold intMerges
          refine sum_congr rfl fun i hi => ?_
          have hib : i ≠ b := by
            rintro rfl
            have : ord i < ord i := by simpa [coverRowEarlier] using (mem_filter.mp hi).1
            exact lt_irrefl _ this
          rw [Function.update_of_ne hib]
        simp only [intPhi, hb, ↓reduceIte, Function.update_self, hm]
      rw [sum_congr rfl fun c _ => hupd c]
      simp only [hM, hb, ↓reduceIte]
      exact gr_integrated_oneVertex hW G ς hς n e he Fr hFr Ux Cz hH ord c' hc' b hb x' hx'
    · simp only [intPhi, hM, hb, ↓reduceIte, sum_const, nsmul_eq_mul, mul_one]
      exact_mod_cast card_le_univ _
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := fun y hy => by
    rw [extCount_univ G hy, Nat.cast_one]
  have hseq := coverRow_seq_upper G (C := univ) (ord := ord) (fun a _ b _ h => hord h)
    (intPhi G ς ord Fr Ux Cz c') M 1 (fun b y => intPhi_nonneg G ς ord Fr Ux Cz c' b y) hM0
    zero_le_one hloc hstep hK Ux.card Ux rfl (subset_univ _)
    (fun b hb b' _ hb' => hseg b' hb' b hb) x₀ hx₀
  have hMprod : ∏ b ∈ Ux, M b = ∏ u ∈ Ux, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ ordT G ord u *
      grIntNum G ς e (Fintype.card F) n ord Fr Cz u) :=
    prod_congr rfl fun b hb => by simp only [hM, hb, ↓reduceIte]
  have hpt : ∀ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a),
      ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e y c') ≤
        2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
    intro y hy
    rw [prod_free_eq_prod_intW]
    refine intW_prod_le G ς ord Fr hFr Ux Cz hH hseg x₀ c' y fun i hi => ?_
    exact (mem_filter.mp hy).2 i (mem_sdiff.mpr ⟨mem_univ i, hi⟩)
  calc coverRowExtSum G (univ \ Ux) x₀
        (fun x => ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c'))
      ≤ ∑ y ∈ (injLabellings F G).filter (fun y => ∀ a ∈ univ \ Ux, y a = x₀ a),
          2 ^ kappaFixed G Fr Ux x₀ c' * ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y := by
        unfold coverRowExtSum
        exact sum_le_sum hpt
    _ = 2 ^ kappaFixed G Fr Ux x₀ c' * coverRowExtSum G (univ \ Ux) x₀
          (fun y => ∏ u ∈ Ux, intPhi G ς ord Fr Ux Cz c' u y) := by
        unfold coverRowExtSum
        rw [mul_sum]
    _ ≤ 2 ^ kappaFixed G Fr Ux x₀ c' * (1 * ∏ b ∈ Ux, M b) :=
        mul_le_mul_of_nonneg_left hseq (by positivity)
    _ = _ := by rw [one_mul, hMprod]


end GrIntegrated


/-! ## The two error pairs -/

section GrInstances

/-- **The coarse error is an error function**: `e_t(q, n') = 2^t (h_t r + n' r²)`
(`eq:graphs:et`; `it:et:compare`, `it:et:poly`). -/
theorem grErr_coarse {q : ℝ} (hq : 1 ≤ q) (n : ℕ) :
    GrErr q n (fun t n' => coarseError t q n') where
  upper t _ hn' := upperError_le_coarseError hq hn' t
  lower t := coverRow_softError_le hq n t
  mono _ hn' _ _ htt := coarseError_mono hn' htt
  nonneg t _ hn' := coarseError_nonneg hn' t

/-- The graded lower error `e^-_t(n') = (𝔈_t + 2^t n')/q = e^+_t + 2^t n' r²` of
`eq:graphs:graded` (`𝔈_t = a_t √q + b_t`, `softError`), the error of the graded pair of
`def:graphs:error-pair` (`graded_isErrorPair`). -/
noncomputable def grGraded (q : ℝ) (t : ℕ) (n' : ℝ) : ℝ := (softError q t + 2 ^ t * n') / q

theorem gr_gradedA_succ (t : ℕ) : gradedA t ≤ gradedA (t + 1) := by
  unfold gradedA
  rcases t with _ | m
  · norm_num
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    have e1 : ((m + 1 + 1 : ℕ) : ℝ) = (m : ℝ) + 2 := by push_cast; ring
    have e2 : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by push_cast; ring
    rw [e1, e2, pow_succ]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    nlinarith

theorem gr_gradedB_succ (t : ℕ) : gradedB t ≤ gradedB (t + 1) := by
  unfold gradedB
  rcases t with _ | m
  · norm_num
  · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    have h2 : (0 : ℝ) < 2 ^ m := by positivity
    rw [pow_succ]
    linarith

theorem gr_softError_mono (q : ℝ) {t t' : ℕ} (htt : t ≤ t') : softError q t ≤ softError q t' := by
  have hA : gradedA t ≤ gradedA t' := monotone_nat_of_le_succ gr_gradedA_succ htt
  have hB : gradedB t ≤ gradedB t' := monotone_nat_of_le_succ gr_gradedB_succ htt
  unfold softError
  have := mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg q)
  linarith

/-- `q e^+_t = 𝔈_t`. -/
theorem gr_mul_upperError {q : ℝ} (hq : 0 < q) (t : ℕ) : q * upperError t q = softError q t := by
  have h := mul_one_add_upperError hq t
  unfold softError
  linarith

/-- **The graded error is an error function** (*Graded errors*, `def:graphs:error-pair`):
`e^+_t ≤ e^-_t(n')` (`it:et:compare`), `𝔈_t + 2^t n = q e^-_t(n)` (exactly), monotone in `t`
(`a_t`, `b_t` nondecreasing, `it:et:poly`) and nonnegative. -/
theorem grErr_graded {q : ℝ} (hq : 0 < q) (n : ℕ) : GrErr q n (grGraded q) where
  upper t n' hn' := by
    unfold grGraded
    rw [le_div_iff₀ hq, mul_comm, gr_mul_upperError hq t]
    have : (0 : ℝ) ≤ 2 ^ t * n' := mul_nonneg (by positivity) hn'
    linarith
  lower t := by
    unfold grGraded
    rw [mul_div_cancel₀ _ hq.ne']
  mono n' hn' t t' htt := by
    unfold grGraded
    refine div_le_div_of_nonneg_right ?_ hq.le
    have h1 := gr_softError_mono q htt
    have h2 : (2 : ℝ) ^ t * n' ≤ 2 ^ t' * n' :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) htt) hn'
    linarith
  nonneg t n' hn' := by
    unfold grGraded
    have h1 := softError_nonneg q t
    have h2 : (0 : ℝ) ≤ 2 ^ t * n' := mul_nonneg (by positivity) hn'
    positivity

end GrInstances


end Sarkozy.ExtractionK

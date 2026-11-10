module

public import Sarkozy.Labellings.Extension

@[expose] public section

/-!
# Counts with merged roots (`lem:extraction-merged-count`)

`paper/sections/16_extraction.tex` (`lem:extraction-merged-count`), with the count errors of
`paper/sections/12_labellings.tex` (`eq:graphs:et`, `eq:graphs:graded`, `it:et:mono`,
`it:et:compare`, `it:et:poly`) and `lem:extension`(b). Throughout `F` is a finite field with
`q` elements (`F = 𝔽_p`, `q = p`, in the paper), `χ = quadraticChar F`, and `r = q^{-1/2}`.

* `coarseH`, `coarseError`: `h_t = t/2 - 1 + 2^{-t}` and the coarse count error
  `e_t(q, n) = 2^t (h_t r + n r²)` of `eq:graphs:et`. `upperError` is the graded upper count
  error `e^+_t = a_t r + b_t r²` of `eq:graphs:graded`, with `a_t = gradedA t`,
  `b_t = gradedB t` of `Sarkozy.Labellings`.
* `gradedA_add_gradedB_eq` is `it:et:compare`, `a_t + b_t = 2^t h_t`; hence
  `upperError_le_coarseError`, `e^+_t ≤ e_t(q, n)` for `q ≥ 1` and `n ≥ 0`.
* `coarseError_mono` is the monotonicity in `t` of `it:et:poly`: for `n ≥ 0`, `e_t(q, n)` is
  nondecreasing in `t` (the increment `2^{t+1}h_{t+1} - 2^t h_t = t 2^{t-1}` comes from the
  increments of `it:et:mono`).
* `two_pow_mul_card_admissible_le`, `card_admissible_le`: `lem:extension`(b) in the paper's
  form `|Φ| ≤ q 2^{-t}(1 + e^+_t)`, from `Sarkozy.Labellings.extension_bounds`.
* `merged_count_le_fintype` (roots indexed by arbitrary finite types) and `merged_count_le`,
  `merged_count_le'` (indices `Fin t`, `Fin h`) are the two inequalities of
  `lem:extraction-merged-count`: with `μ_m = mergedCount β γ = #{(i, l) : β_i = γ_l}`,
  `∑_{y ∉ 𝒳, χ(y - β_i) = s_i ∀ i} ∏_l (1 + s'_l χ(y - γ_l))
    ≤ q 2^{-t} 2^{μ_m} (1 + e_{t+h-μ_m}(q, n')) ≤ q 2^{-t} 2^{μ_m} (1 + e_{t+h}(q, n'))`.

`WeilBound F` is Weil's theorem (`thm:weil`(a)), the literature input; it enters only as a
hypothesis, through `lem:extension`. No hypothesis on the characteristic is needed here.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Labellings

/-! ## Count errors (`eq:graphs:et`, `eq:graphs:graded`, `it:et:mono`, `it:et:compare`,
`it:et:poly`) -/

/-- `h_t = t/2 - 1 + 2^{-t}` (`eq:graphs:et`). -/
noncomputable def coarseH (t : ℕ) : ℝ := (t : ℝ) / 2 - 1 + (2 : ℝ)⁻¹ ^ t

/-- The coarse count error `e_t(q, n) = 2^t (h_t r + n r²)` with `r = q^{-1/2}`
(`eq:graphs:et`; the paper writes `e_t(p, n)`). -/
noncomputable def coarseError (t : ℕ) (q n : ℝ) : ℝ :=
  2 ^ t * (coarseH t * (Real.sqrt q)⁻¹ + n * (Real.sqrt q)⁻¹ ^ 2)

/-- The graded upper count error `e^+_t = a_t r + b_t r²` with `r = q^{-1/2}`
(`eq:graphs:graded`). -/
noncomputable def upperError (t : ℕ) (q : ℝ) : ℝ :=
  gradedA t * (Real.sqrt q)⁻¹ + gradedB t * (Real.sqrt q)⁻¹ ^ 2

/-- `2^t h_t = t 2^t / 2 - 2^t + 1`. -/
theorem two_pow_mul_coarseH (t : ℕ) :
    (2 : ℝ) ^ t * coarseH t = (t : ℝ) * 2 ^ t / 2 - 2 ^ t + 1 := by
  have h : (2 : ℝ) ^ t * (2 : ℝ)⁻¹ ^ t = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
  unfold coarseH
  rw [mul_add, h]
  ring

/-- **`it:et:compare`**: `a_t + b_t = 2^t h_t`. -/
theorem gradedA_add_gradedB_eq (t : ℕ) : gradedA t + gradedB t = 2 ^ t * coarseH t := by
  rw [two_pow_mul_coarseH]
  unfold gradedA gradedB
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · norm_num
  · obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := ⟨t - 1, by omega⟩
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
    push_cast
    rw [pow_succ]
    ring

private theorem gradedB_nonneg_aux (t : ℕ) : 0 ≤ gradedB t := by
  unfold gradedB
  split_ifs with h0
  · exact le_rfl
  · have : (1 : ℝ) ≤ 2 ^ (t - 1) := one_le_pow₀ (by norm_num)
    linarith

/-- The closed form `e_t(q, n) = (t 2^t / 2 - 2^t + 1) r + 2^t n r²`. -/
theorem coarseError_eq (t : ℕ) (q n : ℝ) :
    coarseError t q n =
      ((t : ℝ) * 2 ^ t / 2 - 2 ^ t + 1) * (Real.sqrt q)⁻¹ + 2 ^ t * n * (Real.sqrt q)⁻¹ ^ 2 := by
  unfold coarseError
  rw [← two_pow_mul_coarseH]
  ring

/-- **`it:et:compare`**: `e^+_t ≤ e_t(q, n)` for `q ≥ 1` and `n ≥ 0`; the difference is
`b_t (r - r²) + 2^t n r²`. -/
theorem upperError_le_coarseError {q n : ℝ} (hq : 1 ≤ q) (hn : 0 ≤ n) (t : ℕ) :
    upperError t q ≤ coarseError t q n := by
  unfold upperError coarseError
  have hr0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hr1 : (Real.sqrt q)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hq)
  have hb := gradedB_nonneg_aux t
  have hexp : (2 : ℝ) ^ t * (coarseH t * (Real.sqrt q)⁻¹ + n * (Real.sqrt q)⁻¹ ^ 2) =
      (gradedA t + gradedB t) * (Real.sqrt q)⁻¹ + 2 ^ t * n * (Real.sqrt q)⁻¹ ^ 2 := by
    rw [gradedA_add_gradedB_eq]
    ring
  rw [hexp]
  have h1 : 0 ≤ gradedB t * ((Real.sqrt q)⁻¹ * (1 - (Real.sqrt q)⁻¹)) :=
    mul_nonneg hb (mul_nonneg hr0 (by linarith))
  have h2 : 0 ≤ (2 : ℝ) ^ t * n * (Real.sqrt q)⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hn) (sq_nonneg _)
  nlinarith [h1, h2]

/-- **`it:et:poly`** (monotonicity in `t`): for `n ≥ 0`, `e_t(q, n)` is nondecreasing in `t`.
The increment is `e_{t+1}(q, n) - e_t(q, n) = 2^t (t r / 2 + n r²)`: by the closed form
`coarseError_eq`, `2^{t+1}h_{t+1} - 2^t h_t = t 2^{t-1}`, which is the sum of the increments
`a_{t+1} - a_t` and `b_{t+1} - b_t` of `it:et:mono` (by `it:et:compare`). -/
theorem coarseError_mono {q n : ℝ} (hn : 0 ≤ n) {t t' : ℕ} (htt : t ≤ t') :
    coarseError t q n ≤ coarseError t' q n := by
  refine monotone_nat_of_le_succ (f := fun k => coarseError k q n) (fun k => ?_) htt
  simp only [coarseError_eq]
  have hr0 : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h1 : 0 ≤ (k : ℝ) * 2 ^ k * (Real.sqrt q)⁻¹ := by positivity
  have h2 : 0 ≤ (2 : ℝ) ^ k * n * (Real.sqrt q)⁻¹ ^ 2 :=
    mul_nonneg (mul_nonneg (by positivity) hn) (sq_nonneg _)
  have hp : (2 : ℝ) ^ (k + 1) = 2 ^ k * 2 := pow_succ 2 k
  push_cast
  rw [hp]
  nlinarith [h1, h2]

/-- `e_t(q, n) ≥ 0` for `n ≥ 0`. -/
theorem coarseError_nonneg {q n : ℝ} (hn : 0 ≤ n) (t : ℕ) : 0 ≤ coarseError t q n := by
  have h0 : coarseError 0 q n = n * (Real.sqrt q)⁻¹ ^ 2 := by
    unfold coarseError coarseH
    push_cast
    ring
  have h0' : 0 ≤ coarseError 0 q n := by
    rw [h0]
    exact mul_nonneg hn (sq_nonneg _)
  exact h0'.trans (coarseError_mono hn (Nat.zero_le t))

/-- `q (1 + e^+_t) = q + (a_t √q + b_t)` for `q > 0`. -/
theorem mul_one_add_upperError {q : ℝ} (hq : 0 < q) (t : ℕ) :
    q * (1 + upperError t q) = q + (gradedA t * Real.sqrt q + gradedB t) := by
  unfold upperError
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have hsq : Real.sqrt q ^ 2 = q := Real.sq_sqrt hq.le
  have hs0 : Real.sqrt q ≠ 0 := hs.ne'
  calc q * (1 + (gradedA t * (Real.sqrt q)⁻¹ + gradedB t * (Real.sqrt q)⁻¹ ^ 2))
      = Real.sqrt q ^ 2 *
          (1 + (gradedA t * (Real.sqrt q)⁻¹ + gradedB t * (Real.sqrt q)⁻¹ ^ 2)) := by
        rw [hsq]
    _ = Real.sqrt q ^ 2 + (gradedA t * Real.sqrt q + gradedB t) := by
        field_simp
    _ = q + (gradedA t * Real.sqrt q + gradedB t) := by rw [hsq]

/-! ## `lem:extension`(b) in the paper's form -/

/-- **`lem:extension`(b)** in the form `2^t |Φ| ≤ q (1 + e^+_t)`, whatever the size of `𝒳`
(from `Sarkozy.Labellings.extension_bounds`; `WeilBound F` is Weil's theorem). -/
theorem two_pow_mul_card_admissible_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hW : WeilBound F) {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F)
    (hβ : Function.Injective β) (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (𝒳 : Finset F)
    (h𝒳 : ∀ i, β i ∈ 𝒳) :
    (2 : ℝ) ^ Fintype.card ι * (admissible β s 𝒳).card ≤
      Fintype.card F * (1 + upperError (Fintype.card ι) (Fintype.card F)) := by
  rw [mul_one_add_upperError (by exact_mod_cast Fintype.card_pos)]
  exact (extension_bounds hW β hβ s hs 𝒳 h𝒳).1

/-- **`lem:extension`(b)**: `|Φ| ≤ q 2^{-t} (1 + e^+_t)`, whatever the size of `𝒳`. -/
theorem card_admissible_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hW : WeilBound F) {ι : Type*} [Fintype ι] [DecidableEq ι] (β : ι → F)
    (hβ : Function.Injective β) (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (𝒳 : Finset F)
    (h𝒳 : ∀ i, β i ∈ 𝒳) :
    ((admissible β s 𝒳).card : ℝ) ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ Fintype.card ι *
        (1 + upperError (Fintype.card ι) (Fintype.card F)) := by
  have h := two_pow_mul_card_admissible_le hW β hβ s hs 𝒳 h𝒳
  have hinv : (2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ Fintype.card ι = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  calc ((admissible β s 𝒳).card : ℝ)
      = (2 : ℝ)⁻¹ ^ Fintype.card ι * (2 ^ Fintype.card ι * (admissible β s 𝒳).card) := by
        rw [← mul_assoc, hinv, one_mul]
    _ ≤ (2 : ℝ)⁻¹ ^ Fintype.card ι *
          (Fintype.card F * (1 + upperError (Fintype.card ι) (Fintype.card F))) :=
        mul_le_mul_of_nonneg_left h (by positivity)
    _ = _ := by ring

/-! ## Merged roots -/

/-- The number `μ_m = #{(i, l) : β_i = γ_l}` of merged roots (`lem:extraction-merged-count`). -/
def mergedCount {F : Type*} [DecidableEq F] {ι κ : Type*} [Fintype ι] [Fintype κ] (β : ι → F)
    (γ : κ → F) : ℕ :=
  (univ.filter fun il : ι × κ => β il.1 = γ il.2).card

/-- For injective `β`, each merged root pairs one `β_i` with one `γ_l`, so the unmerged `γ_l`
number `|κ| - μ_m`. -/
theorem card_unmerged_add_mergedCount {F : Type*} [DecidableEq F] {ι κ : Type*} [Fintype ι]
    [Fintype κ] (β : ι → F) (hβ : Function.Injective β) (γ : κ → F) :
    (univ.filter fun l : κ => ∀ i, β i ≠ γ l).card + mergedCount β γ = Fintype.card κ := by
  classical
  have himage : (univ.filter fun il : ι × κ => β il.1 = γ il.2).image (Prod.snd : ι × κ → κ) =
      univ.filter fun l : κ => ¬ ∀ i, β i ≠ γ l := by
    ext l
    simp only [mem_image, mem_filter, mem_univ, true_and, not_forall, not_not, Prod.exists]
    constructor
    · rintro ⟨i, l', h, rfl⟩
      exact ⟨i, h⟩
    · rintro ⟨i, h⟩
      exact ⟨i, l, h, rfl⟩
  have hinj : Set.InjOn (Prod.snd : ι × κ → κ)
      ((univ.filter fun il : ι × κ => β il.1 = γ il.2 : Finset (ι × κ)) : Set (ι × κ)) := by
    rintro ⟨i, l⟩ hil ⟨i', l'⟩ hil' hll
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hil hil'
    have hl : l = l' := hll
    subst hl
    rw [hβ (hil.trans hil'.symm)]
  unfold mergedCount
  rw [← card_image_of_injOn hinj, himage, card_filter_add_card_filter_not, card_univ]

/-- **`lem:extraction-merged-count`**, first inequality, for roots indexed by finite types `ι`
(`t = |ι|`) and `κ` (`h = |κ|`): for distinct `β_i`, distinct `γ_l`, signs `s_i, s'_l = ±1`,
`𝒳` containing all roots and `n' ≥ 0`,
`∑_{y ∉ 𝒳, χ(y - β_i) = s_i ∀ i} ∏_l (1 + s'_l χ(y - γ_l)) ≤ q 2^{-t} 2^{μ_m}
(1 + e_{t+h-μ_m}(q, n'))`. `WeilBound F` is Weil's theorem, the literature input of
`lem:extension`(b). -/
theorem merged_count_le_fintype {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hW : WeilBound F) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (β : ι → F) (hβ : Function.Injective β) (γ : κ → F) (hγ : Function.Injective γ)
    (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (s' : κ → ℤ) (hs' : ∀ l, s' l = 1 ∨ s' l = -1)
    (𝒳 : Finset F) (hβX : ∀ i, β i ∈ 𝒳) (hγX : ∀ l, γ l ∈ 𝒳) {n' : ℝ} (hn' : 0 ≤ n') :
    (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
        ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ *
        (1 + coarseError (Fintype.card ι + Fintype.card κ - mergedCount β γ)
          (Fintype.card F) n') := by
  -- Step 1: for `y ∉ 𝒳` each factor is `0` or `2`, so the sum is `2^h` times the number of
  -- `y ∉ 𝒳` satisfying the `t + h` conditions.
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
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have he0 := coarseError_nonneg (q := Fintype.card F) hn'
    (Fintype.card ι + Fintype.card κ - mergedCount β γ)
  by_cases hbad : ∃ i l, β i = γ l ∧ s i ≠ s' l
  · -- Two conditions at a merged root are incompatible: there is no solution.
    obtain ⟨i, l, hil, hsl⟩ := hbad
    have hΨ0 : ((univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i)).filter
        fun y => ∀ l, quadraticChar F (y - γ l) = s' l) = ∅ := by
      refine eq_empty_of_forall_notMem fun y hy => hsl ?_
      simp only [mem_filter, mem_univ, true_and] at hy
      rw [← hy.1.2 i, ← hy.2 l, hil]
    rw [hΨ0, card_empty, Nat.cast_zero, zero_mul]
    exact mul_nonneg (by positivity) (by linarith)
  · -- Conditions at a merged root coincide: the solutions are those of the `t + h - μ_m`
    -- conditions at the distinct roots `β_i` and the unmerged `γ_l`.
    push Not at hbad
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
    have hup := upperError_le_coarseError hq1 hn'
      (Fintype.card ι + Fintype.card κ - mergedCount β γ)
    have hpow_k : (2 : ℝ) ^ (Fintype.card ι + Fintype.card κ - mergedCount β γ) =
        2 ^ Fintype.card ι * 2 ^ Fintype.card {l : κ // ∀ i, β i ≠ γ l} := by
      rw [← hk, Fintype.card_sum, pow_add]
    have hpow_h : (2 : ℝ) ^ Fintype.card κ =
        2 ^ Fintype.card {l : κ // ∀ i, β i ≠ γ l} * 2 ^ mergedCount β γ := by
      rw [← pow_add, hcardU]
    have hinv : (2 : ℝ) ^ Fintype.card ι * (2 : ℝ)⁻¹ ^ Fintype.card ι = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ two_ne_zero, one_pow]
    have hfac : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ := by positivity
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
      _ ≤ (Fintype.card F * (1 + coarseError (Fintype.card ι + Fintype.card κ - mergedCount β γ)
              (Fintype.card F) n')) * ((2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (by linarith) (by linarith)) hfac
      _ = _ := by ring

/-- **`lem:extraction-merged-count`**, second inequality, for arbitrary finite index types:
the bound with `e_{t+h}(q, n')` (since `e_t(q, n')` is nondecreasing in `t`, `it:et:poly`). -/
theorem merged_count_le_fintype' {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hW : WeilBound F) {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (β : ι → F) (hβ : Function.Injective β) (γ : κ → F) (hγ : Function.Injective γ)
    (s : ι → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1) (s' : κ → ℤ) (hs' : ∀ l, s' l = 1 ∨ s' l = -1)
    (𝒳 : Finset F) (hβX : ∀ i, β i ∈ 𝒳) (hγX : ∀ l, γ l ∈ 𝒳) {n' : ℝ} (hn' : 0 ≤ n') :
    (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
        ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ Fintype.card ι * 2 ^ mergedCount β γ *
        (1 + coarseError (Fintype.card ι + Fintype.card κ) (Fintype.card F) n') := by
  refine (merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn').trans ?_
  have hmono := coarseError_mono (q := Fintype.card F) hn'
    (Nat.sub_le (Fintype.card ι + Fintype.card κ) (mergedCount β γ))
  exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- **`lem:extraction-merged-count`** (first inequality): for distinct `β_1, …, β_t`, distinct
`γ_1, …, γ_h`, signs `s_i, s'_l ∈ {±1}`, `𝒳 ⊆ F` containing all `β_i` and `γ_l`, and `n' ≥ 0`,
`∑_{y ∉ 𝒳, χ(y - β_i) = s_i ∀ i} ∏_l (1 + s'_l χ(y - γ_l)) ≤ q 2^{-t} 2^{μ_m}
(1 + e_{t+h-μ_m}(q, n'))`, `μ_m = #{(i, l) : β_i = γ_l}` (`mergedCount`). The proof uses
`lem:extension`(b) and `it:et:compare`; `WeilBound F` is Weil's theorem (literature input). -/
theorem merged_count_le {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hW : WeilBound F)
    {t h : ℕ} (β : Fin t → F) (hβ : Function.Injective β) (γ : Fin h → F)
    (hγ : Function.Injective γ) (s : Fin t → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (s' : Fin h → ℤ) (hs' : ∀ l, s' l = 1 ∨ s' l = -1) (𝒳 : Finset F) (hβX : ∀ i, β i ∈ 𝒳)
    (hγX : ∀ l, γ l ∈ 𝒳) {n' : ℝ} (hn' : 0 ≤ n') :
    (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
        ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ t * 2 ^ mergedCount β γ *
        (1 + coarseError (t + h - mergedCount β γ) (Fintype.card F) n') := by
  have hb := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn'
  simp only [Fintype.card_fin] at hb
  convert hb using 3

/-- **`lem:extraction-merged-count`** (second inequality): the same sum is at most
`q 2^{-t} 2^{μ_m} (1 + e_{t+h}(q, n'))`, since `e_t(q, n')` is nondecreasing in `t`
(`it:et:poly`). `WeilBound F` is Weil's theorem (literature input). -/
theorem merged_count_le' {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hW : WeilBound F)
    {t h : ℕ} (β : Fin t → F) (hβ : Function.Injective β) (γ : Fin h → F)
    (hγ : Function.Injective γ) (s : Fin t → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (s' : Fin h → ℤ) (hs' : ∀ l, s' l = 1 ∨ s' l = -1) (𝒳 : Finset F) (hβX : ∀ i, β i ∈ 𝒳)
    (hγX : ∀ l, γ l ∈ 𝒳) {n' : ℝ} (hn' : 0 ≤ n') :
    (∑ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
        ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l))) ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ t * 2 ^ mergedCount β γ *
        (1 + coarseError (t + h) (Fintype.card F) n') := by
  have hb := merged_count_le_fintype' hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn'
  simp only [Fintype.card_fin] at hb
  convert hb using 3

end Sarkozy.Extraction

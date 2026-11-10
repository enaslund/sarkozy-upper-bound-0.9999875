module

public import Sarkozy.ExtractionK.SoftPinnedExtraction
public import Sarkozy.ExtractionK.SoftGeneral

@[expose] public section

/-!
# Soft pinned compressed classes for every odd prime (`cor:soft-kernels`(c), `prop:pinned-extraction`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(c) for `prop:pinned-extraction`, without the
condition `χ(-1) = -1` of `SoftPinnedExtraction.lean`.

* The pinned chain of `PinnedExtractionCore.lean` / `PinnedExtraction.lean` restated for cross
  signs merely nonzero in `F` (`hς : ς ≠ 0 → (ς : F) ≠ 0`): `speg_integrated_le`,
  `speg_coverRows_le`, `speg_alpha_sq_le`, `speg_one_side_le`, `speg_other_side_le`,
  `speg_class_count`, `speg_class_sum_le`, `speg_extraction_sum_le`. The proofs are those of the
  original files; `ς ∈ {0, ±1}` was used only for `χ(ς) = ±1`, which holds for every nonzero
  sign (`quadraticChar_dichotomy`); `spe_pinSwap_castF` for the transposed signs.
* With a non-square integer `ν` (`χ(ν) = -1`), a free pair with `D_e < 0` is flipped by `ν`
  (`skFlipN`, `sk_softKer_expandN` of `SoftGeneral.lean`): `spe_soft_extraction_sum_le_g`,
  `spe_soft_pinned_extraction_g`, `spe_soft_pinned_extraction_buckets_g`.
* Over `𝔽_p`, `p` odd (`sk_exists_nonsquare_int`): **`spe_soft_pinned_extraction_zmod`**
  (`eq:push:pinnedclass`) and **`spe_soft_pinned_extraction_buckets_zmod`** (`N^pin`) for all
  coefficients `|D_e| ≤ 1`, with no sign condition.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SpegChain

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem spe_pinSwap_castF {n : ℕ} {ς : Fin n → Fin n → ℤ}
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) :
    ∀ i j, pinSwap ς i j ≠ 0 → ((pinSwap ς i j : ℤ) : F) ≠ 0 := by
  intro i j h
  unfold pinSwap at h ⊢
  have h' : ς j i ≠ 0 := fun h0 => h (by rw [h0, neg_zero])
  push_cast
  exact neg_ne_zero.mpr (hς j i h')

/-- **Step 6 (pinned)**: the sum over the completions of `(x₀_{C_x}, x₀_V)` of the free
product of the integrated vertices is at most `∏_{u ∈ U_x} peNum` (no merges: the pins have their
roots in `𝓜`, which the cross roots avoid). -/
theorem speg_integrated_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V Cx Cz : Finset (Fin n))
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (x₀ : Fin n → F) (y : Fin n → F)
    (hy : y ∈ pinLab M pin) :
    ∑ x ∈ peFib (pinLab M pin) Cx V (restr Cx x₀) (restr V x₀),
        ∏ e ∈ Fr.filter (fun e => e.1 ∈ univ \ (V ∪ Cx)), (1 + chiPair ς e x (restr Cz y)) ≤
      ∏ u ∈ univ \ (V ∪ Cx),
        peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card := by
  set Ux := univ \ (V ∪ Cx) with hUx
  obtain ⟨hyinj, hyM, -⟩ := mem_pinLab_iff.mp hy
  set c' := restr Cz y
  set g : Fin n → F → ℝ := fun i t => if i ∈ Ux then intW ς Fr c' i t else 1 with hg
  have hint : ∀ x : Fin n → F,
      ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x c') = ∏ i, g i (x i) := by
    intro x
    rw [prod_free_eq_prod_intW]
    simp only [hg]
    rw [prod_ite_mem_eq]
  rw [sum_congr rfl fun x _ => hint x]
  have hg0 : ∀ i t, 0 ≤ g i t := by
    intro i t
    simp only [hg]
    split_ifs
    · exact prod_nonneg fun _ _ => (pin_one_add_chi _).1
    · exact zero_le_one
  refine (pe_sum_prod_le _ (fun i => if i ∈ Ux then pinAllowed M pin i else {x₀ i}) ?_ g hg0).trans
    ?_
  · intro x hx i
    obtain ⟨hxI, hxc, hxv⟩ := mem_peFib.mp hx
    split_ifs with hi
    · exact (mem_pinLab.mp hxI).2 i
    · rw [mem_singleton]
      have hi' : i ∈ V ∪ Cx := by
        by_contra h
        exact hi (mem_sdiff.mpr ⟨mem_univ _, h⟩)
      rcases mem_union.mp hi' with hiV | hiC
      · have := congrFun hxv i
        simpa [restr, hiV] using this
      · have := congrFun hxc i
        simpa [restr, hiC] using this
  · have hsplit : ∏ i, ∑ t ∈ (if i ∈ Ux then pinAllowed M pin i else {x₀ i}), g i t =
        ∏ i, (if i ∈ Ux then ∑ t ∈ pinAllowed M pin i, intW ς Fr c' i t else 1) := by
      refine prod_congr rfl fun i _ => ?_
      split_ifs with hi
      · exact sum_congr rfl fun t _ => by simp only [hg, hi, ↓reduceIte]
      · simp only [hg, hi, ↓reduceIte, sum_singleton]
    rw [hsplit, prod_ite_mem_eq]
    refine prod_le_prod₀ (fun u _ => sum_nonneg fun t _ => prod_nonneg fun _ _ =>
      (pin_one_add_chi _).1) fun u hu => ?_
    -- one integrated vertex
    have hHC : ∀ b ∈ intH Fr u, b ∈ Cz := by
      intro b hb
      have hub : (u, b) ∈ Fr := by simpa [intH] using hb
      refine hFr1 (u, b) hub ?_
      have := (mem_sdiff.mp hu).2
      simp only [mem_union, not_or] at this
      exact this.2
    set κ := ↥(intH Fr u)
    let γ : κ → F := fun b => c' b.1
    have hγ : Function.Injective γ := by
      intro a b hab
      simp only [γ, c', restr_apply_of_mem (hHC a.1 a.2), restr_apply_of_mem (hHC b.1 b.2)] at hab
      exact Subtype.ext (hyinj hab)
    have hγM : ∀ l, γ l ∉ M := by
      intro l
      simp only [γ, c', restr_apply_of_mem (hHC l.1 l.2)]
      exact hyM l.1
    let s' : κ → ℤ := fun b => quadraticChar F (-(ς u b.1 : F))
    have hs' : ∀ b, s' b = 1 ∨ s' b = -1 := by
      intro b
      have hb : ς u b.1 ≠ 0 := hFrς (u, b.1) (by simpa [intH] using b.2)
      exact quadraticChar_dichotomy (neg_ne_zero.mpr (hς u b.1 hb))
    have heq : ∀ t, intW ς Fr c' u t = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) := by
      intro t
      unfold intW
      rw [← prod_coe_sort (intH Fr u)]
      refine prod_congr rfl fun b _ => ?_
      simp only [s', γ]
      have : (ς u b.1 : F) * (c' b.1 - t) = -(ς u b.1 : F) * (t - c' b.1) := by ring
      rw [this, map_mul, Int.cast_mul]
    rw [sum_congr rfl fun t _ => heq t]
    have h1 := pe_one_le hW M pin hpin hpinM u γ hγ hγM s' hs' (Cz.image c')
      (fun l => mem_image_of_mem c' (hHC l.1 l.2))
    have hcard : ((Cz.image c').card : ℝ) ≤ n := by
      have : (Cz.image c').card ≤ n :=
        card_image_le.trans ((card_le_univ Cz).trans (by simp))
      exact_mod_cast this
    have hκ : Fintype.card κ = (intH Fr u).card := Fintype.card_coe _
    rw [hκ] at h1
    unfold peNum
    have : ((Cz.image c').card : ℝ) * 2 ^ (intH Fr u).card ≤ (n : ℝ) * 2 ^ (intH Fr u).card :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    linarith

/-- **Step 7 (pinned cover rows)**: for `x ∈ 𝓘_pin`, the sum over the labels `c'` of `C_z`
occurring in `𝓘_pin` of the free product of the pairs at `C_z` is at most `∏_{b ∈ C_z} peNum`. -/
theorem speg_coverRows_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (Cz : Finset (Fin n)) (x : Fin n → F)
    (hx : x ∈ pinLab M pin) :
    ∑ c' ∈ (pinLab M pin).image (restr Cz),
        ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') ≤
      ∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card := by
  obtain ⟨hxinj, hxM, -⟩ := mem_pinLab_iff.mp hx
  set g : Fin n → F → ℝ := fun i t => if i ∈ Cz then peCovW ς Fr x i t else 1 with hg
  have hint : ∀ c' : Fin n → F,
      ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') = ∏ i, g i (c' i) := by
    intro c'
    rw [pe_prod_col]
    simp only [hg]
    rw [prod_ite_mem_eq]
  rw [sum_congr rfl fun c' _ => hint c']
  have hg0 : ∀ i t, 0 ≤ g i t := by
    intro i t
    simp only [hg]
    split_ifs
    · exact prod_nonneg fun _ _ => (pin_one_add_chi _).1
    · exact zero_le_one
  refine (pe_sum_prod_le _ (fun i => if i ∈ Cz then pinAllowed M pin i else {0}) ?_ g hg0).trans ?_
  · intro c' hc' i
    obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
    split_ifs with hi
    · rw [restr_apply_of_mem hi]
      exact (mem_pinLab.mp hy).2 i
    · simp [restr, hi]
  · have hsplit : ∏ i, ∑ t ∈ (if i ∈ Cz then pinAllowed M pin i else {0}), g i t =
        ∏ i, (if i ∈ Cz then ∑ t ∈ pinAllowed M pin i, peCovW ς Fr x i t else 1) := by
      refine prod_congr rfl fun i _ => ?_
      split_ifs with hi
      · exact sum_congr rfl fun t _ => by simp only [hg, hi, ↓reduceIte]
      · simp only [hg, hi, ↓reduceIte, sum_singleton]
    rw [hsplit, prod_ite_mem_eq]
    refine prod_le_prod₀ (fun b _ => sum_nonneg fun t _ => prod_nonneg fun _ _ =>
      (pin_one_add_chi _).1) fun b _ => ?_
    set κ := ↥(peColH Fr b)
    let γ : κ → F := fun a => x a.1
    have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hxinj h)
    have hγM : ∀ l, γ l ∉ M := fun l => hxM l.1
    let s' : κ → ℤ := fun a => quadraticChar F (ς a.1 b : F)
    have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
      have ha : ς a.1 b ≠ 0 := hFrς (a.1, b) (by simpa [peColH] using a.2)
      exact quadraticChar_dichotomy (hς a.1 b ha)
    have heq : ∀ t, peCovW ς Fr x b t = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) := by
      intro t
      unfold peCovW
      rw [← prod_coe_sort (peColH Fr b)]
      refine prod_congr rfl fun a _ => ?_
      simp only [s', γ, map_mul, Int.cast_mul]
    rw [sum_congr rfl fun t _ => heq t]
    have h1 := pe_one_le hW M pin hpin hpinM b γ hγ hγM s' hs' (univ.image x)
      (fun l => mem_image_of_mem x (mem_univ _))
    have hcard : ((univ.image x).card : ℝ) ≤ n := by
      have : (univ.image x).card ≤ n := card_image_le.trans (by simp)
      exact_mod_cast this
    have hκ : Fintype.card κ = (peColH Fr b).card := Fintype.card_coe _
    rw [hκ] at h1
    unfold peNum
    have : ((univ.image x).card : ℝ) * 2 ^ (peColH Fr b).card ≤
        (n : ℝ) * 2 ^ (peColH Fr b).card :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    linarith

/-- **Steps 5–6 (pinned) for one fibre**:
`𝖺_{c,c'}(v)² ≤ 2^{f_V} ∏_{u ∈ U_x} peNum · ∑_{fibre} f(x)² Θ₁⁺(x, c')`. -/
theorem speg_alpha_sq_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V Cx Cz : Finset (Fin n)) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (f : (Fin n → F) → ℝ) (c c' v : Fin n → F)
    (hc' : c' ∈ (pinLab M pin).image (restr Cz)) :
    peAlpha (pinLab M pin) ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx),
          peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card) *
        ∑ x ∈ peFib (pinLab M pin) Cx V c v, f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' := by
  set I := pinLab M pin
  set Ux := univ \ (V ∪ Cx) with hUx
  set MU := ∏ u ∈ Ux, peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set g : (Fin n → F) → ℝ := fun x => groupPos ς Fr (predOne Cx Cz) x c' with hg
  have hg0 : ∀ x, 0 ≤ g x := fun x => groupPos_nonneg ς Fr _ x c'
  have hMU0 : 0 ≤ MU := prod_nonneg fun u _ => peNum_nonneg _ _ _ _ _ (Nat.cast_nonneg _)
  by_cases hne : (peFib I Cx V c v).Nonempty
  swap
  · rw [not_nonempty_iff_eq_empty] at hne
    unfold peAlpha
    rw [hne, sum_empty, sum_empty]
    simp
  obtain ⟨x₀, hx₀⟩ := hne
  obtain ⟨-, hx₀c, hx₀v⟩ := mem_peFib.mp hx₀
  obtain ⟨y, hy, rfl⟩ := mem_image.mp hc'
  have hfib : peFib I Cx V c v = peFib I Cx V (restr Cx x₀) (restr V x₀) := by
    rw [hx₀c, hx₀v]
  have hm := speg_integrated_le hW M pin hpin hpinM ς hς Fr hFrς V Cx Cz hFr1 x₀ y hy
  rw [← hfib] at hm
  have hsumg : ∑ x ∈ peFib I Cx V c v, g x ≤ 2 ^ fV * MU := by
    calc ∑ x ∈ peFib I Cx V c v, g x
        ≤ ∑ x ∈ peFib I Cx V c v, 2 ^ fV *
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x (restr Cz y)) := by
          refine sum_le_sum fun x _ => ?_
          simp only [hg]
          rw [groupPos_one_split ς Fr V Cx Cz hVC hFr1 x (restr Cz y)]
          exact mul_le_mul_of_nonneg_right (prod_free_le_two_pow ς _ x (restr Cz y))
            (prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x (restr Cz y))
      _ = 2 ^ fV * ∑ x ∈ peFib I Cx V c v,
            ∏ e ∈ Fr.filter (fun e => e.1 ∈ Ux), (1 + chiPair ς e x (restr Cz y)) := by
          rw [mul_sum]
      _ ≤ 2 ^ fV * MU := mul_le_mul_of_nonneg_left hm (by positivity)
  have hα : |peAlpha I ς P Fr V Cx Cz f c (restr Cz y) v| ≤
      ∑ x ∈ peFib I Cx V c v, g x * |f x| := by
    unfold peAlpha
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (abs_groupKer_le ς P Fr _ x _) (abs_nonneg _)
  have hcs := weighted_cs (peFib I Cx V c v) g f (fun x _ => hg0 x)
  have hS0 : 0 ≤ ∑ x ∈ peFib I Cx V c v, g x * f x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hg0 x) (sq_nonneg _)
  calc peAlpha I ς P Fr V Cx Cz f c (restr Cz y) v ^ 2
      = |peAlpha I ς P Fr V Cx Cz f c (restr Cz y) v| ^ 2 := (sq_abs _).symm
    _ ≤ (∑ x ∈ peFib I Cx V c v, g x * |f x|) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) hα 2
    _ ≤ (∑ x ∈ peFib I Cx V c v, g x) * ∑ x ∈ peFib I Cx V c v, g x * f x ^ 2 := hcs
    _ ≤ (2 ^ fV * MU) * ∑ x ∈ peFib I Cx V c v, g x * f x ^ 2 :=
        mul_le_mul_of_nonneg_right hsumg hS0
    _ = _ := by
        rw [mul_sum, mul_sum]
        exact sum_congr rfl fun x _ => by simp only [hg]; ring

/-- **One side of `prop:pinned-extraction` (Steps 5–7)**, counting form:
`∑_{c,c'} |Γ| ‖𝖺_{c,c'}‖² ≤ 2^{f_V} ∏_{u ∈ U_x} peNum ∏_{b ∈ C_z} peNum ∑_{x ∈ 𝓘_pin} f(x)²`. -/
theorem speg_one_side_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V Cx Cz : Finset (Fin n)) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hFr1 : ∀ e ∈ Fr, e.1 ∉ Cx → e.2 ∈ Cz) (f : (Fin n → F) → ℝ) :
    ∑ c ∈ (pinLab M pin).image (restr Cx), ∑ c' ∈ (pinLab M pin).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha (pinLab M pin) ς P Fr V Cx Cz f c c' v ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
        (∏ u ∈ univ \ (V ∪ Cx),
          peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card) *
        (∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card) *
        ∑ x ∈ pinLab M pin, f x ^ 2 := by
  set I := pinLab M pin
  set Ix := I.image (restr Cx)
  set Iz := I.image (restr Cz)
  set K := 2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
    (∏ u ∈ univ \ (V ∪ Cx), peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card)
    with hK
  set MC := ∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card
  have hK0 : 0 ≤ K := mul_nonneg (by positivity)
    (prod_nonneg fun u _ => peNum_nonneg _ _ _ _ _ (Nat.cast_nonneg _))
  set Prow : (Fin n → F) → (Fin n → F) → ℝ := fun x c' =>
    ∏ e ∈ Fr.filter (fun e => e.2 ∈ Cz), (1 + chiPair ς e x c') with hProw
  have hProw0 : ∀ x c', 0 ≤ Prow x c' := fun x c' =>
    prod_nonneg fun e _ => one_add_chiPair_nonneg ς e x c'
  have hI : ∀ x ∈ I, Function.Injective x := fun x hx => (mem_pinLab_iff.mp hx).1
  have hstep : ∀ c ∈ Ix, ∀ c' ∈ Iz,
      |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
    intro c _ c' hc'
    have hv : ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2 ≤
        K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
          groupPos ς Fr (predOne Cx Cz) x c' := by
      calc ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2
          ≤ ∑ v ∈ injTuples F V, K * ∑ x ∈ peFib I Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' :=
            sum_le_sum fun v _ => speg_alpha_sq_le hW M pin hpin hpinM ς hς P Fr hFrς V Cx Cz hVC
              hFr1 f c c' v hc'
        _ = K * ∑ v ∈ injTuples F V, ∑ x ∈ peFib I Cx V c v, f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c' := by rw [mul_sum]
        _ = _ := by
            congr 1
            rw [← sum_fiberwise_of_maps_to (s := I.filter (fun x => restr Cx x = c))
              (g := restr V) (t := injTuples F V)
              (fun x hx => pe_restr_mem_injTuples V (hI x (mem_filter.mp hx).1))]
            refine sum_congr rfl fun v _ => ?_
            unfold peFib
            rw [filter_filter]
    have hΓ : ∀ x ∈ I.filter (fun x => restr Cx x = c),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c') ≤ f x ^ 2 * Prow x c' := by
      intro x hx
      have hxc := (mem_filter.mp hx).2
      have hg : groupPos ς Fr (predGam Cx Cz) c c' = groupPos ς Fr (predGam Cx Cz) x c' :=
        groupPos_congr ς Fr _ fun e he => ⟨(restr_eq_iff hxc he.1).symm, rfl⟩
      have h1 := abs_groupKer_le ς P Fr (predGam Cx Cz) c c'
      rw [hg] at h1
      have h0 : 0 ≤ f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c' :=
        mul_nonneg (sq_nonneg _) (groupPos_nonneg ς Fr _ x c')
      calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c')
          ≤ groupPos ς Fr (predGam Cx Cz) x c' *
            (f x ^ 2 * groupPos ς Fr (predOne Cx Cz) x c') := mul_le_mul_of_nonneg_right h1 h0
        _ = f x ^ 2 * (groupPos ς Fr (predOne Cx Cz) x c' *
              groupPos ς Fr (predGam Cx Cz) x c') := by ring
        _ = f x ^ 2 * Prow x c' := by rw [pe_groupPos_one_mul_gam]
    calc |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2
        ≤ |groupKer ς P Fr (predGam Cx Cz) c c'| *
            (K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c') :=
          mul_le_mul_of_nonneg_left hv (abs_nonneg _)
      _ = K * ∑ x ∈ I.filter (fun x => restr Cx x = c),
            |groupKer ς P Fr (predGam Cx Cz) c c'| * (f x ^ 2 *
              groupPos ς Fr (predOne Cx Cz) x c') := by
          rw [mul_sum, mul_sum, mul_sum]
          exact sum_congr rfl fun x _ => by ring
      _ ≤ K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
          mul_le_mul_of_nonneg_left (sum_le_sum hΓ) hK0
  have hrow : ∀ x ∈ I, ∑ c' ∈ Iz, Prow x c' ≤ MC := fun x hx =>
    speg_coverRows_le hW M pin hpin hpinM ς hς Fr hFrς Cz x hx
  calc ∑ c ∈ Ix, ∑ c' ∈ Iz, |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ v ∈ injTuples F V, peAlpha I ς P Fr V Cx Cz f c c' v ^ 2
      ≤ ∑ c ∈ Ix, ∑ c' ∈ Iz, K * ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' :=
        sum_le_sum fun c hc => sum_le_sum fun c' hc' => hstep c hc c' hc'
    _ = K * ∑ c' ∈ Iz, ∑ c ∈ Ix, ∑ x ∈ I.filter (fun x => restr Cx x = c), f x ^ 2 * Prow x c' := by
        rw [sum_comm, mul_sum]
        refine sum_congr rfl fun c' _ => ?_
        rw [mul_sum]
    _ = K * ∑ c' ∈ Iz, ∑ x ∈ I, f x ^ 2 * Prow x c' := by
        congr 1
        refine sum_congr rfl fun c' _ => ?_
        exact sum_fiberwise_of_maps_to (fun x hx => mem_image_of_mem _ hx) _
    _ = K * ∑ x ∈ I, f x ^ 2 * ∑ c' ∈ Iz, Prow x c' := by
        rw [sum_comm]
        congr 1
        exact sum_congr rfl fun x _ => by rw [mul_sum]
    _ ≤ K * ∑ x ∈ I, f x ^ 2 * MC :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun x hx =>
          mul_le_mul_of_nonneg_left (hrow x hx) (sq_nonneg _)) hK0
    _ = _ := by
        rw [← sum_mul]
        ring

/-- **The other side (Step 8)**: the transposed class `𝒞(Pᵀ, Aᵀ)` for the support
`{(j, i) : (i, j) ∈ E_×}` with the signs `-ς_{ji}` (`pinSwap`), the same pinned law on both rows;
no symmetry of `E_×` is used. Its counts are the column counts on `U_z` and the row counts on
`C_x`. -/
theorem speg_other_side_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (W Cx Cz : Finset (Fin n)) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hFr2 : ∀ e ∈ Fr, e.2 ∉ Cz → e.1 ∈ Cx) (h : (Fin n → F) → ℝ) :
    ∑ c ∈ (pinLab M pin).image (restr Cx), ∑ c' ∈ (pinLab M pin).image (restr Cz),
        |groupKer ς P Fr (predGam Cx Cz) c c'| *
          ∑ w ∈ injTuples F W, peBeta (pinLab M pin) ς P Fr W Cx Cz h c c' w ^ 2 ≤
      2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
        (∏ u ∈ univ \ (W ∪ Cz),
          peNum (Fintype.card F) n M.card (pinCount pin u) (peColH Fr u).card) *
        (∏ b ∈ Cx, peNum (Fintype.card F) n M.card (pinCount pin b) (intH Fr b).card) *
        ∑ x ∈ pinLab M pin, h x ^ 2 := by
  have hT := speg_one_side_le hW M pin hpin hpinM (pinSwap ς) (spe_pinSwap_castF hς)
    (P.image Prod.swap) (Fr.image Prod.swap)
    (fun e he => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      simp only [pinSwap, Prod.fst_swap, Prod.snd_swap, neg_ne_zero]
      exact hFrς e₀ he₀)
    W Cz Cx hWC
    (fun e he h1 => by
      obtain ⟨e₀, he₀, rfl⟩ := mem_image.mp he
      exact hFr2 e₀ he₀ h1) h
  rw [card_filter_swap] at hT
  simp only [pe_intH_swap, pe_colH_swap] at hT
  refine le_trans (le_of_eq ?_) hT
  rw [sum_comm]
  refine sum_congr rfl fun c' _ => sum_congr rfl fun c _ => ?_
  rw [pe_gam_swap]
  congr 1
  exact sum_congr rfl fun w _ => by rw [pe_beta_eq_alpha_swap]

/-- **`prop:pinned-extraction`, counting form of the class bound**:
`|∑_{x, y ∈ 𝓘_pin} f(x) K_𝒞(x, y) h(y)| ≤ Λ (2^{f_V} M_{U_x} M_{C_z} ∑ f²)^{1/2}
(2^{f_W} M_{U_z} M_{C_x} ∑ h²)^{1/2}` with `M_S = ∏_{v ∈ S} peNum`. -/
theorem speg_class_count (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (V W Cx Cz : Finset (Fin n)) (hVC : ∀ u ∈ V, u ∉ Cx)
    (hWC : ∀ u ∈ W, u ∉ Cz) (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W) Λ)
    (f h : (Fin n → F) → ℝ) :
    |∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * classKer ς P Fr x x' * h x'| ≤
      Λ * Real.sqrt (2 ^ (Fr.filter (fun e => e.1 ∈ V)).card *
          (∏ u ∈ univ \ (V ∪ Cx),
            peNum (Fintype.card F) n M.card (pinCount pin u) (intH Fr u).card) *
          (∏ b ∈ Cz, peNum (Fintype.card F) n M.card (pinCount pin b) (peColH Fr b).card) *
          ∑ x ∈ pinLab M pin, f x ^ 2) *
        Real.sqrt (2 ^ (Fr.filter (fun e => e.2 ∈ W)).card *
          (∏ u ∈ univ \ (W ∪ Cz),
            peNum (Fintype.card F) n M.card (pinCount pin u) (peColH Fr u).card) *
          (∏ b ∈ Cx, peNum (Fintype.card F) n M.card (pinCount pin b) (intH Fr b).card) *
          ∑ x ∈ pinLab M pin, h x ^ 2) := by
  refine (pe_bilinear_le (pinLab M pin) (fun x hx => (mem_pinLab_iff.mp hx).1) ς P Fr V W Cx Cz
    hVC hWC hP hFr hΛ hker f h).trans ?_
  have h1 := speg_one_side_le hW M pin hpin hpinM ς hς P Fr hFrς V Cx Cz hVC
    (fun e he h1 => (hFr e he).resolve_left h1) f
  have h2 := speg_other_side_le hW M pin hpin hpinM ς hς P Fr hFrς W Cx Cz hWC
    (fun e he h2 => (hFr e he).resolve_right h2) h
  exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt h1) hΛ)
    (Real.sqrt_le_sqrt h2) (Real.sqrt_nonneg _) (mul_nonneg hΛ (Real.sqrt_nonneg _))

/-- **`prop:pinned-extraction`, the class bound** (Steps 1–8, any witness size `k`): with the
pinned law `μ` uniform on `𝓘_pin`, `e^pin_ϖ < 1`, a class with a witness (`|V| = |W| = k`) and a
cover, and the kernel hypothesis `‖𝖶‖ ≤ c_ker r^k` on injective tuples,
`|E_{x,y∼μ} f(x) K_𝒞(x,y) h(y)| ≤ c_ker r^k (2^{f_V + f_W + ϖ_V + ϖ_W} ∏_v F^pin_v)^{1/2}
(1 - e^pin_ϖ)^{-k} ‖f‖_μ ‖h‖_μ`, `ϖ_V`, `ϖ_W` the numbers of pins of the witness vertices (each
witness label contributes the factor `2^{ϖ_v}` of its pins). Written with `E_μ = |𝓘_pin|⁻¹ ∑`.
The counting route needs no completion ratio `R_pin`. -/
theorem speg_class_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * classKer ς P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  set z := M.card
  set I := pinLab M pin
  set N : ℝ := (I.card : ℝ)
  set Ux := univ \ (V ∪ Cx)
  set Uz := univ \ (W ∪ Cz)
  set fV := (Fr.filter (fun e => e.1 ∈ V)).card
  set fW := (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, pinCount pin v
  set tW := ∑ v ∈ W, pinCount pin v
  set e := ePin q n z ϖ
  set ℓ : Fin n → ℝ := fun j => peLow q n z ϖ (pinCount pin j) with hℓ
  have hℓpos : ∀ j, 0 < ℓ j := fun j => peLow_pos hq0 he _
  have hΛ : 0 ≤ cker * Real.sqrt q ^ k := mul_nonneg hcker (by positivity)
  have hQ := speg_class_count hW M pin hpin hpinM ς hς P Fr hFrς V W Cx Cz hVC hWC hP hFr hΛ hker
    f h
  -- the lower count
  have hL : ∏ j, ℓ j ≤ N := by
    have := card_pinLab_ge hW M pin hpin hpinM ϖ hϖ he
    exact this
  have hL0 : 0 < ∏ j, ℓ j := prod_pos fun j _ => hℓpos j
  have hN0 : 0 < N := lt_of_lt_of_le hL0 hL
  -- the factor identities
  set PUx := ∏ u ∈ Ux, peF q n z ϖ (pinCount pin u) (intH Fr u).card
  set PCz := ∏ b ∈ Cz, peF q n z ϖ (pinCount pin b) (peColH Fr b).card
  set PUz := ∏ u ∈ Uz, peF q n z ϖ (pinCount pin u) (peColH Fr u).card
  set PCx := ∏ b ∈ Cx, peF q n z ϖ (pinCount pin b) (intH Fr b).card
  have hfac : ∀ (S : Finset (Fin n)) (hh : Fin n → ℕ),
      ∏ u ∈ S, peNum q n z (pinCount pin u) (hh u) =
        (∏ u ∈ S, peF q n z ϖ (pinCount pin u) (hh u)) * ∏ u ∈ S, ℓ u := by
    intro S hh
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun u _ => peNum_eq hq0 he _ _
  rw [hfac Ux (fun u => (intH Fr u).card), hfac Cz (fun b => (peColH Fr b).card),
    hfac Uz (fun u => (peColH Fr u).card), hfac Cx (fun b => (intH Fr b).card)] at hQ
  set A := (2 : ℝ) ^ fV * (PUx * ∏ u ∈ Ux, ℓ u) * (PCz * ∏ b ∈ Cz, ℓ b)
  set B := (2 : ℝ) ^ fW * (PUz * ∏ u ∈ Uz, ℓ u) * (PCx * ∏ b ∈ Cx, ℓ b)
  have hPUx0 : 0 ≤ PUx := prod_nonneg fun u _ => peF_nonneg hq0 he _ _
  have hPUz0 : 0 ≤ PUz := prod_nonneg fun u _ => peF_nonneg hq0 he _ _
  have hPCz0 : 0 ≤ PCz := prod_nonneg fun b _ => peF_nonneg hq0 he _ _
  have hPCx0 : 0 ≤ PCx := prod_nonneg fun b _ => peF_nonneg hq0 he _ _
  have hA0 : 0 ≤ A := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUx0 (prod_nonneg fun u _ => (hℓpos u).le)))
    (mul_nonneg hPCz0 (prod_nonneg fun u _ => (hℓpos u).le))
  have hB0 : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity)
    (mul_nonneg hPUz0 (prod_nonneg fun u _ => (hℓpos u).le)))
    (mul_nonneg hPCx0 (prod_nonneg fun u _ => (hℓpos u).le))
  have hnorm := normalize_le hN0 hL0 hL0 hL hL hA0 hB0
    (sum_nonneg fun x _ => sq_nonneg (f x)) (sum_nonneg fun x _ => sq_nonneg (h x)) hΛ hQ
  refine hnorm.trans ?_
  -- the witness factors
  set DV := ∏ v ∈ V, ℓ v
  set DW := ∏ v ∈ W, ℓ v
  have hDV : DV = q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k := by
    simp only [DV, hℓ, peLow]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hVk, prod_pow_eq_pow_sum]
  have hDW : DW = q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k := by
    simp only [DW, hℓ, peLow]
    rw [prod_mul_distrib, prod_mul_distrib, prod_const, prod_const, hWk, prod_pow_eq_pow_sum]
  have h1e : 0 < 1 - e := by linarith
  set PF := PUx * PCz * PUz * PCx
  have hsplitX : ∏ v, ℓ v = (∏ v ∈ Ux, ℓ v) * DV * ∏ v ∈ Cx, ℓ v :=
    prod_univ_three V Cx hVC ℓ
  have hsplitZ : ∏ v, ℓ v = (∏ v ∈ Uz, ℓ v) * DW * ∏ v ∈ Cz, ℓ v :=
    prod_univ_three W Cz hWC ℓ
  have hAB : A * B / ((∏ v, ℓ v) * ∏ v, ℓ v) = 2 ^ fV * 2 ^ fW * PF / (DV * DW) := by
    have h1 : (0 : ℝ) < ∏ v ∈ Ux, ℓ v := prod_pos fun v _ => hℓpos v
    have h2 : (0 : ℝ) < ∏ v ∈ Cx, ℓ v := prod_pos fun v _ => hℓpos v
    have h3 : (0 : ℝ) < ∏ v ∈ Uz, ℓ v := prod_pos fun v _ => hℓpos v
    have h4 : (0 : ℝ) < ∏ v ∈ Cz, ℓ v := prod_pos fun v _ => hℓpos v
    have h5 : (0 : ℝ) < DV := prod_pos fun v _ => hℓpos v
    have h6 : (0 : ℝ) < DW := prod_pos fun v _ => hℓpos v
    rw [show ((∏ v, ℓ v) * ∏ v, ℓ v) = ((∏ v ∈ Ux, ℓ v) * DV * ∏ v ∈ Cx, ℓ v) *
        ((∏ v ∈ Uz, ℓ v) * DW * ∏ v ∈ Cz, ℓ v) by rw [← hsplitX, ← hsplitZ]]
    simp only [A, B, PF]
    field_simp
  rw [hAB, hDV, hDW]
  have hinv : ((Real.sqrt q)⁻¹ ^ k) ^ 2 = (q ^ k)⁻¹ := by
    rw [inv_pow, inv_pow, sqrt_pow_sq hq0.le]
  have hsq : (cker * Real.sqrt q ^ k) ^ 2 *
      (2 ^ fV * 2 ^ fW * PF / ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) *
        (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k))) =
      (cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k) ^ 2 * (2 ^ (fV + fW + tV + tW) * PF) := by
    have e1 : (cker * Real.sqrt q ^ k) ^ 2 = cker ^ 2 * q ^ k := by
      rw [mul_pow, sqrt_pow_sq hq0.le]
    have e2 : (cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k) ^ 2 =
        cker ^ 2 * (q ^ k)⁻¹ / ((1 - e) ^ k) ^ 2 := by
      rw [div_pow, mul_pow, hinv]
    rw [e1, e2]
    simp only [pow_add, inv_pow]
    have hq' : (q ^ k) ≠ 0 := by positivity
    have he' : (1 - e) ^ k ≠ 0 := by positivity
    field_simp
  have hc' : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k := by positivity
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg hPUx0 hPCz0) hPUz0) hPCx0
  have hkey : cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
        ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) * (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k))) =
      cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) / (1 - e) ^ k := by
    calc cker * Real.sqrt q ^ k * Real.sqrt (2 ^ fV * 2 ^ fW * PF /
          ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) * (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k)))
        = Real.sqrt ((cker * Real.sqrt q ^ k) ^ 2 * (2 ^ fV * 2 ^ fW * PF /
            ((q ^ k * (2 : ℝ)⁻¹ ^ tV * (1 - e) ^ k) *
              (q ^ k * (2 : ℝ)⁻¹ ^ tW * (1 - e) ^ k)))) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hΛ]
      _ = Real.sqrt ((cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k) ^ 2 *
            (2 ^ (fV + fW + tV + tW) * PF)) := by rw [hsq]
      _ = cker * (Real.sqrt q)⁻¹ ^ k / (1 - e) ^ k *
            Real.sqrt (2 ^ (fV + fW + tV + tW) * PF) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc']
      _ = _ := by ring
  rw [hkey]
  unfold peFactor
  exact le_rfl

/-- **`eq:push:pinnedclass`** (`prop:pinned-extraction`, the class bound in the paper's form, any
witness size `k`; the paper has `k = 2`): under `e^pin_ϖ < 1` and `Δ_pin ≥ ϖ + |N_X(i)|,
ϖ + |N_Y(i)|`,
`|E_{x,y∼μ} f(x) K_𝒞(x, y) h(y)| ≤ c_ker r^k 2^{ex^pin/2 + kϖ} Λ^pin_0 exp(γ_pin 2^ϖ oc^pin)
‖f‖_μ ‖h‖_μ`, `ex^pin = f_V + f_W`, `2^{ex^pin/2}` written `√(2^{ex^pin})`. -/
theorem speg_extraction_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * classKer ς P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  refine (speg_class_sum_le hW M pin hpin hpinM ϖ hϖ he ς hς P Fr hFrς V W Cx Cz hVk hWk hVC hWC
    hP hFr hcker hker f h).trans ?_
  set e := ePin q n M.card ϖ
  set ex := (Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, pinCount pin v
  set tW := ∑ v ∈ W, pinCount pin v
  set R := (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ
  set γ := peGamma q n M.card Δ
  set oc := peOc Fr V W Cx Cz
  set PF := peFactor q n M.card ϖ pin Fr V W Cx Cz
  have h1e : 0 < 1 - e := by linarith
  have he0 : 0 ≤ e := ePin_nonneg _ _ _ _
  set Sf := Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card)
  set Sh := Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)
  have hSf : 0 ≤ Sf := Real.sqrt_nonneg _
  have hSh : 0 ≤ Sh := Real.sqrt_nonneg _
  have hPF := peFactor_le hq0 he pin hϖ ς hΔX hΔY Fr hFrς V W Cx Cz hVk hWk hVC hWC
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg
    (prod_nonneg fun u _ => peF_nonneg hq0 he _ _) (prod_nonneg fun u _ => peF_nonneg hq0 he _ _))
    (prod_nonneg fun u _ => peF_nonneg hq0 he _ _)) (prod_nonneg fun u _ => peF_nonneg hq0 he _ _)
  set E := Real.exp (γ * 2 ^ ϖ * oc + ((n - k : ℕ) : ℝ) * R) / (1 - e) ^ (n - k)
  have hE0 : 0 ≤ E := div_nonneg (Real.exp_pos _).le (pow_nonneg h1e.le _)
  have hsqPF : Real.sqrt PF ≤ E := by
    rw [← Real.sqrt_sq hE0]
    exact Real.sqrt_le_sqrt hPF
  have htV : tV ≤ k * ϖ := by
    calc tV ≤ ∑ _v ∈ V, ϖ := sum_le_sum fun v _ => hϖ v
      _ = k * ϖ := by rw [sum_const, hVk, smul_eq_mul]
  have htW : tW ≤ k * ϖ := by
    calc tW ≤ ∑ _v ∈ W, ϖ := sum_le_sum fun v _ => hϖ v
      _ = k * ϖ := by rw [sum_const, hWk, smul_eq_mul]
  have hsq2 : Real.sqrt ((2 : ℝ) ^ (tV + tW)) ≤ 2 ^ (k * ϖ) := by
    rw [show (2 : ℝ) ^ (k * ϖ) = Real.sqrt ((2 ^ (k * ϖ)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hsplit : Real.sqrt (2 ^ (ex + tV + tW) * PF) =
      Real.sqrt ((2 : ℝ) ^ ex) * Real.sqrt ((2 : ℝ) ^ (tV + tW)) * Real.sqrt PF := by
    rw [show ex + tV + tW = ex + (tV + tW) by ring, pow_add, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
  rw [hsplit]
  -- the constants
  have hR0 : 0 ≤ R := by positivity
  have hnk : ((n - k : ℕ) : ℝ) * R ≤ (Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ := by
    have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
    calc ((n - k : ℕ) : ℝ) * R ≤ n * R := mul_le_mul_of_nonneg_right this hR0
      _ = _ := by simp only [R]; ring
  have hRpin : 1 ≤ peRpin q n M.card ϖ := by
    unfold peRpin
    exact one_le_pow₀ (by rw [one_le_div h1e]; linarith)
  have hkn : k ≤ n := hVk ▸ (card_le_univ V).trans (by simp)
  have hconst : E / (1 - e) ^ k ≤ peLambda0 q n M.card ϖ Δ * Real.exp (γ * 2 ^ ϖ * oc) := by
    have hpow1 : (1 - e) ^ (n + 2) ≤ (1 - e) ^ (n - k) * (1 - e) ^ k := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one h1e.le (by linarith) (by omega)
    have hexp : Real.exp (((n - k : ℕ) : ℝ) * R) ≤
        Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) := Real.exp_le_exp.mpr hnk
    have hC : 0 < (1 - e) ^ (n + 2) := pow_pos h1e _
    have hR2 : 1 ≤ peRpin q n M.card ϖ ^ 2 := one_le_pow₀ hRpin
    have hnum : Real.exp (γ * 2 ^ ϖ * oc) * Real.exp (((n - k : ℕ) : ℝ) * R) ≤
        peRpin q n M.card ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) *
          Real.exp (γ * 2 ^ ϖ * oc) := by
      have h3 : Real.exp (((n - k : ℕ) : ℝ) * R) ≤
          peRpin q n M.card ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) :=
        hexp.trans (le_mul_of_one_le_left (Real.exp_pos _).le hR2)
      calc Real.exp (γ * 2 ^ ϖ * oc) * Real.exp (((n - k : ℕ) : ℝ) * R)
          ≤ Real.exp (γ * 2 ^ ϖ * oc) *
              (peRpin q n M.card ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ)) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = _ := by ring
    have key := div_le_div₀ (by positivity) hnum hC hpow1
    calc E / (1 - e) ^ k
        = Real.exp (γ * 2 ^ ϖ * oc) * Real.exp (((n - k : ℕ) : ℝ) * R) /
            ((1 - e) ^ (n - k) * (1 - e) ^ k) := by
          simp only [E]
          rw [Real.exp_add, div_div]
      _ ≤ _ := key
      _ = _ := by
          unfold peLambda0
          ring
  have hc0 : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k := by positivity
  have h2ex : 0 ≤ Real.sqrt ((2 : ℝ) ^ ex) := Real.sqrt_nonneg _
  calc cker * (Real.sqrt q)⁻¹ ^ k *
        (Real.sqrt ((2 : ℝ) ^ ex) * Real.sqrt ((2 : ℝ) ^ (tV + tW)) * Real.sqrt PF) /
        (1 - e) ^ k * Sf * Sh
      = (cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt ((2 : ℝ) ^ ex)) *
          (Real.sqrt ((2 : ℝ) ^ (tV + tW)) * (Real.sqrt PF / (1 - e) ^ k)) * Sf * Sh := by ring
    _ ≤ (cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt ((2 : ℝ) ^ ex)) *
          (2 ^ (k * ϖ) * (peLambda0 q n M.card ϖ Δ * Real.exp (γ * 2 ^ ϖ * oc))) * Sf * Sh := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc0 h2ex)) hSf) hSh
        refine mul_le_mul hsq2 ?_ (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg h1e.le _))
          (by positivity)
        calc Real.sqrt PF / (1 - e) ^ k ≤ E / (1 - e) ^ k :=
              div_le_div_of_nonneg_right hsqPF (pow_nonneg h1e.le _)
          _ ≤ _ := hconst
    _ = _ := by ring

end SpegChain


section SpegFlip

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem spe_pinNX_flipN {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (Fr : Finset (Fin n × Fin n)) {ν : ℤ} (hν : quadraticChar F (ν : F) = -1) (i : Fin n) :
    pinNX (skFlipN ς D Fr ν) i = pinNX ς i := by
  unfold pinNX
  exact filter_congr fun j _ => skFlipN_ne_zero_iff ς D Fr hν i j

theorem spe_pinNY_flipN {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (Fr : Finset (Fin n × Fin n)) {ν : ℤ} (hν : quadraticChar F (ν : F) = -1) (j : Fin n) :
    pinNY (skFlipN ς D Fr ν) j = pinNY ς j := by
  unfold pinNY
  exact filter_congr fun i _ => skFlipN_ne_zero_iff ς D Fr hν i j

end SpegFlip

section SpegSoft

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The bilinear sum of the soft kernel over any finite set of labellings is the weighted sum of
the Boolean sub-class sums (`sk_softKer_expand`). -/
theorem spe_soft_sum_eqN {n : ℕ} (I : Finset (Fin n → F)) (ς : Fin n → Fin n → ℤ)
    (D : Fin n × Fin n → ℝ) (P Fr : Finset (Fin n × Fin n)) (hPFr : Disjoint P Fr)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1) (f h : (Fin n → F) → ℝ) :
    ∑ x ∈ I, ∑ x' ∈ I, f x * skSoftKer ς D P Fr x x' * h x' =
      (∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
        ∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlipN ς D Fr ν) P T x x' * h x' := by
  simp only [sk_softKer_expandN ς D P Fr hPFr hν]
  calc ∑ x ∈ I, ∑ x' ∈ I,
        f x * ((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset,
          skW D Fr T * classKer (skFlipN ς D Fr ν) P T x x') * h x'
      = ∑ x ∈ I, ∑ x' ∈ I, ∑ T ∈ Fr.powerset,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        exact sum_congr rfl fun T _ => by ring
    _ = ∑ x ∈ I, ∑ T ∈ Fr.powerset, ∑ x' ∈ I,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) :=
        sum_congr rfl fun x _ => sum_comm
    _ = ∑ T ∈ Fr.powerset, ∑ x ∈ I, ∑ x' ∈ I,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) := sum_comm
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun T _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum, mul_sum]

/-- The convexity step: if every sub-class form is bounded by `B ≥ 0`, so is the soft form. -/
theorem spe_soft_le_of_subN {n : ℕ} (I : Finset (Fin n → F)) (ς : Fin n → Fin n → ℤ)
    (D : Fin n × Fin n → ℝ) (P Fr : Finset (Fin n × Fin n)) (hPFr : Disjoint P Fr)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1) (f h : (Fin n → F) → ℝ) {B : ℝ}
    (hB : ∀ T ∈ Fr.powerset,
      |(∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlipN ς D Fr ν) P T x x' * h x') /
        (I.card : ℝ) ^ 2| ≤ B) :
    |(∑ x ∈ I, ∑ x' ∈ I, f x * skSoftKer ς D P Fr x x' * h x') / (I.card : ℝ) ^ 2| ≤ B := by
  rw [spe_soft_sum_eqN I ς D P Fr hPFr hν f h]
  have hc : |∏ e ∈ P, D e| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun e _ => abs_nonneg _) (fun e he => hDP e he)
  have hw0 : ∀ T ∈ Fr.powerset, 0 ≤ skW D Fr T := fun T _ => skW_nonneg hDF T
  calc |((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
          (∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlipN ς D Fr ν) P T x x' * h x')) /
            (I.card : ℝ) ^ 2|
      = |∏ e ∈ P, D e| * |∑ T ∈ Fr.powerset, skW D Fr T *
          ((∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlipN ς D Fr ν) P T x x' * h x') /
            (I.card : ℝ) ^ 2)| := by
        rw [mul_div_assoc, abs_mul, sum_div]
        congr 2
        exact sum_congr rfl fun T _ => by ring
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T *
          |(∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlipN ς D Fr ν) P T x x' * h x') /
            (I.card : ℝ) ^ 2| := by
        refine mul_le_mul hc ?_ (abs_nonneg _) zero_le_one
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact sum_congr rfl fun T hT => by rw [abs_mul, abs_of_nonneg (hw0 T hT)]
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T * B := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun T hT' => ?_) zero_le_one
        exact mul_le_mul_of_nonneg_left (hB T hT') (hw0 T hT')
    _ = B := by rw [← sum_mul, skW_sum, one_mul, one_mul]

end SpegSoft

section SpegMain

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction`, sum form**: the soft class kernel
`K^D_𝒞 = ∑_{S ∈ 𝒞} D_S χ_S` (`skSoftKer`, `|D_e| ≤ 1`) of a pinned row satisfies the bound
`eq:push:pinnedclass` of the Boolean class (`speg_extraction_sum_le`), provided `χ(-1) = -1`
at the free pairs with a negative coefficient (`hν`; no condition when `D ≥ 0` on the free
pairs). -/
theorem spe_soft_extraction_sum_le_g (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (P Fr : Finset (Fin n × Fin n)) (hPFr : Disjoint P Fr)
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : Fin n × Fin n → ℝ) (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * skSoftKer ς D P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  refine spe_soft_le_of_subN (pinLab M pin) ς D P Fr hPFr hν hDP hDF f h ?_
  intro T hT
  rw [mem_powerset] at hT
  have hker' : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W)
      (rectKer (skFlipN ς D Fr ν) P V W) (cker * Real.sqrt (Fintype.card F) ^ k) := by
    rw [sk_rectKer_flipN ς D P Fr hPFr ν V W]
    exact hker
  have hb := speg_extraction_sum_le hW M pin hpin hpinM ϖ hϖ he (skFlipN ς D Fr ν)
    (skFlipN_castF ς hς D Fr hν) (fun i => by rw [spe_pinNX_flipN ς D Fr hν]; exact hΔX i)
    (fun i => by rw [spe_pinNY_flipN ς D Fr hν]; exact hΔY i) P T
    (fun e he => (skFlipN_ne_zero_iff ς D Fr hν e.1 e.2).mpr (hFrς e (hT he))) V W Cx Cz hVk hWk
    hVC hWC hP (fun e he => hFr e (hT he)) hcker hker' f h
  refine hb.trans ?_
  have hL0 : 0 ≤ peLambda0 (Fintype.card F) n M.card ϖ Δ := by
    unfold peLambda0 peRpin
    have he0 := ePin_nonneg (Fintype.card F : ℝ) n M.card ϖ
    have h1 : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
    exact div_nonneg (mul_nonneg (pow_nonneg (pow_nonneg (div_nonneg (by linarith) h1.le) _) _)
      (Real.exp_pos _).le) (pow_pos h1 _).le
  have hγ := spe_peGamma_nonneg (Fintype.card F : ℝ) n M.card Δ
  have hex : Real.sqrt ((2 : ℝ) ^ ((T.filter (fun e => e.1 ∈ V)).card +
      (T.filter (fun e => e.2 ∈ W)).card)) ≤
      Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card +
        (Fr.filter (fun e => e.2 ∈ W)).card)) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (spe_ex_mono hT V W))
  have hoc : Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc T V W Cx Cz) ≤
      Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (spe_peOc_mono hT V W Cx Cz) (by positivity))
  have h1 : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
  have h2 : 0 ≤ Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
      Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by positivity
  have h3 : (0 : ℝ) ≤ 2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ := by positivity
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc T V W Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)
      = (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card)) *
        (2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ) *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc T V W Cx Cz) *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by ring
    _ ≤ (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card +
          (Fr.filter (fun e => e.2 ∈ W)).card)) *
        (2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ) *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by
      gcongr
    _ = _ := by ring

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction`, `eq:push:pinnedclass`**: for a class
`𝒞(P, A)` of `Ex ⊆ E_×` with a witness and a cover, and coefficients `|D_e| ≤ 1` on `Ex`, the soft
class sum `∑_{S ∈ 𝒞} D_S ⟨f, T_S h⟩_μ` (pinned law `μ`) satisfies the bound of
`pinned_extraction`, provided `χ(-1) = -1` at the free pairs with a negative coefficient
(`hν`; e.g. `p ≡ 3 (mod 4)`, or `D ≥ 0` on the free pairs). -/
theorem spe_soft_pinned_extraction_g (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex P A : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (hcls : IsClassDatum Ex (P, A)) {k : ℕ} (w : Fin k → Fin n × Fin n)
    (hw : IsWitness Ex P A w) (Cx Cz : Finset (Fin n)) (hcov : IsCover Ex P A w Cx Cz)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : Fin n × Fin n → ℝ) (hD : ∀ e ∈ Ex, |D e| ≤ 1)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ (((Ex \ (P ∪ A)).filter (fun e => e.1 ∈ witV w)).card +
          ((Ex \ (P ∪ A)).filter (fun e => e.2 ∈ witW w)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ *
          peOc (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨hP, -, hPA⟩ := hcls
  have hK : ∀ x y : Fin n → F, ∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x y) =
      skSoftKer ς D P (Ex \ (P ∪ A)) x y := fun x y =>
    sk_sum_cls_eq Ex P A hP hPA (fun e => D e * chiPair ς e x y)
  simp only [hK]
  set Fr := Ex \ (P ∪ A) with hFr
  have hPFr : Disjoint P Fr := by
    rw [disjoint_left]
    intro e heP heF
    exact (mem_sdiff.mp heF).2 (mem_union_left _ heP)
  have hrect : ∀ e : Fin n × Fin n, e.1 ∈ witV w ∧ e.2 ∈ witW w ↔
      (∃ i, (w i).1 = e.1) ∧ ∃ l, (w l).2 = e.2 := by
    intro e
    simp [witV, witW]
  have hFrEx : ∀ e ∈ Fr, e ∈ Ex := fun e he => (mem_sdiff.mp he).1
  have hP' : ∀ e ∈ P, (e.1 ∈ witV w ∧ e.2 ∈ witW w) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    by_cases hr : e.1 ∈ witV w ∧ e.2 ∈ witW w
    · exact Or.inl hr
    · exact Or.inr (hcov.cover e (mem_union_left _ he) (by rwa [← hrect]))
  have hFr' : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (hFrEx e he) hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  have hVk : (witV w).card = k := by
    unfold witV
    rw [card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]
  have hWk : (witW w).card = k := by
    unfold witW
    rw [card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]
  exact spe_soft_extraction_sum_le_g hW M pin hpin hpinM ϖ hϖ he ς hς hΔX hΔY P Fr hPFr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' hcker
    hker D (fun e he => hD e (hP he)) (fun e he => hD e (hFrEx e he)) hν f h

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction`, the bucket sum `N^pin`**: for an exact
partition of the nonstar subsets of `Ex` and coefficients `|D_e| ≤ 1` on `Ex`, the soft nonstar
part `∑_{S nonstar} D_S T_S` of a pinned row satisfies the bound of `pinned_extraction_buckets`,
provided `χ(-1) = -1` at the pairs with a negative coefficient (`hν`). -/
theorem spe_soft_pinned_extraction_buckets_g (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (Fin n × Fin n) × Finset (Fin n × Fin n)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Fin 2 → Fin n × Fin n)
    (cx cz : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Finset (Fin n))
    (ck : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℝ)
    (bucket : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, Sarkozy.Influence.OpBound (injTuples F (witV (wit c)))
      (injTuples F (witW (wit c))) (rectKer ς c.1 (witV (wit c)) (witW (wit c)))
      (ck c * Real.sqrt (Fintype.card F) ^ 2))
    (hbucket : ∀ c ∈ 𝔓, peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (D : Fin n × Fin n → ℝ) (hD : ∀ e ∈ Ex, |D e| ≤ 1)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * peLambda0 (Fintype.card F) n M.card ϖ Δ * 2 ^ (2 * ϖ) *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
            ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
          Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨hdat, hdisj, hunion⟩ := h𝔓
  set I := pinLab M pin
  set N : ℝ := (I.card : ℝ)
  set r := (Real.sqrt (Fintype.card F))⁻¹
  set L := peLambda0 (Fintype.card F) n M.card ϖ Δ
  set γ := peGamma (Fintype.card F) n M.card Δ
  set Nf := Real.sqrt ((∑ x ∈ I, f x ^ 2) / N)
  set Nh := Real.sqrt ((∑ x ∈ I, h x ^ 2) / N)
  set exc := fun c : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) =>
    Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
      ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))
  have hsplit : ∀ x y : Fin n → F, (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y) := by
    intro x y
    rw [← hunion, sum_biUnion hdisj]
  have hform : (∑ x ∈ I, ∑ y ∈ I,
      f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2 =
      ∑ c ∈ 𝔓, (∑ x ∈ I, ∑ y ∈ I,
        f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2 := by
    rw [← sum_div]
    congr 1
    have hT : ∀ x y : Fin n → F,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y =
        ∑ c ∈ 𝔓, f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y := by
      intro x y
      rw [hsplit, mul_sum, sum_mul]
    calc ∑ x ∈ I, ∑ y ∈ I, f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y
        = ∑ x ∈ I, ∑ y ∈ I, ∑ c ∈ 𝔓,
            f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y :=
          sum_congr rfl fun x _ => sum_congr rfl fun y _ => hT x y
      _ = ∑ x ∈ I, ∑ c ∈ 𝔓, ∑ y ∈ I,
            f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y :=
          sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hform]
  have hγ : 0 ≤ γ := spe_peGamma_nonneg _ _ _ _
  have hL : 0 ≤ L := by
    have h1e : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
    simp only [L, peLambda0, peRpin]
    have : 0 ≤ (1 + ePin (Fintype.card F) n M.card ϖ) /
        (1 - ePin (Fintype.card F) n M.card ϖ) :=
      div_nonneg (by linarith [ePin_nonneg (Fintype.card F : ℝ) n M.card ϖ]) h1e.le
    positivity
  have hclass : ∀ c ∈ 𝔓, |(∑ x ∈ I, ∑ y ∈ I,
      f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2| ≤
      r ^ 2 * L * 2 ^ (2 * ϖ) * (ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) *
        Nf * Nh := by
    intro c hc
    have hb := spe_soft_pinned_extraction_g hW M pin hpin hpinM ϖ hϖ he ς hς hΔX hΔY Ex c.1 c.2
      hEx (hdat c hc) (wit c) (hwit c hc) (cx c) (cz c) (hcov c hc) (hck c hc) (hker c hc) D hD
      hν f h
    refine hb.trans ?_
    have hexp : Real.exp (γ * 2 ^ ϖ * peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
        (cx c) (cz c)) ≤ Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbucket c hc) (by positivity))
    have h0 : 0 ≤ ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L := by
      have := hck c hc
      positivity
    have hN : 0 ≤ Nf * Nh := by positivity
    calc ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L *
          Real.exp (γ * 2 ^ ϖ * peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
            (cz c)) * Nf * Nh
        = (ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L) *
          Real.exp (γ * 2 ^ ϖ * peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
            (cz c)) * (Nf * Nh) := by ring
      _ ≤ (ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L) *
            Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮)) * (Nf * Nh) := by
          gcongr
      _ = _ := by ring
  calc |∑ c ∈ 𝔓, (∑ x ∈ I, ∑ y ∈ I,
        f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2|
      ≤ ∑ c ∈ 𝔓, r ^ 2 * L * 2 ^ (2 * ϖ) *
          (ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) * Nf * Nh :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hclass)
    _ = r ^ 2 * L * 2 ^ (2 * ϖ) *
          (∑ c ∈ 𝔓, ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) * Nf * Nh := by
        rw [mul_sum, sum_mul, sum_mul]
    _ = r ^ 2 * L * 2 ^ (2 * ϖ) * (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * exc c) * Real.exp (γ * 2 ^ ϖ * (b * 2 ^ 𝔮))) * Nf * Nh := by
        congr 3
        rw [← sum_fiberwise_of_maps_to (fun c hc => mem_image_of_mem bucket hc)]
        refine sum_congr rfl fun b _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun c hc => ?_
        rw [(mem_filter.mp hc).2]

end SpegMain

section SpegZMod

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem spe_castF_of_pm {n : ℕ} {ς : Fin n → Fin n → ℤ}
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) :
    ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0 := by
  intro i j h
  rcases hς i j with h0 | h1 | h1
  · exact absurd h0 h
  · rw [h1]; simp
  · rw [h1]; simp

end SpegZMod

section SpegZModP

variable {p : ℕ} [Fact p.Prime]

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction` over `𝔽_p`, no sign condition**: for
every odd prime `p` and all coefficients `|D_e| ≤ 1` on `Ex`, the soft class sum of a pinned class
with a witness and a cover satisfies `eq:push:pinnedclass` (the bound of `pinned_extraction`). -/
theorem spe_soft_pinned_extraction_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p)) {n : ℕ}
    (M : Finset (ZMod p)) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card (ZMod p)) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex P A : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (hcls : IsClassDatum Ex (P, A)) {k : ℕ} (w : Fin k → Fin n × Fin n)
    (hw : IsWitness Ex P A w) (Cx Cz : Finset (Fin n)) (hcov : IsCover Ex P A w Cx Cz)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV w)) (injTuples (ZMod p) (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card (ZMod p)) ^ k))
    (D : Fin n × Fin n → ℝ) (hD : ∀ e ∈ Ex, |D e| ≤ 1)
    (f h : (Fin n → ZMod p) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ k *
        Real.sqrt (2 ^ (((Ex \ (P ∪ A)).filter (fun e => e.1 ∈ witV w)).card +
          ((Ex \ (P ∪ A)).filter (fun e => e.2 ∈ witW w)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card (ZMod p)) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card (ZMod p)) n M.card Δ * 2 ^ ϖ *
          peOc (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact spe_soft_pinned_extraction_g hW M pin hpin hpinM ϖ hϖ he ς (spe_castF_of_pm hς) hΔX hΔY
    Ex P A hEx hcls w hw Cx Cz hcov hcker hker D hD hν f h

/-- **`cor:soft-kernels`(c) for the pinned bucket sum `N^pin` over `𝔽_p`, no sign condition.** -/
theorem spe_soft_pinned_extraction_buckets_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p)) {n : ℕ}
    (M : Finset (ZMod p)) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card (ZMod p)) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (Fin n × Fin n) × Finset (Fin n × Fin n)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Fin 2 → Fin n × Fin n)
    (cx cz : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Finset (Fin n))
    (ck : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℝ)
    (bucket : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, Sarkozy.Influence.OpBound (injTuples (ZMod p) (witV (wit c)))
      (injTuples (ZMod p) (witW (wit c))) (rectKer ς c.1 (witV (wit c)) (witW (wit c)))
      (ck c * Real.sqrt (Fintype.card (ZMod p)) ^ 2))
    (hbucket : ∀ c ∈ 𝔓, peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (D : Fin n × Fin n → ℝ) (hD : ∀ e ∈ Ex, |D e| ≤ 1)
    (f h : (Fin n → ZMod p) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ 2 *
        peLambda0 (Fintype.card (ZMod p)) n M.card ϖ Δ * 2 ^ (2 * ϖ) *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
            ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
          Real.exp (peGamma (Fintype.card (ZMod p)) n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact spe_soft_pinned_extraction_buckets_g hW M pin hpin hpinM ϖ hϖ he ς (spe_castF_of_pm hς)
    hΔX hΔY Ex hEx 𝔓 h𝔓 wit cx cz ck bucket 𝔮 hwit hcov hck hker hbucket D hD hν f h

end SpegZModP

end Sarkozy.ExtractionK

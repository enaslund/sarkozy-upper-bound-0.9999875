module

public import Sarkozy.Cuts.CutCount

/-!
# Cuts, IX⁗: the mass `Z` (`lem:spec:cutkernel` (c), last claim)

`13_cuts_correlations.tex`, `lem:spec:cutkernel` (c): `2^{-m_×} R_cut^{-1} ≤ Z ≤ 2^{-m_×} R_cut`.
Label `U⁺` alone in the order `v_n, …, v_1`; then `v_i` has `t⁰_i` labelled neighbours (`t0deg`,
those in `G⁺`). The proof needs the following.

* `upperProd_halfList`, `lowerProd_halfList`, `nbrCount_halfSet`: the half count along this
  order.
* `tdeg_eq`, `sum_outdeg`: `t_i = t⁰_i + c_i`, where `c_i` counts the neighbours of `v_i` in `U⁻`,
  and `∑_i c_i = m_×`. (So `∑_i t_i - ∑_i t⁰_i = m_×`; the paper writes the two sums as
  `e(U⁺) + m_×` and `e(U⁺)`.)
* `cutZ_Rcut`: the bound.

Here the count error `e_{t⁰_i}` is taken with the same `n' ≥ |U|` as `e_{t_i}`. The paper uses
`e_{t⁰_i}(p, n) ≤ e_{t_i}(p, 2n)`; both are majorized by `e_{t_i}(p, n')`, which is all the proof
uses.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- `t⁰_i`: the number of `G⁺`-neighbours of `v_i` among `v_{i+1}, …, v_n`. -/
def t0deg (i : Fin D.cut.half.card) : ℕ :=
  (Finset.univ.filter (fun j : Fin D.cut.half.card => i < j ∧ D.Adj (D.vtx i) (D.vtx j))).card

/-- The list `v_{m-1}, …, v_0` in `U⁺`. -/
def halfList : (m : ℕ) → m ≤ D.cut.half.card → List D.cut.Half
  | 0, _ => []
  | m + 1, h => D.order ⟨m, h⟩ :: halfList m (Nat.le_of_succ_le h)

/-- `{v_j : j ≥ m}` in `U⁺`. -/
def halfSet (m : ℕ) : Finset D.cut.Half :=
  (Finset.univ.filter (fun j : Fin D.cut.half.card => m ≤ j.val)).image D.order

theorem mem_halfSet (m : ℕ) (u : D.cut.Half) :
    u ∈ D.halfSet m ↔ m ≤ (D.order.symm u).val := by
  simp only [halfSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨j, hj, rfl⟩
    simpa using hj
  · intro h
    exact ⟨D.order.symm u, h, by simp⟩

theorem halfSet_succ (m : ℕ) (h : m < D.cut.half.card) :
    insert (D.order ⟨m, h⟩) (D.halfSet (m + 1)) = D.halfSet m := by
  ext u
  rw [Finset.mem_insert, D.mem_halfSet, D.mem_halfSet]
  constructor
  · rintro (rfl | hu)
    · simp
    · omega
  · intro hu
    rcases Nat.eq_or_lt_of_le hu with h' | h'
    · left
      have : D.order.symm u = ⟨m, h⟩ := Fin.ext h'.symm
      rw [← this, Equiv.apply_symm_apply]
    · exact Or.inr h'

theorem halfSet_card : D.halfSet D.cut.half.card = ∅ := by
  ext u
  rw [D.mem_halfSet]
  simp only [Finset.notMem_empty, iff_false, not_le]
  exact (D.order.symm u).isLt

theorem nbrCount_halfSet (m : ℕ) (h : m < D.cut.half.card) :
    nbrCount D.halfGraph (D.halfSet (m + 1)) (D.order ⟨m, h⟩) = D.t0deg ⟨m, h⟩ := by
  classical
  unfold nbrCount t0deg
  symm
  refine Finset.card_nbij' (fun j => D.order j) (fun u => D.order.symm u) ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hj ⊢
    obtain ⟨hlt, hadj⟩ := hj
    refine ⟨(D.mem_halfSet _ _).2 (by simp only [Equiv.symm_apply_apply]; exact hlt), ?_⟩
    rw [D.mem_halfGraph, D.mem_halfGraph]
    exact (D.adj_symm).1 hadj
  · intro u hu
    simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hu ⊢
    obtain ⟨hmem, hadj⟩ := hu
    refine ⟨(D.mem_halfSet _ _).1 hmem, ?_⟩
    rw [D.mem_halfGraph, D.mem_halfGraph] at hadj
    have : D.vtx (D.order.symm u) = u.1 := by simp [vtx]
    rw [this]
    exact (D.adj_symm).1 hadj
  · intro j _
    exact D.order.symm_apply_apply j
  · intro u _
    exact D.order.apply_symm_apply u

theorem upperProd_halfList (q : ℝ) : ∀ (m : ℕ) (h : m ≤ D.cut.half.card),
    upperProd D.halfGraph q (D.halfSet m) (D.halfList m h) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m), stepUpper q (D.t0deg j)
  | 0, _ => by
      simp only [halfList, upperProd]
      rw [Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.prod_empty]
  | m + 1, h => by
      simp only [halfList, upperProd]
      rw [D.nbrCount_halfSet m h, D.halfSet_succ m h, upperProd_halfList q m (Nat.le_of_succ_le h)]
      have hsplit : Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m + 1) =
          insert ⟨m, h⟩ (Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · exact Or.inr hj'
          · exact Or.inl (Fin.ext hj')
        · rintro (rfl | hj)
          · exact Nat.lt_succ_self m
          · exact Nat.lt_succ_of_lt hj
      rw [hsplit, Finset.prod_insert (by simp)]

theorem lowerProd_halfList (q : ℝ) (nn : ℕ) : ∀ (m : ℕ) (h : m ≤ D.cut.half.card),
    lowerProd D.halfGraph q nn (D.halfSet m) (D.halfList m h) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m),
        stepLower q nn (D.t0deg j)
  | 0, _ => by
      simp only [halfList, lowerProd]
      rw [Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.prod_empty]
  | m + 1, h => by
      simp only [halfList, lowerProd]
      rw [D.nbrCount_halfSet m h, D.halfSet_succ m h,
        lowerProd_halfList q nn m (Nat.le_of_succ_le h)]
      have hsplit : Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m + 1) =
          insert ⟨m, h⟩ (Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m)) := by
        ext j
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
        constructor
        · intro hj
          rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
          · exact Or.inr hj'
          · exact Or.inl (Fin.ext hj')
        · rintro (rfl | hj)
          · exact Nat.lt_succ_self m
          · exact Nat.lt_succ_of_lt hj
      rw [hsplit, Finset.prod_insert (by simp)]

theorem mem_halfList : ∀ (m : ℕ) (h : m ≤ D.cut.half.card) (u : D.cut.Half),
    u ∈ D.halfList m h ↔ (D.order.symm u).val < m
  | 0, _, u => by simp [halfList]
  | m + 1, h, u => by
      simp only [halfList, List.mem_cons]
      rw [mem_halfList m (Nat.le_of_succ_le h) u]
      constructor
      · rintro (rfl | hu)
        · simp
        · omega
      · intro hu
        rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu' | hu'
        · exact Or.inr hu'
        · left
          have : D.order.symm u = ⟨m, h⟩ := Fin.ext hu'
          rw [← this, Equiv.apply_symm_apply]

theorem nodup_halfList : ∀ (m : ℕ) (h : m ≤ D.cut.half.card), (D.halfList m h).Nodup
  | 0, _ => by simp [halfList]
  | m + 1, h => by
      simp only [halfList, List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_halfList m (Nat.le_of_succ_le h)⟩
      have := (D.mem_halfList m (Nat.le_of_succ_le h) _).1 hmem
      simp at this

/-! ### `t_i = t⁰_i + c_i` and `∑ c_i = m_×` -/

/-- `c_i`: the number of neighbours of `v_i` in `U⁻`. -/
def outdeg (i : Fin D.cut.half.card) : ℕ :=
  (Finset.univ.filter (fun w => D.Adj (D.vtx i) w ∧ w ∉ D.cut.half)).card

theorem tdeg_eq (i : Fin D.cut.half.card) : D.tdeg i = D.outdeg i + D.t0deg i := by
  classical
  unfold tdeg outdeg t0deg
  rw [← Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun w : U => D.Adj (D.order i).1 w ∧
      ∀ j : Fin D.cut.half.card, j < i → w ≠ (D.order j).1)) (fun w => w ∉ D.cut.half),
    Finset.filter_filter, Finset.filter_filter]
  congr 1
  · refine Finset.card_nbij' (fun w => w) (fun w => w) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw ⊢
      exact ⟨hw.1.1, hw.2⟩
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and] at hw ⊢
      refine ⟨⟨hw.1, fun j _ hj => hw.2 (hj ▸ D.vtx_mem j)⟩, hw.2⟩
    · intro w _; rfl
    · intro w _; rfl
  · refine Finset.card_nbij' (fun w => if h : w ∈ D.cut.half then D.order.symm ⟨w, h⟩ else i)
      (fun j => D.vtx j) ?_ ?_ ?_ ?_
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, not_not] at hw ⊢
      obtain ⟨⟨hadj, hnot⟩, hwh⟩ := hw
      rw [dite_eq_left hwh]
      set k := D.order.symm ⟨w, hwh⟩ with hk
      have hvk : D.vtx k = w := by simp [vtx, hk]
      refine ⟨?_, by rw [hvk]; exact hadj⟩
      have hki : k ≠ i := by
        rintro rfl
        rw [show (D.order k).1 = w from hvk] at hadj
        exact D.not_adj_self _ hadj
      have hnk : ¬ k < i := fun hlt => hnot k hlt (by rw [← hvk]; rfl)
      rw [Fin.lt_def] at hnk ⊢
      have : k.val ≠ i.val := fun h' => hki (Fin.ext h')
      omega
    · intro j hj
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, not_not] at hj ⊢
      obtain ⟨hlt, hadj⟩ := hj
      refine ⟨⟨hadj, fun j' hj' hjj => ?_⟩, D.vtx_mem j⟩
      have := D.vtx_inj hjj
      rw [this] at hlt
      exact absurd (hlt.trans hj') (lt_irrefl _)
    · intro w hw
      simp only [Finset.coe_filter, Finset.mem_univ, true_and, not_not] at hw
      show D.vtx (if h : w ∈ D.cut.half then D.order.symm ⟨w, h⟩ else i) = w
      rw [dite_eq_left hw.2]
      simp [vtx]
    · intro j _
      show (if h : D.vtx j ∈ D.cut.half then D.order.symm ⟨D.vtx j, h⟩ else i) = j
      rw [dite_eq_left (D.vtx_mem j)]
      simp [vtx]

theorem outdeg_eq_rdeg (i : Fin D.cut.half.card) : D.outdeg i = D.rdeg (D.order i) := by
  unfold outdeg
  rw [← D.card_sgn_ne_zero (D.order i)]
  refine Finset.card_bij'
    (fun w hw => ⟨D.cut.flip w, (D.cut.crosses w).2 (Finset.mem_filter.mp hw).2.2⟩)
    (fun k' _ => D.cut.flip k'.1) ?_ ?_ ?_ ?_
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw ⊢
    rw [D.sgn_ne_zero_iff, D.cut.flip_flip]
    exact hw.1
  · intro k' hk'
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk' ⊢
    exact ⟨(D.sgn_ne_zero_iff _ k').1 hk', D.cut.flip_not_mem k'.2⟩
  · intro w _
    exact D.cut.flip_flip w
  · intro k' _
    exact Subtype.ext (D.cut.flip_flip k'.1)

theorem sum_outdeg : ∑ i, D.outdeg i = D.mcross := by
  classical
  simp only [D.outdeg_eq_rdeg]
  rw [Fintype.sum_equiv D.order (fun i => D.rdeg (D.order i)) D.rdeg (fun _ => rfl)]
  unfold mcross crossPairs
  rw [Finset.card_filter, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [← D.card_sgn_ne_zero j, Finset.card_filter]

theorem t0deg_le (i : Fin D.cut.half.card) : D.t0deg i ≤ D.tdeg i := by
  rw [D.tdeg_eq]
  omega

/-! ### The bound on `Z` -/

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `|I⁺|` lies between the graded products of `G⁺` along `v_n, …, v_1`. -/
theorem card_half_graded (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn) :
    ∏ j, stepLower (Fintype.card F) nn (D.t0deg j) ≤ ((injLabellings F D.halfGraph).card : ℝ) ∧
      ((injLabellings F D.halfGraph).card : ℝ) ≤ ∏ j, stepUpper (Fintype.card F) (D.t0deg j) := by
  have hn' : Fintype.card D.cut.Half ≤ nn :=
    le_trans (Fintype.card_subtype_le _) hn
  have hcov : ∀ u, u ∈ D.halfList D.cut.half.card le_rfl := fun u =>
    (D.mem_halfList _ le_rfl u).2 (D.order.symm u).isLt
  have hb := D.card_half_bounds hW hn' (D.halfList D.cut.half.card le_rfl)
    (D.nodup_halfList _ le_rfl) hcov
  have hU := D.upperProd_halfList (Fintype.card F) D.cut.half.card le_rfl
  have hL := D.lowerProd_halfList (Fintype.card F) nn D.cut.half.card le_rfl
  rw [D.halfSet_card] at hU hL
  have hall : Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < D.cut.half.card) =
      Finset.univ := Finset.filter_true_of_mem (fun j _ => j.isLt)
  rw [hall] at hU hL
  rw [← hU, ← hL]
  exact hb

/-- **`lem:spec:cutkernel` (c), the mass.** If `e_{t_i}(q, n') < 1` for every `i`, then
`2^{-m_×} R_cut^{-1} ≤ Z ≤ 2^{-m_×} R_cut`. -/
theorem cutZ_Rcut (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    (hne : (injLabellings F D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn < 1) :
    (1 / 2) ^ D.mcross * (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card F) t nn))⁻¹ ≤
        D.cutZ hne ∧
      D.cutZ hne ≤
        (1 / 2) ^ D.mcross * D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card F) t nn) := by
  have hq1 : (1 : ℝ) ≤ ((Fintype.card F : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  set q : ℝ := ((Fintype.card F : ℕ) : ℝ) with hq_def
  set e := fun t => TraceMixing.coarseErr q t nn
  have hq0 : (0 : ℝ) < q := by linarith
  have he0 : ∀ t, 0 ≤ e t := fun t => TraceMixing.coarseErr_nonneg hq0 t nn
  have he0' : ∀ i, e (D.t0deg i) ≤ e (D.tdeg i) := fun i =>
    TraceMixing.coarseErr_mono hq0 (D.t0deg_le i) le_rfl
  have hc : ∀ t : ℕ, 0 < q / 2 ^ t := fun t => by positivity
  -- the four products
  set A := ∏ i, q / 2 ^ D.tdeg i * (1 - e (D.tdeg i))
  set B := ∏ i, q / 2 ^ D.tdeg i * (1 + e (D.tdeg i))
  set A0 := ∏ i, q / 2 ^ D.t0deg i * (1 - e (D.t0deg i))
  set B0 := ∏ i, q / 2 ^ D.t0deg i * (1 + e (D.t0deg i))
  have hA : 0 < A := Finset.prod_pos (fun i _ => mul_pos (hc _) (by linarith [he1 i]))
  have hB : 0 < B := Finset.prod_pos (fun i _ => mul_pos (hc _) (by linarith [he0 (D.tdeg i)]))
  have hA0 : 0 < A0 := Finset.prod_pos (fun i _ => mul_pos (hc _)
    (by linarith [he1 i, he0' i]))
  have hB0 : 0 < B0 := Finset.prod_pos (fun i _ => mul_pos (hc _) (by linarith [he0 (D.t0deg i)]))
  -- the graded bounds
  have hLo : A ≤ ∏ j, stepLower (Fintype.card F) nn (D.tdeg j) :=
    Finset.prod_le_prod₀ (fun i _ => (mul_pos (hc _) (by linarith [he1 i])).le)
      (fun i _ => coarse_le_stepLower hq1 nn _)
  have hUp : ∏ j, stepUpper (Fintype.card F) (D.tdeg j) ≤ B :=
    Finset.prod_le_prod₀ (fun i _ => div_nonneg (add_nonneg (by positivity)
      (softError_nonneg _ _)) (by positivity)) (fun i _ => stepUpper_le_coarse hq1 nn _)
  have hLo0 : A0 ≤ ∏ j, stepLower (Fintype.card F) nn (D.t0deg j) :=
    Finset.prod_le_prod₀ (fun i _ => (mul_pos (hc _) (by linarith [he1 i, he0' i])).le)
      (fun i _ => coarse_le_stepLower hq1 nn _)
  have hUp0 : ∏ j, stepUpper (Fintype.card F) (D.t0deg j) ≤ B0 :=
    Finset.prod_le_prod₀ (fun i _ => div_nonneg (add_nonneg (by positivity)
      (softError_nonneg _ _)) (by positivity)) (fun i _ => stepUpper_le_coarse hq1 nn _)
  obtain ⟨hI1, hI2⟩ := D.card_half_graded hW hn
  obtain ⟨hZ1, hZ2⟩ := D.cutZ_bounds hW hn hne
  set c := ((injLabellings F D.halfGraph).card : ℝ)
  have hcpos : 0 < c := lt_of_lt_of_le hA0 (hLo0.trans hI1)
  -- the powers of two
  have hpow : ∏ i, (q / 2 ^ D.tdeg i) / (q / 2 ^ D.t0deg i) = (1 / 2) ^ D.mcross := by
    rw [← D.sum_outdeg, ← Finset.prod_pow_eq_pow_sum]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [D.tdeg_eq i, pow_add]
    have h2 : (0 : ℝ) < 2 ^ D.t0deg i := by positivity
    have h3 : (0 : ℝ) < 2 ^ D.outdeg i := by positivity
    have h4 : (2 : ℝ) ^ D.outdeg i * (1 / 2) ^ D.outdeg i = 1 := by
      rw [← mul_pow]
      norm_num
    field_simp
    linarith
  have hR : D.Rcut e = ∏ i, (1 + e (D.tdeg i)) / (1 - e (D.tdeg i)) := rfl
  constructor
  · -- `Z ≥ N₋/|I⁺| ≥ A/B0 ≥ 2^{-m} R⁻¹`
    have h1 : A / B0 ≤ D.cutZ hne := by
      refine le_trans ?_ hZ1
      exact div_le_div₀ (hA.le.trans hLo) hLo hcpos (hI2.trans hUp0)
    refine le_trans ?_ h1
    have hfac : A / B0 = (∏ i, (q / 2 ^ D.tdeg i) / (q / 2 ^ D.t0deg i)) *
        ∏ i, (1 - e (D.tdeg i)) / (1 + e (D.t0deg i)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have h1' := hc (D.tdeg i)
      have h2' := hc (D.t0deg i)
      have h3' : 0 < 1 + e (D.t0deg i) := by linarith [he0 (D.t0deg i)]
      field_simp
    rw [hfac, hpow, hR, ← Finset.prod_inv_distrib]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · have : 0 < 1 - e (D.tdeg i) := by linarith [he1 i]
      have : 0 < 1 + e (D.tdeg i) := by linarith [he0 (D.tdeg i)]
      positivity
    · have h4 : 0 < 1 - e (D.tdeg i) := by linarith [he1 i]
      have h5 : 0 < 1 + e (D.t0deg i) := by linarith [he0 (D.t0deg i)]
      rw [inv_div]
      exact div_le_div_of_nonneg_left h4.le h5 (by linarith [he0' i])
  · -- `Z ≤ N₊/|I⁺| ≤ B/A0 ≤ 2^{-m} R`
    have h1 : D.cutZ hne ≤ B / A0 := by
      refine hZ2.trans ?_
      exact div_le_div₀ hB.le hUp hA0 (hLo0.trans hI1)
    refine h1.trans ?_
    have hfac : B / A0 = (∏ i, (q / 2 ^ D.tdeg i) / (q / 2 ^ D.t0deg i)) *
        ∏ i, (1 + e (D.tdeg i)) / (1 - e (D.t0deg i)) := by
      rw [← Finset.prod_mul_distrib, ← Finset.prod_div_distrib]
      refine Finset.prod_congr rfl (fun i _ => ?_)
      have h1' := hc (D.tdeg i)
      have h2' := hc (D.t0deg i)
      have h3' : 0 < 1 - e (D.t0deg i) := by linarith [he1 i, he0' i]
      field_simp
    rw [hfac, hpow, hR]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine Finset.prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
    · have : 0 < 1 - e (D.t0deg i) := by linarith [he1 i, he0' i]
      have : 0 < 1 + e (D.tdeg i) := by linarith [he0 (D.tdeg i)]
      positivity
    · have h4 : 0 < 1 - e (D.tdeg i) := by linarith [he1 i]
      have h5 : 0 < 1 + e (D.tdeg i) := by linarith [he0 (D.tdeg i)]
      exact div_le_div_of_nonneg_left h5.le h4 (by linarith [he0' i])

end SpecData

end Sarkozy.Cuts

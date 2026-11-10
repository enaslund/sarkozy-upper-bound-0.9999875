module

public import Sarkozy.Cuts.CutKernel
public import Sarkozy.TraceMixing.PhiBound
public import Sarkozy.TraceMixing.PairExplicit

/-!
# Cuts, IX‴: counting the extensions of a half (`lem:spec:cutkernel` (c))

`13_cuts_correlations.tex`, `lem:spec:cutkernel` (c), in the graded form of the counting lemma
`Sarkozy.Labellings.extCount_bounds` (`lem:graphs:sequential`). Let `v_i = 𝔬(i)` and let `t_i`
be the deletion degrees (`SpecData.tdeg`). For `x ∈ I⁺` let
`N(x) = #{x' ∈ I⁺ : K(x, x') = 1}` (`Ncount`).

* `Ncount_eq_extCount`: `N(x)` is the number of labellings of `G` restricting to `x` on `U⁺`.
* `upperProd_delList`, `lowerProd_delList`: label `U⁻` in the order `ϑv_n, …, ϑv_1`. When `ϑv_i`
  is labelled, it has exactly `t_i` labelled neighbours (`nbrCount_delSet`).
* `Ncount_bounds`: `N₋ ≤ N(x) ≤ N₊` with `N₊ = ∏_i (q + 𝔈_{t_i})/2^{t_i}` and
  `N₋ = ∏_i max(0, (q - 𝔈_{t_i} - 2^{t_i} n)/2^{t_i})`. These are the step bounds of
  `lem:graphs:sequential`.
* `rho_eq`, `rho_bounds`: `ϱ(x) = N(x)|I⁺|/|Inj(G)|`, hence `N₋/N₊ ≤ ϱ ≤ N₊/N₋` on `I⁺`.

* `cutZ_bounds`, `card_half_bounds`: `N₋/|I⁺| ≤ Z ≤ N₊/|I⁺|`, and `|I⁺|` lies between the
  graded products of `G⁺`.

* `stepUpper_le_coarse`, `coarse_le_stepLower`, `Ncount_coarse`, `rho_Rcut`: the coarse errors
  `e_t(p, n') = 2^t (h_t r + n' r²)` (`Sarkozy.TraceMixing.coarseErr`) majorize the graded step
  errors. This gives the
  paper's `N_± = ∏_i p 2^{-t_i}(1 ± e_{t_i})`, `N₊/N₋ = R_cut`, and `R_cut^{-1} ≤ ϱ ≤ R_cut`
  on `I⁺`.
* `inj_nonempty`: since `e_t` is nondecreasing in `t` (`TraceMixing.coarseErr_mono`), if `e_t < 1`
  for `t ≤ Δ`, then
  `Inj(G) ≠ ∅` (part (a), first claim).

The bound `2^{-m_×} R_cut^{-1} ≤ Z ≤ 2^{-m_×} R_cut` is in `Sarkozy.Cuts.CutMass`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Labellings

namespace SpecData

variable {U : Type*} [Fintype U] [DecidableEq U] (D : SpecData U)

/-- `v_i = 𝔬(i)`. -/
def vtx (i : Fin D.cut.half.card) : U := (D.order i).1

theorem vtx_mem (i : Fin D.cut.half.card) : D.vtx i ∈ D.cut.half := (D.order i).2

theorem vtx_inj {i j : Fin D.cut.half.card} (h : D.vtx i = D.vtx j) : i = j :=
  D.order.injective (Subtype.ext h)

theorem exists_vtx {w : U} (hw : w ∈ D.cut.half) : ∃ i, D.vtx i = w :=
  ⟨D.order.symm ⟨w, hw⟩, by simp only [vtx, Equiv.apply_symm_apply]⟩

theorem not_adj_self (u : U) : ¬ D.Adj u u := by
  rintro (h | h) <;> exact D.G.loopless u h

/-- The list `ϑv_{m-1}, …, ϑv_0`. -/
def delList : (m : ℕ) → m ≤ D.cut.half.card → List U
  | 0, _ => []
  | m + 1, h => D.cut.flip (D.vtx ⟨m, h⟩) :: delList m (Nat.le_of_succ_le h)

/-- `A_m = U⁺ ∪ {ϑv_j : j ≥ m}`. -/
def delSet (m : ℕ) : Finset U :=
  D.cut.half ∪ (Finset.univ.filter (fun j : Fin D.cut.half.card => m ≤ j.val)).image
    (fun j => D.cut.flip (D.vtx j))

theorem mem_delSet (m : ℕ) (u : U) :
    u ∈ D.delSet m ↔ u ∈ D.cut.half ∨ ∃ j : Fin D.cut.half.card, m ≤ j.val ∧
      D.cut.flip (D.vtx j) = u := by
  simp only [delSet, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ,
    true_and]

theorem delSet_succ (m : ℕ) (h : m < D.cut.half.card) :
    insert (D.cut.flip (D.vtx ⟨m, h⟩)) (D.delSet (m + 1)) = D.delSet m := by
  ext u
  rw [Finset.mem_insert, D.mem_delSet, D.mem_delSet]
  constructor
  · rintro (rfl | hu | ⟨j, hj, rfl⟩)
    · exact Or.inr ⟨⟨m, h⟩, le_rfl, rfl⟩
    · exact Or.inl hu
    · exact Or.inr ⟨j, by omega, rfl⟩
  · rintro (hu | ⟨j, hj, rfl⟩)
    · exact Or.inr (Or.inl hu)
    · rcases Nat.eq_or_lt_of_le hj with hjm | hjm
      · left
        have : j = ⟨m, h⟩ := Fin.ext hjm.symm
        rw [this]
      · exact Or.inr (Or.inr ⟨j, hjm, rfl⟩)

theorem delSet_card : D.delSet D.cut.half.card = D.cut.half := by
  ext u
  rw [D.mem_delSet]
  constructor
  · rintro (hu | ⟨j, hj, _⟩)
    · exact hu
    · exact absurd j.isLt (by omega)
  · exact Or.inl

/-- When `ϑv_m` is labelled after `A_{m+1}`, it has `t_m` labelled neighbours. -/
theorem nbrCount_delSet (m : ℕ) (h : m < D.cut.half.card) :
    nbrCount D.G (D.delSet (m + 1)) (D.cut.flip (D.vtx ⟨m, h⟩)) = D.tdeg ⟨m, h⟩ := by
  classical
  unfold nbrCount tdeg
  refine Finset.card_nbij' (fun u => D.cut.flip u) (fun w => D.cut.flip w) ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_coe, Finset.mem_filter] at hu ⊢
    obtain ⟨huA, hadj⟩ := hu
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · have h1 : D.Adj u (D.cut.flip (D.vtx ⟨m, h⟩)) := hadj
      have h2 := (D.adj_flip u (D.cut.flip (D.vtx ⟨m, h⟩))).2 h1
      rw [D.cut.flip_flip] at h2
      exact (D.adj_symm).1 h2
    · intro j hj hjw
      rcases (D.mem_delSet (m + 1) u).1 huA with hu' | ⟨k, hk, rfl⟩
      · exact D.cut.flip_not_mem hu' (hjw ▸ D.vtx_mem j)
      · rw [D.cut.flip_flip] at hjw
        have hkj := D.vtx_inj hjw
        have hj' : j.val < m := hj
        rw [hkj] at hk
        omega
  · intro w hw
    simp only [Finset.mem_coe, Finset.mem_filter] at hw ⊢
    obtain ⟨_, hadj, hnot⟩ := hw
    refine ⟨?_, ?_⟩
    · rw [D.mem_delSet]
      by_cases hwh : w ∈ D.cut.half
      · obtain ⟨k, rfl⟩ := D.exists_vtx hwh
        right
        refine ⟨k, ?_, rfl⟩
        have hkm : k ≠ ⟨m, h⟩ := by
          rintro rfl
          exact D.not_adj_self _ hadj
        have hk : ¬ k.val < m := fun hk => hnot k hk rfl
        have : k.val ≠ m := fun h' => hkm (Fin.ext h')
        omega
      · exact Or.inl ((D.cut.crosses w).2 hwh)
    · have h1 : D.Adj w (D.vtx ⟨m, h⟩) := (D.adj_symm).1 hadj
      have h2 := (D.adj_flip w (D.vtx ⟨m, h⟩)).2 h1
      exact h2
  · intro u _
    exact D.cut.flip_flip u
  · intro w _
    exact D.cut.flip_flip w

theorem upperProd_delList (q : ℝ) : ∀ (m : ℕ) (h : m ≤ D.cut.half.card),
    upperProd D.G q (D.delSet m) (D.delList m h) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m), stepUpper q (D.tdeg j)
  | 0, _ => by
      simp only [delList, upperProd]
      rw [Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.prod_empty]
  | m + 1, h => by
      simp only [delList, upperProd]
      rw [D.nbrCount_delSet m h, D.delSet_succ m h, upperProd_delList q m (Nat.le_of_succ_le h)]
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

theorem lowerProd_delList (q : ℝ) (nn : ℕ) : ∀ (m : ℕ) (h : m ≤ D.cut.half.card),
    lowerProd D.G q nn (D.delSet m) (D.delList m h) =
      ∏ j ∈ Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < m),
        stepLower q nn (D.tdeg j)
  | 0, _ => by
      simp only [delList, lowerProd]
      rw [Finset.filter_false_of_mem (fun j _ => Nat.not_lt_zero _), Finset.prod_empty]
  | m + 1, h => by
      simp only [delList, lowerProd]
      rw [D.nbrCount_delSet m h, D.delSet_succ m h,
        lowerProd_delList q nn m (Nat.le_of_succ_le h)]
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

theorem mem_delList : ∀ (m : ℕ) (h : m ≤ D.cut.half.card) (w : U),
    w ∈ D.delList m h ↔ ∃ j : Fin D.cut.half.card, j.val < m ∧ D.cut.flip (D.vtx j) = w
  | 0, _, w => by
      simp only [delList, List.not_mem_nil, false_iff, not_exists, not_and]
      intro j hj
      exact absurd hj (Nat.not_lt_zero _)
  | m + 1, h, w => by
      simp only [delList, List.mem_cons]
      rw [mem_delList m (Nat.le_of_succ_le h) w]
      constructor
      · rintro (rfl | ⟨j, hj, rfl⟩)
        · exact ⟨⟨m, h⟩, Nat.lt_succ_self m, rfl⟩
        · exact ⟨j, Nat.lt_succ_of_lt hj, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | hj'
        · exact Or.inr ⟨j, hj', rfl⟩
        · left
          have : j = ⟨m, h⟩ := Fin.ext hj'
          rw [this]

theorem nodup_delList : ∀ (m : ℕ) (h : m ≤ D.cut.half.card), (D.delList m h).Nodup
  | 0, _ => by simp [delList]
  | m + 1, h => by
      simp only [delList, List.nodup_cons]
      refine ⟨fun hmem => ?_, nodup_delList m (Nat.le_of_succ_le h)⟩
      obtain ⟨j, hj, hjw⟩ := (D.mem_delList m (Nat.le_of_succ_le h) _).1 hmem
      have := D.vtx_inj (D.cut.flip.injective hjw)
      rw [this] at hj
      exact absurd hj (Nat.lt_irrefl m)

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `N(x) = #{x' ∈ I⁺ : K(x, x') = 1}`. -/
noncomputable def Ncount (x : D.cut.Half → F) : ℕ := by
  classical exact ((injLabellings F D.halfGraph).filter (fun x' => D.CutOK x x')).card

theorem feasible_glue {x : D.cut.Half → F} (hx : x ∈ injLabellings F D.halfGraph) :
    Feasible F D.G D.cut.half (D.glue x x) := by
  rw [mem_inj_half] at hx
  obtain ⟨hinj, hedge⟩ := hx
  have hg : ∀ a (ha : a ∈ D.cut.half), D.glue x x a = x ⟨a, ha⟩ := fun a ha => by
    simp only [glue, dite_eq_left ha]
  refine ⟨fun a ha b hb hab => ?_, fun e he h1 h2 => ?_⟩
  · rw [hg a ha, hg b hb] at hab
    exact congrArg Subtype.val (hinj _ (Finset.mem_univ _) _ (Finset.mem_univ _) hab)
  · rw [hg _ h1, hg _ h2]
    exact hedge (⟨e.1, h1⟩, ⟨e.2, h2⟩) ((D.mem_halfGraph _).2 he) (Finset.mem_univ _)
      (Finset.mem_univ _)

/-- `N(x)` is the number of labellings of `G` restricting to `x` on `U⁺`. -/
theorem Ncount_eq_extCount {x : D.cut.Half → F} (hx : x ∈ injLabellings F D.halfGraph) :
    D.Ncount x = extCount D.G D.cut.half (D.glue x x) := by
  classical
  unfold Ncount extCount
  have hg : ∀ x' : D.cut.Half → F, ∀ a (ha : a ∈ D.cut.half), D.glue x x' a = x ⟨a, ha⟩ :=
    fun x' a ha => by simp only [glue, dite_eq_left ha]
  refine Finset.card_nbij' (fun x' => D.glue x x') (fun y => D.halfR y) ?_ ?_ ?_ ?_
  · intro x' hx'
    simp only [Finset.mem_coe, Finset.mem_filter] at hx' ⊢
    refine ⟨(D.glue_mem_iff x x').2 ⟨hx, hx'.1, hx'.2⟩, fun a ha => ?_⟩
    rw [hg x' a ha, hg x a ha]
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyI, hagree⟩ := hy
    obtain ⟨_, h2, h3⟩ := (D.mem_inj_iff y).1 hyI
    have hL : D.halfL y = x := by
      funext k
      simp only [halfL]
      rw [hagree k.1 k.2, hg x k.1 k.2]
    rw [hL] at h3
    exact ⟨h2, h3⟩
  · intro x' _
    exact (D.halves_glue x x').2
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨_, hagree⟩ := hy
    have hL : D.halfL y = x := by
      funext k
      simp only [halfL]
      rw [hagree k.1 k.2, hg x k.1 k.2]
    simp only
    rw [← hL, D.glue_halves]

/-- **`lem:spec:cutkernel` (c), graded form.** For `x ∈ I⁺`, `N₋ ≤ N(x) ≤ N₊`, where
`N₊ = ∏_i (q + 𝔈_{t_i})/2^{t_i}` and `N₋ = ∏_i max(0, (q - 𝔈_{t_i} - 2^{t_i} n')/2^{t_i})`,
`q = |F|`, `n' ≥ |U|`. -/
theorem Ncount_bounds (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    {x : D.cut.Half → F} (hx : x ∈ injLabellings F D.halfGraph) :
    ∏ j, stepLower (Fintype.card F) nn (D.tdeg j) ≤ (D.Ncount x : ℝ) ∧
      (D.Ncount x : ℝ) ≤ ∏ j, stepUpper (Fintype.card F) (D.tdeg j) := by
  have hcov : ∀ w, w ∈ D.cut.half ∨ w ∈ D.delList D.cut.half.card le_rfl := by
    intro w
    by_cases hw : w ∈ D.cut.half
    · exact Or.inl hw
    · right
      rw [D.mem_delList]
      obtain ⟨j, hj⟩ := D.exists_vtx ((D.cut.crosses w).2 hw)
      exact ⟨j, j.isLt, by rw [hj, D.cut.flip_flip]⟩
  have hdisj : ∀ w ∈ D.delList D.cut.half.card le_rfl, w ∉ D.cut.half := by
    intro w hw
    obtain ⟨j, _, rfl⟩ := (D.mem_delList _ le_rfl w).1 hw
    exact D.cut.flip_not_mem (D.vtx_mem j)
  have hb := extCount_bounds hW D.G hn (D.delList D.cut.half.card le_rfl) D.cut.half
    (D.glue x x) (D.nodup_delList _ le_rfl) hcov hdisj (D.feasible_glue hx)
  have hU := D.upperProd_delList (Fintype.card F) D.cut.half.card le_rfl
  have hL := D.lowerProd_delList (Fintype.card F) nn D.cut.half.card le_rfl
  rw [D.delSet_card] at hU hL
  have hall : Finset.univ.filter (fun j : Fin D.cut.half.card => j.val < D.cut.half.card) =
      Finset.univ := Finset.filter_true_of_mem (fun j _ => j.isLt)
  rw [hall] at hU hL
  rw [D.Ncount_eq_extCount hx, ← hU, ← hL]
  exact hb

/-- `∑_{x' ∈ I⁺} K(x, x') = N(x)`. -/
theorem sum_cutK (x : D.cut.Half → F) :
    ∑ x' ∈ injLabellings F D.halfGraph, D.cutK x x' = D.Ncount x := by
  classical
  unfold cutK Ncount
  rw [Finset.sum_boole]

/-- `|Inj(G)| = ∑_{x ∈ I⁺} N(x)`. -/
theorem card_inj_eq_sum :
    ((injLabellings F D.G).card : ℝ) = ∑ x ∈ injLabellings F D.halfGraph, (D.Ncount x : ℝ) := by
  have h := D.sum_inj_halves (F := F) (fun _ _ => 1)
  simp only [mul_one, Finset.sum_const, nsmul_eq_mul] at h
  rw [h]
  exact Finset.sum_congr rfl (fun x _ => D.sum_cutK x)

/-- **`lem:spec:cutkernel` (c).** `ϱ(x) = (A1)(x) = N(x)|I⁺|/|Inj(G)|` on `I⁺`. -/
theorem rho_eq (hne : (injLabellings F D.G).Nonempty) (x : D.cut.Half → F) :
    rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x =
      D.Ncount x * (injLabellings F D.halfGraph).card / (injLabellings F D.G).card := by
  unfold rowFun halfLaw
  rw [graphLaw_expect', ← Finset.sum_div, D.sum_cutK, D.cutZ_eq]
  have h1 : (0 : ℝ) < (injLabellings F D.G).card := by exact_mod_cast Finset.card_pos.mpr hne
  have h2 : (0 : ℝ) < (injLabellings F D.halfGraph).card := by
    exact_mod_cast Finset.card_pos.mpr (D.half_nonempty hne)
  field_simp

/-- **`lem:spec:cutkernel` (c), the density range.** If `N₋ > 0`, then
`N₋/N₊ ≤ ϱ ≤ N₊/N₋` on `I⁺`. -/
theorem rho_bounds (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    (hne : (injLabellings F D.G).Nonempty)
    (hlow : 0 < ∏ j, stepLower (Fintype.card F) nn (D.tdeg j))
    {x : D.cut.Half → F} (hx : x ∈ injLabellings F D.halfGraph) :
    (∏ j, stepLower (Fintype.card F) nn (D.tdeg j)) / ∏ j, stepUpper (Fintype.card F) (D.tdeg j) ≤
        rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x ∧
      rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x ≤
        (∏ j, stepUpper (Fintype.card F) (D.tdeg j)) /
          ∏ j, stepLower (Fintype.card F) nn (D.tdeg j) := by
  have hc : (0 : ℝ) < ((injLabellings F D.halfGraph).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (D.half_nonempty hne)
  set Lo := ∏ j, stepLower (Fintype.card F) nn (D.tdeg j)
  set Up := ∏ j, stepUpper (Fintype.card F) (D.tdeg j)
  set c := ((injLabellings F D.halfGraph).card : ℝ)
  have hbx := D.Ncount_bounds hW hn hx
  have hUp : 0 < Up := lt_of_lt_of_le hlow (hbx.1.trans hbx.2)
  have hsum := D.card_inj_eq_sum (F := F)
  have hI : c * Lo ≤ (injLabellings F D.G).card ∧ ((injLabellings F D.G).card : ℝ) ≤ c * Up := by
    rw [hsum]
    constructor
    · calc c * Lo = ∑ _x ∈ injLabellings F D.halfGraph, Lo := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ _ := Finset.sum_le_sum (fun x hx => (D.Ncount_bounds hW hn hx).1)
    · calc ∑ x ∈ injLabellings F D.halfGraph, (D.Ncount x : ℝ)
          ≤ ∑ _x ∈ injLabellings F D.halfGraph, Up :=
            Finset.sum_le_sum (fun x hx => (D.Ncount_bounds hW hn hx).2)
        _ = c * Up := by rw [Finset.sum_const, nsmul_eq_mul]
  have hInj : (0 : ℝ) < (injLabellings F D.G).card := by exact_mod_cast Finset.card_pos.mpr hne
  rw [D.rho_eq hne x]
  constructor
  · rw [div_le_div_iff₀ hUp hInj]
    calc Lo * (injLabellings F D.G).card ≤ Lo * (c * Up) :=
          mul_le_mul_of_nonneg_left hI.2 hlow.le
      _ = Lo * c * Up := by ring
      _ ≤ D.Ncount x * c * Up := by
          apply mul_le_mul_of_nonneg_right _ hUp.le
          exact mul_le_mul_of_nonneg_right hbx.1 hc.le
  · rw [div_le_div_iff₀ hInj hlow]
    calc (D.Ncount x : ℝ) * c * Lo ≤ Up * c * Lo := by
          apply mul_le_mul_of_nonneg_right _ hlow.le
          exact mul_le_mul_of_nonneg_right hbx.2 hc.le
      _ = Up * (c * Lo) := by ring
      _ ≤ Up * (injLabellings F D.G).card := mul_le_mul_of_nonneg_left hI.1 hUp.le

/-- **`lem:spec:cutkernel` (c), the mass.** `N₋/|I⁺| ≤ Z ≤ N₊/|I⁺|`. -/
theorem cutZ_bounds (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    (hne : (injLabellings F D.G).Nonempty) :
    (∏ j, stepLower (Fintype.card F) nn (D.tdeg j)) / (injLabellings F D.halfGraph).card ≤
        D.cutZ hne ∧
      D.cutZ hne ≤ (∏ j, stepUpper (Fintype.card F) (D.tdeg j)) /
        (injLabellings F D.halfGraph).card := by
  have hc : (0 : ℝ) < ((injLabellings F D.halfGraph).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr (D.half_nonempty hne)
  set Lo := ∏ j, stepLower (Fintype.card F) nn (D.tdeg j)
  set Up := ∏ j, stepUpper (Fintype.card F) (D.tdeg j)
  set c := ((injLabellings F D.halfGraph).card : ℝ)
  have hsum := D.card_inj_eq_sum (F := F)
  have hlo : c * Lo ≤ (injLabellings F D.G).card := by
    rw [hsum]
    calc c * Lo = ∑ _x ∈ injLabellings F D.halfGraph, Lo := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ _ := Finset.sum_le_sum (fun x hx => (D.Ncount_bounds hW hn hx).1)
  have hup : ((injLabellings F D.G).card : ℝ) ≤ c * Up := by
    rw [hsum]
    calc ∑ x ∈ injLabellings F D.halfGraph, (D.Ncount x : ℝ)
        ≤ ∑ _x ∈ injLabellings F D.halfGraph, Up :=
          Finset.sum_le_sum (fun x hx => (D.Ncount_bounds hW hn hx).2)
      _ = c * Up := by rw [Finset.sum_const, nsmul_eq_mul]
  rw [D.cutZ_eq hne]
  constructor
  · rw [div_le_div_iff₀ hc (by positivity)]
    nlinarith
  · rw [div_le_div_iff₀ (by positivity) hc]
    nlinarith

/-- `|I⁺|` lies between the lower and upper products of `G⁺` along any ordering of `U⁺`
(`lem:graphs:sequential`). -/
theorem card_half_bounds (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card D.cut.Half ≤ nn)
    (l : List D.cut.Half) (hnd : l.Nodup) (hcov : ∀ w, w ∈ l) :
    lowerProd D.halfGraph (Fintype.card F) nn ∅ l ≤ (injLabellings F D.halfGraph).card ∧
      ((injLabellings F D.halfGraph).card : ℝ) ≤ upperProd D.halfGraph (Fintype.card F) ∅ l := by
  classical
  refine ⟨lowerProd_le_card_inj hW D.halfGraph hn l hnd hcov, ?_⟩
  have hfeas : Feasible F D.halfGraph ∅ (fun _ => (0 : F)) := ⟨by simp, by simp⟩
  have h := (extCount_bounds hW D.halfGraph hn l ∅ (fun _ => (0 : F)) hnd
    (fun w => Or.inr (hcov w)) (by simp) hfeas).2
  have he : extCount D.halfGraph ∅ (fun _ => (0 : F)) = (injLabellings F D.halfGraph).card := by
    unfold extCount
    congr 1
    exact Finset.filter_true_of_mem fun _ _ => by simp
  rwa [he] at h

/-! ### The coarse form: `R_cut^{-1} ≤ ϱ ≤ R_cut` -/

/-- The graded step error is at most the coarse one: `𝔈_t/2^t ≤ h_t √q` for `q ≥ 1`. -/
theorem softError_le {q : ℝ} (hq : 1 ≤ q) (t : ℕ) :
    softError q t / 2 ^ t ≤ ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * Real.sqrt q := by
  have hs1 : 1 ≤ Real.sqrt q := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hq
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have hB := gradedB_nonneg t
  have hsum := TraceMixing.gradedA_add_gradedB t
  rw [div_le_iff₀ h2]
  unfold softError
  have : gradedB t ≤ gradedB t * Real.sqrt q := le_mul_of_one_le_right hB hs1
  nlinarith

/-- `stepUpper q t ≤ q 2^{-t} (1 + e_t(q, n))` for `q ≥ 1`. -/
theorem stepUpper_le_coarse {q : ℝ} (hq : 1 ≤ q) (n t : ℕ) :
    stepUpper q t ≤ q / 2 ^ t * (1 + TraceMixing.coarseErr q t n) := by
  have hq0 : 0 < q := by linarith
  have h := softError_le hq t
  have h2ne : (2 : ℝ) ^ t ≠ 0 := by positivity
  have hdiv : q / Real.sqrt q = Real.sqrt q := Real.div_sqrt
  have hn : q * ((n : ℝ) / q) = n := by field_simp
  have e : q / 2 ^ t * (1 + TraceMixing.coarseErr q t n) =
      q / 2 ^ t + ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * Real.sqrt q + n := by
    unfold TraceMixing.coarseErr
    have e1 : q / 2 ^ t * (1 + 2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ +
        n / q)) = q / 2 ^ t + (q / 2 ^ t * 2 ^ t) * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) *
          (Real.sqrt q)⁻¹) + (q / 2 ^ t * 2 ^ t) * (n / q) := by ring
    rw [e1, div_mul_cancel₀ q h2ne, hn,
      show q * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹) =
        ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (q / Real.sqrt q) by ring, hdiv]
  rw [e]
  unfold stepUpper
  rw [add_div]
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

/-- `q 2^{-t} (1 - e_t(q, n)) ≤ stepLower q n t` for `q ≥ 1`. -/
theorem coarse_le_stepLower {q : ℝ} (hq : 1 ≤ q) (n t : ℕ) :
    q / 2 ^ t * (1 - TraceMixing.coarseErr q t n) ≤ stepLower q n t := by
  have hq0 : 0 < q := by linarith
  have h := softError_le hq t
  have h2ne : (2 : ℝ) ^ t ≠ 0 := by positivity
  have hdiv : q / Real.sqrt q = Real.sqrt q := Real.div_sqrt
  have hn : q * ((n : ℝ) / q) = n := by field_simp
  have e : q / 2 ^ t * (1 - TraceMixing.coarseErr q t n) =
      q / 2 ^ t - ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * Real.sqrt q - n := by
    unfold TraceMixing.coarseErr
    have e1 : q / 2 ^ t * (1 - 2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹ +
        n / q)) = q / 2 ^ t - (q / 2 ^ t * 2 ^ t) * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) *
          (Real.sqrt q)⁻¹) - (q / 2 ^ t * 2 ^ t) * (n / q) := by ring
    rw [e1, div_mul_cancel₀ q h2ne, hn,
      show q * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt q)⁻¹) =
        ((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (q / Real.sqrt q) by ring, hdiv]
  rw [e]
  unfold stepLower
  refine le_trans ?_ (le_max_right _ _)
  have e2 : (q - softError q t - 2 ^ t * n) / 2 ^ t = q / 2 ^ t - softError q t / 2 ^ t - n := by
    field_simp
  rw [e2]
  linarith

/-- **`lem:spec:cutkernel` (c).** If `e_{t_i}(q, n') < 1` for every `i` (for instance
`e_Δ(p, 2n) < 1`, since `e_t` is nondecreasing in `t`), then `R_cut^{-1} ≤ ϱ ≤ R_cut` on `I⁺`,
with `R_cut = ∏_i (1 + e_{t_i})/(1 - e_{t_i})` (`eq:spec:Rcut`). -/
theorem rho_Rcut (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    (hne : (injLabellings F D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn < 1)
    {x : D.cut.Half → F} (hx : x ∈ injLabellings F D.halfGraph) :
    (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card F) t nn))⁻¹ ≤
        rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x ∧
      rowFun (D.halfLaw hne) (fun x x' => D.cutK x x' / D.cutZ hne) x ≤
        D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card F) t nn) := by
  have hq1 : (1 : ℝ) ≤ ((Fintype.card F : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  set q : ℝ := ((Fintype.card F : ℕ) : ℝ) with hq_def
  set e := (fun t => TraceMixing.coarseErr q t nn)
  have hc : ∀ i : Fin D.cut.half.card, 0 < q / 2 ^ D.tdeg i := fun i => by positivity
  have ha : ∀ i : Fin D.cut.half.card, 0 < q / 2 ^ D.tdeg i * (1 - e (D.tdeg i)) := fun i =>
    mul_pos (hc i) (by linarith [he1 i])
  have hb : ∀ i : Fin D.cut.half.card, 0 < q / 2 ^ D.tdeg i * (1 + e (D.tdeg i)) := fun i =>
    mul_pos (hc i)
      (by linarith [TraceMixing.coarseErr_nonneg (by linarith : (0 : ℝ) < q) (D.tdeg i) nn])
  set A := ∏ i, q / 2 ^ D.tdeg i * (1 - e (D.tdeg i))
  set B := ∏ i, q / 2 ^ D.tdeg i * (1 + e (D.tdeg i))
  have hA : 0 < A := Finset.prod_pos (fun i _ => ha i)
  have hB : 0 < B := Finset.prod_pos (fun i _ => hb i)
  have hLo : A ≤ ∏ j, stepLower (Fintype.card F) nn (D.tdeg j) :=
    Finset.prod_le_prod₀ (fun i _ => (ha i).le) (fun i _ => coarse_le_stepLower hq1 nn _)
  have hUp : ∏ j, stepUpper (Fintype.card F) (D.tdeg j) ≤ B :=
    Finset.prod_le_prod₀ (fun i _ => div_nonneg (add_nonneg (by positivity)
      (softError_nonneg _ _)) (by positivity)) (fun i _ => stepUpper_le_coarse hq1 nn _)
  have hLo0 : 0 < ∏ j, stepLower (Fintype.card F) nn (D.tdeg j) := lt_of_lt_of_le hA hLo
  obtain ⟨h1, h2⟩ := D.rho_bounds hW hn hne hLo0 hx
  have hratio : B / A = D.Rcut e := by
    unfold Rcut
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl (fun i _ => ?_)
    have hci := (hc i).ne'
    have h1e : 1 - e (D.tdeg i) ≠ 0 := by linarith [he1 i]
    field_simp
  have hUp0 : 0 < ∏ j, stepUpper (Fintype.card F) (D.tdeg j) :=
    lt_of_lt_of_le hLo0 ((D.Ncount_bounds hW hn hx).1.trans (D.Ncount_bounds hW hn hx).2)
  constructor
  · refine le_trans ?_ h1
    rw [← hratio, inv_div]
    exact div_le_div₀ hLo0.le hLo hUp0 hUp
  · refine h2.trans ?_
    rw [← hratio]
    exact div_le_div₀ hB.le hUp hA hLo

/-- **`lem:spec:cutkernel` (c), coarse form.** For `x ∈ I⁺`, `N₋ ≤ N(x) ≤ N₊` with
`N_± = ∏_i p 2^{-t_i} (1 ± e_{t_i}(p, n'))`; and `N₊/N₋ = R_cut` when every `e_{t_i} < 1`. -/
theorem Ncount_coarse (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn < 1)
    {x : D.cut.Half → F} (hx : x ∈ injLabellings F D.halfGraph) :
    ∏ i, (Fintype.card F : ℝ) / 2 ^ D.tdeg i *
        (1 - TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn) ≤ (D.Ncount x : ℝ) ∧
      (D.Ncount x : ℝ) ≤ ∏ i, (Fintype.card F : ℝ) / 2 ^ D.tdeg i *
        (1 + TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn) ∧
      (∏ i, (Fintype.card F : ℝ) / 2 ^ D.tdeg i *
          (1 + TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn)) /
        (∏ i, (Fintype.card F : ℝ) / 2 ^ D.tdeg i *
          (1 - TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn)) =
          D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card F) t nn) := by
  have hq1 : (1 : ℝ) ≤ ((Fintype.card F : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  obtain ⟨hlo, hup⟩ := D.Ncount_bounds hW hn hx
  have hc : ∀ t : ℕ, (0 : ℝ) < (Fintype.card F : ℝ) / 2 ^ t := fun t => by positivity
  refine ⟨le_trans (Finset.prod_le_prod₀ (fun i _ => (mul_pos (hc _)
      (by linarith [he1 i])).le) (fun i _ => coarse_le_stepLower hq1 nn _)) hlo,
    hup.trans (Finset.prod_le_prod₀ (fun i _ => div_nonneg (add_nonneg (by positivity)
      (softError_nonneg _ _)) (by positivity)) (fun i _ => stepUpper_le_coarse hq1 nn _)), ?_⟩
  unfold Rcut
  rw [← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl (fun i _ => ?_)
  have hci := (hc (D.tdeg i)).ne'
  have h1e : 1 - TraceMixing.coarseErr (Fintype.card F) (D.tdeg i) nn ≠ 0 := by linarith [he1 i]
  field_simp

/-! ### Nonemptiness (`lem:spec:cutkernel` (a), first claim) -/

/-- If every vertex has at most `Δ` neighbours and `e_t(q, n') < 1` for `t ≤ Δ`, every lower
product is positive. -/
theorem lowerProd_pos {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W) {q : ℝ}
    (hq : 1 ≤ q) {nn Δ : ℕ} (he : ∀ t ≤ Δ, TraceMixing.coarseErr q t nn < 1)
    (hdeg : ∀ v, (Finset.univ.filter (fun w => (v, w) ∈ G.E ∨ (w, v) ∈ G.E)).card ≤ Δ) :
    ∀ (l : List W) (A : Finset W), 0 < lowerProd G q nn A l
  | [], _ => by simp [lowerProd]
  | v :: l, A => by
      classical
      simp only [lowerProd]
      refine mul_pos ?_ (lowerProd_pos G hq he hdeg l _)
      have hnb : nbrCount G A v ≤ Δ := by
        refine le_trans ?_ (hdeg v)
        unfold nbrCount
        refine Finset.card_le_card (fun u hu => ?_)
        rw [Finset.mem_filter] at hu ⊢
        exact ⟨Finset.mem_univ _, hu.2.symm⟩
      have h1 := coarse_le_stepLower hq nn (nbrCount G A v)
      have h2 : 0 < q / 2 ^ nbrCount G A v * (1 - TraceMixing.coarseErr q (nbrCount G A v) nn) :=
        mul_pos (by positivity) (by linarith [he _ hnb])
      exact lt_of_lt_of_le h2 h1

/-- **`lem:spec:cutkernel` (a), first claim.** If `e_t(q, n') < 1` for `t ≤ Δ` (for instance
`e_Δ(p, 2n) < 1`, by `TraceMixing.coarseErr_mono`), then `Inj(G)` (and so `I⁺`) is nonempty. -/
theorem inj_nonempty (hW : WeilBound F) {nn : ℕ} (hn : Fintype.card U ≤ nn)
    (he : ∀ t ≤ D.Delta, TraceMixing.coarseErr (Fintype.card F) t nn < 1) :
    (injLabellings F D.G).Nonempty := by
  have hq1 : (1 : ℝ) ≤ ((Fintype.card F : ℕ) : ℝ) := by exact_mod_cast Fintype.card_pos
  have hdeg : ∀ v, (Finset.univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤
      D.Delta := by
    intro v
    rw [← D.maxDegree_eq_Delta]
    exact Finset.le_sup (f := D.degree) (Finset.mem_univ v)
  have hpos := lowerProd_pos D.G hq1 he hdeg Finset.univ.toList ∅
  have hle := lowerProd_le_card_inj hW D.G hn Finset.univ.toList (Finset.nodup_toList _)
    (fun w => Finset.mem_toList.mpr (Finset.mem_univ w))
  have : (0 : ℝ) < (injLabellings F D.G).card := lt_of_lt_of_le hpos hle
  exact Finset.card_pos.mp (by exact_mod_cast this)

end SpecData

end Sarkozy.Cuts

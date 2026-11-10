module

public import Sarkozy.SpectralD.CxCutCounts

@[expose] public section






namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- `N_i(x, a) = #{x' ∈ 𝓘⁺ : K(x, x') = 1, x'_i = a}`. -/
noncomputable def NcountAt (x : D.cut.Half → ZMod p) (i : D.cut.Half) (a : ZMod p) : ℕ := by
  classical exact ((Labellings.injLabellings (ZMod p) D.halfGraph).filter
    (fun x' => D.CutOK x x' ∧ x' i = a)).card

/-- The fixed vertices `U⁺ ∪ {ϑi}`. -/
def fixSet (i : D.cut.Half) : Finset W := insert (D.cut.flip i.1) D.cut.half

/-- The partial labelling: `x` on `U⁺`, `a` at `ϑi`. -/
noncomputable def fixLab (x : D.cut.Half → ZMod p) (i : D.cut.Half) (a : ZMod p) : W → ZMod p :=
  Function.update (D.glue x x) (D.cut.flip i.1) a

omit [Fact p.Prime] in
lemma glue_half (x x' : D.cut.Half → ZMod p) {w : W} (hw : w ∈ D.cut.half) :
    D.glue x x' w = x ⟨w, hw⟩ := by
  simp only [Cuts.SpecData.glue, dite_eq_left hw]

omit [Fact p.Prime] in
lemma glue_flip (x x' : D.cut.Half → ZMod p) (i : D.cut.Half) :
    D.glue x x' (D.cut.flip i.1) = x' i := by
  have h := D.cut.flip_not_mem i.2
  simp only [Cuts.SpecData.glue, dite_eq_right h]
  congr 1
  exact Subtype.ext (D.cut.flip_flip i.1)

theorem NcountAt_eq_extCount {x : D.cut.Half → ZMod p}
    (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) (i : D.cut.Half) (a : ZMod p) :
    NcountAt D x i a = Labellings.extCount D.G (fixSet D i) (fixLab D x i a) := by
  classical
  unfold NcountAt Labellings.extCount
  have hfi : D.cut.flip i.1 ∉ D.cut.half := D.cut.flip_not_mem i.2
  have hfix : ∀ w (hw : w ∈ D.cut.half), fixLab D x i a w = x ⟨w, hw⟩ := by
    intro w hw
    have hne : w ≠ D.cut.flip i.1 := fun h => hfi (h ▸ hw)
    unfold fixLab
    rw [Function.update_of_ne hne, glue_half D x x hw]
  refine Finset.card_nbij' (fun x' => D.glue x x') (fun y => D.halfR y) ?_ ?_ ?_ ?_
  · intro x' hx'
    simp only [Finset.mem_coe, Finset.mem_filter] at hx' ⊢
    obtain ⟨hx'I, hok, hxa⟩ := hx'
    refine ⟨(D.glue_mem_iff x x').2 ⟨hx, hx'I, hok⟩, fun w hw => ?_⟩
    rcases mem_insert.mp hw with rfl | hw'
    · rw [glue_flip, hxa]; unfold fixLab; rw [Function.update_self]
    · rw [glue_half D x x' hw', hfix w hw']
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy ⊢
    obtain ⟨hyI, hagree⟩ := hy
    obtain ⟨_, h2, h3⟩ := (D.mem_inj_iff y).1 hyI
    have hL : D.halfL y = x := by
      funext k
      simp only [Cuts.SpecData.halfL]
      rw [hagree k.1 (mem_insert_of_mem k.2), hfix k.1 k.2]
    rw [hL] at h3
    refine ⟨h2, h3, ?_⟩
    simp only [Cuts.SpecData.halfR]
    rw [hagree _ (mem_insert_self _ _)]
    unfold fixLab
    rw [Function.update_self]
  · intro x' _
    exact (D.halves_glue x x').2
  · intro y hy
    simp only [Finset.mem_coe, Finset.mem_filter] at hy
    obtain ⟨_, hagree⟩ := hy
    have hL : D.halfL y = x := by
      funext k
      simp only [Cuts.SpecData.halfL]
      rw [hagree k.1 (mem_insert_of_mem k.2), hfix k.1 k.2]
    show D.glue x (D.halfR y) = y
    rw [← hL, D.glue_halves]

/-- **The partial labelling is feasible** for `a` in the allowed set `Φ_i(x)`. -/
theorem fixLab_feasible {x : D.cut.Half → ZMod p}
    (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) (i : D.cut.Half) {a : ZMod p}
    (ha : a ∈ allowedSet D.Nset (sgnZ D) i x) :
    Labellings.Feasible (ZMod p) D.G (fixSet D i) (fixLab D x i a) := by
  classical
  apply Labellings.feasible_insert (D.feasible_glue hx) (D.cut.flip_not_mem i.2)
  simp only [allowedSet, mem_filter, mem_univ, true_and] at ha
  obtain ⟨ha1, ha2⟩ := ha
  simp only [Labellings.vertexAdmissible, mem_filter, mem_univ, true_and]
  refine ⟨?_, fun u hu he => ?_, fun u hu he => ?_⟩
  · intro hmem
    obtain ⟨u, hu, hua⟩ := mem_image.mp hmem
    apply ha1
    rw [glue_half D x x hu] at hua
    exact mem_image.mpr ⟨⟨u, hu⟩, mem_univ _, hua⟩
  · -- an edge into `ϑi`: `ς = 1`
    have hs : D.sgn ⟨u, hu⟩ i = 1 := by
      simp only [Cuts.SpecData.sgn, he, ↓reduceIte]
    have hj : (⟨u, hu⟩ : D.cut.Half) ∈ D.Nset i := by
      simp only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and, hs]; decide
    obtain ⟨hne, hsq⟩ := ha2 _ hj
    have h1 : (sgnZ (p := p) D ⟨u, hu⟩ i) = 1 := by
      unfold sgnZ; rw [hs]; simp
    rw [h1, one_mul] at hne hsq
    rw [glue_half D x x hu]
    exact (quadraticChar_one_iff_isSquare hne).mpr hsq
  · -- an edge out of `ϑi`: `ς = −1`
    have hno : (u, D.cut.flip i.1) ∉ D.G.E := fun h => D.G.oriented _ _ he h
    have hs : D.sgn ⟨u, hu⟩ i = -1 := by
      simp only [Cuts.SpecData.sgn, hno, he, ↓reduceIte]
    have hj : (⟨u, hu⟩ : D.cut.Half) ∈ D.Nset i := by
      simp only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and, hs]; decide
    obtain ⟨hne, hsq⟩ := ha2 _ hj
    have h1 : (sgnZ (p := p) D ⟨u, hu⟩ i) = -1 := by
      unfold sgnZ; rw [hs]; simp
    rw [h1] at hne hsq
    rw [glue_half D x x hu]
    have e : x ⟨u, hu⟩ - a = -1 * (a - x ⟨u, hu⟩) := by ring
    rw [e]
    exact (quadraticChar_one_iff_isSquare hne).mpr hsq

/-- **`L_i ≤ N_i(a) ≤ U_i` on `Φ_i(x)`** (`lem:extension`, sequentially along `l_i`). -/
theorem NcountAt_bounds (hW : Labellings.WeilBound (ZMod p)) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (i : D.cut.Half) (l : List W) (hnd : l.Nodup) (hcov : ∀ w, w ∈ fixSet D i ∨ w ∈ l)
    (hdisj : ∀ w ∈ l, w ∉ fixSet D i) {x : D.cut.Half → ZMod p}
    (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) {a : ZMod p}
    (ha : a ∈ allowedSet D.Nset (sgnZ D) i x) :
    Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) l ≤ (NcountAt D x i a : ℝ) ∧
      (NcountAt D x i a : ℝ) ≤ Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) l := by
  rw [NcountAt_eq_extCount D hx]
  exact Labellings.extCount_bounds hW D.G hn l (fixSet D i) (fixLab D x i a) hnd hcov hdisj
    (fixLab_feasible D hx i ha)

/-- `N(x) = ∑_b N_i(b)`. -/
theorem Ncount_eq_sum (x : D.cut.Half → ZMod p) (i : D.cut.Half) :
    D.Ncount x = ∑ b, NcountAt D x i b := by
  classical
  unfold Cuts.SpecData.Ncount NcountAt
  rw [card_eq_sum_card_fiberwise (f := fun x' => x' i) (t := univ) (fun _ _ => mem_univ _)]
  refine sum_congr rfl fun b _ => ?_
  congr 1
  ext x'
  simp only [mem_filter]
  tauto

/-- `N_i(b) = 0` for `b ∉ Φ_i(x)` (as in `condP_supp`). -/
theorem NcountAt_off (x : D.cut.Half → ZMod p) (i : D.cut.Half) {b : ZMod p}
    (hb : b ∉ allowedSet D.Nset (sgnZ D) i x) : NcountAt D x i b = 0 := by
  classical
  unfold NcountAt
  rw [card_eq_zero, filter_eq_empty_iff]
  rintro x' - ⟨⟨hd, hc⟩, hx'b⟩
  apply hb
  simp only [allowedSet, mem_filter, mem_univ, true_and]
  refine ⟨?_, fun j hj => ?_⟩
  · intro hmem
    rw [disjoint_left] at hd
    exact hd hmem (mem_image.mpr ⟨i, mem_univ _, hx'b⟩)
  · have hjk : (j, i) ∈ D.crossPairs := by
      simp only [Cuts.SpecData.crossPairs, mem_filter, mem_univ, true_and]
      simp only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] at hj
      exact hj
    have hq := hc (j, i) hjk
    simp only at hq
    rw [hx'b] at hq
    have hne0 : (sgnZ D j i : ZMod p) * (b - x j) ≠ 0 := by
      intro h0
      unfold sgnZ at h0
      rw [h0, quadraticChar_zero] at hq
      exact zero_ne_one hq
    exact ⟨hne0, (quadraticChar_one_iff_isSquare hne0).mp hq⟩

/-- **`P_i(a | x) = N_i(a)/N(x)`** for the uniform half law and `K/Z`. -/
theorem condP_eq_count (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x : D.cut.Half → ZMod p) (i : D.cut.Half) (a : ZMod p) :
    condP (D.halfLaw hne).weight (cutKn D hne) i x a = (NcountAt D x i a : ℝ) / D.Ncount x := by
  classical
  set I := Labellings.injLabellings (ZMod p) D.halfGraph with hI
  have hIc : (0 : ℝ) < I.card := by exact_mod_cast card_pos.mpr (D.half_nonempty hne)
  have hZ := D.cutZ_pos hne
  have hw : ∀ x', (D.halfLaw hne).weight x' = if x' ∈ I then 1 / (I.card : ℝ) else 0 := by
    intro x'; rfl
  have hnum : ∑ x', (if x' i = a then (D.halfLaw hne).weight x' * cutKn D hne x x' else 0) =
      (NcountAt D x i a : ℝ) / ((I.card : ℝ) * D.cutZ hne) := by
    have e : ∀ x', (if x' i = a then (D.halfLaw hne).weight x' * cutKn D hne x x' else 0) =
        (if x' ∈ I.filter (fun x' => D.CutOK x x' ∧ x' i = a) then 1 else 0) /
          ((I.card : ℝ) * D.cutZ hne) := by
      intro x'
      rw [hw]
      unfold cutKn Cuts.SpecData.cutK
      by_cases h1 : x' ∈ I <;> by_cases h2 : D.CutOK x x' <;> by_cases h3 : x' i = a <;>
        simp [h1, h2, h3, mem_filter, mul_comm]
    rw [sum_congr rfl fun x' _ => e x', ← sum_div, sum_boole]
    unfold NcountAt
    simp only [filter_mem_eq_inter, univ_inter]
    rfl
  have hden : rhoK (D.halfLaw hne).weight (cutKn D hne) x =
      (D.Ncount x : ℝ) / ((I.card : ℝ) * D.cutZ hne) := by
    unfold rhoK
    have e : ∀ x', (D.halfLaw hne).weight x' * cutKn D hne x x' =
        (if x' ∈ I.filter (fun x' => D.CutOK x x') then 1 else 0) /
          ((I.card : ℝ) * D.cutZ hne) := by
      intro x'
      rw [hw]
      unfold cutKn Cuts.SpecData.cutK
      by_cases h1 : x' ∈ I <;> by_cases h2 : D.CutOK x x' <;>
        simp [h1, h2, mem_filter, mul_comm]
    rw [sum_congr rfl fun x' _ => e x', ← sum_div, sum_boole]
    unfold Cuts.SpecData.Ncount
    simp only [filter_mem_eq_inter, univ_inter]
    rfl
  unfold condP
  rw [hnum, hden]
  have hc : (I.card : ℝ) * D.cutZ hne ≠ 0 := by positivity
  rw [div_div_div_cancel_right₀ hc]

/-- **The densities (iii) of instance (A)** (`eq:spec:Rprime`): for `x ∈ 𝓘⁺` and
`a ∈ Φ_i(x)`, `|Φ_i(x)| P_i(a | x) ∈ [1/R'_i, R'_i]`, `R'_i = max(1, U_i/L_i)`, where `L_i`,
`U_i` are the sequential lower and upper counts along `l_i` (`L_i > 0` assumed; WP-P's
`lowerProd_pos` gives it when `e_t(p, n') < 1` up to the maximal degree). This is the
hypothesis `hPdens` of `couplingDataA` and `couplingBound_cut`. -/
theorem PA_density (hW : Labellings.WeilBound (ZMod p)) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (l : D.cut.Half → List W) (hnd : ∀ i, (l i).Nodup)
    (hcov : ∀ i w, w ∈ fixSet D i ∨ w ∈ l i) (hdisj : ∀ i, ∀ w ∈ l i, w ∉ fixSet D i)
    (hLpos : ∀ i, 0 < Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i))
    (i : D.cut.Half) {x : D.cut.Half → ZMod p}
    (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) {a : ZMod p}
    (ha : a ∈ allowedSet D.Nset (sgnZ D) i x) :
    (max 1 (Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) (l i) /
        Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i)))⁻¹ ≤
        PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ∧
      PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ≤
        max 1 (Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) (l i) /
          Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i)) := by
  set L := Labellings.lowerProd D.G (Fintype.card (ZMod p)) nn (fixSet D i) (l i) with hLdef
  set Up := Labellings.upperProd D.G (Fintype.card (ZMod p)) (fixSet D i) (l i) with hUdef
  set Φ := allowedSet D.Nset (sgnZ D) i x with hΦ
  have hL := hLpos i
  have hb : ∀ b ∈ Φ, L ≤ (NcountAt D x i b : ℝ) ∧ (NcountAt D x i b : ℝ) ≤ Up :=
    fun b hb => NcountAt_bounds D hW hn i (l i) (hnd i) (hcov i) (hdisj i) hx hb
  have hNsum : (D.Ncount x : ℝ) = ∑ b ∈ Φ, (NcountAt D x i b : ℝ) := by
    rw [Ncount_eq_sum D x i]
    push_cast
    rw [← sum_subset (subset_univ Φ) fun b _ hbΦ => by
      rw [NcountAt_off D x i hbΦ]; simp]
  have hΦpos : (0 : ℝ) < Φ.card := by exact_mod_cast card_pos.mpr ⟨a, ha⟩
  have hNlow : (Φ.card : ℝ) * L ≤ D.Ncount x := by
    rw [hNsum]
    calc (Φ.card : ℝ) * L = ∑ _b ∈ Φ, L := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := sum_le_sum fun b hb' => (hb b hb').1
  have hNup : (D.Ncount x : ℝ) ≤ Φ.card * Up := by
    rw [hNsum]
    calc ∑ b ∈ Φ, (NcountAt D x i b : ℝ) ≤ ∑ _b ∈ Φ, Up := sum_le_sum fun b hb' => (hb b hb').2
      _ = Φ.card * Up := by rw [sum_const, nsmul_eq_mul]
  have hNpos : (0 : ℝ) < D.Ncount x := lt_of_lt_of_le (mul_pos hΦpos hL) hNlow
  have hUpos : 0 < Up := lt_of_lt_of_le hL (le_trans (hb a ha).1 (hb a ha).2)
  have hPA : PA D hne i x a = (NcountAt D x i a : ℝ) / D.Ncount x := by
    unfold PA
    simp only [hx, ↓reduceIte]
    exact condP_eq_count D hne x i a
  rw [hPA]
  obtain ⟨ha1, ha2⟩ := hb a ha
  have hval : (NcountAt D x i a : ℝ) / D.Ncount x * Φ.card =
      (NcountAt D x i a : ℝ) * Φ.card / D.Ncount x := by ring
  rw [hval]
  constructor
  · -- `L/U ≤ N(a)|Φ|/N`
    have h1 : L / Up ≤ (NcountAt D x i a : ℝ) * Φ.card / D.Ncount x := by
      rw [div_le_div_iff₀ hUpos hNpos]
      calc L * D.Ncount x ≤ L * (Φ.card * Up) := mul_le_mul_of_nonneg_left hNup hL.le
        _ = (L * Φ.card) * Up := by ring
        _ ≤ ((NcountAt D x i a : ℝ) * Φ.card) * Up :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha1 hΦpos.le) hUpos.le
    refine le_trans ?_ h1
    rw [inv_le_comm₀ (lt_of_lt_of_le one_pos (le_max_left _ _)) (div_pos hL hUpos), inv_div]
    exact le_max_right _ _
  · -- `N(a)|Φ|/N ≤ U/L`
    have h2 : (NcountAt D x i a : ℝ) * Φ.card / D.Ncount x ≤ Up / L := by
      rw [div_le_div_iff₀ hNpos hL]
      calc (NcountAt D x i a : ℝ) * Φ.card * L ≤ Up * Φ.card * L :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ha2 hΦpos.le) hL.le
        _ = Up * (Φ.card * L) := by ring
        _ ≤ Up * D.Ncount x := mul_le_mul_of_nonneg_left hNlow hUpos.le
    exact h2.trans (le_max_right _ _)

end Sarkozy.SpectralD.Cx

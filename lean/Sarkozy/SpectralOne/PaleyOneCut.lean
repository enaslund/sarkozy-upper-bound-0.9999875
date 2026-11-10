module

public import Sarkozy.SpectralOne.Marginal
public import Sarkozy.SpectralD.CxCutCounts

@[expose] public section

/-!
# `lem:spec2:paley-one` for the cut laws (instance (A))

`paper/sections/14_spectral.tex`, `subsec:advance:parity`, `lem:spec2:paley-one`: "Let
`p ≡ 1 (mod 4)` … For every `J ⊆ U⁺` with `|J| ≥ 2` … If `J` is not coverable, then
`|t_J| ≤ ζ r`, `ζ = (R_ν R_full − 1) + n/((p − n) r)` … In instance (A),
`R_ν R_full = R_cut R_full`."

The proof uses, for the law `ν = ϱ λ(G⁺)` of instance (A):
* `lem:graphs:vertex`(subset) for `G⁺`: the law of `x_J` under `λ(G⁺)` is proportional to the
  number of completions of `x_J` in `Inj_p(G⁺)`, which lies in `[L_J, U_J]` (`lem:extension`,
  `Labellings.extCount_bounds`, along any ordering of `U⁺ ∖ J`);
* the density bound (i) of the coupling data, `ϱ ∈ [R_cut⁻¹, R_cut]` on `Inj_p(G⁺)` (S1's
  `rho_counts`, from `lem:spec:cutkernel`(c));
* the isolated-vertex bound (`norm_tJ_le_isolated`).

Formalized:
* `card_inj_eq_sum`: `|Inj_p(G)| = ∑_{y ∈ Inj_p(G[J])} C_J(y)`;
* `margJ_dens`: the law of `x_J` under `ϱ λ(G)` has density in `[1/R, R]` with respect to
  `u_cons`, `R = R₀ U_J/L_J`, when `ϱ ∈ [R₀⁻¹, R₀]` on `Inj_p(G)` and `C_J ∈ [L_J, U_J]`;
* `tJ_graph_le`: `|t_J| ≤ (R₀ U_J/L_J − 1) r + |J|/(p − |J| + 1)` for `J` with an isolated
  vertex, any oriented graph `G`, `ν = ϱ λ(G)`;
* **`tJ_nuA_le`**: the same for S1's `nuA D hne` (instance (A) of the cut), `R₀ = R_cut`, with
  `L_J`, `U_J` the lower and upper products along `(U⁺ ∖ J).toList`;
* **`hzeta_cut`**: S1's hypothesis `hζ` of `spectral_criterion_cut` (`cor:spec2:coupling`), for
  every relation `Adj` containing the adjacency of `G⁺`, with the paper's
  `ζ = (R_cut R_full − 1) + n/((p − n) r)`. Here `R_full` is any bound
  `U_J ≤ R_full L_J` (`hRfull`; the paper's `∏_{i∈U⁺}(1 + e_{d⁰_i}(p, n))/(1 − e_{d⁰_i}(p, n))`
  is such a bound by the step comparisons of `lem:extension`, which are not restated here).

The bound holds at every odd `p`; S1's `hζ` asks for it only at `p ≡ 1 (mod 4)`.

New material for this paper.
-/

namespace Sarkozy.SpectralOne

attribute [local instance] feasibleDec

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC Sarkozy.Labellings
open scoped BigOperators ComplexConjugate

section Counts

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

lemma feasible_restr_of_inj {G : OrientedGraph U} (J : Finset U) {x : U → ZMod p}
    (hx : x ∈ injLabellings (ZMod p) G) : Feasible (ZMod p) G J (restr J x) := by
  have hF : Feasible (ZMod p) G univ x := by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx
  have hJ : Feasible (ZMod p) G J x :=
    ⟨fun a _ b _ h => hF.1 a (mem_univ _) b (mem_univ _) h,
      fun e he _ _ => hF.2 e he (mem_univ _) (mem_univ _)⟩
  exact (feasible_congr fun k hk => restr_apply_of_mem hk x).mpr hJ

/-- `C_J(y)`, the number of completions of `y` in `Inj_p(G)`, is the size of the fibre of `y`. -/
lemma extCount_eq_fiber (G : OrientedGraph U) {J : Finset U} {y : U → ZMod p}
    (hy : y ∈ cfgs J) :
    extCount G J y = ((injLabellings (ZMod p) G).filter (fun x => restr J x = y)).card := by
  unfold extCount
  congr 1
  ext x
  simp only [mem_filter]
  rw [restr_eq_iff hy]

/-- `|Inj_p(G)| = ∑_{y ∈ Inj_p(G[J])} C_J(y)`. -/
lemma card_inj_eq_sum (G : OrientedGraph U) (J : Finset U) :
    ((injLabellings (ZMod p) G).card : ℝ) = ∑ y ∈ feasCfgs (p := p) G J, (extCount G J y : ℝ) := by
  rw [card_eq_sum_ones, Nat.cast_sum,
    ← sum_fiberwise_of_maps_to (g := restr J) (t := cfgs J) (fun x _ => restr_mem_cfgs J x),
    feasCfgs, sum_filter]
  refine sum_congr rfl fun y hy => ?_
  split_ifs with hfe
  · rw [extCount_eq_fiber G hy]
    simp
  · refine sum_eq_zero fun x hx => ?_
    obtain ⟨hxI, hxy⟩ := mem_filter.mp hx
    exact absurd (hxy ▸ feasible_restr_of_inj J hxI) hfe

/-- **The law of `x_J` under `ϱ λ(G)`** (`lem:graphs:vertex`(subset) with the density bound (i)):
if `ϱ ∈ [R₀⁻¹, R₀]` on `Inj_p(G)` and every completion count `C_J(y)` of `y ∈ Inj_p(G[J])` lies
in `[L, U']`, `L > 0`, then the law of `x_J` has density in `[1/R, R]` with respect to `u_cons`,
`R = R₀ U'/L`. -/
theorem margJ_dens (G : OrientedGraph U) (hne : (injLabellings (ZMod p) G).Nonempty)
    (ϱ : (U → ZMod p) → ℝ) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hϱ : ∀ x ∈ injLabellings (ZMod p) G, R₀⁻¹ ≤ ϱ x ∧ ϱ x ≤ R₀)
    (J : Finset U) {L Up : ℝ} (hL : 0 < L)
    (hcnt : ∀ y ∈ feasCfgs (p := p) G J, L ≤ extCount G J y ∧ (extCount G J y : ℝ) ≤ Up)
    (y : U → ZMod p) :
    (R₀ * (Up / L))⁻¹ * refLaw G J y ≤ margJ (fun x => (graphLaw G hne).weight x * ϱ x) J y ∧
      margJ (fun x => (graphLaw G hne).weight x * ϱ x) J y ≤ R₀ * (Up / L) * refLaw G J y := by
  set I := injLabellings (ZMod p) G with hI
  set N : ℝ := (I.card : ℝ) with hN
  have hNpos : 0 < N := by rw [hN]; exact_mod_cast card_pos.mpr hne
  -- the marginal as a sum over the fibre in `Inj_p(G)`
  have hm : margJ (fun x => (graphLaw G hne).weight x * ϱ x) J y =
      ∑ x ∈ I.filter (fun x => restr J x = y), ϱ x / N := by
    unfold margJ graphLaw
    simp only [ite_mul, zero_mul]
    rw [sum_ite_mem]
    have hset : univ.filter (fun x => restr J x = y) ∩ injLabellings (ZMod p) G =
        I.filter (fun x => restr J x = y) := by
      ext x; simp only [mem_inter, mem_filter, mem_univ, true_and, hI]; tauto
    rw [hset]
    refine sum_congr rfl fun x _ => ?_
    rw [hN]; ring
  rw [hm]
  by_cases hy : y ∈ feasCfgs (p := p) G J
  · have hyc : y ∈ cfgs J := (mem_filter.mp hy).1
    have hF : (feasCfgs (p := p) G J).Nonempty := ⟨y, hy⟩
    have hFc : (0 : ℝ) < (feasCfgs (p := p) G J).card := by exact_mod_cast card_pos.mpr hF
    have href : refLaw G J y = ((feasCfgs (p := p) G J).card : ℝ)⁻¹ := by
      simp only [refLaw, hy, ↓reduceIte]
    rw [href]
    obtain ⟨hLy, hUy⟩ := hcnt y hy
    have hLU : L ≤ Up := hLy.trans hUy
    have hU0 : 0 < Up := hL.trans_le hLU
    -- `N` is between `|F| L` and `|F| U'`
    have hNsum := card_inj_eq_sum (p := p) G J
    have hNlo : ((feasCfgs (p := p) G J).card : ℝ) * L ≤ N := by
      rw [hN, hNsum, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun z hz => (hcnt z hz).1
    have hNhi : N ≤ ((feasCfgs (p := p) G J).card : ℝ) * Up := by
      rw [hN, hNsum, ← nsmul_eq_mul, ← sum_const]
      exact sum_le_sum fun z hz => (hcnt z hz).2
    -- the fibre size
    have hE : (((I.filter (fun x => restr J x = y)).card : ℕ) : ℝ) = extCount G J y := by
      rw [extCount_eq_fiber G hyc]
    set E : ℝ := (((I.filter (fun x => restr J x = y)).card : ℕ) : ℝ) with hEdef
    have hsum_lo : R₀⁻¹ * E / N ≤ ∑ x ∈ I.filter (fun x => restr J x = y), ϱ x / N := by
      rw [hEdef, mul_comm, ← nsmul_eq_mul, ← sum_const, sum_div]
      exact sum_le_sum fun x hx =>
        div_le_div_of_nonneg_right (hϱ x (mem_filter.mp hx).1).1 hNpos.le
    have hsum_hi : ∑ x ∈ I.filter (fun x => restr J x = y), ϱ x / N ≤ R₀ * E / N := by
      rw [hEdef, mul_comm, ← nsmul_eq_mul, ← sum_const, sum_div]
      exact sum_le_sum fun x hx =>
        div_le_div_of_nonneg_right (hϱ x (mem_filter.mp hx).1).2 hNpos.le
    rw [hE] at hsum_lo hsum_hi
    set c : ℝ := ((feasCfgs (p := p) G J).card : ℝ) with hc
    constructor
    · -- lower bound: `R₀⁻¹ L/(c U') ≤ R₀⁻¹ C_J/N`
      refine le_trans ?_ hsum_lo
      have h1 : (R₀ * (Up / L))⁻¹ * c⁻¹ = R₀⁻¹ * L / (c * Up) := by
        field_simp
      rw [h1]
      have h2 : R₀⁻¹ * L / (c * Up) ≤ R₀⁻¹ * L / N :=
        div_le_div_of_nonneg_left (by positivity) hNpos hNhi
      have h3 : R₀⁻¹ * L / N ≤ R₀⁻¹ * (extCount G J y : ℝ) / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hLy (by positivity)) hNpos.le
      exact h2.trans h3
    · -- upper bound: `R₀ C_J/N ≤ R₀ U'/(c L)`
      refine hsum_hi.trans ?_
      have h1 : R₀ * (Up / L) * c⁻¹ = R₀ * Up / (c * L) := by
        field_simp
      rw [h1]
      have h2 : R₀ * (extCount G J y : ℝ) / N ≤ R₀ * Up / N :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hUy hR₀.le) hNpos.le
      have h3 : R₀ * Up / N ≤ R₀ * Up / (c * L) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hNlo
      exact h2.trans h3
  · -- off `Inj_p(G[J])` both laws vanish
    have hempty : I.filter (fun x => restr J x = y) = ∅ := by
      refine filter_eq_empty_iff.mpr fun x hxI hxy => hy ?_
      rw [← hxy]
      exact mem_filter.mpr ⟨restr_mem_cfgs J x, feasible_restr_of_inj J hxI⟩
    have href : refLaw G J y = 0 := by simp only [refLaw, hy, ↓reduceIte]
    rw [hempty, sum_empty, href, mul_zero, mul_zero]
    exact ⟨le_rfl, le_rfl⟩

/-- **`lem:spec2:paley-one` for `ν = ϱ λ(G)`**: if `j ∉ J` is isolated in `G[{j} ∪ J]`, the
density `ϱ` lies in `[R₀⁻¹, R₀]` on `Inj_p(G)`, and the completion counts of the labellings of
`J⁺ = {j} ∪ J` lie in `[L, U']`, then `|t_{J⁺}| ≤ (R₀ U'/L − 1) r + (|J| + 1)/(p − |J|)`. -/
theorem tJ_graph_le (hp2 : p ≠ 2) (G : OrientedGraph U) (hne : (injLabellings (ZMod p) G).Nonempty)
    (ϱ : (U → ZMod p) → ℝ) {R₀ : ℝ} (hR₀ : 1 ≤ R₀)
    (hϱ : ∀ x ∈ injLabellings (ZMod p) G, R₀⁻¹ ≤ ϱ x ∧ ϱ x ≤ R₀)
    {J : Finset U} {j : U} (hj : j ∉ J) (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E)
    {L Up : ℝ} (hL : 0 < L)
    (hcnt : ∀ y ∈ feasCfgs (p := p) G (insert j J),
      L ≤ extCount G (insert j J) y ∧ (extCount G (insert j J) y : ℝ) ≤ Up) :
    ‖SpectralD.PaleyB.tJ (fun x => (graphLaw G hne).weight x * ϱ x) (insert j J)‖ ≤
      (R₀ * (Up / L) - 1) * rp p + ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := by
  obtain ⟨x₀, hx₀⟩ := hne
  have hF : (feasCfgs (p := p) G (insert j J)).Nonempty :=
    ⟨restr (insert j J) x₀, mem_filter.mpr ⟨restr_mem_cfgs _ x₀, feasible_restr_of_inj _ hx₀⟩⟩
  obtain ⟨y₀, hy₀⟩ := hF
  have hLU : L ≤ Up := (hcnt y₀ hy₀).1.trans (hcnt y₀ hy₀).2
  have hR : 1 ≤ R₀ * (Up / L) := by
    have : 1 ≤ Up / L := (one_le_div hL).mpr hLU
    nlinarith
  exact norm_tJ_le_isolated hp2 G _ hj hiso ⟨y₀, hy₀⟩ hR
    (margJ_dens G ⟨x₀, hx₀⟩ ϱ (by linarith) hϱ (insert j J) hL hcnt)

end Counts

/-! ## The cut laws -/

section Cut

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The lower product `L_J` along `(U⁺ ∖ J).toList`. -/
noncomputable def lowJ (nn : ℕ) (J : Finset D.cut.Half) : ℝ :=
  lowerProd D.halfGraph (Fintype.card (ZMod p)) nn J (univ \ J).toList

/-- The upper product `U_J` along `(U⁺ ∖ J).toList`. -/
noncomputable def upJ (J : Finset D.cut.Half) : ℝ :=
  upperProd D.halfGraph (Fintype.card (ZMod p)) J (univ \ J).toList

/-- **`lem:spec2:paley-one` in instance (A) of the cut**: for `ν = ϱ λ(G⁺)` (`nuA`) and
`j ∉ J` isolated in `G⁺[{j} ∪ J]`, with `thm:weil`, `e_{t_i}(p, n') < 1` and `L_{J⁺} > 0`:
`|t_{J⁺}| ≤ (R_cut U_{J⁺}/L_{J⁺} − 1) r + (|J| + 1)/(p − |J|)`. -/
theorem tJ_nuA_le (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m)
    {J : Finset D.cut.Half} {j : D.cut.Half} (hj : j ∉ J)
    (hiso : ∀ i ∈ J, (i, j) ∉ D.halfGraph.E ∧ (j, i) ∉ D.halfGraph.E)
    (hL : 0 < lowJ (p := p) D m (insert j J)) :
    ‖SpectralD.PaleyB.tJ (SpectralD.Cx.nuA D hne) (insert j J)‖ ≤
      (D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) *
          (upJ (p := p) D (insert j J) / lowJ (p := p) D m (insert j J)) - 1) * rp p +
        ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := by
  have hR1 := SpectralD.Cx.one_le_Rcut D he1
  set Rc := D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) with hRc
  have hRc0 : 0 < Rc := by linarith
  obtain ⟨-, hdens⟩ := SpectralD.Cx.rho_counts D hW hn hne he1
  have hϱ : ∀ x ∈ injLabellings (ZMod p) D.halfGraph,
      Rc⁻¹ ≤ SpectralD.Cx.rhoK (D.halfLaw hne).weight (SpectralD.Cx.cutKn D hne) x ∧
        SpectralD.Cx.rhoK (D.halfLaw hne).weight (SpectralD.Cx.cutKn D hne) x ≤ Rc := by
    intro x hx
    obtain ⟨h1, h2⟩ := hdens x hx
    refine ⟨h1, h2.trans (le_of_eq ?_)⟩
    rw [← hRc]
    field_simp
  have hcnt : ∀ y ∈ feasCfgs (p := p) D.halfGraph (insert j J),
      lowJ (p := p) D m (insert j J) ≤ extCount D.halfGraph (insert j J) y ∧
        (extCount D.halfGraph (insert j J) y : ℝ) ≤ upJ (p := p) D (insert j J) := by
    intro y hy
    exact extCount_bounds hW D.halfGraph hm _ _ y (nodup_toList _)
      (fun w => by
        by_cases hw : w ∈ insert j J
        · exact Or.inl hw
        · exact Or.inr (mem_toList.mpr (mem_sdiff.mpr ⟨mem_univ _, hw⟩)))
      (fun w hw => (mem_sdiff.mp (mem_toList.mp hw)).2) (mem_filter.mp hy).2
  exact tJ_graph_le hp2 D.halfGraph (D.half_nonempty hne) _ hR1 hϱ hj hiso hL hcnt

/-- **S1's hypothesis `hζ`** (`cor:spec2:coupling`, `lem:spec2:paley-one`): for every relation
`Adj` containing the adjacency of `G⁺` (so that a non-coverable `J` has a vertex isolated in
`G⁺[J]`), if `U_J ≤ R_full L_J` with `L_J > 0` for the non-coverable `J`, and `|U⁺| ≤ m < p`,
then `|t_J| ≤ ζ r` for every non-coverable `J`, `|J| ≥ 2`, with the paper's
`ζ = (R_cut R_full − 1) + m/((p − m) r)`. -/
theorem hzeta_cut (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) {nn : ℕ} (hn : Fintype.card W ≤ nn)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (he1 : ∀ i, TraceMixing.coarseErr (Fintype.card (ZMod p)) (D.tdeg i) nn < 1)
    {m : ℕ} (hm : Fintype.card D.cut.Half ≤ m) (hmp : m < p)
    (Adj : D.cut.Half → D.cut.Half → Prop)
    (hAdj : ∀ i j : D.cut.Half, (i, j) ∈ D.halfGraph.E ∨ (j, i) ∈ D.halfGraph.E → Adj i j)
    {Rfull : ℝ}
    (hLJ : ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ SpectralD.PaleyB.Coverable Adj J →
      0 < lowJ (p := p) D m J)
    (hRJ : ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ SpectralD.PaleyB.Coverable Adj J →
      upJ (p := p) D J ≤ Rfull * lowJ (p := p) D m J) :
    ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ SpectralD.PaleyB.Coverable Adj J →
      ‖SpectralD.PaleyB.tJ (SpectralD.Cx.nuA D hne) J‖ ≤
        ((D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) * Rfull - 1) +
          (m : ℝ) / (((p : ℝ) - m) * rp p)) * rp p := by
  intro J hJ2 hnc
  -- an isolated vertex
  have hiso : ∃ j ∈ J, ∀ i ∈ J, i ≠ j → ¬ Adj i j := by
    by_contra h
    push Not at h
    exact hnc fun j hj => by
      obtain ⟨i, hi, hij, hadj⟩ := h j hj
      exact ⟨i, hi, hij, hadj⟩
  obtain ⟨j, hjJ, hjiso⟩ := hiso
  set J' := J.erase j with hJ'
  have hJeq : insert j J' = J := insert_erase hjJ
  have hj' : j ∉ J' := notMem_erase j J
  have hiso' : ∀ i ∈ J', (i, j) ∉ D.halfGraph.E ∧ (j, i) ∉ D.halfGraph.E := by
    intro i hi
    have hij : i ≠ j := ne_of_mem_erase hi
    have hna := hjiso i (mem_of_mem_erase hi) hij
    exact ⟨fun h => hna (hAdj i j (Or.inl h)), fun h => hna (hAdj i j (Or.inr h))⟩
  have hL := hLJ J hJ2 hnc
  have hRJ' := hRJ J hJ2 hnc
  rw [← hJeq] at hL hRJ' ⊢
  have h := tJ_nuA_le D hW hp2 hn hne he1 hm hj' hiso' hL
  have hR1 := SpectralD.Cx.one_le_Rcut D he1
  set Rc := D.Rcut (fun t => TraceMixing.coarseErr (Fintype.card (ZMod p)) t nn) with hRc
  have hr : 0 < rp p := by
    unfold rp
    have : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    positivity
  -- `U_J/L_J ≤ R_full`
  have hratio : upJ (p := p) D (insert j J') / lowJ (p := p) D m (insert j J') ≤ Rfull := by
    rw [div_le_iff₀ hL]; exact hRJ'
  have h1 : (Rc * (upJ (p := p) D (insert j J') / lowJ (p := p) D m (insert j J')) - 1) * rp p ≤
      (Rc * Rfull - 1) * rp p := by
    apply mul_le_mul_of_nonneg_right _ hr.le
    have := mul_le_mul_of_nonneg_left hratio (by linarith : (0 : ℝ) ≤ Rc)
    linarith
  -- `(|J'| + 1)/(p − |J'|) ≤ m/(p − m)`
  have hJcard : J'.card + 1 ≤ m := by
    have h1 : J'.card + 1 = J.card := by rw [hJ']; exact card_erase_add_one hjJ
    have h2 : J.card ≤ Fintype.card D.cut.Half := card_le_univ J
    omega
  have hmpR : (m : ℝ) < p := by exact_mod_cast hmp
  have h2 : ((J'.card : ℝ) + 1) / ((p : ℝ) - J'.card) ≤ (m : ℝ) / ((p : ℝ) - m) := by
    have hc : (J'.card : ℝ) + 1 ≤ m := by exact_mod_cast hJcard
    have hd : (p : ℝ) - m ≤ (p : ℝ) - J'.card := by linarith
    have hpm : (0 : ℝ) < (p : ℝ) - m := by linarith
    calc ((J'.card : ℝ) + 1) / ((p : ℝ) - J'.card) ≤ (m : ℝ) / ((p : ℝ) - J'.card) :=
          div_le_div_of_nonneg_right hc (by linarith)
      _ ≤ (m : ℝ) / ((p : ℝ) - m) := div_le_div_of_nonneg_left (by positivity) hpm hd
  have h3 : (m : ℝ) / ((p : ℝ) - m) = (m : ℝ) / (((p : ℝ) - m) * rp p) * rp p := by
    field_simp
  calc ‖SpectralD.PaleyB.tJ (SpectralD.Cx.nuA D hne) (insert j J')‖
      ≤ (Rc * (upJ (p := p) D (insert j J') / lowJ (p := p) D m (insert j J')) - 1) * rp p +
          ((J'.card : ℝ) + 1) / ((p : ℝ) - J'.card) := h
    _ ≤ (Rc * Rfull - 1) * rp p + (m : ℝ) / (((p : ℝ) - m) * rp p) * rp p := by
        rw [← h3]; exact add_le_add h1 h2
    _ = ((Rc * Rfull - 1) + (m : ℝ) / (((p : ℝ) - m) * rp p)) * rp p := by ring

end Cut

end Sarkozy.SpectralOne

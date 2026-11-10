module

public import Sarkozy.TraceMixing.Vertex
public import Sarkozy.TraceMixing.PairExplicit

/-!
# Marginals of a graph law on subsets (`lem:graphs:vertex`(c), (d))

`paper/sections/12_labellings.tex`, `lem:graphs:vertex`, over any finite field `F` with `q`
elements, for a graph with `|W| ≤ n` and `e_{d_i}(q, n) < 1` for every vertex `i`
(`d_i = deg_G(i)`), and `R_Y = ∏_{i ∈ Y} (1 + e_{d_i}(q, n))/(1 - e_{d_i}(q, n))` (`RY`).

The graph law `λ_p(G[J])` of the induced graph is the uniform law on the labellings of `J` that
are feasible for `G` on `J` (`feasLabels`; injective on `J`, strict squares on the edges inside
`J`), so its density with respect to it is `x ↦ λ_J(x) · |feasLabels|`.

* `upperProd_le_RY`: along any ordering `l`, `upperProd(A, l) ≤ R_l · lowerProd(A, l)` and
  `lowerProd(A, l) > 0` (each step: `(1 + e⁺_t)/(1 - e⁻_t(n)) ≤ (1 + e_d)/(1 - e_d)` for
  `t ≤ d`).
* (d) `marginalJ_support`: `λ_J` is supported on `feasLabels`; `marginalJ_density`: the density
  is positive on `feasLabels` and any two of its values have ratio at most `R_{W∖J}`, that is it
  takes values in an interval `[c', R_{W∖J} c']`, `c' > 0`; `marginalJ_density_bounds`: in
  particular in `[R_{W∖J}⁻¹, R_{W∖J}]`; `marginalJ_density_of_density`: for `m` with
  `dm/dλ ∈ [c, Rc]`, the density of `m_J` takes values in `[c'', R R_{W∖J} c'']`.
* (c) `marginal_delete`: the case `J = W ∖ {w}`.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)

/-- `R_Y = ∏_{i ∈ Y} (1 + e_{d_i}(q, n))/(1 - e_{d_i}(q, n))`. -/
noncomputable def RY (q : ℝ) (n : ℕ) (Y : Finset W) : ℝ :=
  ∏ i ∈ Y, (1 + coarseErr q (degree G i) n) / (1 - coarseErr q (degree G i) n)

variable (F) in
/-- The feasible labellings of `J`: the support of `λ_p(G[J])`. -/
noncomputable def feasLabels (J : Finset W) : Finset (J → F) := by
  classical exact univ.filter fun x => Feasible F G J (extendLabel J x)

omit [Fintype W] in
theorem mem_feasLabels {J : Finset W} {x : J → F} :
    x ∈ feasLabels F G J ↔ Feasible F G J (extendLabel J x) := by
  unfold feasLabels
  simp

theorem nbrCount_le_degree (A : Finset W) (v : W) : nbrCount G A v ≤ degree G v := by
  unfold nbrCount degree nbrCount
  apply card_le_card
  intro a ha
  simp only [mem_filter, mem_erase, mem_univ, and_true] at ha ⊢
  refine ⟨?_, ha.2⟩
  rintro rfl
  rcases ha.2 with h | h <;> exact G.loopless a h

/-- **One step**: `stepUpper(t) ≤ (1 + e_d)/(1 - e_d) · stepLower(t)` and `stepLower(t) > 0`
for `t ≤ d` and `e_d(q, n) < 1`. -/
theorem step_ratio {q : ℝ} (hq : 1 ≤ q) (n : ℕ) {t d : ℕ} (htd : t ≤ d)
    (hd : coarseErr q d n < 1) :
    stepUpper q t ≤ (1 + coarseErr q d n) / (1 - coarseErr q d n) * stepLower q n t ∧
      0 < stepLower q n t := by
  have hq0 : 0 < q := by linarith
  have hpow : (0 : ℝ) < 2 ^ t := pow_pos two_pos t
  have hden : 0 < 1 - coarseErr q d n := by linarith
  have hlow : Sarkozy.TraceMixing.lowerErr q t n ≤ coarseErr q d n :=
    (lowerErr_le_coarseErr hq t n).trans (coarseErr_mono hq0 htd le_rfl)
  have hsE : softError q t / q ≤ coarseErr q d n :=
    (softError_div_le_lowerErr hq0 t n).trans hlow
  have hL : q / 2 ^ t * (1 - coarseErr q d n) ≤ stepLower q n t := by
    unfold stepLower
    refine le_max_of_le_right ?_
    have hexp : (q - softError q t - 2 ^ t * n) / 2 ^ t =
        q / 2 ^ t * (1 - Sarkozy.TraceMixing.lowerErr q t n) := by
      unfold Sarkozy.TraceMixing.lowerErr
      field_simp
      ring
    rw [hexp]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hq0.le hpow.le)
  have hU : stepUpper q t ≤ q / 2 ^ t * (1 + coarseErr q d n) := by
    unfold stepUpper
    have hexp : (q + softError q t) / 2 ^ t = q / 2 ^ t * (1 + softError q t / q) := by
      field_simp
    rw [hexp]
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hq0.le hpow.le)
  have hLpos : 0 < q / 2 ^ t * (1 - coarseErr q d n) := mul_pos (div_pos hq0 hpow) hden
  refine ⟨?_, lt_of_lt_of_le hLpos hL⟩
  calc stepUpper q t ≤ q / 2 ^ t * (1 + coarseErr q d n) := hU
    _ = (1 + coarseErr q d n) / (1 - coarseErr q d n) * (q / 2 ^ t * (1 - coarseErr q d n)) := by
        field_simp
    _ ≤ (1 + coarseErr q d n) / (1 - coarseErr q d n) * stepLower q n t := by
        apply mul_le_mul_of_nonneg_left hL
        apply div_nonneg _ hden.le
        have := coarseErr_nonneg hq0 d n
        linarith

/-- **The completion ratio**: `upperProd(A, l) ≤ R_l · lowerProd(A, l)` and `lowerProd(A, l) > 0`
along any ordering, when every `e_{d_i}(q, n) < 1`. -/
theorem upperProd_le_RY {q : ℝ} (hq : 1 ≤ q) {n : ℕ}
    (hS1 : ∀ i, coarseErr q (degree G i) n < 1) :
    ∀ (l : List W) (A : Finset W), upperProd G q A l ≤
        (l.map fun i => (1 + coarseErr q (degree G i) n) / (1 - coarseErr q (degree G i) n)).prod *
          lowerProd G q n A l ∧ 0 < lowerProd G q n A l
  | [], A => by simp [upperProd, lowerProd]
  | v :: l, A => by
      obtain ⟨ih1, ih2⟩ := upperProd_le_RY hq hS1 l (insert v A)
      have hq0 : 0 < q := by linarith
      obtain ⟨hstep, hpos⟩ := step_ratio hq n (nbrCount_le_degree G A v) (hS1 v)
      have hU0 : 0 ≤ stepUpper q (nbrCount G A v) := by
        unfold stepUpper
        exact div_nonneg (add_nonneg hq0.le (softError_nonneg _ _)) (by positivity)
      have hR0 : 0 ≤ (1 + coarseErr q (degree G v) n) / (1 - coarseErr q (degree G v) n) := by
        apply div_nonneg
        · have := coarseErr_nonneg hq0 (degree G v) n
          linarith
        · linarith [hS1 v]
      have hup0 : 0 ≤ upperProd G q (insert v A) l := upperProd_nonneg G hq0.le l _
      simp only [upperProd, lowerProd, List.map_cons, List.prod_cons]
      refine ⟨?_, mul_pos hpos ih2⟩
      calc stepUpper q (nbrCount G A v) * upperProd G q (insert v A) l
          ≤ ((1 + coarseErr q (degree G v) n) / (1 - coarseErr q (degree G v) n) *
              stepLower q n (nbrCount G A v)) *
            ((l.map fun i => (1 + coarseErr q (degree G i) n) /
              (1 - coarseErr q (degree G i) n)).prod * lowerProd G q n (insert v A) l) :=
            mul_le_mul hstep ih1 hup0 (mul_nonneg hR0 hpos.le)
        _ = _ := by ring

variable (hne : (injLabellings F G).Nonempty)

/-- The marginal `λ_J(x) = P(z|_J = x)` of the graph law on `J`. -/
noncomputable def marginalJ (J : Finset W) (x : J → F) : ℝ :=
  (extCount G J (extendLabel J x) : ℝ) / (injLabellings F G).card

omit [Fintype F] [DecidableEq F] [Fintype W] in
theorem extendLabel_agree {J : Finset W} (y : W → F) :
    ∀ a ∈ J, y a = extendLabel J (fun a : J => y a) a := by
  intro a ha
  unfold extendLabel
  rw [dite_eq_left ha]

theorem feasible_of_extCount_ne_zero {J : Finset W} {x : W → F} (h : extCount G J x ≠ 0) :
    Feasible F G J x := by
  unfold extCount at h
  obtain ⟨y, hy⟩ := card_ne_zero.mp h
  simp only [mem_filter] at hy
  obtain ⟨hyinj, hagree⟩ := hy
  have hf := (mem_injLabellings_iff G y).mp hyinj
  exact feasible_congr' G hagree (feasible_mono G (subset_univ _) hf)

/-- **(d) `λ_J` is supported on the feasible labellings of `J`.** -/
theorem marginalJ_support (J : Finset W) (x : J → F) (hx : marginalJ G J x ≠ 0) :
    x ∈ feasLabels F G J := by
  rw [mem_feasLabels]
  apply feasible_of_extCount_ne_zero G
  intro h0
  apply hx
  unfold marginalJ
  rw [h0, Nat.cast_zero, zero_div]

include hne in
/-- The marginal of `λ` on `J` is a probability on the labellings of `J`. -/
theorem sum_marginalJ (J : Finset W) : ∑ x : J → F, marginalJ G J x = 1 := by
  have hI : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  unfold marginalJ
  rw [← Finset.sum_div, div_eq_one_iff_eq hI.ne']
  have hfib : ∀ x : J → F, extCount G J (extendLabel J x) =
      ((injLabellings F G).filter fun y => (fun a : J => y a) = x).card := by
    intro x
    unfold extCount
    congr 1
    ext y
    simp only [mem_filter]
    constructor
    · rintro ⟨hy, h⟩
      refine ⟨hy, funext fun a => ?_⟩
      rw [h a a.2]
      unfold extendLabel
      rw [dite_eq_left a.2]
    · rintro ⟨hy, rfl⟩
      exact ⟨hy, fun a ha => by unfold extendLabel; rw [dite_eq_left ha]⟩
  simp only [hfib]
  rw [← Nat.cast_sum]
  congr 1
  exact (card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)).symm

include hne in
/-- **(d) The density of `λ_J` with respect to `λ_p(G[J])`** (`x ↦ λ_J(x) |feasLabels|`) is
positive on `feasLabels`, and any two of its values have ratio at most `R_{W∖J}`. -/
theorem marginalJ_density (hW : WeilBound F) {n : ℕ} (hn : Fintype.card W ≤ n)
    (hS1 : ∀ i, coarseErr (Fintype.card F) (degree G i) n < 1) (J : Finset W) :
    (∀ x ∈ feasLabels F G J, 0 < marginalJ G J x * (feasLabels F G J).card) ∧
      ∀ x ∈ feasLabels F G J, ∀ x' ∈ feasLabels F G J,
        marginalJ G J x * (feasLabels F G J).card ≤
          RY G (Fintype.card F) n (univ \ J) * (marginalJ G J x' * (feasLabels F G J).card) := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hI : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  set l := (univ \ J).toList with hl
  have hnd : l.Nodup := nodup_toList _
  have hcov : ∀ w, w ∈ J ∨ w ∈ l := fun w => by
    by_cases h : w ∈ J
    · exact Or.inl h
    · exact Or.inr (mem_toList.mpr (mem_sdiff.mpr ⟨mem_univ w, h⟩))
  have hdisj : ∀ w ∈ l, w ∉ J := fun w hw => (mem_sdiff.mp (mem_toList.mp hw)).2
  obtain ⟨hratio, hlpos⟩ := upperProd_le_RY G hq1 hS1 l J
  have hRl : (l.map fun i => (1 + coarseErr (Fintype.card F) (degree G i) n) /
      (1 - coarseErr (Fintype.card F) (degree G i) n)).prod = RY G (Fintype.card F) n (univ \ J) := by
    unfold RY
    rw [hl, Finset.prod_map_toList]
  rw [hRl] at hratio
  have hbounds (x : J → F) (hx : x ∈ feasLabels F G J) :
      lowerProd G (Fintype.card F) n J l ≤ extCount G J (extendLabel J x) ∧
        (extCount G J (extendLabel J x) : ℝ) ≤ upperProd G (Fintype.card F) J l := by
    have hfeas : Feasible F G J (extendLabel J x) := (mem_feasLabels G).mp hx
    exact extCount_bounds hW G hn l J _ hnd hcov hdisj hfeas
  have hfeas0 (x : J → F) (hx : x ∈ feasLabels F G J) : (0 : ℝ) < (feasLabels F G J).card := by
    exact_mod_cast card_pos.mpr ⟨x, hx⟩
  constructor
  · intro x hx
    have h1 := (hbounds x hx).1
    unfold marginalJ
    exact mul_pos (div_pos (lt_of_lt_of_le hlpos h1) hI) (hfeas0 x hx)
  · intro x hx x' hx'
    have h1 := (hbounds x hx).2
    have h2 := (hbounds x' hx').1
    have hN := hfeas0 x hx
    unfold marginalJ
    have hR0 : 0 ≤ RY G (Fintype.card F) n (univ \ J) := by
      unfold RY
      apply prod_nonneg
      intro i _
      apply div_nonneg
      · have := coarseErr_nonneg (by linarith : (0 : ℝ) < Fintype.card F) (degree G i) n
        linarith
      · linarith [hS1 i]
    have key : (extCount G J (extendLabel J x) : ℝ) ≤
        RY G (Fintype.card F) n (univ \ J) * extCount G J (extendLabel J x') :=
      h1.trans (hratio.trans (mul_le_mul_of_nonneg_left h2 hR0))
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div, mul_div_assoc', div_le_div_iff_of_pos_right hI]
    nlinarith

include hne in
/-- **(d), in particular**: the density takes values in `[R_{W∖J}⁻¹, R_{W∖J}]`. -/
theorem marginalJ_density_bounds (hW : WeilBound F) {n : ℕ} (hn : Fintype.card W ≤ n)
    (hS1 : ∀ i, coarseErr (Fintype.card F) (degree G i) n < 1) (J : Finset W)
    (x : J → F) (hx : x ∈ feasLabels F G J) :
    (RY G (Fintype.card F) n (univ \ J))⁻¹ ≤ marginalJ G J x * (feasLabels F G J).card ∧
      marginalJ G J x * (feasLabels F G J).card ≤ RY G (Fintype.card F) n (univ \ J) := by
  obtain ⟨hpos, hrat⟩ := marginalJ_density G hne hW hn hS1 J
  set N : ℝ := ((feasLabels F G J).card : ℝ) with hN
  set R := RY G (Fintype.card F) n (univ \ J) with hR
  set d : (J → F) → ℝ := fun x => marginalJ G J x * N with hd
  have hN0 : 0 < N := by rw [hN]; exact_mod_cast card_pos.mpr ⟨x, hx⟩
  -- the density has mean one under the uniform law on `feasLabels`
  have hmean : ∑ y ∈ feasLabels F G J, d y = N := by
    have h1 : ∑ y ∈ feasLabels F G J, marginalJ G J y = 1 := by
      rw [← sum_marginalJ G hne J]
      apply Finset.sum_subset (subset_univ _)
      intro y _ hy
      by_contra h
      exact hy (marginalJ_support G J y h)
    simp only [hd]
    rw [← Finset.sum_mul, h1, one_mul]
  -- `d x ≤ R d y` for all `y`, so `N d x ≤ R N`; and `d y ≤ R d x`, so `N ≤ R N d x`
  have hup : N * d x ≤ R * N := by
    calc N * d x = ∑ _y ∈ feasLabels F G J, d x := by rw [sum_const, nsmul_eq_mul]
      _ ≤ ∑ y ∈ feasLabels F G J, R * d y := Finset.sum_le_sum (fun y hy => hrat x hx y hy)
      _ = R * N := by rw [← Finset.mul_sum, hmean]
  have hlo : N ≤ R * (N * d x) := by
    calc N = ∑ y ∈ feasLabels F G J, d y := hmean.symm
      _ ≤ ∑ _y ∈ feasLabels F G J, R * d x := Finset.sum_le_sum (fun y hy => hrat y hy x hx)
      _ = R * (N * d x) := by rw [sum_const, nsmul_eq_mul]; ring
  have hdx := hpos x hx
  have hR0 : 0 < R := by
    by_contra h
    push Not at h
    have : R * (N * d x) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    linarith
  constructor
  · rw [inv_le_iff_one_le_mul₀ hR0]
    nlinarith
  · nlinarith

/-- **(d) for a perturbed law**: if `m` is a law on `Inj(G)` with `dm/dλ ∈ [c, Rc]`, the density
of its marginal `m_J` with respect to `λ_p(G[J])` takes values in `[c'', R R_{W∖J} c'']`: any two
values have ratio at most `R R_{W∖J}`. Here `m_J(x) = ∑_{y|_J = x} m(y)`. -/
theorem marginal_of_density_ratio (hW : WeilBound F) {n : ℕ} (hn : Fintype.card W ≤ n)
    (hS1 : ∀ i, coarseErr (Fintype.card F) (degree G i) n < 1) (J : Finset W)
    (m : FiniteLaw (W → F)) {c R : ℝ}
    (hc : 0 < c)
    (hm : ∀ z ∈ injLabellings F G, c * (graphLaw G hne).weight z ≤ m.weight z ∧
      m.weight z ≤ R * c * (graphLaw G hne).weight z)
    (x : J → F) (hx : x ∈ feasLabels F G J) (x' : J → F) (hx' : x' ∈ feasLabels F G J) :
    ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x), m.weight y ≤
      R * RY G (Fintype.card F) n (univ \ J) *
        ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x'), m.weight y := by
  set c₀ : ℝ := 1 / ((injLabellings F G).card : ℝ) with hc₀
  have hI : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hc₀0 : 0 < c₀ := by rw [hc₀]; positivity
  have hlam1 (z : W → F) (hz : z ∈ injLabellings F G) : (graphLaw G hne).weight z = c₀ := by
    unfold graphLaw
    simp only []
    rw [ite_eq_left hz]
  have hcount (x : J → F) : ((injLabellings F G).filter (fun y => (fun a : J => y a) = x)).card =
      extCount G J (extendLabel J x) := by
    unfold extCount
    congr 1
    ext y
    simp only [mem_filter]
    constructor
    · rintro ⟨hy, rfl⟩
      exact ⟨hy, fun a ha => by unfold extendLabel; rw [dite_eq_left ha]⟩
    · rintro ⟨hy, h⟩
      refine ⟨hy, funext fun a => ?_⟩
      rw [h a a.2]
      unfold extendLabel
      rw [dite_eq_left a.2]
  have hupper (x : J → F) : ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x),
      m.weight y ≤ R * c * c₀ * extCount G J (extendLabel J x) := by
    calc ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x), m.weight y
        ≤ ∑ _y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x), R * c * c₀ :=
          Finset.sum_le_sum (fun y hy => by
            have hy' := (mem_filter.mp hy).1
            have := (hm y hy').2
            rwa [hlam1 y hy'] at this)
      _ = R * c * c₀ * extCount G J (extendLabel J x) := by
          rw [sum_const, nsmul_eq_mul, hcount]
          ring
  have hlower (x : J → F) : c * c₀ * extCount G J (extendLabel J x) ≤
      ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x), m.weight y := by
    calc c * c₀ * (extCount G J (extendLabel J x) : ℝ)
        = ∑ _y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x), c * c₀ := by
          rw [sum_const, nsmul_eq_mul, hcount]
          ring
      _ ≤ _ := Finset.sum_le_sum (fun y hy => by
            have hy' := (mem_filter.mp hy).1
            have := (hm y hy').1
            rwa [hlam1 y hy'] at this)
  obtain ⟨hpos, hrat⟩ := marginalJ_density G hne hW hn hS1 J
  have hN0 : (0 : ℝ) < (feasLabels F G J).card := by exact_mod_cast card_pos.mpr ⟨x, hx⟩
  have hratC : (extCount G J (extendLabel J x) : ℝ) ≤
      RY G (Fintype.card F) n (univ \ J) * extCount G J (extendLabel J x') := by
    have h := hrat x hx x' hx'
    unfold marginalJ at h
    have h' : (extCount G J (extendLabel J x) : ℝ) * ((feasLabels F G J).card / (injLabellings F G).card) ≤
        RY G (Fintype.card F) n (univ \ J) * extCount G J (extendLabel J x') *
          ((feasLabels F G J).card / (injLabellings F G).card) := by
      have e1 : (extCount G J (extendLabel J x) : ℝ) / (injLabellings F G).card * (feasLabels F G J).card =
          (extCount G J (extendLabel J x) : ℝ) * ((feasLabels F G J).card / (injLabellings F G).card) := by
        ring
      have e2 : RY G (Fintype.card F) n (univ \ J) * ((extCount G J (extendLabel J x') : ℝ) /
          (injLabellings F G).card * (feasLabels F G J).card) =
          RY G (Fintype.card F) n (univ \ J) * extCount G J (extendLabel J x') *
            ((feasLabels F G J).card / (injLabellings F G).card) := by ring
      linarith
    exact le_of_mul_le_mul_right h' (div_pos hN0 hI)
  have hR0 : 0 ≤ R := by
    rcases id hne with ⟨z, hz⟩
    have h := hm z hz
    rw [hlam1 z hz] at h
    have h1 : c * c₀ ≤ R * c * c₀ := h.1.trans h.2
    nlinarith [mul_pos hc hc₀0]
  calc ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x), m.weight y
      ≤ R * c * c₀ * extCount G J (extendLabel J x) := hupper x
    _ ≤ R * c * c₀ * (RY G (Fintype.card F) n (univ \ J) * extCount G J (extendLabel J x')) :=
        mul_le_mul_of_nonneg_left hratC (by positivity)
    _ = R * RY G (Fintype.card F) n (univ \ J) * (c * c₀ * extCount G J (extendLabel J x')) := by
        ring
    _ ≤ R * RY G (Fintype.card F) n (univ \ J) *
          ∑ y ∈ (injLabellings F G).filter (fun y => (fun a : J => y a) = x'), m.weight y := by
        apply mul_le_mul_of_nonneg_left (hlower x')
        apply mul_nonneg hR0
        unfold RY
        apply prod_nonneg
        intro i _
        apply div_nonneg
        · have := coarseErr_nonneg (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < Fintype.card F)
            (degree G i) n
          linarith
        · linarith [hS1 i]

include hne in
/-- **(c) Deleting a vertex**: the marginal of `λ` on `W ∖ {w}` is supported on the feasible
labellings of `W ∖ {w}` (`Inj_p(G - w)`), and its density with respect to `λ_p(G - w)` takes
values in `[R_{{w}}⁻¹, R_{{w}}]`. -/
theorem marginal_delete (hW : WeilBound F) {n : ℕ} (hn : Fintype.card W ≤ n)
    (hS1 : ∀ i, coarseErr (Fintype.card F) (degree G i) n < 1) (w : W)
    (x : {a // a ∈ univ.erase w} → F) (hx : x ∈ feasLabels F G (univ.erase w)) :
    (RY G (Fintype.card F) n {w})⁻¹ ≤
        marginalJ G (univ.erase w) x * (feasLabels F G (univ.erase w)).card ∧
      marginalJ G (univ.erase w) x * (feasLabels F G (univ.erase w)).card ≤
        RY G (Fintype.card F) n {w} := by
  have h : univ \ univ.erase w = ({w} : Finset W) := by
    ext a
    simp only [mem_sdiff, mem_univ, mem_erase, true_and, not_and, mem_singleton]
    constructor
    · intro h
      by_contra hne'
      exact absurd (h hne') (by simp)
    · rintro rfl h
      exact absurd rfl h
  have := marginalJ_density_bounds G hne hW hn hS1 (univ.erase w) x hx
  rwa [h] at this

end Sarkozy.TraceMixing

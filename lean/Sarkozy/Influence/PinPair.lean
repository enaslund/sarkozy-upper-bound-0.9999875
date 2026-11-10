module

public import Sarkozy.Influence.Defs
public import Sarkozy.Influence.PairBound

/-!
# Pinned influence, VI: the fully pinned pair (`lem:mid:pinpair`)

This file covers `lem:mid:pinpair` (`13_cuts_correlations.tex`), up to the combinatorial
count. It fixes all vertices except two, `i` and `j`, at a feasible value `z` of
`y_{U \ {i,j}}`. Under the conditional graph law, `(y_i, y_j)` is then distributed by the
`0/1` kernel `pinKernel G i j z`: `(x, x')` is allowed when the completion `compl2 i j z x x'`
lies in `Inj_p(G)` (`condLaw_pair_expect`). Its maximal correlation therefore equals that of
`kernelLaw (pinKernel …)` (`maxCorr_pin_eq`).

`mem_inj_compl2` describes the allowed pairs: `x ∈ S_i`, `x' ∈ S_j`, `x ≠ x'`, and the square
constraint on the edge `ij`, if there is one.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

/-- The maximal correlation depends only on the joint law of the pair, even across different
probability spaces. -/
theorem maxCorr_congr_joint {Ω Ω' α β : Type*} [Fintype Ω] [Fintype Ω'] {μ : FiniteLaw Ω}
    {ν : FiniteLaw Ω'} {X : Ω → α} {Y : Ω → β} {X' : Ω' → α} {Y' : Ω' → β}
    (h : ∀ φ : α → β → ℝ,
      μ.expect (fun ω => φ (X ω) (Y ω)) = ν.expect (fun ω => φ (X' ω) (Y' ω))) :
    maxCorr μ X Y = maxCorr ν X' Y' := by
  unfold maxCorr
  congr 1
  ext c
  constructor
  · rintro ⟨f, g, h1, h2, h3, h4, rfl⟩
    refine ⟨f, g, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; exact (h (fun a _ => f a)).symm
    · rw [← h2]; exact (h (fun _ b => g b)).symm
    · rw [← h3]; exact (h (fun a _ => f a ^ 2)).symm
    · rw [← h4]; exact (h (fun _ b => g b ^ 2)).symm
    · rw [h (fun a b => f a * g b)]
  · rintro ⟨f, g, h1, h2, h3, h4, rfl⟩
    refine ⟨f, g, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; exact h (fun a _ => f a)
    · rw [← h2]; exact h (fun _ b => g b)
    · rw [← h3]; exact h (fun a _ => f a ^ 2)
    · rw [← h4]; exact h (fun _ b => g b ^ 2)
    · rw [h (fun a b => f a * g b)]

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ}

/-- `U \ {i, j}`. -/
def offPair (i j : U) : Finset U := Finset.univ \ {i, j}

theorem mem_offPair {i j v : U} : v ∈ offPair i j ↔ v ≠ i ∧ v ≠ j := by
  simp [offPair, not_or]

/-- The completion of `z` by `x` at `i` and `x'` at `j`. -/
def compl2 (i j : U) (z : U → ZMod p) (x x' : ZMod p) : U → ZMod p :=
  fun v => if v = i then x else if v = j then x' else z v

omit [Fintype U] in
theorem compl2_left (i j : U) (z : U → ZMod p) (x x' : ZMod p) : compl2 i j z x x' i = x := by
  simp [compl2]

omit [Fintype U] in
theorem compl2_right {i j : U} (hij : i ≠ j) (z : U → ZMod p) (x x' : ZMod p) :
    compl2 i j z x x' j = x' := by
  simp [compl2, Ne.symm hij]

omit [Fintype U] in
theorem compl2_off {i j v : U} (z : U → ZMod p) (x x' : ZMod p) (hvi : v ≠ i) (hvj : v ≠ j) :
    compl2 i j z x x' v = z v := by
  simp [compl2, hvi, hvj]

theorem eq_compl2 {i j : U} {z ω : U → ZMod p} (hω : pinEvent (offPair i j) z ω) :
    ω = compl2 i j z (ω i) (ω j) := by
  funext v
  by_cases hvi : v = i
  · subst hvi
    rw [compl2_left]
  · by_cases hvj : v = j
    · subst hvj
      rw [compl2_right (Ne.symm hvi)]
    · rw [compl2_off z _ _ hvi hvj]
      exact hω v (mem_offPair.mpr ⟨hvi, hvj⟩)

theorem pinEvent_compl2 (i j : U) (z : U → ZMod p) (x x' : ZMod p) :
    pinEvent (offPair i j) z (compl2 i j z x x') := by
  intro v hv
  obtain ⟨hvi, hvj⟩ := mem_offPair.mp hv
  exact compl2_off z x x' hvi hvj

variable [NeZero p]

open Classical in
/-- The fully pinned kernel: `1` if the completion is an injective strict-square labelling. -/
noncomputable def pinKernel (G : OrientedGraph U) (i j : U) (z : U → ZMod p)
    (x x' : ZMod p) : ℝ :=
  if compl2 i j z x x' ∈ injLabellings G p then 1 else 0

theorem pinKernel_nonneg (G : OrientedGraph U) (i j : U) (z : U → ZMod p) (x x' : ZMod p) :
    0 ≤ pinKernel G i j z x x' := by
  unfold pinKernel
  split_ifs <;> norm_num

theorem graphLaw_expect (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    (u : (U → ZMod p) → ℝ) :
    (graphLaw G p hInj).expect u =
      (∑ ω ∈ injLabellings G p, u ω) / ((injLabellings G p).card : ℝ) := by
  classical
  unfold FiniteLaw.expect
  simp only [graphLaw, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_div]
  exact Finset.sum_congr rfl (fun ω _ => by ring)

/-- The bijection between the completions of `z` and the allowed pairs. -/
theorem sum_pin_eq_kernel (G : OrientedGraph U) {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (φ : ZMod p → ZMod p → ℝ) :
    ∑ ω ∈ injLabellings G p, ind (pinEvent (offPair i j) z) ω * φ (ω i) (ω j) =
      ∑ x, ∑ x', pinKernel G i j z x x' * φ x x' := by
  classical
  have e1 : ∑ ω ∈ injLabellings G p, ind (pinEvent (offPair i j) z) ω * φ (ω i) (ω j) =
      ∑ ω ∈ (injLabellings G p).filter (pinEvent (offPair i j) z), φ (ω i) (ω j) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ω _ => ?_)
    by_cases hω : pinEvent (offPair i j) z ω
    · rw [ind_of_pos hω, one_mul, ite_eq_left hω]
    · rw [ind_of_neg hω, zero_mul, ite_eq_right hω]
  have e2 : ∑ x, ∑ x', pinKernel G i j z x x' * φ x x' =
      ∑ q ∈ (Finset.univ : Finset (ZMod p × ZMod p)).filter
        (fun q => compl2 i j z q.1 q.2 ∈ injLabellings G p), φ q.1 q.2 := by
    rw [Finset.sum_filter, ← Finset.univ_product_univ, Finset.sum_product]
    refine Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun x' _ => ?_))
    simp only [pinKernel, ite_mul, one_mul, zero_mul]
  rw [e1, e2]
  refine Finset.sum_nbij' (fun ω => (ω i, ω j)) (fun q => compl2 i j z q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro ω hω
    rw [Finset.mem_filter] at hω ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [← eq_compl2 hω.2]
    exact hω.1
  · intro q hq
    rw [Finset.mem_filter] at hq ⊢
    exact ⟨hq.2, pinEvent_compl2 i j z q.1 q.2⟩
  · intro ω hω
    rw [Finset.mem_filter] at hω
    exact (eq_compl2 hω.2).symm
  · intro q _
    simp only [compl2_left, compl2_right hij]
  · intro ω _
    rfl

/-- Under the graph law conditioned on `y_{U \ {i,j}} = z`, the pair `(y_i, y_j)` is
distributed by the pinned kernel. -/
theorem condLaw_pair_expect (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent (offPair i j) z))
    (hZ : 0 < ∑ x, ∑ x', pinKernel G i j z x x') (φ : ZMod p → ZMod p → ℝ) :
    (condLaw (graphLaw G p hInj) (pinEvent (offPair i j) z) h).expect
        (fun ω => φ (ω i) (ω j)) =
      (kernelLaw (pinKernel G i j z) (pinKernel_nonneg G i j z) hZ).expect
        (fun q => φ q.1 q.2) := by
  rw [cond_expect, kernelLaw_expect]
  unfold prob
  rw [graphLaw_expect, graphLaw_expect, sum_pin_eq_kernel G hij z φ]
  have e : ∑ ω ∈ injLabellings G p, ind (pinEvent (offPair i j) z) ω =
      ∑ x, ∑ x', pinKernel G i j z x x' := by
    have := sum_pin_eq_kernel G hij z (fun _ _ => 1)
    simp only [mul_one] at this
    exact this
  rw [e]
  have hc : ((injLabellings G p).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hInj).ne'
  rw [div_div_div_cancel_right₀ hc]

/-- The positivity of the pinned kernel's total mass follows from feasibility. -/
theorem pinKernel_mass_pos (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent (offPair i j) z)) :
    0 < ∑ x, ∑ x', pinKernel G i j z x x' := by
  unfold prob at h
  rw [graphLaw_expect] at h
  have e := sum_pin_eq_kernel G hij z (fun _ _ => 1)
  simp only [mul_one] at e
  rw [e] at h
  have hc : (0 : ℝ) < (injLabellings G p).card := by
    exact_mod_cast Finset.card_pos.mpr hInj
  exact (div_pos_iff_of_pos_right hc).mp h

/-- The fully pinned correlation is the maximal correlation of the pinned kernel law. -/
theorem maxCorr_pin_eq (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    {i j : U} (hij : i ≠ j) (z : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent (offPair i j) z)) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent (offPair i j) z) h)
        (fun ω => ω i) (fun ω => ω j) =
      maxCorr (kernelLaw (pinKernel G i j z) (pinKernel_nonneg G i j z)
        (pinKernel_mass_pos G hInj hij z h)) Prod.fst Prod.snd :=
  maxCorr_congr_joint (fun φ => condLaw_pair_expect G hInj hij z h _ φ)

end Sarkozy.Influence

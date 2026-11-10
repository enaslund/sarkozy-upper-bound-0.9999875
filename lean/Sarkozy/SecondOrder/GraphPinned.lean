module

public import Sarkozy.SecondOrder.OrderedStar
public import Sarkozy.Labellings.GraphLaw

/-!
# Graph laws are pinned half laws (`def:pinned-law`, the remark after it)

`paper/sections/15_second_order.tex`, after `def:pinned-law`: for an oriented graph `G⁺` on `U`,
the uniform law `λ_p(G⁺)` on `Inj_p(G⁺)` is a pinned half law. Its neighbourhoods `N⁰(i)` are
the neighbours of `i`, with signs `ς⁰_ij = +1` for an edge `(j, i)` and `-1` for an edge
`(i, j)`. Given `x_{-i}`, the admissible values of `x_i` are exactly `Φ_i(x_{-i})`. By
`lem:extension`, with the `n - 1` other labels excluded, one may take
`e_i = (𝔈_{d_i} + 2^{d_i}(n - 1))/p`, `𝔈_t = a_t √p + b_t`, whenever this is below one.

* `mem_pinnedPhi_iff`: `Φ_i(x_{-i})` is the set `vertexAdmissible` of `lem:graphs:sequential`;
* `update_mem_injLabellings_iff`: for `x ∈ Inj_p(G)`, `x[i ↦ z] ∈ Inj_p(G) ↔ z ∈ Φ_i(x_{-i})`;
* `graphPinned`: the pinned half law `λ_p(G⁺)`, from Weil's bound (`WeilBound`).

With `graphPinned`, `ordered_star`, `star_mean`, `wt_second_cond` and `wt_cond_first` apply to
the graph laws.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Labellings

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The neighbours of `i` in `G`. -/
def graphNbrs (G : OrientedGraph U) (i : U) : Finset U :=
  univ.filter fun j => (j, i) ∈ G.E ∨ (i, j) ∈ G.E

/-- `ς⁰_ij = +1` for an edge `(j, i)`, `-1` for an edge `(i, j)`. -/
def graphSign (G : OrientedGraph U) (i j : U) : ZMod p :=
  if (i, j) ∈ G.E then -1 else 1

omit [Fintype U] in
theorem graphSign_ne (G : OrientedGraph U) (i j : U) : graphSign (p := p) G i j ≠ 0 := by
  unfold graphSign
  split_ifs
  · exact neg_ne_zero.mpr one_ne_zero
  · exact one_ne_zero

theorem not_mem_graphNbrs (G : OrientedGraph U) (i : U) : i ∉ graphNbrs G i := by
  unfold graphNbrs
  simp only [mem_filter, mem_univ, true_and, or_self]
  exact G.loopless i

/-- `Φ_i(x_{-i})` is the admissible set `vertexAdmissible G (U ∖ {i}) x i`. -/
theorem mem_pinnedPhi_iff (G : OrientedGraph U) (i : U) (x : U → ZMod p) (z : ZMod p) :
    z ∈ pinnedPhi (graphNbrs G) (graphSign G) i x ↔
      z ∈ vertexAdmissible G (univ.erase i) x i := by
  classical
  unfold pinnedPhi vertexAdmissible graphNbrs graphSign
  simp only [mem_filter, mem_univ, true_and, mem_erase]
  constructor
  · rintro ⟨hz, h⟩
    refine ⟨hz, fun u _ hu => ?_, fun u _ hu => ?_⟩
    · have hiu : (i, u) ∉ G.E := G.oriented _ _ hu
      have := h u (Or.inl hu)
      simp only [hiu, ↓reduceIte, one_mul] at this
      exact this
    · have := h u (Or.inr hu)
      simp only [hu, ↓reduceIte] at this
      rw [show (-1 : ZMod p) * (z - x u) = x u - z by ring] at this
      exact this
  · rintro ⟨hz, hin, hout⟩
    refine ⟨hz, fun j hj => ?_⟩
    have hji : j ≠ i := by
      rintro rfl
      rcases hj with h | h <;> exact G.loopless j h
    rcases hj with h | h
    · have hiu : (i, j) ∉ G.E := G.oriented _ _ h
      simp only [hiu, ↓reduceIte, one_mul]
      exact hin j ⟨hji, trivial⟩ h
    · simp only [h, ↓reduceIte]
      rw [show (-1 : ZMod p) * (z - x j) = x j - z by ring]
      exact hout j ⟨hji, trivial⟩ h

theorem feasible_erase_of_mem {G : OrientedGraph U} {x : U → ZMod p}
    (hx : x ∈ injLabellings (ZMod p) G) (i : U) : Feasible (ZMod p) G (univ.erase i) x := by
  classical
  have h : Feasible (ZMod p) G univ x := by
    unfold injLabellings at hx
    exact (mem_filter.mp hx).2
  exact ⟨fun a _ b _ hab => h.1 a (mem_univ _) b (mem_univ _) hab,
    fun e he _ _ => h.2 e he (mem_univ _) (mem_univ _)⟩

/-- For `x ∈ Inj_p(G)`: `x[i ↦ z] ∈ Inj_p(G)` iff `z ∈ Φ_i(x_{-i})`. -/
theorem update_mem_injLabellings_iff {G : OrientedGraph U} {x : U → ZMod p}
    (hx : x ∈ injLabellings (ZMod p) G) (i : U) (z : ZMod p) :
    Function.update x i z ∈ injLabellings (ZMod p) G ↔
      z ∈ pinnedPhi (graphNbrs G) (graphSign G) i x := by
  classical
  rw [mem_pinnedPhi_iff]
  have hxe := feasible_erase_of_mem hx i
  have hupd : ∀ u, u ≠ i → Function.update x i z u = x u := fun u hu =>
    Function.update_of_ne hu z x
  constructor
  · intro h
    have hf : Feasible (ZMod p) G univ (Function.update x i z) := by
      unfold injLabellings at h
      exact (mem_filter.mp h).2
    unfold vertexAdmissible
    simp only [mem_filter, mem_univ, true_and, mem_image, mem_erase, not_exists, not_and]
    refine ⟨fun u hu hxu => ?_, fun u hu he => ?_, fun u hu he => ?_⟩
    · have := hf.1 u (mem_univ _) i (mem_univ _) (by rw [hupd u hu.1, Function.update_self, hxu])
      exact hu.1 this
    · have := hf.2 (u, i) he (mem_univ _) (mem_univ _)
      simp only [Function.update_self, hupd u hu.1] at this
      exact this
    · have := hf.2 (i, u) he (mem_univ _) (mem_univ _)
      simp only [Function.update_self, hupd u hu.1] at this
      exact this
  · intro h
    have hins := feasible_insert hxe (notMem_erase i univ) h
    rw [insert_erase (mem_univ i)] at hins
    unfold injLabellings
    exact mem_filter.mpr ⟨mem_univ _, hins⟩

theorem nbrCount_erase_self (G : OrientedGraph U) (i : U) :
    nbrCount G (univ.erase i) i = (graphNbrs G i).card := by
  classical
  unfold nbrCount graphNbrs
  congr 1
  ext j
  simp only [mem_filter, mem_erase, mem_univ, and_true, true_and]
  constructor
  · rintro ⟨_, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rintro rfl
    rcases h with h | h <;> exact G.loopless j h

/-- The count error `e_i = (𝔈_{d_i} + 2^{d_i}(n - 1))/p` of `λ_p(G⁺)`. -/
noncomputable def graphCountError (G : OrientedGraph U) (i : U) : ℝ :=
  (softError p (graphNbrs G i).card + 2 ^ (graphNbrs G i).card * ((Fintype.card U : ℝ) - 1)) / p

/-- **`λ_p(G⁺)` is a pinned half law** (`def:pinned-law`), from Weil's bound, when every count
error is below one. -/
noncomputable def graphPinned (hW : WeilBound (ZMod p)) (G : OrientedGraph U)
    (hne : (injLabellings (ZMod p) G).Nonempty) (he : ∀ i, graphCountError (p := p) G i < 1) :
    PinnedHalfLaw p U where
  N := graphNbrs G
  not_mem_N := not_mem_graphNbrs G
  sign := graphSign G
  sign_ne := graphSign_ne G
  e := graphCountError G
  e_nonneg := fun i => by
    unfold graphCountError
    have hn : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast Fintype.card_pos_iff.mpr ⟨i⟩
    have := softError_nonneg (p : ℝ) (graphNbrs G i).card
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    apply div_nonneg _ hp0.le
    have : (0 : ℝ) ≤ 2 ^ (graphNbrs G i).card * ((Fintype.card U : ℝ) - 1) :=
      mul_nonneg (by positivity) (by linarith)
    linarith
  e_lt := he
  μ := (graphLaw G hne).weight
  μ_nonneg := (graphLaw G hne).nonneg
  μ_sum := (graphLaw G hne).total
  μ_inj := fun x hx => by
    classical
    have hmem : x ∈ injLabellings (ZMod p) G := by
      by_contra h
      simp only [graphLaw, h, ↓reduceIte, lt_self_iff_false] at hx
    have hf : Feasible (ZMod p) G univ x := by
      unfold injLabellings at hmem
      exact (mem_filter.mp hmem).2
    exact fun a b hab => hf.1 a (mem_univ _) b (mem_univ _) hab
  cond := fun i x hx z => by
    classical
    have hmem : x ∈ injLabellings (ZMod p) G := by
      by_contra h
      simp only [graphLaw, h, ↓reduceIte, lt_self_iff_false] at hx
    have hw : ∀ w, (graphLaw G hne).weight (Function.update x i w) =
        if w ∈ pinnedPhi (graphNbrs G) (graphSign G) i x then
          1 / ((injLabellings (ZMod p) G).card : ℝ) else 0 := by
      intro w
      simp only [graphLaw]
      by_cases hwΦ : w ∈ pinnedPhi (graphNbrs G) (graphSign G) i x
      · have := (update_mem_injLabellings_iff hmem i w).mpr hwΦ
        simp only [this, hwΦ, ↓reduceIte]
      · have : Function.update x i w ∉ injLabellings (ZMod p) G :=
          fun h => hwΦ ((update_mem_injLabellings_iff hmem i w).mp h)
        simp only [this, hwΦ, ↓reduceIte]
    simp_rw [hw]
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    by_cases hzΦ : z ∈ pinnedPhi (graphNbrs G) (graphSign G) i x
    · simp only [hzΦ, ↓reduceIte]; ring
    · simp only [hzΦ, ↓reduceIte, zero_mul]
  count := fun i x hx => by
    classical
    have hmem : x ∈ injLabellings (ZMod p) G := by
      by_contra h
      simp only [graphLaw, h, ↓reduceIte, lt_self_iff_false] at hx
    have hxe := feasible_erase_of_mem hmem i
    obtain ⟨-, hlow⟩ := card_vertexAdmissible hW G hxe i
    rw [nbrCount_erase_self, card_erase_of_mem (mem_univ i), card_univ, ZMod.card] at hlow
    have hΦ : (pinnedPhi (graphNbrs G) (graphSign G) i x).card =
        (vertexAdmissible G (univ.erase i) x i).card := by
      congr 1
      ext z
      exact mem_pinnedPhi_iff G i x z
    rw [hΦ]
    have hn : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨i⟩
    rw [Nat.cast_sub hn, Nat.cast_one] at hlow
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
    have h2 : (0 : ℝ) < 2 ^ (graphNbrs G i).card := by positivity
    unfold graphCountError
    rw [div_le_iff₀ h2]
    have : (1 - (softError p (graphNbrs G i).card + 2 ^ (graphNbrs G i).card *
        ((Fintype.card U : ℝ) - 1)) / p) * p = p - softError p (graphNbrs G i).card -
          2 ^ (graphNbrs G i).card * ((Fintype.card U : ℝ) - 1) := by
      field_simp
      ring
    rw [this]
    linarith

end Sarkozy.SecondOrder

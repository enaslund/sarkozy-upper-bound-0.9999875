module

public import Sarkozy.SpectralOne.Marginal

@[expose] public section

/-!
# Non-vacuity of the isolated-vertex bound

The hypotheses of `norm_tJ_le_isolated` (`lem:spec2:paley-one`, realized) hold together: for
`ν = u_cons` itself the law of `x_J` is `u_cons` (`margJ_refLaw`), so the density hypothesis holds
with `R = 1`, and the theorem gives the isolated-vertex average
`|E_{u_cons} S_J| ≤ (|J'| + 1)/(p − |J'|)` (`norm_tJ_refLaw_le`). For the cut laws the hypotheses
are discharged outright (`tJ_nuA_le`, `hzeta_cut_paper`).

New material for this paper.
-/

namespace Sarkozy.SpectralOne

attribute [local instance] feasibleDec

open Finset Sarkozy.SpectralC Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

lemma restr_of_mem_cfgs {J : Finset U} {y : U → ZMod p} (hy : y ∈ cfgs J) : restr J y = y :=
  (restr_eq_iff hy).mpr fun _ _ => rfl

/-- **The law of `x_J` under `u_cons` is `u_cons`.** -/
theorem margJ_refLaw (G : OrientedGraph U) (J : Finset U) (y : U → ZMod p) :
    margJ (refLaw G J) J y = refLaw G J y := by
  unfold margJ
  by_cases hy : y ∈ cfgs (p := p) J
  · rw [sum_eq_single_of_mem (s := univ.filter fun x => restr J x = y) (f := refLaw G J) y
      (by simp only [mem_filter, mem_univ, true_and]; exact restr_of_mem_cfgs hy)]
    intro x hx hxy
    have hrx : restr J x = y := (mem_filter.mp hx).2
    unfold refLaw
    split_ifs with hxF
    · exact absurd ((restr_of_mem_cfgs (mem_filter.mp hxF).1).symm.trans hrx) hxy
    · rfl
  · have h0 : refLaw (p := p) G J y = 0 := by
      unfold refLaw
      split_ifs with hyF
      · exact absurd (mem_filter.mp hyF).1 hy
      · rfl
    rw [h0]
    refine sum_eq_zero fun x hx => ?_
    exact absurd ((mem_filter.mp hx).2 ▸ restr_mem_cfgs J x) hy

/-- **Non-vacuity of `norm_tJ_le_isolated`**: its hypotheses hold for `ν = u_cons`, `R = 1`. -/
theorem norm_tJ_refLaw_le (hp2 : p ≠ 2) (G : OrientedGraph U) {J : Finset U} {j : U}
    (hj : j ∉ J) (hiso : ∀ i ∈ J, (i, j) ∉ G.E ∧ (j, i) ∉ G.E)
    (hF : (feasCfgs (p := p) G (insert j J)).Nonempty) :
    ‖SpectralD.PaleyB.tJ (refLaw (p := p) G (insert j J)) (insert j J)‖ ≤
      ((J.card : ℝ) + 1) / ((p : ℝ) - J.card) := by
  have h := norm_tJ_le_isolated hp2 G (refLaw (p := p) G (insert j J)) hj hiso hF le_rfl
    (fun y => by rw [margJ_refLaw, inv_one, one_mul]; exact ⟨le_rfl, le_rfl⟩)
  simpa using h

end Sarkozy.SpectralOne

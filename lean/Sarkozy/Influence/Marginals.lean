module

public import Sarkozy.Influence.PinPairBound
public import Sarkozy.Energy




@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

variable {U : Type*} [Fintype U] [DecidableEq U] {p : ℕ} [NeZero p]

theorem translate_mem_injLabellings (G : OrientedGraph U) {ω : U → ZMod p}
    (hω : ω ∈ injLabellings G p) (c : ZMod p) : (fun u => ω u + c) ∈ injLabellings G p := by
  obtain ⟨hinj, hsq⟩ := mem_injLabellings.mp hω
  refine mem_injLabellings.mpr ⟨fun u u' h => hinj (add_right_cancel h), fun u v he => ?_⟩
  have e : ω v + c - (ω u + c) = ω v - ω u := by ring
  simp only [e]
  exact hsq u v he

/-- **Uniform marginals**: every label of the graph law is uniform on `ZMod p`. -/
theorem graphLaw_hasUniformMarginals (G : OrientedGraph U)
    (hInj : (injLabellings G p).Nonempty) : HasUniformMarginals (graphLaw G p hInj) := by
  intro v f
  rw [graphLaw_expect, FiniteLaw.expect_uniform, ZMod.card]
  have hc : ((injLabellings G p).card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_pos.mpr hInj).ne'
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne p
  -- translation invariance of the sum over `Inj_p(G)`
  have hinv : ∀ c : ZMod p, ∑ ω ∈ injLabellings G p, f (ω v + c) =
      ∑ ω ∈ injLabellings G p, f (ω v) := by
    intro c
    refine Finset.sum_nbij' (fun ω => fun u => ω u + c) (fun ω => fun u => ω u - c)
      (fun ω hω => translate_mem_injLabellings G hω c)
      (fun ω hω => by
        have := translate_mem_injLabellings G hω (-c)
        simpa only [← sub_eq_add_neg] using this)
      (fun ω _ => by funext u; ring) (fun ω _ => by funext u; ring) (fun ω _ => rfl)
  -- average over all translations
  have hsum : (p : ℝ) * ∑ ω ∈ injLabellings G p, f (ω v) =
      ((injLabellings G p).card : ℝ) * ∑ x, f x := by
    calc (p : ℝ) * ∑ ω ∈ injLabellings G p, f (ω v)
        = ∑ c : ZMod p, ∑ ω ∈ injLabellings G p, f (ω v + c) := by
          rw [Finset.sum_congr rfl (fun c _ => hinv c), Finset.sum_const, Finset.card_univ,
            ZMod.card, nsmul_eq_mul]
      _ = ∑ ω ∈ injLabellings G p, ∑ c : ZMod p, f (ω v + c) := Finset.sum_comm
      _ = ∑ ω ∈ injLabellings G p, ∑ x, f x := by
          refine Finset.sum_congr rfl (fun ω _ => ?_)
          exact Fintype.sum_equiv (Equiv.addLeft (ω v)) _ _ (fun c => rfl)
      _ = ((injLabellings G p).card : ℝ) * ∑ x, f x := by
          rw [Finset.sum_const, nsmul_eq_mul]
  field_simp
  linarith

/-- `lem:mid:pinpair` with the count errors of `def:mid:influence` (i) for `(G, F)`,
`F = U \ S`. -/
theorem pinpair_of_countErrors (G : OrientedGraph U) (hInj : (injLabellings G p).Nonempty)
    (hsq : SquareShiftBound p) (S : Finset U) {w wconn : ℝ}
    (hce : CountErrors G p (free S) w wconn) {i j : U} (hi : i ∈ free S) (hj : j ∈ free S)
    (hij : i ≠ j) (z : U → ZMod p)
    (h : 0 < prob (graphLaw G p hInj) (pinEvent (offPair i j) z)) :
    maxCorr (condLaw (graphLaw G p hInj) (pinEvent (offPair i j) z) h)
      (fun ω => ω i) (fun ω => ω j) ≤ influence G p w i j :=
  pinpair G hInj hsq (free S) hce.w_nonneg hce.w_lt_one hce.first hi hj hij z h

end Sarkozy.Influence

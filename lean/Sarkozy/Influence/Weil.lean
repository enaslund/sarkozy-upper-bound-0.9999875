module

public import Sarkozy.Influence.Defs
public import Sarkozy.Labellings.Extension




@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy

variable {p : ℕ} [Fact p.Prime]

/-- `ε (x - a) ∈ Q_p ⟺ χ(x - a) = χ(ε)` for `x ≠ a` and `ε = ±1`. -/
theorem isNzSq_mul_iff {ε d : ZMod p} (hε : ε = 1 ∨ ε = -1) (hd : d ≠ 0) :
    IsNzSq (ε * d) ↔ quadraticChar (ZMod p) d = quadraticChar (ZMod p) ε := by
  have hε0 : ε ≠ 0 := by
    rcases hε with h | h <;> rw [h]
    · exact one_ne_zero
    · exact neg_ne_zero.mpr one_ne_zero
  have hεd : ε * d ≠ 0 := mul_ne_zero hε0 hd
  unfold IsNzSq
  rw [and_iff_right hεd, ← quadraticChar_one_iff_isSquare hεd, map_mul]
  rcases quadraticChar_dichotomy hε0 with h1 | h1 <;>
    rcases quadraticChar_dichotomy hd with h2 | h2 <;> rw [h1, h2] <;> decide

/-- The count `N` of `eq:mid:standing` is the size of the admissible set of
`lem:extension` with the signs `χ(ε_m)`. -/
theorem standingCount_eq_admissible {t : ℕ} (a sg : Fin t → ZMod p)
    (hsg : ∀ m, sg m = 1 ∨ sg m = -1) (E' : Finset (ZMod p)) (haE : ∀ m, a m ∈ E') :
    standingCount a sg E' =
      (Labellings.admissible a (fun m => quadraticChar (ZMod p) (sg m)) E').card := by
  classical
  unfold standingCount Labellings.admissible
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hxE, hcon⟩
    refine ⟨hxE, fun m => ?_⟩
    have hd : x - a m ≠ 0 := sub_ne_zero.mpr (fun h => hxE (h ▸ haE m))
    exact (isNzSq_mul_iff (hsg m) hd).mp (hcon m)
  · rintro ⟨hxE, hcon⟩
    refine ⟨hxE, fun m => ?_⟩
    have hd : x - a m ≠ 0 := sub_ne_zero.mpr (fun h => hxE (h ▸ haE m))
    exact (isNzSq_mul_iff (hsg m) hd).mpr (hcon m)

/-- **Count errors from Weil's bound.** Assume `WeilBound (ZMod p)` and that `w`
bounds the graded errors `e^-_t(M) = (a_t √p + b_t + 2^t M)/p` for every `t ≤ T`. Then `w`
satisfies the count-error inequality of `eq:mid:standing` with at most `T` roots and at most
`M` excluded values. -/
theorem standingBound_of_weil (hW : Labellings.WeilBound (ZMod p)) {T M : ℕ}
    {w : ℝ}
    (hw : ∀ t ≤ T, (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t +
      2 ^ t * (M : ℝ)) / p ≤ w) :
    StandingBound p T M w := by
  classical
  intro t a sg E' ha hsg haE ht hE'
  set s : Fin t → ℤ := fun m => quadraticChar (ZMod p) (sg m) with hs_def
  have hs : ∀ m, s m = 1 ∨ s m = -1 := by
    intro m
    have hε0 : sg m ≠ 0 := by
      rcases hsg m with h | h <;> rw [h]
      · exact one_ne_zero
      · exact neg_ne_zero.mpr one_ne_zero
    exact quadraticChar_dichotomy hε0
  have hb := (Labellings.extension_bounds hW a ha s hs E' haE).2
  rw [Fintype.card_fin, ZMod.card] at hb
  rw [standingCount_eq_admissible a sg hsg E' haE]
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hwt := hw t ht
  have hM : (E'.card : ℝ) ≤ M := by exact_mod_cast hE'
  have h2t : (0 : ℝ) < 2 ^ t := by positivity
  rw [le_div_iff₀ hp]
  rw [div_le_iff₀ hp] at hwt
  have : (2 : ℝ) ^ t * E'.card ≤ 2 ^ t * M := mul_le_mul_of_nonneg_left hM h2t.le
  nlinarith

/-- **`CountErrors` from Weil's bound**: for `WeilBound (ZMod p)` and numbers
`0 ≤ w, w^{conn} < 1` bounding the graded errors (`e^-_t(n)` for `t ≤ Δ_F`, and `e^-_t(2n)`
for `t ≤ Δ_F + 1`, `n = |U|`), the count-error conditions `eq:mid:standing` hold. -/
theorem countErrors_of_weil {U : Type*} [Fintype U] (G : OrientedGraph U)
    (hW : Labellings.WeilBound (ZMod p)) (F : Finset U) {w wconn : ℝ} (hw0 : 0 ≤ w)
    (hw1 : w < 1) (hc0 : 0 ≤ wconn) (hc1 : wconn < 1)
    (hw : ∀ t ≤ maxDeg G F, (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t +
      2 ^ t * (Fintype.card U : ℝ)) / p ≤ w)
    (hwc : ∀ t ≤ maxDeg G F + 1, (Labellings.gradedA t * √(p : ℝ) + Labellings.gradedB t +
      2 ^ t * ((2 * Fintype.card U : ℕ) : ℝ)) / p ≤ wconn) :
    CountErrors G p F w wconn :=
  ⟨hw0, hw1, hc0, hc1, standingBound_of_weil hW hw, standingBound_of_weil hW hwc⟩

end Sarkozy.Influence

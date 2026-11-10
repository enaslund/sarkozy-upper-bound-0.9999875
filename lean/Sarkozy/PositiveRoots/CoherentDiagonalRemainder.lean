module

public import Sarkozy.PositiveRoots.CoherentDiagonalCross
public import Sarkozy.PositiveRoots.CoherentSoftBound
public import Sarkozy.PartV.KernelErrorSupport

/-! One-sided traces and deleted evaluation points on the actual induced half. -/

@[expose] public section

namespace Sarkozy.PositiveRoots.CoherentFrame

open Finset Sarkozy.L20Cap Sarkozy.Cuts Sarkozy.Recentering Sarkozy.Labellings
open Sarkozy.PartV.CoherentDictionary

variable {p : ℕ} [Fact p.Prime]

noncomputable def chamberAuxiliary (x y : CoreT (ZMod p) × PairT (ZMod p)) : ℝ :=
  (∑ z, dictionaryEval dictionary39 (fun S => evaluation S
    (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) z) ^ 2) / p

noncomputable def chamberTwoSided (x y : CoreT (ZMod p) × PairT (ZMod p)) : ℝ :=
  dictionaryEval (twoSidedRaw false) (fun S => chamberTrace S x y)

noncomputable def chamberDiagonalRemainder (x y : CoreT (ZMod p) × PairT (ZMod p)) : ℝ :=
  chamberAuxiliary x y - 13 / 75 - chamberTwoSided x y

theorem half_avoid_injective (x : CoreT (ZMod p) × PairT (ZMod p)) (hx : Avoid x) :
    Function.Injective (emb x.1.val x.2.val) := by
  intro i j hij
  exact ((mem_injLabellings_iff_feasible G6 (labels x)).mp
    ((labels_mem x).mpr hx)).1 i (mem_univ _) j (mem_univ _) hij

theorem chamber_config_injOn (x y : CoreT (ZMod p) × PairT (ZMod p))
    (hx : Avoid x) (hy : Avoid y) :
    Set.InjOn (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val))
      {v | cutSide false v = true} ∧
    Set.InjOn (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val))
      {v | cutSide false v = false} := by
  have hx' : Function.Injective (chamberLabelsEquiv true (emb x.1.val x.2.val)) := by
    intro u v h
    exact (chamberEquiv true).symm.injective (half_avoid_injective x hx h)
  have hy' : Function.Injective (chamberLabelsEquiv false (emb y.1.val y.2.val)) := by
    intro u v h
    exact (chamberEquiv false).symm.injective (half_avoid_injective y hy h)
  exact ⟨joinHalves_injOn_left false _ _ hx', joinHalves_injOn_right false _ _ hy'⟩

theorem chamber_diagonal_remainder_pointwise (hp2 : p ≠ 2)
    (x y : CoreT (ZMod p) × PairT (ZMod p)) (hx : Avoid x) (hy : Avoid y) :
    |chamberDiagonalRemainder x y| ≤ ((1936 / 75 : ℝ) + 8 / 45) * (p : ℝ)⁻¹ := by
  obtain ⟨hL, hR⟩ := chamber_config_injOn x y hx hy
  have he := auxiliary_diagonal_split_error hp2 false
    (chamberConfiguration (emb x.1.val x.2.val) (emb y.1.val y.2.val)) hL hR
  change |chamberAuxiliary x y - (13 / 75 + -(8 / 45 : ℝ) / p + chamberTwoSided x y)| ≤
    (1936 / 75 : ℝ) / p at he
  calc
    _ = |(chamberAuxiliary x y - (13 / 75 + -(8 / 45 : ℝ) / p + chamberTwoSided x y)) -
        (8 / 45 : ℝ) / p| := by unfold chamberDiagonalRemainder; congr 1; ring
    _ ≤ |chamberAuxiliary x y - (13 / 75 + -(8 / 45 : ℝ) / p + chamberTwoSided x y)| +
        |(8 / 45 : ℝ) / p| := by
      simpa only [sub_eq_add_neg, abs_neg] using abs_add_le
        (chamberAuxiliary x y - (13 / 75 + -(8 / 45 : ℝ) / p + chamberTwoSided x y))
        (-((8 / 45 : ℝ) / p))
    _ ≤ (1936 / 75 : ℝ) / p + (8 / 45 : ℝ) / p := by
      rw [abs_of_nonneg (by positivity : 0 ≤ (8 / 45 : ℝ) / p)]
      exact add_le_add he le_rfl
    _ = _ := by ring

theorem halfLaw_nonzero_avoid [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (hp6 : 6 ≤ p) (x : CoreT (ZMod p) × PairT (ZMod p))
    (hx : (halfLaw (by rwa [ZMod.card])).weight x ≠ 0) : Avoid x := by
  by_contra hn
  rw [halfLaw_weight, ite_eq_right hn] at hx
  exact hx rfl

theorem chamber_diagonal_remainder_bound (hp3 : p % 4 = 3) (hp6 : 6 ≤ p)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {M : ℝ}
    (hM : ∀ f : CoreT (ZMod p) × PairT (ZMod p) → ℝ,
      |kernelForm (halfLaw (by rwa [ZMod.card])) (halfLaw (by rwa [ZMod.card])) Ksoft f f| ≤
        M * nrm (halfLaw (by rwa [ZMod.card])) f ^ 2)
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw (by rwa [ZMod.card])) (halfLaw (by rwa [ZMod.card]))
      (fun x y => Ksoft x y * chamberDiagonalRemainder x y) f f| ≤
      (((1936 / 75 : ℝ) + 8 / 45) * (p : ℝ)⁻¹) * M *
        nrm (halfLaw (by rwa [ZMod.card])) f ^ 2 := by
  apply kernel_error_supported _ _ _ (Ksoft_nonneg_actual hp3) (by positivity) _ hM f
  intro x y hx hy
  exact chamber_diagonal_remainder_pointwise (by omega) x y
    (halfLaw_nonzero_avoid hp6 x hx) (halfLaw_nonzero_avoid hp6 y hy)

end Sarkozy.PositiveRoots.CoherentFrame

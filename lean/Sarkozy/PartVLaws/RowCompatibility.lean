module

public import Sarkozy.PartVLaws.RowGraphs
public import Sarkozy.JointRows.RawIndicator

/-! Cross-row compatibility and injectivity in the actual graph coordinates. -/

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.Labellings Sarkozy.JointRows

variable {p : ℕ} [Fact p.Prime]

theorem cross_sign_iff (c : RowCase) (x y : c.Index → ZMod p) :
    (∀ i j, c.crossSign i j ≠ 0 → quadraticChar (ZMod p)
      ((c.crossSign i j : ZMod p) * (y j - x i)) = 1) ↔
    (∀ i j, c.edge (0, i) (2, j) = true → quadraticChar (ZMod p) (y j - x i) = 1) ∧
    (∀ i j, c.edge (2, j) (0, i) = true → quadraticChar (ZMod p) (x i - y j) = 1) := by
  constructor
  · intro h
    constructor
    · intro i j hij
      have hs : c.crossSign i j = 1 := by simp [crossSign, hij]
      simpa only [hs, Int.cast_one, one_mul] using h i j (by rw [hs]; norm_num)
    · intro i j hij
      have ha := c.edge_asymm (2, j) (0, i) hij
      have hs : c.crossSign i j = -1 := by simp [crossSign, hij, ha]
      simpa only [hs, Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub]
        using h i j (by rw [hs]; norm_num)
  · rintro ⟨h1, h2⟩ i j hij
    unfold crossSign at hij ⊢
    split_ifs with h02 h20
    · simpa only [Int.cast_one, one_mul] using h1 i j h02
    · simpa only [Int.cast_neg, Int.cast_one, neg_one_mul, neg_sub] using h2 i j h20
    · exact False.elim (hij (by simp [h02, h20]))

theorem compatible_iff (c : RowCase) (x y : c.Index → ZMod p) :
    Coll.Compatible c.finSigns (c.labelEquiv x) (c.labelEquiv y) ↔
    (∀ i j, x i ≠ y j) ∧
    (∀ i j, c.edge (0, i) (2, j) = true → quadraticChar (ZMod p) (y j - x i) = 1) ∧
    (∀ i j, c.edge (2, j) (0, i) = true → quadraticChar (ZMod p) (x i - y j) = 1) := by
  rw [← c.cross_sign_iff x y]
  simp only [Coll.Compatible, Coll.pairSet, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hs, he⟩
    constructor
    · intro i j
      simpa only [labelEquiv, Equiv.arrowCongr_apply, Function.comp_def,
        Equiv.refl_apply, Equiv.symm_apply_apply] using hs (c.indexEquiv i) (c.indexEquiv j)
    · intro i j hij
      simpa only [finSigns, labelEquiv, Equiv.arrowCongr_apply, Function.comp_def,
        Equiv.refl_apply, Equiv.symm_apply_apply] using
        he (c.indexEquiv i, c.indexEquiv j) (by simpa only [finSigns,
          Equiv.symm_apply_apply] using hij)
  · rintro ⟨hs, he⟩
    exact ⟨fun i j => hs _ _, fun e h => he _ _ h⟩

omit [Fact p.Prime] in
def pack (c : RowCase) (b x y : c.Index → ZMod p) (v : Fin 3 × c.Index) : ZMod p :=
  ![x, b, y] v.1 v.2

omit [Fact p.Prime] in
theorem pack_injective (c : RowCase) (b x y : c.Index → ZMod p)
    (hb : Function.Injective b) (hx : Function.Injective x) (hy : Function.Injective y)
    (hxb : ∀ i j, x i ≠ b j) (hyb : ∀ i j, y i ≠ b j) (hxy : ∀ i j, x i ≠ y j) :
    Function.Injective (c.pack b x y) := by
  rintro ⟨a, i⟩ ⟨d, j⟩ h
  fin_cases a <;> fin_cases d <;> dsimp [pack] at h ⊢
  · exact congrArg (Prod.mk 0) (hx h)
  · exact False.elim (hxb _ _ h)
  · exact False.elim (hxy _ _ h)
  · exact False.elim (hxb _ _ h.symm)
  · exact congrArg (Prod.mk 1) (hb h)
  · exact False.elim (hyb _ _ h.symm)
  · exact False.elim (hxy _ _ h.symm)
  · exact False.elim (hyb _ _ h)
  · exact congrArg (Prod.mk 2) (hy h)

end Sarkozy.PartVLaws.FieldGraphs.RowCase

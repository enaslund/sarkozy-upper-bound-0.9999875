module

public import Sarkozy.Moments.Mixed

/-!
# Tensorization of mixed Lp bounds

An independent product of two slot laws has the product of their mixed-norm
constants, at the same exponent. Fubini identifies the nested marginal Lp norm
with the norm on the product alphabet.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy
namespace FiniteLaw

@[ext] theorem ext {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω}
    (h : ∀ x, μ.weight x = ν.weight x) : μ = ν := by
  cases μ
  cases ν
  congr
  exact funext h

theorem uniform_product {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y] :
    (uniform X).product (uniform Y) = uniform (X × Y) := by
  ext xy
  simp only [product, uniform, Fintype.card_prod, Nat.cast_mul, mul_inv_rev]
  ring

theorem lpNorm_product {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteLaw X) (ν : FiniteLaw Y) {p : ℝ} (hp : p ≠ 0) (f : X × Y → ℝ) :
    μ.lpNorm p (fun x => ν.lpNorm p (fun y => f (x, y))) = (μ.product ν).lpNorm p f := by
  unfold lpNorm
  congr 1
  change μ.expect (fun x => |ν.lpNorm p (fun y => f (x, y))| ^ p) = _
  simp only [abs_of_nonneg (ν.lpNorm_nonneg _ _), ν.lpNorm_rpow hp]
  exact (expect_product μ ν (fun xy => |f xy| ^ p)).symm

noncomputable def slotProduct {V X Y : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteLaw (V → X)) (ν : FiniteLaw (V → Y)) : FiniteLaw (V → X × Y) :=
  (μ.product ν).map (fun zw v => (zw.1 v, zw.2 v))

theorem expect_slotProduct {V X Y : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (μ : FiniteLaw (V → X)) (ν : FiniteLaw (V → Y)) (f : (V → X × Y) → ℝ) :
    (μ.slotProduct ν).expect f = μ.expect (fun z => ν.expect (fun w => f (fun v => (z v, w v)))) := by
  rw [slotProduct, expect_map, expect_product]
  rfl

end FiniteLaw

theorem MixedLpBound.slotProduct {V X Y : Type*} [Fintype V] [DecidableEq V]
    [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y] [Nonempty X] [Nonempty Y]
    {μ : FiniteLaw (V → X)} {ν : FiniteLaw (V → Y)} {p C D : ℝ}
    (hμ : MixedLpBound μ p C) (hν : MixedLpBound ν p D) (hD : 0 ≤ D) (hp : p ≠ 0) :
    MixedLpBound (μ.slotProduct ν) p (C * D) := by
  intro f
  rw [FiniteLaw.expect_slotProduct]
  let g : V → X → ℝ := fun v x => (FiniteLaw.uniform Y).lpNorm p (fun y => f v (x, y))
  have hg (z : V → X) : 0 ≤ ∏ v, g v (z v) :=
    Finset.prod_nonneg (fun _ _ => (FiniteLaw.uniform Y).lpNorm_nonneg _ _)
  calc
    |μ.expect (fun z => ν.expect (fun w => ∏ v, f v (z v, w v)))| ≤
        μ.expect (fun z => |ν.expect (fun w => ∏ v, f v (z v, w v))|) := μ.abs_expect_le _
    _ ≤ μ.expect (fun z => D * ∏ v, g v (z v)) :=
      μ.expect_mono (fun z => hν (fun v y => f v (z v, y)))
    _ = D * μ.expect (fun z => ∏ v, g v (z v)) := μ.expect_const_mul _ _
    _ ≤ D * (C * ∏ v, (FiniteLaw.uniform X).lpNorm p (g v)) := by
      apply mul_le_mul_of_nonneg_left _ hD
      simpa only [abs_of_nonneg (μ.expect_nonneg hg)] using hμ g
    _ = (C * D) * ∏ v, (FiniteLaw.uniform (X × Y)).lpNorm p (f v) := by
      simp only [g, FiniteLaw.lpNorm_product _ _ hp, FiniteLaw.uniform_product]
      ring

end Sarkozy

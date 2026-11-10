module

public import Sarkozy.SpectralD.RootOneChecks
public import Sarkozy.SpectralD.MatrixCertificate

/-!
# Integer certificates for the class-one finite spectral tests

Multiplying the test matrix by 2000 clears the denominators. The three
character values are -1, 0, and 1. LL20 uses weight eight on its middle
twelve vertices for the nonzero characters; every other weight is one.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset Sarkozy.SpectralC

def oneTestMatrix (c : ReflectionCut Slot) (H : c.Half → c.Half → ℤ)
    (b t ε : ℤ) (i j : c.Half) : ℤ :=
  (if i = j then b else 0) + ε * t * crossOne c i j +
    2000 * ε ^ 2 * (∑ k, crossOne c k i * crossOne c k j) - 2000 * H i j

def oneChar (e : Fin 3) : ℤ := (e.val : ℤ) - 1

noncomputable def LL20_oneTest (e : Fin 3) : LL20.cut.Half → LL20.cut.Half → ℤ :=
  oneTestMatrix LL20.cut (fun i j => oneEntry LL20_HplusOneTable (slotCode i.1) (slotCode j.1))
    24919727 223000 (oneChar e)

noncomputable def LL22_oneTest (e : Fin 3) : LL22.cut.Half → LL22.cut.Half → ℤ :=
  oneTestMatrix LL22.cut
    (fun i j => oneEntry LL22_HplusOneTable (slotCode i.1 / 2) (slotCode j.1 / 2))
    3893612 88000 (oneChar e)

def LL20_oneWeight (e : Fin 3) (i : LL20.cut.Half) : ℤ :=
  if oneChar e ≠ 0 ∧ 12 ≤ slotCode i.1 ∧ slotCode i.1 < 24 then 8 else 1

set_option maxHeartbeats 0
set_option maxRecDepth 1000000

theorem LL20_oneTest_symm : ∀ (e : Fin 3) (i j : LL20.cut.Half),
    LL20_oneTest e i j = LL20_oneTest e j i := by decide +kernel

theorem LL22_oneTest_symm : ∀ (e : Fin 3) (i j : LL22.cut.Half),
    LL22_oneTest e i j = LL22_oneTest e j i := by decide +kernel

theorem LL20_oneTest_rows : ∀ (e : Fin 3) (i : LL20.cut.Half),
    ∑ j, |(if i = j then (2 : ℤ) ^ 40 else 0) -
      LL20_oneWeight e i * LL20_oneTest e i j * LL20_oneWeight e j| ≤ 2 ^ 40 := by
  decide +kernel

theorem LL22_oneTest_rows : ∀ (e : Fin 3) (i : LL22.cut.Half),
    ∑ j, |(if i = j then (2 : ℤ) ^ 40 else 0) - LL22_oneTest e i j| ≤ 2 ^ 40 := by
  decide +kernel

theorem LL20_oneTest_nonneg (e : Fin 3) (x : LL20.cut.Half → ℂ) :
    0 ≤ (qform (fun i j => (LL20_oneTest e i j : ℂ)) x).re := by
  apply qform_nonneg_of_integer_rows _ (LL20_oneTest_symm e) (LL20_oneWeight e) _
    (2 ^ 40) (LL20_oneTest_rows e) x
  intro i
  unfold LL20_oneWeight
  split_ifs <;> norm_num

theorem LL22_oneTest_nonneg (e : Fin 3) (x : LL22.cut.Half → ℂ) :
    0 ≤ (qform (fun i j => (LL22_oneTest e i j : ℂ)) x).re := by
  apply qform_nonneg_of_integer_rows _ (LL22_oneTest_symm e) (fun _ => 1)
    (fun _ => by norm_num) (2 ^ 40) _ x
  simpa only [one_mul, mul_one] using LL22_oneTest_rows e

end Sarkozy.SpectralD.Root

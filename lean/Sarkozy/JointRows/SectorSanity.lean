module

public import Sarkozy.JointRows.SectorGate

/-!
# Non-vacuity of the sector reduction

* `cxStruct_I`: multiplication by `i` on `ℂ`, a two-dimensional real inner product space, is a
  complex structure compatible with the inner product (`J* = -J`, `J² = -I`), so `CxStruct` is
  satisfiable.
* `toy_qMat_lower`: `Sector.qMat_lower` applies with `ℋ = ℂ`, `J = i·`, one singleton and one
  set coordinate, `𝒵 = 0`, `𝒜 = 0` and `k = 1` (the sector block is the identity).
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows.SectorSanity

open Sarkozy.JointRows.Sector

/-- **Multiplication by `i` is a complex structure on `ℂ`** (as a real inner product space). -/
theorem cxStruct_I : CxStruct (H := ℂ) (fun z => Complex.I * z) := by
  constructor
  · intro h h'
    simp only [Complex.inner, map_mul, Complex.conj_I, Complex.mul_re, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im]
    ring
  · intro h
    rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]

/-- **`Sector.qMat_lower` applies to a toy instance.** -/
theorem toy_qMat_lower (y : PiLp 2 (fun _ : Unit ⊕ Unit => ℂ)) :
    -1 * ‖y‖ ^ 2 ≤ qMat (0 : Matrix Unit Unit ℝ) (0 : Matrix Unit Unit ℝ)
      (fun z => Complex.I * z) y := by
  refine qMat_lower cxStruct_I 0 0 ?_ y
  have h0 : RowsA.cplx (0 : Matrix Unit Unit ℝ) = 0 := by
    ext i j; simp [RowsA.cplx]
  rw [h0, neg_zero, smul_zero, add_zero, conjTranspose_zero]
  have he : fromBlocks (((1 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) 0 0
      (((1 : ℝ) : ℂ) • (1 : Matrix Unit Unit ℂ)) = (1 : Matrix (Unit ⊕ Unit) (Unit ⊕ Unit) ℂ) := by
    rw [Complex.ofReal_one, one_smul, fromBlocks_one]
  rw [he]
  exact PosSemidef.one

end Sarkozy.JointRows.SectorSanity

module

public import Sarkozy.Functional.IndexAverages
public import Sarkozy.Functional.SignedIndex

@[expose] public section

/-!
# The coupled index with the actual inputs (`def:hyb:coupled`, `eq:record:expansion`)

`SignedIndex` states `def:hyb:coupled`(a)–(d) and `eq:record:expansion` for
abstract slot inputs. Here the inputs are the paper's: the index of a query is
`ω_e = (b_e, s_e) ∈ ℤ/Kℤ × ℤ/M₀ℤ`, the input at an end of the query is
`g^{I_{b_e},M₀,s_e}` (`def:record:functional`(f)), and the unindexed slots carry
`F_A`. The per-query mean identity `E_{b,s} g^{I_b,M₀,s} = F_A` is
`lem:twointerval`(iii); with it, `I_{κ,∅} = Y_κ := Q_κ(X̄, X̄)` holds for the
actual inputs, for every bilinear form `Q` and every family of transition
kernels (in particular the shift ⊗ convolution kernels `shiftConvKernel`).
-/

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.Functional

open Sarkozy.FourierArithmetic

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]

/-- The input `g^{I_b,M₀,s}` at the index `ω = (b, s)`, as a real function on
the group (it is real, `input_real`). -/
noncomputable def indexedInput (cut : ℝ) (K L M0 : ℕ) (A : Finset ℤ)
    (ω : ZMod K × ZMod M0) (y : ResidueSpace m) : ℝ :=
  (input m cut (blockInterval K L ω.1) M0 ω.2 A y).re

/-- `F_A` as a real function on the group (it is real, `wholeLift_real`). -/
noncomputable def realWholeLift (cut : ℝ) (N : ℕ) (A : Finset ℤ) (y : ResidueSpace m) : ℝ :=
  (wholeLift m cut N A y).re

/-- `lem:twointerval`(iii) for the uniform index law on `ℤ/Kℤ × ℤ/M₀ℤ`:
`E_{(b,s)} g^{I_b,M₀,s} = F_A`. -/
theorem expect_indexedInput (cut : ℝ) {K L M0 : ℕ} [NeZero K] [NeZero M0] (hL : 1 ≤ L)
    (A : Finset ℤ) (y : ResidueSpace m) :
    (FiniteLaw.uniform (ZMod K × ZMod M0)).expect (fun ω => indexedInput m cut K L M0 A ω y) =
      realWholeLift m cut (K * L) A y := by
  have h := congrArg Complex.re (average_input_blocks m cut (K := K) hL M0 A y)
  have hre : ∀ (n : ℕ) (w : ℂ), ((n : ℂ)⁻¹ * w).re = (n : ℝ)⁻¹ * w.re := by
    intro n w
    rw [show ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  simp only [hre, Complex.re_sum] at h
  rw [FiniteLaw.expect_uniform, Fintype.card_prod, ZMod.card, ZMod.card,
    Fintype.sum_prod_type]
  unfold indexedInput realWholeLift
  rw [← h, ← Finset.mul_sum]
  have hK : (K : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne K
  have hM : (M0 : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne M0
  push_cast
  field_simp

variable {E : Type*} [Fintype E] [DecidableEq E] {V : Type*} [Fintype V] [DecidableEq V]

/-- `eq:record:expansion`, second identity, for the actual inputs:
`I_{κ,∅} = Q(X̄, X̄)` with `X̄(x) = ∏_v F_A(x_v)`, for any bilinear form `Q`
on half-functions and any transition kernels `T`. -/
theorem coupledForm_empty_inputs (B : LinearMap.BilinForm ℝ ((V → ResidueSpace m) → ℝ))
    {u w : E → V} (hu : Function.Injective u) (hw : Function.Injective w)
    (cut : ℝ) {K L M0 : ℕ} [NeZero K] [NeZero M0] (hL : 1 ≤ L) (A : Finset ℤ)
    (T : ∀ _ : E, ZMod K × ZMod M0 → ZMod K × ZMod M0 → ℝ) :
    coupledForm (Ωe := fun _ => ZMod K × ZMod M0) B u w
        (fun _ => indexedInput m cut K L M0 A) (realWholeLift m cut (K * L) A) T ∅ =
      B (fullHalf (realWholeLift m cut (K * L) A)) (fullHalf (realWholeLift m cut (K * L) A)) :=
  coupledForm_empty (Ωe := fun _ => ZMod K × ZMod M0) B hu hw
    (fun _ y => expect_indexedInput m cut hL A y) T

/-- `eq:record:expansion` for the actual inputs:
`J_κ = ∑_{S ≠ ∅} (-1)^{|S|} 2^{k-|S|} I_{κ,S} + 2^k Y_κ`. -/
theorem signedForm_eq_inputs (B : LinearMap.BilinForm ℝ ((V → ResidueSpace m) → ℝ))
    {u w : E → V} (hu : Function.Injective u) (hw : Function.Injective w)
    (cut : ℝ) {K L M0 : ℕ} [NeZero K] [NeZero M0] (hL : 1 ≤ L) (A : Finset ℤ)
    (T : ∀ _ : E, ZMod K × ZMod M0 → ZMod K × ZMod M0 → ℝ) :
    signedForm (Ωe := fun _ => ZMod K × ZMod M0) B u w
        (fun _ => indexedInput m cut K L M0 A) (realWholeLift m cut (K * L) A) T =
      ∑ S ∈ univ.erase (∅ : Finset E), (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
        coupledForm (Ωe := fun _ => ZMod K × ZMod M0) B u w
          (fun _ => indexedInput m cut K L M0 A) (realWholeLift m cut (K * L) A) T S +
      2 ^ Fintype.card E *
        B (fullHalf (realWholeLift m cut (K * L) A)) (fullHalf (realWholeLift m cut (K * L) A)) :=
  signedForm_eq (Ωe := fun _ => ZMod K × ZMod M0) B hu hw
    (fun _ y => expect_indexedInput m cut hL A y) T

/-- The intervals of `𝓘_L` are of the form `c + [M]` used in `FibreScale`:
`I_b = ((b−1)L, bL] = c + [L]` with `c = (b−1)L`. -/
theorem blockInterval_eq_Icc {K : ℕ} (L : ℕ) (b : ZMod K) :
    blockInterval K L b =
      Icc (((leastPosRep b : ℤ) - 1) * L + 1) (((leastPosRep b : ℤ) - 1) * L + L) := by
  ext n
  simp only [blockInterval, mem_Ioc, mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith
  · rintro ⟨h1, h2⟩; constructor <;> nlinarith

/-- `[N] = 0 + [N]`. -/
theorem Icc_one_eq_shift (N : ℕ) : Icc (1 : ℤ) N = Icc (0 + 1) (0 + (N : ℤ)) := by
  simp

end Sarkozy.Functional

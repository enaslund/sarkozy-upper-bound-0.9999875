module

public import Sarkozy.Labellings.ConditionalCharacter
public import Sarkozy.JointRows.CollLambda
public import Sarkozy.SpectralD.TailCounts

/-! Counts for a coordinate with at most four pins in the tail range. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.PinCoordinate

open Finset Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]

theorem small_soft_error {d : ℕ} (hd : d ≤ 5) :
    softCountError (ZMod p) d ≤ 64 * Real.sqrt p := by
  have hq : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hs : (1 : ℝ) ≤ Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  interval_cases d <;> norm_num [softCountError, ZMod.card, gradedA, gradedB] <;> linarith

theorem card_lower (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (β : I → ZMod p) (hβ : Function.Injective β)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset (ZMod p)) (hM : ∀ i, β i ∈ M)
    (hI : Fintype.card I ≤ 4) (hz : M.card ≤ 12) :
    (p : ℝ) * (1 - (2 : ℝ)⁻¹ ^ 50) ≤
      2 ^ Fintype.card I * (admissible β s M).card := by
  have hlow := (extension_bounds hW β hβ s hs M hM).2
  have hq : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hsoft := Extraction.coverRow_softError_le hq M.card (Fintype.card I)
  have he := mul_le_mul_of_nonneg_left
    (SpectralD.coarseError_tail hp (by omega : Fintype.card I ≤ 24)
      (by omega : M.card ≤ 72)) (Nat.cast_nonneg p : (0 : ℝ) ≤ p)
  simp only [ZMod.card] at hlow
  unfold softError at hsoft
  linarith

theorem allowed_nonempty (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (β : I → ZMod p) (hβ : Function.Injective β)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset (ZMod p)) (hM : ∀ i, β i ∈ M)
    (hI : Fintype.card I ≤ 4) (hz : M.card ≤ 12) : (admissible β s M).Nonempty := by
  have h := card_lower hp hW β hβ s hs M hM hI hz
  have hpos : (0 : ℝ) < p * (1 - (2 : ℝ)⁻¹ ^ 50) :=
    mul_pos (by exact_mod_cast (Fact.out : p.Prime).pos) (by norm_num)
  have hc : (0 : ℝ) < (admissible β s M).card :=
    (mul_pos_iff_of_pos_left (by positivity : (0 : ℝ) < 2 ^ Fintype.card I)).mp
      (hpos.trans_le h)
  exact card_pos.mp (by exact_mod_cast hc)

theorem density_bound (hp : 2 ^ 512 ≤ p) (hW : WeilBound (ZMod p))
    (β : I → ZMod p) (hβ : Function.Injective β)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset (ZMod p)) (hM : ∀ i, β i ∈ M)
    (hI : Fintype.card I ≤ 4) (hz : M.card ≤ 12)
    (hA : (admissible β s M).Nonempty) (a : ZMod p) :
    (Coll.unifOn (admissible β s M) hA).weight a ≤
      (2 : ℝ) ^ Fintype.card I * (1 + 1 / 100000) / p := by
  have hlow := card_lower hp hW β hβ s hs M hM hI hz
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hA0 : (0 : ℝ) < (admissible β s M).card := by exact_mod_cast card_pos.mpr hA
  have hscaled : (p : ℝ) ≤
      2 ^ Fintype.card I * (1 + 1 / 100000) * (admissible β s M).card := by
    have h := mul_le_mul_of_nonneg_left hlow (by norm_num : (0 : ℝ) ≤ 1 + 1 / 100000)
    have hsmall : (p : ℝ) ≤ (1 + 1 / 100000) * (p * (1 - (2 : ℝ)⁻¹ ^ 50)) := by
      have hnum : (1 : ℝ) ≤ (1 + 1 / 100000) * (1 - (2 : ℝ)⁻¹ ^ 50) := by norm_num
      nlinarith
    exact (hsmall.trans h).trans_eq (by ring)
  change (if a ∈ admissible β s M then ((admissible β s M).card : ℝ)⁻¹ else 0) ≤ _
  split_ifs
  · rw [← one_div, div_le_div_iff₀ hA0 hp0, one_mul]
    exact hscaled
  · positivity

theorem character_sum_small (hW : WeilBound (ZMod p))
    (β : I → ZMod p) (hβ : Function.Injective β)
    (s : I → ℤ) (hs : ∀ i, s i = 1 ∨ s i = -1)
    (M : Finset (ZMod p)) (hM : ∀ i, β i ∈ M)
    (hI : Fintype.card I ≤ 4) (hz : M.card ≤ 12)
    (t : ZMod p) (ht : t ∉ M) :
    (2 : ℝ) ^ Fintype.card I *
      |((∑ x ∈ admissible β s M, quadraticChar (ZMod p) (x - t) : ℤ) : ℝ)| ≤
        512 * Real.sqrt p := by
  have h := character_admissible_bound hW β hβ s hs M hM t
    (fun i heq => ht (heq.symm ▸ hM i))
  have h0 := small_soft_error (p := p) (by omega : Fintype.card I ≤ 5)
  have h1 := small_soft_error (p := p) (by omega : Fintype.card I + 1 ≤ 5)
  have hpow : (2 : ℝ) ^ Fintype.card I ≤ 16 := by
    convert pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hI using 1
    norm_num
  have hzR : (M.card : ℝ) ≤ 12 := by exact_mod_cast hz
  have hprod := mul_le_mul hpow hzR (by positivity) (by norm_num : (0 : ℝ) ≤ 16)
  have hq : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hsqrt : (1 : ℝ) ≤ Real.sqrt p := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hq
  linarith

end Sarkozy.JointRows.PinCoordinate

module

public import Sarkozy.SpectralC.StarProductCube

/-! Raw-star products on an injective law with a proved cube comparison. -/

@[expose] public section

namespace Sarkozy.SpectralC.TwoLabel

open Finset Sarkozy.Cuts
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [Fintype Ω]

theorem starProduct_law_sq (hDLK : Target.FourCycle) (hp : p ≠ 2)
    (ν : FiniteLaw Ω) (X : Ω → ι → ZMod p) (hX : ∀ ω, Function.Injective (X ω))
    {D : ℝ} (hD : 0 ≤ D)
    (hdens : ∀ (f : (ι → ZMod p) → ℝ), (∀ x, 0 ≤ f x) →
      ν.expect (fun ω => f (X ω)) ≤ D * (cube p ι).expect f)
    (S T : Finset ι) (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (F : ZMod p → ZMod p → ℝ) (hF : ∀ u, F u u = 0) :
    ν.expect (fun ω => starProduct S T F (X ω) ^ 2) ≤
      (if S = T then 4 else 1) * D * (p : ℝ)⁻¹ ^ 2 *
        (fieldLaw p).expect (fun u => (fieldLaw p).expect (fun v => F u v ^ 2)) := by
  by_cases he : S = T
  · subst T
    rw [ite_eq_left rfl]
    rw [union_self] at hST
    obtain ⟨i, hi, j, hj, hij⟩ := one_lt_card.mp (by omega : 1 < S.card)
    let g := fun x : ι → ZMod p => (if x i = x j then 0 else starProduct S S F x) ^ 2
    have hg (ω : Ω) : g (X ω) = starProduct S S F (X ω) ^ 2 := by
      dsimp [g]
      rw [ite_eq_right (fun h => hij (hX ω h))]
    calc
      _ = ν.expect (fun ω => g (X ω)) := ν.expect_congr fun ω => (hg ω).symm
      _ ≤ D * (cube p ι).expect g := hdens g (fun _ => sq_nonneg _)
      _ ≤ D * (4 * (p : ℝ)⁻¹ ^ 2 * (fieldLaw p).expect
          (fun u => (fieldLaw p).expect (fun v => F u v ^ 2))) :=
        mul_le_mul_of_nonneg_left (starProduct_equal_sq hDLK hp S hi hj hij F hF) hD
      _ = _ := by ring
  · rw [ite_eq_right he, one_mul]
    calc
      _ ≤ D * (cube p ι).expect (fun x => starProduct S T F x ^ 2) :=
        hdens _ (fun _ => sq_nonneg _)
      _ ≤ D * ((p : ℝ)⁻¹ ^ 2 * (fieldLaw p).expect
          (fun u => (fieldLaw p).expect (fun v => F u v ^ 2))) :=
        mul_le_mul_of_nonneg_left (starProduct_distinct_sq hp S T hS hT he F) hD
      _ = _ := by ring

noncomputable def offdiagFeature (S T : Finset ι) (x : ι → ZMod p)
    (z : ZMod p × ZMod p) : ℝ :=
  if z.1 = z.2 then 0 else
    (∏ i ∈ S, chiRe (z.1 - x i)) * (∏ j ∈ T, chiRe (z.2 - x j))

omit [Fintype ι] [DecidableEq ι] [Fintype Ω] in
theorem offdiagFeature_map (S T : Finset ι) (F : ZMod p × ZMod p → ℝ) (x : ι → ZMod p) :
    recOp ((fieldLaw p).product (fieldLaw p)) (offdiagFeature S T) F x =
      starProduct S T (fun u v => if u = v then 0 else F (u, v)) x := by
  unfold recOp starProduct
  rw [FiniteLaw.expect_product]
  apply FiniteLaw.expect_congr
  intro u
  apply FiniteLaw.expect_congr
  intro v
  unfold offdiagFeature
  dsimp only
  split_ifs <;> ring

/-- The auxiliary diagonal is removed once, on the shared pair of labels. -/
theorem offdiagFeature_law_sq (hDLK : Target.FourCycle) (hp : p ≠ 2)
    (ν : FiniteLaw Ω) (X : Ω → ι → ZMod p) (hX : ∀ ω, Function.Injective (X ω))
    {D : ℝ} (hD : 0 ≤ D)
    (hdens : ∀ (f : (ι → ZMod p) → ℝ), (∀ x, 0 ≤ f x) →
      ν.expect (fun ω => f (X ω)) ≤ D * (cube p ι).expect f)
    (S T : Finset ι) (hS : S.Nonempty) (hT : T.Nonempty) (hST : 2 ≤ (S ∪ T).card)
    (F : ZMod p × ZMod p → ℝ) :
    ν.expect (fun ω => recOp ((fieldLaw p).product (fieldLaw p))
      (fun ω z => offdiagFeature S T (X ω) z) F ω ^ 2) ≤
      (if S = T then 4 else 1) * D * (p : ℝ)⁻¹ ^ 2 *
        ((fieldLaw p).product (fieldLaw p)).expect (fun z => F z ^ 2) := by
  have he (ω : Ω) : recOp ((fieldLaw p).product (fieldLaw p))
      (fun ω z => offdiagFeature S T (X ω) z) F ω =
        starProduct S T (fun u v => if u = v then 0 else F (u, v)) (X ω) :=
    offdiagFeature_map S T F (X ω)
  simp_rw [he]
  have h := starProduct_law_sq hDLK hp ν X hX hD hdens S T hS hT hST
    (fun u v => if u = v then 0 else F (u, v)) (fun _ => ite_eq_left rfl)
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by split_ifs <;> positivity))
  rw [FiniteLaw.expect_product]
  apply FiniteLaw.expect_mono
  intro u
  apply FiniteLaw.expect_mono
  intro v
  by_cases h : u = v
  · rw [ite_eq_left h]
    norm_num only [zero_pow, OfNat.ofNat_ne_zero]
    exact sq_nonneg _
  · rw [ite_eq_right h]

end Sarkozy.SpectralC.TwoLabel

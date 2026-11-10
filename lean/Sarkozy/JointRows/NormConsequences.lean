module

public import Sarkozy.JointRows.RowsA

/-! A full kernel estimate controls its mass and both centred marginal images. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Finset Sarkozy.FiveType

variable {X : Type*} [Fintype X]

theorem nrm_const_one (μ : FiniteLaw X) : nrm μ (fun _ => 1) = 1 := by
  simp [nrm, ip, FiniteLaw.expect_const]

theorem kf_const_one (μ : FiniteLaw X) (f g : X → ℝ) :
    kf μ (fun _ _ => 1) f g = μ.expect f * μ.expect g := by
  simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

theorem formBound_sub_one_iff (μ : FiniteLaw X) (K : X → X → ℝ) (d : ℝ) :
    FormBound μ (fun x y => K x y - 1) d ↔ NormBound μ K d := by
  have heq (f g : X → ℝ) :
      kf μ (fun x y => K x y - 1) f g = kf μ K f g - μ.expect f * μ.expect g := by
    rw [← kf_const_one]
    simp only [kf, mul_sub, sub_mul, sum_sub_distrib]
  simp only [FormBound, NormBound, heq]

theorem normBound_of_parts (μ : FiniteLaw X) (K A B C : X → X → ℝ)
    (heq : ∀ x y, K x y = 1 + A x y + B x y - C x y)
    {a b c : ℝ} (ha : FormBound μ A a) (hb : FormBound μ B b) (hc : FormBound μ C c) :
    NormBound μ K (a + b + c) := by
  rw [← formBound_sub_one_iff]
  intro f g
  have hh : kf μ (fun x y => K x y - 1) f g =
      kf μ A f g + kf μ B f g - kf μ C f g := by
    simp only [kf, ← sum_add_distrib, ← sum_sub_distrib]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by rw [heq]; ring
  rw [hh]
  calc
    _ ≤ |kf μ A f g| + |kf μ B f g| + |kf μ C f g| :=
      (abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by linarith [ha f g, hb f g, hc f g]

theorem normBound_mass {μ : FiniteLaw X} {K : X → X → ℝ} {d : ℝ}
    (h : NormBound μ K d) : |RowsA.mass μ K - 1| ≤ d := by
  have hh := h (fun _ => 1) (fun _ => 1)
  simpa only [RowsA.mass, nrm_const_one, FiniteLaw.expect_const, mul_one] using hh

theorem normBound_transpose {μ : FiniteLaw X} {K : X → X → ℝ} {d : ℝ}
    (h : NormBound μ K d) : NormBound μ (fun x y => K y x) d := by
  intro f g
  have heq : kf μ (fun x y => K y x) f g = kf μ K g f := by
    unfold kf
    rw [sum_comm]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  rw [heq]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using h g f

theorem normBound_kone {μ : FiniteLaw X} {K : X → X → ℝ} {d : ℝ}
    (h : NormBound μ K d) : nrm μ (fun x => kone μ K x - 1) ≤ d := by
  let f := fun x => kone μ K x - 1
  have hh := h f (fun _ => 1)
  rw [nrm_const_one, FiniteLaw.expect_const, mul_one, mul_one, kf_one_right] at hh
  have heq : ip μ f (kone μ K) - μ.expect f = ip μ f f := by
    unfold ip
    rw [← FiniteLaw.expect_sub]
    exact μ.expect_congr fun x => by dsimp [f]; ring
  rw [heq, ip_self_eq, abs_of_nonneg (sq_nonneg _)] at hh
  have hd : 0 ≤ d := (abs_nonneg _).trans (normBound_mass h)
  have hf0 := FiveType.nrm_nonneg μ f
  change nrm μ f ≤ d
  nlinarith

theorem normBound_kone' {μ : FiniteLaw X} {K : X → X → ℝ} {d : ℝ}
    (h : NormBound μ K d) : nrm μ (fun x => kone' μ K x - 1) ≤ d :=
  normBound_kone (normBound_transpose h)

theorem normBound_cen_kone {μ : FiniteLaw X} {K : X → X → ℝ} {d : ℝ}
    (h : NormBound μ K d) : nrm μ (cen μ (kone μ K)) ≤ d := by
  have heq : cen μ (kone μ K) = cen μ (fun x => kone μ K x - 1) := by
    funext x
    simp only [cen, FiniteLaw.expect_sub, FiniteLaw.expect_const]
    ring
  rw [heq]
  exact (RowsA.nrm_cen_le _ _).trans (normBound_kone h)

theorem normBound_cen_kone' {μ : FiniteLaw X} {K : X → X → ℝ} {d : ℝ}
    (h : NormBound μ K d) : nrm μ (cen μ (kone' μ K)) ≤ d :=
  normBound_cen_kone (normBound_transpose h)

end Sarkozy.JointRows

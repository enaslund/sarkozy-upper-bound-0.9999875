module

public import Sarkozy.Cuts.SwappedLower

/-! Removing the leading singular tensor from the swapped rectangle. -/

@[expose] public section

namespace Sarkozy.Cuts

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

omit [Fintype Y] in
theorem ip_remove_unit_projection (μ : FiniteLaw X) (u f : X → ℝ) (hu : nrm μ u = 1) :
    ip μ (fun x => f x - ip μ f u * u x) u = 0 := by
  have hu2 : μ.expect (fun x => u x * u x) = 1 := by
    change ip μ u u = 1
    rw [← nrm_sq_eq, hu]
    norm_num
  unfold ip
  have he : (fun x => (f x - μ.expect (fun y => f y * u y) * u x) * u x) =
      fun x => f x * u x - μ.expect (fun y => f y * u y) * (u x * u x) := by
    funext x; ring
  rw [he, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, hu2]
  ring

omit [Fintype Y] in
theorem nrm_remove_unit_projection_le (μ : FiniteLaw X) (u f : X → ℝ)
    (hu : nrm μ u = 1) :
    nrm μ (fun x => f x - ip μ f u * u x) ≤ nrm μ f := by
  let m := ip μ f u
  have hu2 : μ.expect (fun x => u x * u x) = 1 := by
    change ip μ u u = 1
    rw [← nrm_sq_eq, hu]
    norm_num
  have hm : μ.expect (fun x => f x * u x) = m := rfl
  change Real.sqrt (ip μ (fun x => f x - m * u x) (fun x => f x - m * u x)) ≤ _
  apply Real.sqrt_le_sqrt
  unfold ip
  have he : (fun x => (f x - m * u x) * (f x - m * u x)) =
      fun x => f x * f x - 2 * m * (f x * u x) + m ^ 2 * (u x * u x) := by
    funext x; ring
  rw [he, FiniteLaw.expect_add, FiniteLaw.expect_sub,
    FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul, hu2, hm]
  nlinarith [sq_nonneg m]

theorem swap_norm_deflated (α : FiniteLaw X) (β : FiniteLaw Y)
    (A A' : X → Y → ℝ) {σ c s : ℝ} (u : X → ℝ) (v : Y → ℝ)
    (hu : nrm α u = 1) (hv : nrm β v = 1) (hσ : 0 ≤ σ)
    (hA : ∀ x y, A x y = σ * u x * v y + A' x y)
    (hAv : ∀ x, recOp β A' v x = 0) (hAu : ∀ y, recAdj α A' u y = 0)
    (hc0 : 0 ≤ c) (hc : ∀ h, nrm α (recOp β A' h) ≤ c * nrm β h)
    (hsσ : σ ≤ s) (hsc : c ≤ s) (f : X × Y → ℝ) :
    nrm (α.product β) (fun p => swapOp α β A f p -
      σ ^ 2 * ip (α.product β) f (fun q => u q.1 * v q.2) * (u p.1 * v p.2)) ≤
      s * c * nrm (α.product β) f := by
  let w : X × Y → ℝ := fun p => u p.1 * v p.2
  let m := ip (α.product β) f w
  have hw : nrm (α.product β) w = 1 := by
    dsimp [w]
    rw [nrm_tensor, hu, hv, one_mul]
  have hu2 : α.expect (fun x => u x * u x) = 1 := by
    change ip α u u = 1
    rw [← nrm_sq_eq, hu]
    norm_num
  have hv2 : β.expect (fun y => v y * v y) = 1 := by
    change ip β v v = 1
    rw [← nrm_sq_eq, hv]
    norm_num
  have hAv' (x : X) : recOp β A v x = σ * u x := by
    unfold recOp
    have he : (fun y => A x y * v y) =
        fun y => (σ * u x) * (v y * v y) + A' x y * v y := by
      funext y; rw [hA]; ring
    rw [he, FiniteLaw.expect_add, FiniteLaw.expect_const_mul, hv2,
      show β.expect (fun y => A' x y * v y) = 0 from hAv x]
    ring
  have hAu' (y : Y) : recAdj α A u y = σ * v y := by
    unfold recAdj
    have he : (fun x => A x y * u x) =
        fun x => (σ * v y) * (u x * u x) + A' x y * u x := by
      funext x; rw [hA]; ring
    rw [he, FiniteLaw.expect_add, FiniteLaw.expect_const_mul, hu2,
      show α.expect (fun x => A' x y * u x) = 0 from hAu y]
    ring
  have heigen (p : X × Y) : swapOp α β A w p = σ ^ 2 * w p := by
    dsimp only [w]
    rw [swapOp_tensor, hAv', hAu']
    ring
  have hlin : swapOp α β A (fun q => f q - m * w q) =
      fun p => swapOp α β A f p - σ ^ 2 * m * w p := by
    funext p
    have he : (fun q => A p.1 q.2 * A q.1 p.2 * (f q - m * w q)) =
        fun q => A p.1 q.2 * A q.1 p.2 * f q - m * (A p.1 q.2 * A q.1 p.2 * w q) := by
      funext q; ring
    change (α.product β).expect _ = _
    rw [he, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul]
    change swapOp α β A f p - m * swapOp α β A w p = _
    rw [heigen]
    ring
  have hb := swap_norm_perp α β A A' u v hu hv hσ hA hAv hAu hc0 hc hsσ hsc
    (fun q => f q - m * w q) (ip_remove_unit_projection _ w f hw)
  rw [hlin] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (nrm_remove_unit_projection_le _ w f hw)
    (mul_nonneg (hσ.trans hsσ) hc0))

omit [Fintype Y] in
theorem rank_one_difference_norm (μ : FiniteLaw X) (a b f : X → ℝ) :
    nrm μ (fun x => ip μ f a * a x - ip μ f b * b x) ≤
      (nrm μ a + nrm μ b) * nrm μ (fun x => a x - b x) * nrm μ f := by
  have hip : ip μ f a - ip μ f b = ip μ f (fun x => a x - b x) := by
    unfold ip
    rw [← FiniteLaw.expect_sub]
    exact μ.expect_congr fun x => by ring
  have he : (fun x => ip μ f a * a x - ip μ f b * b x) =
      fun x => ip μ f a * (a x - b x) + ip μ f (fun y => a y - b y) * b x := by
    funext x; rw [← hip]; ring
  rw [he]
  refine (nrm_add_le _ _ _).trans ?_
  rw [nrm_smul, nrm_smul]
  calc
    _ ≤ (nrm μ f * nrm μ a) * nrm μ (fun x => a x - b x) +
        (nrm μ f * nrm μ (fun x => a x - b x)) * nrm μ b := by
      exact add_le_add (mul_le_mul_of_nonneg_right (abs_ip_le μ f a) (nrm_nonneg _ _))
        (mul_le_mul_of_nonneg_right (abs_ip_le μ f _) (nrm_nonneg _ _))
    _ = _ := by ring

end Sarkozy.Cuts

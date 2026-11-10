module

public import Sarkozy.Cuts.Swapped

/-! Whole-rectangle Cauchy–Schwarz with bounded private factors and shared labels. -/

@[expose] public section

namespace Sarkozy.Cuts

open Sarkozy.Recentering
open scoped BigOperators

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

theorem swap_decorated_multiplier_norm (α : FiniteLaw X) (β : FiniteLaw Y) (π : FiniteLaw S)
    (A : X → Y → ℝ) (φ φ' : X → S → ℝ) (ψ ψ' : Y → S → ℝ)
    (hψ : ∀ y s, |ψ y s| ≤ 1) (hψ' : ∀ y s, |ψ' y s| ≤ 1) {c c' : ℝ} (hc : 0 ≤ c) (hc' : 0 ≤ c')
    (hY : ∀ G, nrm α (recOp (β.product π) (fun x q => A x q.1 * φ x q.2) G) ≤
      c * nrm (β.product π) G)
    (hY' : ∀ G, nrm α (recOp (β.product π) (fun x q => A x q.1 * φ' x q.2) G) ≤
      c' * nrm (β.product π) G)
    (Fn Hn : X × Y → ℝ) :
    |kernelForm (α.product β) (α.product β)
        (fun p q => A p.1 q.2 * A q.1 p.2 * ip π (fun s => φ p.1 s * ψ p.2 s) (fun s => φ' q.1 s * ψ' q.2 s)) Fn Hn| ≤
      c * c' * nrm (α.product β) Fn * nrm (α.product β) Hn := by
  set P : (Y × Y) × S → ℝ := fun r =>
    recAdj α (fun x q => A x q.1 * φ x q.2) (fun x => Fn (x, r.1.1)) (r.1.2, r.2) * ψ r.1.1 r.2 with hP
  set Q : (Y × Y) × S → ℝ := fun r =>
    recAdj α (fun x q => A x q.1 * φ' x q.2) (fun x => Hn (x, r.1.2)) (r.1.1, r.2) * ψ' r.1.2 r.2 with hQ
  have hA : kernelForm (α.product β) (α.product β)
      (fun p q => A p.1 q.2 * A q.1 p.2 * ip π (fun s => φ p.1 s * ψ p.2 s) (fun s => φ' q.1 s * ψ' q.2 s)) Fn Hn =
        ip ((β.product β).product π) P Q := by
    simp only [kernelForm, LinearMap.mk₂_apply, ip, hP, hQ, recAdj, FiniteLaw.expect,
      FiniteLaw.product, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext x'; rw [Finset.sum_comm]
    conv_lhs => arg 2; ext x'; arg 2; ext y'; rw [Finset.sum_comm]
    conv_lhs => rw [Finset.sum_comm]
    conv_lhs => arg 2; ext y'; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun y' _ => Finset.sum_congr rfl (fun s _ =>
      Finset.sum_congr rfl (fun x' _ => Finset.sum_congr rfl (fun x _ => ?_))))
    ring
  have hFub : ∀ (G : (Y × Y) × S → ℝ), ((β.product β).product π).expect G =
      β.expect (fun y => (β.product π).expect (fun q => G ((y, q.1), q.2))) := by
    intro G
    rw [FiniteLaw.expect_product, FiniteLaw.expect_product]
    refine β.expect_congr (fun y => ?_)
    rw [FiniteLaw.expect_product]
  have hFub' : ∀ (G : (Y × Y) × S → ℝ), ((β.product β).product π).expect G =
      β.expect (fun y' => (β.product π).expect (fun q => G ((q.1, y'), q.2))) := by
    intro G
    rw [FiniteLaw.expect_product, FiniteLaw.expect_product, expect_comm]
    refine β.expect_congr (fun y' => ?_)
    rw [FiniteLaw.expect_product]
  have hnF : nrm (α.product β) Fn ^ 2 = β.expect (fun y => α.expect (fun x => Fn (x, y) ^ 2)) := by
    rw [nrm_sq_expect, FiniteLaw.expect_product, expect_comm]
  have hnH : nrm (α.product β) Hn ^ 2 = β.expect (fun y => α.expect (fun x => Hn (x, y) ^ 2)) := by
    rw [nrm_sq_expect, FiniteLaw.expect_product, expect_comm]
  have hPn : nrm ((β.product β).product π) P ≤ c * nrm (α.product β) Fn := by
    apply nrm_le_of_sq_le _ _ hc
    rw [nrm_sq_expect, hFub, hnF, ← FiniteLaw.expect_const_mul]
    refine β.expect_mono (fun y => ?_)
    have h := nrm_recAdj_le α (β.product π) (fun x q => A x q.1 * φ x q.2) hc hY
      (fun x => Fn (x, y))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    refine le_trans (FiniteLaw.expect_mono _ (fun q => ?_)) hsq
    change (_ * ψ y q.2) ^ 2 ≤ _ ^ 2
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      ((sq_le_one_iff_abs_le_one _).mpr (hψ y q.2)) (sq_nonneg _)
  have hQn : nrm ((β.product β).product π) Q ≤ c' * nrm (α.product β) Hn := by
    apply nrm_le_of_sq_le _ _ hc'
    rw [nrm_sq_expect, hFub', hnH, ← FiniteLaw.expect_const_mul]
    refine β.expect_mono (fun y' => ?_)
    have h := nrm_recAdj_le α (β.product π) (fun x q => A x q.1 * φ' x q.2) hc' hY'
      (fun x => Hn (x, y'))
    have hsq := pow_le_pow_left₀ (nrm_nonneg _ _) h 2
    rw [mul_pow, nrm_sq_expect, nrm_sq_expect] at hsq
    refine le_trans (FiniteLaw.expect_mono _ (fun q => ?_)) hsq
    change (_ * ψ' y' q.2) ^ 2 ≤ _ ^ 2
    rw [mul_pow]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left
      ((sq_le_one_iff_abs_le_one _).mpr (hψ' y' q.2)) (sq_nonneg _)
  rw [hA]
  calc |ip ((β.product β).product π) P Q|
      ≤ nrm ((β.product β).product π) P * nrm ((β.product β).product π) Q := abs_ip_le _ _ _
    _ ≤ (c * nrm (α.product β) Fn) * (c' * nrm (α.product β) Hn) :=
        mul_le_mul hPn hQn (nrm_nonneg _ _) (mul_nonneg hc (nrm_nonneg _ _))
    _ = c * c' * nrm (α.product β) Fn * nrm (α.product β) Hn := by ring


end Sarkozy.Cuts

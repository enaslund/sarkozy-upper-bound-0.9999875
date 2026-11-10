module

public import Sarkozy.JointRows.StarScalarBound

/-!
# Individual exact-support terms with a centre multiplier

Complementary leaf means are multipliers on the star centre. Every
nonempty exact support still contributes a Paley factor p^(-1/2).
This permits a coarse sum of the mean terms at the tail threshold.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

theorem nrm_mul_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : FiniteLaw Ω) (a f : Ω → ℝ) {b : ℝ} (hb : 0 ≤ b)
    (ha : ∀ x, μ.weight x ≠ 0 → |a x| ≤ b) :
    nrm μ (fun x => a x * f x) ≤ b * nrm μ f := by
  have hs : ip μ (fun x => a x * f x) (fun x => a x * f x) ≤ b ^ 2 * ip μ f f := by
    unfold ip FiniteLaw.expect
    rw [mul_sum]
    apply sum_le_sum
    intro x _
    by_cases hx : μ.weight x = 0
    · simp [hx]
    · have hsq : a x ^ 2 ≤ b ^ 2 := by
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (a x)) hb).mpr (ha x hx)
      have h := mul_le_mul_of_nonneg_left hsq
        (mul_nonneg (μ.nonneg x) (sq_nonneg (f x)))
      nlinarith
  calc _ ≤ Real.sqrt (b ^ 2 * ip μ f f) := Real.sqrt_le_sqrt hs
    _ = _ := by rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb]; rfl

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem uStar_sq_le (νp : X → FiniteLaw (ZMod p)) (i : X) {κ : ℝ}
    (hκ : ∀ a, (νp i).weight a ≤ κ / p) (f : (X → ZMod p) → ℝ) :
    ip (FiniteLaw.uniform (ZMod p)) (uStar νp i f) (uStar νp i f) ≤
      κ * ip (blockLaw νp) f f := by
  let u := uStar νp i f
  have hn : 0 ≤ ip (FiniteLaw.uniform (ZMod p)) u u :=
    FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  have hf : 0 ≤ ip (blockLaw νp) f f :=
    FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hk0 : 0 ≤ κ := by
    have h := ((νp i).nonneg 0).trans (hκ 0)
    rwa [le_div_iff₀ hp0, zero_mul] at h
  have heval : ip (blockLaw νp) (fun x => u (x i)) (fun x => u (x i)) ≤
      κ * ip (FiniteLaw.uniform (ZMod p)) u u := by
    unfold ip
    rw [expect_eval νp i (fun a => u a * u a), FiniteLaw.expect_uniform, ZMod.card]
    unfold FiniteLaw.expect
    rw [mul_div_assoc', mul_sum, sum_div]
    apply sum_le_sum
    intro a _
    have h := mul_le_mul_of_nonneg_right (hκ a) (mul_self_nonneg (u a))
    convert h using 1
    ring
  have heq : (blockLaw νp).expect (fun x => u (x i) * f x) =
      ip (FiniteLaw.uniform (ZMod p)) u u := expect_eval_mul νp i u f
  have hcs := (blockLaw νp).cauchy_schwarz_sq (fun x => u (x i)) f
  have hsquare (g : (X → ZMod p) → ℝ) :
      (blockLaw νp).expect (fun x => g x ^ 2) = ip (blockLaw νp) g g := by
    exact FiniteLaw.expect_congr _ fun x => sq (g x)
  rw [heq, hsquare, hsquare] at hcs
  have h := hcs.trans (mul_le_mul_of_nonneg_right heval hf)
  by_cases hz : ip (FiniteLaw.uniform (ZMod p)) u u = 0
  · change ip (FiniteLaw.uniform (ZMod p)) u u ≤ _
    rw [hz]
    exact mul_nonneg hk0 hf
  · have hpos := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

theorem wStar_sq_le_odd (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    (S : Finset X) (hS : S.Nonempty) {κ : ℝ}
    (hκ : ∀ i ∈ S, ∀ a, (νp i).weight a ≤ κ / p) (f : (X → ZMod p) → ℝ) :
    ip (FiniteLaw.uniform (ZMod p)) (wStar νp S f) (wStar νp S f) ≤
      κ * (p : ℝ)⁻¹ * ip (blockLaw νp) f f := by
  let w := wStar νp S f
  have hn : 0 ≤ ip (FiniteLaw.uniform (ZMod p)) w w :=
    FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  have hf : 0 ≤ ip (blockLaw νp) f f :=
    FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  have hk0 : 0 ≤ κ := by
    obtain ⟨i, hi⟩ := hS
    have h := ((νp i).nonneg 0).trans (hκ i hi 0)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
    rwa [le_div_iff₀ hp0, zero_mul] at h
  have hW := wOp_norm_le_odd hp νp S hS hκ w
  have hcs := (blockLaw νp).cauchy_schwarz_sq (wOp νp S w) f
  have hsquare (g : (X → ZMod p) → ℝ) :
      (blockLaw νp).expect (fun x => g x ^ 2) = ip (blockLaw νp) g g := by
    exact FiniteLaw.expect_congr _ fun x => sq (g x)
  change (ip (blockLaw νp) (wOp νp S w) f) ^ 2 ≤ _ at hcs
  rw [ip_wOp, hsquare, hsquare] at hcs
  have h := hcs.trans (mul_le_mul_of_nonneg_right hW hf)
  by_cases hz : ip (FiniteLaw.uniform (ZMod p)) w w = 0
  · change ip (FiniteLaw.uniform (ZMod p)) w w ≤ _
    rw [hz]
    positivity
  · have hpos := lt_of_le_of_ne hn (Ne.symm hz)
    nlinarith

theorem uStar_nrm_le (νp : X → FiniteLaw (ZMod p)) (i : X) {κ : ℝ} (hk : 0 ≤ κ)
    (hκ : ∀ a, (νp i).weight a ≤ κ / p) (f : (X → ZMod p) → ℝ) :
    nrm (FiniteLaw.uniform (ZMod p)) (uStar νp i f) ≤
      Real.sqrt κ * nrm (blockLaw νp) f := by
  calc _ ≤ Real.sqrt (κ * ip (blockLaw νp) f f) :=
      Real.sqrt_le_sqrt (uStar_sq_le νp i hκ f)
    _ = _ := by rw [Real.sqrt_mul hk]; rfl

theorem wStar_nrm_le_odd (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    (S : Finset X) (hS : S.Nonempty) {κ : ℝ} (hk : 0 ≤ κ)
    (hκ : ∀ i ∈ S, ∀ a, (νp i).weight a ≤ κ / p) (f : (X → ZMod p) → ℝ) :
    nrm (FiniteLaw.uniform (ZMod p)) (wStar νp S f) ≤
      Real.sqrt κ * (Real.sqrt p)⁻¹ * nrm (blockLaw νp) f := by
  calc _ ≤ Real.sqrt (κ * (p : ℝ)⁻¹ * ip (blockLaw νp) f f) :=
      Real.sqrt_le_sqrt (wStar_sq_le_odd hp νp S hS hκ f)
    _ = _ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hk, Real.sqrt_inv]
      rfl

theorem rowStar_multiplier_form (νp : X → FiniteLaw (ZMod p))
    (νq : Y → FiniteLaw (ZMod p)) (i : X) (T : Finset Y) (a : ZMod p → ℝ)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq (fun x y => a (x i) * ∏ j ∈ T, phi (νq j) (x i) (y j)) f g =
      ip (FiniteLaw.uniform (ZMod p)) (uStar νp i f) (fun t => a t * wStar νq T g t) := by
  have hin (x : X → ZMod p) : (blockLaw νq).expect
      (fun y => f x * (a (x i) * ∏ j ∈ T, phi (νq j) (x i) (y j)) * g y) =
      (a (x i) * wStar νq T g (x i)) * f x := by
    unfold wStar
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_mul_const]
    exact FiniteLaw.expect_congr _ fun y => by ring
  unfold bform
  rw [FiniteLaw.expect_congr _ hin,
    expect_eval_mul νp i (fun t => a t * wStar νq T g t) f]
  unfold ip
  exact FiniteLaw.expect_congr _ fun t => by ring

theorem rowStar_multiplier_bound (hp : p ≠ 2)
    (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (i : X) (T : Finset Y) (hT : T.Nonempty) (a : ZMod p → ℝ)
    {κ b : ℝ} (hk : 0 ≤ κ) (hb : 0 ≤ b) (ha : ∀ t, |a t| ≤ b)
    (hdensX : ∀ t, (νp i).weight t ≤ κ / p)
    (hdensY : ∀ j ∈ T, ∀ t, (νq j).weight t ≤ κ / p)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    |bform νp νq (fun x y => a (x i) * ∏ j ∈ T, phi (νq j) (x i) (y j)) f g| ≤
      κ * (Real.sqrt p)⁻¹ * b * nrm (blockLaw νp) f * nrm (blockLaw νq) g := by
  rw [rowStar_multiplier_form]
  have hleft := uStar_nrm_le νp i hk hdensX f
  have hright := (nrm_mul_le (FiniteLaw.uniform (ZMod p)) a (wStar νq T g) hb
    (fun t _ => ha t)).trans (mul_le_mul_of_nonneg_left
      (wStar_nrm_le_odd hp νq T hT hk hdensY g) hb)
  apply (abs_ip_le _ _ _).trans
  apply (mul_le_mul hleft hright (FiveType.nrm_nonneg _ _)
    (mul_nonneg (Real.sqrt_nonneg _) (FiveType.nrm_nonneg _ _))).trans_eq
  have hsq := Real.mul_self_sqrt hk
  calc _ = (Real.sqrt κ * Real.sqrt κ) *
      ((Real.sqrt p)⁻¹ * b * nrm (blockLaw νp) f * nrm (blockLaw νq) g) := by ring
    _ = _ := by rw [hsq]; ring

end Sarkozy.JointRows.StarOps

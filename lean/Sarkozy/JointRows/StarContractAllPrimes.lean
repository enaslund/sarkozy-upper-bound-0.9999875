module

public import Sarkozy.JointRows.StarContract
public import Sarkozy.JointRows.StarFeaturesAllPrimes

/-!
# The star feature contraction at every odd prime

Orthogonality of exact supports and the Paley contraction give the
assembled feature contraction used in the tail row estimate.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]
variable {X : Type*} [Fintype X] [DecidableEq X]

theorem featMap_norm_le_odd (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (𝒮 : Finset (Finset X))
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) (u : X → ZMod p → ℝ) (w : Finset X → ZMod p → ℝ) :
    ip (blockLaw νp) (featMap νp κ 𝒮 u w) (featMap νp κ 𝒮 u w) ≤
      (∑ i, ip (FiniteLaw.uniform (ZMod p)) (u i) (u i)) +
        ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (w S) (w S) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set c : ℝ := (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ with hc
  set a : X → (X → ZMod p) → ℝ := fun i x => (Real.sqrt κ)⁻¹ * uOp νp i (u i) x with ha
  set b : Finset X → (X → ZMod p) → ℝ := fun S x => c * wOp νp S (w S) x with hb
  have hF : featMap νp κ 𝒮 u w = fun x => (∑ i, a i x) + ∑ S ∈ 𝒮, b S x := rfl
  have haS : ∀ i, Star.ExactSupport νp {i} (a i) := fun i =>
    exactSupport_const_mul νp (uOp_exactSupport νp i (u i)) _
  have hbS : ∀ S, Star.ExactSupport νp S (b S) := fun S =>
    exactSupport_const_mul νp (wOp_exactSupport νp S (w S)) _
  have hne : ∀ i, ∀ S ∈ 𝒮, ({i} : Finset X) ≠ S := fun i S hS hiS => by
    have := h𝒮 S hS
    rw [← hiS, Finset.card_singleton] at this
    omega
  rw [hF, ip_add_add, ip_sum_sum, ip_sum_sum, ip_sum_sum, ip_sum_sum]
  have haa : ∑ i, ∑ j, ip (blockLaw νp) (a i) (a j) = ∑ i, ip (blockLaw νp) (a i) (a i) :=
    sum_sum_diag _ _ fun i _ j _ hij => Star.hoeffding_orthogonal νp
      (by rw [Ne, Finset.singleton_inj]; exact hij) (haS i) (haS j)
  have hab : ∑ i, ∑ S ∈ 𝒮, ip (blockLaw νp) (a i) (b S) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun S hS =>
      Star.hoeffding_orthogonal νp (hne i S hS) (haS i) (hbS S)
  have hba : ∑ S ∈ 𝒮, ∑ i, ip (blockLaw νp) (b S) (a i) = 0 :=
    Finset.sum_eq_zero fun S hS => Finset.sum_eq_zero fun i _ =>
      Star.hoeffding_orthogonal νp (Ne.symm (hne i S hS)) (hbS S) (haS i)
  have hbb : ∑ S ∈ 𝒮, ∑ T ∈ 𝒮, ip (blockLaw νp) (b S) (b T) =
      ∑ S ∈ 𝒮, ip (blockLaw νp) (b S) (b S) :=
    sum_sum_diag _ _ fun S _ T _ hST => Star.hoeffding_orthogonal νp hST (hbS S) (hbS T)
  rw [haa, hab, hba, hbb, add_zero, add_zero]
  have hka : ∀ i, ip (blockLaw νp) (a i) (a i) ≤ ip (FiniteLaw.uniform (ZMod p)) (u i) (u i) := by
    intro i
    have h1 := ip_uOp_self_le νp i (hdens i) (u i)
    have h2 : ip (blockLaw νp) (a i) (a i) =
        κ⁻¹ * ip (blockLaw νp) (uOp νp i (u i)) (uOp νp i (u i)) := by
      simp only [ha, ip]
      rw [← FiniteLaw.expect_const_mul]
      refine FiniteLaw.expect_congr _ fun x => ?_
      have hk : (Real.sqrt κ)⁻¹ * (Real.sqrt κ)⁻¹ = κ⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hκ.le]
      linear_combination (uOp νp i (u i) x * uOp νp i (u i) x) * hk
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hκ.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul] at h3
  have hkb : ∀ S ∈ 𝒮, ip (blockLaw νp) (b S) (b S) ≤
      ip (FiniteLaw.uniform (ZMod p)) (w S) (w S) := by
    intro S hS
    have hSne : S.Nonempty := Finset.card_pos.mp (by have := h𝒮 S hS; omega)
    have h1 := wOp_norm_le_odd hp νp S hSne (fun i _ a => hdens i a) (w S)
    have h2 : ip (blockLaw νp) (b S) (b S) = c * c * ip (blockLaw νp) (wOp νp S (w S))
        (wOp νp S (w S)) := by
      simp only [hb, ip]
      rw [← FiniteLaw.expect_const_mul]
      exact FiniteLaw.expect_congr _ fun x => by ring
    have hcc : c * c * (κ * (p : ℝ)⁻¹) = 1 := by
      rw [hc, ← mul_inv, mul_inv]
      have hsp0 : Real.sqrt p ≠ 0 := by positivity
      have hsκ0 : Real.sqrt κ ≠ 0 := by positivity
      field_simp
      rw [Real.sq_sqrt hp0.le, Real.sq_sqrt hκ.le]
      ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (mul_self_nonneg c)
    calc c * c * ip (blockLaw νp) (wOp νp S (w S)) (wOp νp S (w S))
        ≤ c * c * (κ * (p : ℝ)⁻¹ * ip (FiniteLaw.uniform (ZMod p)) (w S) (w S)) := h3
      _ = ip (FiniteLaw.uniform (ZMod p)) (w S) (w S) := by
        rw [← mul_assoc, hcc, one_mul]
  exact add_le_add (Finset.sum_le_sum fun i _ => hka i) (Finset.sum_le_sum hkb)

/-- **`‖𝓕_X^* f‖ ≤ ‖f‖`** for `f ∈ L²_0(ν_X)`: the feature vector of `pure_block_identity`
has norm at most `‖f‖`. This is `hV` of `lem:joint-rows`(a) for one row. -/
theorem featStar_norm_le_odd (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (𝒮 : Finset (Finset X))
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) {f : (X → ZMod p) → ℝ} (hf : (blockLaw νp).expect f = 0) :
    (∑ i, ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i) (featU νp κ f i)) +
        ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S) (featW νp κ f S) ≤
      ip (blockLaw νp) f f := by
  set N : ℝ := (∑ i, ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i) (featU νp κ f i)) +
    ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S) (featW νp κ f S) with hN
  set F := featMap νp κ 𝒮 (featU νp κ f) (featW νp κ f) with hFdef
  -- the adjoint identity `⟨𝓕(𝓕^* f), f⟩ = ‖𝓕^* f‖²`
  have hadj : ip (blockLaw νp) F f = N := by
    have hU : ∀ i, ip (blockLaw νp) (fun x => (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x) f =
        ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i) (featU νp κ f i) := by
      intro i
      have h1 := ip_uOp_adj νp i (featU νp κ f i) hf
      unfold ip at h1 ⊢
      rw [show (fun x => (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x * f x) =
          fun x => (Real.sqrt κ)⁻¹ * (uOp νp i (featU νp κ f i) x * f x) from
          funext fun x => by ring, FiniteLaw.expect_const_mul, h1, ← FiniteLaw.expect_const_mul]
      exact FiniteLaw.expect_congr _ fun a => by unfold featU; ring
    have hW : ∀ S, ip (blockLaw νp) (fun x => (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ *
        wOp νp S (featW νp κ f S) x) f =
        ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S) (featW νp κ f S) := by
      intro S
      have h1 := ip_wOp νp S (featW νp κ f S) f
      set c : ℝ := (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ with hc
      have hcen : featW νp κ f S =
          cen (FiniteLaw.uniform (ZMod p)) (fun t => c * wStar νp S f t) := by
        funext t; unfold featW cen; rw [FiniteLaw.expect_const_mul, hc]; ring
      have hmean : (FiniteLaw.uniform (ZMod p)).expect (featW νp κ f S) = 0 := by
        rw [hcen]; unfold cen
        rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]
      unfold ip at h1 ⊢
      rw [show (fun x => c * wOp νp S (featW νp κ f S) x * f x) =
          fun x => c * (wOp νp S (featW νp κ f S) x * f x) from funext fun x => by ring,
        FiniteLaw.expect_const_mul, h1, ← FiniteLaw.expect_const_mul]
      -- `c ⟨w, W^* f⟩ = ⟨w, w⟩` for `w = cen (c W^* f)`, which has mean zero
      have hw : ∀ t, c * wStar νp S f t = featW νp κ f S t +
          (FiniteLaw.uniform (ZMod p)).expect (fun t => c * wStar νp S f t) := by
        intro t; rw [hcen]; unfold cen; ring
      calc (FiniteLaw.uniform (ZMod p)).expect (fun ω => c * (featW νp κ f S ω * wStar νp S f ω))
          = (FiniteLaw.uniform (ZMod p)).expect (fun ω => featW νp κ f S ω * featW νp κ f S ω +
              (FiniteLaw.uniform (ZMod p)).expect (fun t => c * wStar νp S f t) *
                featW νp κ f S ω) :=
            FiniteLaw.expect_congr _ fun ω => by
              rw [show c * (featW νp κ f S ω * wStar νp S f ω) =
                featW νp κ f S ω * (c * wStar νp S f ω) by ring, hw ω]
              ring
        _ = _ := by rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, hmean, mul_zero, add_zero]
    rw [hFdef]
    unfold featMap
    have hsplit := ip_add_add (blockLaw νp)
    unfold ip at hU hW ⊢
    rw [show (fun x => ((∑ i, (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x) +
        ∑ S ∈ 𝒮, (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wOp νp S (featW νp κ f S) x) * f x) =
        fun x => (∑ i, (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x * f x) +
          ∑ S ∈ 𝒮, (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wOp νp S (featW νp κ f S) x * f x from
        funext fun x => by rw [add_mul, Finset.sum_mul, Finset.sum_mul],
      FiniteLaw.expect_add, expect_finset_sum, expect_finset_sum]
    simp only [hU, hW, hN, ip]
  -- Cauchy–Schwarz and the contraction
  have hN0 : 0 ≤ N := by
    rw [hN]
    exact add_nonneg (Finset.sum_nonneg fun i _ => FiniteLaw.expect_nonneg _ fun _ =>
      mul_self_nonneg _) (Finset.sum_nonneg fun S _ => FiniteLaw.expect_nonneg _ fun _ =>
      mul_self_nonneg _)
  have hC := featMap_norm_le_odd hp νp hκ hdens 𝒮 h𝒮 (featU νp κ f) (featW νp κ f)
  rw [← hFdef, ← hN] at hC
  have hcs := FiniteLaw.cauchy_schwarz_sq (blockLaw νp) F f
  have hsq : ∀ g : (X → ZMod p) → ℝ, (blockLaw νp).expect (fun x => g x ^ 2) =
      ip (blockLaw νp) g g := fun g => FiniteLaw.expect_congr _ fun x => sq (g x)
  rw [hsq, hsq] at hcs
  unfold ip at hadj
  rw [hadj] at hcs
  have hff : 0 ≤ ip (blockLaw νp) f f := FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  -- `N² ≤ ‖F‖² ‖f‖² ≤ N ‖f‖²`
  have h2 : N ^ 2 ≤ N * ip (blockLaw νp) f f := hcs.trans (mul_le_mul_of_nonneg_right hC hff)
  by_cases hN' : N = 0
  · rw [hN']; exact hff
  · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hN')
    nlinarith

end Sarkozy.JointRows.StarOps

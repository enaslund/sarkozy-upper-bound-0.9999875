module

public import Sarkozy.Moments.CoarseDeficit
public import Sarkozy.Moments.Product
public import Sarkozy.DensityUpgrade.BlockGate

/-!
# The typed-mixture lemma with the exact coefficient, for one bad component

`paper/sections/30_density_moment_upgrade.tex`, `lem:density:typed-mixture`, final sentence: a
mixture of a unit mixed `L^s` law of weight `1 - t` and an arbitrary law with uniform marginals
of weight `t` has unit mixed `L^R` whenever `t (1 + C_d(Q)) ≤ 1`. With `v = d` the paper's
coefficient is `C_d(Q) = φ(Q)/ψ(Q)`, `φ(t) = t^λ - λ t + λ - 1`, `ψ(t) = κ t + 1 - κ - t^κ`,
`λ = d/R`, `κ = s/R`, by the monotone-ratio argument of its proof.

* `phi_le_exactCoeff_psi`: `φ(t) ≤ C' ψ(t)` on `[0, Q]` with
  `C' = max(φ(Q)/ψ(Q), λ(λ-1)/(κ(1-κ)))`: on `[1, Q]` by WP-FI's monotone ratio
  (`DensityUpgrade.blockGate_ratio_mono`), on `[0, 1]` by the curvature comparison
  (`Sarkozy.powerGap_le_curvature`). The second term of the maximum is the paper's value of the
  ratio at `t = 1` (`φ''(1)/ψ''(1)`); keeping it avoids the limit `t → 1⁺`. It is about `1.3` at
  the paper's constants, far below the coefficients of the gates.
* `exact_deficit`: the one-coordinate estimate `‖f‖_d^d - 1 ≤ C' (1 - ‖f‖_s^d)` for `‖f‖_R = 1`.
* `exact_typed_mixture`: the final sentence of `lem:density:typed-mixture` with the constant `C'`,
  on `d` slots, for laws with uniform marginals (`DensityUpgrade.blockGateUnitMixed`).
* `exact_joint_block_gate`: `lem:density:joint-block-gate` without named hypotheses: with
  `log Q ≤ L`, `κ_* > e^{-L(1-κ_*)}`, `t(β)(1 + C(L)) < 1` and `t(β)(1 + c) ≤ 1`,
  `c = θ_*(θ_*-1)/(κ_*(1-κ_*))`, the packet has unit mixed `L^{R_*}`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityMoments

open Sarkozy.DensityUpgrade

/-- The exact coefficient with its curvature floor. -/
noncomputable def exactCoeff (θ κ Q : ℝ) : ℝ :=
  max (blockGatePhi θ Q / blockGatePsi κ Q) (θ * (θ - 1) / (κ * (1 - κ)))

theorem exactCoeff_nonneg {θ κ Q : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    0 ≤ exactCoeff θ κ Q :=
  le_max_of_le_right (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg hκ0.le (by linarith)))

theorem psi_pos {κ t : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (ht : 1 < t) : 0 < blockGatePsi κ t := by
  have h := rpow_one_add_lt_one_add_mul_self (s := t - 1) (by linarith) (by linarith)
    hκ0 hκ1
  rw [show 1 + (t - 1) = t by ring] at h
  unfold blockGatePsi
  linarith

/-- **The pointwise comparison** `φ(t) ≤ C' ψ(t)` on `[0, Q]`. -/
theorem phi_le_exactCoeff_psi {θ κ Q t : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (ht : 0 ≤ t) (htQ : t ≤ Q) :
    blockGatePhi θ t ≤ exactCoeff θ κ Q * blockGatePsi κ t := by
  have hψ0 : 0 ≤ blockGatePsi κ t := concavePowerGap_nonneg hκ0.le hκ1.le ht
  rcases le_or_gt t 1 with ht1 | ht1
  · have h := powerGap_le_curvature hκ0 hκ1 hθ (le_refl 1) ht ht1
    rw [Real.one_rpow, mul_one] at h
    calc blockGatePhi θ t = powerGap θ t := rfl
      _ ≤ θ * (θ - 1) / (κ * (1 - κ)) * concavePowerGap κ t := h
      _ ≤ exactCoeff θ κ Q * blockGatePsi κ t :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hψ0
  · have hψ := psi_pos hκ0 hκ1 ht1
    have hr := blockGate_ratio_mono hθ hκ0 hκ1 t Q ht1 htQ
    calc blockGatePhi θ t = blockGatePhi θ t / blockGatePsi κ t * blockGatePsi κ t := by
          field_simp
      _ ≤ blockGatePhi θ Q / blockGatePsi κ Q * blockGatePsi κ t :=
          mul_le_mul_of_nonneg_right hr hψ.le
      _ ≤ exactCoeff θ κ Q * blockGatePsi κ t :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) hψ.le

/-- **The one-coordinate estimate with the exact coefficient**: for `0 < s < R < d`, `|X| = Q > 1`
and `‖f‖_R = 1`, `‖f‖_d^d - 1 ≤ C' (1 - ‖f‖_s^d)` with `C' = exactCoeff (d/R) (s/R) Q`. -/
theorem exact_deficit {X : Type*} [Fintype X] [Nonempty X] {d : ℕ} {s R : ℝ} (hs : 0 < s)
    (hsR : s < R) (hRd : R < d) (hQ : 1 < (Fintype.card X : ℝ)) {f : X → ℝ}
    (hn : (FiniteLaw.uniform X).lpNorm R f = 1) :
    (FiniteLaw.uniform X).lpNorm d f ^ d - 1 ≤
      exactCoeff ((d : ℝ) / R) (s / R) (Fintype.card X) *
        (1 - (FiniteLaw.uniform X).lpNorm s f ^ d) := by
  have hR : 0 < R := hs.trans hsR
  have hd0 : (0 : ℝ) < d := hR.trans hRd
  have hd : d ≠ 0 := by
    intro h
    rw [h] at hd0
    simp at hd0
  set μ := FiniteLaw.uniform X
  set Q : ℝ := (Fintype.card X : ℝ) with hQdef
  set θ : ℝ := (d : ℝ) / R with hθdef
  set κ : ℝ := s / R with hκdef
  have hθ : 1 < θ := (one_lt_div hR).mpr hRd
  have hκ0 : 0 < κ := div_pos hs hR
  have hκ1 : κ < 1 := (div_lt_one hR).mpr hsR
  set w : X → ℝ := fun x => |f x| ^ R with hwdef
  have hw0 (x : X) : 0 ≤ w x := Real.rpow_nonneg (abs_nonneg _) _
  have hEw : μ.expect w = 1 := by
    have h := μ.lpNorm_rpow hR.ne' f
    rw [hn, Real.one_rpow] at h
    exact h.symm
  have hwQ (x : X) : w x ≤ Q := by
    have hsum : (∑ y, w y) / Q = 1 := by
      rw [← hEw]
      exact (FiniteLaw.expect_uniform w).symm
    have hsum' : ∑ y, w y = Q := by
      have hQ0 : Q ≠ 0 := by linarith
      field_simp at hsum
      linarith
    rw [← hsum']
    exact Finset.single_le_sum (fun y _ => hw0 y) (Finset.mem_univ x)
  have hpow (q : ℝ) (x : X) : w x ^ (q / R) = |f x| ^ q := by
    rw [hwdef, ← Real.rpow_mul (abs_nonneg _)]
    congr 1
    field_simp
  have hmd : μ.expect (fun x => w x ^ θ) = μ.moment d f := by
    unfold FiniteLaw.moment
    congr 1
    funext x
    exact hpow d x
  have hms : μ.expect (fun x => w x ^ κ) = μ.moment s f := by
    unfold FiniteLaw.moment
    congr 1
    funext x
    exact hpow s x
  -- the averaged comparison
  have hgap : μ.moment d f - 1 ≤ exactCoeff θ κ Q * (1 - μ.moment s f) := by
    have hpt (x : X) := phi_le_exactCoeff_psi hθ hκ0 hκ1 (Q := Q) (hw0 x) (hwQ x)
    have hE := μ.expect_mono hpt
    have hl : μ.expect (fun x => blockGatePhi θ (w x)) = μ.moment d f - 1 := by
      unfold blockGatePhi
      simp only [FiniteLaw.expect_sub, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
        FiniteLaw.expect_const, hEw, hmd]
      ring
    have hr : μ.expect (fun x => exactCoeff θ κ Q * blockGatePsi κ (w x)) =
        exactCoeff θ κ Q * (1 - μ.moment s f) := by
      rw [FiniteLaw.expect_const_mul]
      unfold blockGatePsi
      simp only [FiniteLaw.expect_sub, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
        FiniteLaw.expect_const, hEw, hms]
      ring
    rw [hl, hr] at hE
    exact hE
  -- `‖f‖_d^d` is the `d`-th moment, `‖f‖_s^d ≤ ‖f‖_s^s`
  have hdd : μ.lpNorm d f ^ d = μ.moment d f := by
    rw [μ.lpNorm_nat_pow hd, μ.moment_nat]
  have hms1 : μ.moment s f ≤ 1 := by
    have hmono := μ.lpNorm_mono hs hsR.le f
    rw [hn] at hmono
    have h := Real.rpow_le_rpow (μ.lpNorm_nonneg s f) hmono hs.le
    rwa [μ.lpNorm_rpow hs.ne', Real.one_rpow] at h
  have hsd : μ.lpNorm s f ^ d ≤ μ.moment s f := by
    have hnorm : μ.lpNorm s f ^ d = μ.moment s f ^ ((d : ℝ) / s) := by
      unfold FiniteLaw.lpNorm
      rw [← Real.rpow_natCast, ← Real.rpow_mul (μ.moment_nonneg s f)]
      congr 1
      field_simp
    rw [hnorm]
    have hds : 1 ≤ (d : ℝ) / s := (one_le_div hs).mpr (hsR.trans hRd).le
    rcases (μ.moment_nonneg s f).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow (by linarith)]
    · have h := Real.rpow_le_rpow_of_exponent_ge hpos hms1 hds
      rwa [Real.rpow_one] at h
  rw [hdd]
  calc μ.moment d f - 1 ≤ exactCoeff θ κ Q * (1 - μ.moment s f) := hgap
    _ ≤ exactCoeff θ κ Q * (1 - μ.lpNorm s f ^ d) :=
        mul_le_mul_of_nonneg_left (by linarith) (exactCoeff_nonneg hθ hκ0 hκ1)

/-- The two-component mixture weights `(1 - t, t)` on `Bool` (`true` = good, `false` = bad). -/
noncomputable def twoWeights (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : FiniteLaw Bool where
  weight b := if b then 1 - t else t
  nonneg b := by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> linarith
  total := by simp

/-- **The final sentence of `lem:density:typed-mixture`, with the exact coefficient** `C'`: a
packet `(1 - t) good + t bad` on `d` slots, `good` with unit mixed `L^s` and uniform marginals,
`bad` with uniform marginals, `|X| ≥ 2`, `t (1 + C') ≤ 1`, has unit mixed `L^R`. -/
theorem exact_typed_mixture {X : Type*} [Fintype X] [Nonempty X] {d : ℕ} {s R : ℝ}
    (hs : 0 < s) (hsR : s < R) (hRd : R < d) (hQ : 2 ≤ Fintype.card X)
    {good bad packet : FiniteLaw (Fin d → X)} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hgood : blockGateUnitMixed good s) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    (hgate : t * (1 + exactCoeff ((d : ℝ) / R) (s / R) (Fintype.card X)) ≤ 1) :
    blockGateUnitMixed packet R := by
  have hR : 0 < R := hs.trans hsR
  have hd0 : (0 : ℝ) < d := hR.trans hRd
  have hNe : Nonempty (Fin d) := ⟨⟨0, by exact_mod_cast hd0⟩⟩
  have hQ1 : (1 : ℝ) < Fintype.card X := by
    have : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hQ
    linarith
  set C := exactCoeff ((d : ℝ) / R) (s / R) (Fintype.card X) with hCdef
  have hC0 : 0 ≤ C := exactCoeff_nonneg ((one_lt_div hR).mpr hRd) (div_pos hs hR)
    ((div_lt_one hR).mpr hsR)
  set wts := twoWeights t ht0 ht1 with hwts
  set laws : Bool → FiniteLaw (Fin d → X) := fun b => if b then good else bad with hlaws
  set r : Bool → ℝ := fun b => if b then s else (d : ℝ) with hr
  set Cs : Bool → ℝ := fun b => if b then 0 else C with hCs
  have hcard : (Fintype.card (Fin d) : ℝ) = d := by rw [Fintype.card_fin]
  have hmix := mixedLpBound_typed_mixture wts laws r Cs hs hsR
    (fun b => by cases b <;> simp only [hr, Bool.false_eq_true, ↓reduceIte] <;> linarith)
    (fun b => by
      cases b
      · simp only [hlaws, hr, Bool.false_eq_true, ↓reduceIte]
        have h := mixedLpBound_of_uniform_marginals bad hbad
        rwa [hcard] at h
      · simp only [hlaws, hr, ↓reduceIte]
        exact hgood.2)
    (by
      have hfilt1 : Finset.univ.filter (fun b : Bool => R < r b) = {false} := by
        ext b
        cases b <;> simp [hr, hRd, not_lt.mpr hsR.le]
      have hfilt2 : Finset.univ.filter (fun b : Bool => r b ≤ s) = {true} := by
        ext b
        cases b <;> simp [hr, not_le.mpr (hsR.trans hRd)]
      rw [hfilt1, hfilt2, Finset.sum_singleton, Finset.sum_singleton]
      simp only [hwts, twoWeights, hCs, Bool.false_eq_true, ↓reduceIte]
      linarith)
    (fun f _ hn b hb => by
      cases b
      · simp only [hr, hCs, Bool.false_eq_true, ↓reduceIte] at hb ⊢
        rw [Fintype.card_fin]
        exact exact_deficit hs hsR hRd hQ1 hn
      · simp only [hr, ↓reduceIte] at hb
        linarith)
  have hlaw : packet = FiniteLaw.mixture wts laws := by
    apply FiniteLaw.ext
    intro z
    rw [hpacket]
    simp only [FiniteLaw.mixture, Fintype.sum_bool, hwts, twoWeights, hlaws, ↓reduceIte,
      Bool.false_eq_true]
  refine ⟨?_, ?_⟩
  · intro v g
    rw [hlaw]
    rw [FiniteLaw.expect_mixture]
    unfold FiniteLaw.expect
    simp only [Fintype.sum_bool, hwts, twoWeights, hlaws, ↓reduceIte, Bool.false_eq_true]
    have h1 := hgood.1 v g
    have h2 := hbad v g
    unfold FiniteLaw.expect at h1 h2
    rw [h1, h2]
    ring
  · rw [hlaw]
    exact hmix

/-- **`lem:density:joint-block-gate` without named hypotheses.** A twelve-slot packet
`(1 - t) good + t bad`, `good` of unit mixed `L^{11}`, `bad` with uniform marginals, alphabet
with `|X| ≥ 2` and `log |X| ≤ L`, `t ≤ t(β)`: if `κ_* > e^{-L(1-κ_*)}`,
`t(β)(1 + C(L)) < 1` and `t(β)(1 + θ_*(θ_*-1)/(κ_*(1-κ_*))) ≤ 1`, the packet has unit mixed
`L^{R_*}`. -/
theorem exact_joint_block_gate {X : Type*} [Fintype X] [Nonempty X]
    (hQ : 2 ≤ Fintype.card X) {L : ℝ} (hL : Real.log (Fintype.card X) ≤ L)
    {good bad packet : FiniteLaw (Fin 12 → X)} {t tβ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htβ : t ≤ tβ)
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    (hk : Real.exp (-(L * (1 - blockGateKappa))) < blockGateKappa)
    (hgate : tβ * (1 + (Real.exp (L * (blockGateTheta - 1)) - 1) /
      (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa))))) < 1)
    (hcurv : tβ * (1 + blockGateTheta * (blockGateTheta - 1) /
      (blockGateKappa * (1 - blockGateKappa))) ≤ 1) :
    blockGateUnitMixed packet blockGateR := by
  have hgood' : blockGateUnitMixed good blockGateS :=
    hgood.mono (by norm_num) blockGate_eleven_le_s
  have hQ2 : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) < Fintype.card X := by linarith
  have hQL : (Fintype.card X : ℝ) ≤ Real.exp L := by
    calc (Fintype.card X : ℝ) = Real.exp (Real.log (Fintype.card X)) :=
          (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hθR : ((12 : ℕ) : ℝ) / blockGateR = blockGateTheta := by
    rw [show ((12 : ℕ) : ℝ) = 12 by norm_num]
    exact blockGate_twelve_div_R
  have hκR : blockGateS / blockGateR = blockGateKappa := blockGate_s_div_R
  have hratio := blockGate_ratio_le_exp blockGate_one_lt_theta blockGate_kappa_pos
    blockGate_kappa_lt_one hQ1 hQL hk
  have htβ0 : 0 ≤ tβ := ht0.trans htβ
  apply exact_typed_mixture (d := 12) (s := blockGateS) (R := blockGateR)
    (by linarith [blockGate_eleven_le_s]) blockGate_s_lt_R
    (by rw [show ((12 : ℕ) : ℝ) = 12 by norm_num]; exact blockGate_R_lt_twelve) hQ ht0 ht1
    hgood' hbad hpacket
  rw [hθR, hκR]
  unfold exactCoeff
  have hC0 : 0 ≤ blockGateTheta * (blockGateTheta - 1) / (blockGateKappa * (1 - blockGateKappa)) := by
    have := blockGate_one_lt_theta
    have := blockGate_kappa_pos
    have := blockGate_kappa_lt_one
    exact div_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg (by linarith) (by linarith))
  rcases le_total (blockGatePhi blockGateTheta (Fintype.card X) / blockGatePsi blockGateKappa (Fintype.card X))
      (blockGateTheta * (blockGateTheta - 1) / (blockGateKappa * (1 - blockGateKappa))) with h | h
  · rw [max_eq_right h]
    calc t * (1 + blockGateTheta * (blockGateTheta - 1) / (blockGateKappa * (1 - blockGateKappa)))
        ≤ tβ * (1 + blockGateTheta * (blockGateTheta - 1) /
            (blockGateKappa * (1 - blockGateKappa))) :=
          mul_le_mul_of_nonneg_right htβ (by linarith)
      _ ≤ 1 := hcurv
  · rw [max_eq_left h]
    have hpos : 0 ≤ 1 + blockGatePhi blockGateTheta (Fintype.card X) /
        blockGatePsi blockGateKappa (Fintype.card X) := by linarith
    calc t * (1 + blockGatePhi blockGateTheta (Fintype.card X) /
          blockGatePsi blockGateKappa (Fintype.card X))
        ≤ tβ * (1 + blockGatePhi blockGateTheta (Fintype.card X) /
          blockGatePsi blockGateKappa (Fintype.card X)) := mul_le_mul_of_nonneg_right htβ hpos
      _ ≤ tβ * (1 + (Real.exp (L * (blockGateTheta - 1)) - 1) /
            (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa))))) :=
          mul_le_mul_of_nonneg_left (by linarith) htβ0
      _ ≤ 1 := hgate.le

end Sarkozy.DensityMoments

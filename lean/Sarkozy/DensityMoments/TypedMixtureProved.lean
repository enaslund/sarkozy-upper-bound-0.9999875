module

public import Sarkozy.DensityMoments.ExactTypedMixture

/-!
# WP-FI's named hypothesis `blockGateTypedMixture`, proved

`paper/sections/30_density_moment_upgrade.tex`, `lem:density:typed-mixture`, final sentence, with
the paper's exact coefficient `C_d(Q) = typedCoeff d R s d Q`, as stated in
`DensityUpgrade.blockGateTypedMixture` (`Sarkozy/DensityUpgrade/BlockGate.lean`).

* `curv_psi_le_phi`: the lower curvature comparison `c ψ(Q) ≤ φ(Q)` for `Q ≥ 1`,
  `c = λ(λ-1)/(κ(1-κ))` (the paper's value of the ratio at `1`): `φ - cψ` and its derivative
  vanish at `1`, and its second derivative `λ(λ-1)(t^{λ-2} - t^{κ-2})` is nonnegative on `[1, ∞)`.
* `exactCoeff_eq_typedCoeff`: hence the curvature floor of `exactCoeff` is inactive:
  `exactCoeff (d/R) (s/R) Q = C_d(Q)` for `Q > 1`.
* `blockGateTypedMixture_proved`: **`blockGateTypedMixture d R s`** for all `d, R, s`.
* `blockGate_joint_block_gate_proved`: WP-FI's `lem:density:joint-block-gate` without its named
  hypothesis.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityMoments

open Sarkozy.DensityUpgrade

/-- **The lower curvature comparison**: `λ(λ-1)/(κ(1-κ)) · ψ_κ(Q) ≤ φ_λ(Q)` for `Q ≥ 1`. -/
theorem curv_psi_le_phi {θ κ Q : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ) (hκ1 : κ < 1) (hQ : 1 ≤ Q) :
    θ * (θ - 1) / (κ * (1 - κ)) * blockGatePsi κ Q ≤ blockGatePhi θ Q := by
  set c := θ * (θ - 1) / (κ * (1 - κ)) with hc
  have hκκ : 0 < κ * (1 - κ) := mul_pos hκ0 (by linarith)
  have hcκ : c * (κ * (κ - 1)) = -(θ * (θ - 1)) := by
    have h1κ : (1 - κ) ≠ 0 := (show (0 : ℝ) < 1 - κ by linarith).ne'
    have hκ' : κ ≠ 0 := hκ0.ne'
    rw [hc]
    field_simp
    ring
  set G : ℝ → ℝ := fun t => blockGatePhi' θ t - c * blockGatePsi' κ t with hG
  set F : ℝ → ℝ := fun t => blockGatePhi θ t - c * blockGatePsi κ t with hF
  have hGd : ∀ t, 0 < t → HasDerivAt G (blockGatePhi'' θ t - c * blockGatePsi'' κ t) t :=
    fun t ht => (blockGate_hasDerivAt_phi' θ ht).sub ((blockGate_hasDerivAt_psi' κ ht).const_mul c)
  have hFd : ∀ t, 0 < t → HasDerivAt F (G t) t :=
    fun t ht => (blockGate_hasDerivAt_phi θ ht).sub ((blockGate_hasDerivAt_psi κ ht).const_mul c)
  have hGmono : MonotoneOn G (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
      exact (hGd t (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
      exact (hGd t (by linarith)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
      rw [(hGd t (by linarith)).deriv]
      unfold blockGatePhi'' blockGatePsi''
      have hp : t ^ (κ - 1 - 1) ≤ t ^ (θ - 1 - 1) :=
        Real.rpow_le_rpow_of_exponent_le ht1.le (by linarith)
      have key : θ * ((θ - 1) * t ^ (θ - 1 - 1)) - c * -(κ * ((κ - 1) * t ^ (κ - 1 - 1))) =
          θ * (θ - 1) * (t ^ (θ - 1 - 1) - t ^ (κ - 1 - 1)) := by
        linear_combination t ^ (κ - 1 - 1) * hcκ
      rw [key]
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have hG1 : G 1 = 0 := by
    simp only [hG, blockGatePhi', blockGatePsi', Real.one_rpow]
    ring
  have hFmono : MonotoneOn F (Set.Ici 1) := by
    apply monotoneOn_of_deriv_nonneg (convex_Ici 1)
    · intro t ht
      have ht1 : (1 : ℝ) ≤ t := Set.mem_Ici.mp ht
      exact (hFd t (by linarith)).continuousAt.continuousWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
      exact (hFd t (by linarith)).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Ici] at ht
      have ht1 : (1 : ℝ) < t := Set.mem_Ioi.mp ht
      rw [(hFd t (by linarith)).deriv]
      have h := hGmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht1.le) ht1.le
      linarith
  have hF1 : F 1 = 0 := by
    simp only [hF, blockGatePhi, blockGatePsi, Real.one_rpow]
    ring
  have h := hFmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hQ) hQ
  simp only [hF] at h hF1
  linarith

/-- With `v = d` the coefficient of `lem:density:typed-mixture` is the ratio `φ(Q)/ψ(Q)`. -/
theorem typedCoeff_eq_ratio {d : ℕ} (hd : (d : ℝ) ≠ 0) (R s Q : ℝ) :
    typedCoeff d R s d Q = blockGatePhi ((d : ℝ) / R) Q / blockGatePsi (s / R) Q := by
  unfold typedCoeff blockGatePhi blockGatePsi
  rw [div_self hd, sub_self, mul_zero, Real.rpow_zero, one_mul, one_mul]

/-- **The curvature floor is inactive**: `exactCoeff (d/R) (s/R) Q = C_d(Q)` for `Q > 1`. -/
theorem exactCoeff_eq_typedCoeff {d : ℕ} {R s Q : ℝ} (hs : 0 < s) (hsR : s < R)
    (hRd : R < d) (hQ : 1 < Q) :
    exactCoeff ((d : ℝ) / R) (s / R) Q = typedCoeff d R s d Q := by
  have hR : 0 < R := hs.trans hsR
  have hd : (d : ℝ) ≠ 0 := by linarith
  have hθ : 1 < (d : ℝ) / R := (one_lt_div hR).mpr hRd
  have hκ0 : 0 < s / R := div_pos hs hR
  have hκ1 : s / R < 1 := (div_lt_one hR).mpr hsR
  rw [typedCoeff_eq_ratio hd, exactCoeff, max_eq_left]
  rw [le_div_iff₀ (psi_pos hκ0 hκ1 hQ)]
  exact curv_psi_le_phi hθ hκ0 hκ1 hQ.le

/-- **`DensityUpgrade.blockGateTypedMixture`, proved** (the final sentence of
`lem:density:typed-mixture` with the exact coefficient). -/
theorem blockGateTypedMixture_proved.{u} (d : ℕ) (R s : ℝ) :
    blockGateTypedMixture.{u} d R s := by
  intro hs1 hsR hRd X _ _ hQ good bad packet t ht0 ht1 hgood hbad hpacket hgate
  have hQ1 : (1 : ℝ) < Fintype.card X := by
    have : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hQ
    linarith
  have hs : 0 < s := by linarith
  apply exact_typed_mixture hs hsR hRd hQ ht0 ht1 hgood hbad hpacket
  rw [exactCoeff_eq_typedCoeff hs hsR hRd hQ1]
  exact hgate

/-- **WP-FI's `lem:density:joint-block-gate` without its named hypothesis.** -/
theorem blockGate_joint_block_gate_proved {X : Type*} [Fintype X] [Nonempty X]
    (hQ : 2 ≤ Fintype.card X) {L : ℝ} (hL : Real.log (Fintype.card X) ≤ L)
    {good bad packet : FiniteLaw (Fin 12 → X)} {t tβ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htβ : t ≤ tβ)
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    (hk : Real.exp (-(L * (1 - blockGateKappa))) < blockGateKappa)
    (hgate : tβ * (1 + (Real.exp (L * (blockGateTheta - 1)) - 1) /
      (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa))))) < 1) :
    blockGateUnitMixed packet blockGateR :=
  blockGate_joint_block_gate (blockGateTypedMixture_proved 12 blockGateR blockGateS) hQ hL ht0
    ht1 htβ hgood hbad hpacket hk hgate

end Sarkozy.DensityMoments

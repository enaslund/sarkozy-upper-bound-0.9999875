module

public import Sarkozy.Moments.Mixed
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
public import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-!
# Joint block-size moment gate (`lem:density:joint-block-gate`)

Source: `paper/sections/31_density_induction_upgrade.tex`, Lemma "Joint block-size moment
gate". Constants: `κ* = 98861/100000`, `θ* = 1014587/1000000`, `R* = 12/θ*`, `s* = κ* R*`.

Statement (first part, the one formalized here). Suppose a packet on twelve slots, a
probability law on `Fin 12 → X` with `|X| = Q` and `log Q ≤ L`, is the mixture
`(1 - t) · good + t · bad`, where `good` has unit mixed `L^11` norm, `bad` has uniform one-slot
marginals, and `t ≤ t(β)`. Then the packet has unit mixed `L^{R*}` norm provided
`t(β) (1 + (e^{L(θ*-1)} - 1)/(κ* - e^{-L(1-κ*)})) < 1` and `κ* > e^{-L(1-κ*)}`.

Contents.
* `typedCoeff d R s v Q` is the coefficient `C_v(Q)` of `lem:density:typed-mixture`.
* `blockGate_typedCoeff_twelve`: `C_12(Q) = (Q^{θ*} - θ* Q + θ* - 1)/(κ* Q + 1 - κ* - Q^{κ*})`
  for `d = v = 12`, `R = R*`, `s = s*`.
* `blockGate_ratio_mono`: this ratio is increasing on `(1, ∞)` (for any `θ > 1`,
  `0 < κ < 1`), proved by applying a monotone l'Hôpital rule twice (Cauchy mean value
  theorem); this is the paper's assertion that the coefficient is increasing in `Q`.
* `blockGate_ratio_le_exp`: for `1 < Q ≤ e^L` and `κ > e^{-L(1-κ)}`, the ratio is at most
  `(e^{L(θ-1)} - 1)/(κ - e^{-L(1-κ)})`.
* `blockGate_typedCoeff_le_gate`: the same bound for `C_12(Q)` at the paper's constants;
  `blockGate_typedCoeff_mono`: `C_12(Q)` is increasing in `Q > 1`.
* `blockGate_joint_block_gate`: the gate itself.
* `blockGate_piece_bound` (second sentence of the lemma): a block of naturals in `[X, Y)`
  with product `Q`, `log Q ≤ 570` and `(n + 1) log X > 570` has at most `n` elements and
  `log Q ≤ min(570, n log Y)`; `blockGate_joint_block_gate_piece` combines it with the gate.

Hypotheses. The final sentence of `lem:density:typed-mixture` is not proved here: it is the
explicit named hypothesis `blockGateTypedMixture` (a `Prop`), taken at
`d = 12`, `R = R*`, `s = s*`. Unit mixed norms (`def:density:mixed-moment`) are
`blockGateUnitMixed`, defined from the repository's `MixedLpBound` with constant `1` and
uniform coordinate marginals; as in that repository convention the test functions are
real-valued. Monotonicity in the exponent is proved (`blockGateUnitMixed.mono`), from
`MixedLpBound.mono_exponent`. The third sentence of the paper lemma (the histogram
alternative `β ↦ max(X, β)`, `L = 570k/2^16`, read from certified records) is not formalized
here.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityUpgrade

universe u

/-! ## Definitions -/

/-- `def:density:mixed-moment`: a law `μ` on `V → X` has *unit mixed `L^r` norm* if its
coordinates are uniform on `X` and `|∫ ∏_v f_v(x_v) dμ| ≤ ∏_v ‖f_v‖_{L^r(X)}` for all
(real) functions `f_v`, the norms taken for the uniform probability on `X`. -/
def blockGateUnitMixed {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]
    (μ : FiniteLaw (V → X)) (r : ℝ) : Prop :=
  HasUniformMarginals μ ∧ MixedLpBound μ r 1

/-- `def:density:mixed-moment`, last sentence: a unit mixed bound at exponent `r` holds at
every larger exponent. -/
theorem blockGateUnitMixed.mono {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]
    [Nonempty X] {μ : FiniteLaw (V → X)} {r r' : ℝ} (h : blockGateUnitMixed μ r)
    (hr : 0 < r) (hrr' : r ≤ r') : blockGateUnitMixed μ r' :=
  ⟨h.1, h.2.mono_exponent zero_le_one hr hrr'⟩

/-- The coefficient of `lem:density:typed-mixture`:
`C_v(Q) = (d/v) Q^{(v/R-1)(d/v-1)} (Q^{v/R} - (v/R)Q + v/R - 1)/(κQ + 1 - κ - Q^κ)`,
with `κ = s/R`. -/
noncomputable def typedCoeff (d R s v Q : ℝ) : ℝ :=
  d / v * Q ^ ((v / R - 1) * (d / v - 1)) *
    ((Q ^ (v / R) - v / R * Q + v / R - 1) / (s / R * Q + 1 - s / R - Q ^ (s / R)))

/-- **Named hypothesis** (`lem:density:typed-mixture`, final sentence;
`paper/sections/30_density_moment_upgrade.tex`). Let `|X| = Q ≥ 2` and `1 ≤ s < R < d`.
A mixture of a law with unit mixed `L^s` norm, of weight `1 - t`, and an arbitrary law with
uniform coordinate marginals, of weight `t`, has unit mixed `L^R` norm whenever
`t (1 + C_d(Q)) ≤ 1`, where `C_d(Q) = typedCoeff d R s d Q`. This is assumed, not proved,
in this file. -/
def blockGateTypedMixture (d : ℕ) (R s : ℝ) : Prop :=
  1 ≤ s → s < R → R < d →
    ∀ (X : Type u) [Fintype X] [Nonempty X], 2 ≤ Fintype.card X →
    ∀ (good bad packet : FiniteLaw (Fin d → X)) (t : ℝ), 0 ≤ t → t ≤ 1 →
      blockGateUnitMixed good s → HasUniformMarginals bad →
      (∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z) →
      t * (1 + typedCoeff d R s d (Fintype.card X)) ≤ 1 →
      blockGateUnitMixed packet R

/-! ## The constants -/

/-- `κ* = 98861/100000`. -/
noncomputable def blockGateKappa : ℝ := 98861 / 100000

/-- `θ* = 1014587/1000000`. -/
noncomputable def blockGateTheta : ℝ := 1014587 / 1000000

/-- `R* = 12/θ*`. -/
noncomputable def blockGateR : ℝ := 12 / blockGateTheta

/-- `s* = κ* R*`. -/
noncomputable def blockGateS : ℝ := blockGateKappa * blockGateR

theorem blockGateS_eq : blockGateS = 1694760 / 144941 := by
  unfold blockGateS blockGateR blockGateKappa blockGateTheta
  norm_num

/-- `s* ≥ 11`. -/
theorem blockGate_eleven_le_s : (11 : ℝ) ≤ blockGateS := by
  rw [blockGateS_eq]
  norm_num

theorem blockGate_s_lt_R : blockGateS < blockGateR := by
  unfold blockGateS blockGateR blockGateKappa blockGateTheta
  norm_num

theorem blockGate_R_lt_twelve : blockGateR < 12 := by
  unfold blockGateR blockGateTheta
  norm_num

theorem blockGate_one_lt_theta : 1 < blockGateTheta := by
  unfold blockGateTheta
  norm_num

theorem blockGate_kappa_pos : 0 < blockGateKappa := by
  unfold blockGateKappa
  norm_num

theorem blockGate_kappa_lt_one : blockGateKappa < 1 := by
  unfold blockGateKappa
  norm_num

theorem blockGate_twelve_div_R : 12 / blockGateR = blockGateTheta := by
  unfold blockGateR blockGateTheta
  norm_num

theorem blockGate_s_div_R : blockGateS / blockGateR = blockGateKappa := by
  unfold blockGateS blockGateR blockGateKappa blockGateTheta
  norm_num

/-! ## The coefficient at `v = d = 12` -/

/-- Numerator `φ_θ(t) = t^θ - θ t + θ - 1` of the coefficient. -/
noncomputable def blockGatePhi (θ t : ℝ) : ℝ := t ^ θ - θ * t + θ - 1

/-- Derivative of `blockGatePhi`. -/
noncomputable def blockGatePhi' (θ t : ℝ) : ℝ := θ * t ^ (θ - 1) - θ

/-- Second derivative of `blockGatePhi`. -/
noncomputable def blockGatePhi'' (θ t : ℝ) : ℝ := θ * ((θ - 1) * t ^ (θ - 1 - 1))

/-- Denominator `ψ_κ(t) = κ t + 1 - κ - t^κ` of the coefficient. -/
noncomputable def blockGatePsi (κ t : ℝ) : ℝ := κ * t + 1 - κ - t ^ κ

/-- Derivative of `blockGatePsi`. -/
noncomputable def blockGatePsi' (κ t : ℝ) : ℝ := κ - κ * t ^ (κ - 1)

/-- Second derivative of `blockGatePsi`. -/
noncomputable def blockGatePsi'' (κ t : ℝ) : ℝ := -(κ * ((κ - 1) * t ^ (κ - 1 - 1)))

/-- For `d = v = 12`, `R = R*`, `s = s*`:
`C_12(Q) = (Q^{θ*} - θ* Q + θ* - 1)/(κ* Q + 1 - κ* - Q^{κ*})`. -/
theorem blockGate_typedCoeff_twelve (Q : ℝ) :
    typedCoeff 12 blockGateR blockGateS 12 Q =
      (Q ^ blockGateTheta - blockGateTheta * Q + blockGateTheta - 1) /
        (blockGateKappa * Q + 1 - blockGateKappa - Q ^ blockGateKappa) := by
  rw [typedCoeff, blockGate_twelve_div_R, blockGate_s_div_R,
    div_self (by norm_num : (12 : ℝ) ≠ 0), sub_self, mul_zero, Real.rpow_zero, one_mul, one_mul]

theorem blockGate_hasDerivAt_phi (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (blockGatePhi θ) (blockGatePhi' θ t) t :=
  ((((Real.hasDerivAt_rpow_const (p := θ) (Or.inl ht.ne')).sub
    ((hasDerivAt_id' t).const_mul θ)).add_const θ).sub_const 1).congr_deriv
    (by rw [blockGatePhi']; ring)

theorem blockGate_hasDerivAt_phi' (θ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (blockGatePhi' θ) (blockGatePhi'' θ t) t :=
  ((Real.hasDerivAt_rpow_const (p := θ - 1) (Or.inl ht.ne')).const_mul θ).sub_const θ

theorem blockGate_hasDerivAt_psi (κ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (blockGatePsi κ) (blockGatePsi' κ t) t :=
  (((((hasDerivAt_id' t).const_mul κ).add_const 1).sub_const κ).sub
    (Real.hasDerivAt_rpow_const (p := κ) (Or.inl ht.ne'))).congr_deriv
    (by rw [blockGatePsi']; ring)

theorem blockGate_hasDerivAt_psi' (κ : ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (blockGatePsi' κ) (blockGatePsi'' κ t) t :=
  ((Real.hasDerivAt_rpow_const (p := κ - 1) (Or.inl ht.ne')).const_mul κ).const_sub κ

/-- A monotone l'Hôpital rule: if `f(a) = g(a) = 0`, `g' > 0` on `(a, ∞)` and `f'/g'` is
increasing on `(a, ∞)`, then `f/g` is increasing on `(a, ∞)`. -/
theorem blockGate_ratio_le_ratio {f g f' g' : ℝ → ℝ} {a : ℝ}
    (hf : ∀ x, a ≤ x → HasDerivAt f (f' x) x)
    (hg : ∀ x, a ≤ x → HasDerivAt g (g' x) x)
    (hfa : f a = 0) (hga : g a = 0)
    (hpos : ∀ x, a < x → 0 < g' x)
    (hmono : ∀ x y, a < x → x ≤ y → f' x / g' x ≤ f' y / g' y) :
    ∀ x y, a < x → x ≤ y → f x / g x ≤ f y / g y := by
  have fcont : ∀ u v, a ≤ u → ContinuousOn f (Set.Icc u v) := fun u v hu z hz =>
    (hf z (hu.trans hz.1)).continuousAt.continuousWithinAt
  have gcont : ∀ u v, a ≤ u → ContinuousOn g (Set.Icc u v) := fun u v hu z hz =>
    (hg z (hu.trans hz.1)).continuousAt.continuousWithinAt
  have ginc : ∀ u v, a ≤ u → u < v → g u < g v := by
    intro u v hu huv
    obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope g g' huv (gcont u v hu)
      (fun z hz => hg z (hu.trans hz.1.le))
    have hgc := hpos c (lt_of_le_of_lt hu hc.1)
    rw [eq_div_iff (sub_ne_zero.mpr huv.ne')] at hcd
    nlinarith [mul_pos hgc (sub_pos.mpr huv)]
  intro x y hx hxy
  have hgx : 0 < g x := by
    have h := ginc a x le_rfl hx
    rwa [hga] at h
  rcases hxy.lt_or_eq with hxy | hxy
  · have hgxy := ginc x y hx.le hxy
    have hgy : 0 < g y := hgx.trans hgxy
    obtain ⟨c, hc, hcx⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hx (fcont a x le_rfl)
      (fun z hz => hf z hz.1.le) g g' (gcont a x le_rfl) (fun z hz => hg z hz.1.le)
    obtain ⟨e, he, hey⟩ := exists_ratio_hasDerivAt_eq_ratio_slope f f' hxy (fcont x y hx.le)
      (fun z hz => hf z (hx.le.trans hz.1.le)) g g' (gcont x y hx.le)
      (fun z hz => hg z (hx.le.trans hz.1.le))
    have hgc := hpos c hc.1
    have hge := hpos e (hx.trans he.1)
    have hce := hmono c e hc.1 (hc.2.trans he.1).le
    rw [div_le_div_iff₀ hgc hge] at hce
    rw [hfa, hga, sub_zero, sub_zero] at hcx
    rw [div_le_div_iff₀ hgx hgy]
    have key : (f x * g y - f y * g x) * (g' c * g' e) =
        g x * (g y - g x) * (f' c * g' e - f' e * g' c) := by
      linear_combination (g y - g x) * g' e * hcx.symm - g x * g' c * hey.symm
    have hneg : (f x * g y - f y * g x) * (g' c * g' e) ≤ 0 := by
      rw [key]
      nlinarith [mul_nonneg (mul_nonneg hgx.le (sub_nonneg.mpr hgxy.le)) (sub_nonneg.mpr hce)]
    by_contra hcon
    have hprod := mul_pos (sub_pos.mpr (not_le.mp hcon)) (mul_pos hgc hge)
    linarith
  · subst hxy
    exact le_rfl

/-- The ratio `φ_θ/ψ_κ` is increasing on `(1, ∞)` when `θ > 1` and `0 < κ < 1`; in
particular `C_12(Q)` is increasing in `Q > 1`. -/
theorem blockGate_ratio_mono {θ κ : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    ∀ x y : ℝ, 1 < x → x ≤ y →
      blockGatePhi θ x / blockGatePsi κ x ≤ blockGatePhi θ y / blockGatePsi κ y := by
  have hpos'' : ∀ x : ℝ, 0 < x → 0 < blockGatePsi'' κ x := by
    intro x hx
    have hp := Real.rpow_pos_of_pos hx (κ - 1 - 1)
    rw [blockGatePsi'']
    nlinarith [mul_pos hκ0 hp]
  have hpos' : ∀ x : ℝ, 1 < x → 0 < blockGatePsi' κ x := by
    intro x hx
    have h1 := Real.rpow_lt_one_of_one_lt_of_neg hx (by linarith : κ - 1 < 0)
    rw [blockGatePsi']
    nlinarith
  have hmono2 : ∀ x y : ℝ, 1 < x → x ≤ y →
      blockGatePhi'' θ x / blockGatePsi'' κ x ≤ blockGatePhi'' θ y / blockGatePsi'' κ y := by
    intro x y hx hxy
    have hx0 : 0 < x := by linarith
    have hy0 : 0 < y := by linarith
    rw [div_le_div_iff₀ (hpos'' x hx0) (hpos'' y hy0)]
    have hsplit : ∀ z : ℝ, 0 < z → z ^ (θ - 1 - 1) = z ^ (θ - κ) * z ^ (κ - 1 - 1) := by
      intro z hz
      rw [← Real.rpow_add hz]
      congr 1
      ring
    have hab := Real.rpow_le_rpow hx0.le hxy (by linarith : (0 : ℝ) ≤ θ - κ)
    have hp := Real.rpow_pos_of_pos hx0 (κ - 1 - 1)
    have hq := Real.rpow_pos_of_pos hy0 (κ - 1 - 1)
    simp only [blockGatePhi'', blockGatePsi'']
    rw [hsplit x hx0, hsplit y hy0]
    have hc : 0 ≤ θ * (θ - 1) * (κ * (1 - κ)) :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) (mul_nonneg hκ0.le (by linarith))
    nlinarith [mul_nonneg (mul_nonneg hc (mul_pos hp hq).le) (sub_nonneg.mpr hab)]
  have hstep := blockGate_ratio_le_ratio (f := blockGatePhi' θ) (g := blockGatePsi' κ)
    (f' := blockGatePhi'' θ) (g' := blockGatePsi'' κ) (a := 1)
    (fun x hx => blockGate_hasDerivAt_phi' θ (by linarith))
    (fun x hx => blockGate_hasDerivAt_psi' κ (by linarith))
    (by simp only [blockGatePhi', Real.one_rpow]; ring)
    (by simp only [blockGatePsi', Real.one_rpow]; ring)
    (fun x hx => hpos'' x (by linarith)) hmono2
  exact blockGate_ratio_le_ratio (f := blockGatePhi θ) (g := blockGatePsi κ)
    (f' := blockGatePhi' θ) (g' := blockGatePsi' κ) (a := 1)
    (fun x hx => blockGate_hasDerivAt_phi θ (by linarith))
    (fun x hx => blockGate_hasDerivAt_psi κ (by linarith))
    (by simp only [blockGatePhi, Real.one_rpow]; ring)
    (by simp only [blockGatePsi, Real.one_rpow]; ring)
    hpos' hstep

/-- Evaluating the increasing ratio at `M ≥ Q` and dividing numerator and denominator
by `M`. -/
theorem blockGate_ratio_le_at {θ κ Q M : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hQ : 1 < Q) (hQM : Q ≤ M) (hk : M ^ (κ - 1) < κ) :
    blockGatePhi θ Q / blockGatePsi κ Q ≤ (M ^ (θ - 1) - 1) / (κ - M ^ (κ - 1)) := by
  have hM1 : 1 < M := hQ.trans_le hQM
  have hM0 : 0 < M := by linarith
  apply (blockGate_ratio_mono hθ hκ0 hκ1 Q M hQ hQM).trans
  have hMθ : M ^ θ = M ^ (θ - 1) * M := by
    conv_lhs => rw [← sub_add_cancel θ 1, Real.rpow_add hM0, Real.rpow_one]
  have hMκ : M ^ κ = M ^ (κ - 1) * M := by
    conv_lhs => rw [← sub_add_cancel κ 1, Real.rpow_add hM0, Real.rpow_one]
  have hθ1 : 1 ≤ M ^ (θ - 1) := Real.one_le_rpow hM1.le (by linarith)
  have hnum : blockGatePhi θ M ≤ M * (M ^ (θ - 1) - 1) := by
    rw [blockGatePhi, hMθ]
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ.le) (sub_nonneg.mpr hM1.le)]
  have hden : M * (κ - M ^ (κ - 1)) ≤ blockGatePsi κ M := by
    rw [blockGatePsi, hMκ]
    nlinarith
  have hD : 0 < M * (κ - M ^ (κ - 1)) := mul_pos hM0 (by linarith)
  calc blockGatePhi θ M / blockGatePsi κ M
      ≤ (M * (M ^ (θ - 1) - 1)) / (M * (κ - M ^ (κ - 1))) :=
        div_le_div₀ (mul_nonneg hM0.le (by linarith)) hnum hD hden
    _ = (M ^ (θ - 1) - 1) / (κ - M ^ (κ - 1)) := mul_div_mul_left _ _ hM0.ne'

/-- For `1 < Q ≤ e^L` and `κ > e^{-L(1-κ)}`:
`φ_θ(Q)/ψ_κ(Q) ≤ (e^{L(θ-1)} - 1)/(κ - e^{-L(1-κ)})`. -/
theorem blockGate_ratio_le_exp {θ κ Q L : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hQ : 1 < Q) (hQL : Q ≤ Real.exp L) (hk : Real.exp (-(L * (1 - κ))) < κ) :
    blockGatePhi θ Q / blockGatePsi κ Q ≤
      (Real.exp (L * (θ - 1)) - 1) / (κ - Real.exp (-(L * (1 - κ)))) := by
  have hκe : Real.exp (-(L * (1 - κ))) = Real.exp L ^ (κ - 1) := by
    rw [← Real.exp_mul]
    congr 1
    ring
  rw [hκe] at hk ⊢
  rw [Real.exp_mul L (θ - 1)]
  exact blockGate_ratio_le_at hθ hκ0 hκ1 hQ hQL hk

/-- At the paper's constants: if `1 < Q ≤ e^L` and `κ* > e^{-L(1-κ*)}`, then
`C_12(Q) ≤ (e^{L(θ*-1)} - 1)/(κ* - e^{-L(1-κ*)})`. -/
theorem blockGate_typedCoeff_le_gate {Q L : ℝ} (hQ : 1 < Q) (hQL : Q ≤ Real.exp L)
    (hk : Real.exp (-(L * (1 - blockGateKappa))) < blockGateKappa) :
    typedCoeff 12 blockGateR blockGateS 12 Q ≤
      (Real.exp (L * (blockGateTheta - 1)) - 1) /
        (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa)))) := by
  rw [blockGate_typedCoeff_twelve]
  exact blockGate_ratio_le_exp blockGate_one_lt_theta blockGate_kappa_pos blockGate_kappa_lt_one
    hQ hQL hk

/-- `C_12(Q)` at the paper's constants is increasing in `Q > 1`. -/
theorem blockGate_typedCoeff_mono {Q Q' : ℝ} (hQ : 1 < Q) (hQQ' : Q ≤ Q') :
    typedCoeff 12 blockGateR blockGateS 12 Q ≤ typedCoeff 12 blockGateR blockGateS 12 Q' := by
  rw [blockGate_typedCoeff_twelve, blockGate_typedCoeff_twelve]
  exact blockGate_ratio_mono blockGate_one_lt_theta blockGate_kappa_pos blockGate_kappa_lt_one
    Q Q' hQ hQQ'

/-! ## The gate -/

/-- `lem:density:joint-block-gate` (first part). A packet on twelve slots over an alphabet `X`
with `|X| = Q ≥ 2` and `log Q ≤ L`, equal to `(1 - t) · good + t · bad` with `good` of unit
mixed `L^11` norm, `bad` with uniform one-slot marginals, and `0 ≤ t ≤ t(β)`, `t ≤ 1`, has unit
mixed `L^{R*}` norm provided `κ* > e^{-L(1-κ*)}` and
`t(β) (1 + (e^{L(θ*-1)} - 1)/(κ* - e^{-L(1-κ*)})) < 1`.
The final sentence of `lem:density:typed-mixture` enters as the hypothesis `hmix`. -/
theorem blockGate_joint_block_gate {X : Type u} [Fintype X] [Nonempty X]
    (hmix : blockGateTypedMixture.{u} 12 blockGateR blockGateS)
    (hQ : 2 ≤ Fintype.card X) {L : ℝ} (hL : Real.log (Fintype.card X) ≤ L)
    {good bad packet : FiniteLaw (Fin 12 → X)} {t tβ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htβ : t ≤ tβ)
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    (hk : Real.exp (-(L * (1 - blockGateKappa))) < blockGateKappa)
    (hgate : tβ * (1 + (Real.exp (L * (blockGateTheta - 1)) - 1) /
      (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa))))) < 1) :
    blockGateUnitMixed packet blockGateR := by
  have hgood' : blockGateUnitMixed good blockGateS :=
    hgood.mono (by norm_num) blockGate_eleven_le_s
  have hQ2 : (2 : ℝ) ≤ Fintype.card X := by exact_mod_cast hQ
  have hQ1 : (1 : ℝ) < Fintype.card X := by linarith
  have hQL : (Fintype.card X : ℝ) ≤ Real.exp L := by
    calc (Fintype.card X : ℝ) = Real.exp (Real.log (Fintype.card X)) :=
          (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp L := Real.exp_le_exp.mpr hL
  have hC := blockGate_typedCoeff_le_gate hQ1 hQL hk
  set C := typedCoeff 12 blockGateR blockGateS 12 (Fintype.card X) with hCdef
  set G := (Real.exp (L * (blockGateTheta - 1)) - 1) /
    (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa)))) with hGdef
  have htC : t * (1 + C) ≤ 1 := by
    rcases le_or_gt 0 (1 + C) with h1C | h1C
    · have htβ0 : 0 ≤ tβ := ht0.trans htβ
      calc t * (1 + C) ≤ tβ * (1 + C) := mul_le_mul_of_nonneg_right htβ h1C
        _ ≤ tβ * (1 + G) := mul_le_mul_of_nonneg_left (by linarith) htβ0
        _ ≤ 1 := hgate.le
    · nlinarith
  have hcast : ((12 : ℕ) : ℝ) = 12 := by norm_num
  apply hmix (blockGate_eleven_le_s.trans' (by norm_num)) blockGate_s_lt_R
    (by rw [hcast]; exact blockGate_R_lt_twelve) X hQ good bad packet t ht0 ht1 hgood' hbad
    hpacket
  rw [hcast]
  exact htC

/-! ## The piece bound for `L` -/

/-- `lem:density:joint-block-gate`, second sentence. Let a block be a finite set `B` of
naturals (the primes of the block) inside a piece `[X, Y)`, `0 < X`, `1 ≤ Y`, whose product
`Q` satisfies the block budget `log Q ≤ 570`. If `(n + 1) log X > 570`, then the block has at
most `n` elements and `log Q ≤ min(570, n log Y)`, so `L = min(570, n log Y)` may be used in
`blockGate_joint_block_gate`. Primality is not used. -/
theorem blockGate_piece_bound (B : Finset ℕ) {X Y : ℝ} {n : ℕ}
    (hX : 0 < X) (hY : 1 ≤ Y)
    (hmem : ∀ p ∈ B, X ≤ (p : ℝ) ∧ (p : ℝ) < Y)
    (hbudget : Real.log (∏ p ∈ B, (p : ℝ)) ≤ 570)
    (hn : 570 < (n + 1) * Real.log X) :
    B.card ≤ n ∧ Real.log (∏ p ∈ B, (p : ℝ)) ≤ min 570 (n * Real.log Y) := by
  have hpos : ∀ p ∈ B, (0 : ℝ) < p := fun p hp => hX.trans_le (hmem p hp).1
  have hlog : Real.log (∏ p ∈ B, (p : ℝ)) = ∑ p ∈ B, Real.log p :=
    Real.log_prod (fun p hp => (hpos p hp).ne')
  have hlow : (B.card : ℝ) * Real.log X ≤ Real.log (∏ p ∈ B, (p : ℝ)) := by
    rw [hlog]
    have h : ∑ _p ∈ B, Real.log X ≤ ∑ p ∈ B, Real.log (p : ℝ) :=
      Finset.sum_le_sum (fun p hp => Real.log_le_log hX (hmem p hp).1)
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hup : Real.log (∏ p ∈ B, (p : ℝ)) ≤ (B.card : ℝ) * Real.log Y := by
    rw [hlog]
    have h : ∑ p ∈ B, Real.log (p : ℝ) ≤ ∑ _p ∈ B, Real.log Y :=
      Finset.sum_le_sum (fun p hp => Real.log_le_log (hpos p hp) (hmem p hp).2.le)
    rwa [Finset.sum_const, nsmul_eq_mul] at h
  have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
  have hlogX : 0 < Real.log X := by
    by_contra h
    have h' := mul_le_mul_of_nonneg_left (not_lt.mp h) hn0
    linarith
  have hcard : B.card ≤ n := by
    by_contra h
    have h' : (n : ℝ) + 1 ≤ B.card := by exact_mod_cast Nat.succ_le_of_lt (not_le.mp h)
    have h'' := mul_le_mul_of_nonneg_right h' hlogX.le
    linarith
  refine ⟨hcard, le_min hbudget (hup.trans ?_)⟩
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (Real.log_nonneg hY)

/-- The gate with the piece choice `L = min(570, n log Y)`: the alphabet `A` of the packet has
`|A| = ∏_{p ∈ B} p` for a block `B` in the piece `[X, Y)` with `log ∏_{p ∈ B} p ≤ 570` and
`(n + 1) log X > 570`. -/
theorem blockGate_joint_block_gate_piece {A : Type u} [Fintype A] [Nonempty A]
    (hmix : blockGateTypedMixture.{u} 12 blockGateR blockGateS)
    (B : Finset ℕ) {X Y : ℝ} {n : ℕ} (hX : 0 < X) (hY : 1 ≤ Y)
    (hmem : ∀ p ∈ B, X ≤ (p : ℝ) ∧ (p : ℝ) < Y)
    (hA : (Fintype.card A : ℝ) = ∏ p ∈ B, (p : ℝ))
    (hbudget : Real.log (∏ p ∈ B, (p : ℝ)) ≤ 570)
    (hn : 570 < (n + 1) * Real.log X) (hQ : 2 ≤ Fintype.card A)
    {good bad packet : FiniteLaw (Fin 12 → A)} {t tβ : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (htβ : t ≤ tβ)
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z)
    (hk : Real.exp (-(min 570 (n * Real.log Y) * (1 - blockGateKappa))) < blockGateKappa)
    (hgate : tβ * (1 + (Real.exp (min 570 (n * Real.log Y) * (blockGateTheta - 1)) - 1) /
      (blockGateKappa - Real.exp (-(min 570 (n * Real.log Y) * (1 - blockGateKappa))))) < 1) :
    blockGateUnitMixed packet blockGateR := by
  have hL : Real.log (Fintype.card A) ≤ min 570 (n * Real.log Y) := by
    rw [hA]
    exact (blockGate_piece_bound B hX hY hmem hbudget hn).2
  exact blockGate_joint_block_gate hmix hQ hL ht0 ht1 htβ hgood hbad hpacket hk hgate

end Sarkozy.DensityUpgrade

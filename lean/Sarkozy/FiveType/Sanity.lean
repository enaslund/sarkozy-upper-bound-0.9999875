module

public import Sarkozy.FiveType.Criteria
public import Sarkozy.FiveType.PolarizationTensor
public import Sarkozy.FiveType.FoldDataRemark

/-!
# A toy five-type datum (non-vacuity of `def:five-type-datum` and of `lem:five-type`(b), (c), (f))

The uniform datum on `𝔛 = Fin 2`: `ν`, `ν^b`, `Γ`, `π_E`, `π_F`, `π_L` are uniform (independent
objects), and `T_E^b = T_F^b = 1`. Every field of `Datum` is proved. The hypotheses of (b)
(`e_F = e_E = 0`), (c) (`H = 1`, `β = q⊥ = ρ_E = 0`, `t_Y = 1/2`) and (f) (`H = 1`,
`υ = ε_T = ε_E = κ_J = 0`, `t_Y = 1/2`) hold, including the new structures `FoldData` and
`JointData`, and the three criteria give reflection positivity at every chamber cut
(`toy_full_norm_rp`, `toy_schur_rp`, `toy_joint_rp`). The root branch of the hypothesis is used in
`toy_full_norm_rp_root`: the uniform root is i.i.d., hence positive at `ϑ₀`, so the root envelope
holds with `δ = 0` and `a_L = 1`.

`toy_polarization` and `toy_polarization_c` apply `lem:tr:polarization`(a), (b) and (c) (two
blocks).

The instance is degenerate (all covariances vanish); it shows that the hypotheses are consistent,
not that the bounds are sharp.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType.Sanity

open Sarkozy Sarkozy.FiveType

/-- **The uniform five-type datum on `Fin 2`.** -/
noncomputable def toyDatum : Datum (Fin 2) where
  nu := FiniteLaw.uniform (Fin 2)
  nub := fun _ => FiniteLaw.uniform (Fin 2)
  Gam := FiniteLaw.uniform (Fin 2 → Fin 2)
  Gam_weight := by intro ω; simp [FiniteLaw.uniform]; norm_num
  Gam_symm := fun _ => rfl
  piE := FiniteLaw.uniform (Fin 3 → Fin 2)
  TE := fun _ _ _ => 1
  TE_nonneg := fun _ _ _ => zero_le_one
  piE_weight := by intro ω; simp [FiniteLaw.uniform]; norm_num
  piE_exch := fun _ _ => rfl
  piF := FiniteLaw.uniform (Fin 3 → Fin 2)
  TF := fun _ _ _ => 1
  TF_nonneg := fun _ _ _ => zero_le_one
  piF_weight := by intro ω; simp [FiniteLaw.uniform]; norm_num
  piL := FiniteLaw.uniform (ZMod 6 → Fin 2)
  piL_inv := fun _ _ => rfl

/-- The kernel `1` is the projection `J`. -/
theorem kf_one (μ : FiniteLaw (Fin 2)) (Φ Ψ : Fin 2 → ℝ) :
    kf μ (fun _ _ => 1) Φ Ψ = μ.expect Φ * μ.expect Ψ := by
  simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  ring

theorem normBound_one (μ : FiniteLaw (Fin 2)) : NormBound μ (fun _ _ => 1) 0 := by
  intro Φ Ψ
  rw [kf_one, sub_self, abs_zero, zero_mul, zero_mul]

theorem exact_one (μ : FiniteLaw (Fin 2)) : ExactMarginals μ (fun _ _ => 1) := by
  constructor <;> intro x _ <;> simp only [kone, kone', mul_one, μ.total]

theorem nrm_zero (μ : FiniteLaw (Fin 2)) : nrm μ (fun _ => 0) = 0 := by
  simp [nrm, ip]

theorem foldData_one (μ : FiniteLaw (Fin 2)) : FoldData μ (fun _ _ => 1) 1 0 0 := by
  have hk1 : kone μ (fun _ _ => 1) = fun _ => 1 := by
    funext x; simp [kone, μ.total]
  have hk2 : kone' μ (fun _ _ => 1) = fun _ => 1 := by
    funext x; simp [kone', μ.total]
  have hc1 : cen μ (kone μ (fun _ _ => 1)) = fun _ => 0 := by
    rw [hk1]; funext x; simp [cen]
  have hc2 : cen μ (kone' μ (fun _ _ => 1)) = fun _ => 0 := by
    rw [hk2]; funext x; simp [cen]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [kf_one]; simp
  · rw [kf_one]; simp
  · rw [hc1, nrm_zero]
  · rw [hc2, nrm_zero]
  · intro Φ Ψ hΦ _
    rw [kf_one, hΦ]
    simp

/-- The joint data of the kernel `1`: `m = 1`, `φ₀ = φ₂ = 𝟙`, `C = R = 0`. -/
noncomputable def jointData_one (μ : FiniteLaw (Fin 2)) :
    JointData μ (fun _ _ => 1) (fun _ _ => 1) 1 0 0 0 0 where
  m := 1
  φ0 := fun _ => 1
  φ2 := fun _ => 1
  C := fun _ _ => 0
  R := fun _ _ => 0
  decomp := fun _ _ => by ring
  m_lower := by norm_num
  m_upper := le_rfl
  mean0 := μ.expect_const 1
  mean2 := μ.expect_const 1
  dev0 := by simp [nrm, ip]
  dev2 := by simp [nrm, ip]
  annC := ⟨fun _ _ => by simp [kone], fun _ _ => by simp [kone']⟩
  annR := ⟨fun _ _ => by simp [kone], fun _ _ => by simp [kone']⟩
  normR := fun _ _ => by simp [kf]
  lowerE := fun Φ => by simp only [eform, kf_one]; nlinarith
  joint := fun Φ Ψ => by
    have h0 : kf μ (fun _ _ => (0 : ℝ)) Φ Ψ = 0 := by simp [kf]
    have h1 := sq (μ.expect Φ)
    have h2 := sq (μ.expect Ψ)
    simp only [eform, kf_one, h0, neg_zero, zero_mul]
    linarith

/-- The toy weights `(a_L, a_D, a_S, a_R, a_C)`. -/
def toyWeights (aL aD aS aR aC : ℝ) : Ty → ℝ
  | .L => aL
  | .D => aD
  | .S => aS
  | .R => aR
  | .C => aC

/-- **(b) applies to the toy datum**, with all of `D, S, R, C` present. -/
theorem toy_full_norm_rp : RPAll (toyDatum.Q (toyWeights 0 1 1 1 1)) := by
  refine toyDatum.full_norm_rp (toyWeights 0 1 1 1 1)
    (fun t => by cases t <;> norm_num [toyWeights])
    le_rfl (fun _ _ => normBound_one _) (fun _ _ => normBound_one _)
    (by norm_num [toyWeights]) (by norm_num [toyWeights]) (by norm_num [toyWeights]) (δ := 0)
    (Or.inl rfl)

/-- The uniform root is the i.i.d. law. -/
theorem compL_eq_iid : toyDatum.compL = ReflectionCut.iidLaw (FiniteLaw.uniform (Fin 2)) := by
  apply LinearMap.ext
  intro f
  change ∑ Ψ, (FiniteLaw.uniform (ZMod 6 → Fin 2)).weight Ψ * f Ψ =
    ∑ Ψ, (∏ i, (FiniteLaw.uniform (Fin 2)).weight (Ψ i)) * f Ψ
  refine Finset.sum_congr rfl fun Ψ _ => ?_
  simp only [FiniteLaw.uniform, Finset.prod_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_fin, ZMod.card]
  norm_num

/-- **The root branch**: the uniform root is positive at `ϑ₀`, so the root envelope holds with
`δ = 0`, and (b) applies with `a_L = 1`. -/
theorem toy_full_norm_rp_root : RPAll (toyDatum.Q (toyWeights 1 1 1 1 1)) := by
  have hpos : (chamberCut 0).Positive toyDatum.compL := by
    rw [compL_eq_iid]; exact ReflectionCut.iidLaw_positive _ _
  have henv : (chamberCut 0).Below (-(0 : ℝ) • toyDatum.compF 0) toyDatum.compL := by
    change (chamberCut 0).Positive (toyDatum.compL - -(0 : ℝ) • toyDatum.compF 0)
    rwa [neg_zero, zero_smul, sub_zero]
  exact toyDatum.full_norm_rp (toyWeights 1 1 1 1 1) (fun t => by cases t <;> norm_num [toyWeights])
    le_rfl (fun _ _ => normBound_one _) (fun _ _ => normBound_one _)
    (by norm_num [toyWeights]) (by norm_num [toyWeights]) (by norm_num [toyWeights])
    (Or.inr ⟨henv, by norm_num [toyWeights]⟩)

/-- **(c) applies to the toy datum** (`H = 1`, `t_Y = 1/2`, `M = 2`, `s = k = 1`). -/
theorem toy_schur_rp : RPAll (toyDatum.Q (toyWeights 0 1 2 1 1)) := by
  refine toyDatum.schur_rp (toyWeights 0 1 2 1 1) (fun t => by cases t <;> norm_num [toyWeights])
    (by norm_num [toyWeights]) le_rfl (fun _ _ => exact_one _) (fun _ _ => normBound_one _)
    (fun _ _ => foldData_one _) (tY := 1 / 2) (by norm_num) (by norm_num [toyWeights])
    (by norm_num) (by norm_num [toyWeights]) (by norm_num [toyWeights]) (δ := 0) (Or.inl rfl)

/-- **(f) applies to the toy datum** (`H = 1`, `t_Y = 1/2`, `M = 2`, `s = k = 1`). -/
theorem toy_joint_rp : RPAll (toyDatum.Q (toyWeights 0 1 2 1 1)) := by
  refine toyDatum.joint_schur_rp (toyWeights 0 1 2 1 1)
    (fun t => by cases t <;> norm_num [toyWeights])
    (by norm_num [toyWeights]) le_rfl le_rfl (fun _ _ => exact_one _)
    (fun _ _ => jointData_one _) (tY := 1 / 2) (by norm_num) (by norm_num)
    (by norm_num [toyWeights]) (by norm_num [toyWeights]) (by norm_num [toyWeights]) (δ := 0)
    (Or.inl rfl)

/-- **`lem:tr:polarization`(a), (b) apply to the toy datum** (`e_F = e_E = 0`, `ε = 0`). -/
theorem toy_polarization :
    (chamberCut 0).Below toyDatum.QF (toyDatum.QE 0) ∧
      (chamberCut 0).Below (-toyDatum.QF) (toyDatum.QE 0) :=
  toyDatum.polarization_b (fun _ _ => normBound_one _) (fun _ _ => normBound_one _)
    (by norm_num)

/-- **`lem:tr:polarization`(c) applies to two toy blocks.** -/
theorem toy_polarization_c :
    (chamberCut 0).Below
      (tensorLaw (fun _ : Fin 2 => toyDatum.compF 1) +
        tensorLaw (fun _ : Fin 2 => toyDatum.compF 2))
      (tensorLaw (fun _ : Fin 2 => toyDatum.QE 0)) :=
  polarization_c_second (fun _ => toyDatum) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ _ _ => normBound_one _) (fun _ _ _ => normBound_one _) (fun _ => by norm_num)

/-- **`rem:five-type-fold-data` applies to the kernel `1`** (`H = R_m = 1`, `υ = ρ_F = 0`). -/
theorem toy_foldData_of_marginals (μ : FiniteLaw (Fin 2)) :
    FoldData μ (fun _ _ => 1) 1 (1 * 0) (1 * (1 * 0 + 0 ^ 2)) := by
  have hm : kf μ (fun _ _ => (1 : ℝ)) (fun _ => 1) (fun _ => 1) = 1 := by
    rw [kf_one]; simp
  have hL : ∀ x, margL μ (fun _ _ => 1) x = 1 := fun x => by
    simp only [margL, hm, div_one, kone, mul_one, μ.total]
  have hR : ∀ x, margR μ (fun _ _ => 1) x = 1 := fun x => by
    simp only [margR, hm, div_one, kone', mul_one, μ.total]
  have hc : covKernel μ (fun _ _ => 1) = fun _ _ => 0 := by
    funext x y; simp only [covKernel, hm, div_one, hL, hR, mul_one, sub_self]
  refine foldData_of_marginals (by norm_num) (by rw [hm]; norm_num) (by rw [hm])
    (fun _ _ => zero_le_one) (fun x _ => by rw [hL]) (fun x _ => by rw [hR]) ?_ ?_ le_rfl ?_
  · simp only [hL, sub_self]; exact le_of_eq (nrm_zero μ)
  · simp only [hR, sub_self]; exact le_of_eq (nrm_zero μ)
  · intro h h'
    rw [hc]
    simp [kf]

end Sarkozy.FiveType.Sanity

module

public import Sarkozy.PartVLaws.LayerCaps
public import Sarkozy.PartVLaws.SchurRows
public import Sarkozy.PartVLaws.TailInputs

@[expose] public section





namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

/-! ## One-point spaces -/

theorem weight_eq_one {Ω : Type*} [Fintype Ω] [Subsingleton Ω] (μ : FiniteLaw Ω) (ω : Ω) :
    μ.weight ω = 1 := by
  have h := μ.total
  rwa [Fintype.sum_subsingleton _ ω] at h

/-- **On a one-point configuration space every nonnegative functional is reflection positive.** -/
theorem positive_of_subsingleton {V X : Type*} [Fintype V] [DecidableEq V] [Subsingleton X]
    (c : ReflectionCut V) (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hL : ∀ f : (V → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ L f) : c.Positive L := by
  have key : ∀ (F G : (c.Half → X) → ℝ), c.form L F G =
      L (fun z => F (fun v => z v.1) * G (fun v => z v.1)) := by
    intro F G
    unfold ReflectionCut.form
    congr 1
    funext z
    rw [Subsingleton.elim (fun v : c.Half => z (c.flip v.1)) (fun v => z v.1)]
  constructor
  · intro F G
    rw [key, key]
    congr 1
    funext z
    ring
  · intro F
    rw [key]
    exact hL _ fun z => mul_self_nonneg _

theorem lawL_nonneg {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) (hf : ∀ z, 0 ≤ f z) :
    0 ≤ lawL μ f :=
  μ.expect_nonneg hf

/-- The kernels of a datum on a one-point set are `1`. -/
theorem datum_TF_eq_one {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] [Subsingleton 𝔛] (D : Datum 𝔛)
    (b x y : 𝔛) : D.TF b x y = 1 := by
  have h := D.piF_weight ![x, b, y]
  simp only [weight_eq_one, one_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact h.symm

theorem datum_TE_eq_one {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] [Subsingleton 𝔛] (D : Datum 𝔛)
    (b x y : 𝔛) : D.TE b x y = 1 := by
  have h := D.piE_weight ![x, b, y]
  simp only [weight_eq_one, one_mul, Matrix.cons_val_one, Matrix.cons_val_zero,
    Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at h
  exact h.symm

/-- `‖T - J‖ ≤ e` for every `e ≥ 0` on a one-point space when `T = 1`. -/
theorem normBound_one {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] [Subsingleton 𝔛]
    (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ∀ x y, T x y = 1) {e : ℝ} (he : 0 ≤ e) :
    NormBound μ T e := by
  intro Φ Ψ
  have hne : Nonempty 𝔛 := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := μ.total
    simp at this
  obtain ⟨x₀⟩ := hne
  have hk : kf μ T Φ Ψ - μ.expect Φ * μ.expect Ψ = 0 := by
    unfold kf FiniteLaw.expect
    rw [Fintype.sum_subsingleton _ x₀, Fintype.sum_subsingleton _ x₀,
      Fintype.sum_subsingleton _ x₀, Fintype.sum_subsingleton _ x₀, weight_eq_one, hT]
    ring
  rw [hk, abs_zero]
  exact mul_nonneg (mul_nonneg he (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-! ## The toy upper block -/

/-- The toy field laws: one label, so every law is the point mass. -/
noncomputable def toyF : UpperFieldLaws Unit where
  two _ _ := FiniteLaw.uniform _
  one _ _ := FiniteLaw.uniform _

theorem toy_graphInv2 : GraphInv toyF.two := by
  intro f₀ f₁ π _ g
  refine FiniteLaw.expect_congr _ fun y => ?_
  rw [Subsingleton.elim (y ∘ π) y]

theorem toy_graphInv1 : GraphInv toyF.one := by
  intro f₀ f₁ π _ g
  refine FiniteLaw.expect_congr _ fun y => ?_
  rw [Subsingleton.elim (y ∘ π) y]

theorem toy_suppExt2 : SuppExt toyF.two where
  left _ y _ _ _ := ⟨y, by rw [weight_eq_one]; exact one_ne_zero, fun _ _ => rfl⟩
  right _ y _ _ _ := ⟨y, by rw [weight_eq_one]; exact one_ne_zero, fun _ _ => rfl⟩

theorem toy_suppExt1 : SuppExt toyF.one where
  left _ y _ _ _ := ⟨y, by rw [weight_eq_one]; exact one_ne_zero, fun _ _ => rfl⟩
  right _ y _ _ _ := ⟨y, by rw [weight_eq_one]; exact one_ne_zero, fun _ _ => rfl⟩

/-- **The toy row data form five-type data.** -/
theorem toyDatumHyp : UpperDatumHyp toyF :=
  upperDatumHyp_of toyF toy_graphInv2 toy_graphInv1 toy_suppExt2 toy_suppExt1

theorem toy_rootEnv {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] [Subsingleton 𝔛] (D : Datum 𝔛)
    {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) : RootEnv D d r := by
  refine positive_of_subsingleton _ _ fun f hf => ?_
  rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have h1 : 0 ≤ D.compL f := lawL_nonneg _ f hf
  have h2 : 0 ≤ D.compF 0 f := lawL_nonneg _ f hf
  nlinarith [mul_nonneg (mul_nonneg hd hr) h2]

theorem toy_validRows {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] [Subsingleton 𝔛] (D : Datum 𝔛)
    {r f h M : ℝ} (hr : 0 ≤ r) (hf : 0 ≤ f) (hh : 0 ≤ h) (hM : 1 ≤ M) : ValidRows D r f h M :=
  Or.inl ⟨hf, hM, fun b _ => ⟨normBound_one _ _ (datum_TF_eq_one D b) (mul_nonneg hf hr),
    normBound_one _ _ (datum_TE_eq_one D b) (mul_nonneg hh hr)⟩⟩

theorem tailOrd_nonneg (f : FieldTy) :
    (0 : ℝ) ≤ (tailOrd f).d ∧ (0 : ℝ) ≤ (tailOrd f).f ∧ (0 : ℝ) ≤ (tailOrd f).h ∧
      (1 : ℝ) ≤ (tailOrd f).M := by
  cases f <;> norm_num [tailOrd, tailOrdinary, toFType]

theorem tailRes_nonneg (f : FieldTy) :
    (0 : ℝ) ≤ (tailRes f).d ∧ (0 : ℝ) ≤ (tailRes f).f ∧ (0 : ℝ) ≤ (tailRes f).h ∧
      (1 : ℝ) ≤ (tailRes f).M := by
  cases f <;> norm_num [tailRes, tailReserved, toFType]

theorem tailCap_nonneg (t₀ t₁ : PType) : 0 ≤ tailCap t₀ t₁ := by
  cases t₀ <;> cases t₁ <;> norm_num [tailCap, tailFieldCap, PType.field]

/-- **The toy inputs are valid**, with the tail datum's inputs and caps, at `r = 1/2`. -/
theorem toyValid : ValidInputs toyF toyDatumHyp (1 / 2) tailOrd tailRes tailCap where
  root20 f' := toy_rootEnv _ (tailOrd_nonneg f').1 (by norm_num)
  root21 f' := toy_rootEnv _ (tailOrd_nonneg f').1 (by norm_num)
  root10 f' := toy_rootEnv _ (tailRes_nonneg f').1 (by norm_num)
  root11 f' := toy_rootEnv _ (tailRes_nonneg f').1 (by norm_num)
  rows20 f' := toy_validRows _ (by norm_num) (tailOrd_nonneg f').2.1 (tailOrd_nonneg f').2.2.1
    (tailOrd_nonneg f').2.2.2
  rows21 f' := toy_validRows _ (by norm_num) (tailOrd_nonneg f').2.1 (tailOrd_nonneg f').2.2.1
    (tailOrd_nonneg f').2.2.2
  rows10 f' := toy_validRows _ (by norm_num) (tailRes_nonneg f').2.1 (tailRes_nonneg f').2.2.1
    (tailRes_nonneg f').2.2.2
  rows11 f' := toy_validRows _ (by norm_num) (tailRes_nonneg f').2.1 (tailRes_nonneg f').2.2.1
    (tailRes_nonneg f').2.2.2
  caps t φ := by
    refine positive_of_subsingleton _ _ fun f hf => ?_
    rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    have h1 : 0 ≤ signedIntegral (upComponent toyF (true, ⟨t, φ⟩)).weight f := by
      rw [← FiniteLaw.expect_eq_signedIntegral]
      exact FiniteLaw.expect_nonneg _ hf
    have h2 : 0 ≤ signedIntegral (upComponent toyF (false, ⟨t, φ⟩)).weight f := by
      rw [← FiniteLaw.expect_eq_signedIntegral]
      exact FiniteLaw.expect_nonneg _ hf
    have hk := tailCap_nonneg t.1 t.2
    nlinarith [mul_nonneg (mul_nonneg hk (by norm_num : (0 : ℝ) ≤ 1 / 2)) h2]

/-- **All hypotheses of `upperReference_familyPositive` hold together** (with the paper's tail
weights and inputs), so the theorem is not vacuous. -/
theorem toy_upper_familyPositive :
    TheoremC.FamilyReflectionPositive
      (signedIntegral (upperReference toyF tailWeights (by norm_num : (0 : ℝ) ≤ 1 / 2)).weight) :=
  upperReference_familyPositive toyF tailWeights (by norm_num) toyDatumHyp toyValid tailWeightsOK

/-- **(V3) in the paper's form holds in the toy**, with the tail datum's caps. -/
theorem toy_fieldLayerCaps : FieldLayerCaps toyF tailKappa (1 / 2) := by
  intro f0 f1
  refine positive_of_subsingleton _ _ fun f hf => ?_
  rw [LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  have h1 : 0 ≤ lawL (lam2 toyF f0 f1) f := lawL_nonneg _ f hf
  have h2 : 0 ≤ pushFunctional (lawL (lam1 toyF f0 f1)) Reserved.diagF f :=
    lawL_nonneg _ _ fun _ => hf _
  have hk : 0 ≤ tailKappa f0 f1 := by
    cases f0 <;> cases f1 <;> norm_num [tailKappa, tailFieldCap, toFType]
  nlinarith [mul_nonneg (mul_nonneg hk (by norm_num : (0 : ℝ) ≤ 1 / 2)) h2]

/-! ## The Schur-row data on a one-point datum -/

section SchurToy

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] [Subsingleton 𝔛]

omit [DecidableEq 𝔛] [Subsingleton 𝔛] in
theorem exists_point (μ : FiniteLaw 𝔛) : Nonempty 𝔛 := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := μ.total
  simp at this

omit [DecidableEq 𝔛] in
theorem kf_one_point (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ∀ x y, T x y = 1) :
    kf μ T (fun _ => 1) (fun _ => 1) = 1 := by
  obtain ⟨x₀⟩ := exists_point μ
  unfold kf
  rw [Fintype.sum_subsingleton _ x₀, Fintype.sum_subsingleton _ x₀, weight_eq_one, hT]
  ring

omit [DecidableEq 𝔛] in
theorem kone_one_point (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ∀ x y, T x y = 1) (x : 𝔛) :
    kone μ T x = 1 := by
  unfold kone
  rw [Fintype.sum_subsingleton _ x, weight_eq_one, hT, one_mul]

omit [DecidableEq 𝔛] in
theorem kone'_one_point (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ∀ x y, T x y = 1) (y : 𝔛) :
    kone' μ T y = 1 := by
  unfold kone'
  rw [Fintype.sum_subsingleton _ y, weight_eq_one, hT, one_mul]

omit [DecidableEq 𝔛] in
theorem margL_one_point (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ∀ x y, T x y = 1) (x : 𝔛) :
    margL μ T x = 1 := by
  unfold margL
  rw [kone_one_point μ T hT, kf_one_point μ T hT, div_one]

omit [DecidableEq 𝔛] in
theorem margR_one_point (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ∀ x y, T x y = 1) (y : 𝔛) :
    margR μ T y = 1 := by
  unfold margR
  rw [kone'_one_point μ T hT, kf_one_point μ T hT, div_one]

omit [DecidableEq 𝔛] [Subsingleton 𝔛] in
theorem nrm_zero_fun (μ : FiniteLaw 𝔛) : nrm μ (fun _ => (0 : ℝ)) = 0 := by
  unfold nrm ip
  simp

/-- **The Schur-row data hold on a one-point datum** (with `H = R_m = 1`, `υ = ρ_F = ρ_E = 0`). -/
theorem toy_schurRowData (D : Datum 𝔛) (b : 𝔛) :
    SchurRowData (D.nub b) (D.TF b) (D.TE b) 1 0 1 0 0 := by
  have hF := datum_TF_eq_one D b
  have hE := datum_TE_eq_one D b
  refine ⟨?_, ?_, fun x y => by rw [hF]; exact zero_le_one, fun x _ => ?_, fun x _ => ?_, ?_, ?_,
    fun h h' => ?_,
    ⟨fun x _ => kone_one_point _ _ hE x, fun y _ => kone'_one_point _ _ hE y⟩,
    normBound_one _ _ hE le_rfl⟩
  · rw [kf_one_point _ _ hF, inv_one]
  · rw [kf_one_point _ _ hF]
  · rw [margL_one_point _ _ hF]
  · rw [margR_one_point _ _ hF]
  · have : (fun x => margL (D.nub b) (D.TF b) x - 1) = fun _ => (0 : ℝ) := by
      funext x
      rw [margL_one_point _ _ hF, sub_self]
    rw [this, nrm_zero_fun]
  · have : (fun x => margR (D.nub b) (D.TF b) x - 1) = fun _ => (0 : ℝ) := by
      funext x
      rw [margR_one_point _ _ hF, sub_self]
    rw [this, nrm_zero_fun]
  · have hc : covKernel (D.nub b) (D.TF b) = fun _ _ => 0 := by
      funext x y
      unfold covKernel
      rw [hF, kf_one_point _ _ hF, margL_one_point _ _ hF, margR_one_point _ _ hF]
      ring
    rw [hc]
    unfold kf
    simp

/-- **`validRows_of_schurRows` applies to a one-point datum** with the tail datum's `M = 21/20`. -/
theorem toy_validRows_schur (D : Datum 𝔛) {r : ℝ} (hr : 0 < r) :
    ValidRows D r ((1 * 1 * 0 + (1 + 50 * 1 ^ 2) * 0 ^ 2) / r) (0 / r) (21 / 20) :=
  validRows_of_schurRows D hr one_pos (by norm_num) zero_le_one le_rfl (by norm_num)
    fun b _ => toy_schurRowData D b

/-- **The Schur inputs of the tail datum hold on a one-point datum** (non-vacuity of
`SchurInputs`). -/
theorem toy_schurInputs (D : Datum 𝔛) (r : ℝ) (f : FieldTy) :
    SchurInputs D r (tailOrd f) := by
  have hI := tailOrd_nonneg f
  have hM : (1 : ℝ) + 1 / 50 ≤ ((tailOrd f).M : ℝ) := by
    cases f <;> norm_num [tailOrd, tailOrdinary, toFType]
  refine ⟨1, 0, 1, 0, 0, one_pos, by norm_num, hM, zero_le_one, le_rfl, ?_, ?_,
    fun b _ => toy_schurRowData D b⟩
  · simp only [mul_zero, add_zero, zero_div, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow]
    exact hI.2.1
  · rw [zero_div]
    exact hI.2.2.1

end SchurToy

end Sarkozy.PartVLaws

module

public import Sarkozy.PartV.Protection
public import Sarkozy.PartV.LayerSwap
public import Sarkozy.PartV.Acceptance
public import Sarkozy.RecordExpansion.Multilinear
public import Sarkozy.Reflection.Bracket

@[expose] public section

/-!
# The middle frame (`def:record:frame`)

`paper/sections/20c_middle_frame.tex`, `subsec:middle-first-stage`, `def:record:frame`.

On a middle block `𝔅` with least prime `b` and `r = b^{-1/2}`, `q = r²`, the frame consists of the
reference `μ_𝔅 = μ̃_𝔅 / μ̃_𝔅(1)` of `lem:front12:reference` (V1's `middleReference`) and the
following measures, all defined *before* the common normalization by `μ̃_𝔅(1) = P(r)`
(`def:record:frame`(b)); `Diag_ι(Π⁽¹⁾_φ)` is the one-layer component of the pattern `φ` placed on
both layers (V1's `midComponent F (false, ⟨t, φ⟩)`, here `FrameData.diag t φ`):

* `Ffold = v_D r² (Diag_ι(Π⁽¹⁾_{F₁}) + Diag_ι(Π⁽¹⁾_{F₂}))`, mass `2 v_D r²` (`Ffold`);
* `Efold = v_S r² (Diag_ι(Π⁽¹⁾_{E₀}) + Diag_ι(Π⁽¹⁾_{E₁}))`, mass `2 v_S r²` (`Efold`);
* `Eadd = v_D r² (Diag_ι(Π⁽¹⁾_{E₀}) + Diag_ι(Π⁽¹⁾_{E₁}))`, mass `2 v_D r²` (`Eadd`);
* the polarization correction `G = (f₁ + h₁) r (G_e + G_o)`, `G_e = v_D r² Diag_ι(Π⁽¹⁾_{G₀₀})`,
  `G_o = v_D r² Diag_ι(Π⁽¹⁾_{G₁₁})`, mass `2 v_D (f₁ + h₁) r³` (`Gpol`, `Ge`, `Go`);
* `H`, which adds `Diag_ι(Π⁽¹⁾_{E_s})` with coefficient `2 w_S r · 3/(b - 3)` for `s = 0, 1`
  (`Hdiag`, coefficient `hCoef`), mass `12 w_S r/(b - 3)` (`= 12 w_S r³/(1 - 3q)` for `r² = 1/b`);
* `E_new` (`def:record:frame`(c)): each folded matching record of type `E_s` of
  `Efold + Eadd`, of mass `(v_S + v_D) r²`, is replaced by the measure of the same mass that is
  the image under the same diagonal emission of a *replacement law* `κnew` of three objects
  (`Enew`). In `lem:record:one-stage-folded-e`(e), `κnew` is the law under which the shared
  label (object `2`) is uniform and the private pair (objects `0, 1`) is distributed by
  `⊗_p 𝒦₊^{(c_p)}`; that law is built in `Sarkozy.PartVRecords.OneStage`. Here `κnew` is a
  parameter of the frame (`FrameData.κnew`).

The decomposition (d), blockwise, with every record divided by `P(r)`:
`ρ = μ - Ffold + Eadd + G`, `λ = μ - Ffold - Efold + E_new + G`, `δ_E = E_new - Efold - Eadd`,
`Ñ = λ + Ffold + H`, `Ñ₀ = μ + Eadd + G + H` (`rho`, `lam`, `deltaE`, `Nbr`, `Nbr0`), and the
identities `λ = ρ + δ_E`, `Ñ = Ñ₀ + δ_E`, `Ñ - λ = Ffold + H`,
`Ñ + λ = 2μ - Ffold - 2Efold + H + 2E_new + 2G` (`lam_eq_rho_add_deltaE`, `Nbr_eq_Nbr0_add_deltaE`,
`Nbr_sub_lam`, `Nbr_add_lam`).

**Proved here** (`def:record:frame`(b), the sentences after the list): all five measures and
`E_new` are nonnegative (`Ffold_nonneg`, …), reserved diagonal (`IsDiagonalAt reservedCut`, and
positive and symmetric at `ι`), with the stated masses; `Ffold` and `Efold` are summands of `μ̃_𝔅`
(`muT_sub_Ffold_Efold_nonneg`: `μ̃_𝔅 - Ffold - Efold ≥ 0`), so `ρ` and `λ` are nonnegative
(`rho_nonneg`, `lam_nonneg`). The normalized records are positive records (nonnegative with uniform
one-slot marginals) when the one-layer field laws and `κnew` have uniform vertex marginals
(`isPositiveRecord_diag`, `isPositiveRecord_newRec`).

The prices and tags (e) are in `Sarkozy.PartVRecords.Prices`; the bracket `lem:record:gram` in
`Sarkozy.PartVRecords.Gram`.

**Interpretation choices.**
1. The frame is stated for arbitrary middle field laws `F`, weights `W` and inputs `I` (only
   `f₁, h₁` are read), for a real `r ≥ 0` and a real `b` (in the paper `r = b^{-1/2}` with `b` the
   least prime of the block; the relation `r² = 1/b` is assumed only where it is used, in the
   prices).
2. The paper's `G` and `H` are `Gpol` and `Hdiag` here (the letters `G`, `H` are used for graphs
   and test functions elsewhere in the library).
3. Measures are linear functionals `SlotMeasure X` (`Sarkozy.TheoremC.SlotMeasure`), as for V1's
   `middleTilde`.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC Sarkozy.RecordExpansion

variable {X : Type} [Fintype X] [DecidableEq X]

/-! ## Reserved-diagonal emitted laws -/

/-- The image of a law under an emission fixed by a cut is diagonal at the cut. -/
theorem isDiagonalAt_emit {I : Type*} [Fintype I] [DecidableEq I] (lam : FiniteLaw (I → X))
    (π : Slot → I) (c : ReflectionCut Slot) (hπ : ∀ v, π (c.flip v) = π v) :
    IsDiagonalAt c (signedIntegral (emit lam π).weight) := by
  intro z hz v
  rw [lawDensity_signedIntegral'] at hz
  obtain ⟨y, -, rfl⟩ := emit_support lam π hz
  simp only [Function.comp_apply, hπ]

/-- The image of a law under an emission fixed by a cut is symmetric at the cut. -/
theorem isSymmetricAt_emit {I : Type*} [Fintype I] [DecidableEq I] (lam : FiniteLaw (I → X))
    (π : Slot → I) (c : ReflectionCut Slot) (hπ : ∀ v, π (c.flip v) = π v) :
    IsSymmetricAt c (signedIntegral (emit lam π).weight) := by
  apply LinearMap.ext
  intro f
  rw [reflect_apply, ← FiniteLaw.expect_eq_signedIntegral, ← FiniteLaw.expect_eq_signedIntegral,
    expect_emit, expect_emit]
  apply FiniteLaw.expect_congr
  intro y
  congr 1
  funext v
  simp only [Function.comp_apply, hπ]

omit [DecidableEq X] in
/-- A law, as a functional, is nonnegative. -/
theorem isNonneg_law (μ : FiniteLaw (Slot → X)) : IsNonneg (signedIntegral μ.weight) :=
  fun _ hf => μ.expect_nonneg hf

omit [DecidableEq X] in
theorem mass_law (μ : FiniteLaw (Slot → X)) : mass (signedIntegral μ.weight) = 1 :=
  μ.expect_const 1

omit [DecidableEq X] in
theorem nonneg_add {κ κ' : SlotMeasure X} (h : IsNonneg κ) (h' : IsNonneg κ') :
    IsNonneg (κ + κ') := fun f hf => add_nonneg (h f hf) (h' f hf)

omit [DecidableEq X] in
theorem nonneg_smul {κ : SlotMeasure X} (h : IsNonneg κ) {a : ℝ} (ha : 0 ≤ a) :
    IsNonneg (a • κ) := fun f hf => mul_nonneg ha (h f hf)

theorem diagonal_add {c : ReflectionCut Slot} {κ κ' : SlotMeasure X} (h : IsDiagonalAt c κ)
    (h' : IsDiagonalAt c κ') : IsDiagonalAt c (κ + κ') := by
  intro z hz v
  have hsum : lawDensity (κ + κ') z = lawDensity κ z + lawDensity κ' z := rfl
  rw [hsum] at hz
  by_cases hκ : lawDensity κ z = 0
  · rw [hκ, zero_add] at hz
    exact h' z hz v
  · exact h z hκ v

theorem diagonal_smul {c : ReflectionCut Slot} {κ : SlotMeasure X} (h : IsDiagonalAt c κ)
    (a : ℝ) : IsDiagonalAt c (a • κ) := by
  intro z hz v
  have hs : lawDensity (a • κ) z = a * lawDensity κ z := rfl
  rw [hs] at hz
  exact h z (right_ne_zero_of_mul hz) v

omit [DecidableEq X] in
/-- `c • signedIntegral μ.weight` has uniform one-slot marginals when `μ` does. -/
theorem hasUniformSlotMarginals_smul_law [Nonempty X] (μ : FiniteLaw (Slot → X))
    (hμ : HasUniformMarginals μ) (a : ℝ) :
    HasUniformSlotMarginals (a • signedIntegral μ.weight) := by
  intro v g
  change a * μ.expect (fun z => g (z v)) = a * μ.expect (fun _ => 1) * _
  rw [hμ v g, FiniteLaw.expect_const, mul_one, FiniteLaw.expect_uniform]

/-! ## The frame data -/

/-- **The data of the frame on one middle block** (`def:record:frame`): the field laws `F` of the
block (V1's `MiddleFieldLaws`), the completion weights `W`, the inputs `I` (the row constants
`f₁, h₁` are read), `r` (`= b^{-1/2}` in the paper), the least prime `b` of the block, and the
replacement law `κnew` of three objects of the folded matching records
(`lem:record:one-stage-folded-e`(e); built in `Sarkozy.PartVRecords.OneStage`). -/
structure FrameData (X : Type) [Fintype X] [DecidableEq X] where
  F : MiddleFieldLaws X
  W : MiddleWeights
  I : MiddleInputs
  r : ℝ
  r_nonneg : 0 ≤ r
  b : ℝ
  κnew : FiniteLaw (Fin 3 × Fin 1 → X)

namespace FrameData

variable (D : FrameData X)

/-- The two-layer component `Π_φ` of the pattern `φ` of type `t`, as a functional. -/
noncomputable def two (t : PType) (φ : t.Pat) : SlotMeasure X :=
  signedIntegral (midComponent D.F (true, ⟨t, φ⟩)).weight

/-- The one-layer component placed on both layers, `Diag_ι(Π⁽¹⁾_φ)`, as a functional. -/
noncomputable def diag (t : PType) (φ : t.Pat) : SlotMeasure X :=
  signedIntegral (midComponent D.F (false, ⟨t, φ⟩)).weight

/-- `μ̃_𝔅` (V1's `middleTilde`). -/
noncomputable def muT : SlotMeasure X := middleTilde D.F D.W D.r

/-- The normalizer `μ̃_𝔅(1) = P(r)` (V1's `midPoly`). -/
noncomputable def P : ℝ := midPoly D.W D.r

/-- **`F_fold`**: the two nonaccepting one-layer fold components on the reserved diagonal. -/
noncomputable def Ffold : SlotMeasure X :=
  (D.W.v .D * D.r ^ 2) • (D.diag .D (1 : Fin 3) + D.diag .D (2 : Fin 3))

/-- **`E_fold`**: the two reserved-folded matching components. -/
noncomputable def Efold : SlotMeasure X :=
  (D.W.v .S * D.r ^ 2) • (D.diag .S (0 : Fin 2) + D.diag .S (1 : Fin 2))

/-- **`E_add`**: a pair of reserved-folded matching records of total mass `2 v_D r²`. -/
noncomputable def Eadd : SlotMeasure X :=
  (D.W.v .D * D.r ^ 2) • (D.diag .S (0 : Fin 2) + D.diag .S (1 : Fin 2))

/-- `G_e = v_D r² Diag_ι(Π⁽¹⁾_{G₀₀})`. -/
noncomputable def Ge : SlotMeasure X := (D.W.v .D * D.r ^ 2) • D.diag .R ((0 : Fin 2), (0 : Fin 3))

/-- `G_o = v_D r² Diag_ι(Π⁽¹⁾_{G₁₁})`. -/
noncomputable def Go : SlotMeasure X := (D.W.v .D * D.r ^ 2) • D.diag .R ((1 : Fin 2), (1 : Fin 3))

/-- **The polarization correction `G = (f₁ + h₁) r (G_e + G_o)`.** -/
noncomputable def Gpol : SlotMeasure X := ((D.I.f₁ + D.I.h₁) * D.r) • (D.Ge + D.Go)

/-- The coefficient `2 w_S r · 3/(b - 3)` of each actual half diagonal in `H`. -/
noncomputable def hCoef : ℝ := 2 * D.W.w .S * D.r * (3 / (D.b - 3))

/-- **`H`**: for each two-layer matching component `Π_{E_s}`, its actual half diagonal
`Diag_ι(Π⁽¹⁾_{E_s})` with coefficient `2 w_S r · 3/(b - 3)`. -/
noncomputable def Hdiag : SlotMeasure X := D.hCoef • (D.diag .S (0 : Fin 2) + D.diag .S (1 : Fin 2))

/-- The replacement record of type `E_s` (normalized to mass one): the image of `κnew` under the
diagonal emission of the matching `E_s`. -/
noncomputable def newRec (s : Fin 2) : SlotMeasure X :=
  signedIntegral (emit D.κnew (midDiagEmission (matching s))).weight

/-- **`E_new`** (`def:record:frame`(c)): each folded matching record of type `E_s` of
`E_fold + E_add` (mass `(v_S + v_D) r²`) replaced by the record of the same mass with the
replacement law. -/
noncomputable def Enew : SlotMeasure X :=
  ((D.W.v .S + D.W.v .D) * D.r ^ 2) • (D.newRec 0 + D.newRec 1)

/-! ### The decomposition (`def:record:frame`(d)) -/

/-- The reference `μ_𝔅 = μ̃_𝔅 / P(r)`. -/
noncomputable def mu : SlotMeasure X := D.P⁻¹ • D.muT

/-- `ρ = μ - F_fold + E_add + G` (records divided by `P(r)`). -/
noncomputable def rho : SlotMeasure X := D.P⁻¹ • (D.muT - D.Ffold + D.Eadd + D.Gpol)

/-- **The first stage** `λ = μ - F_fold - E_fold + E_new + G`. -/
noncomputable def lam : SlotMeasure X := D.P⁻¹ • (D.muT - D.Ffold - D.Efold + D.Enew + D.Gpol)

/-- `δ_E = E_new - E_fold - E_add`. -/
noncomputable def deltaE : SlotMeasure X := D.P⁻¹ • (D.Enew - D.Efold - D.Eadd)

/-- **The bracket measure** `Ñ = λ + F_fold + H`. -/
noncomputable def Nbr : SlotMeasure X := D.lam + D.P⁻¹ • (D.Ffold + D.Hdiag)

/-- `Ñ₀ = μ + E_add + G + H`. -/
noncomputable def Nbr0 : SlotMeasure X := D.P⁻¹ • (D.muT + D.Eadd + D.Gpol + D.Hdiag)

/-- `μ_𝔅` is V1's normalized middle reference. -/
theorem mu_eq : D.mu = signedIntegral (middleReference D.F D.W D.r_nonneg).weight := by
  rw [middleReference_eq]
  rfl

/-- **`λ = ρ + δ_E`** (`def:record:frame`(d)). -/
theorem lam_eq_rho_add_deltaE : D.lam = D.rho + D.deltaE := by
  apply LinearMap.ext
  intro f
  simp only [lam, rho, deltaE, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- **`Ñ = Ñ₀ + δ_E`** (`def:record:frame`(d)). -/
theorem Nbr_eq_Nbr0_add_deltaE : D.Nbr = D.Nbr0 + D.deltaE := by
  apply LinearMap.ext
  intro f
  simp only [Nbr, Nbr0, lam, deltaE, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **`Ñ - λ = F_fold + H`**: `F_fold` occurs with coefficient one. -/
theorem Nbr_sub_lam : D.Nbr - D.lam = D.P⁻¹ • (D.Ffold + D.Hdiag) := by
  apply LinearMap.ext
  intro f
  simp only [Nbr, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- **`Ñ + λ = 2μ - F_fold - 2E_fold + H + 2E_new + 2G`.** -/
theorem Nbr_add_lam : D.Nbr + D.lam = D.P⁻¹ • ((2 : ℝ) • D.muT - D.Ffold - (2 : ℝ) • D.Efold +
    D.Hdiag + (2 : ℝ) • D.Enew + (2 : ℝ) • D.Gpol) := by
  apply LinearMap.ext
  intro f
  simp only [Nbr, lam, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- `Ñ₀ - μ = E_add + G + H` (records divided by `P(r)`). -/
theorem Nbr0_sub_mu : D.Nbr0 - D.mu = D.P⁻¹ • (D.Eadd + D.Gpol + D.Hdiag) := by
  apply LinearMap.ext
  intro f
  simp only [Nbr0, mu, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- `ρ - μ = E_add + G - F_fold` (records divided by `P(r)`). -/
theorem rho_sub_mu : D.rho - D.mu = D.P⁻¹ • (D.Eadd + D.Gpol - D.Ffold) := by
  apply LinearMap.ext
  intro f
  simp only [rho, mu, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-! ### The records: nonnegativity, masses, reserved diagonal (`def:record:frame`(b)) -/

theorem diag_nonneg (t : PType) (φ : t.Pat) : IsNonneg (D.diag t φ) := isNonneg_law _

theorem two_nonneg (t : PType) (φ : t.Pat) : IsNonneg (D.two t φ) := isNonneg_law _

theorem newRec_nonneg (s : Fin 2) : IsNonneg (D.newRec s) := isNonneg_law _

theorem diag_mass (t : PType) (φ : t.Pat) : mass (D.diag t φ) = 1 := mass_law _

theorem newRec_mass (s : Fin 2) : mass (D.newRec s) = 1 := mass_law _

theorem diag_diagonal (t : PType) (φ : t.Pat) : IsDiagonalAt reservedCut (D.diag t φ) :=
  isDiagonalAt_emit _ _ _ (midDiagEmission_reserved _)

theorem newRec_diagonal (s : Fin 2) : IsDiagonalAt reservedCut (D.newRec s) :=
  isDiagonalAt_emit _ _ _ (midDiagEmission_reserved _)

theorem diag_positive (t : PType) (φ : t.Pat) : reservedCut.Positive (D.diag t φ) :=
  emit_positive _ _ _ (midDiagEmission_reserved _)

theorem newRec_positive (s : Fin 2) : reservedCut.Positive (D.newRec s) :=
  emit_positive _ _ _ (midDiagEmission_reserved _)

theorem diag_symmetric (t : PType) (φ : t.Pat) : IsSymmetricAt reservedCut (D.diag t φ) :=
  isSymmetricAt_emit _ _ _ (midDiagEmission_reserved _)

theorem newRec_symmetric (s : Fin 2) : IsSymmetricAt reservedCut (D.newRec s) :=
  isSymmetricAt_emit _ _ _ (midDiagEmission_reserved _)

theorem coef2_nonneg (t : PType) : 0 ≤ D.W.v t * D.r ^ 2 :=
  mul_nonneg (D.W.v_nonneg t) (sq_nonneg _)

theorem hCoef_nonneg (hb : 3 < D.b) : 0 ≤ D.hCoef := by
  unfold hCoef
  have h3 : 0 < D.b - 3 := by linarith
  have := D.W.w_nonneg .S
  have := D.r_nonneg
  positivity

/-- The five measures of (b) and `E_new` are nonnegative (for `f₁ + h₁ ≥ 0` and `b > 3`). -/
theorem records_nonneg (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) :
    IsNonneg D.Ffold ∧ IsNonneg D.Efold ∧ IsNonneg D.Eadd ∧ IsNonneg D.Gpol ∧ IsNonneg D.Hdiag ∧
      IsNonneg D.Enew := by
  refine ⟨nonneg_smul (nonneg_add (D.diag_nonneg _ _) (D.diag_nonneg _ _)) (D.coef2_nonneg _),
    nonneg_smul (nonneg_add (D.diag_nonneg _ _) (D.diag_nonneg _ _)) (D.coef2_nonneg _),
    nonneg_smul (nonneg_add (D.diag_nonneg _ _) (D.diag_nonneg _ _)) (D.coef2_nonneg _),
    nonneg_smul (nonneg_add (nonneg_smul (D.diag_nonneg _ _) (D.coef2_nonneg _))
      (nonneg_smul (D.diag_nonneg _ _) (D.coef2_nonneg _))) (mul_nonneg hfh D.r_nonneg),
    nonneg_smul (nonneg_add (D.diag_nonneg _ _) (D.diag_nonneg _ _)) (D.hCoef_nonneg hb),
    nonneg_smul (nonneg_add (D.newRec_nonneg _) (D.newRec_nonneg _))
      (mul_nonneg (add_nonneg (D.W.v_nonneg _) (D.W.v_nonneg _)) (sq_nonneg _))⟩

/-- The five measures of (b) and `E_new` are reserved diagonal (fixed samplewise by `ι`). -/
theorem records_diagonal :
    IsDiagonalAt reservedCut D.Ffold ∧ IsDiagonalAt reservedCut D.Efold ∧
      IsDiagonalAt reservedCut D.Eadd ∧ IsDiagonalAt reservedCut D.Gpol ∧
      IsDiagonalAt reservedCut D.Hdiag ∧ IsDiagonalAt reservedCut D.Enew :=
  ⟨diagonal_smul (diagonal_add (D.diag_diagonal _ _) (D.diag_diagonal _ _)) _,
    diagonal_smul (diagonal_add (D.diag_diagonal _ _) (D.diag_diagonal _ _)) _,
    diagonal_smul (diagonal_add (D.diag_diagonal _ _) (D.diag_diagonal _ _)) _,
    diagonal_smul (diagonal_add (diagonal_smul (D.diag_diagonal _ _) _)
      (diagonal_smul (D.diag_diagonal _ _) _)) _,
    diagonal_smul (diagonal_add (D.diag_diagonal _ _) (D.diag_diagonal _ _)) _,
    diagonal_smul (diagonal_add (D.newRec_diagonal _) (D.newRec_diagonal _)) _⟩

/-- **The masses** (`def:record:frame`(b)): `2 v_D r²`, `2 v_S r²`, `2 v_D r²`,
`2 v_D (f₁ + h₁) r³`, `2 hCoef = 12 w_S r/(b - 3)`, and `E_new` has the mass `2 (v_S + v_D) r²` of
`E_fold + E_add`. -/
theorem records_mass :
    mass D.Ffold = 2 * D.W.v .D * D.r ^ 2 ∧ mass D.Efold = 2 * D.W.v .S * D.r ^ 2 ∧
      mass D.Eadd = 2 * D.W.v .D * D.r ^ 2 ∧
      mass D.Gpol = 2 * D.W.v .D * (D.I.f₁ + D.I.h₁) * D.r ^ 3 ∧
      mass D.Hdiag = 12 * D.W.w .S * D.r / (D.b - 3) ∧
      mass D.Enew = 2 * (D.W.v .S + D.W.v .D) * D.r ^ 2 ∧
      mass D.Enew = mass D.Efold + mass D.Eadd := by
  have hd := D.diag_mass
  have hn := D.newRec_mass
  unfold mass at hd hn
  simp only [mass, Ffold, Efold, Eadd, Gpol, Ge, Go, Hdiag, hCoef, Enew, LinearMap.add_apply,
    LinearMap.smul_apply, smul_eq_mul, hd, hn]
  refine ⟨by ring, by ring, by ring, by ring, by ring, by ring, by ring⟩

/-- The five measures of (b) and `E_new` are positive at `ι` (nonnegative and reserved diagonal,
`lem:commoncut`). -/
theorem records_reserved_positive (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) :
    reservedCut.Positive D.Ffold ∧ reservedCut.Positive D.Efold ∧ reservedCut.Positive D.Eadd ∧
      reservedCut.Positive D.Gpol ∧ reservedCut.Positive D.Hdiag ∧
      reservedCut.Positive D.Enew :=
  ⟨((D.diag_positive _ _).add (D.diag_positive _ _)).smul (D.coef2_nonneg _),
    ((D.diag_positive _ _).add (D.diag_positive _ _)).smul (D.coef2_nonneg _),
    ((D.diag_positive _ _).add (D.diag_positive _ _)).smul (D.coef2_nonneg _),
    (((D.diag_positive _ _).smul (D.coef2_nonneg _)).add
      ((D.diag_positive _ _).smul (D.coef2_nonneg _))).smul (mul_nonneg hfh D.r_nonneg),
    ((D.diag_positive _ _).add (D.diag_positive _ _)).smul (D.hCoef_nonneg hb),
    ((D.newRec_positive _).add (D.newRec_positive _)).smul
      (mul_nonneg (add_nonneg (D.W.v_nonneg _) (D.W.v_nonneg _)) (sq_nonneg _))⟩

/-- The five measures of (b) and `E_new` are symmetric at `ι`. -/
theorem records_symmetric :
    IsSymmetricAt reservedCut D.Ffold ∧ IsSymmetricAt reservedCut D.Efold ∧
      IsSymmetricAt reservedCut D.Eadd ∧ IsSymmetricAt reservedCut D.Gpol ∧
      IsSymmetricAt reservedCut D.Hdiag ∧ IsSymmetricAt reservedCut D.Enew :=
  ⟨((D.diag_symmetric _ _).add (D.diag_symmetric _ _)).smul _,
    ((D.diag_symmetric _ _).add (D.diag_symmetric _ _)).smul _,
    ((D.diag_symmetric _ _).add (D.diag_symmetric _ _)).smul _,
    (((D.diag_symmetric _ _).smul _).add ((D.diag_symmetric _ _).smul _)).smul _,
    ((D.diag_symmetric _ _).add (D.diag_symmetric _ _)).smul _,
    ((D.newRec_symmetric _).add (D.newRec_symmetric _)).smul _⟩

/-! ### `F_fold` and `E_fold` are summands of `μ̃_𝔅` -/

/-- The pair of the two summands of `μ̃_𝔅` of one pattern. -/
noncomputable def pairTerm (s : Σ t : PType, t.Pat) : SlotMeasure X :=
  midCoeff D.W D.r (true, s) • signedIntegral (midComponent D.F (true, s)).weight +
    midCoeff D.W D.r (false, s) • signedIntegral (midComponent D.F (false, s)).weight

/-- `μ̃_𝔅 = ∑_φ (w_𝔱 r^{deg} Π_φ + v_𝔱 r^{deg+1} Diag_ι(Π⁽¹⁾_φ))`. -/
theorem muT_eq_sum : D.muT = ∑ s, D.pairTerm s := by
  unfold muT middleTilde tildeMeasure pairTerm
  rw [Fintype.sum_prod_type, Fintype.sum_bool, ← sum_add_distrib]

theorem pairTerm_nonneg (s : Σ t : PType, t.Pat) : IsNonneg (D.pairTerm s) :=
  nonneg_add (nonneg_smul (isNonneg_law _) (midCoeff_nonneg D.W D.r_nonneg _))
    (nonneg_smul (isNonneg_law _) (midCoeff_nonneg D.W D.r_nonneg _))

/-- A sum over the patterns, split into the five types. -/
theorem sum_sigma_pType {M : Type*} [AddCommMonoid M] (g : (Σ t : PType, t.Pat) → M) :
    ∑ s, g s = g ⟨.L, ()⟩ + ((g ⟨.D, (0 : Fin 3)⟩ + g ⟨.D, (1 : Fin 3)⟩ + g ⟨.D, (2 : Fin 3)⟩) +
      ((g ⟨.S, (0 : Fin 2)⟩ + g ⟨.S, (1 : Fin 2)⟩) +
      (∑ φ : PType.Pat .R, g ⟨.R, φ⟩ + ∑ φ : PType.Pat .C, g ⟨.C, φ⟩))) := by
  rw [Fintype.sum_sigma, PType.sum_pType]
  have hL : ∑ φ : PType.Pat .L, g ⟨.L, φ⟩ = g ⟨.L, ()⟩ := Fintype.sum_unique _
  have hD : ∑ φ : PType.Pat .D, g ⟨.D, φ⟩ =
      g ⟨.D, (0 : Fin 3)⟩ + g ⟨.D, (1 : Fin 3)⟩ + g ⟨.D, (2 : Fin 3)⟩ :=
    Fin.sum_univ_three (fun j : Fin 3 => g ⟨.D, j⟩)
  have hS : ∑ φ : PType.Pat .S, g ⟨.S, φ⟩ = g ⟨.S, (0 : Fin 2)⟩ + g ⟨.S, (1 : Fin 2)⟩ :=
    Fin.sum_univ_two (fun j : Fin 2 => g ⟨.S, j⟩)
  rw [hL, hD, hS]

/-- **`μ̃_𝔅 - F_fold - E_fold` is nonnegative**: `F_fold` and `E_fold` are actual summands of the
unnormalized reference (`def:record:frame`(b); used for `λ ≥ 0` in `lem:record:gram`(ii)). -/
theorem muT_sub_Ffold_Efold_nonneg : IsNonneg (D.muT - D.Ffold - D.Efold) := by
  have hexp := D.muT_eq_sum
  rw [sum_sigma_pType] at hexp
  -- the summands of `Diag_ι(Π⁽¹⁾_{F_j})` and `Diag_ι(Π⁽¹⁾_{E_s})` inside `μ̃`
  have hD (j : Fin 3) : D.pairTerm ⟨.D, j⟩ =
      (D.W.w .D * D.r) • D.two .D j + (D.W.v .D * D.r ^ 2) • D.diag .D j := by
    simp only [pairTerm, midCoeff, PType.deg, pow_one]
    rfl
  have hS (s : Fin 2) : D.pairTerm ⟨.S, s⟩ =
      (D.W.w .S * D.r) • D.two .S s + (D.W.v .S * D.r ^ 2) • D.diag .S s := by
    simp only [pairTerm, midCoeff, PType.deg, pow_one]
    rfl
  have key : D.muT - D.Ffold - D.Efold = D.pairTerm ⟨.L, ()⟩ + D.pairTerm ⟨.D, (0 : Fin 3)⟩ +
      (D.W.w .D * D.r) • D.two .D (1 : Fin 3) + (D.W.w .D * D.r) • D.two .D (2 : Fin 3) +
      (D.W.w .S * D.r) • D.two .S (0 : Fin 2) + (D.W.w .S * D.r) • D.two .S (1 : Fin 2) +
      (∑ φ : PType.Pat .R, D.pairTerm ⟨.R, φ⟩ + ∑ φ : PType.Pat .C, D.pairTerm ⟨.C, φ⟩) := by
    rw [hexp, hD 1, hD 2, hS 0, hS 1]
    apply LinearMap.ext
    intro f
    simp only [Ffold, Efold, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      smul_eq_mul]
    ring
  rw [key]
  have hw : ∀ t, 0 ≤ D.W.w t * D.r := fun t => mul_nonneg (D.W.w_nonneg t) D.r_nonneg
  refine nonneg_add (nonneg_add (nonneg_add (nonneg_add (nonneg_add (nonneg_add
    (D.pairTerm_nonneg _) (D.pairTerm_nonneg _)) (nonneg_smul (D.two_nonneg _ _) (hw _)))
    (nonneg_smul (D.two_nonneg _ _) (hw _))) (nonneg_smul (D.two_nonneg _ _) (hw _)))
    (nonneg_smul (D.two_nonneg _ _) (hw _))) ?_
  intro f hf
  rw [LinearMap.add_apply, LinearMap.sum_apply, LinearMap.sum_apply]
  exact add_nonneg (sum_nonneg fun φ _ => D.pairTerm_nonneg _ f hf)
    (sum_nonneg fun φ _ => D.pairTerm_nonneg _ f hf)

theorem P_pos : 0 < D.P := lt_of_lt_of_le one_pos (one_le_midPoly D.W D.r_nonneg)

/-- **`ρ` is nonnegative.** -/
theorem rho_nonneg (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) : IsNonneg D.rho := by
  obtain ⟨-, hE, hEa, hG, -, -⟩ := D.records_nonneg hfh hb
  have h := nonneg_add (nonneg_add (nonneg_add D.muT_sub_Ffold_Efold_nonneg hE) hEa) hG
  have he : D.muT - D.Ffold + D.Eadd + D.Gpol = D.muT - D.Ffold - D.Efold + D.Efold + D.Eadd +
      D.Gpol := by abel
  unfold rho
  rw [he]
  exact nonneg_smul h (inv_nonneg.mpr D.P_pos.le)

/-- **`λ` is nonnegative** (`lem:record:gram`(ii), first sentence): `F_fold` and `E_fold` are actual
components of `μ̃_𝔅`, and `E_new`, `G` are nonnegative. -/
theorem lam_nonneg (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) : IsNonneg D.lam := by
  obtain ⟨-, -, -, hG, -, hN⟩ := D.records_nonneg hfh hb
  exact nonneg_smul (nonneg_add (nonneg_add D.muT_sub_Ffold_Efold_nonneg hN) hG)
    (inv_nonneg.mpr D.P_pos.le)

/-! ### Positive records (`def:cp:records`) -/

/-- **The normalized records of (b) are positive records** when the one-layer field laws have
uniform vertex marginals: every `Diag_ι(Π⁽¹⁾_φ) / P(r)`, scaled by a nonnegative weight, is
nonnegative with uniform one-slot marginals (the remark after `def:record:frame`). -/
theorem isPositiveRecord_diag [Nonempty X]
    (h1 : ∀ f (o : f.Obj × Fin 1) (g : X → ℝ),
      (D.F.one f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g)
    (t : PType) (φ : t.Pat) {a : ℝ} (ha : 0 ≤ a) : IsPositiveRecord (a • D.diag t φ) :=
  ⟨nonneg_smul (D.diag_nonneg t φ) ha,
    hasUniformSlotMarginals_smul_law _ (emit_uniform _ _ (h1 t.field)) a⟩

/-- The replacement records are positive records when `κnew` has uniform vertex marginals. -/
theorem isPositiveRecord_newRec [Nonempty X]
    (hκ : ∀ (o : Fin 3 × Fin 1) (g : X → ℝ),
      D.κnew.expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g)
    (s : Fin 2) {a : ℝ} (ha : 0 ≤ a) : IsPositiveRecord (a • D.newRec s) :=
  ⟨nonneg_smul (D.newRec_nonneg s) ha, hasUniformSlotMarginals_smul_law _ (emit_uniform _ _ hκ) a⟩

end FrameData

end Sarkozy.PartVRecords

module

public import Sarkozy.PartVLaws.ExactMarginals
public import Sarkozy.PartVLaws.LayerCaps
public import Sarkozy.PartVLaws.ReferenceFields

@[expose] public section

/-!
# The tail inputs in the paper's form (`lem:tail-law`(i)–(ii), `it:record:upper-F5`(b))

`paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i): "the rows are those of (F5)(b),
with `t_Y = 1/50` and `M = 21/20`"; the row inputs are upper bounds for the coefficients
`f_Schur` and `h = ρ_E/r` of `def:record:upper-bands`, item (F5)(b).

* `normBound_mono`, **`ValidRows.mono`**: valid rows stay valid with larger coefficients
  `f, h` (so "coefficients at most `(f_φ, h_φ)`" of (V2) is meaningful).
* `SchurInputs D r I`: the Schur-row data of (F5)(b) at every middle value, with constants whose
  `f_Schur` and `ρ_E/r` are at most the input `I` and `H + 1/50 ≤ I.M`; `validRows_of_schurInputs`
  gives `ValidRows D r I.f I.h I.M`.
* `TailInputsSchur P`, **`tailInputsValid_of_schur`**: the same inputs at every tail prime
  `q ≥ P` give `TailInputsValid P`, the hypothesis of `tailFamilyFrom_rpp`, `tailReference` and
  `partVReference`.
* **`tailLaw_familyPositive_schur`**: `lem:tail-law`(ii) at a prime `p ≥ 2²⁰` under H1, from
  (V1) the root envelopes, (V2) in the form of (F5)(b) (`SchurInputs` with the tail datum's
  inputs) and (V3) for the nine field laws. The remaining inputs are the spectral constants
  themselves (the completed-root caps, the spectral criterion and the row comparisons, at
  `p₀ = 2⁶⁴`, and their monotonicity in `p`), which are not formalized.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

omit [DecidableEq 𝔛] in
theorem normBound_mono {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} {e e' : ℝ} (h : NormBound μ T e)
    (he : e ≤ e') : NormBound μ T e' := fun Φ Ψ =>
  (h Φ Ψ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he
    (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

theorem fJ_anti_h {H kJ h h' r εT tY υ : ℝ} (hH : 0 ≤ H) (hr : 0 ≤ r) (hh : h ≤ h') :
    fJ H kJ h' r εT tY υ ≤ fJ H kJ h r εT tY υ := by
  unfold fJ
  refine div_le_div_of_nonneg_right ?_ hr
  have hmax : max (kJ - h') 0 ≤ max (kJ - h) 0 := max_le_max (by linarith) le_rfl
  have := mul_le_mul_of_nonneg_right hmax hr
  nlinarith

/-- **Valid rows stay valid with larger coefficients.** -/
theorem ValidRows.mono {D : Datum 𝔛} {r f h f' h' M : ℝ} (hv : ValidRows D r f h M) (hr : 0 ≤ r)
    (hf : f ≤ f') (hh : h ≤ h') : ValidRows D r f' h' M := by
  have hhr : h * r ≤ h' * r := mul_le_mul_of_nonneg_right hh hr
  rcases hv with ⟨hf0, hM, hb⟩ | ⟨H, β, qperp, tY, hq, htY, htH, hHM, hfal, hb⟩ |
      ⟨H, υ, εT, kJ, tY, hh0, hεT, htY, htH, hHM, hfJ, hb⟩
  · exact Or.inl ⟨hf0.trans hf, hM, fun b hb' => ⟨normBound_mono (hb b hb').1
      (mul_le_mul_of_nonneg_right hf hr), normBound_mono (hb b hb').2 hhr⟩⟩
  · exact Or.inr (Or.inl ⟨H, β, qperp, tY, hq, htY, htH, hHM, hfal.trans hf, fun b hb' =>
      ⟨(hb b hb').1, normBound_mono (hb b hb').2.1 hhr, (hb b hb').2.2⟩⟩)
  · have hH : 0 < H := inv_pos.mp (lt_of_lt_of_le htY htH)
    refine Or.inr (Or.inr ⟨H, υ, εT, kJ, tY, hh0.trans hh, hεT, htY, htH, hHM,
      (fJ_anti_h hH.le hr hh).trans (hfJ.trans hf), fun b hb' => ⟨(hb b hb').1, ?_⟩⟩)
    obtain ⟨J⟩ := (hb b hb').2
    refine ⟨⟨J.m, J.φ0, J.φ2, J.C, J.R, J.decomp, J.m_lower, J.m_upper, J.mean0, J.mean2, J.dev0,
      J.dev2, J.annC, J.annR, J.normR, fun Φ => ?_, J.joint⟩⟩
    have h1 := J.lowerE Φ
    have h2 : 0 ≤ nrm (D.nub b) Φ ^ 2 := sq_nonneg _
    nlinarith [mul_le_mul_of_nonneg_right hhr h2]

/-- **The Schur-row inputs of (F5)(b)** for the input `I`: constants `H, υ, R_m, ρ_F, ρ_E` with
`0 < H ≤ 50`, `H + 1/50 ≤ M`, `R_m, ρ_F ≥ 0`, `f_Schur ≤ f`, `ρ_E/r ≤ h`, and the Schur-row
data at every middle value. -/
def SchurInputs (D : Datum 𝔛) (r : ℝ) (I : CompletionInput) : Prop :=
  ∃ H υ Rm ρF ρE : ℝ, 0 < H ∧ H ≤ 50 ∧ H + 1 / 50 ≤ (I.M : ℝ) ∧ 0 ≤ Rm ∧ 0 ≤ ρF ∧
    (H * Rm * ρF + (H + 50 * H ^ 2) * υ ^ 2) / r ≤ (I.f : ℝ) ∧ ρE / r ≤ (I.h : ℝ) ∧
    ∀ b, D.nu.weight b ≠ 0 → SchurRowData (D.nub b) (D.TF b) (D.TE b) H υ Rm ρF ρE

/-- **Schur inputs give valid rows** with the coefficients of the input. -/
theorem validRows_of_schurInputs {D : Datum 𝔛} {r : ℝ} (hr : 0 < r) {I : CompletionInput}
    (hS : SchurInputs D r I) : ValidRows D r I.f I.h I.M := by
  obtain ⟨H, υ, Rm, ρF, ρE, hH, hH50, hM, hRm, hρF, hf, hh, hb⟩ := hS
  exact (validRows_of_schurRows D hr hH hH50 hRm hρF hM hb).mono hr.le hf hh

/-- **`lem:tail-law`(ii) from the paper's form of the inputs**: at every prime `p ≥ 2²⁰`, under
H1, with (V1) the root envelopes, (V2) the Schur rows of (F5)(b) with the tail datum's inputs
(`t_Y = 1/50`, `M = 21/20`), and (V3) the layer caps of the nine field laws, the tail law is
reflection positive at every cut of `𝔉`. -/
theorem tailLaw_familyPositive_schur (p : ℕ) [Fact p.Prime] (hW : WeilBound (ZMod p))
    (hp : (2 : ℝ) ^ 20 ≤ p) (hne : TailNonempty p)
    (hroot20 : ∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two0 f')) (tailOrd f').d (tailR p))
    (hroot21 : ∀ f', RootEnv (rowD1 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two1 f')) (tailOrd f').d (tailR p))
    (hroot10 : ∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one0 f')) (tailRes f').d (tailR p))
    (hroot11 : ∀ f', RootEnv (rowD1 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one1 f')) (tailRes f').d (tailR p))
    (hs20 : ∀ f', SchurInputs (rowD0 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two0 f')) (tailR p) (tailOrd f'))
    (hs21 : ∀ f', SchurInputs (rowD1 (lam2 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).two1 f')) (tailR p) (tailOrd f'))
    (hs10 : ∀ f', SchurInputs (rowD0 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one0 f')) (tailR p) (tailRes f'))
    (hs11 : ∀ f', SchurInputs (rowD1 (lam1 (tailFieldLaws p hne)) f'
      ((tail_upperDatumHyp p hW hp hne).one1 f')) (tailR p) (tailRes f'))
    (hcaps : FieldLayerCaps (tailFieldLaws p hne) tailKappa (tailR p)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (tailLaw p hne).weight) :=
  tailLaw_familyPositive' p hW hp hne hroot20 hroot21 hroot10 hroot11
    (fun f' => validRows_of_schurInputs (tailR_pos p) (hs20 f'))
    (fun f' => validRows_of_schurInputs (tailR_pos p) (hs21 f'))
    (fun f' => validRows_of_schurInputs (tailR_pos p) (hs10 f'))
    (fun f' => validRows_of_schurInputs (tailR_pos p) (hs11 f')) hcaps

/-- **The tail inputs in the paper's form at every tail prime `q ≥ P`**: (V1) the root envelopes,
(V2) the Schur inputs of (F5)(b) with the tail datum's inputs, and (V3) for the nine field laws. -/
def TailInputsSchur (P : ℕ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
    (hp : (2 : ℝ) ^ 20 ≤ q),
    (∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f').d (tailR q)) ∧
    (∀ f', RootEnv (rowD1 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailOrd f').d (tailR q)) ∧
    (∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f').d (tailR q)) ∧
    (∀ f', RootEnv (rowD1 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailRes f').d (tailR q)) ∧
    (∀ f', SchurInputs (rowD0 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailR q) (tailOrd f')) ∧
    (∀ f', SchurInputs (rowD1 (lam2 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailR q) (tailOrd f')) ∧
    (∀ f', SchurInputs (rowD0 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailR q) (tailRes f')) ∧
    (∀ f', SchurInputs (rowD1 (lam1 (tailFieldLaws q hne)) f'
      ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailR q) (tailRes f')) ∧
    FieldLayerCaps (tailFieldLaws q hne) tailKappa (tailR q)

/-- **The paper's form of the tail inputs gives `TailInputsValid`.** -/
theorem tailInputsValid_of_schur {P : ℕ} (h : TailInputsSchur P) : TailInputsValid P := by
  intro q _ hq hne hW hp
  obtain ⟨r20, r21, r10, r11, s20, s21, s10, s11, hcaps⟩ := h q hq hne hW hp
  have hV := ValidInputs.ofField (H := tail_upperDatumHyp q hW hp hne) r20 r21 r10 r11
    (fun f' => validRows_of_schurInputs (tailR_pos q) (s20 f'))
    (fun f' => validRows_of_schurInputs (tailR_pos q) (s21 f'))
    (fun f' => validRows_of_schurInputs (tailR_pos q) (s10 f'))
    (fun f' => validRows_of_schurInputs (tailR_pos q) (s11 f')) hcaps
  rw [tailCap_eq] at hV
  exact hV

end Sarkozy.PartVLaws

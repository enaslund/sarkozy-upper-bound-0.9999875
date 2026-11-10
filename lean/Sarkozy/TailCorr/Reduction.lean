module

public import Sarkozy.PartVLaws.TailRowsAll

@[expose] public section

/-!
# `TailInputsCorr P₄` from the spectral bounds of the tail datum, with no loss in the constants

`paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i);
`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`, items `it:record:upper-F4`
and `it:record:upper-F5`(b), `subsec:row-anova-correlation` (`eq:row-anova-stars`,
`eq:row-anova-actual`), `subsec:upper-reference-rp` ((V1)–(V3)).

V2's obligation `PartVLaws.TailInputsCorr P` has nine conjuncts at every prime `q ≥ P`: the root
envelopes (V1) of the four row families, the correlation form `CorrSchur` of (F4) with the
numerical conditions of (F5)(b), and the layer caps (V3). This file removes the numerical layer
of `CorrSchur` and states what remains as bare spectral bounds `ρ_F ≤ c_F r`, `ρ_E ≤ c_E r`.

* **`tailSchurF_le_sharp`**: `f_Schur ≤ (1 + 2⁻¹⁹⁸) √p ρ_F + 2⁻¹⁰⁰` at every prime `p ≥ P₄`.
  V2's `tailSchurF_le` has the factor `2` in place of `1 + 2⁻¹⁹⁸`. That factor cannot be
  afforded: the paper's leading coefficient for the largest `F` row is `8(6 + √684) < 257.228`
  (`eq:row-anova-stars`) against the recorded input `f = 258`, a margin of `0.3%`; for the
  largest `E` row it is `8(4 + √120) < 119.636` against `h = 120`.
* **`corrSchur_of_bounds`**: `CorrInputs D (c_F r) (c_E r)` with `(1 + 2⁻¹⁹⁸) c_F + 2⁻¹⁰⁰ ≤ f`,
  `0 ≤ c_F` and `c_E ≤ h` give `CorrSchur q D I`.
* **`tailCF`**: the canonical constant `c_F = f - 2⁻⁹⁰`, which satisfies the side condition for
  every input of the tail datum (`tailCF_ok`).
* **`TailSpectral`**: the spectral content of `lem:tail-law`(i) at one prime, nine labelled
  fields: (V1) the root envelopes; (F4) the correlations `ρ_F ≤ (f - 2⁻⁹⁰) r`, `ρ_E ≤ h r` of the
  four row families; (V3) the layer caps.
* **`tailInputsCorr_of_spectral`**: `TailSpectral` at every prime `q ≥ P ≥ P₄` gives
  `TailInputsCorr P`.

So `hC` of the main statement reduces to `TailSpectral` at the primes `q ≥ P₄`, with no numerical
condition left.
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws

/-! ## The sharp form of `f_Schur ≤ f` -/

/-- The arithmetic of `tailSchurF_le_sharp`, with `H = ρ^{144}`, `R = ρ^{288}`, `s = √p`. -/
theorem schurF_arith_sharp {H R s ρF : ℝ} (hH : H ≤ 1 + 1 / 2 ^ 200) (hH1 : 1 ≤ H)
    (hR : R ≤ 1 + 1 / 2 ^ 200) (hR1 : 1 ≤ R) (hs : 2 ^ 256 ≤ s)
    (hυ' : R - 1 ≤ 576 * (2 ^ 28 / s)) (hρF : 0 ≤ ρF) :
    (H * R * ρF + (H + 50 * H ^ 2) * (R - 1) ^ 2) * s ≤
      (1 + 1 / 2 ^ 198) * (s * ρF) + 1 / 2 ^ 100 := by
  have hs0 : 0 < s := lt_of_lt_of_le (by positivity) hs
  have hυ0 : 0 ≤ R - 1 := by linarith
  have h1 : H * R ≤ 1 + 1 / 2 ^ 198 := by
    calc H * R ≤ (1 + 1 / 2 ^ 200) * (1 + 1 / 2 ^ 200) :=
          mul_le_mul hH hR (by linarith) (by positivity)
      _ ≤ 1 + 1 / 2 ^ 198 := by norm_num
  have h2 : H + 50 * H ^ 2 ≤ 202 := by
    have hHsq : H ^ 2 ≤ (1 + 1 / 2 ^ 200) ^ 2 := pow_le_pow_left₀ (by linarith) hH 2
    have : (1 : ℝ) + 1 / 2 ^ 200 + 50 * (1 + 1 / 2 ^ 200) ^ 2 ≤ 202 := by norm_num
    linarith
  have h3 : (R - 1) ^ 2 * s ≤ (576 * 2 ^ 28) ^ 2 / s := by
    have hsq : (R - 1) ^ 2 ≤ (576 * (2 ^ 28 / s)) ^ 2 := pow_le_pow_left₀ hυ0 hυ' 2
    calc (R - 1) ^ 2 * s ≤ (576 * (2 ^ 28 / s)) ^ 2 * s := mul_le_mul_of_nonneg_right hsq hs0.le
      _ = (576 * 2 ^ 28) ^ 2 / s := by field_simp
  have h4 : (576 * 2 ^ 28 : ℝ) ^ 2 / s ≤ 1 / 2 ^ 100 / 202 := by
    rw [div_le_iff₀ hs0]
    have : (576 * 2 ^ 28 : ℝ) ^ 2 ≤ 1 / 2 ^ 100 / 202 * 2 ^ 256 := by norm_num
    have h5 : 1 / 2 ^ 100 / 202 * 2 ^ 256 ≤ 1 / 2 ^ 100 / 202 * s :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    linarith
  have e1 : H * R * ρF * s ≤ (1 + 1 / 2 ^ 198) * (s * ρF) := by
    calc H * R * ρF * s = (H * R) * (s * ρF) := by ring
      _ ≤ (1 + 1 / 2 ^ 198) * (s * ρF) :=
          mul_le_mul_of_nonneg_right h1 (mul_nonneg hs0.le hρF)
  have e2 : (H + 50 * H ^ 2) * (R - 1) ^ 2 * s ≤ 1 / 2 ^ 100 := by
    have hυs : 0 ≤ (R - 1) ^ 2 * s := mul_nonneg (sq_nonneg _) hs0.le
    calc (H + 50 * H ^ 2) * (R - 1) ^ 2 * s = (H + 50 * H ^ 2) * ((R - 1) ^ 2 * s) := by ring
      _ ≤ 202 * ((R - 1) ^ 2 * s) := mul_le_mul_of_nonneg_right h2 hυs
      _ ≤ 202 * (1 / 2 ^ 100 / 202) := by linarith
      _ = 1 / 2 ^ 100 := by norm_num
  have e3 : (H * R * ρF + (H + 50 * H ^ 2) * (R - 1) ^ 2) * s =
      H * R * ρF * s + (H + 50 * H ^ 2) * (R - 1) ^ 2 * s := by ring
  rw [e3]
  linarith

/-- **`f_Schur ≤ (1 + 2⁻¹⁹⁸) √p ρ_F + 2⁻¹⁰⁰`** at every prime `p ≥ P₄`
(`it:record:upper-F5`(b) for the tail datum, with the counted constants `H = ρ^{144}`,
`R_m = ρ^{288}`, `υ = ρ^{288} - 1`). The sharp form of V2's `tailSchurF_le`: the factor of `ρ_F`
is `(1 + 2⁻¹⁹⁸)√p` instead of `2√p`. -/
theorem tailSchurF_le_sharp (p : ℕ) [Fact p.Prime] (hp : P4 ≤ p) {ρF : ℝ} (hρF : 0 ≤ ρF) :
    tailSchurF p ρF ≤ (1 + 1 / 2 ^ 198) * (Real.sqrt p * ρF) + 1 / 2 ^ 100 := by
  have hs := sqrt_ge_of_P4 p hp
  rw [ZMod.card] at hs
  have hH := countRho_pow_le p hp (n := 144) (by norm_num)
  have hR := countRho_pow_le p hp (n := 288) (by norm_num)
  have hH1 : 1 ≤ countRho p ^ 144 := one_le_pow₀ (one_le_countRho p)
  have hR1 : 1 ≤ countRho p ^ 288 := one_le_pow₀ (one_le_countRho p)
  clear hp
  have hs0 : 0 < Real.sqrt (p : ℝ) := lt_of_lt_of_le (by positivity) hs
  have hε : (0 : ℝ) ≤ 2 ^ 28 / Real.sqrt p := div_nonneg (by positivity) hs0.le
  have hnε : ((288 : ℕ) : ℝ) * (2 ^ 28 / Real.sqrt p) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hs0]
    have : ((288 : ℕ) : ℝ) * 2 ^ 28 ≤ 1 / 2 * 2 ^ 256 := by norm_num
    linarith
  have hυ := one_add_pow_le hε 288 hnε
  have hυ' : countRho p ^ 288 - 1 ≤ 576 * (2 ^ 28 / Real.sqrt p) := by
    rw [sub_le_iff_le_add']
    refine le_trans hυ (le_of_eq ?_)
    push_cast
    ring
  unfold tailSchurF
  rw [tailR_eq_inv_sqrt, div_inv_eq_mul]
  exact schurF_arith_sharp hH hH1 hR hR1 hs hυ' hρF

/-! ## `CorrSchur` from bare correlation bounds -/

section Generic

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **`CorrInputs` is monotone in its two constants.** -/
theorem corrInputs_mono {D : Datum 𝔛} {ρF ρE ρF' ρE' : ℝ} (h : CorrInputs D ρF ρE)
    (hF : ρF ≤ ρF') (hE : ρE ≤ ρE') : CorrInputs D ρF' ρE' := by
  intro b hb
  obtain ⟨h1, h2⟩ := h b hb
  refine ⟨fun g g' => (h1 g g').trans ?_, fun Φ Ψ => (h2 Φ Ψ).trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hF (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hE (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)

/-- **(F5)(b) is implied by bare correlation bounds** (`it:record:upper-F5`(b),
`it:record:upper-F4`): at a prime `q ≥ P₄`, the correlation bounds `ρ_F ≤ c_F r`, `ρ_E ≤ c_E r`
(`CorrInputs` at `(c_F r, c_E r)`, `r = q^{-1/2}`), with `0 ≤ c_F`,
`(1 + 2⁻¹⁹⁸) c_F + 2⁻¹⁰⁰ ≤ f` and `c_E ≤ h`, give the correlation form `CorrSchur q D I` of the
Schur inputs. -/
theorem corrSchur_of_bounds (q : ℕ) [Fact q.Prime] (hq : P4 ≤ q) (D : Datum 𝔛)
    (I : CompletionInput) {cF cE : ℝ} (hcF : 0 ≤ cF)
    (hf : (1 + 1 / 2 ^ 198) * cF + 1 / 2 ^ 100 ≤ (I.f : ℝ)) (hh : cE ≤ (I.h : ℝ))
    (hcorr : CorrInputs D (cF * tailR q) (cE * tailR q)) : CorrSchur q D I := by
  have hr : 0 < tailR q := PartVLaws.tailR_pos q
  have hs : Real.sqrt q * tailR q = 1 := by
    rw [tailR_eq_inv_sqrt]
    have : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : q.Prime).pos)
    field_simp
  refine ⟨cF * tailR q, cE * tailR q, mul_nonneg hcF hr.le, hcorr, ?_, ?_⟩
  · refine (tailSchurF_le_sharp q hq (mul_nonneg hcF hr.le)).trans ?_
    have : Real.sqrt q * (cF * tailR q) = cF := by
      calc Real.sqrt q * (cF * tailR q) = cF * (Real.sqrt q * tailR q) := by ring
        _ = cF := by rw [hs, mul_one]
    rw [this]
    exact hf
  · rw [mul_div_assoc, div_self hr.ne', mul_one]
    exact hh

end Generic

/-! ## The canonical fold constant `c_F = f - 2⁻⁹⁰` -/

/-- **The fold correlation constant of an input**: `c_F = f - 2⁻⁹⁰`. Any proved bound
`ρ_F ≤ c r` with `c ≤ f - 2⁻⁹⁰` gives the fold row of the input; the paper's leading coefficient
`257.228` of the largest `F` row (`eq:row-anova-stars`) is below `258 - 2⁻⁹⁰`. -/
noncomputable def tailCF (I : CompletionInput) : ℝ := (I.f : ℝ) - 1 / 2 ^ 90

theorem cf_arith {f ε δ t : ℝ} (hε : 0 ≤ ε) (hδ : 0 ≤ δ) (h : ε * f + t ≤ δ) :
    (1 + ε) * (f - δ) + t ≤ f := by
  nlinarith [mul_nonneg hε hδ]

/-- The side conditions of `corrSchur_of_bounds` hold for `c_F = f - 2⁻⁹⁰` when `1 ≤ f ≤ 2⁸⁰`. -/
theorem tailCF_ok (I : CompletionInput) (hf1 : (1 : ℝ) ≤ I.f) (hf2 : (I.f : ℝ) ≤ 2 ^ 80) :
    0 ≤ tailCF I ∧ (1 + 1 / 2 ^ 198) * tailCF I + 1 / 2 ^ 100 ≤ (I.f : ℝ) := by
  unfold tailCF
  constructor
  · have : (1 : ℝ) / 2 ^ 90 ≤ 1 := by norm_num
    linarith
  · refine cf_arith (by positivity) (by positivity) ?_
    have h1 : 1 / 2 ^ 198 * (I.f : ℝ) ≤ 1 / 2 ^ 198 * 2 ^ 80 :=
      mul_le_mul_of_nonneg_left hf2 (by positivity)
    have h2 : (1 : ℝ) / 2 ^ 198 * 2 ^ 80 + 1 / 2 ^ 100 ≤ 1 / 2 ^ 90 := by norm_num
    linarith

/-- The ordinary and reserved inputs of the tail datum have `1 ≤ f ≤ 2⁸⁰`. -/
theorem tail_f_range (f' : FieldTy) :
    ((1 : ℝ) ≤ (tailOrd f').f ∧ ((tailOrd f').f : ℝ) ≤ 2 ^ 80) ∧
      ((1 : ℝ) ≤ (tailRes f').f ∧ ((tailRes f').f : ℝ) ≤ 2 ^ 80) := by
  cases f' <;> norm_num [tailOrd, tailRes, tailOrdinary, tailReserved, toFType]

/-! ## The spectral content of `lem:tail-law`(i) -/

/-- **The spectral inputs of the tail datum at one prime** (`lem:tail-law`(i), its spectral part;
`subsec:upper-reference-rp` (V1)–(V3) and `it:record:upper-F4`). Hypothesis bundle, not proved
here; each field is the paper's statement for the single prime `q`, in V1/V2's formal terms:
* `root20`, `root21`, `root10`, `root11` (V1, `it:upper-valid-root`; the per-prime caps of
  `lem:upper-completed-root` for the root cuts and of `it:record:upper-F6` for the nonroot
  chamber cuts): the root envelope `Π_L ⪰_{ϑ₀} -d r Π_{F₀}` of the four row families with the
  recorded `d` of the tail datum;
* `corr20`, `corr21`, `corr10`, `corr11` (F4, `it:record:upper-F4`, `eq:row-anova-actual` with
  `eq:row-anova-stars`): at every middle value, the maximal correlation of the fold kernel is at
  most `(f - 2⁻⁹⁰) r` and `‖T_E^b - J‖ ≤ h r`, with the recorded `(f, h)` of the tail datum;
* `caps` (V3, `it:upper-valid-layer`; `it:record:upper-F6` at the layer cuts): the layer caps
  `λ_{φφ'} ⪰_ι -κ_{φφ'} r Diag_ι(λ⁽¹⁾_{φφ'})` of the nine field laws.

Compared with `TailInputsCorr`, the numerical conditions of (F5)(b) are gone: they are proved
(`corrSchur_of_bounds`, `tailCF_ok`). -/
structure TailSpectral (q : ℕ) [Fact q.Prime] (hne : TailNonempty q) (hW : WeilBound (ZMod q))
    (hp : (2 : ℝ) ^ 20 ≤ q) : Prop where
  root20 : ∀ f', RootEnv (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f')) (tailOrd f').d (tailR q)
  root21 : ∀ f', RootEnv (rowD1 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two1 f')) (tailOrd f').d (tailR q)
  root10 : ∀ f', RootEnv (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f')) (tailRes f').d (tailR q)
  root11 : ∀ f', RootEnv (rowD1 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one1 f')) (tailRes f').d (tailR q)
  corr20 : ∀ f', CorrInputs (rowD0 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two0 f'))
      (tailCF (tailOrd f') * tailR q) ((tailOrd f').h * tailR q)
  corr21 : ∀ f', CorrInputs (rowD1 (lam2 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).two1 f'))
      (tailCF (tailOrd f') * tailR q) ((tailOrd f').h * tailR q)
  corr10 : ∀ f', CorrInputs (rowD0 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one0 f'))
      (tailCF (tailRes f') * tailR q) ((tailRes f').h * tailR q)
  corr11 : ∀ f', CorrInputs (rowD1 (lam1 (tailFieldLaws q hne)) f'
    ((tail_upperDatumHyp q hW hp hne).one1 f'))
      (tailCF (tailRes f') * tailR q) ((tailRes f').h * tailR q)
  caps : FieldLayerCaps (tailFieldLaws q hne) tailKappa (tailR q)

/-- **`TailInputsCorr P` from the spectral inputs** (`lem:tail-law`(i), reduced to its spectral
part): for `P ≥ P₄`, the bundle `TailSpectral` at every prime `q ≥ P` gives V2's
`TailInputsCorr P`; the numerical conditions of (F5)(b) are discharged. -/
theorem tailInputsCorr_of_spectral {P : ℕ} (hP : P4 ≤ P)
    (hS : ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
      (hp : (2 : ℝ) ^ 20 ≤ q), TailSpectral q hne hW hp) :
    TailInputsCorr P := by
  intro q _ hq hne hW hp
  have hq4 : P4 ≤ q := hP.trans hq
  obtain ⟨r20, r21, r10, r11, c20, c21, c10, c11, caps⟩ := hS q hq hne hW hp
  have hord : ∀ f', 0 ≤ tailCF (tailOrd f') ∧
      (1 + 1 / 2 ^ 198) * tailCF (tailOrd f') + 1 / 2 ^ 100 ≤ ((tailOrd f').f : ℝ) :=
    fun f' => tailCF_ok _ (tail_f_range f').1.1 (tail_f_range f').1.2
  have hres : ∀ f', 0 ≤ tailCF (tailRes f') ∧
      (1 + 1 / 2 ^ 198) * tailCF (tailRes f') + 1 / 2 ^ 100 ≤ ((tailRes f').f : ℝ) :=
    fun f' => tailCF_ok _ (tail_f_range f').2.1 (tail_f_range f').2.2
  refine ⟨r20, r21, r10, r11, fun f' => ?_, fun f' => ?_, fun f' => ?_, fun f' => ?_, caps⟩
  · exact corrSchur_of_bounds q hq4 _ _ (hord f').1 (hord f').2 le_rfl (c20 f')
  · exact corrSchur_of_bounds q hq4 _ _ (hord f').1 (hord f').2 le_rfl (c21 f')
  · exact corrSchur_of_bounds q hq4 _ _ (hres f').1 (hres f').2 le_rfl (c10 f')
  · exact corrSchur_of_bounds q hq4 _ _ (hres f').1 (hres f').2 le_rfl (c11 f')

end Sarkozy.TailCorr

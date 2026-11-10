module

public import Sarkozy.BlockRows.UpperJoint
public import Sarkozy.BlockRows.UpperProduct
public import Sarkozy.BlockInputs.UpperLayer

@[expose] public section

/-!
# Block rows, VII: the upper rows (V2) from per-prime joint rows

`paper/sections/25_upper_reference.tex`, (V2) of `subsec:upper-reference-rp`,
`lem:upper-reference-rp`(ii), `def:record:upper-bands` (F3), (F5)(a) and its block form ("For
(F5): let the block have least prime `b`, `r_b = b^{-1/2} ≤ r₀`…"); `cor:joint-completion-blocks`.

BA's `UpperBandRowsV2 k` (block level, kind C) asks, on every block of band `k`, for the rows of
the coordinate `0` at every field type `𝔣'` to be valid (`ValidRows`) with the recorded ordinary
(two layers) and reserved (one layer) inputs `(f, h, M)`. For the bands the paper uses the joint
rows, `lem:five-type`(f) through `cor:joint-completion-blocks` ((F5)(a)). Here this is **proved**
from per-prime statements:

* `UpperRowGate X n M f h ℓ c_mar c_F c_E k_J t_Y`: the gates of (F5)(a) at `p₀ = X` (the band
  start) and `n̄ = n`: `H = e^{n̄ ℓ_mid}`, `υ² = e^{n̄ c_mar²/p₀} - 1`,
  `E_T = (2υ + υ²)(e^{n̄ c_F r₀} - 1)`, `0 < t_Y ≤ H⁻¹`, `M ≥ H + t_Y`, `c_F r₀, c_E r₀ < 1`,
  `(c_F² + c_E²) r₀ ≤ k_J` and `f ≥ [H{(k_J - h)_+ r₀ + E_T} + (H + H²/t_Y) υ²]/r₀`;
* `joint_eval`: the block evaluation (`r_b ≤ r₀`): `f_J(r_b) ≤` the gate's right side;
* `UpperRowCert k` (**the band certificate**, kind C + F): for each field type `𝔣'` and both layer
  sets, constants with `UpperRowGate` at the recorded input, and `JointPrimeCert` for the row laws
  of `λ_p(G_{E𝔣'})`, `λ_p(G_{F𝔣'})` at every class-three prime of the band (under Weil's bound);
* **`upperBandRowsV2_of_cert`**: BA's `UpperBandRowsV2 k` from `UpperRowCert k`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.Labellings Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.FiveType.TwoCoord
  Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.BlockSpecPaper Sarkozy.BlockInputs

/-! ## The gates of (F5)(a) and the block evaluation -/

/-- **The gates of (F5)(a)** at `p₀ = X` with `n̄ = n`, for the recorded input `(f, h, M)`. -/
def UpperRowGate (X n M f h ℓ cmar cF cE kJ tY : ℝ) : Prop :=
  0 ≤ ℓ ∧ 0 ≤ cmar ∧ 0 ≤ cF ∧ 0 ≤ cE ∧ 0 ≤ h ∧ 0 < tY ∧ tY ≤ (Real.exp (n * ℓ))⁻¹ ∧
    Real.exp (n * ℓ) + tY ≤ M ∧ cF * (√X)⁻¹ < 1 ∧ cE * (√X)⁻¹ < 1 ∧
    (cF ^ 2 + cE ^ 2) * (√X)⁻¹ ≤ kJ ∧
    (Real.exp (n * ℓ) * (max (kJ - h) 0 * (√X)⁻¹ +
        (2 * √(Real.exp (n * cmar ^ 2 * (√X)⁻¹ ^ 2) - 1) +
          √(Real.exp (n * cmar ^ 2 * (√X)⁻¹ ^ 2) - 1) ^ 2) *
        (Real.exp (n * cF * (√X)⁻¹) - 1)) +
      (Real.exp (n * ℓ) + Real.exp (n * ℓ) ^ 2 / tY) *
        √(Real.exp (n * cmar ^ 2 * (√X)⁻¹ ^ 2) - 1) ^ 2) / (√X)⁻¹ ≤ f

theorem sq_sqrt_exp_sub_one {y : ℝ} (hy : 0 ≤ y) : √(Real.exp y - 1) ^ 2 = Real.exp y - 1 :=
  Real.sq_sqrt (by linarith [Real.add_one_le_exp y])

/-- **The block evaluation of (F5)(a)**: for `0 < r ≤ r₀`, `υ = (e^{n c_mar² r²} - 1)^{1/2}` and
`r_p ≤ r`, `f_J(H, k_J, h, r, E_T(υ, c_F, r_p), t_Y, υ)` is at most the gate's right side at
`r₀`. -/
theorem joint_eval {ι : Type*} [Fintype ι] (rp : ι → ℝ) {r r0 n H cmar cF kJ h tY : ℝ}
    (hr : 0 < r) (hrr0 : r ≤ r0) (hcard : (Fintype.card ι : ℝ) ≤ n)
    (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ r) (hH : 0 ≤ H) (hcF : 0 ≤ cF) (htY : 0 < tY) :
    fJ H kJ h r (ET √(Real.exp (n * cmar ^ 2 * r ^ 2) - 1) cF rp) tY
        √(Real.exp (n * cmar ^ 2 * r ^ 2) - 1) ≤
      (H * (max (kJ - h) 0 * r0 +
          (2 * √(Real.exp (n * cmar ^ 2 * r0 ^ 2) - 1) +
            √(Real.exp (n * cmar ^ 2 * r0 ^ 2) - 1) ^ 2) * (Real.exp (n * cF * r0) - 1)) +
        (H + H ^ 2 / tY) * √(Real.exp (n * cmar ^ 2 * r0 ^ 2) - 1) ^ 2) / r0 := by
  have hr0 : 0 < r0 := lt_of_lt_of_le hr hrr0
  have hn0 : 0 ≤ n := le_trans (Nat.cast_nonneg _) hcard
  set t : ℝ := r / r0 with ht
  have ht0 : 0 ≤ t := div_nonneg hr.le hr0.le
  have ht1 : t ≤ 1 := (div_le_one hr0).mpr hrr0
  set υ : ℝ := √(Real.exp (n * cmar ^ 2 * r ^ 2) - 1) with hυ
  set υ0 : ℝ := √(Real.exp (n * cmar ^ 2 * r0 ^ 2) - 1) with hυ0
  have hY : 0 ≤ n * cmar ^ 2 * r0 ^ 2 := by positivity
  -- `υ² ≤ t υ₀²` and `υ ≤ υ₀`
  have hυ2 : υ ^ 2 ≤ t * υ0 ^ 2 := by
    rw [hυ, hυ0, sq_sqrt_exp_sub_one (by positivity), sq_sqrt_exp_sub_one hY]
    have h1 := exp_mul_sub_one_le (y := n * cmar ^ 2 * r0 ^ 2) (sq_nonneg t)
      (by nlinarith)
    have e : t ^ 2 * (n * cmar ^ 2 * r0 ^ 2) = n * cmar ^ 2 * r ^ 2 := by
      rw [ht]
      field_simp
    rw [e] at h1
    have hE0 : 0 ≤ Real.exp (n * cmar ^ 2 * r0 ^ 2) - 1 := by
      linarith [Real.add_one_le_exp (n * cmar ^ 2 * r0 ^ 2)]
    have htt : t ^ 2 ≤ t := by nlinarith
    have h2 := mul_le_mul_of_nonneg_right htt hE0
    linarith
  have hυ0n : 0 ≤ υ0 := Real.sqrt_nonneg _
  have hυn : 0 ≤ υ := Real.sqrt_nonneg _
  have hυle : υ ≤ υ0 := by
    have : υ ^ 2 ≤ υ0 ^ 2 := hυ2.trans (by nlinarith [sq_nonneg υ0])
    exact (pow_le_pow_iff_left₀ hυn hυ0n two_ne_zero).mp this
  -- `E_T ≤ t E_T(r₀)`
  have hET : ET υ cF rp ≤ t * ((2 * υ0 + υ0 ^ 2) * (Real.exp (n * cF * r0) - 1)) := by
    have h1 := ET_le_exp (n := Fintype.card ι) hυn hcF hr.le hrp le_rfl
    have h2 : Real.exp ((Fintype.card ι : ℕ) * cF * r) - 1 ≤ Real.exp (n * cF * r) - 1 := by
      have := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcard hcF) hr.le)
      linarith
    have h3 : Real.exp (n * cF * r) - 1 ≤ t * (Real.exp (n * cF * r0) - 1) := by
      have := exp_mul_sub_one_le (y := n * cF * r0) ht0 ht1
      have e : t * (n * cF * r0) = n * cF * r := by rw [ht]; field_simp
      rwa [e] at this
    have h4 : 2 * υ + υ ^ 2 ≤ 2 * υ0 + υ0 ^ 2 := by nlinarith
    have h5 : 0 ≤ Real.exp (n * cF * r) - 1 := by
      linarith [Real.add_one_le_exp (n * cF * r), Real.exp_nonneg (n * cF * r),
        show 0 ≤ n * cF * r by positivity]
    have h6 : 0 ≤ 2 * υ + υ ^ 2 := by positivity
    calc ET υ cF rp ≤ (2 * υ + υ ^ 2) * (Real.exp ((Fintype.card ι : ℕ) * cF * r) - 1) := h1
      _ ≤ (2 * υ + υ ^ 2) * (Real.exp (n * cF * r) - 1) := mul_le_mul_of_nonneg_left h2 h6
      _ ≤ (2 * υ0 + υ0 ^ 2) * (t * (Real.exp (n * cF * r0) - 1)) :=
          mul_le_mul h4 h3 h5 (by positivity)
      _ = t * ((2 * υ0 + υ0 ^ 2) * (Real.exp (n * cF * r0) - 1)) := by ring
  -- assemble
  unfold fJ
  rw [div_le_div_iff₀ hr hr0]
  have hHt : 0 ≤ H + H ^ 2 / tY := by positivity
  have hm : 0 ≤ max (kJ - h) 0 := le_max_right _ _
  have e1 : r = t * r0 := by rw [ht]; field_simp
  have k1 : H * ET υ cF rp ≤ H * (t * ((2 * υ0 + υ0 ^ 2) * (Real.exp (n * cF * r0) - 1))) :=
    mul_le_mul_of_nonneg_left hET hH
  have k2 : (H + H ^ 2 / tY) * υ ^ 2 ≤ (H + H ^ 2 / tY) * (t * υ0 ^ 2) :=
    mul_le_mul_of_nonneg_left hυ2 hHt
  rw [e1]
  nlinarith [mul_le_mul_of_nonneg_right k1 hr0.le, mul_le_mul_of_nonneg_right k2 hr0.le]

/-! ## The band certificate -/

/-- `n̄ = L_band / log X` for band `k` (the largest number of primes of a block of the band). -/
noncomputable def bandLen (k : Fin 310) : ℝ :=
  ((UpperRecords.CompletionData.record k).budget : ℝ) / Real.log (bandOf k).1

/-- **The upper row certificate of band `k`** ((F3), (F5)(a), `cor:joint-completion-blocks`,
`cert:upper-band-inputs`(c)). For every field type `𝔣'`, for the two-layer rows with the ordinary
input `bandOrd k 𝔣'` and for the one-layer rows with the reserved input `bandRes k 𝔣'`:
constants `(ℓ_mid, c_mar, c_F, c_E, k_J, t_Y)` with the gates of (F5)(a) at the band start, and
the per-prime joint rows `JointPrimeCert` of the row laws of `λ_p(G_{E𝔣'})`, `λ_p(G_{F𝔣'})` at
every class-three prime `p` of the band (under Weil's bound, `p ≥ 2²⁰`), with the recorded `h`.
*Hypothesis* (kind C + F: per-prime analytic statements with per-band constants). -/
def UpperRowCert (k : Fin 310) : Prop :=
  ∀ f' : FieldTy,
    (∃ ℓ cmar cF cE kJ tY : ℝ,
      UpperRowGate (bandOf k).1 (bandLen k) (UpperRecords.bandOrd k f').M
        (UpperRecords.bandOrd k f').f (UpperRecords.bandOrd k f').h ℓ cmar cF cE kJ tY ∧
      ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → (bandOf k).1 ≤ p → p < (bandOf k).2 →
        WeilBound (ZMod p) → (2 : ℝ) ^ 20 ≤ p → ∀ hne : TailNonempty p,
          JointPrimeCert (rowLaw2 (tailFieldLaws p hne) .E rfl f')
            (rowLaw2 (tailFieldLaws p hne) .F rfl f') (√(p : ℝ))⁻¹ ℓ cmar cF cE kJ
            (UpperRecords.bandOrd k f').h) ∧
    (∃ ℓ cmar cF cE kJ tY : ℝ,
      UpperRowGate (bandOf k).1 (bandLen k) (UpperRecords.bandRes k f').M
        (UpperRecords.bandRes k f').f (UpperRecords.bandRes k f').h ℓ cmar cF cE kJ tY ∧
      ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → (bandOf k).1 ≤ p → p < (bandOf k).2 →
        WeilBound (ZMod p) → (2 : ℝ) ^ 20 ≤ p → ∀ hne : TailNonempty p,
          JointPrimeCert (rowLaw1 (tailFieldLaws p hne) .E rfl f')
            (rowLaw1 (tailFieldLaws p hne) .F rfl f') (√(p : ℝ))⁻¹ ℓ cmar cF cE kJ
            (UpperRecords.bandRes k f').h)

theorem ET_nonneg' {ι : Type*} [Fintype ι] {υ cF : ℝ} {rp : ι → ℝ} (hυ : 0 ≤ υ) (hcF : 0 ≤ cF)
    (hrp : ∀ i, 0 ≤ rp i) : 0 ≤ ET υ cF rp := by
  unfold ET
  refine mul_nonneg (by positivity) ?_
  have h := prod_le_prod₀ (s := (univ : Finset ι)) (f := fun _ => (1 : ℝ))
    (g := fun i => 1 + cF * rp i) (fun _ _ => zero_le_one)
    (fun i _ => by nlinarith [mul_nonneg hcF (hrp i)])
  rw [prod_const_one] at h
  linarith

/-- **Valid rows (V2), joint form, from the gate and the per-prime joint rows** for one layer set:
the common block step of the two-layer and the one-layer rows. -/
theorem validRows_of_joint {ι : Type} [Fintype ι] [DecidableEq ι] {Y : ι → Type}
    [∀ i, Fintype (Y i)] [∀ i, DecidableEq (Y i)] {𝔛 : Type} [Fintype 𝔛] [DecidableEq 𝔛]
    (s : 𝔛 ≃ ∀ i, Y i) {piE piF : FiniteLaw (Fin 3 → 𝔛)} (piL : FiniteLaw (ZMod 6 → 𝔛))
    {piEp piFp : ∀ i, FiniteLaw (Fin 3 → Y i)} (hPE : IsProd3 s piE piEp)
    (hPF : IsProd3 s piF piFp)
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (hsupp : GamSupported piE piF)
    (hL : ∀ (k : Fin 6) (Ψ : ZMod 6 → 𝔛), piL.weight (Ψ ∘ g6 k) = piL.weight Ψ)
    (hexchp : ∀ i (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Y i),
      (piEp i).weight (ω ∘ σ) = (piEp i).weight ω)
    (rp : ι → ℝ) {X b n M f h ℓ cmar cF cE kJ tY : ℝ} (hX : 0 < X) (hXb : X ≤ b)
    (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ (√b)⁻¹) (hcard : (Fintype.card ι : ℝ) ≤ n)
    (hg : UpperRowGate X n M f h ℓ cmar cF cE kJ tY)
    (hc : ∀ i, JointPrimeCert (piEp i) (piFp i) (rp i) ℓ cmar cF cE kJ h) :
    ValidRows (datumOfGam piE piF piL hexch hsupp hL) (√b)⁻¹ f h M := by
  obtain ⟨hℓ, hcm, hcF, hcE, hh, htY, htH, hHM, hcFr0, hcEr0, hkJ0, hf⟩ := hg
  have hb : 0 < b := lt_of_lt_of_le hX hXb
  have hr : 0 < (√b)⁻¹ := inv_pos.mpr (Real.sqrt_pos.mpr hb)
  have hrr0 : (√b)⁻¹ ≤ (√X)⁻¹ := inv_anti₀ (Real.sqrt_pos.mpr hX) (Real.sqrt_le_sqrt hXb)
  have hcFr : cF * (√b)⁻¹ < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr0 hcF) hcFr0
  have hcEr : cE * (√b)⁻¹ < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr0 hcE) hcEr0
  have hkJ : (cF ^ 2 + cE ^ 2) * (√b)⁻¹ ≤ kJ :=
    le_trans (mul_le_mul_of_nonneg_left hrr0 (by positivity)) hkJ0
  right
  right
  refine ⟨Real.exp (n * ℓ), √(Real.exp (n * cmar ^ 2 * (√b)⁻¹ ^ 2) - 1),
    ET √(Real.exp (n * cmar ^ 2 * (√b)⁻¹ ^ 2) - 1) cF rp, kJ, tY, hh,
    ET_nonneg' (Real.sqrt_nonneg _) hcF (fun i => (hrp i).1), htY, htH, hHM,
    (joint_eval rp hr hrr0 hcard hrp (Real.exp_pos _).le hcF htY).trans hf, fun ξ hξ => ?_⟩
  exact ⟨kernelOf_exactE piE hexch hξ,
    jointData_of_primeCerts s hPE hPF hexch hexchp rp hr.le hrp hcard hℓ hcm hcF hcE hh hcFr
      hcEr hkJ hc hξ⟩

/-- **BA's upper rows (V2) from the band certificate** (`lem:upper-reference-rp`(ii), (V2), with
(F5)(a) and `cor:joint-completion-blocks`). -/
theorem upperBandRowsV2_of_cert {k : Fin 310} (hC : UpperRowCert k) : UpperBandRowsV2 k := by
  intro ι _ _ pr _ b _ h3 hband hbud hb hb' hne hW' hp'
  have hP3 : (P3 : ℝ) ≤ (bandOf k).1 := by exact_mod_cast P3_le_bandStart k
  have hX0 : (0 : ℝ) < (bandOf k).1 := lt_of_lt_of_le (by norm_num [P3]) hP3
  have hlog : 0 < Real.log (bandOf k).1 :=
    Real.log_pos (lt_of_lt_of_le (by norm_num [P3]) hP3)
  have hXp : ∀ j, ((bandOf k).1 : ℝ) ≤ (pr j : ℝ) := fun j => by exact_mod_cast (hband j).1
  have hXb : ((bandOf k).1 : ℝ) ≤ b := by
    obtain ⟨j, hj⟩ := hb'
    rw [← hj]
    exact hXp j
  have hb0 : (0 : ℝ) < b := lt_of_lt_of_le hX0 hXb
  have hcard : (Fintype.card ι : ℝ) ≤ bandLen k := by
    unfold bandLen
    rw [le_div_iff₀ hlog]
    calc (Fintype.card ι : ℝ) * Real.log (bandOf k).1 = ∑ _j : ι, Real.log (bandOf k).1 := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ∑ j, Real.log (pr j) := sum_le_sum fun j _ => Real.log_le_log hX0 (hXp j)
      _ ≤ _ := hbud
  have hrp : ∀ j, 0 ≤ (√(pr j : ℝ))⁻¹ ∧ (√(pr j : ℝ))⁻¹ ≤ (√(b : ℝ))⁻¹ := fun j =>
    ⟨inv_nonneg.mpr (Real.sqrt_nonneg _), inv_anti₀ (Real.sqrt_pos.mpr hb0)
      (Real.sqrt_le_sqrt (by exact_mod_cast hb j))⟩
  rw [BlockAdapter.rpow_neg_half_eq b]
  refine ⟨fun f' => ?_, fun f' => ?_⟩
  · obtain ⟨⟨ℓ, cmar, cF, cE, kJ, tY, hg, hpc⟩, -⟩ := hC f'
    exact validRows_of_joint (objSplit pr (f'.Obj × ZMod 2)) _
      (rowLaw2_isProd3 pr hne .E rfl f') (rowLaw2_isProd3 pr hne .F rfl f') _ _ _
      (fun i => ((primeDatumHyp pr hne hW' hp' i).two0 f').exch) (fun j => (√(pr j : ℝ))⁻¹)
      hX0 hXb hrp hcard hg
      (fun i => hpc (pr i) (h3 i) (hband i).1 (hband i).2 (hW' i) (hp' i) (primeNonempty pr hne i))
  · obtain ⟨-, ⟨ℓ, cmar, cF, cE, kJ, tY, hg, hpc⟩⟩ := hC f'
    exact validRows_of_joint (objSplit pr (f'.Obj × Unit)) _
      (rowLaw1_isProd3 pr hne .E rfl f') (rowLaw1_isProd3 pr hne .F rfl f') _ _ _
      (fun i => ((primeDatumHyp pr hne hW' hp' i).one0 f').exch) (fun j => (√(pr j : ℝ))⁻¹)
      hX0 hXb hrp hcard hg
      (fun i => hpc (pr i) (h3 i) (hband i).1 (hband i).2 (hW' i) (hp' i) (primeNonempty pr hne i))

end Sarkozy.BlockRows

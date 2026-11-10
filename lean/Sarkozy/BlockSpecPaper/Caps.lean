module

public import Sarkozy.BlockSpecPaper.CapChecks
public import Sarkozy.BlockSpecPaper.Lemmas
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# The ALLp caps in block-cap form (`lem:front12:reference`(ii), `lem:majorant`(c))

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(ii);
`paper/sections/25_upper_reference.tex` and W7's `UpperReference/BlockCaps.lean` (the block step
`cut_block_cap`, `lem:spec:tensorcomp`, `lem:majorant`(c)).

The paper's block caps come from per-prime cut bounds `-g p^{-1/2} ⪯ Op ⪯ 1 + B/p` for the primes
`p ≥ X` of a piece through the tensor step, which gives the block cap
`g exp(B L/(X log X)) b^{-1/2}` for a block of log-length `≤ L` with least prime `b` (W7's
`cut_block_cap`). The records store `d = g exp(B L_loc/(X log X))` (upper endpoint, `L_loc = 585`)
with the per-prime constants `g` (`clean_g`) and `B` (`positive_B`) of each cut
(`AllpConsts.lean`).

* **`allp_blockCap_le`** (kernel-checked arithmetic): for every piece and each of the four cuts
  L20, L10, L21, E21, `capVal i c = g exp(B·570/(X_i log X_i)) ≤ cap` (the record's `d`, `d₁`,
  `k_L`, `k_E`). The F21 cap `k_D` is not of this form (its `clean_g` exceeds it) and stays at its
  recorded value. The proof uses `log X ≥ k log 2 + 1 - 2^k/X` (`log_two_gt_d9`,
  `one_sub_inv_le_log_of_pos`), `exp t ≤ 1/(1 - t)` and a `decide +kernel` check of the rational
  inequalities (`allp_capCheck`).
* `rootEnvelope_mono`, `middleLayerCaps_mono`: a smaller cap may be used (`compF0_positive`,
  `middleDiag_reserved_positive`, `below_mono_coeff`).
* **`MiddleUniformCapLemma i`**, `MiddleIndividualCapLemma i u`: `MiddleUniformLemma` with the root
  envelopes and layer caps at the block-cap values `capVal i c` (the form of `cut_block_cap`'s
  output at `L = 570`, `X = X_i`, `b` the least prime) instead of the recorded caps; the rows are
  unchanged. *Hypotheses* (spectral). `middleUniformLemma_of_cap`, `middleIndividualLemma_of_cap`
  derive the recorded-cap forms.
-/

open Finset

namespace Sarkozy.BlockSpecPaper

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.FiveType
  Sarkozy.FiveType.TwoCoord Sarkozy.PartVLaws Sarkozy.BlockSpecPaper.AllpData

/-! ## The arithmetic of the block caps -/

/-- `log X ≥ k log 2 + (1 - 2^k/X) > k · 0.6931471803 + (1 - 2^k/X)` for `2^k ≤ X`. -/
theorem logLower_le {X k : ℕ} (hk : 2 ^ k ≤ X) : ((logLower X k : ℚ) : ℝ) ≤ Real.log X := by
  have hk' : (2 : ℝ) ^ k ≤ X := by exact_mod_cast hk
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hX : (0 : ℝ) < X := lt_of_lt_of_le h2k hk'
  have hsplit : Real.log X = k * Real.log 2 + Real.log (X / 2 ^ k) := by
    rw [Real.log_div hX.ne' h2k.ne', Real.log_pow]
    ring
  have h1 : (1 : ℝ) - 2 ^ k / X ≤ Real.log (X / 2 ^ k) := by
    have := Real.one_sub_inv_le_log_of_pos (div_pos hX h2k)
    rwa [inv_div] at this
  have h2 : (k : ℝ) * (6931471803 / 10 ^ 10) ≤ k * Real.log 2 := by
    have := Real.log_two_gt_d9
    exact mul_le_mul_of_nonneg_left (by norm_num at this ⊢; linarith) (Nat.cast_nonneg k)
  unfold logLower
  push_cast
  rw [hsplit]
  linarith

/-- **The block-cap inequality**: if `0 < ℓ ≤ log X`, `t̄ = B·570/(X ℓ) < 1` and `g/(1 - t̄) ≤ cap`,
then `g exp(B·570/(X log X)) ≤ cap`. -/
theorem blockCap_le {g B X ℓ cap : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 0 < X) (hℓ : 0 < ℓ)
    (hℓX : ℓ ≤ Real.log X) (ht : B * 570 / (X * ℓ) < 1)
    (hcap : g / (1 - B * 570 / (X * ℓ)) ≤ cap) :
    g * Real.exp (B * 570 / (X * Real.log X)) ≤ cap := by
  set t := B * 570 / (X * ℓ) with ht_def
  have htt : B * 570 / (X * Real.log X) ≤ t :=
    div_le_div_of_nonneg_left (by positivity) (mul_pos hX hℓ) (mul_le_mul_of_nonneg_left hℓX hX.le)
  have h1t : 0 < 1 - t := by linarith
  have hexp : Real.exp t ≤ 1 / (1 - t) := by
    rw [le_div_iff₀ h1t]
    have h := Real.add_one_le_exp (-t)
    have hprod : Real.exp t * Real.exp (-t) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith [Real.exp_pos t]
  calc g * Real.exp (B * 570 / (X * Real.log X)) ≤ g * Real.exp t :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htt) hg
    _ ≤ g * (1 / (1 - t)) := mul_le_mul_of_nonneg_left hexp hg
    _ = g / (1 - t) := by ring
    _ ≤ cap := hcap

/-- **The block-cap value** of cut `c` on piece `i`: `g exp(B·570/(X_i log X_i))`, the factor of
`b^{-1/2}` in `cut_block_cap` at `L = 570`, `X = X_i`. -/
noncomputable def capVal (i : Fin 33) (c : Fin 5) : ℝ :=
  (allpG i c : ℝ) *
    Real.exp ((allpB i c : ℝ) * 570 / ((pieceStart i : ℝ) * Real.log (pieceStart i)))

/-- **The recorded ALLp caps dominate the block-cap values** (kernel-checked arithmetic of
`lem:front12:reference`(ii) at `L = 570`). -/
theorem allp_blockCap_le (i : Fin 33) (c : Fin 5) (hc : c ≠ 3) :
    capVal i c ≤ (allpCap i c : ℝ) := by
  obtain ⟨hk, hℓ, hg, hB, ht, hcap⟩ := allp_capCheck i c hc
  have hk' : (2 : ℝ) ^ allpLog2 i ≤ pieceStart i := by exact_mod_cast hk
  have hX : (0 : ℝ) < pieceStart i := lt_of_lt_of_le (by positivity) hk'
  refine blockCap_le (ℓ := ((logLower (pieceStart i) (allpLog2 i) : ℚ) : ℝ)) (by exact_mod_cast hg)
    (by exact_mod_cast hB) hX (by exact_mod_cast hℓ) (logLower_le hk) ?_ ?_
  · have h := (Rat.cast_lt (K := ℝ)).mpr ht
    push_cast at h
    exact h
  · have h := (Rat.cast_le (K := ℝ)).mpr hcap
    push_cast at h
    exact h

/-! ## A smaller cap may be used -/

/-- **The root envelope is monotone in the cap** (`compF0_positive`). -/
theorem rootEnvelope_mono {Λ : Type} [Fintype Λ] [DecidableEq Λ] {𝔛 : Type} [Fintype 𝔛]
    [DecidableEq 𝔛] (D : Datum (Λ → 𝔛)) {d d' r : ℝ} (hr : 0 ≤ r) (hd : d ≤ d')
    (h : RootEnvelope D d r) : RootEnvelope D d' r :=
  Reserved.below_mono_coeff (chamberCut 0) D.compF0_positive (mul_le_mul_of_nonneg_right hd hr) h

/-- **The layer caps are monotone in the caps** (`middleDiag_reserved_positive`). -/
theorem middleLayerCaps_mono {𝔛 : Type} [Fintype 𝔛] [DecidableEq 𝔛] (F : MiddleFieldLaws 𝔛)
    {k k' : PType → ℝ} {r : ℝ} (hr : 0 ≤ r) (hk : ∀ t, k t ≤ k' t) (h : MiddleLayerCaps F k r) :
    MiddleLayerCaps F k' r := fun t φ =>
  Reserved.below_mono_coeff reservedCut (middleDiag_reserved_positive F t φ)
    (mul_le_mul_of_nonneg_right (hk t) hr) (h t φ)

/-! ## The middle lemmas at the block-cap values -/

/-- The layer caps at the block-cap values: `k_L ← L21`, `k_S = k_R = k_C ← E21`; `k_D` (F21) at
its recorded value, which is not of block-cap form. -/
noncomputable def capK (i : Fin 33) : PType → ℝ
  | .L => capVal i 2
  | .D => (allpInputs i).k .D
  | .S | .R | .C => capVal i 4

theorem capK_le (i : Fin 33) (t : PType) : capK i t ≤ (allpInputs i).k t := by
  cases t
  · exact allp_blockCap_le i 2 (by decide)
  · exact le_rfl
  · exact allp_blockCap_le i 4 (by decide)
  · exact allp_blockCap_le i 4 (by decide)
  · exact allp_blockCap_le i 4 (by decide)

/-- **`lem:front12:reference`(i),(ii) on piece `i`, uniform root, at the block-cap values.** As
`MiddleUniformLemma`, with the root envelopes (L20, L10) and the layer caps at `capVal i c`, the
output form of the tensor step. *Hypothesis* (spectral). -/
def MiddleUniformCapLemma (i : Fin 33) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) (allpInputs i).f₂ (allpInputs i).h₂
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂ pr hne)) (capVal i 0)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) (capVal i 1)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      MiddleLayerCaps (middleBlockFieldLaws pr hne (uniformRoot pr hne)) (capK i)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- **`lem:front12:reference`(i),(ii) on piece `i`, individual-square root `u`, at the block-cap
values.** *Hypothesis* (spectral). -/
def MiddleIndividualCapLemma (i : Fin 33) (u : ℚ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ),
    Function.Injective pr → (∀ j, pr j % 4 = 3) →
    (∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i) →
    (∑ j, Real.log (pr j) ≤ middleBudget) → (∀ j, b ≤ pr j) → (∃ j, pr j = b) →
    ∀ hne : MiddleNonempty pr,
      RowBounds (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (allpInputs i).f₂
        (allpInputs i).h₂ ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) (allpInputs i).f₁ (allpInputs i).h₁
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₂_individual pr hne u)) (capVal i 0)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) (capVal i 1)
        ((b : ℝ) ^ (-(1 / 2 : ℝ))) ∧
      MiddleLayerCaps (middleBlockFieldLaws pr hne (individualBlockRoot pr u hne.L2)) (capK i)
        ((b : ℝ) ^ (-(1 / 2 : ℝ)))

/-- The block-cap form implies the recorded-cap form (uniform root). -/
theorem middleUniformLemma_of_cap {i : Fin 33} (h : MiddleUniformCapLemma i) :
    MiddleUniformLemma i := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  have hr : 0 ≤ (b : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2, h3', h4, h5⟩ := h ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨h1, h2, rootEnvelope_mono _ hr (allp_blockCap_le i 0 (by decide)) h3',
    rootEnvelope_mono _ hr (allp_blockCap_le i 1 (by decide)) h4,
    middleLayerCaps_mono _ hr (capK_le i) h5⟩

/-- The block-cap form implies the recorded-cap form (individual-square root). -/
theorem middleIndividualLemma_of_cap {i : Fin 33} {u : ℚ} (h : MiddleIndividualCapLemma i u) :
    MiddleIndividualLemma i u := by
  intro ι _ _ pr _ b hinj h3 hpc hbud hb hb' hne
  have hr : 0 ≤ (b : ℝ) ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  obtain ⟨h1, h2, h3', h4, h5⟩ := h ι pr b hinj h3 hpc hbud hb hb' hne
  exact ⟨h1, h2, rootEnvelope_mono _ hr (allp_blockCap_le i 0 (by decide)) h3',
    rootEnvelope_mono _ hr (allp_blockCap_le i 1 (by decide)) h4,
    middleLayerCaps_mono _ hr (capK_le i) h5⟩

end Sarkozy.BlockSpecPaper

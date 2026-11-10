module

public import Sarkozy.SignedDecompCrude.Main
public import Sarkozy.SignedDecompCrude.Removed
public import Sarkozy.SignedDecompCrude.Nonstar

@[expose] public section

/-!
# `NewDecomp` at the paper's fold records, at the crude constant `e_sg′` (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), last claim, at every prime of
every middle block of the F1 data, with the removed query proved (`removedBound_crude`).

* **`kRQ p = 8(2 - t)/((1 - 1/p)(1 - 2/p))`** (the proved removed-query constant), and
  **`esgCrude κF nF p = κF(p) + c_g/q + 6 (D_g/q) Γ_A r + (nF(p) + kRQ p)/(1 - e₀)`** at
  `q = 1/p`, `r = p^{-1/2}`, `e₀ = e₀(p)`, `Γ_A = GammaA(1/p, p^{-1/2})` (W6's frame majorant).
* **`newDecomp_prime`**: at a prime of a middle block, (K) at `κF(p)` and (NS) at `nF(p)` give
  `NewDecomp` at `esgCrude κF nF p`.
* **`CrudeNewInputs κF nF C`** ((K) and (NS) at every prime of every middle block),
  **`CrudeNewInputs.toCrudeSD`**: with the gates `PieceGate (esgCrude κF nF) 38 k`, ND's
  `CrudeSD`, hence PG's `SignedDecompInputsC` (`CrudeSD.toSD`).
* **With (NS) proved** (`nonstarBound_tensor`, constant `nT p`): **`RecordInputs κF C`** ((K) only)
  and **`RecordInputs.toSD`**.
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents Sarkozy.Labellings
open Sarkozy.SignedEstimates Sarkozy.SignedDecomp Sarkozy.MiddleRecords
open Sarkozy.MiddleComparison (signedCoef)
open Sarkozy.PartV (MiddleNonempty)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.PartVLaws (PaperBlockSpec blockPrimes)
open Sarkozy.MainFinalF1 (bOf Blk SignedSpec specF analyticInputs)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.BlockSpecPaper
open Sarkozy.AnalyticCells (f1Cell)

/-- **The removed-query constant** `8(2 - t)/((1 - 1/p)(1 - 2/p))` at `t = tPaper`. -/
noncomputable def kRQ (p : ℕ) : ℝ :=
  2 * (4 * (2 - tPaper)) / ((1 - (p : ℝ)⁻¹) * (1 - 2 * (p : ℝ)⁻¹))

/-- **The crude constant `e_sg′(p)`** of the signed record, given the constants `κF(p)` of (K)
and `nF(p)` of (NS). -/
noncomputable def esgCrude (κF nF : ℕ → ℝ) (p : ℕ) : ℝ :=
  esgND (p : ℝ)⁻¹ (√(p : ℝ))⁻¹ (e0 (p : ℝ)) (GammaA (1 / (p : ℝ)) (√(1 / (p : ℝ)))) (κF p) (nF p)
    (kRQ p)

theorem newDecomp_mono {F : Type} [Field F] [Fintype F] [DecidableEq F]
    {m : (Fin 3 → F) → ℝ} {N : Matrix (Fin 3 → F) (Fin 3 → F) ℝ} {t e e' : ℝ}
    (h : NewDecomp m N t e) (he : e ≤ e') : NewDecomp m N t e' := by
  intro f g hf hg
  refine (h f g hf hg).trans ?_
  have hq : (0 : ℝ) ≤ (Fintype.card F : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he hq)
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))

theorem DgC_nonneg {e : ℝ} (he0 : 0 ≤ e) : 0 ≤ DgC e := by
  unfold DgC; positivity

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- **`prop:signed-bounds`(c), the centred signed record, at a prime of a middle block**, from
(K) at `κ` and (NS) at `n`, with the removed query proved: `NewDecomp` at
`esgND(1/p, p^{-1/2}, e₀, Γ_A, κ, n, kRQ p)`. -/
theorem newDecomp_prime (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) (i : ι) {N : Matrix (Ai pr i) (Ai pr i) ℝ} {κ n : ℝ} (hn : 0 ≤ n)
    (hK : RecordForm (hne.F2 i) N tPaper κ) (hNS : NonstarBound (F := ZMod (pr i)) tPaper n) :
    NewDecomp (mP hne i) N tPaper (esgND (pr i : ℝ)⁻¹ (√(pr i : ℝ))⁻¹ (e0 (pr i : ℝ))
      (GammaA (1 / (pr i : ℝ)) (√(1 / (pr i : ℝ)))) κ n (kRQ (pr i))) := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 i
  have ht0 := tPaper_nonneg
  have ht1 := tPaper_le_one
  have hQ := removedBound_crude (F := ZMod (pr i)) hR h19' ht0 ht1
  have hk : 0 ≤ 2 * (4 * (2 - tPaper)) /
      ((1 - (Fintype.card (ZMod (pr i)) : ℝ)⁻¹) *
        (1 - 2 * (Fintype.card (ZMod (pr i)) : ℝ)⁻¹)) := by
    rw [card_zmod]
    have h19r : (19 : ℝ) ≤ (pr i : ℝ) := by exact_mod_cast h19 i
    have hp : (0 : ℝ) < (pr i : ℝ) := by linarith
    have h1 : 0 < 1 - (pr i : ℝ)⁻¹ := by
      rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
    have h2 : 0 < 1 - 2 * (pr i : ℝ)⁻¹ := by
      rw [sub_pos, ← div_eq_mul_inv, div_lt_one hp]; linarith
    have : 0 ≤ 2 * (4 * (2 - tPaper)) := by linarith
    positivity
  have h := newDecomp_of_inputs (hne.F2 i) hR h3' h19' ht0 ht1 hn hk hK hNS hQ
  rw [card_zmod] at h
  refine newDecomp_mono h ?_
  -- `Γ ≤ Γ_A`
  have h7 : (7 : ℝ) ≤ (Fintype.card (ZMod (pr i)) : ℝ) := by
    rw [card_zmod]; exact_mod_cast le_trans (by norm_num) (h19 i)
  have hΓ := gammaW_le (F := ZMod (pr i)) h7
  rw [card_zmod] at hΓ
  have h19r : (19 : ℝ) ≤ (pr i : ℝ) := by exact_mod_cast h19 i
  have hp : (0 : ℝ) < (pr i : ℝ) := by linarith
  have he0 : 0 ≤ e0 (pr i : ℝ) := by
    have := e0_nonneg (F := ZMod (pr i)) h19'
    rwa [card_zmod] at this
  unfold esgND kRQ
  have hc : 0 ≤ 6 * (DgC (e0 (pr i : ℝ)) / (pr i : ℝ)⁻¹) * (√(pr i : ℝ))⁻¹ := by
    have := DgC_nonneg he0
    positivity
  have := mul_le_mul_of_nonneg_left hΓ hc
  linarith

end Block

/-! ## At every middle block of the F1 data -/

variable (hW : Target.Weil)

/-- **(K) and (NS) at a class-three block of the F1 data**, by specification, at the constants
`κF(p)`, `nF(p)`. `True` on an upper block. -/
def SpecKN (κF nF : ℕ → ℝ) {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => ∀ i, RecordForm (M.hne.F2 i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (κF (blockPrimes bOf b i)) ∧
      NonstarBound (F := ZMod (blockPrimes bOf b i)) tPaper (nF (blockPrimes bOf b i))
  | .middleIndividual M, E => ∀ i, RecordForm (M.hne.F2 i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (κF (blockPrimes bOf b i)) ∧
      NonstarBound (F := ZMod (blockPrimes bOf b i)) tPaper (nF (blockPrimes bOf b i))
  | .middleCoherent M, E => ∀ i, RecordForm (M.hne.F2 i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (κF (blockPrimes bOf b i)) ∧
      NonstarBound (F := ZMod (blockPrimes bOf b i)) tPaper (nF (blockPrimes bOf b i))

/-- `esgCrude κF nF p ≥ 0` for `p ≥ 19`, `κF(p), nF(p) ≥ 0`. -/
theorem esgCrude_nonneg {κF nF : ℕ → ℝ} {p : ℕ} [Fact p.Prime] (hp19 : 19 ≤ p) (hκ : 0 ≤ κF p)
    (hn : 0 ≤ nF p) : 0 ≤ esgCrude κF nF p := by
  have h19r : (19 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp19
  have hp : (0 : ℝ) < (p : ℝ) := by linarith
  have he0 : 0 ≤ e0 (p : ℝ) := by
    unfold e0
    have h3' : (0 : ℝ) < p - 3 := by linarith
    have h4' : (0 : ℝ) < p - 4 := by linarith
    positivity
  have he1 : e0 (p : ℝ) < 1 := by
    unfold e0
    rw [div_lt_one (by nlinarith)]
    nlinarith
  have hΓ : 0 ≤ GammaA (1 / (p : ℝ)) (√(1 / (p : ℝ))) := by
    have h7 : (7 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) := by rw [ZMod.card]; linarith
    have h0 := gammaW_nonneg (F := ZMod p) h7
    have h1 := gammaW_le (F := ZMod p) h7
    rw [ZMod.card] at h1
    linarith
  have h1 : 0 < 1 - (p : ℝ)⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have h2 : 0 < 1 - 2 * (p : ℝ)⁻¹ := by
    rw [sub_pos, ← div_eq_mul_inv, div_lt_one hp]; linarith
  have hk : 0 ≤ kRQ p := by
    unfold kRQ
    have := tPaper_le_one
    have : 0 ≤ 2 * (4 * (2 - tPaper)) := by linarith
    positivity
  unfold esgCrude esgND
  have := DgC_nonneg he0
  have : 0 ≤ cgC (e0 (p : ℝ)) := by unfold cgC; positivity
  have h1e : 0 < 1 - e0 (p : ℝ) := by linarith
  positivity

/-- (K) and (NS) give the crude `new` input at a middle block. -/
theorem specNew_of_KN {κF nF : ℕ → ℝ} (hκ : ∀ p, 19 ≤ p → 0 ≤ κF p)
    (hn : ∀ p, 19 ≤ p → 0 ≤ nF p) {b : Blk} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecKN hW κF nF S E →
      SpecNew hW (esgCrude κF nF) S E
  | .upper _, _, _ => trivial
  | .middleUniform M, _, H =>
      ⟨fun i => esgCrude_nonneg (blockPrimes_ge19 b i) (hκ _ (blockPrimes_ge19 b i))
          (hn _ (blockPrimes_ge19 b i)),
        fun i => newDecomp_prime M.hne (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
          (blockPrimes_ge19 b) i (hn _ (blockPrimes_ge19 b i)) (H i).1 (H i).2⟩
  | .middleIndividual M, _, H =>
      ⟨fun i => esgCrude_nonneg (blockPrimes_ge19 b i) (hκ _ (blockPrimes_ge19 b i))
          (hn _ (blockPrimes_ge19 b i)),
        fun i => newDecomp_prime M.hne (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
          (blockPrimes_ge19 b) i (hn _ (blockPrimes_ge19 b i)) (H i).1 (H i).2⟩
  | .middleCoherent M, _, H =>
      ⟨fun i => esgCrude_nonneg (blockPrimes_ge19 b i) (hκ _ (blockPrimes_ge19 b i))
          (hn _ (blockPrimes_ge19 b i)),
        fun i => newDecomp_prime M.hne (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1)
          (blockPrimes_ge19 b) i (hn _ (blockPrimes_ge19 b i)) (H i).1 (H i).2⟩

variable {hW} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **The two kernel inputs of the signed record at every prime of every middle block**
(*hypotheses*, 1 field), at constants `κF(p) ≥ 0`, `nF(p) ≥ 0`:
* (K) `RecordForm` (`prop:signed-bounds`(c), Step 1: the normalizations and completions of the
  three components; the paper's `(1 + t)E_c`);
* (NS) `NonstarBound` (`lem:record:projected-nonstar`(a) for the nine nonstars; the paper's
  `2(9 - 6t)/Z`).
The removed query is proved (`removedBound_crude`). -/
structure CrudeNewInputs (κF nF : ℕ → ℝ) (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  κ_nonneg : ∀ p, 19 ≤ p → 0 ≤ κF p
  n_nonneg : ∀ p, 19 ≤ p → 0 ≤ nF p
  kn : ∀ b i, blockSite b = .inl i → SpecKN hW κF nF (specF hW A b) (C.blk b)

/-- **ND's `CrudeSD` from (K), (NS) and the gates** at `e_sg′ = esgCrude κF nF`. -/
theorem CrudeNewInputs.toCrudeSD {κF nF : ℕ → ℝ} {C : ComparisonPartsTC hW hMR hFour A}
    (H : CrudeNewInputs κF nF C) (G : ∀ k, PieceGate (esgCrude κF nF) 38 k) :
    CrudeSD (esgCrude κF nF) C :=
  ⟨fun b i hb => specNew_of_KN hW H.κ_nonneg H.n_nonneg (specF hW A b) (C.blk b) (H.kn b i hb),
    G⟩

/-- **A constructor of PG's `SignedDecompInputsC`** from (K), (NS) and the gates: `c_col = 73`
(`collisionBound_73`), `c_+ = 38` (`comp38_paper`), the removed query (`removedBound_crude`),
the star part and the transports (`newDecomp_of_inputs`) proved. -/
theorem CrudeNewInputs.toSD {κF nF : ℕ → ℝ} {C : ComparisonPartsTC hW hMR hFour A}
    (H : CrudeNewInputs κF nF C) (G : ∀ k, PieceGate (esgCrude κF nF) 38 k) :
    SignedDecompInputsC C :=
  (H.toCrudeSD G).toSD

/-! ## With the nonstars proved: one input left -/

/-- **The proved nonstar constant** `2|𝐚||𝐛|/((1 - 1/p)(1 - 2/p))` at `t = tPaper`
(`nonstarBound_tensor`). -/
noncomputable def nT (p : ℕ) : ℝ :=
  2 * (√(1 + 2 * (1 - tPaper) ^ 2) * √(1 + (1 + tPaper) ^ 2 + (1 - tPaper) ^ 2)) /
    ((1 - (p : ℝ)⁻¹) * (1 - 2 * (p : ℝ)⁻¹))

theorem nT_nonneg (p : ℕ) (hp : 19 ≤ p) : 0 ≤ nT p := by
  unfold nT
  have h19r : (19 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have h1 : 0 < 1 - (p : ℝ)⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have h2 : 0 < 1 - 2 * (p : ℝ)⁻¹ := by
    rw [sub_pos, ← div_eq_mul_inv, div_lt_one hp0]; linarith
  positivity

/-- **(NS) at every prime of a middle block**, proved (`nonstarBound_tensor`). -/
theorem nonstar_prime {ι : Type} {pr : ι → ℕ} [∀ i, Fact (pr i).Prime] (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) (i : ι) :
    NonstarBound (F := ZMod (pr i)) tPaper (nT (pr i)) := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 i
  have h := nonstarBound_tensor (F := ZMod (pr i)) hR h3' h19' tPaper
  rw [card_zmod] at h
  exact h

variable (hW) in
/-- **(K) at a class-three block of the F1 data**, by specification, at `κF(p)`. `True` on an upper
block. -/
def SpecK (κF : ℕ → ℝ) {b : Blk} : (S : PaperBlockSpec bOf b) → SignedSpec hW S → Prop
  | .upper _, _ => True
  | .middleUniform M, E => ∀ i, RecordForm (M.hne.F2 i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (κF (blockPrimes bOf b i))
  | .middleIndividual M, E => ∀ i, RecordForm (M.hne.F2 i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (κF (blockPrimes bOf b i))
  | .middleCoherent M, E => ∀ i, RecordForm (M.hne.F2 i)
      (∑ c, signedCoef tPaper c • compP M.hne (paperComponents E.down.toDC) c i) tPaper
      (κF (blockPrimes bOf b i))

theorem specKN_of_K {κF : ℕ → ℝ} {b : Blk} :
    (S : PaperBlockSpec bOf b) → (E : SignedSpec hW S) → SpecK hW κF S E →
      SpecKN hW κF nT S E
  | .upper _, _, _ => trivial
  | .middleUniform _, _, H => fun i => ⟨H i, nonstar_prime
      (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1) (blockPrimes_ge19 b) i⟩
  | .middleIndividual _, _, H => fun i => ⟨H i, nonstar_prime
      (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1) (blockPrimes_ge19 b) i⟩
  | .middleCoherent _, _, H => fun i => ⟨H i, nonstar_prime
      (fun j => (Sarkozy.FirstStagePaper.blockPrimes_mod_ge b j).1) (blockPrimes_ge19 b) i⟩

/-- **The one remaining analytic input of the signed record** (*hypothesis*, 2 fields): (K)
`RecordForm` (`prop:signed-bounds`(c), Step 1: the normalizations `z_{uv}` and the completions
`M_c` of the three components, weighted by `1 + t`; the paper's `(1 + t)E_c q`) at a constant
`κF(p) ≥ 0`, at every prime of every middle block of the F1 data. The nonstars
(`nonstarBound_tensor`), the removed query (`removedBound_crude`), the star part and the
transports (`newDecomp_of_inputs`) are proved. -/
structure RecordInputs (κF : ℕ → ℝ) (C : ComparisonPartsTC hW hMR hFour A) : Prop where
  κ_nonneg : ∀ p, 19 ≤ p → 0 ≤ κF p
  form : ∀ b i, blockSite b = .inl i → SpecK hW κF (specF hW A b) (C.blk b)

/-- `RecordInputs` gives `CrudeNewInputs` at `nF = nT` (the nonstars proved). -/
theorem RecordInputs.toKN {κF : ℕ → ℝ} {C : ComparisonPartsTC hW hMR hFour A}
    (H : RecordInputs κF C) : CrudeNewInputs κF nT C where
  κ_nonneg := H.κ_nonneg
  n_nonneg := nT_nonneg
  kn b i hb := specKN_of_K (specF hW A b) (C.blk b) (H.form b i hb)

/-- **A constructor of PG's `SignedDecompInputsC` from (K) and the gates**: at
`e_sg′ = esgCrude κF nT`, with `c_col = 73`, `c_+ = 38`, the nonstars, the removed query, the star
part and the transports proved. -/
theorem RecordInputs.toSD {κF : ℕ → ℝ} {C : ComparisonPartsTC hW hMR hFour A}
    (H : RecordInputs κF C) (G : ∀ k, PieceGate (esgCrude κF nT) 38 k) :
    SignedDecompInputsC C :=
  H.toKN.toSD G

end Sarkozy.SignedDecompCrude

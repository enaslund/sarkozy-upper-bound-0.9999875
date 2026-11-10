module

public import Sarkozy.UpperRepair.All

/-!
# `Up`'s certificate inputs: the record tables and the block statements

`paper/sections/26_upper_comparison.tex`: `lem:record:domain`(ii) (the repaired and replaced
records at blocks), (F7) (`it:record:upper-F7`, the one-way repairs), `def:upper-comparison` (the
state ledgers `Λ^s`, `Λ^a`); `lem:tr:repair`(f).

UR's `UpperRepairDataS` (`Up` in the main statement) has two kinds of content:
* **finite** (the paper's band certificates): the per-band record coefficients `C^s_{k,ρ}`,
  `C^a_{k,ρ}` (the values of (F7)/(F9) at the band start) and their scaled state ledgers `hLed`;
* **analytic** (`lem:record:domain`(ii)): at every upper block, replacing laws whose constants are
  at most `C^ε_{k,ρ} r_𝔅`.

This file separates them and proves the monotone step of (F7):
* `UpperRecordTables` (finite) and `UpperRecordBlocks T` (analytic), **`UpperRepairDataS.ofSplit`**.
* `f7F`, `f7Rho`: the normalized (F7) quantities `F/r`-free form `F̄(r) = u r (1 + κ/(1 - n r))` and
  `ρ̄'(r) = (n(1 + 2F̄) + u² r)/(1 - u r)`, so that `ρ' ≤ ρ̄'(r) r`; **`f7F_mono`**,
  **`f7Rho_mono`**
  (nondecreasing in `r`, i.e. nonincreasing in the prime).
* **`oneWayData_F_le`, `oneWayData_ρ'_le`** (proved): block inputs `U ≤ u r`, `ρ_new ≤ n r`,
  `K_∞ ≤ κ` give `ρ' ≤ ρ̄'(r) r`.
* **`oneWay_coef_le`** (proved, `lem:record:domain`(ii) for (F7)): with also `ρ_old ≤ o r` and
  `r ≤ r₀`, a one-way record has `C^s ≤ (o + ρ̄'(r₀)) r` and `C^a ≤ ρ̄'(r₀) r`. So `hs`, `ha` of a
  one-way record follow from the block inputs (analytic) and the finite band-start check
  `o + ρ̄'(r₀) ≤ C^s_{k,ρ}`, `ρ̄'(r₀) ≤ C^a_{k,ρ}` with the gates `u r₀ < 1`, `n r₀ < 1`.
* `coef_sym_le_of`, `coef_skew_le_of`: `hs`, `ha` of a block from the per-record bounds.
-/

@[expose] public section

open Finset

namespace Sarkozy.UpperCapsPaper

open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.UpperComparison Sarkozy.UpperRepair
  Sarkozy.F7Repair
open Sarkozy.PartVLaws (blockPrimes UpperBlockInputs)
open Sarkozy.ComparisonLawPaper (upperNe)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs)
open Sarkozy.MainFinalF1 (specF Blk bOf bandIdx)

/-! ## The split of `Up` -/

/-- **The finite part of `Up`: the paper's per-record table** (`def:upper-comparison`,
`lem:record:domain`(ii)): per band the record coefficients `C^s_{k,ρ}`, `C^a_{k,ρ}` (the values of
(F7)/(F9) at the band start), with state sums at most `c ∈ [1, 5/4]` times the ledgers `Λ^s`,
`Λ^a` of `upper_dense_refined.json`. *Hypothesis* (finite, given the table). (RG: `5/4` since
7 November, 23:55 UTC: RB's check of CM's `hCv` at the formal totals fails at `c = 7/4` with the
proved class savings, break-even `c ≈ 1.52`; it was `7/4` at the rebase, `5/2` at `a_T`; the
intended value is `c = 1`.) -/
structure UpperRecordTables where
  c : ℝ
  hc : 1 ≤ c
  hc' : c ≤ 5 / 4
  Cs : Fin 310 → UpIdx → ℝ
  Ca : Fin 310 → UpIdx → ℝ
  hCs : ∀ k i, 0 ≤ Cs k i
  hCa : ∀ k i, 0 ≤ Ca k i
  hLed : ScaledLedgers c Cs Ca

/-- **The analytic part of `Up`** (`lem:record:domain`(ii); (F7), `prop:le-mixture`,
`prop:dense-comparison` at blocks): at every upper block, the replacing laws of the 92 changed
records, with constants at most the table's `C^ε_{k,ρ} r_𝔅`. *Hypothesis* (analytic). -/
structure UpperRecordBlocks (hW : Target.Weil) (A : PaperAnalyticInputs f1Cell)
    (T : UpperRecordTables) where
  rep : ∀ (b : Blk) (U : UpperBlockInputs bOf b), specF hW A b = .upper U →
    BlockRepl (blockPrimes bOf b) (upperNe hW U)
  hs : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).coef ρ .sym ≤ T.Cs (bandIdx b) ρ * U.r
  ha : ∀ b U (h : specF hW A b = .upper U) ρ, upperFate ρ = .changed →
    (rep b U h).coef ρ .skew ≤ T.Ca (bandIdx b) ρ * U.r

/-- **`Up` from the finite table and the block statements.** -/
noncomputable def UpperRepairDataS.ofSplit {hW : Target.Weil} {A : PaperAnalyticInputs f1Cell}
    (T : UpperRecordTables) (Bk : UpperRecordBlocks hW A T) : UpperRepairDataS hW A where
  c := T.c
  hc := T.hc
  hc' := T.hc'
  Cs := T.Cs
  Ca := T.Ca
  hCs := T.hCs
  hCa := T.hCa
  hLed := T.hLed
  rep := Bk.rep
  hs := Bk.hs
  ha := Bk.ha

/-! ## (F7): the monotone step -/

/-- `F̄(r) = u r (1 + κ/(1 - n r))`: the bound for `F = U(1 + K_∞/(1 - ρ_new))` from
`U ≤ u r`, `ρ_new ≤ n r`, `K_∞ ≤ κ`. -/
noncomputable def f7F (u n κ r : ℝ) : ℝ := u * r * (1 + κ / (1 - n * r))

/-- `ρ̄'(r) = (n(1 + 2F̄(r)) + u² r)/(1 - u r)`, so that `ρ' ≤ ρ̄'(r) r` (`lem:tr:repair`(f)). -/
noncomputable def f7Rho (u n κ r : ℝ) : ℝ := (n * (1 + 2 * f7F u n κ r) + u ^ 2 * r) / (1 - u * r)

theorem f7F_nonneg {u n κ r : ℝ} (hu : 0 ≤ u) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hn1 : n * r < 1) :
    0 ≤ f7F u n κ r := by
  unfold f7F
  have : 0 ≤ κ / (1 - n * r) := div_nonneg hκ (by linarith)
  positivity

/-- **`F̄` is nondecreasing in `r`** (nonincreasing in the prime). -/
theorem f7F_mono {u n κ r r₀ : ℝ} (hu : 0 ≤ u) (hn : 0 ≤ n) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hrr : r ≤ r₀) (hn₀ : n * r₀ < 1) : f7F u n κ r ≤ f7F u n κ r₀ := by
  unfold f7F
  have hnr : n * r ≤ n * r₀ := mul_le_mul_of_nonneg_left hrr hn
  have hd : 0 < 1 - n * r₀ := by linarith
  have hk : κ / (1 - n * r) ≤ κ / (1 - n * r₀) :=
    div_le_div_of_nonneg_left hκ hd (by linarith)
  have hk0 : 0 ≤ κ / (1 - n * r) := div_nonneg hκ (by linarith)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hrr hu) (by linarith) (by linarith)
    (mul_nonneg hu (hr.trans hrr))

/-- **`ρ̄'` is nondecreasing in `r`** (nonincreasing in the prime; `lem:record:domain`, Step 2). -/
theorem f7Rho_mono {u n κ r r₀ : ℝ} (hu : 0 ≤ u) (hn : 0 ≤ n) (hκ : 0 ≤ κ) (hr : 0 ≤ r)
    (hrr : r ≤ r₀) (hn₀ : n * r₀ < 1) (hu₀ : u * r₀ < 1) : f7Rho u n κ r ≤ f7Rho u n κ r₀ := by
  unfold f7Rho
  have hF := f7F_mono hu hn hκ hr hrr hn₀
  have hF0 := f7F_nonneg hu hκ hr (lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr hn) hn₀)
  have hur : u * r ≤ u * r₀ := mul_le_mul_of_nonneg_left hrr hu
  have hd : 0 < 1 - u * r₀ := by linarith
  have hnum : n * (1 + 2 * f7F u n κ r) + u ^ 2 * r ≤ n * (1 + 2 * f7F u n κ r₀) + u ^ 2 * r₀ :=
    add_le_add (mul_le_mul_of_nonneg_left (by linarith) hn)
      (mul_le_mul_of_nonneg_left hrr (sq_nonneg u))
  have hnum0 : 0 ≤ n * (1 + 2 * f7F u n κ r) + u ^ 2 * r := by positivity
  exact div_le_div₀ (hnum0.trans hnum) hnum hd (by linarith)

section OneWay

variable {X Y : Type*} [Fintype X] [Fintype Y] {ν : FiniteLaw (X × Y)} {μX : FiniteLaw X}
  {μY : FiniteLaw Y} (D : OneWayData ν μX μY)

/-- `F ≤ F̄(r)` from the block inputs. -/
theorem oneWayData_F_le {u n κ r : ℝ} (hU : D.U ≤ u * r) (hρ : D.ρ ≤ n * r) (hK : D.K ≤ κ)
    (hn1 : n * r < 1) : D.F ≤ f7F u n κ r := by
  unfold OneWayData.F f7F
  have h1 : 0 < 1 - D.ρ := D.one_sub_ρ_pos
  have h2 : 0 < 1 - n * r := by linarith
  have hk : D.K / (1 - D.ρ) ≤ κ / (1 - n * r) :=
    div_le_div₀ (D.K_nonneg.trans hK) hK h2 (by linarith)
  have hk0 : 0 ≤ D.K / (1 - D.ρ) := div_nonneg D.K_nonneg h1.le
  exact mul_le_mul hU (by linarith) (by linarith) (D.U_nonneg.trans hU)

/-- **(F7) at a block, with the block inputs**: `U ≤ u r`, `ρ_new ≤ n r`, `K_∞ ≤ κ` give
`ρ' ≤ ρ̄'(r) r`. -/
theorem oneWayData_ρ'_le {u n κ r : ℝ} (hn : 0 ≤ n) (hr : 0 ≤ r)
    (hU : D.U ≤ u * r) (hρ : D.ρ ≤ n * r) (hK : D.K ≤ κ) (hn1 : n * r < 1) (hu1 : u * r < 1) :
    D.ρ' ≤ f7Rho u n κ r * r := by
  have hF := oneWayData_F_le D hU hρ hK hn1
  have hF0 := D.F_nonneg
  have hd : 0 < 1 - u * r := by linarith
  have hnum : D.ρ * (1 + 2 * D.F) + D.U ^ 2 ≤ n * r * (1 + 2 * f7F u n κ r) + (u * r) ^ 2 :=
    add_le_add (mul_le_mul hρ (by linarith) (by linarith) (by positivity))
      (pow_le_pow_left₀ D.U_nonneg hU 2)
  have hnum0 : 0 ≤ D.ρ * (1 + 2 * D.F) + D.U ^ 2 := by
    have := D.ρ_nonneg
    positivity
  have h := div_le_div₀ (hnum0.trans hnum) hnum hd (by linarith : 1 - u * r ≤ 1 - D.U)
  have he : (n * r * (1 + 2 * f7F u n κ r) + (u * r) ^ 2) / (1 - u * r) =
      f7Rho u n κ r * r := by
    unfold f7Rho
    rw [div_mul_eq_mul_div]
    congr 1
    ring
  unfold OneWayData.ρ'
  linarith

end OneWay

/-- **`lem:record:domain`(ii) for a one-way record** ((F7) at a block): with the block inputs
`U ≤ u r`, `ρ_new ≤ n r`, `K_∞ ≤ κ`, `ρ_old ≤ o r` at `r = r_𝔅 ≤ r₀` and the band-start gates
`n r₀ < 1`, `u r₀ < 1`, the record's constants are `C^s ≤ (o + ρ̄'(r₀)) r` and `C^a ≤ ρ̄'(r₀) r`;
so the band-start values `o + ρ̄'(r₀) ≤ c_s`, `ρ̄'(r₀) ≤ c_a` give `C^s ≤ c_s r`, `C^a ≤ c_a r`. -/
theorem oneWay_coef_le {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : UpperNonempty pr} {t : PType × PType}
    {φ : t.1.Pat × t.2.Pat} (I : OneWayGraphInput pr hne t φ) {u n κ o r r₀ cs ca : ℝ}
    (hu : 0 ≤ u) (hn : 0 ≤ n) (hκ : 0 ≤ κ) (hr : 0 ≤ r) (hrr : r ≤ r₀)
    (hU : I.R.D.U ≤ u * r) (hρ : I.R.D.ρ ≤ n * r) (hK : I.R.D.K ≤ κ) (ho : I.R.ρold ≤ o * r)
    (hn₀ : n * r₀ < 1) (hu₀ : u * r₀ < 1) (hcs : o + f7Rho u n κ r₀ ≤ cs)
    (hca : f7Rho u n κ r₀ ≤ ca) :
    I.toRepl.Cs ≤ cs * r ∧ I.toRepl.Ca ≤ ca * r := by
  have hn1 : n * r < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr hn) hn₀
  have hu1 : u * r < 1 := lt_of_le_of_lt (mul_le_mul_of_nonneg_left hrr hu) hu₀
  have h1 := oneWayData_ρ'_le I.R.D hn hr hU hρ hK hn1 hu1
  have h2 := mul_le_mul_of_nonneg_right (f7Rho_mono hu hn hκ hr hrr hn₀ hu₀) hr
  have hs : I.toRepl.Cs = I.R.ρold + I.R.D.ρ' := rfl
  have ha : I.toRepl.Ca = I.R.D.ρ' := rfl
  rw [hs, ha]
  constructor
  · have := mul_le_mul_of_nonneg_right hcs hr
    nlinarith
  · have := mul_le_mul_of_nonneg_right hca hr
    linarith

/-! ## `hs`, `ha` of a block from its records -/

/-- `hs` of a block from the per-record bounds `C^s ≤ C^s_ρ r`. -/
theorem coef_sym_le_of {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : UpperNonempty pr} (R : BlockRepl pr hne) (Cs : UpIdx → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hCs : ∀ ρ, 0 ≤ Cs ρ)
    (h : ∀ t φ (hc : upperFate (true, ⟨t, φ⟩) = .changed), (R t φ hc).Cs ≤ Cs (true, ⟨t, φ⟩) * r)
    (ρ : UpIdx) : R.coef ρ .sym ≤ Cs ρ * r := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact mul_nonneg (hCs _) hr
  · show (if hc : upperFate (true, ⟨t, φ⟩) = .changed then (R t φ hc).C .sym else 0) ≤ _
    split_ifs with hc
    · exact h t φ hc
    · exact mul_nonneg (hCs _) hr

/-- `ha` of a block from the per-record bounds `C^a ≤ C^a_ρ r`. -/
theorem coef_skew_le_of {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ}
    [∀ i, Fact (pr i).Prime] {hne : UpperNonempty pr} (R : BlockRepl pr hne) (Ca : UpIdx → ℝ)
    {r : ℝ} (hr : 0 ≤ r) (hCa : ∀ ρ, 0 ≤ Ca ρ)
    (h : ∀ t φ (hc : upperFate (true, ⟨t, φ⟩) = .changed), (R t φ hc).Ca ≤ Ca (true, ⟨t, φ⟩) * r)
    (ρ : UpIdx) : R.coef ρ .skew ≤ Ca ρ * r := by
  rcases ρ with ⟨b, t, φ⟩
  cases b
  · exact mul_nonneg (hCa _) hr
  · show (if hc : upperFate (true, ⟨t, φ⟩) = .changed then (R t φ hc).C .skew else 0) ≤ _
    split_ifs with hc
    · exact h t φ hc
    · exact mul_nonneg (hCa _) hr

end Sarkozy.UpperCapsPaper

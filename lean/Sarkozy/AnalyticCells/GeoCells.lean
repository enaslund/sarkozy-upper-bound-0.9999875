module

public import Sarkozy.AnalyticCells.CellData

@[expose] public section

/-!
# Soundness of the rational cell majorants

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(i), `eq:record:cell-charge`.

For a piece with the geometric cells `x_j = cellPoint x Y 𝗇 j` of `[x, Y)`,
`n_j = ⌊570/log x_{j+1}⌋`
(`def:record:exact-blocks`(d)), rational enclosures of `log x` and `log Y` (a `GeoQ`) satisfying the
kernel conditions `GeoQ.Checks`, and `𝖾 = 2411/(5·10⁶ log x_0)` (`thm:bmor`), the right side of
`eq:record:cell-charge` (M2's `Misc.cellBound`) at `a = a_T` is at most `GeoQ.bound2` for `s = 1`
(**`cellBound_le_bound2`**) and `GeoQ.bound3` for `s = 3/2` (**`cellBound_le_bound3`**).

The analytic inputs are elementary: `log x_j = log x + (j/𝗇)(log Y - log x)`,
`I_j(1) = log(L_{j+1}/L_j)` (M2's `cellIntegral_one`),
`I_j(3/2) ≤ 2(x_j^{-1/2} - x_{j+1}^{-1/2})/log x_j` (`1/log t ≤ 1/log x_j`
on the cell, `cellIntegral_three_halves_le`), `e^y ≥ 1 + y`, and the rational bounds of
`ExpBounds.lean`.
-/

open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV

/-! ## The integral at `s = 3/2` -/

theorem cellIntegral_three_halves_le {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    cellIntegral (3 / 2) a b ≤ 2 * (a ^ (-(1 / 2 : ℝ)) - b ^ (-(1 / 2 : ℝ))) / Real.log a := by
  have ha0 : 0 < a := by linarith
  have hla : 0 < Real.log a := Real.log_pos ha
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(3 / 2 : ℝ)) / Real.log a) (Set.Icc a b) := by
    apply ContinuousOn.div_const
    apply ContinuousOn.rpow_const continuousOn_id
    intro t ht
    left
    have : a ≤ t := ht.1
    simp only [id]
    linarith
  have h1 : cellIntegral (3 / 2) a b ≤ ∫ t in a..b, t ^ (-(3 / 2 : ℝ)) / Real.log a := by
    unfold cellIntegral
    apply intervalIntegral.integral_mono_on hab
      ((continuousOn_fs (3 / 2) ha).intervalIntegrable_of_Icc hab)
      (hcont.intervalIntegrable_of_Icc hab)
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    unfold fs
    apply div_le_div_of_nonneg_left (Real.rpow_nonneg (by linarith) _) hla
    exact Real.log_le_log ha0 ht.1
  have h2 : ∫ t in a..b, t ^ (-(3 / 2 : ℝ)) / Real.log a =
      2 * (a ^ (-(1 / 2 : ℝ)) - b ^ (-(1 / 2 : ℝ))) / Real.log a := by
    rw [intervalIntegral.integral_div]
    have h0 : (0 : ℝ) ∉ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]
      intro h
      linarith [h.1]
    rw [integral_rpow (Or.inr ⟨by norm_num, h0⟩)]
    have he : (-(3 / 2 : ℝ)) + 1 = -(1 / 2) := by norm_num
    rw [he]
    congr 1
    ring
  linarith

/-! ## The logarithms of the cell points -/

theorem log_cellPoint {x Y : ℝ} (hx : 0 < x) (hY : 0 < Y) (n j : ℕ) :
    Real.log (cellPoint x Y n j) = Real.log x + (j : ℝ) / n * (Real.log Y - Real.log x) := by
  unfold cellPoint
  rw [Real.log_mul (Real.rpow_pos_of_pos hx _).ne' (Real.rpow_pos_of_pos hY _).ne',
    Real.log_rpow hx, Real.log_rpow hY]
  ring

namespace GeoQ

variable (G : GeoQ)

/-- The kernel conditions, unpacked. -/
theorem checks_spec (h : G.Checks = true) :
    0 < G.n ∧ 1 < G.lxl ∧ G.lxl ≤ G.lxh ∧ G.lYl ≤ G.lYh ∧ G.lxh ≤ G.lYl ∧ 0 ≤ G.dhi ∧
      G.dhi ≤ 2 ∧ ∀ j < G.n,
        1 ≤ G.m j ∧ (G.m j : ℚ) * G.Lhi (j + 1) ≤ 570 ∧ 570 < ((G.m j : ℚ) + 1) * G.Llo (j + 1) ∧
        (G.m (j + 1) ≤ G.m j ∨ j + 1 = G.n) ∧ |G.phi 0 j| ≤ 64 ∧ |G.phi (1 / 2) j| ≤ 64 ∧
        |G.phi 1 j| ≤ 64 ∧ |G.phi (3 / 2) j| ≤ 64 ∧ G.dhi / G.Llo j < 1 ∧
        |G.stepR 0 (G.m j)| ≤ 1 ∧ |G.stepR (1 / 2) (G.m j)| ≤ 1 ∧ |G.stepR 1 (G.m j)| ≤ 1 ∧
        |G.stepR (3 / 2) (G.m j)| ≤ 1 := by
  unfold Checks at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, h6, h7, fun j hj => ?_⟩
  have := h8 j hj
  tauto

end GeoQ

/-! ## The geometric cells -/

section Geo

variable {x Y : ℝ}

/-- The hypotheses on the piece: `1 < x ≤ Y` and the enclosures of `log x`, `log Y`. -/
structure Encl (G : GeoQ) (x Y : ℝ) : Prop where
  one_lt : 1 < x
  le : x ≤ Y
  lx_lo : (G.lxl : ℝ) ≤ Real.log x
  lx_hi : Real.log x ≤ G.lxh
  lY_lo : (G.lYl : ℝ) ≤ Real.log Y
  lY_hi : Real.log Y ≤ G.lYh
  checks : G.Checks = true

variable {G : GeoQ} (H : Encl G x Y)
include H

theorem Encl.x_pos : 0 < x := by linarith [H.one_lt]

theorem Encl.Y_pos : 0 < Y := by linarith [H.one_lt, H.le]

theorem Encl.n_pos : 0 < G.n := (G.checks_spec H.checks).1

theorem Encl.logL (j : ℕ) : Real.log (cellPoint x Y G.n j) =
    Real.log x + (j : ℝ) / G.n * (Real.log Y - Real.log x) :=
  log_cellPoint H.x_pos H.Y_pos G.n j

theorem Encl.t_mem {j : ℕ} (hj : j ≤ G.n) : 0 ≤ (j : ℝ) / G.n ∧ (j : ℝ) / G.n ≤ 1 := by
  have hn : (0 : ℝ) < G.n := by exact_mod_cast H.n_pos
  refine ⟨by positivity, ?_⟩
  rw [div_le_one hn]
  exact_mod_cast hj

theorem Encl.Llo_le {j : ℕ} (hj : j ≤ G.n) : (G.Llo j : ℝ) ≤ Real.log (cellPoint x Y G.n j) := by
  rw [H.logL]
  have hL : (G.Llo j : ℝ) = G.lxl + (j : ℝ) / G.n * (G.lYl - G.lxl) := by
    unfold GeoQ.Llo
    push_cast
    ring
  rw [hL]
  obtain ⟨t0, t1⟩ := H.t_mem hj
  have h1 := H.lx_lo
  have h2 := H.lY_lo
  nlinarith [mul_nonneg t0 (sub_nonneg.mpr h2), mul_nonneg (sub_nonneg.mpr t1) (sub_nonneg.mpr h1)]

theorem Encl.le_Lhi {j : ℕ} (hj : j ≤ G.n) : Real.log (cellPoint x Y G.n j) ≤ (G.Lhi j : ℝ) := by
  rw [H.logL]
  have hL : (G.Lhi j : ℝ) = G.lxh + (j : ℝ) / G.n * (G.lYh - G.lxh) := by
    unfold GeoQ.Lhi
    push_cast
    ring
  rw [hL]
  obtain ⟨t0, t1⟩ := H.t_mem hj
  have h1 := H.lx_hi
  have h2 := H.lY_hi
  nlinarith [mul_nonneg t0 (sub_nonneg.mpr h2), mul_nonneg (sub_nonneg.mpr t1) (sub_nonneg.mpr h1)]

theorem Encl.one_lt_Llo {j : ℕ} (hj : j ≤ G.n) : (1 : ℝ) < G.Llo j := by
  obtain ⟨hn, h1, h2, h3, h4, -⟩ := G.checks_spec H.checks
  have hL : (G.Llo j : ℝ) = G.lxl + (j : ℝ) / G.n * (G.lYl - G.lxl) := by
    unfold GeoQ.Llo
    push_cast
    ring
  rw [hL]
  obtain ⟨t0, -⟩ := H.t_mem hj
  have h1' : (1 : ℝ) < G.lxl := by exact_mod_cast h1
  have h5 : (0 : ℝ) ≤ G.lYl - G.lxl := by
    have : G.lxl ≤ G.lYl := h2.trans h4
    have : (G.lxl : ℝ) ≤ G.lYl := by exact_mod_cast this
    linarith
  nlinarith [mul_nonneg t0 h5]

theorem Encl.one_lt_L {j : ℕ} (hj : j ≤ G.n) : 1 < Real.log (cellPoint x Y G.n j) :=
  lt_of_lt_of_le (H.one_lt_Llo hj) (H.Llo_le hj)

theorem Encl.X_pos (j : ℕ) : 0 < cellPoint x Y G.n j := by
  unfold cellPoint
  exact mul_pos (Real.rpow_pos_of_pos H.x_pos _) (Real.rpow_pos_of_pos H.Y_pos _)

theorem Encl.one_lt_X {j : ℕ} (hj : j ≤ G.n) : 1 < cellPoint x Y G.n j := by
  have h := H.one_lt_L hj
  have hp := H.X_pos j
  by_contra hc
  push Not at hc
  have : Real.log (cellPoint x Y G.n j) ≤ 0 := Real.log_nonpos hp.le hc
  linarith

/-- `Δ = L_{j+1} - L_j`. -/
theorem Encl.L_succ (j : ℕ) : Real.log (cellPoint x Y G.n (j + 1)) =
    Real.log (cellPoint x Y G.n j) + (Real.log Y - Real.log x) / G.n := by
  rw [H.logL, H.logL]
  push_cast
  ring

theorem Encl.delta_nonneg : 0 ≤ (Real.log Y - Real.log x) / G.n := by
  apply div_nonneg _ (Nat.cast_nonneg _)
  have := Real.log_le_log H.x_pos H.le
  linarith

theorem Encl.delta_le : (Real.log Y - Real.log x) / G.n ≤ (G.dhi : ℝ) := by
  have hn : (0 : ℝ) < G.n := by exact_mod_cast H.n_pos
  have hd : (G.dhi : ℝ) = (G.lYh - G.lxl) / G.n := by unfold GeoQ.dhi; push_cast; rfl
  rw [hd]
  apply div_le_div_of_nonneg_right _ hn.le
  linarith [H.lY_hi, H.lx_lo]

theorem Encl.dhi_nonneg : (0 : ℝ) ≤ G.dhi := le_trans H.delta_nonneg H.delta_le

/-- **`n_j = m j`** on every cell. -/
theorem Encl.card_eq {j : ℕ} (hj : j < G.n) : cellCard 570 x Y G.n j = G.m j := by
  obtain ⟨-, -, -, -, -, -, -, hc⟩ := G.checks_spec H.checks
  obtain ⟨hm1, hmhi, hmlo, -⟩ := hc j hj
  unfold cellCard
  have hL := H.one_lt_L (j := j + 1) (by omega)
  have hlo := H.Llo_le (j := j + 1) (by omega)
  have hhi := H.le_Lhi (j := j + 1) (by omega)
  set L := Real.log (cellPoint x Y G.n (j + 1))
  have hL0 : 0 < L := by linarith
  rw [Nat.floor_eq_iff (by positivity)]
  have hmhi' : (G.m j : ℝ) * G.Lhi (j + 1) ≤ 570 := by exact_mod_cast hmhi
  have hmlo' : (570 : ℝ) < ((G.m j : ℝ) + 1) * G.Llo (j + 1) := by exact_mod_cast hmlo
  have hm0 : (0 : ℝ) ≤ G.m j := Nat.cast_nonneg _
  constructor
  · rw [le_div_iff₀ hL0]
    nlinarith
  · rw [div_lt_iff₀ hL0]
    nlinarith

omit H in
theorem aQ_eq : (aQ : ℝ) = Sarkozy.TargetLedger.targetDecay := by
  unfold aQ Sarkozy.TargetLedger.targetDecay
  push_cast
  ring

/-- The real exponent `2a n_j L_{j+1} - σ L_j` is at most `phi σ j`. -/
theorem Encl.exponent_le {σ : ℚ} (hσ : 0 ≤ σ) {j : ℕ} (hj : j < G.n) :
    2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) -
        (σ : ℝ) * Real.log (cellPoint x Y G.n j) ≤ (G.phi σ j : ℝ) := by
  have hhi := H.le_Lhi (j := j + 1) (by omega)
  have hlo := H.Llo_le (j := j) hj.le
  have hphi : (G.phi σ j : ℝ) = 2 * (aQ : ℝ) * (G.m j : ℝ) * G.Lhi (j + 1) - σ * G.Llo j := by
    unfold GeoQ.phi
    push_cast
    ring
  rw [hphi]
  have ha : (0 : ℝ) ≤ 2 * (aQ : ℝ) * (G.m j : ℝ) := by
    have : (0 : ℝ) ≤ aQ := by unfold aQ; norm_num
    positivity
  have hσ' : (0 : ℝ) ≤ σ := by exact_mod_cast hσ
  nlinarith [mul_le_mul_of_nonneg_left hhi ha, mul_le_mul_of_nonneg_left hlo hσ']

theorem Encl.exp_le_W {σ : ℚ} (hσ : 0 ≤ σ) {j : ℕ} (hj : j < G.n) {w : ℚ}
    (hw : Real.exp (G.phi σ j) ≤ w) :
    Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) -
        (σ : ℝ) * Real.log (cellPoint x Y G.n j)) ≤ w :=
  (Real.exp_le_exp.mpr (H.exponent_le hσ hj)).trans hw

/-! ## One cell -/

theorem Encl.cellPi_eq {j : ℕ} (hj : j < G.n) :
    cellPi (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j =
      Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1))) := by
  unfold cellPi
  rw [H.card_eq hj]

theorem Encl.m_pos {j : ℕ} (hj : j < G.n) : (0 : ℝ) < G.m j := by
  have := ((G.checks_spec H.checks).2.2.2.2.2.2.2 j hj).1
  exact_mod_cast this

theorem Encl.cellG_eq {j : ℕ} (hj : j < G.n) :
    cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j =
      Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1))) / G.m j := by
  unfold cellG
  rw [H.cellPi_eq hj, H.card_eq hj]

/-- The restart `Π_j x_j^{-s}`. -/
theorem Encl.termA_le {s : ℚ} (hs : 0 ≤ s) {j : ℕ} (hj : j < G.n) {w : ℚ}
    (hw : Real.exp (G.phi s j) ≤ w) :
    cellPi (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
      cellPoint x Y G.n j ^ (-(s : ℝ)) ≤ w := by
  rw [H.cellPi_eq hj, Real.rpow_def_of_pos (H.X_pos j), ← Real.exp_add]
  have h := H.exp_le_W hs hj hw
  have he : 2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) +
      Real.log (cellPoint x Y G.n j) * (-(s : ℝ)) =
      2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) -
        (s : ℝ) * Real.log (cellPoint x Y G.n j) := by ring
  rw [he]
  exact h

/-- `g_j x_j^{1-s} ≤ w/n_j` from `w ≥ exp(φ_j(s-1))`. -/
theorem Encl.gX_le {σ : ℚ} (hσ : 0 ≤ σ) {j : ℕ} (hj : j < G.n) {w : ℚ}
    (hw : Real.exp (G.phi σ j) ≤ w) :
    cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
      cellPoint x Y G.n j ^ (1 - ((σ : ℝ) + 1)) ≤ (w : ℝ) / G.m j := by
  rw [H.cellG_eq hj, Real.rpow_def_of_pos (H.X_pos j), div_mul_eq_mul_div, ← Real.exp_add]
  apply div_le_div_of_nonneg_right _ (H.m_pos hj).le
  have h := H.exp_le_W hσ hj hw
  have he : 2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) +
      Real.log (cellPoint x Y G.n j) * (1 - ((σ : ℝ) + 1)) =
      2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) -
        (σ : ℝ) * Real.log (cellPoint x Y G.n j) := by ring
  rw [he]
  exact h

omit H in
theorem cellG_nonneg_geo (j : ℕ) :
    0 ≤ cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j := by
  unfold cellG cellPi
  positivity

/-- The main term at `s = 1`: `g_j I_j(1) ≤ (w/n_j) logUp(dhi/Llo_j)`. -/
theorem Encl.termB1_le {j : ℕ} (hj : j < G.n) {w : ℚ} (hw : Real.exp (G.phi 0 j) ≤ w) :
    0 ≤ cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral 1 (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ∧
      cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral 1 (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ≤
      (w : ℝ) / G.m j * (logUp (G.dhi / G.Llo j) : ℝ) := by
  have hX := H.one_lt_X hj.le
  have hmono := cellPoint_mono H.x_pos H.le G.n j
  rw [cellIntegral_one hX hmono]
  have hL := H.one_lt_L hj.le
  have hLlo := H.Llo_le hj.le
  have hlo1 := H.one_lt_Llo hj.le
  have hΔ0 := H.delta_nonneg
  have hΔle := H.delta_le
  have hd0 := H.dhi_nonneg
  have hratio : Real.log (cellPoint x Y G.n (j + 1)) / Real.log (cellPoint x Y G.n j) =
      1 + (Real.log Y - Real.log x) / G.n / Real.log (cellPoint x Y G.n j) := by
    rw [H.L_succ]
    field_simp
  have hu : (Real.log Y - Real.log x) / G.n / Real.log (cellPoint x Y G.n j) ≤
      (G.dhi : ℝ) / G.Llo j := div_le_div₀ hd0 hΔle (by linarith) hLlo
  have hu0 : 0 ≤ (Real.log Y - Real.log x) / G.n / Real.log (cellPoint x Y G.n j) :=
    div_nonneg hΔ0 (by linarith)
  have hq0 : 0 ≤ G.dhi / G.Llo j := by
    have : (0 : ℚ) < G.Llo j := by exact_mod_cast (show (0 : ℝ) < G.Llo j by linarith)
    have : (0 : ℚ) ≤ G.dhi := by exact_mod_cast hd0
    positivity
  have hq1 := ((G.checks_spec H.checks).2.2.2.2.2.2.2 j hj).2.2.2.2.2.2.2.2.1
  have hlog : Real.log (Real.log (cellPoint x Y G.n (j + 1)) / Real.log (cellPoint x Y G.n j)) ≤
      (logUp (G.dhi / G.Llo j) : ℝ) := by
    rw [hratio]
    have h1 := log_one_add_le_logUp hq0 hq1
    push_cast at h1
    exact (Real.log_le_log (by linarith) (by linarith)).trans h1
  have hlog0 : 0 ≤ Real.log (Real.log (cellPoint x Y G.n (j + 1)) /
      Real.log (cellPoint x Y G.n j)) := by
    rw [hratio]
    exact Real.log_nonneg (by linarith)
  have hg := cellG_nonneg_geo (x := x) (Y := Y) (G := G) j
  refine ⟨mul_nonneg hg hlog0, ?_⟩
  have hgw : cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j ≤ (w : ℝ) / G.m j := by
    rw [H.cellG_eq hj]
    apply div_le_div_of_nonneg_right _ (H.m_pos hj).le
    have h := H.exp_le_W (le_refl 0) hj hw
    simpa using h
  exact mul_le_mul hgw hlog hlog0 (hg.trans hgw)

/-- The main term at `s = 3/2`: `g_j I_j(3/2) ≤ w · 2κ(dhi/2)/(n_j Llo_j)`. -/
theorem Encl.termB3_le {j : ℕ} (hj : j < G.n) {w : ℚ} (hw : Real.exp (G.phi (1 / 2) j) ≤ w) :
    0 ≤ cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ∧
      cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ≤
      (w : ℝ) * (2 * (kappa (G.dhi / 2) : ℝ)) / ((G.m j : ℝ) * G.Llo j) := by
  have hX := H.one_lt_X hj.le
  have hmono := cellPoint_mono H.x_pos H.le G.n j
  have hL := H.one_lt_L hj.le
  have hLlo := H.Llo_le hj.le
  have hlo1 := H.one_lt_Llo hj.le
  have hΔ0 := H.delta_nonneg
  have hΔle := H.delta_le
  have hd0 := H.dhi_nonneg
  have hd2 := (G.checks_spec H.checks).2.2.2.2.2.2.1
  have hm := H.m_pos hj
  have hg := cellG_nonneg_geo (x := x) (Y := Y) (G := G) j
  have hI0 : 0 ≤ cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) := by
    unfold cellIntegral
    apply intervalIntegral.integral_nonneg hmono
    intro t ht
    exact (fs_pos (lt_of_lt_of_le hX ht.1)).le
  refine ⟨mul_nonneg hg hI0, ?_⟩
  have hI := cellIntegral_three_halves_le hX hmono
  -- `x_j^{-1/2} - x_{j+1}^{-1/2} = x_j^{-1/2} (1 - e^{-Δ/2})`
  set L := Real.log (cellPoint x Y G.n j) with hLdef
  set Δ := (Real.log Y - Real.log x) / G.n with hΔdef
  have hp1 : cellPoint x Y G.n j ^ (-(1 / 2 : ℝ)) = Real.exp (-(1 / 2) * L) := by
    rw [Real.rpow_def_of_pos (H.X_pos j)]
    congr 1
    ring
  have hp2 : cellPoint x Y G.n (j + 1) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-(1 / 2) * L) * Real.exp (-(Δ / 2)) := by
    rw [Real.rpow_def_of_pos (H.X_pos (j + 1)), H.L_succ, ← Real.exp_add]
    congr 1
    ring
  have hy0 : (0 : ℚ) ≤ G.dhi / 2 := by
    have : (0 : ℚ) ≤ G.dhi := by exact_mod_cast hd0
    positivity
  have hy1 : G.dhi / 2 ≤ 1 := by linarith
  have hk := one_sub_exp_neg_le_kappa hy0 hy1
  push_cast at hk
  have hk' : 1 - Real.exp (-(Δ / 2)) ≤ (kappa (G.dhi / 2) : ℝ) := by
    have : Real.exp (-((G.dhi : ℝ) / 2)) ≤ Real.exp (-(Δ / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hk0 : 0 ≤ 1 - Real.exp (-(Δ / 2)) := by
    have : Real.exp (-(Δ / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hI' : cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ≤
      2 * Real.exp (-(1 / 2) * L) * (kappa (G.dhi / 2) : ℝ) / L := by
    refine hI.trans ?_
    rw [hp1, hp2]
    apply div_le_div_of_nonneg_right _ (by linarith)
    have he0 := Real.exp_pos (-(1 / 2) * L)
    nlinarith [mul_le_mul_of_nonneg_left hk' he0.le]
  have hgE := H.cellG_eq hj
  have hW := H.exp_le_W (σ := 1 / 2) (by norm_num) hj hw
  set E := Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)))
  have hEE : E * Real.exp (-(1 / 2) * L) =
      Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)) -
        ((1 / 2 : ℚ) : ℝ) * L) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hκ0 : (0 : ℝ) ≤ (kappa (G.dhi / 2) : ℝ) := le_trans hk0 hk'
  calc cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1))
      ≤ E / G.m j * (2 * Real.exp (-(1 / 2) * L) * (kappa (G.dhi / 2) : ℝ) / L) := by
        rw [hgE]
        exact mul_le_mul_of_nonneg_left hI' (by positivity)
    _ = (E * Real.exp (-(1 / 2) * L)) * (2 * (kappa (G.dhi / 2) : ℝ)) / ((G.m j : ℝ) * L) := by
        field_simp
    _ ≤ (w : ℝ) * (2 * (kappa (G.dhi / 2) : ℝ)) / ((G.m j : ℝ) * L) := by
        rw [hEE]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hW (by positivity)
    _ ≤ (w : ℝ) * (2 * (kappa (G.dhi / 2) : ℝ)) / ((G.m j : ℝ) * G.Llo j) := by
        have hw0 : (0 : ℝ) ≤ w := le_trans (Real.exp_pos _).le hw
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_left hLlo hm.le

/-! ## The jumps -/

/-- `ρ_{k+1} g_{k+1} ≤ g_k`, from `e^y ≥ 1 + y`. -/
theorem Encl.rho_le {k : ℕ} (hk : k + 1 < G.n) :
    (G.rho (k + 1) : ℝ) * cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (k + 1) ≤
      cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) k := by
  have hc := (G.checks_spec H.checks).2.2.2.2.2.2.2
  have hmk : G.m (k + 1) ≤ G.m k := by
    rcases (hc k (by omega)).2.2.2.1 with h | h
    · exact h
    · omega
  have hm0 := H.m_pos (j := k) (by omega)
  have hm1 := H.m_pos (j := k + 1) hk
  rw [H.cellG_eq hk, H.cellG_eq (j := k) (by omega)]
  have hLlo := H.Llo_le (j := k + 1) (by omega)
  have hΔle := H.delta_le
  have hsucc := H.L_succ (k + 1)
  set L := Real.log (cellPoint x Y G.n (k + 1))
  set L2 := Real.log (cellPoint x Y G.n (k + 1 + 1))
  set Δ := (Real.log Y - Real.log x) / G.n
  have ha : (0 : ℝ) ≤ aQ := by unfold aQ; norm_num
  have hmk' : (G.m (k + 1) : ℝ) ≤ G.m k := by exact_mod_cast hmk
  set y := 2 * (aQ : ℝ) * (((G.m k : ℝ) - G.m (k + 1)) * L - G.m (k + 1) * Δ)
  set ylo := 2 * (aQ : ℝ) * (((G.m k : ℝ) - G.m (k + 1)) * G.Llo (k + 1) - G.m (k + 1) * G.dhi)
  have hy : ylo ≤ y := by
    have h1 : ((G.m k : ℝ) - G.m (k + 1)) * G.Llo (k + 1) ≤ ((G.m k : ℝ) - G.m (k + 1)) * L :=
      mul_le_mul_of_nonneg_left hLlo (by linarith)
    have h2 : (G.m (k + 1) : ℝ) * Δ ≤ G.m (k + 1) * G.dhi :=
      mul_le_mul_of_nonneg_left hΔle hm1.le
    have h3 : 0 ≤ 2 * (aQ : ℝ) := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) h3
  have hrho : (G.rho (k + 1) : ℝ) = (1 + ylo) * G.m (k + 1) / G.m k := by
    unfold GeoQ.rho
    simp only [Nat.add_sub_cancel]
    push_cast
    ring
  have hexp : 2 * (aQ : ℝ) * (G.m k : ℝ) * L = 2 * (aQ : ℝ) * (G.m (k + 1) : ℝ) * L2 + y := by
    rw [hsucc]
    ring
  rw [hrho, hexp, Real.exp_add]
  have hey : 1 + ylo ≤ Real.exp y := by linarith [Real.add_one_le_exp y]
  set E := Real.exp (2 * (aQ : ℝ) * (G.m (k + 1) : ℝ) * L2)
  have hE := Real.exp_pos (2 * (aQ : ℝ) * (G.m (k + 1) : ℝ) * L2)
  have : (1 + ylo) * (G.m (k + 1) : ℝ) / G.m k * (E / G.m (k + 1)) = (1 + ylo) * E / G.m k := by
    field_simp
  rw [this]
  apply div_le_div_of_nonneg_right _ hm0.le
  nlinarith

/-- The first edge term. -/
theorem Encl.edge0_le {σ : ℚ} (hσ : 0 ≤ σ) {w : ℚ} (hw : Real.exp (G.phi σ 0) ≤ w) :
    2 * cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) 0 *
        (cellPoint x Y G.n 0 ^ (1 - ((σ : ℝ) + 1)) / Real.log (cellPoint x Y G.n 0)) ≤
      (2 * (w : ℝ) / G.m 0 * (G.edgeF 0 : ℝ) / G.Llo 0) := by
  have hn := H.n_pos
  have h := H.gX_le hσ hn hw
  have hlo := H.Llo_le (j := 0) (by omega)
  have hlo1 := H.one_lt_Llo (j := 0) (by omega)
  have hm := H.m_pos hn
  have hw0 : (0 : ℝ) ≤ w := le_trans (Real.exp_pos _).le hw
  have hgx0 : 0 ≤ cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) 0 *
      cellPoint x Y G.n 0 ^ (1 - ((σ : ℝ) + 1)) :=
    mul_nonneg (cellG_nonneg_geo (x := x) (Y := Y) (G := G) 0) (Real.rpow_nonneg (H.X_pos 0).le _)
  have he : (G.edgeF 0 : ℝ) = 1 := by unfold GeoQ.edgeF; simp
  rw [he, mul_one]
  calc 2 * cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) 0 *
        (cellPoint x Y G.n 0 ^ (1 - ((σ : ℝ) + 1)) / Real.log (cellPoint x Y G.n 0))
      = 2 * (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) 0 *
          cellPoint x Y G.n 0 ^ (1 - ((σ : ℝ) + 1))) / Real.log (cellPoint x Y G.n 0) := by ring
    _ ≤ 2 * ((w : ℝ) / G.m 0) / Real.log (cellPoint x Y G.n 0) :=
        div_le_div_of_nonneg_right (by linarith) (by linarith)
    _ ≤ 2 * ((w : ℝ) / G.m 0) / G.Llo 0 :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hlo
    _ = 2 * (w : ℝ) / G.m 0 / G.Llo 0 := by ring

/-- A jump edge term. -/
theorem Encl.edge_succ_le {σ : ℚ} (hσ : 0 ≤ σ) {k : ℕ} (hk : k + 1 < G.n) {w : ℚ}
    (hw : Real.exp (G.phi σ (k + 1)) ≤ w) :
    2 * max (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (k + 1) -
        cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (k + 1 - 1)) 0 *
        (cellPoint x Y G.n (k + 1) ^ (1 - ((σ : ℝ) + 1)) /
          Real.log (cellPoint x Y G.n (k + 1))) ≤
      (2 * (w : ℝ) / G.m (k + 1) * (G.edgeF (k + 1) : ℝ) / G.Llo (k + 1)) := by
  simp only [Nat.add_sub_cancel]
  have h := H.gX_le hσ hk hw
  have hlo := H.Llo_le (j := k + 1) (by omega)
  have hlo1 := H.one_lt_Llo (j := k + 1) (by omega)
  have hm := H.m_pos hk
  have hw0 : (0 : ℝ) ≤ w := le_trans (Real.exp_pos _).le hw
  have hρ := H.rho_le hk
  set g1 := cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (k + 1)
  set g0 := cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) k
  have hg1 : 0 ≤ g1 := cellG_nonneg_geo (x := x) (Y := Y) (G := G) (k + 1)
  have he : (G.edgeF (k + 1) : ℝ) = max 0 (1 - (G.rho (k + 1) : ℝ)) := by
    unfold GeoQ.edgeF
    simp only [Nat.add_one_ne_zero, ↓reduceIte]
    push_cast
    rfl
  rw [he]
  set F := max 0 (1 - (G.rho (k + 1) : ℝ))
  have hF0 : 0 ≤ F := le_max_left _ _
  have hmax : max (g1 - g0) 0 ≤ g1 * F := by
    apply max_le
    · have : g1 * (1 - (G.rho (k + 1) : ℝ)) ≤ g1 * F :=
        mul_le_mul_of_nonneg_left (le_max_right _ _) hg1
      nlinarith
    · exact mul_nonneg hg1 hF0
  have hX := Real.rpow_nonneg (H.X_pos (k + 1)).le (1 - ((σ : ℝ) + 1))
  set Xs := cellPoint x Y G.n (k + 1) ^ (1 - ((σ : ℝ) + 1))
  set L := Real.log (cellPoint x Y G.n (k + 1))
  have hL : 0 < L := by linarith
  calc 2 * max (g1 - g0) 0 * (Xs / L) ≤ 2 * (g1 * F) * (Xs / L) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        linarith
    _ = 2 * F * (g1 * Xs) / L := by ring
    _ ≤ 2 * F * ((w : ℝ) / G.m (k + 1)) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left h (by positivity)) hL.le
    _ ≤ 2 * F * ((w : ℝ) / G.m (k + 1)) / G.Llo (k + 1) :=
        div_le_div_of_nonneg_left (by positivity) (by linarith) hlo
    _ = 2 * (w : ℝ) / G.m (k + 1) * F / G.Llo (k + 1) := by ring

/-- The edge term of cell `j`, as it appears in `cellEdge`. -/
noncomputable def edgeTerm (x Y : ℝ) (G : GeoQ) (s : ℝ) (j : ℕ) : ℝ :=
  if j = 0 then
    2 * cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) 0 *
      (cellPoint x Y G.n 0 ^ (1 - s) / Real.log (cellPoint x Y G.n 0))
  else
    2 * max (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j -
      cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (j - 1)) 0 *
      (cellPoint x Y G.n j ^ (1 - s) / Real.log (cellPoint x Y G.n j))

theorem Encl.edgeTerm_le {σ : ℚ} (hσ : 0 ≤ σ) {j : ℕ} (hj : j < G.n) {w : ℚ}
    (hw : Real.exp (G.phi σ j) ≤ w) :
    0 ≤ edgeTerm x Y G ((σ : ℝ) + 1) j ∧
      edgeTerm x Y G ((σ : ℝ) + 1) j ≤ 2 * (w : ℝ) / G.m j * (G.edgeF j : ℝ) / G.Llo j := by
  have hg := fun j => cellG_nonneg_geo (x := x) (Y := Y) (G := G) j
  rcases Nat.eq_zero_or_pos j with h0 | hpos
  · subst h0
    refine ⟨?_, ?_⟩
    · unfold edgeTerm
      simp only [↓reduceIte]
      have := H.one_lt_L (j := 0) (by omega)
      have := Real.rpow_nonneg (H.X_pos 0).le (1 - ((σ : ℝ) + 1))
      have := hg 0
      positivity
    · unfold edgeTerm
      simp only [↓reduceIte]
      exact H.edge0_le hσ hw
  · obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
    refine ⟨?_, ?_⟩
    · unfold edgeTerm
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      have := H.one_lt_L (j := k + 1) hj.le
      have := Real.rpow_nonneg (H.X_pos (k + 1)).le (1 - ((σ : ℝ) + 1))
      have := le_max_right (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (k + 1) -
        cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) (k + 1 - 1)) 0
      positivity
    · unfold edgeTerm
      simp only [Nat.add_one_ne_zero, ↓reduceIte]
      exact H.edge_succ_le hσ hj hw

omit H in
theorem cellEdge_eq_sum (s : ℝ) (hn : 0 < G.n) :
    cellEdge G.n (cellPoint x Y G.n) (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n)) s =
      ∑ j ∈ range G.n, edgeTerm x Y G s j := by
  unfold cellEdge
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hn, mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  have hj0 : j ≠ 0 := by
    have := (mem_Ico.mp hj).1
    omega
  unfold edgeTerm
  simp only [hj0, ↓reduceIte]
  ring

/-! ## The recursion over the cells -/

omit H in
theorem nextW_le {σ : ℚ} (hσ : ∀ j < G.n, |G.stepR σ (G.m j)| ≤ 1 ∧ |G.phi σ j| ≤ 64)
    {j : ℕ} (hj : j + 1 < G.n) {w : ℚ} (hw : Real.exp (G.phi σ j) ≤ w) :
    Real.exp (G.phi σ (j + 1)) ≤ (G.nextW σ j w : ℝ) := by
  unfold GeoQ.nextW
  split_ifs with hm
  · have hstep : G.phi σ (j + 1) = G.phi σ j + G.stepR σ (G.m j) := by
      unfold GeoQ.phi GeoQ.stepR GeoQ.Lhi GeoQ.Llo
      rw [hm]
      push_cast
      ring
    have hr : Real.exp (G.stepR σ (G.m j)) ≤ (G.rUp σ (G.m j) : ℝ) :=
      (exp_le_taylorUp (hσ j (by omega)).1).trans (le_roundUpQ_real _)
    rw [hstep]
    push_cast
    rw [Real.exp_add]
    refine le_trans ?_ (le_roundUpQ_real _)
    push_cast
    exact mul_le_mul hw hr (Real.exp_pos _).le (le_trans (Real.exp_pos _).le hw)
  · exact exp_le_expUpQ (hσ (j + 1) hj).2

omit H in
theorem accum_sound (term : ℕ → ℚ → ℚ → ℚ) (sA sB : ℚ) (F : ℕ → ℝ)
    (hA : ∀ j < G.n, |G.stepR sA (G.m j)| ≤ 1 ∧ |G.phi sA j| ≤ 64)
    (hB : ∀ j < G.n, |G.stepR sB (G.m j)| ≤ 1 ∧ |G.phi sB j| ≤ 64)
    (hcell : ∀ j < G.n, ∀ wA wB : ℚ, Real.exp (G.phi sA j) ≤ wA → Real.exp (G.phi sB j) ≤ wB →
      F j ≤ term j wA wB) :
    ∀ k j (wA wB : ℚ), j + k ≤ G.n → Real.exp (G.phi sA j) ≤ wA →
      Real.exp (G.phi sB j) ≤ wB →
      ∑ t ∈ range k, F (j + t) ≤ (G.accum term sA sB k j wA wB : ℝ)
  | 0, j, wA, wB, _, _, _ => by simp [GeoQ.accum]
  | k + 1, j, wA, wB, hjk, hwA, hwB => by
      rw [Finset.sum_range_succ']
      simp only [GeoQ.accum]
      push_cast
      have h1 := hcell j (by omega) wA wB hwA hwB
      rcases Nat.eq_zero_or_pos k with hk | hk
      · subst hk
        simp only [Finset.range_zero, Finset.sum_empty, GeoQ.accum, Rat.cast_zero, add_zero,
          zero_add]
        simpa using h1
      · have ih := accum_sound term sA sB F hA hB hcell k (j + 1) (G.nextW sA j wA)
          (G.nextW sB j wB) (by omega) (nextW_le (G := G) hA (by omega) hwA)
          (nextW_le (G := G) hB (by omega) hwB)
        have he : ∑ t ∈ range k, F (j + (t + 1)) = ∑ t ∈ range k, F (j + 1 + t) := by
          apply Finset.sum_congr rfl
          intro t _
          congr 1
          omega
        rw [he, add_zero]
        linarith

/-! ## The cell bounds -/

theorem Encl.e_bounds (herr : G.err = 2411 / (5000000 * G.Llo 0)) :
    0 ≤ (2411 / (5000000 * Real.log x) : ℝ) ∧
    (2411 / (5000000 * Real.log x) : ℝ) ≤ (G.ehi : ℝ) := by
  have hlo := H.Llo_le (j := 0) (by omega)
  have hlo1 := H.one_lt_Llo (j := 0) (by omega)
  have h0 : Real.log (cellPoint x Y G.n 0) = Real.log x := by rw [cellPoint_zero]
  rw [h0] at hlo
  have hehi : (G.ehi : ℝ) = 2411 / (5000000 * (G.Llo 0 : ℝ)) := by
    unfold GeoQ.ehi
    rw [herr]
    push_cast
    rfl
  rw [hehi]
  have hlx : 0 < Real.log x := by linarith
  refine ⟨div_nonneg (by norm_num) (mul_nonneg (by norm_num) hlx.le), ?_⟩
  apply div_le_div_of_nonneg_left (by norm_num) (mul_pos (by norm_num) (by linarith))
  linarith

omit H in
theorem combine_le {A B C wA B' C' e e' : ℝ} (hA : A ≤ wA) (hB0 : 0 ≤ B) (hB : B ≤ B')
    (hC0 : 0 ≤ C) (hC : C ≤ C') (he0 : 0 ≤ e) (he : e ≤ e') :
    A + (1 / 2 + e) * B + e * C ≤ wA + (1 / 2 + e') * B' + e' * C' := by
  have h1 : (1 / 2 + e) * B ≤ (1 / 2 + e') * B' := mul_le_mul (by linarith) hB hB0 (by linarith)
  have h2 : e * C ≤ e' * C' := mul_le_mul he hC hC0 (by linarith)
  linarith

/-- **The cell bound at `s = 1`** (`eq:record:cell-charge` at `a_T`, `d = 2`): M2's `cellBound` of a
piece with the geometric cells of `[x, Y)` and `n_j = ⌊570/log x_{j+1}⌋`, with `thm:bmor`'s error
`2411/(5·10⁶ log x_0)`, is at most the rational `G.bound2`. -/
theorem Encl.cellBound_le_bound2_e (P : MiddlePiece) (hPn : P.n = G.n)
    (hPx : P.x = cellPoint x Y G.n) (hPnc : P.nc = cellCard 570 x Y G.n) {e : ℝ} (he0 : 0 ≤ e)
    (he : e ≤ (G.ehi : ℝ)) :
    cellBound P (aQ : ℝ) 1 e ≤ (G.bound2 : ℝ) := by
  have hn := H.n_pos
  have hc := (G.checks_spec H.checks).2.2.2.2.2.2.2
  unfold cellBound
  rw [hPn, hPx, hPnc]
  simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  rw [cellEdge_eq_sum 1 hn, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hs := accum_sound (G := G) G.term2 1 0
    (fun j => cellPi (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellPoint x Y G.n j ^ (-(1 : ℝ)) +
      (1 / 2 + e) * (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral 1 (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1))) +
      e * edgeTerm x Y G 1 j)
    (fun j hj => ⟨(hc j hj).2.2.2.2.2.2.2.2.2.2.2.1, (hc j hj).2.2.2.2.2.2.1⟩)
    (fun j hj => ⟨(hc j hj).2.2.2.2.2.2.2.2.2.1, (hc j hj).2.2.2.2.1⟩)
    (fun j hj wA wB hwA hwB => by
      have hA := H.termA_le (s := 1) (by norm_num) hj hwA
      push_cast at hA
      obtain ⟨hB0, hB⟩ := H.termB1_le hj hwB
      obtain ⟨hC0, hC⟩ := H.edgeTerm_le (σ := 0) (le_refl 0) hj hwB
      have h01 : ((0 : ℚ) : ℝ) + 1 = 1 := by norm_num
      rw [h01] at hC0 hC
      refine le_trans ?_ (le_roundUpQ_real _)
      push_cast
      exact combine_le hA hB0 hB hC0 hC he0 he)
    G.n 0 (G.W 1 0) (G.W 0 0) (by omega)
    (exp_le_expUpQ (hc 0 hn).2.2.2.2.2.2.1) (exp_le_expUpQ (hc 0 hn).2.2.2.2.1)
  simp only [zero_add] at hs
  unfold GeoQ.bound2
  convert hs using 2

/-- **The cell bound at `s = 3/2`** (`eq:record:cell-charge` at `a_T`, `d = 3`). -/
theorem Encl.cellBound_le_bound3_e (P : MiddlePiece) (hPn : P.n = G.n)
    (hPx : P.x = cellPoint x Y G.n) (hPnc : P.nc = cellCard 570 x Y G.n) {e : ℝ} (he0 : 0 ≤ e)
    (he : e ≤ (G.ehi : ℝ)) :
    cellBound P (aQ : ℝ) (3 / 2) e ≤ (G.bound3 : ℝ) := by
  have hn := H.n_pos
  have hc := (G.checks_spec H.checks).2.2.2.2.2.2.2
  unfold cellBound
  rw [hPn, hPx, hPnc]
  simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  rw [cellEdge_eq_sum (3 / 2) hn, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hs := accum_sound (G := G) G.term3 (3 / 2) (1 / 2)
    (fun j => cellPi (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellPoint x Y G.n j ^ (-(3 / 2 : ℝ)) +
      (1 / 2 + e) * (cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1))) +
      e * edgeTerm x Y G (3 / 2) j)
    (fun j hj => ⟨(hc j hj).2.2.2.2.2.2.2.2.2.2.2.2, (hc j hj).2.2.2.2.2.2.2.1⟩)
    (fun j hj => ⟨(hc j hj).2.2.2.2.2.2.2.2.2.2.1, (hc j hj).2.2.2.2.2.1⟩)
    (fun j hj wA wB hwA hwB => by
      have hA := H.termA_le (s := 3 / 2) (by norm_num) hj hwA
      push_cast at hA
      obtain ⟨hB0, hB⟩ := H.termB3_le hj hwB
      obtain ⟨hC0, hC⟩ := H.edgeTerm_le (σ := 1 / 2) (by norm_num) hj hwB
      have h01 : ((1 / 2 : ℚ) : ℝ) + 1 = 3 / 2 := by norm_num
      rw [h01] at hC0 hC
      refine le_trans ?_ (le_roundUpQ_real _)
      push_cast
      exact combine_le hA hB0 hB hC0 hC he0 he)
    G.n 0 (G.W (3 / 2) 0) (G.W (1 / 2) 0) (by omega)
    (exp_le_expUpQ (hc 0 hn).2.2.2.2.2.2.2.1) (exp_le_expUpQ (hc 0 hn).2.2.2.2.2.1)
  simp only [zero_add] at hs
  unfold GeoQ.bound3
  convert hs using 2

/-- **The cell bound at `s = 1` with `thm:bmor`'s error** `2411/(5·10⁶ log x_0)` (`d = 2`). -/
theorem Encl.cellBound_le_bound2 (P : MiddlePiece) (hPn : P.n = G.n)
    (hPx : P.x = cellPoint x Y G.n) (hPnc : P.nc = cellCard 570 x Y G.n)
    (herr : G.err = 2411 / (5000000 * G.Llo 0)) :
    cellBound P (aQ : ℝ) 1 (2411 / (5000000 * Real.log (P.x 0))) ≤ (G.bound2 : ℝ) := by
  have h0 : P.x 0 = x := by rw [hPx, cellPoint_zero]
  rw [h0]
  exact H.cellBound_le_bound2_e P hPn hPx hPnc (H.e_bounds herr).1 (H.e_bounds herr).2

/-- **The cell bound at `s = 3/2` with `thm:bmor`'s error** (`d = 3`). -/
theorem Encl.cellBound_le_bound3 (P : MiddlePiece) (hPn : P.n = G.n)
    (hPx : P.x = cellPoint x Y G.n) (hPnc : P.nc = cellCard 570 x Y G.n)
    (herr : G.err = 2411 / (5000000 * G.Llo 0)) :
    cellBound P (aQ : ℝ) (3 / 2) (2411 / (5000000 * Real.log (P.x 0))) ≤ (G.bound3 : ℝ) := by
  have h0 : P.x 0 = x := by rw [hPx, cellPoint_zero]
  rw [h0]
  exact H.cellBound_le_bound3_e P hPn hPx hPnc (H.e_bounds herr).1 (H.e_bounds herr).2

end Geo

end Sarkozy.AnalyticCells

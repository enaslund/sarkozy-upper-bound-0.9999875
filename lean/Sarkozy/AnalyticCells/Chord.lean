module

public import Sarkozy.AnalyticCells.GeoCells

@[expose] public section

/-!
# The secant bound for `I_j(3/2)` and the sharper cell bound at `s = 3/2`

`lem:record:block-charge`(i), `eq:record:cell-charge`.

`GeoCells.lean` bounds `I_j(3/2) = ∫ t^{-3/2}/log t` with `1/log t ≤ 1/log x_j`, which loses
`≈ Δ/(2L_j)`; on the wide F1 cells below `X_Ch` (two cells in `[2·10⁷, 2.2·10⁷)`) that is `0.13 %`.
Here `1/log t` is bounded by its secant on `[log a, log b]`, as the pipeline's `laplace_over_log`
does: **`cellIntegral_three_halves_chord`**,
`I(3/2) ≤ 2 (a^{-1/2}(log b - 2) - b^{-1/2}(log a - 2)) / (log a log b)`. With `b^{-1/2} =
a^{-1/2} e^{-Δ/2}` this is `2 a^{-1/2} (Δ + (log a - 2)(1 - e^{-Δ/2}))/(log a log b)`.

`GeoQ.term3c`, `GeoQ.bound3c` use it; **`Encl.cellBound_le_bound3c_e`** is the soundness theorem
(for `log x ≥ 2`).
-/

open Finset

namespace Sarkozy.AnalyticCells

open Sarkozy.Misc Sarkozy.PartV

/-- **The secant bound** for `I(3/2)` on `[a, b]`, `1 < a ≤ b`. -/
theorem cellIntegral_three_halves_chord {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    cellIntegral (3 / 2) a b ≤ 2 * (a ^ (-(1 / 2 : ℝ)) * (Real.log b - 2) -
      b ^ (-(1 / 2 : ℝ)) * (Real.log a - 2)) / (Real.log a * Real.log b) := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := by linarith
  set L0 := Real.log a with hL0
  set L1 := Real.log b with hL1
  have hl0 : 0 < L0 := Real.log_pos ha
  have hl01 : L0 ≤ L1 := Real.log_le_log ha0 hab
  have hl1 : 0 < L1 := lt_of_lt_of_le hl0 hl01
  set c : ℝ → ℝ := fun t => t ^ (-(3 / 2 : ℝ)) * (L0 + L1 - Real.log t) / (L0 * L1) with hc
  have hcont : ContinuousOn c (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := by have := ht.1; linarith
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div_const
    exact (Real.continuousAt_rpow_const _ _ (Or.inl ht0)).mul
      (continuousAt_const.sub (Real.continuousAt_log ht0))
  have h1 : cellIntegral (3 / 2) a b ≤ ∫ t in a..b, c t := by
    unfold cellIntegral
    apply intervalIntegral.integral_mono_on hab
      ((continuousOn_fs (3 / 2) ha).intervalIntegrable_of_Icc hab)
      (hcont.intervalIntegrable_of_Icc hab)
    intro t ht
    have ht1 : 1 < t := lt_of_lt_of_le ha ht.1
    have hlt : 0 < Real.log t := Real.log_pos ht1
    have hla : L0 ≤ Real.log t := Real.log_le_log ha0 ht.1
    have hlb : Real.log t ≤ L1 := Real.log_le_log (by linarith) ht.2
    unfold fs
    simp only [hc]
    have hp : 0 ≤ t ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (by linarith) _
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hp
    rw [inv_eq_one_div, div_le_div_iff₀ hlt (mul_pos hl0 hl1)]
    nlinarith [mul_nonneg (sub_nonneg.mpr hla) (sub_nonneg.mpr hlb)]
  -- the antiderivative
  set G : ℝ → ℝ := fun t =>
    2 / (L0 * L1) * (t ^ (-(1 / 2 : ℝ)) * (Real.log t + 2) - (L0 + L1) * t ^ (-(1 / 2 : ℝ)))
    with hG
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt G (c t) t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have hr := Real.hasDerivAt_rpow_const (x := t) (p := -(1 / 2 : ℝ)) (Or.inl ht0.ne')
    have hl := Real.hasDerivAt_log ht0.ne'
    have h := ((hr.mul (hl.add_const 2)).sub (hr.const_mul (L0 + L1))).const_mul (2 / (L0 * L1))
    convert h using 1
    simp only [hc]
    have e1 : t ^ (-(1 / 2 : ℝ) - 1) = t ^ (-(3 / 2 : ℝ)) := by norm_num
    have e2 : t ^ (-(1 / 2 : ℝ)) = t ^ (-(3 / 2 : ℝ)) * t := by
      rw [← Real.rpow_add_one ht0.ne']
      norm_num
    rw [e1, e2]
    field_simp
    ring
  have h2 : ∫ t in a..b, c t = G b - G a :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable_of_Icc hab)
  rw [h2] at h1
  refine h1.trans (le_of_eq ?_)
  simp only [hG]
  field_simp
  ring

/-! ## The sharper term and bound at `s = 3/2` -/

namespace GeoQ

variable (G : GeoQ)

/-- The bound of the contribution of cell `j` at `s = 3/2` with the secant bound. -/
def term3c (j : ℕ) (wA wB : ℚ) : ℚ :=
  roundUpQ (wA + (1 / 2 + G.ehi) *
      (wB * (2 * (G.dhi + (G.Lhi j - 2) * kappa (G.dhi / 2))) /
        (G.m j * (G.Llo j * G.Llo (j + 1)))) +
    G.ehi * (2 * wB / G.m j * G.edgeF j / G.Llo j))

/-- The rational cell bound at `s = 3/2` with the secant bound. -/
def bound3c : ℚ := G.accum G.term3c (3 / 2) (1 / 2) G.n 0 (G.W (3 / 2) 0) (G.W (1 / 2) 0)

end GeoQ

section Geo

variable {x Y : ℝ} {G : GeoQ} (H : Encl G x Y)
include H

/-- The main term at `s = 3/2` with the secant bound. -/
theorem Encl.termB3c_le (h2 : (2 : ℚ) ≤ G.lxl) {j : ℕ} (hj : j < G.n) {w : ℚ}
    (hw : Real.exp (G.phi (1 / 2) j) ≤ w) :
    0 ≤ cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ∧
      cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ≤
      (w : ℝ) * (2 * ((G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * (kappa (G.dhi / 2) : ℝ))) /
        ((G.m j : ℝ) * ((G.Llo j : ℝ) * G.Llo (j + 1))) := by
  obtain ⟨hB0, -⟩ := H.termB3_le hj hw
  refine ⟨hB0, ?_⟩
  have hX := H.one_lt_X hj.le
  have hmono := cellPoint_mono H.x_pos H.le G.n j
  have hLlo := H.Llo_le hj.le
  have hLlo1 := H.Llo_le (j := j + 1) (by omega)
  have hLhi := H.le_Lhi hj.le
  have hlo1 := H.one_lt_Llo hj.le
  have hlo11 := H.one_lt_Llo (j := j + 1) (by omega)
  have hΔ0 := H.delta_nonneg
  have hΔle := H.delta_le
  have hd0 := H.dhi_nonneg
  have hd2 := (G.checks_spec H.checks).2.2.2.2.2.2.1
  have hm := H.m_pos hj
  have hg := cellG_nonneg_geo (x := x) (Y := Y) (G := G) j
  have hI := cellIntegral_three_halves_chord hX hmono
  set L := Real.log (cellPoint x Y G.n j) with hLdef
  set Δ := (Real.log Y - Real.log x) / G.n with hΔdef
  have hsucc : Real.log (cellPoint x Y G.n (j + 1)) = L + Δ := H.L_succ j
  have hL2 : (2 : ℝ) ≤ L := by
    have h2' : (2 : ℝ) ≤ G.lxl := by exact_mod_cast h2
    have : (G.lxl : ℝ) ≤ G.Llo j := by
      have hL : (G.Llo j : ℝ) = G.lxl + (j : ℝ) / G.n * (G.lYl - G.lxl) := by
        unfold GeoQ.Llo
        push_cast
        ring
      rw [hL]
      obtain ⟨t0, -⟩ := H.t_mem hj.le
      have h5 : (0 : ℝ) ≤ G.lYl - G.lxl := by
        obtain ⟨-, -, h2, h3, h4, -⟩ := G.checks_spec H.checks
        have : G.lxl ≤ G.lYl := h2.trans h4
        have : (G.lxl : ℝ) ≤ G.lYl := by exact_mod_cast this
        linarith
      nlinarith [mul_nonneg t0 h5]
    linarith
  have hp1 : cellPoint x Y G.n j ^ (-(1 / 2 : ℝ)) = Real.exp (-(1 / 2) * L) := by
    rw [Real.rpow_def_of_pos (H.X_pos j)]
    congr 1
    ring
  have hp2 : cellPoint x Y G.n (j + 1) ^ (-(1 / 2 : ℝ)) =
      Real.exp (-(1 / 2) * L) * Real.exp (-(Δ / 2)) := by
    rw [Real.rpow_def_of_pos (H.X_pos (j + 1)), hsucc, ← Real.exp_add]
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
  have hκ0 : (0 : ℝ) ≤ (kappa (G.dhi / 2) : ℝ) := le_trans hk0 hk'
  set κ := (kappa (G.dhi / 2) : ℝ)
  set E1 := Real.exp (-(1 / 2) * L)
  have hE1 : 0 < E1 := Real.exp_pos _
  -- the bracket
  have hbr : (L + Δ - 2) - Real.exp (-(Δ / 2)) * (L - 2) ≤
      (G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ := by
    have h1 : (L + Δ - 2) - Real.exp (-(Δ / 2)) * (L - 2) =
        Δ + (L - 2) * (1 - Real.exp (-(Δ / 2))) := by
      ring
    rw [h1]
    have h3 : (L - 2) * (1 - Real.exp (-(Δ / 2))) ≤ ((G.Lhi j : ℝ) - 2) * κ :=
      mul_le_mul (by linarith) hk' hk0 (by linarith)
    linarith
  have hI' : cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1)) ≤
      2 * E1 * ((G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ) / (L * (L + Δ)) := by
    refine hI.trans ?_
    rw [hp1, hp2, hsucc]
    have hden : 0 < L * (L + Δ) := by positivity
    apply div_le_div_of_nonneg_right _ hden.le
    have : E1 * (L + Δ - 2) - E1 * Real.exp (-(Δ / 2)) * (L - 2) =
        E1 * ((L + Δ - 2) - Real.exp (-(Δ / 2)) * (L - 2)) := by ring
    nlinarith [mul_le_mul_of_nonneg_left hbr hE1.le]
  have hgE := H.cellG_eq hj
  have hW := H.exp_le_W (σ := 1 / 2) (by norm_num) hj hw
  set E := Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) * Real.log (cellPoint x Y G.n (j + 1)))
  have hEE : E * E1 = Real.exp (2 * (aQ : ℝ) * (G.m j : ℝ) *
      Real.log (cellPoint x Y G.n (j + 1)) - ((1 / 2 : ℚ) : ℝ) * L) := by
    rw [← Real.exp_add]
    congr 1
    push_cast
    ring
  have hnum0 : (0 : ℝ) ≤ (G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ :=
    add_nonneg hd0 (mul_nonneg (by linarith) hκ0)
  have hw0 : (0 : ℝ) ≤ w := le_trans (Real.exp_pos _).le hw
  calc cellG (aQ : ℝ) (cellPoint x Y G.n) (cellCard 570 x Y G.n) j *
        cellIntegral (3 / 2) (cellPoint x Y G.n j) (cellPoint x Y G.n (j + 1))
      ≤ E / G.m j * (2 * E1 * ((G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ) / (L * (L + Δ))) := by
        rw [hgE]
        exact mul_le_mul_of_nonneg_left hI' (by positivity)
    _ = (E * E1) * (2 * ((G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ)) /
          ((G.m j : ℝ) * (L * (L + Δ))) := by
        field_simp
    _ ≤ (w : ℝ) * (2 * ((G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ)) /
          ((G.m j : ℝ) * (L * (L + Δ))) := by
        rw [hEE]
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hW (by positivity)
    _ ≤ (w : ℝ) * (2 * ((G.dhi : ℝ) + ((G.Lhi j : ℝ) - 2) * κ)) /
          ((G.m j : ℝ) * ((G.Llo j : ℝ) * G.Llo (j + 1))) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        apply mul_le_mul_of_nonneg_left _ hm.le
        rw [← hsucc]
        exact mul_le_mul hLlo hLlo1 (by linarith) (by linarith)

/-- **The cell bound at `s = 3/2` with the secant bound**, for any error constant `0 ≤ e ≤ ehi`. -/
theorem Encl.cellBound_le_bound3c_e (h2 : (2 : ℚ) ≤ G.lxl) (P : MiddlePiece) (hPn : P.n = G.n)
    (hPx : P.x = cellPoint x Y G.n) (hPnc : P.nc = cellCard 570 x Y G.n) {e : ℝ} (he0 : 0 ≤ e)
    (he : e ≤ (G.ehi : ℝ)) :
    cellBound P (aQ : ℝ) (3 / 2) e ≤ (G.bound3c : ℝ) := by
  have hn := H.n_pos
  have hc := (G.checks_spec H.checks).2.2.2.2.2.2.2
  unfold cellBound
  rw [hPn, hPx, hPnc]
  simp only [Nat.pos_iff_ne_zero.mp hn, ↓reduceIte]
  rw [cellEdge_eq_sum (3 / 2) hn, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_add_distrib]
  have hs := accum_sound (G := G) G.term3c (3 / 2) (1 / 2)
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
      obtain ⟨hB0, hB⟩ := H.termB3c_le h2 hj hwB
      obtain ⟨hC0, hC⟩ := H.edgeTerm_le (σ := 1 / 2) (by norm_num) hj hwB
      have h01 : ((1 / 2 : ℚ) : ℝ) + 1 = 3 / 2 := by norm_num
      rw [h01] at hC0 hC
      refine le_trans ?_ (le_roundUpQ_real _)
      push_cast
      exact combine_le hA hB0 hB hC0 hC he0 he)
    G.n 0 (G.W (3 / 2) 0) (G.W (1 / 2) 0) (by omega)
    (exp_le_expUpQ (hc 0 hn).2.2.2.2.2.2.2.1) (exp_le_expUpQ (hc 0 hn).2.2.2.2.2.1)
  simp only [zero_add] at hs
  unfold GeoQ.bound3c
  convert hs using 2

end Geo

end Sarkozy.AnalyticCells

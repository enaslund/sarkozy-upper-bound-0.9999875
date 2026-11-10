module

public import Sarkozy.NumericalFields.Bands
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Kernel-checkable bounds for `bandBound` (HS): the generic lemmas

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(i), `eq:record:cell-charge`:
E2's `NumericalFields.bandBound a d k` is the right side of `eq:record:cell-charge` at `s = d/2`
over the recorded cells of band `k`. This file proves the generic estimates used to bound it by a
rational number (`HsumProof/BandUB.lean`):

* rational constants with `log2lo < log 2 < log2hi`, `eLo < e` (Mathlib's 9-digit bounds);
* `exp_le_expUB`: `exp x ≤ expUB x` for rational `0 ≤ x ≤ 2` (Taylor with remainder,
  `Real.exp_bound'`, at `x/2`, squared);
* `log_ge_of_pow`, `mul_log_le_of_pow`: logarithms of integers from integer powers;
* `rpow_neg_half_le`: `A^{-d/2} ≤ 1/r^d` when `r² ≤ A`;
* `cellIntegral_le`: `∫_a^b t^{-s}/log t ≤ (b - a) a^{-s}/log a` (the integrand decreases);
* `bandBound_le_cells`: `bandBound a d k ≤ ∑_j cellF a d k j`, a sum of per-cell terms with no
  integral and no positive part;
* `group_le`: a block of consecutive cells with `x_j ≥ A`, `Π_j ≤ P`, `g_j ≤ G` is bounded by an
  explicit expression in `A, P, G` and the two end points (the interval lengths telescope).
-/

open Finset

namespace Sarkozy.HsumProof

open Sarkozy.NumericalFields Sarkozy.Misc Sarkozy.PartV

/-! ## Rational constants -/

/-- A rational lower bound of `log 2`. -/
def log2lo : ℚ := 6931471803 / 10 ^ 10

/-- A rational upper bound of `log 2`. -/
def log2hi : ℚ := 6931471808 / 10 ^ 10

/-- A rational lower bound of `e`. -/
def eLo : ℚ := 27182818283 / 10 ^ 10

/-- The error constant `2411/(5·10⁶)` of `thm:bmor` in `bandBound` (divided by `log x₀`). -/
def eC : ℚ := 2411 / 5000000

theorem log2lo_lt : (log2lo : ℝ) < Real.log 2 := by
  have h := Real.log_two_gt_d9
  unfold log2lo
  push_cast
  norm_num at h ⊢
  linarith

theorem log2_lt_hi : Real.log 2 < (log2hi : ℝ) := by
  have h := Real.log_two_lt_d9
  unfold log2hi
  push_cast
  norm_num at h ⊢
  linarith

theorem eLo_lt : (eLo : ℝ) < Real.exp 1 := by
  have h := Real.exp_one_gt_d9
  unfold eLo
  push_cast
  norm_num at h ⊢
  linarith

theorem log2lo_pos : (0 : ℝ) < log2lo := by
  unfold log2lo
  push_cast
  norm_num

/-! ## `exp` -/

/-- Taylor's upper bound `∑_{m<12} y^m/m! + y^{12}·13/(12!·12)` of `exp y` on `[0, 1]`. -/
def taylorUB (y : ℚ) : ℚ :=
  (∑ m ∈ range 12, y ^ m / (m.factorial : ℚ)) + y ^ 12 * 13 / ((Nat.factorial 12 : ℚ) * 12)

theorem exp_le_taylorUB {y : ℚ} (h0 : 0 ≤ y) (h1 : y ≤ 1) : Real.exp y ≤ (taylorUB y : ℝ) := by
  have h := Real.exp_bound' (x := (y : ℝ)) (by exact_mod_cast h0) (by exact_mod_cast h1)
    (n := 12) (by norm_num)
  refine h.trans (le_of_eq ?_)
  unfold taylorUB
  push_cast
  ring

/-- `exp x ≤ taylorUB(x/2)²`. -/
def expUB (x : ℚ) : ℚ := taylorUB (x / 2) ^ 2

theorem exp_le_expUB {x : ℚ} (h0 : 0 ≤ x) (h2 : x ≤ 2) : Real.exp x ≤ (expUB x : ℝ) := by
  have hx : Real.exp (x : ℝ) = Real.exp ((x : ℝ) / 2) ^ 2 := by
    rw [sq, ← Real.exp_add]
    ring_nf
  have hy := exp_le_taylorUB (y := x / 2) (by positivity) (by linarith)
  have hy' : Real.exp ((x : ℝ) / 2) ≤ (taylorUB (x / 2) : ℝ) := by
    have h := hy
    push_cast at h
    exact h
  rw [hx, expUB, Rat.cast_pow]
  exact pow_le_pow_left₀ (Real.exp_pos _).le hy' 2

/-! ## Logarithms of integers -/

/-- From `2^p ≤ X^q`: `(p/q)·log2lo ≤ log X`. -/
theorem log_ge_of_pow {X : ℕ} (p q : ℕ) (hq : 0 < q) (h : 2 ^ p ≤ X ^ q) :
    (((p : ℚ) / q * log2lo : ℚ) : ℝ) ≤ Real.log X := by
  have hX : 1 ≤ X := by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · subst h0
      rw [zero_pow hq.ne'] at h
      exact absurd h (Nat.not_le.mpr (Nat.two_pow_pos p))
    · exact h0
  have hX' : (0 : ℝ) < X := by exact_mod_cast hX
  have h' : (2 : ℝ) ^ p ≤ (X : ℝ) ^ q := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at hl
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have h2 := log2lo_lt
  push_cast
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  calc (p : ℝ) / q * (log2lo : ℝ) ≤ (p : ℝ) / q * Real.log 2 :=
        mul_le_mul_of_nonneg_left h2.le (by positivity)
    _ = (p * Real.log 2) / q := by ring
    _ ≤ (q * Real.log X) / q := div_le_div_of_nonneg_right hl hq'.le
    _ = Real.log X := by field_simp

/-- From `Y^m ≤ eLo^L`: `m log Y ≤ L`. -/
theorem mul_log_le_of_pow {Y : ℕ} (m L : ℕ) (hY : 1 ≤ Y) (h : (Y : ℚ) ^ m ≤ eLo ^ L) :
    (m : ℝ) * Real.log Y ≤ L := by
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  have he : (0 : ℝ) < eLo := by unfold eLo; push_cast; norm_num
  have h' : (Y : ℝ) ^ m ≤ (eLo : ℝ) ^ L := by exact_mod_cast h
  have hl := Real.log_le_log (by positivity) h'
  rw [Real.log_pow, Real.log_pow] at hl
  have h1 : Real.log (eLo : ℝ) < 1 := by
    have := Real.log_lt_log he eLo_lt
    rwa [Real.log_exp] at this
  have hL : (0 : ℝ) ≤ L := Nat.cast_nonneg L
  nlinarith

/-! ## Powers -/

/-- `A^{-d/2} ≤ 1/r^d` when `0 < r`, `r² ≤ A`. -/
theorem rpow_neg_half_le {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (h : r ^ 2 ≤ A) (d : ℕ) :
    A ^ (-((d : ℝ) / 2)) ≤ 1 / r ^ d := by
  have hs : r ≤ Real.sqrt A := Real.le_sqrt_of_sq_le h
  have e : A ^ ((d : ℝ) / 2) = Real.sqrt A ^ d := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hA.le]
    congr 1
    ring
  rw [Real.rpow_neg hA.le, e, one_div]
  exact inv_anti₀ (by positivity) (pow_le_pow_left₀ hr.le hs d)

/-- `A^{1-d/2} ≤ A/r^d` when `0 < r`, `r² ≤ A`. -/
theorem rpow_one_sub_half_le {A r : ℝ} (hA : 0 < A) (hr : 0 < r) (h : r ^ 2 ≤ A) (d : ℕ) :
    A ^ (1 - (d : ℝ) / 2) ≤ A / r ^ d := by
  rw [sub_eq_add_neg, Real.rpow_add hA, Real.rpow_one]
  calc A * A ^ (-((d : ℝ) / 2)) ≤ A * (1 / r ^ d) :=
        mul_le_mul_of_nonneg_left (rpow_neg_half_le hA hr h d) hA.le
    _ = A / r ^ d := by ring

/-! ## The integrand -/

theorem fs_le {s a t : ℝ} (hs : 0 ≤ s) (ha : 1 < a) (hat : a ≤ t) : fs s t ≤ fs s a := by
  unfold fs
  have ha0 : 0 < a := by linarith
  exact div_le_div₀ (Real.rpow_nonneg ha0.le _) (Real.rpow_le_rpow_of_nonpos ha0 hat (by linarith))
    (Real.log_pos ha) (Real.log_le_log ha0 hat)

/-- `∫_a^b t^{-s}/log t ≤ (b - a) a^{-s}/log a` for `1 < a ≤ b`, `s ≥ 0`. -/
theorem cellIntegral_le {s a b : ℝ} (hs : 0 ≤ s) (ha : 1 < a) (hab : a ≤ b) :
    cellIntegral s a b ≤ (b - a) * fs s a := by
  unfold cellIntegral
  have hint : IntervalIntegrable (fs s) MeasureTheory.volume a b :=
    (continuousOn_fs s ha).intervalIntegrable_of_Icc hab
  calc ∫ t in a..b, fs s t ≤ ∫ _ in a..b, fs s a :=
        intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
          (fun t ht => fs_le hs ha ht.1)
    _ = (b - a) * fs s a := by rw [intervalIntegral.integral_const, smul_eq_mul]

/-- `x^{1-s}/log x` decreases on `(1, ∞)` for `s ≥ 1`. -/
theorem edgeTerm_le {s a t : ℝ} (hs : 1 ≤ s) (ha : 1 < a) (hat : a ≤ t) :
    t ^ (1 - s) / Real.log t ≤ a ^ (1 - s) / Real.log a := by
  have ha0 : 0 < a := by linarith
  exact div_le_div₀ (Real.rpow_nonneg ha0.le _) (Real.rpow_le_rpow_of_nonpos ha0 hat (by linarith))
    (Real.log_pos ha) (Real.log_le_log ha0 hat)

/-! ## The cell form of `bandBound` -/

/-- The error factor `e_k = 2411/(5·10⁶ log x₀)` of band `k`. -/
noncomputable def errK (k : Fin 310) : ℝ := 2411 / (5000000 * Real.log (bx k 0))

/-- **The per-cell terms**: `Π_j x_j^{-s} + (½ + e) g_j (x_{j+1} - x_j) x_j^{-s}/log x_j
+ e · 2 g_j x_j^{1-s}/log x_j`, `s = d/2`. -/
noncomputable def cellF (a : ℝ) (d : ℕ) (k : Fin 310) (j : ℕ) : ℝ :=
  cellPi a (bx k) (bnc k) j * bx k j ^ (-((d : ℝ) / 2)) +
    (1 / 2 + errK k) * (cellG a (bx k) (bnc k) j * ((bx k (j + 1) - bx k j) *
      fs ((d : ℝ) / 2) (bx k j))) +
    errK k * (2 * (cellG a (bx k) (bnc k) j *
      (bx k j ^ (1 - (d : ℝ) / 2) / Real.log (bx k j))))

theorem bx_mono (k : Fin 310) (j : ℕ) : bx k j ≤ bx k (j + 1) := by
  unfold bx
  exact cellPoint_mono (by linarith [bandX_pos k]) (bandXY k).le _ j

theorem bx_ge (k : Fin 310) (j : ℕ) : bx k 0 ≤ bx k j := by
  induction j with
  | zero => exact le_rfl
  | succ j ih => exact ih.trans (bx_mono k j)

theorem bx0_eq (k : Fin 310) : bx k 0 = (bandOf k).1 := by
  unfold bx
  exact cellPoint_zero _ _ _

theorem one_lt_bx (k : Fin 310) (j : ℕ) : 1 < bx k j := by
  have h := bx_ge k j
  rw [bx0_eq] at h
  linarith [bandX_pos k]

theorem cellG_nonneg (a : ℝ) (x : ℕ → ℝ) (nc : ℕ → ℕ) (j : ℕ) : 0 ≤ cellG a x nc j := by
  unfold cellG cellPi
  positivity

theorem errK_nonneg (k : Fin 310) : 0 ≤ errK k := by
  unfold errK
  have := Real.log_pos (one_lt_bx k 0)
  positivity

/-- `cellEdge ≤ 2 ∑_j g_j F_j` for `g, F ≥ 0` (the positive parts are at most `g_j`). -/
theorem cellEdge_le {n : ℕ} (hn : 1 ≤ n) (x g : ℕ → ℝ) (s : ℝ) (hg : ∀ j, 0 ≤ g j)
    (hF : ∀ j, 0 ≤ x j ^ (1 - s) / Real.log (x j)) :
    cellEdge n x g s ≤ 2 * ∑ j ∈ range n, g j * (x j ^ (1 - s) / Real.log (x j)) := by
  unfold cellEdge
  rw [range_eq_Ico, sum_eq_sum_Ico_succ_bot (by omega : 0 < n), mul_add]
  have h : ∑ j ∈ Ico 1 n, max (g j - g (j - 1)) 0 * (x j ^ (1 - s) / Real.log (x j)) ≤
      ∑ j ∈ Ico 1 n, g j * (x j ^ (1 - s) / Real.log (x j)) :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_right
      (max_le (by linarith [hg (j - 1)]) (hg j)) (hF j)
  linarith

/-- **`bandBound` is at most the sum of the per-cell terms** (`cellIntegral_le` on every cell,
`cellEdge_le`). -/
theorem bandBound_le_cells (k : Fin 310) (a : ℝ) {d : ℕ} (hd : 2 ≤ d) :
    bandBound a d k ≤ ∑ j ∈ range (bandN k), cellF a d k j := by
  have hs : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hI : ∑ j ∈ range (bandN k), cellG a (bx k) (bnc k) j *
        cellIntegral ((d : ℝ) / 2) (bx k j) (bx k (j + 1)) ≤
      ∑ j ∈ range (bandN k), cellG a (bx k) (bnc k) j *
        ((bx k (j + 1) - bx k j) * fs ((d : ℝ) / 2) (bx k j)) :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      (cellIntegral_le hs (one_lt_bx k j) (bx_mono k j)) (cellG_nonneg _ _ _ _)
  have hE := cellEdge_le (one_le_bandN k) (bx k) (cellG a (bx k) (bnc k)) ((d : ℝ) / 2)
    (cellG_nonneg _ _ _) (fun j => by
      have := Real.log_pos (one_lt_bx k j)
      have h0 : 0 < bx k j := by linarith [one_lt_bx k j]
      positivity)
  have he := errK_nonneg k
  have hhalf : 0 ≤ 1 / 2 + errK k := by linarith
  have h1 := mul_le_mul_of_nonneg_left hI hhalf
  have h2 := mul_le_mul_of_nonneg_left hE he
  have hsplit : ∑ j ∈ range (bandN k), cellF a d k j =
      ∑ j ∈ range (bandN k), cellPi a (bx k) (bnc k) j * bx k j ^ (-((d : ℝ) / 2)) +
      (1 / 2 + errK k) * ∑ j ∈ range (bandN k), cellG a (bx k) (bnc k) j *
        ((bx k (j + 1) - bx k j) * fs ((d : ℝ) / 2) (bx k j)) +
      errK k * (2 * ∑ j ∈ range (bandN k), cellG a (bx k) (bnc k) j *
        (bx k j ^ (1 - (d : ℝ) / 2) / Real.log (bx k j))) := by
    unfold cellF
    rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
  rw [hsplit]
  unfold bandBound
  change _ + (1 / 2 + errK k) * _ + errK k * _ ≤ _
  linarith

/-- **A block of consecutive cells** `j₀, …, j₀ + len - 1` with `x_j ≥ A > 1`, `Π_j ≤ P`,
`g_j ≤ G`, `r² ≤ A`, `λ ≤ log A`, `λ₀ ≤ log x₀`: the per-cell terms sum to at most
`len P/r^d + (½ + c/λ₀) G (x_{j₀+len} - x_{j₀})/(r^d λ) + (c/λ₀) 2 len G A/(r^d λ)`,
`c = 2411/(5·10⁶)`. -/
theorem group_le (k : Fin 310) (a : ℝ) {d : ℕ} (hd : 2 ≤ d) (j0 len : ℕ) {A P G lam lam0 r : ℝ}
    (hA : 1 < A) (hr : 0 < r) (hrA : r ^ 2 ≤ A) (hlam : 0 < lam) (hlamA : lam ≤ Real.log A)
    (hlam0 : 0 < lam0) (hlam0x : lam0 ≤ Real.log (bx k 0))
    (hx : ∀ j < len, A ≤ bx k (j0 + j))
    (hP : ∀ j < len, cellPi a (bx k) (bnc k) (j0 + j) ≤ P)
    (hG : ∀ j < len, cellG a (bx k) (bnc k) (j0 + j) ≤ G) (hP0 : 0 ≤ P) (hG0 : 0 ≤ G) :
    ∑ j ∈ range len, cellF a d k (j0 + j) ≤
      len * P / r ^ d + (1 / 2 + (eC : ℝ) / lam0) * G * (bx k (j0 + len) - bx k j0) /
        (r ^ d * lam) + (eC : ℝ) / lam0 * 2 * len * G * A / (r ^ d * lam) := by
  have hA0 : 0 < A := by linarith
  have hs : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hs1 : (1 : ℝ) ≤ (d : ℝ) / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    exact_mod_cast (by omega : 1 * 2 ≤ d)
  have hrd : 0 < r ^ d := by positivity
  have hlogA : 0 < Real.log A := Real.log_pos hA
  have hR1 : A ^ (-((d : ℝ) / 2)) ≤ 1 / r ^ d := rpow_neg_half_le hA0 hr hrA d
  have hR2 : A ^ (1 - (d : ℝ) / 2) ≤ A / r ^ d := rpow_one_sub_half_le hA0 hr hrA d
  have he : errK k ≤ (eC : ℝ) / lam0 := by
    unfold errK eC
    push_cast
    rw [div_le_div_iff₀ (by have := Real.log_pos (one_lt_bx k 0); positivity) hlam0]
    nlinarith
  have he0 := errK_nonneg k
  -- each cell
  have hcell : ∀ j < len, cellF a d k (j0 + j) ≤
      P / r ^ d + (1 / 2 + (eC : ℝ) / lam0) * G * (bx k (j0 + j + 1) - bx k (j0 + j)) /
        (r ^ d * lam) + (eC : ℝ) / lam0 * 2 * G * A / (r ^ d * lam) := by
    intro j hj
    have hxj := hx j hj
    have hxj0 : 0 < bx k (j0 + j) := by linarith
    have hgj := hG j hj
    have hg0 := cellG_nonneg a (bx k) (bnc k) (j0 + j)
    have hpj := hP j hj
    have hp0 : 0 ≤ cellPi a (bx k) (bnc k) (j0 + j) := by unfold cellPi; positivity
    have hw : 0 ≤ bx k (j0 + j + 1) - bx k (j0 + j) := by linarith [bx_mono k (j0 + j)]
    -- term 1
    have t1 : cellPi a (bx k) (bnc k) (j0 + j) * bx k (j0 + j) ^ (-((d : ℝ) / 2)) ≤ P / r ^ d := by
      have := Real.rpow_le_rpow_of_nonpos hA0 hxj (by linarith : -((d : ℝ) / 2) ≤ 0)
      calc _ ≤ P * (1 / r ^ d) := mul_le_mul hpj (this.trans hR1) (by positivity) hP0
        _ = P / r ^ d := by ring
    -- term 2
    have hfs : fs ((d : ℝ) / 2) (bx k (j0 + j)) ≤ 1 / (r ^ d * lam) := by
      refine (fs_le hs hA hxj).trans ?_
      unfold fs
      calc A ^ (-((d : ℝ) / 2)) / Real.log A ≤ (1 / r ^ d) / lam :=
            div_le_div₀ (by positivity) hR1 hlam hlamA
        _ = 1 / (r ^ d * lam) := by rw [div_div]
    have t2 : (1 / 2 + errK k) * (cellG a (bx k) (bnc k) (j0 + j) *
        ((bx k (j0 + j + 1) - bx k (j0 + j)) * fs ((d : ℝ) / 2) (bx k (j0 + j)))) ≤
        (1 / 2 + (eC : ℝ) / lam0) * G * (bx k (j0 + j + 1) - bx k (j0 + j)) /
          (r ^ d * lam) := by
      have hfs0 : 0 ≤ fs ((d : ℝ) / 2) (bx k (j0 + j)) :=
        (fs_pos (one_lt_bx k (j0 + j))).le
      have i1 : cellG a (bx k) (bnc k) (j0 + j) *
          ((bx k (j0 + j + 1) - bx k (j0 + j)) * fs ((d : ℝ) / 2) (bx k (j0 + j))) ≤
          G * ((bx k (j0 + j + 1) - bx k (j0 + j)) * (1 / (r ^ d * lam))) :=
        mul_le_mul hgj (mul_le_mul_of_nonneg_left hfs hw) (by positivity) hG0
      calc _ ≤ (1 / 2 + (eC : ℝ) / lam0) *
            (G * ((bx k (j0 + j + 1) - bx k (j0 + j)) * (1 / (r ^ d * lam)))) :=
            mul_le_mul (by linarith) i1 (by positivity) (by
              have : (0 : ℝ) ≤ (eC : ℝ) / lam0 := by unfold eC; push_cast; positivity
              linarith)
        _ = _ := by ring
    -- term 3
    have hedge : bx k (j0 + j) ^ (1 - (d : ℝ) / 2) / Real.log (bx k (j0 + j)) ≤
        A / (r ^ d * lam) := by
      refine (edgeTerm_le hs1 hA hxj).trans ?_
      calc A ^ (1 - (d : ℝ) / 2) / Real.log A ≤ (A / r ^ d) / lam :=
            div_le_div₀ (by positivity) hR2 hlam hlamA
        _ = A / (r ^ d * lam) := by rw [div_div]
    have t3 : errK k * (2 * (cellG a (bx k) (bnc k) (j0 + j) *
        (bx k (j0 + j) ^ (1 - (d : ℝ) / 2) / Real.log (bx k (j0 + j))))) ≤
        (eC : ℝ) / lam0 * 2 * G * A / (r ^ d * lam) := by
      have hE0 : 0 ≤ bx k (j0 + j) ^ (1 - (d : ℝ) / 2) / Real.log (bx k (j0 + j)) := by
        have := Real.log_pos (one_lt_bx k (j0 + j))
        positivity
      have i1 : cellG a (bx k) (bnc k) (j0 + j) *
          (bx k (j0 + j) ^ (1 - (d : ℝ) / 2) / Real.log (bx k (j0 + j))) ≤
          G * (A / (r ^ d * lam)) := mul_le_mul hgj hedge hE0 hG0
      calc _ ≤ (eC : ℝ) / lam0 * (2 * (G * (A / (r ^ d * lam)))) :=
            mul_le_mul he (by linarith) (by positivity) (by unfold eC; push_cast; positivity)
        _ = _ := by ring
    unfold cellF
    linarith
  calc ∑ j ∈ range len, cellF a d k (j0 + j) ≤ ∑ j ∈ range len,
        (P / r ^ d + (1 / 2 + (eC : ℝ) / lam0) * G * (bx k (j0 + j + 1) - bx k (j0 + j)) /
          (r ^ d * lam) + (eC : ℝ) / lam0 * 2 * G * A / (r ^ d * lam)) :=
        sum_le_sum fun j hj => hcell j (mem_range.mp hj)
    _ = len * P / r ^ d + (1 / 2 + (eC : ℝ) / lam0) * G * (bx k (j0 + len) - bx k j0) /
        (r ^ d * lam) + (eC : ℝ) / lam0 * 2 * len * G * A / (r ^ d * lam) := by
      rw [sum_add_distrib, sum_add_distrib, sum_const, sum_const, card_range]
      have ht : ∑ j ∈ range len, (1 / 2 + (eC : ℝ) / lam0) * G *
          (bx k (j0 + j + 1) - bx k (j0 + j)) / (r ^ d * lam) =
          (1 / 2 + (eC : ℝ) / lam0) * G * (bx k (j0 + len) - bx k j0) / (r ^ d * lam) := by
        rw [← sum_div, ← mul_sum]
        congr 2
        have := sum_range_sub (fun i => bx k (j0 + i)) len
        simp only [Nat.add_zero] at this
        rw [← this]
        exact sum_congr rfl fun i _ => by rw [Nat.add_assoc]
      rw [ht, nsmul_eq_mul, nsmul_eq_mul]
      ring

end Sarkozy.HsumProof

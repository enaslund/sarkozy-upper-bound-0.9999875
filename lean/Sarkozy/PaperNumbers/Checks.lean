module

public import Sarkozy.PaperNumbers.Cell

@[expose] public section




namespace Sarkozy.PaperNumbers

open Sarkozy.PartV

/-- A list of naturals increases strictly. -/
def StrictlyIncreasing : List ℕ → Bool
  | a :: b :: l => decide (a < b) && StrictlyIncreasing (b :: l)
  | _ => true

/-- **The bin endpoints increase strictly.** -/
theorem binEnds_chain : StrictlyIncreasing binEnds = true := by decide +kernel

/-- **The threshold points increase strictly.** -/
theorem thresholdData_chain : StrictlyIncreasing (thresholdData.map Prod.fst) = true := by
  decide +kernel

/-- **Each threshold point is the least even integer `c` with `c^d ≥ 2^e`** (`(e, d) = (0, 0)`
marks `X_Ch`). -/
theorem thresholdData_spec : thresholdData.all (fun t =>
    (t.2.2 = 0 && t.1 == XCh) ||
      (t.1 % 2 == 0 && decide (2 ^ t.2.1 ≤ t.1 ^ t.2.2) &&
        decide ((t.1 - 2) ^ t.2.2 < 2 ^ t.2.1))) = true := by decide +kernel

/-- **The root data are the paper's**: `c_97, …, c_128` (fourth roots of `2^j`) and the three
points `c'_1, c'_2, c'_3` (`2^{195/8}`, `2^{123/5}`, `2^{197/8}`), and `X_Ch`. -/
theorem thresholdData_exponents :
    (thresholdData.filter (fun t => t.2.2 == 4)).map (fun t => t.2.1) = List.range' 97 32 ∧
      (thresholdData.filter (fun t => t.2.2 != 4)).map (fun t => t.2) =
        [(195, 8), (123, 5), (197, 8), (0, 0)] := by decide +kernel

/-- **Every piece endpoint below `X_Ch` is a threshold point**, so every part lies in one piece. -/
theorem pieceEnds_thresholds :
    (pieceEnds.filter (· < XCh)).all (· ∈ thresholdData.map Prod.fst) = true := by decide +kernel

/-- `⌈128 log₂(Y/x)⌉ = 𝗇` from the integer inequalities
`2^{𝗇-1} x^{128} < Y^{128} ≤ 2^𝗇 x^{128}`. -/
theorem cellCount_eq {x Y N : ℕ} (hx : 0 < x) (hN : 1 ≤ N)
    (h1 : 2 ^ (N - 1) * x ^ 128 < Y ^ 128) (h2 : Y ^ 128 ≤ 2 ^ N * x ^ 128) :
    cellCount (x : ℝ) (Y : ℝ) = N := by
  have hY : 0 < Y := by
    rcases Nat.eq_zero_or_pos Y with h | h
    · subst h
      simp at h1
    · exact h
  have hx' : (0 : ℝ) < x := by exact_mod_cast hx
  have hY' : (0 : ℝ) < Y := by exact_mod_cast hY
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpow : ∀ M : ℕ, (Real.log 2) * (M : ℝ) = Real.log ((2 : ℝ) ^ M) := fun M => by
    rw [Real.log_pow]
    ring
  have hlog : 128 * Real.logb 2 ((Y : ℝ) / x) * Real.log 2 = Real.log (((Y : ℝ) / x) ^ 128) := by
    rw [Real.log_pow, Real.logb]
    field_simp
    push_cast
    ring
  have hq : ((Y : ℝ) / x) ^ 128 = (Y : ℝ) ^ 128 / (x : ℝ) ^ 128 := div_pow _ _ _
  have hx128 : (0 : ℝ) < (x : ℝ) ^ 128 := by positivity
  unfold cellCount
  rw [Nat.ceil_eq_iff (by omega)]
  constructor
  · rw [← mul_lt_mul_iff_of_pos_right hl2, hlog, mul_comm, hpow,
      Real.log_lt_log_iff (by positivity) (by positivity), hq, lt_div_iff₀ hx128]
    have : ((2 ^ (N - 1) * x ^ 128 : ℕ) : ℝ) < ((Y ^ 128 : ℕ) : ℝ) := by exact_mod_cast h1
    push_cast at this
    exact this
  · rw [← mul_le_mul_iff_of_pos_right hl2, hlog, mul_comm (N : ℝ), hpow,
      Real.log_le_log_iff (by positivity) (by positivity), hq, div_le_iff₀ hx128]
    have : ((Y ^ 128 : ℕ) : ℝ) ≤ ((2 ^ N * x ^ 128 : ℕ) : ℝ) := by exact_mod_cast h2
    push_cast at this
    exact this

/-- **`[X_Ch, 2³⁴)` has `𝗇 = 236` cells** (`def:record:exact-blocks`(d)). -/
theorem cellCount_28 :
    cellCount (max (pieceStart 28 : ℝ) XCh) (pieceStop 28 : ℝ) = 236 := by
  have h1 : max (pieceStart 28 : ℝ) XCh = (XCh : ℝ) := by
    apply max_eq_right
    have : pieceStart 28 ≤ XCh := by decide +kernel
    exact_mod_cast this
  have h2 : pieceStop 28 = 2 ^ 34 := by decide +kernel
  rw [h1, h2]
  exact_mod_cast cellCount_eq (by norm_num [XCh]) (by norm_num)
    (by decide +kernel) (by decide +kernel)

/-- **`[2³⁴, 2³⁶)` has `𝗇 = 256` cells.** -/
theorem cellCount_29 :
    cellCount (max (pieceStart 29 : ℝ) XCh) (pieceStop 29 : ℝ) = 256 := by
  have h0 : pieceStart 29 = 2 ^ 34 := by decide +kernel
  have h1 : max (pieceStart 29 : ℝ) XCh = ((2 ^ 34 : ℕ) : ℝ) := by
    rw [h0]
    apply max_eq_left
    norm_num [XCh]
  have h2 : pieceStop 29 = 2 ^ 36 := by decide +kernel
  rw [h1, h2]
  exact cellCount_eq (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **`[2³⁶, 2⁴⁰)` has `𝗇 = 512` cells.** -/
theorem cellCount_30 :
    cellCount (max (pieceStart 30 : ℝ) XCh) (pieceStop 30 : ℝ) = 512 := by
  have h0 : pieceStart 30 = 2 ^ 36 := by decide +kernel
  have h1 : max (pieceStart 30 : ℝ) XCh = ((2 ^ 36 : ℕ) : ℝ) := by
    rw [h0]
    apply max_eq_left
    norm_num [XCh]
  have h2 : pieceStop 30 = 2 ^ 40 := by decide +kernel
  rw [h1, h2]
  exact cellCount_eq (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **`[2⁴⁰, 2⁴⁵)` has `𝗇 = 640` cells.** -/
theorem cellCount_31 :
    cellCount (max (pieceStart 31 : ℝ) XCh) (pieceStop 31 : ℝ) = 640 := by
  have h0 : pieceStart 31 = 2 ^ 40 := by decide +kernel
  have h1 : max (pieceStart 31 : ℝ) XCh = ((2 ^ 40 : ℕ) : ℝ) := by
    rw [h0]
    apply max_eq_left
    norm_num [XCh]
  have h2 : pieceStop 31 = 2 ^ 45 := by decide +kernel
  rw [h1, h2]
  exact cellCount_eq (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

/-- **`[2⁴⁵, P₃)` has `𝗇 = 306` cells.** -/
theorem cellCount_32 :
    cellCount (max (pieceStart 32 : ℝ) XCh) (pieceStop 32 : ℝ) = 306 := by
  have h0 : pieceStart 32 = 2 ^ 45 := by decide +kernel
  have h1 : max (pieceStart 32 : ℝ) XCh = ((2 ^ 45 : ℕ) : ℝ) := by
    rw [h0]
    apply max_eq_left
    norm_num [XCh]
  have h2 : pieceStop 32 = 167 * 2 ^ 40 := by decide +kernel
  rw [h1, h2]
  exact cellCount_eq (by norm_num) (by norm_num) (by decide +kernel) (by decide +kernel)

end Sarkozy.PaperNumbers

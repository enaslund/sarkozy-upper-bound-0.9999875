module

public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Rat.Floor
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Field.Basic












@[expose] public section

open scoped BigOperators

namespace Sarkozy.Certificates

/-- The density endpoint `θ = 51/50`. -/
def clique36Theta : ℚ := 51 / 50

/-- The target norm `R = d/θ = 600/17`, `d = 36`. -/
def clique36R : ℚ := 600 / 17

theorem clique36R_eq : clique36R = 36 / clique36Theta := by
  norm_num [clique36R, clique36Theta]

/-- The band `b = 16 (i + 1) ∈ {16, 32, …, 496}` of index `i`. -/
def clique36Band (i : Fin 31) : ℕ := 16 * (i.val + 1)

/-- The integer `j` used on each band, in increasing order of `b`. -/
def clique36J : Fin 31 → ℕ :=
  ![5, 9, 12, 15, 18, 20, 23, 26, 28, 31, 33, 36, 38, 40, 43, 45,
    47, 50, 52, 54, 56, 58, 61, 63, 65, 67, 69, 71, 73, 75, 77]

/-- The edge norm `r = 1 + 1/j`. -/
def clique36r (j : ℕ) : ℚ := 1 + 1 / (j : ℚ)

/-- The balanced-class norm `s = 18 r`. -/
def clique36s (j : ℕ) : ℚ := 18 * clique36r j

/-- `κ = s/R`. -/
def clique36Kappa (j : ℕ) : ℚ := clique36s j / clique36R

/-- The class norm `v_k`: `v_0 = 36`, and `v_k = min(36, (36 - k) r)` for `k ≥ 1`. -/
def clique36V (j k : ℕ) : ℚ :=
  if k = 0 then 36 else min 36 ((36 - (k : ℚ)) * clique36r j)

/-- The weight `C(36,18)/2^36` of the balanced choice vectors (the `1/w_0` factor). -/
def clique36AnchorWeight : ℚ := (Nat.choose 36 18 : ℚ) / 2 ^ 36

/-- The weight `w_k = 2 C(36,k)/2^36` of the two complementary classes of minority count `k`. -/
def clique36W (k : ℕ) : ℚ := 2 * (Nat.choose 36 k : ℚ) / 2 ^ 36

/-- The left side of `eq:density:clique-binomial-gate` on the band `[2^b, 2^(b+16))`. -/
def clique36BinomialCharge (b j : ℕ) : ℚ :=
  (1 / clique36AnchorWeight) *
    ∑ k ∈ (Finset.range 18).filter (fun k => clique36R < clique36V j k),
      clique36W k * (72 / (clique36Kappa j * clique36V j k)) *
        (2 : ℚ) ^ ⌈2 * ((b : ℚ) + 16) * (clique36Theta - 36 / clique36V j k)⌉

/-- The floor exponents `⌊2b(1-κ)⌋`, as reported by the checker. -/
def clique36DenominatorExponent : Fin 31 → ℤ :=
  ![12, 27, 42, 58, 73, 89, 104, 120, 135, 151, 167, 182, 198, 213, 229, 245,
    260, 276, 291, 307, 323, 338, 354, 370, 385, 401, 416, 432, 448, 463, 479]

/-- The exact left sides of the binomial gate, as reported by the checker. -/
def clique36CheckerRatio : Fin 31 → ℚ :=
  ![95659840 / 13884957009, 240817 / 2057030668, 78011008 / 2868015008859,
    20 / 2313003, 27657088 / 3155999302379, 8522240 / 1652309884071,
    41863 / 10262794311, 6457984 / 2124398422377, 75776 / 19174464441,
    1184 / 149300613, 18944 / 2384285547, 201711616 / 24640656114305,
    35483648 / 4322606353065, 471695360 / 54461429708301, 187268096 / 19600930977705,
    18227200 / 1904296140901, 177472 / 15676564365, 416153600 / 28089268029207,
    4955045888 / 455033182779945, 971931648 / 54447030493625, 3670016 / 115494688485,
    618299392 / 19444525714845, 9292269568 / 155673509665905, 21209 / 367326905,
    1335393280 / 11760558586623, 554918656 / 2463970879755, 647975936 / 2875930105125,
    654331456 / 1457920485945, 18063297536 / 20160536820795, 3490403200 / 3898587373527,
    272781824 / 152373878865]

/-- The floor exponents of `eq:density:clique-denominator` agree with the checker. -/
theorem clique36_denominator_exponent_eq (i : Fin 31) :
    ⌊2 * (clique36Band i : ℚ) * (1 - clique36Kappa (clique36J i))⌋ =
      clique36DenominatorExponent i := by
  fin_cases i <;>
    norm_num [clique36Band, clique36J, clique36Kappa, clique36s, clique36r, clique36R,
      clique36DenominatorExponent]

set_option exponentiation.threshold 1024 in
/-- `eq:density:clique-denominator` on each of the `31` bands: `2^(-⌊2b(1-κ)⌋) ≤ κ/2`. -/
theorem clique36_denominator_gate (i : Fin 31) :
    (2 : ℚ) ^ (-⌊2 * (clique36Band i : ℚ) * (1 - clique36Kappa (clique36J i))⌋) ≤
      clique36Kappa (clique36J i) / 2 := by
  fin_cases i <;>
    norm_num [clique36Band, clique36J, clique36Kappa, clique36s, clique36r, clique36R]

/-- The binomial-gate left side on the band `b = 16` (`j = 5`). -/
theorem clique36_binomial_charge_b16 :
    clique36BinomialCharge 16 5 = 95659840 / 13884957009 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 32` (`j = 9`). -/
theorem clique36_binomial_charge_b32 :
    clique36BinomialCharge 32 9 = 240817 / 2057030668 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 48` (`j = 12`). -/
theorem clique36_binomial_charge_b48 :
    clique36BinomialCharge 48 12 = 78011008 / 2868015008859 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 64` (`j = 15`). -/
theorem clique36_binomial_charge_b64 :
    clique36BinomialCharge 64 15 = 20 / 2313003 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 80` (`j = 18`). -/
theorem clique36_binomial_charge_b80 :
    clique36BinomialCharge 80 18 = 27657088 / 3155999302379 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 96` (`j = 20`). -/
theorem clique36_binomial_charge_b96 :
    clique36BinomialCharge 96 20 = 8522240 / 1652309884071 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 112` (`j = 23`). -/
theorem clique36_binomial_charge_b112 :
    clique36BinomialCharge 112 23 = 41863 / 10262794311 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 128` (`j = 26`). -/
theorem clique36_binomial_charge_b128 :
    clique36BinomialCharge 128 26 = 6457984 / 2124398422377 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 144` (`j = 28`). -/
theorem clique36_binomial_charge_b144 :
    clique36BinomialCharge 144 28 = 75776 / 19174464441 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 160` (`j = 31`). -/
theorem clique36_binomial_charge_b160 :
    clique36BinomialCharge 160 31 = 1184 / 149300613 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 176` (`j = 33`). -/
theorem clique36_binomial_charge_b176 :
    clique36BinomialCharge 176 33 = 18944 / 2384285547 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 192` (`j = 36`). -/
theorem clique36_binomial_charge_b192 :
    clique36BinomialCharge 192 36 = 201711616 / 24640656114305 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 208` (`j = 38`). -/
theorem clique36_binomial_charge_b208 :
    clique36BinomialCharge 208 38 = 35483648 / 4322606353065 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 224` (`j = 40`). -/
theorem clique36_binomial_charge_b224 :
    clique36BinomialCharge 224 40 = 471695360 / 54461429708301 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 240` (`j = 43`). -/
theorem clique36_binomial_charge_b240 :
    clique36BinomialCharge 240 43 = 187268096 / 19600930977705 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 256` (`j = 45`). -/
theorem clique36_binomial_charge_b256 :
    clique36BinomialCharge 256 45 = 18227200 / 1904296140901 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 272` (`j = 47`). -/
theorem clique36_binomial_charge_b272 :
    clique36BinomialCharge 272 47 = 177472 / 15676564365 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 288` (`j = 50`). -/
theorem clique36_binomial_charge_b288 :
    clique36BinomialCharge 288 50 = 416153600 / 28089268029207 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 304` (`j = 52`). -/
theorem clique36_binomial_charge_b304 :
    clique36BinomialCharge 304 52 = 4955045888 / 455033182779945 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 320` (`j = 54`). -/
theorem clique36_binomial_charge_b320 :
    clique36BinomialCharge 320 54 = 971931648 / 54447030493625 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 336` (`j = 56`). -/
theorem clique36_binomial_charge_b336 :
    clique36BinomialCharge 336 56 = 3670016 / 115494688485 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 352` (`j = 58`). -/
theorem clique36_binomial_charge_b352 :
    clique36BinomialCharge 352 58 = 618299392 / 19444525714845 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 368` (`j = 61`). -/
theorem clique36_binomial_charge_b368 :
    clique36BinomialCharge 368 61 = 9292269568 / 155673509665905 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 384` (`j = 63`). -/
theorem clique36_binomial_charge_b384 :
    clique36BinomialCharge 384 63 = 21209 / 367326905 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 400` (`j = 65`). -/
theorem clique36_binomial_charge_b400 :
    clique36BinomialCharge 400 65 = 1335393280 / 11760558586623 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 416` (`j = 67`). -/
theorem clique36_binomial_charge_b416 :
    clique36BinomialCharge 416 67 = 554918656 / 2463970879755 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 432` (`j = 69`). -/
theorem clique36_binomial_charge_b432 :
    clique36BinomialCharge 432 69 = 647975936 / 2875930105125 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 448` (`j = 71`). -/
theorem clique36_binomial_charge_b448 :
    clique36BinomialCharge 448 71 = 654331456 / 1457920485945 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 464` (`j = 73`). -/
theorem clique36_binomial_charge_b464 :
    clique36BinomialCharge 464 73 = 18063297536 / 20160536820795 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 480` (`j = 75`). -/
theorem clique36_binomial_charge_b480 :
    clique36BinomialCharge 480 75 = 3490403200 / 3898587373527 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The binomial-gate left side on the band `b = 496` (`j = 77`). -/
theorem clique36_binomial_charge_b496 :
    clique36BinomialCharge 496 77 = 272781824 / 152373878865 := by
  unfold clique36BinomialCharge
  rw [Finset.sum_filter]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero]
  norm_num [clique36Kappa, clique36s, clique36r, clique36R, clique36V, clique36W,
    clique36AnchorWeight, clique36Theta, min_def, Nat.choose]

/-- The left side of `eq:density:clique-binomial-gate` agrees with the checker on each band. -/
theorem clique36_binomial_charge_eq (i : Fin 31) :
    clique36BinomialCharge (clique36Band i) (clique36J i) = clique36CheckerRatio i := by
  fin_cases i
  · exact clique36_binomial_charge_b16
  · exact clique36_binomial_charge_b32
  · exact clique36_binomial_charge_b48
  · exact clique36_binomial_charge_b64
  · exact clique36_binomial_charge_b80
  · exact clique36_binomial_charge_b96
  · exact clique36_binomial_charge_b112
  · exact clique36_binomial_charge_b128
  · exact clique36_binomial_charge_b144
  · exact clique36_binomial_charge_b160
  · exact clique36_binomial_charge_b176
  · exact clique36_binomial_charge_b192
  · exact clique36_binomial_charge_b208
  · exact clique36_binomial_charge_b224
  · exact clique36_binomial_charge_b240
  · exact clique36_binomial_charge_b256
  · exact clique36_binomial_charge_b272
  · exact clique36_binomial_charge_b288
  · exact clique36_binomial_charge_b304
  · exact clique36_binomial_charge_b320
  · exact clique36_binomial_charge_b336
  · exact clique36_binomial_charge_b352
  · exact clique36_binomial_charge_b368
  · exact clique36_binomial_charge_b384
  · exact clique36_binomial_charge_b400
  · exact clique36_binomial_charge_b416
  · exact clique36_binomial_charge_b432
  · exact clique36_binomial_charge_b448
  · exact clique36_binomial_charge_b464
  · exact clique36_binomial_charge_b480
  · exact clique36_binomial_charge_b496

/-- `eq:density:clique-binomial-gate` on each of the `31` bands. -/
theorem clique36_binomial_gate (i : Fin 31) :
    clique36BinomialCharge (clique36Band i) (clique36J i) ≤ 95659840 / 13884957009 := by
  rw [clique36_binomial_charge_eq]
  fin_cases i <;> norm_num [clique36CheckerRatio]

/-- The bound of `eq:density:clique-binomial-gate` is below `1`. -/
theorem clique36_binomial_gate_lt_one : (95659840 : ℚ) / 13884957009 < 1 := by
  norm_num

/-- The bound of `eq:density:clique-binomial-gate` is attained at `b = 16`. -/
theorem clique36_binomial_gate_attained :
    clique36BinomialCharge (clique36Band 0) (clique36J 0) = 95659840 / 13884957009 :=
  clique36_binomial_charge_eq 0

end Sarkozy.Certificates

module

public import Sarkozy.PartVLaws.PadicPrice

@[expose] public section





namespace Sarkozy.IndexCert

open Finset

/-! ## Trial division -/

/-- Trial division of `p` by `d, d + 2, d + 4, …` while the square of the divisor is at most
`p`; with the fuel exhausted it reports whether `p < d²`. -/
def noDiv2 (p : ℕ) : ℕ → ℕ → Bool
  | 0, d => decide (p < d * d)
  | f + 1, d => if p < d * d then true else if p % d = 0 then false else noDiv2 p f (d + 2)

theorem noDiv2_iff (p : ℕ) : ∀ (f d : ℕ), p < (d + 2 * f) * (d + 2 * f) →
    (noDiv2 p f d = true ↔ ∀ m, d ≤ m → (m - d) % 2 = 0 → m * m ≤ p → ¬ m ∣ p) := by
  intro f
  induction f with
  | zero =>
    intro d hd
    simp only [noDiv2, decide_eq_true_eq]
    constructor
    · intro h m hm _ hmm
      exfalso
      have : d * d ≤ m * m := Nat.mul_le_mul hm hm
      omega
    · intro _
      simpa using hd
  | succ f ih =>
    intro d hd
    by_cases h1 : p < d * d
    · simp only [noDiv2, h1, ↓reduceIte, true_iff]
      intro m hm _ hmm
      have : d * d ≤ m * m := Nat.mul_le_mul hm hm
      omega
    · by_cases h2 : p % d = 0
      · simp only [noDiv2, h1, h2, ↓reduceIte, Bool.false_eq_true, false_iff]
        intro h
        exact h d le_rfl (by simp) (by omega) (Nat.dvd_of_mod_eq_zero h2)
      · simp only [noDiv2, h1, h2, ↓reduceIte]
        have e : d + 2 + 2 * f = d + 2 * (f + 1) := by ring
        rw [ih (d + 2) (by rw [e]; exact hd)]
        constructor
        · intro h m hm hpar hmm
          rcases Nat.eq_or_lt_of_le hm with rfl | hlt
          · intro hdvd
            exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
          · exact h m (by omega) (by omega) hmm
        · intro h m hm hpar hmm
          exact h m (by omega) (by omega) hmm

theorem odd_of_dvd_odd {m p : ℕ} (hp : p % 2 = 1) (h : m ∣ p) : m % 2 = 1 := by
  obtain ⟨k, rfl⟩ := h
  rcases Nat.mod_two_eq_zero_or_one m with hm | hm
  · exfalso
    have : m * k % 2 = m % 2 * (k % 2) % 2 := Nat.mul_mod _ _ _
    rw [hm, zero_mul, Nat.zero_mod] at this
    omega
  · exact hm

/-- **Trial division decides primality** of odd `p ≥ 3`. -/
theorem noDiv2_prime_iff {p : ℕ} (hodd : p % 2 = 1) (h3 : 3 ≤ p) :
    noDiv2 p p 3 = true ↔ p.Prime := by
  rw [noDiv2_iff p p 3 (by nlinarith), Nat.prime_def_le_sqrt]
  constructor
  · intro h
    refine ⟨by omega, fun m hm2 hms hdvd => ?_⟩
    have hmm : m * m ≤ p := Nat.le_sqrt.mp hms
    have hmo := odd_of_dvd_odd hodd hdvd
    exact h m (by omega) (by omega) hmm hdvd
  · rintro ⟨_, h⟩ m hm _ hmm hdvd
    exact h m (by omega) (Nat.le_sqrt.mpr hmm) hdvd

/-! ## Sums over the primes `p ≡ 3 (mod 4)` -/

/-- `∑_{p < 4J, p prime, p ≡ 3 (mod 4)} f p`, by trial division of `4j + 3`, `j < J`. -/
def smallSum (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => smallSum f j + if noDiv2 (4 * j + 3) (4 * j + 3) 3 then f (4 * j + 3) else 0

theorem sum_indexPrimes_succ {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ p ∈ PartVLaws.indexPrimes (n + 1), f p =
      ∑ p ∈ PartVLaws.indexPrimes n, f p + if n.Prime ∧ n % 4 = 3 then f n else 0 := by
  unfold PartVLaws.indexPrimes
  rw [range_add_one, filter_insert]
  split_ifs with h
  · rw [sum_insert (by simp), add_comm]
  · rw [add_zero]

theorem sum_indexPrimes_succ_of {M : Type*} [AddCommMonoid M] (f : ℕ → M) {n : ℕ}
    (h : n % 4 ≠ 3) :
    ∑ p ∈ PartVLaws.indexPrimes (n + 1), f p = ∑ p ∈ PartVLaws.indexPrimes n, f p := by
  rw [sum_indexPrimes_succ]
  simp [h]

/-- **The kernel sum is the sum over `indexPrimes (4J)`.** -/
theorem sum_indexPrimes_eq (f : ℕ → ℕ) (J : ℕ) :
    ∑ p ∈ PartVLaws.indexPrimes (4 * J), f p = smallSum f J := by
  induction J with
  | zero => simp [PartVLaws.indexPrimes, smallSum]
  | succ J ih =>
    rw [show 4 * (J + 1) = 4 * J + 3 + 1 by ring, sum_indexPrimes_succ,
      sum_indexPrimes_succ_of f (n := 4 * J + 2) (by omega),
      sum_indexPrimes_succ_of f (n := 4 * J + 1) (by omega),
      sum_indexPrimes_succ_of f (n := 4 * J) (by omega), ih, smallSum]
    congr 1
    have hiff := noDiv2_prime_iff (p := 4 * J + 3) (by omega) (by omega)
    by_cases hp : (4 * J + 3).Prime
    · have h1 : (4 * J + 3).Prime ∧ (4 * J + 3) % 4 = 3 := ⟨hp, by omega⟩
      simp only [h1, hiff.mpr hp, and_self, ↓reduceIte]
    · have h1 : ¬ ((4 * J + 3).Prime ∧ (4 * J + 3) % 4 = 3) := fun h => hp h.1
      have h2 : ¬ (noDiv2 (4 * J + 3) (4 * J + 3) 3 = true) := fun h => hp (hiff.mp h)
      simp only [h1, h2, Bool.false_eq_true, ↓reduceIte]

/-! ## Rounding and bit lengths -/

/-- `⌈a / b⌉`. -/
def ceilDiv (a b : ℕ) : ℕ := (a + b - 1) / b

theorem le_ceilDiv_mul (a b : ℕ) (hb : 0 < b) : a ≤ ceilDiv a b * b := by
  unfold ceilDiv
  have h := Nat.lt_mul_div_succ (a + b - 1) hb
  rw [Nat.mul_add, Nat.mul_one, Nat.mul_comm] at h
  generalize (a + b - 1) / b * b = t at h ⊢
  omega

/-- The power of the bit-length bound for logarithms. -/
def kL : ℕ := 256

/-- `⌊log₂ p^{256}⌋`, computed from `⌊log₂ p⌋` and the bit length of `(p/2^{⌊log₂ p⌋})^{256}`. -/
def nB (p : ℕ) : ℕ := kL * Nat.log2 p + Nat.log2 (p ^ kL / 2 ^ (kL * Nat.log2 p))

theorem nB_spec {p : ℕ} (hp : p ≠ 0) : 2 ^ nB p ≤ p ^ kL ∧ p ^ kL < 2 ^ (nB p + 1) := by
  set j := Nat.log2 p
  set s := kL * j
  have hj : 2 ^ j ≤ p := Nat.log2_self_le hp
  have hs : 2 ^ s ≤ p ^ kL := by
    rw [show s = j * kL by ring, pow_mul]
    exact Nat.pow_le_pow_left hj kL
  have hs0 : 0 < 2 ^ s := by positivity
  set u := p ^ kL / 2 ^ s
  have hu : u ≠ 0 := by
    have : 1 ≤ u := (Nat.le_div_iff_mul_le hs0).mpr (by simpa using hs)
    omega
  have hu1 : 2 ^ Nat.log2 u ≤ u := Nat.log2_self_le hu
  have hu2 : u < 2 ^ (Nat.log2 u + 1) := Nat.lt_log2_self
  have hnB : nB p = s + Nat.log2 u := rfl
  constructor
  · rw [hnB, pow_add]
    calc 2 ^ s * 2 ^ Nat.log2 u ≤ 2 ^ s * u := Nat.mul_le_mul_left _ hu1
      _ = u * 2 ^ s := Nat.mul_comm _ _
      _ ≤ p ^ kL := Nat.div_mul_le_self _ _
  · rw [hnB, show s + Nat.log2 u + 1 = s + (Nat.log2 u + 1) by ring, pow_add]
    calc p ^ kL < 2 ^ s * (u + 1) := Nat.lt_mul_div_succ _ hs0
      _ ≤ 2 ^ s * 2 ^ (Nat.log2 u + 1) := Nat.mul_le_mul_left _ hu2

/-! ## The small-prime terms -/

/-- The scale of the square-root approximations. -/
def DS : ℕ := 2 ^ 20

/-- The fixed-point scale. -/
def FP : ℕ := 2 ^ 64

/-- `Ẑ = Zn/Zd = 1.000857`, an upper bound for `p^{a₀/18}` below `2^{25}`. -/
def Zn : ℕ := 1000857

/-- See `Zn`. -/
def Zd : ℕ := 1000000

/-- Newton's iteration for the integer square root (only its accuracy matters, not its
correctness: the bound `√p ≤ (p + q²)/(2q)` holds for every `q > 0`). -/
def newton (n : ℕ) : ℕ → ℕ → ℕ
  | 0, x => x
  | f + 1, x => newton n f ((x + n / x) / 2)

/-- An approximation of `√n`. -/
def isq (n : ℕ) : ℕ := newton n 14 (2 ^ (Nat.log2 n / 2 + 1))

/-- A positive approximation of `2^{20} √p`. -/
def rS (p : ℕ) : ℕ := max 1 (isq (p * DS * DS))

theorem rS_pos (p : ℕ) : 0 < rS p := lt_of_lt_of_le one_pos (le_max_left _ _)

/-- **The rounded-up small-prime term**: `tS p ≥ 2^{64}(nB p + 1)·(p D² + r²)/(2rD)/(p − Ẑ)`
with `D = 2^{20}`, `r = rS p`; so that `log p · √p/(p − Ẑ) ≤ (log 2)/256 · tS p / 2^{64}`. -/
def tS (p : ℕ) : ℕ :=
  ceilDiv ((nB p + 1) * (p * DS * DS + rS p * rS p) * Zd * FP) (2 * rS p * DS * (p * Zd - Zn))

/-! ## The Abel weights -/

/-- **The Abel weight** `gW s = ⌈2^{64} s/(s² − Ẑ)⌉`, for the primes in `[s², (s+1)²)`. -/
def gW (s : ℕ) : ℕ := ceilDiv (s * FP * Zd) (s * s * Zd - Zn)

/-! ## Chunked sums (the kernel's recursion depth stays below `120`) -/

/-- `∑_{j < k} f (i₀ + j)`. -/
def bsum (f : ℕ → ℕ) (i₀ : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => bsum f i₀ k + f (i₀ + k)

theorem bsum_eq (f : ℕ → ℕ) (i₀ k : ℕ) : bsum f i₀ k = ∑ j ∈ range k, f (i₀ + j) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [bsum, ih, sum_range_succ]

/-- `∑_{i < kB} f i`, in `B` blocks of `k`. -/
def csum (f : ℕ → ℕ) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | B + 1 => csum f k B + bsum f (k * B) k

theorem csum_eq (f : ℕ → ℕ) (k B : ℕ) : csum f k B = ∑ i ∈ range (k * B), f i := by
  induction B with
  | zero => simp [csum]
  | succ B ih => rw [csum, ih, bsum_eq, show k * (B + 1) = k * B + k by ring, sum_range_add]

/-- `∑_{i < 4338} f i`, in `67` blocks of `64` and a block of `50`. -/
def gridSum (f : ℕ → ℕ) : ℕ := csum f 64 67 + bsum f 4288 50

theorem gridSum_eq (f : ℕ → ℕ) : gridSum f = ∑ i ∈ range 4338, f i := by
  rw [gridSum, csum_eq, bsum_eq, show 4338 = 64 * 67 + 50 by norm_num, sum_range_add]

/-- The violations of the antitonicity of `gW` on `[128, 4466]`. -/
def viol (i : ℕ) : ℕ := if gW (129 + i) ≤ gW (128 + i) then 0 else 1

/-- The Abel terms `(gW(128 + i) − gW(129 + i)) · w(129 + i)`. -/
def abelTerm (w : ℕ → ℕ) (i : ℕ) : ℕ := (gW (128 + i) - gW (129 + i)) * w (129 + i)

theorem gW_anti_of (h : gridSum viol = 0) : ∀ i < 4338, gW (129 + i) ≤ gW (128 + i) := by
  rw [gridSum_eq, sum_eq_zero_iff] at h
  intro i hi
  have := h i (mem_range.mpr hi)
  unfold viol at this
  split_ifs at this with h'
  · exact h'

/-! ## The kernel-checked values -/

/-- The sum of the small-prime terms over the `958` primes `p ≡ 3 (mod 4)` below `2^{14}`. -/
theorem smallT_eq : smallSum tS 4096 = 861202739404713745892444 := by decide +kernel

/-- The sum of `⌊log₂ p^{256}⌋` over the primes `p ≡ 3 (mod 4)` below `2^{14}`. -/
theorem smallN_eq : smallSum nB 4096 = 3024061 := by decide +kernel

/-- `gW` is antitone on `[128, 4466]`. -/
theorem viol_eq : gridSum viol = 0 := by decide +kernel

theorem abel2_eq : gridSum (abelTerm fun s => s * s) = 80087994762344705953805 := by
  decide +kernel

theorem abel1_eq : gridSum (abelTerm fun s => s) = 65598638960976287003 := by decide +kernel

theorem gW_128 : gW 128 = 144123992244954158 := by decide +kernel

theorem gW_4466 : gW 4466 = 4130484773707033 := by decide +kernel

end Sarkozy.IndexCert

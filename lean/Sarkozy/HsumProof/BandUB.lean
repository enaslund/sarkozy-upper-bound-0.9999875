module

public import Sarkozy.HsumProof.NumBounds
public import Sarkozy.HsumProof.UpperData
public import Sarkozy.PaperNumbers.Budget

@[expose] public section

/-!
# A rational upper bound of `bandBound a d k` on all 310 bands (HS)

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(i), `eq:record:cell-charge`;
`def:record:upper-bands`(b). For a rational decay `a ≥ 0` and `d ≥ 2`, `bandBound a d k ≤ UBQ a k d`
(`bandBound_le_UBQ`), with `UBQ` an explicit rational, under a Boolean side condition `bandOK a k`
that the kernel checks (`HsumProof/Upper.lean`, `decide +kernel`). The side data come from the
untrusted generator (`UpperData`); nothing in them is assumed.

* **Near bands** (`k < 301`, two cells; `nearUB`): one group, `A = X`, `n_j ≥ m` from
  `Y^m ≤ eLo^L` and `n_j = ⌊L/log x_{j+1}⌋`, `Π_j ≤ e^{2aL}` from `n_j log x_{j+1} ≤ L`.
* **Far bands** (`k ≥ 301`, `[2^b, 2^{b'})`, `128 (b' - b)` cells; `farUB`): one group per octave
  `[2^{b+i}, 2^{b+i+1})` (128 cells), `n_j ≥ nlo_i` from the runs meeting the octave (the runs cover
  all cells: `covers`), `Π_j ≤ exp(2a Lmax/128 · log2hi)` from `n (128 b + last + 1) ≤ Lmax` on
  every run.

The bound loses about 2% against E2's floating-point `bandBound` on the near bands and a factor
about 1.7 on the far bands (which carry 2% of the upper part).
-/

open Finset

namespace Sarkozy.HsumProof

open Sarkozy.NumericalFields Sarkozy.Misc Sarkozy.PartV Sarkozy.PaperNumbers

/-- The budget `L` of band `k`. -/
def bandL (k : Fin 310) : ℕ := (UpperRecords.CompletionData.record k).budget

/-! ## Near bands -/

/-- The generator's near-band data `(pX, m, r)`. -/
def nearData (k : Fin 310) : ℕ × ℕ × ℕ := UpperData.nearTab.getD k.val (1, 1, 1)

/-- `λ = (pX/64) log2lo ≤ log X`. -/
def nearLam (k : Fin 310) : ℚ := ((nearData k).1 : ℚ) / 64 * log2lo

/-- `P = expUB(2 a L) ≥ e^{2aL} ≥ Π_j`. -/
def nearP (a : ℚ) (k : Fin 310) : ℚ := expUB (2 * a * (bandL k : ℚ))

/-- `G = P/m ≥ g_j`. -/
def nearG (a : ℚ) (k : Fin 310) : ℚ := nearP a k / ((nearData k).2.1 : ℚ)

/-- **The near-band bound.** -/
def nearUB (a : ℚ) (k : Fin 310) (d : ℕ) : ℚ :=
  2 * nearP a k / ((nearData k).2.2 : ℚ) ^ d +
    (1 / 2 + eC / nearLam k) * nearG a k * (((bandOf k).2 : ℚ) - (bandOf k).1) /
      (((nearData k).2.2 : ℚ) ^ d * nearLam k) +
    eC / nearLam k * 2 * 2 * nearG a k * ((bandOf k).1 : ℚ) /
      (((nearData k).2.2 : ℚ) ^ d * nearLam k)

/-- The side conditions of a near band. -/
def nearOK (a : ℚ) (k : Fin 310) : Bool :=
  decide ((bandOf k).1 < 2 ^ 52) && decide (0 < (nearData k).1) &&
    decide (2 ^ (nearData k).1 ≤ (bandOf k).1 ^ 64) && decide (1 ≤ (nearData k).2.1) &&
    decide ((bandOf k).2 ^ (nearData k).2.1 * 10 ^ (10 * bandL k) ≤ 27182818283 ^ bandL k) &&
    decide (0 < (nearData k).2.2) && decide ((nearData k).2.2 ^ 2 ≤ (bandOf k).1) &&
    decide (0 ≤ a) && decide (2 * a * (bandL k : ℚ) ≤ 2)

/-- `Y^m 10^{10L} ≤ 27182818283^L` gives `m log Y ≤ L`. -/
theorem mul_log_le_of_natPow {Y : ℕ} (m L : ℕ) (hY : 1 ≤ Y)
    (h : Y ^ m * 10 ^ (10 * L) ≤ 27182818283 ^ L) : (m : ℝ) * Real.log Y ≤ L := by
  apply mul_log_le_of_pow m L hY
  unfold eLo
  have h' : ((Y ^ m * 10 ^ (10 * L) : ℕ) : ℚ) ≤ ((27182818283 ^ L : ℕ) : ℚ) := by exact_mod_cast h
  push_cast at h'
  rw [div_pow, le_div_iff₀ (by positivity), ← pow_mul]
  exact h'

theorem near_le (a : ℚ) (k : Fin 310) (hk : k.val < 301) (hok : nearOK a k = true) {d : ℕ}
    (hd : 2 ≤ d) : bandBound a d k ≤ (nearUB a k d : ℝ) := by
  simp only [nearOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨h52, hp0⟩, hpX⟩, hm1⟩, hmY⟩, hr0⟩, hrX⟩, ha0⟩, ha2⟩ := hok
  have hnk : ¬ 301 ≤ k.val := by omega
  have hN : bandN k = 2 := by
    rw [bandN_near k hnk]
    unfold bandCells
    simp only [h52, ↓reduceIte]
  have hbnc : ∀ j, bnc k j = ⌊(bandL k : ℝ) / Real.log (bx k (j + 1))⌋₊ := by
    intro j
    simp only [bnc, bx, rule_near k hnk, bandN_near k hnk, paperBandRule, geoRule, cellCard,
      bandL]
  set X := (bandOf k).1 with hXdef
  set Y := (bandOf k).2 with hYdef
  set L := bandL k
  set pX := (nearData k).1
  set m := (nearData k).2.1
  set r := (nearData k).2.2
  have hX1 : (1 : ℝ) < X := by linarith [bandX_pos k]
  have hXpos : (0 : ℝ) < X := by linarith
  have hY1 : 1 ≤ Y := by
    have : X < Y := band_lt k
    have : 1 < X := by exact_mod_cast hX1
    omega
  have hx2 : bx k 2 = Y := by
    unfold bx
    rw [← hN]
    exact cellPoint_self (by rw [hN]; norm_num)
  have hx0 : bx k 0 = X := bx0_eq k
  have hlogY : (m : ℝ) * Real.log Y ≤ L := mul_log_le_of_natPow m L hY1 hmY
  have hlam : ((nearLam k : ℚ) : ℝ) ≤ Real.log X := by
    unfold nearLam
    exact log_ge_of_pow pX 64 (by norm_num) hpX
  have hlam0 : (0 : ℝ) < (nearLam k : ℚ) := by
    unfold nearLam
    have : (0 : ℝ) < pX := by exact_mod_cast hp0
    push_cast
    have := log2lo_pos
    positivity
  have hexp := exp_le_expUB (x := 2 * a * (L : ℚ)) (by positivity) ha2
  have hP0 : (0 : ℝ) ≤ (nearP a k : ℚ) := (Real.exp_pos _).le.trans hexp
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hG0 : (0 : ℝ) ≤ (nearG a k : ℚ) := by
    unfold nearG
    push_cast
    exact div_nonneg hP0 hm0.le
  have hr : (0 : ℝ) < r := by exact_mod_cast hr0
  have hrA : (r : ℝ) ^ 2 ≤ X := by exact_mod_cast hrX
  -- per-cell facts for `j < 2`
  have hcell : ∀ j < 2, Real.log (bx k (j + 1)) ≤ Real.log Y ∧ 0 < Real.log (bx k (j + 1)) := by
    intro j hj
    have hle : bx k (j + 1) ≤ bx k 2 := by
      interval_cases j
      · exact bx_mono k 1
      · exact le_rfl
    rw [hx2] at hle
    exact ⟨Real.log_le_log (by linarith [one_lt_bx k (j + 1)]) hle,
      Real.log_pos (one_lt_bx k (j + 1))⟩
  have hPj : ∀ j < 2, cellPi a (bx k) (bnc k) (0 + j) ≤ (nearP a k : ℚ) := by
    intro j hj
    rw [zero_add]
    obtain ⟨-, hl0⟩ := hcell j hj
    have hfl : (bnc k j : ℝ) * Real.log (bx k (j + 1)) ≤ L := by
      rw [hbnc j]
      have := Nat.floor_le (div_nonneg (Nat.cast_nonneg L) hl0.le)
      calc (⌊(L : ℝ) / Real.log (bx k (j + 1))⌋₊ : ℝ) * Real.log (bx k (j + 1)) ≤
            (L : ℝ) / Real.log (bx k (j + 1)) * Real.log (bx k (j + 1)) :=
            mul_le_mul_of_nonneg_right this hl0.le
        _ = L := by field_simp
    unfold cellPi nearP
    refine le_trans (Real.exp_le_exp.mpr ?_) (by push_cast at hexp ⊢; exact hexp)
    have ha : (0 : ℝ) ≤ a := by exact_mod_cast ha0
    nlinarith
  have hGj : ∀ j < 2, cellG a (bx k) (bnc k) (0 + j) ≤ (nearG a k : ℚ) := by
    intro j hj
    have hp := hPj j hj
    rw [zero_add] at hp ⊢
    obtain ⟨hlY, hl0⟩ := hcell j hj
    have hmn : m ≤ bnc k j := by
      rw [hbnc j]
      apply Nat.le_floor
      rw [le_div_iff₀ hl0]
      nlinarith
    have hmn' : (m : ℝ) ≤ bnc k j := by exact_mod_cast hmn
    unfold cellG nearG
    push_cast
    exact div_le_div₀ hP0 hp hm0 hmn'
  have hxj : ∀ j < 2, (X : ℝ) ≤ bx k (0 + j) := fun j _ => by
    rw [← hx0]; exact bx_ge k _
  have hg := group_le k a hd 0 2 hX1 hr hrA hlam0 hlam hlam0 (by rw [hx0]; exact hlam) hxj hPj
    hGj hP0 hG0
  have hb := bandBound_le_cells k a hd
  rw [hN] at hb
  simp only [zero_add] at hg
  rw [hx2, hx0] at hg
  refine hb.trans (hg.trans (le_of_eq ?_))
  unfold nearUB
  push_cast
  ring

/-! ## Far bands -/

/-- The runs of a far band cover the cells `s, …, N - 1` (consecutive runs from `s`). -/
def covers : ℕ → List (ℕ × ℕ × ℕ) → ℕ → Bool
  | s, [], N => decide (N ≤ s)
  | s, r :: rs, N => decide (r.1 ≤ s) && covers (r.2.1 + 1) rs N

theorem covers_spec : ∀ (runs : List (ℕ × ℕ × ℕ)) (s N : ℕ), covers s runs N = true →
    ∀ j, s ≤ j → j < N → ∃ r ∈ runs, r.1 ≤ j ∧ j ≤ r.2.1
  | [], s, N, h, j, hs, hj => by
    simp only [covers, decide_eq_true_eq] at h
    omega
  | r :: rs, s, N, h, j, hs, hj => by
    simp only [covers, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hjr : j ≤ r.2.1
    · exact ⟨r, List.mem_cons_self, by omega, hjr⟩
    · obtain ⟨r', hr', h1, h2⟩ := covers_spec rs (r.2.1 + 1) N h.2 j (by omega) hj
      exact ⟨r', List.mem_cons_of_mem _ hr', h1, h2⟩

/-- The generator's far-band data `(Lmax, nlo)` of band `k ≥ 301`. -/
def farData (k : Fin 310) : ℕ × List ℕ := UpperData.farTab.getD (k.val - 301) (0, [])

/-- The least `n_j` on octave `i`. -/
def farNlo (k : Fin 310) (i : ℕ) : ℕ := (farData k).2.getD i 1

/-- `b`, `b'` and the runs of a far band. -/
def farB (k : Fin 310) : ℕ := (farBand (farIdx k)).1

def farB' (k : Fin 310) : ℕ := (farBand (farIdx k)).2.1

def farRuns (k : Fin 310) : List (ℕ × ℕ × ℕ) := (farBand (farIdx k)).2.2

/-- `P = expUB(2 a (Lmax/128) log2hi)`. -/
def farP (a : ℚ) (k : Fin 310) : ℚ := expUB (2 * a * (((farData k).1 : ℚ) / 128 * log2hi))

/-- `r_e² ≤ 2^e`: `2^{e/2}`, times `1.414213` for odd `e`. -/
def octR (e : ℕ) : ℚ := if e % 2 = 0 then 2 ^ (e / 2) else 2 ^ (e / 2) * (1414213 / 1000000)

theorem octR_pos (e : ℕ) : 0 < octR e := by
  unfold octR
  split_ifs <;> positivity

theorem octR_sq (e : ℕ) : octR e ^ 2 ≤ 2 ^ e := by
  unfold octR
  split_ifs with h
  · rw [← pow_mul]
    exact le_of_eq (by congr 1; omega)
  · rw [mul_pow, ← pow_mul]
    have he : e = e / 2 * 2 + 1 := by omega
    calc (2 : ℚ) ^ (e / 2 * 2) * (1414213 / 1000000) ^ 2 ≤ 2 ^ (e / 2 * 2) * 2 :=
          mul_le_mul_of_nonneg_left (by norm_num) (by positivity)
      _ = 2 ^ e := by rw [he, pow_succ]; congr 2; omega

/-- The term of octave `i` of a far band. -/
def octTerm (a : ℚ) (k : Fin 310) (d i : ℕ) : ℚ :=
  128 * farP a k / octR (farB k + i) ^ d +
    (1 / 2 + eC / ((farB k : ℚ) * log2lo)) * (farP a k / (farNlo k i : ℚ)) *
      (2 : ℚ) ^ (farB k + i) / (octR (farB k + i) ^ d * (((farB k + i : ℕ) : ℚ) * log2lo)) +
    eC / ((farB k : ℚ) * log2lo) * 2 * 128 * (farP a k / (farNlo k i : ℚ)) *
      (2 : ℚ) ^ (farB k + i) / (octR (farB k + i) ^ d * (((farB k + i : ℕ) : ℚ) * log2lo))

/-- **The far-band bound.** -/
def farUB (a : ℚ) (k : Fin 310) (d : ℕ) : ℚ :=
  ∑ i ∈ range (farB' k - farB k), octTerm a k d i

/-- The side conditions of a far band. -/
def farOK (a : ℚ) (k : Fin 310) : Bool :=
  decide (0 < farB k) && covers 0 (farRuns k) (128 * (farB' k - farB k)) &&
    (farRuns k).all (fun r => decide (r.2.2 * (128 * farB k + r.2.1 + 1) ≤ (farData k).1)) &&
    (List.range (farB' k - farB k)).all (fun i => decide (1 ≤ farNlo k i) &&
      (farRuns k).all (fun r =>
        decide (r.1 ≤ 128 * i + 127 → 128 * i ≤ r.2.1 → farNlo k i ≤ r.2.2))) &&
    decide (0 ≤ a) && decide (2 * a * (((farData k).1 : ℚ) / 128 * log2hi) ≤ 2)

theorem sum_range_mul128 (f : ℕ → ℝ) (N : ℕ) :
    ∑ j ∈ range (128 * N), f j = ∑ i ∈ range N, ∑ j ∈ range 128, f (128 * i + j) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.mul_succ, sum_range_add, ih,
      sum_range_succ (fun i => ∑ j ∈ range 128, f (128 * i + j)) N]

theorem far_le (a : ℚ) (k : Fin 310) (hk : 301 ≤ k.val) (hok : farOK a k = true) {d : ℕ}
    (hd : 2 ≤ d) : bandBound a d k ≤ (farUB a k d : ℝ) := by
  simp only [farOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hb0, hcov⟩, hLmax⟩, hnlo⟩, ha0⟩, ha2⟩ := hok
  have hkf : k = ⟨301 + (farIdx k).val, by omega⟩ := by
    apply Fin.ext
    simp only [farIdx]
    omega
  have hspec := farBand_spec (farIdx k)
  rw [← hkf] at hspec
  generalize hb : farB k = b at hb0 hLmax hnlo hcov
  generalize hb' : farB' k = b' at hcov hnlo
  have hband : bandOf k = (2 ^ b, 2 ^ b') := by
    rw [← hb, ← hb']
    exact hspec.1
  have hbb : b < b' := by
    rw [← hb, ← hb']
    exact hspec.2
  clear hkf hspec
  generalize hLm : (farData k).1 = Lm at hLmax ha2
  have hfarP : farP a k = expUB (2 * a * ((Lm : ℚ) / 128 * log2hi)) := by
    unfold farP
    rw [hLm]
  clear hLm
  simp only [List.all_eq_true, decide_eq_true_eq] at hLmax
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hnlo
  have hN : bandN k = 128 * (b' - b) := by
    rw [bandN_far k hk, ← hb, ← hb']
    rfl
  have hX : ((bandOf k).1 : ℝ) = (2 : ℝ) ^ b := by rw [hband]; push_cast; rfl
  have hY : ((bandOf k).2 : ℝ) = (2 : ℝ) ^ b' := by rw [hband]; push_cast; rfl
  have hlogx : ∀ m, Real.log (bx k m) = ((b : ℝ) + (m : ℝ) / 128) * Real.log 2 := by
    intro m
    unfold bx
    rw [hX, hY, hN]
    exact log_cellPoint_pow2 hbb m
  have hbnc : ∀ j, bnc k j = runCard (farRuns k) j := by
    intro j
    simp only [bnc, rule_far k hk, farRule, farRuns]
  have hxpos : ∀ m, 0 < bx k m := fun m => by linarith [one_lt_bx k m]
  have hpow : ∀ e : ℕ, Real.log ((2 : ℝ) ^ e) = (e : ℝ) * Real.log 2 := fun e => by
    rw [Real.log_pow]
  have hxeq : ∀ i : ℕ, bx k (128 * i) = (2 : ℝ) ^ (b + i) := by
    intro i
    apply Real.log_injOn_pos (Set.mem_Ioi.mpr (hxpos _)) (Set.mem_Ioi.mpr (by positivity))
    rw [hlogx, hpow]
    push_cast
    ring
  have hl2 := log2lo_lt
  have hl2' := log2_lt_hi
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ha : (0 : ℝ) ≤ a := by exact_mod_cast ha0
  -- every cell lies in a run
  have hrun : ∀ j < 128 * (b' - b), ∃ r ∈ farRuns k, r.1 ≤ j ∧ j ≤ r.2.1 ∧
      bnc k j = r.2.2 := by
    intro j hj
    obtain ⟨r, hr, h1, h2⟩ := covers_spec _ 0 _ hcov j (Nat.zero_le _) hj
    rw [hbnc]
    unfold runCard
    cases hf : (farRuns k).find? (fun r => decide (r.1 ≤ j ∧ j ≤ r.2.1)) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp only [decide_eq_true_eq]; exact ⟨h1, h2⟩) (hf r hr)
    | some r'' =>
      have hp := List.find?_some hf
      simp only [decide_eq_true_eq] at hp
      exact ⟨r'', List.mem_of_find?_eq_some hf, hp.1, hp.2, rfl⟩
  have hl2hi : (0 : ℚ) ≤ log2hi := by unfold log2hi; norm_num
  have hexp := exp_le_expUB (x := 2 * a * ((Lm : ℚ) / 128 * log2hi))
    (mul_nonneg (mul_nonneg (by norm_num) ha0)
      (mul_nonneg (div_nonneg (Nat.cast_nonneg _) (by norm_num)) hl2hi)) ha2
  rw [← hfarP] at hexp
  have hP0 : (0 : ℝ) ≤ (farP a k : ℚ) := (Real.exp_pos _).le.trans hexp
  have hPj : ∀ j < 128 * (b' - b), cellPi a (bx k) (bnc k) j ≤ (farP a k : ℝ) := by
    intro j hj
    obtain ⟨r, hr, -, h2, h3⟩ := hrun j hj
    have hc := hLmax r hr
    have hc' : r.2.2 * (128 * b + j + 1) ≤ Lm :=
      le_trans (Nat.mul_le_mul_left _ (by omega)) hc
    have hc'' : ((r.2.2 * (128 * b + j + 1) : ℕ) : ℝ) ≤ (Lm : ℝ) := by
      exact_mod_cast hc'
    push_cast at hc''
    have hcj : (bnc k j : ℝ) * (((b : ℝ) + ((j + 1 : ℕ) : ℝ) / 128) * Real.log 2) ≤
        (Lm : ℝ) / 128 * (log2hi : ℝ) := by
      rw [h3]
      calc (r.2.2 : ℝ) * (((b : ℝ) + ((j + 1 : ℕ) : ℝ) / 128) * Real.log 2) =
            ((r.2.2 : ℝ) * (128 * b + j + 1)) / 128 * Real.log 2 := by push_cast; ring
        _ ≤ (Lm : ℝ) / 128 * Real.log 2 := by
            apply mul_le_mul_of_nonneg_right _ hlog2.le
            exact div_le_div_of_nonneg_right hc'' (by norm_num)
        _ ≤ _ := mul_le_mul_of_nonneg_left hl2'.le (div_nonneg (Nat.cast_nonneg _) (by norm_num))
    unfold cellPi
    refine le_trans (Real.exp_le_exp.mpr ?_) hexp
    rw [hlogx (j + 1)]
    push_cast at hcj ⊢
    have h2a : (0 : ℝ) ≤ 2 * (a : ℝ) := mul_nonneg (by norm_num) ha
    calc 2 * (a : ℝ) * (bnc k j : ℝ) * (((b : ℝ) + ((j : ℝ) + 1) / 128) * Real.log 2) =
          2 * (a : ℝ) * ((bnc k j : ℝ) * (((b : ℝ) + ((j : ℝ) + 1) / 128) * Real.log 2)) := by
          ring
      _ ≤ 2 * (a : ℝ) * ((Lm : ℝ) / 128 * (log2hi : ℝ)) := mul_le_mul_of_nonneg_left hcj h2a
  have hbc := bandBound_le_cells k a hd
  rw [hN, sum_range_mul128] at hbc
  refine hbc.trans ?_
  unfold farUB
  rw [hb, hb']
  push_cast
  apply sum_le_sum
  intro i hi
  rw [mem_range] at hi
  have hbi : 0 < b + i := by omega
  have hA1 : (1 : ℝ) < (2 : ℝ) ^ (b + i) := one_lt_pow₀ (by norm_num) (by omega)
  have hr0 : (0 : ℝ) < (octR (b + i) : ℝ) := by exact_mod_cast octR_pos (b + i)
  have hrA : (octR (b + i) : ℝ) ^ 2 ≤ (2 : ℝ) ^ (b + i) := by exact_mod_cast octR_sq (b + i)
  have hlamA : (((b + i : ℕ) : ℚ) * log2lo : ℚ) ≤ Real.log ((2 : ℝ) ^ (b + i)) := by
    rw [hpow]
    push_cast
    exact mul_le_mul_of_nonneg_left hl2.le (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  have hlam : (0 : ℝ) < (((b + i : ℕ) : ℚ) * log2lo : ℚ) := by
    have := log2lo_pos
    push_cast
    exact mul_pos (by exact_mod_cast hbi) this
  have hb0' : (0 : ℝ) < b := by exact_mod_cast hb0
  have hlam0 : (0 : ℝ) < ((b : ℚ) * log2lo : ℚ) := by
    have := log2lo_pos
    push_cast
    exact mul_pos hb0' this
  have hlam0x : (((b : ℚ) * log2lo : ℚ) : ℝ) ≤ Real.log (bx k 0) := by
    rw [hlogx 0]
    push_cast
    simp only [zero_div, add_zero]
    exact mul_le_mul_of_nonneg_left hl2.le hb0'.le
  obtain ⟨hn1, hnr⟩ := hnlo i hi
  have hn0 : (0 : ℝ) < farNlo k i := by exact_mod_cast hn1
  have hG0 : (0 : ℝ) ≤ ((farP a k / (farNlo k i : ℚ) : ℚ) : ℝ) := by
    push_cast
    exact div_nonneg hP0 hn0.le
  have hJ : ∀ j < 128, 128 * i + j < 128 * (b' - b) := fun j hj => by
    have : i + 1 ≤ b' - b := hi
    omega
  have hx : ∀ j < 128, (2 : ℝ) ^ (b + i) ≤ bx k (128 * i + j) := by
    intro j _
    rw [← Real.log_le_log_iff (pow_pos two_pos _) (hxpos _), hpow, hlogx]
    apply mul_le_mul_of_nonneg_right _ hlog2.le
    push_cast
    have : (0 : ℝ) ≤ (j : ℝ) / 128 := div_nonneg (Nat.cast_nonneg _) (by norm_num)
    have e : ((128 : ℝ) * i + j) / 128 = i + (j : ℝ) / 128 := by ring
    rw [e]
    linarith
  have hP : ∀ j < 128, cellPi a (bx k) (bnc k) (128 * i + j) ≤ (farP a k : ℝ) :=
    fun j hj => hPj _ (hJ j hj)
  have hG : ∀ j < 128, cellG a (bx k) (bnc k) (128 * i + j) ≤
      ((farP a k / (farNlo k i : ℚ) : ℚ) : ℝ) := by
    intro j hj
    obtain ⟨r, hr, h1, h2, h3⟩ := hrun _ (hJ j hj)
    have hn : farNlo k i ≤ bnc k (128 * i + j) := by
      rw [h3]
      exact hnr r hr (by omega) (by omega)
    have hn' : (farNlo k i : ℝ) ≤ bnc k (128 * i + j) := by exact_mod_cast hn
    unfold cellG
    push_cast
    exact div_le_div₀ hP0 (hP j hj) hn0 hn'
  have hg := group_le k a hd (128 * i) 128 hA1 hr0 hrA hlam hlamA hlam0 hlam0x hx hP hG hP0 hG0
  have hend : bx k (128 * i + 128) - bx k (128 * i) = (2 : ℝ) ^ (b + i) := by
    have h1 := hxeq (i + 1)
    rw [show 128 * (i + 1) = 128 * i + 128 by ring] at h1
    rw [h1, hxeq i, show b + (i + 1) = b + i + 1 by ring, pow_succ]
    ring
  rw [hend] at hg
  refine hg.trans (le_of_eq ?_)
  unfold octTerm
  rw [hb]
  push_cast
  ring

end Sarkozy.HsumProof

module

public import Sarkozy.TailCorr.InjCount

@[expose] public section

/-!
# The matching kernel of the uniform law on injective row configurations

`paper/sections/25_upper_reference.tex`, `subsec:row-anova-correlation` (`ρ_E`), for a matching
graph without edges; `paper/sections/17_completion_repair.tex`, `def:five-type-datum`.

Let `π_E` be uniform on the jointly injective configurations `ω : Fin 3 → Q → F` of three rows
(`|Q| = k`, `|F| = N`). Then, with `A = (N - k)_k` and `M = (N - 2k)_k`:
* `gam_eq`, `nu_eq`, `nub_eq`: `Γ(x, b) ∝ M·[(x, b) injective]`, `ν(b) ∝ M A·[b injective]`, and
  `ν^b` is uniform on the `A` rows `x` with `(x, b)` injective;
* `kernel_eq`: `T_E^b(x, y) = (A/M)·[(x, b, y) injective]` on the support of `ν^b ⊗ ν^b`;
* `rowSum_eq`: every row of `|T_E^b - 1|` has `ν^b`-mass `2(A - M)/A`;
* **`uniform_normBound`**: `‖T_E^b - J‖ ≤ 2(A - M)/A` on `L²(ν^b)` at every middle value;
* **`uniform_normBound_sqrt`**: for `k ≤ 6` and `N ≥ 2²⁰`, `‖T_E^b - J‖ ≤ N^{-1/2}`.
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.FiveType Sarkozy.PartV Sarkozy.PartVLaws

variable {F : Type*} [Fintype F] [DecidableEq F] {Q : Type*} [Fintype Q] [DecidableEq Q]

variable (F Q) in
/-- `A = (N - k)_k`: the rows `x` with `(x, b)` injective, for an injective `b`. -/
def cntA : ℕ := (Fintype.card F - Fintype.card Q).descFactorial (Fintype.card Q)

variable (F Q) in
/-- `M = (N - 2k)_k`: the rows `y` with `(x, b, y)` injective, for an injective `(x, b)`. -/
def cntM : ℕ := (Fintype.card F - 2 * Fintype.card Q).descFactorial (Fintype.card Q)

variable (F Q) in
omit [DecidableEq F] [DecidableEq Q] in
/-- `M ≤ A`. -/
theorem cntM_le_cntA : cntM F Q ≤ cntA F Q := by
  unfold cntM cntA
  exact Nat.descFactorial_le _ (by omega)

/-- `∑_y [p y] c = c·#{y : p y}`. -/
theorem sum_ite_const {α : Type*} [Fintype α] (p : α → Prop) [DecidablePred p] (c : ℝ) :
    ∑ y, (if p y then c else 0) = c * ((univ.filter p).card : ℝ) := by
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul, mul_comm]

section Law

variable (πE : FiniteLaw (Fin 3 → Q → F)) {c0 : ℝ}
  (hπ : ∀ ω, πE.weight ω = if JInj ω then c0 else 0)

include hπ

/-- **`Γ(x, b) = c₀ M [(x, b) injective]`.** -/
theorem gam_eq (x b : Q → F) :
    (gamOf πE).weight ![x, b] = if JInj ![x, b] then c0 * cntM F Q else 0 := by
  rw [gamOf_weight_eq_sum]
  simp_rw [hπ]
  rw [sum_ite_const]
  by_cases h : JInj ![x, b]
  · simp only [h, ↓reduceIte]
    rw [card_inj3 h]
    rfl
  · have he : (univ.filter fun y : Q → F => JInj ![x, b, y]) = ∅ := by
      ext y
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hy => h ((inj3_iff x b y).mp hy).1
    simp only [h, ↓reduceIte, he, card_empty, Nat.cast_zero, mul_zero]

/-- **`ν(b) = c₀ M A [b injective]`.** -/
theorem nu_eq (b : Q → F) :
    (nuOf πE).weight b = if Function.Injective b then c0 * cntM F Q * cntA F Q else 0 := by
  rw [← sum_gamOf]
  simp_rw [gam_eq πE hπ]
  rw [sum_ite_const]
  by_cases h : Function.Injective b
  · simp only [h, ↓reduceIte]
    rw [card_inj2 h]
    rfl
  · have he : (univ.filter fun x : Q → F => JInj ![x, b]) = ∅ := by
      ext x
      simp only [mem_filter, mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun hx => h ((inj2_iff x b).mp hx).1
    simp only [h, ↓reduceIte, he, card_empty, Nat.cast_zero, mul_zero]

/-- A middle value charged by `ν` is injective. -/
theorem inj_of_nu {b : Q → F} (hb : (nuOf πE).weight b ≠ 0) : Function.Injective b := by
  by_contra h
  rw [nu_eq πE hπ] at hb
  simp only [h, ↓reduceIte, ne_eq, not_true_eq_false] at hb

variable (hc0 : 0 < c0) (hM : 0 < cntM F Q) (hA : 0 < cntA F Q)

include hc0 hM hA

/-- **`ν^b` is uniform on the `A` rows `x` with `(x, b)` injective.** -/
theorem nub_eq {b : Q → F} (hb : Function.Injective b) (x : Q → F) :
    (nubOf πE b).weight x = if JInj ![x, b] then (cntA F Q : ℝ)⁻¹ else 0 := by
  have hν : (nuOf πE).weight b = c0 * cntM F Q * cntA F Q := by
    rw [nu_eq πE hπ]
    simp only [hb, ↓reduceIte]
  have hν0 : (nuOf πE).weight b ≠ 0 := by
    rw [hν]
    have : (0 : ℝ) < cntM F Q := by exact_mod_cast hM
    have : (0 : ℝ) < cntA F Q := by exact_mod_cast hA
    positivity
  rw [nubOf_weight πE hν0, gam_eq πE hπ, hν]
  by_cases h : JInj ![x, b]
  · simp only [h, ↓reduceIte]
    have : (0 : ℝ) < cntM F Q := by exact_mod_cast hM
    field_simp
  · simp only [h, ↓reduceIte, zero_div]

/-- **The matching kernel**: `T_E^b(x, y) = (A/M) [(x, b, y) injective]` on the support of
`ν^b ⊗ ν^b`, and `0` off it. -/
theorem kernel_eq {b : Q → F} (hb : Function.Injective b) (x y : Q → F) :
    kernelOf πE πE b x y = if JInj ![x, b] ∧ JInj ![y, b] then
      (if JInj ![x, b, y] then (cntA F Q : ℝ) / cntM F Q else 0) else 0 := by
  have hν : (nuOf πE).weight b = c0 * cntM F Q * cntA F Q := by
    rw [nu_eq πE hπ]
    simp only [hb, ↓reduceIte]
  have hM' : (0 : ℝ) < cntM F Q := by exact_mod_cast hM
  have hA' : (0 : ℝ) < cntA F Q := by exact_mod_cast hA
  unfold kernelOf
  rw [nub_eq πE hπ hc0 hM hA hb, nub_eq πE hπ hc0 hM hA hb, hν, hπ]
  by_cases hx : JInj ![x, b]
  · by_cases hy : JInj ![y, b]
    · have hd : c0 * (cntM F Q : ℝ) * cntA F Q * (cntA F Q : ℝ)⁻¹ * (cntA F Q : ℝ)⁻¹ ≠ 0 := by
        positivity
      simp only [hx, hy, ↓reduceIte, hd, and_self]
      by_cases hxy : JInj ![x, b, y]
      · simp only [hxy, ↓reduceIte]
        field_simp
      · simp only [hxy, ↓reduceIte, zero_div]
    · simp only [hx, hy, ↓reduceIte, mul_zero, and_false]
  · simp only [hx, ↓reduceIte, mul_zero, zero_mul, false_and]

/-- **Every row of `|T_E^b - 1|` has `ν^b`-mass `2(A - M)/A`.** -/
theorem rowSum_eq {b : Q → F} (hb : Function.Injective b) {x : Q → F} (hx : JInj ![x, b]) :
    ∑ y, (nubOf πE b).weight y * |kernelOf πE πE b x y - 1| =
      2 * (((cntA F Q : ℝ) - cntM F Q) / cntA F Q) := by
  have hM' : (0 : ℝ) < cntM F Q := by exact_mod_cast hM
  have hA' : (0 : ℝ) < cntA F Q := by exact_mod_cast hA
  have hMA : (cntM F Q : ℝ) ≤ cntA F Q := by exact_mod_cast cntM_le_cntA F Q
  have hterm : ∀ y, (nubOf πE b).weight y * |kernelOf πE πE b x y - 1| =
      (if JInj ![x, b, y] then (cntA F Q : ℝ)⁻¹ * ((cntA F Q : ℝ) / cntM F Q - 1) else 0) +
        (if JInj ![y, b] ∧ ¬ JInj ![x, b, y] then (cntA F Q : ℝ)⁻¹ else 0) := by
    intro y
    rw [nub_eq πE hπ hc0 hM hA hb, kernel_eq πE hπ hc0 hM hA hb]
    by_cases hy : JInj ![y, b]
    · by_cases hxy : JInj ![x, b, y]
      · simp only [hy, hxy, hx, and_self, ↓reduceIte, not_true_eq_false, and_false, add_zero]
        rw [abs_of_nonneg]
        rw [sub_nonneg, le_div_iff₀ hM', one_mul]
        exact hMA
      · simp only [hy, hxy, hx, and_self, ↓reduceIte, not_false_eq_true, zero_add,
          zero_sub, abs_neg, abs_one, mul_one]
    · have hxy : ¬ JInj ![x, b, y] := fun h => hy (inj2_of_inj3 h)
      simp only [hy, hxy, ↓reduceIte, zero_mul, and_false, add_zero, false_and]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, sum_ite_const, sum_ite_const, card_inj3 hx]
  have hsplit : ((univ.filter fun y : Q → F => JInj ![y, b] ∧ ¬ JInj ![x, b, y]).card : ℝ) =
      cntA F Q - cntM F Q := by
    have hsub : (univ.filter fun y : Q → F => JInj ![x, b, y]) ⊆
        univ.filter fun y : Q → F => JInj ![y, b] := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      exact inj2_of_inj3 hy
    have hfilt : (univ.filter fun y : Q → F => JInj ![y, b] ∧ ¬ JInj ![x, b, y]) =
        (univ.filter fun y : Q → F => JInj ![y, b]) \
          univ.filter fun y : Q → F => JInj ![x, b, y] := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    have h2 : (univ.filter fun y : Q → F => JInj ![y, b]).card = cntA F Q := by
      have e : (univ.filter fun y : Q → F => JInj ![y, b]) =
          univ.filter fun y : Q → F => Function.Injective y ∧ ∀ q, y q ∉ univ.image b := by
        ext y
        simp only [mem_filter, mem_univ, true_and, inj2_iff, hb]
      rw [e, card_avoid, card_image_of_injective _ hb, card_univ]
      rfl
    rw [hfilt, card_sdiff_of_subset hsub, h2, card_inj3 hx, Nat.cast_sub]
    · rfl
    · rw [← h2, ← card_inj3 hx]
      exact card_le_card hsub
  rw [hsplit]
  change (cntA F Q : ℝ)⁻¹ * ((cntA F Q : ℝ) / cntM F Q - 1) * cntM F Q +
    (cntA F Q : ℝ)⁻¹ * (cntA F Q - cntM F Q) = 2 * (((cntA F Q : ℝ) - cntM F Q) / cntA F Q)
  field_simp
  ring

/-- **`‖T_E^b - J‖ ≤ 2(A - M)/A` on `L²(ν^b)`** at every middle value charged by `ν`. -/
theorem uniform_normBound {b : Q → F} (hb : (nuOf πE).weight b ≠ 0) :
    NormBound (nubOf πE b) (kernelOf πE πE b) (2 * (((cntA F Q : ℝ) - cntM F Q) / cntA F Q)) := by
  have hbi := inj_of_nu πE hπ hb
  have hA' : (0 : ℝ) < cntA F Q := by exact_mod_cast hA
  have hMA : (cntM F Q : ℝ) ≤ cntA F Q := by exact_mod_cast cntM_le_cntA F Q
  have hsupp : ∀ x, (nubOf πE b).weight x ≠ 0 → JInj ![x, b] := by
    intro x hx
    by_contra h
    rw [nub_eq πE hπ hc0 hM hA hbi] at hx
    simp only [h, ↓reduceIte, ne_eq, not_true_eq_false] at hx
  refine normBound_of_rowSums _ _ (by
    have : (0 : ℝ) ≤ ((cntA F Q : ℝ) - cntM F Q) / cntA F Q :=
      div_nonneg (by linarith) hA'.le
    linarith) (fun x hx => le_of_eq (rowSum_eq πE hπ hc0 hM hA hbi (hsupp x hx)))
    (fun y hy => le_of_eq ?_)
  rw [← rowSum_eq πE hπ hc0 hM hA hbi (hsupp y hy)]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [kernel_eq πE hπ hc0 hM hA hbi, kernel_eq πE hπ hc0 hM hA hbi]
  have e1 : (JInj ![x, b] ∧ JInj ![y, b]) ↔ (JInj ![y, b] ∧ JInj ![x, b]) := and_comm
  simp only [e1, inj3_swap x b y]

end Law

/-! ## The size of `2(A - M)/A` -/

omit [DecidableEq F] [DecidableEq Q] in
/-- `0 < M` and `0 < A` when `3k ≤ N`. -/
theorem cnt_pos (h : 3 * Fintype.card Q ≤ Fintype.card F) : 0 < cntM F Q ∧ 0 < cntA F Q := by
  unfold cntM cntA
  constructor <;> exact Nat.pos_of_ne_zero fun h0 => by
    rw [Nat.descFactorial_eq_zero_iff_lt] at h0
    omega

omit [DecidableEq F] [DecidableEq Q] in
/-- **`2(A - M)/A ≤ 4k²/(N - 3k)`** when `3k < N` and `k²/(N - 3k) ≤ 1/2`. -/
theorem defect_le (h3 : 3 * Fintype.card Q < Fintype.card F)
    (hsmall : (Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) /
      ((Fintype.card F : ℝ) - 3 * Fintype.card Q)) ≤ 1 / 2) :
    2 * (((cntA F Q : ℝ) - cntM F Q) / cntA F Q) ≤
      4 * (Fintype.card Q : ℝ) * ((Fintype.card Q : ℝ) /
        ((Fintype.card F : ℝ) - 3 * Fintype.card Q)) := by
  set k := Fintype.card Q with hk
  set N := Fintype.card F with hN
  have hpos := cnt_pos (F := F) (Q := Q) h3.le
  have hM' : (0 : ℝ) < cntM F Q := by exact_mod_cast hpos.1
  have hA' : (0 : ℝ) < cntA F Q := by exact_mod_cast hpos.2
  -- `A ≤ (1 + ε)^k M` with `a = N - 2k`, `ε = k/(a - k)`
  have hka : k < N - 2 * k := by omega
  have hratio := descFactorial_ratio hka k le_rfl
  have ha : N - 2 * k + k = N - k := by omega
  rw [ha] at hratio
  have hcast : ((N - 2 * k : ℕ) : ℝ) - k = (N : ℝ) - 3 * k := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    ring
  rw [hcast] at hratio
  set ε := (k : ℝ) / ((N : ℝ) - 3 * k) with hε
  have hε0 : 0 ≤ ε := by
    have : (3 * k : ℝ) < N := by exact_mod_cast h3
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hpow := one_add_pow_le hε0 k hsmall
  have hA_le : (cntA F Q : ℝ) ≤ (1 + 2 * k * ε) * cntM F Q := by
    calc (cntA F Q : ℝ) ≤ (1 + ε) ^ k * cntM F Q := hratio
      _ ≤ (1 + 2 * k * ε) * cntM F Q := mul_le_mul_of_nonneg_right hpow hM'.le
  have hMA : (cntM F Q : ℝ) ≤ cntA F Q := by exact_mod_cast cntM_le_cntA F Q
  have hkε : 0 ≤ 2 * (k : ℝ) * ε := by positivity
  have h2 : (cntA F Q : ℝ) - cntM F Q ≤ 2 * k * ε * cntA F Q := by
    have : 2 * k * ε * (cntM F Q : ℝ) ≤ 2 * k * ε * cntA F Q :=
      mul_le_mul_of_nonneg_left hMA hkε
    nlinarith
  have h3 : ((cntA F Q : ℝ) - cntM F Q) / cntA F Q ≤ 2 * k * ε := by
    rw [div_le_iff₀ hA']
    exact h2
  linarith

omit [DecidableEq F] [DecidableEq Q] in
/-- **`2(A - M)/A ≤ N^{-1/2}`** for `k ≤ 6` and `N ≥ 2²⁰`. -/
theorem defect_le_sqrt (hk : Fintype.card Q ≤ 6) (hN : (2 : ℝ) ^ 20 ≤ Fintype.card F) :
    2 * (((cntA F Q : ℝ) - cntM F Q) / cntA F Q) ≤ 1 / Real.sqrt (Fintype.card F) := by
  set k := Fintype.card Q with hkdef
  set N := Fintype.card F with hNdef
  have hk' : (k : ℝ) ≤ 6 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h3 : 3 * k < N := by
    have : (3 * k : ℝ) < N := by linarith
    exact_mod_cast this
  have hden : (2 : ℝ) ^ 20 - 18 ≤ (N : ℝ) - 3 * k := by linarith
  have hden0 : (0 : ℝ) < (N : ℝ) - 3 * k := lt_of_lt_of_le (by norm_num) hden
  have hsmall : (k : ℝ) * ((k : ℝ) / ((N : ℝ) - 3 * k)) ≤ 1 / 2 := by
    rw [mul_div_assoc', div_le_iff₀ hden0]
    nlinarith
  refine (defect_le h3 hsmall).trans ?_
  have hs : (2 : ℝ) ^ 10 ≤ Real.sqrt N := by
    rw [show (2 : ℝ) ^ 10 = Real.sqrt ((2 ^ 10) ^ 2) from
      (Real.sqrt_sq (by norm_num)).symm]
    have h20 : ((2 : ℝ) ^ 10) ^ 2 ≤ N := by
      have : ((2 : ℝ) ^ 10) ^ 2 = 2 ^ 20 := by norm_num
      linarith
    exact Real.sqrt_le_sqrt h20
  have hs0 : 0 < Real.sqrt N := lt_of_lt_of_le (by norm_num) hs
  have hsq : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt (Nat.cast_nonneg _)
  rw [mul_div_assoc', div_le_div_iff₀ hden0 hs0, one_mul]
  have hkk : 4 * (k : ℝ) * k ≤ 144 := by nlinarith
  calc 4 * (k : ℝ) * k * Real.sqrt N ≤ 144 * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hkk hs0.le
    _ ≤ (N : ℝ) - 3 * k := by nlinarith

/-- **`‖T_E^b - J‖ ≤ N^{-1/2}`** for the uniform law on injective configurations of three rows
of `k ≤ 6` labels in a set of `N ≥ 2²⁰` labels, at every middle value charged by `ν`. -/
theorem uniform_normBound_sqrt (πE : FiniteLaw (Fin 3 → Q → F)) {c0 : ℝ}
    (hπ : ∀ ω, πE.weight ω = if JInj ω then c0 else 0) (hc0 : 0 < c0)
    (hk : Fintype.card Q ≤ 6) (hN : (2 : ℝ) ^ 20 ≤ Fintype.card F) {b : Q → F}
    (hb : (nuOf πE).weight b ≠ 0) :
    NormBound (nubOf πE b) (kernelOf πE πE b) (1 / Real.sqrt (Fintype.card F)) := by
  have h3 : 3 * Fintype.card Q ≤ Fintype.card F := by
    have : (3 * Fintype.card Q : ℝ) ≤ Fintype.card F := by
      have hk' : (Fintype.card Q : ℝ) ≤ 6 := by exact_mod_cast hk
      linarith
    exact_mod_cast this
  have hpos := cnt_pos (F := F) (Q := Q) h3
  exact normBound_mono (uniform_normBound πE hπ hc0 hpos.1 hpos.2 hb) (defect_le_sqrt hk hN)

end Sarkozy.TailCorr

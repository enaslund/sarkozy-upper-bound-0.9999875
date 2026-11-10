module

public import Sarkozy.TailCorr.Uniform

@[expose] public section

/-!
# The cut kernel of the uniform law on injective pairs of configurations

`paper/sections/25_upper_reference.tex`, `subsec:upper-reference-rp` (V3) for the field pair
`EE`, whose graph has no edges.

Let `x, y : Q → F` (`|Q| = k`, `|F| = N`) be jointly injective and uniform. The law of `x` is
uniform on the `A = (N)_k` injective configurations, and given `x`, `y` is uniform on the
`M = (N - k)_k` injective configurations avoiding the values of `x`. With
`T(x, y) = (A/M)[(x, y) injective]` on the injective pairs:
* `pair_weight`: `μ(x) μ(y) T(x, y) = [(x, y) injective]/(A M)`;
* `uniform2_normBound`: `‖T - J‖ ≤ 2(A - M)/A` on `L²(μ)`;
* `defect_le_gen`, `defect2_le_sqrt`: `2(A - M)/A ≤ N^{-1/2}` for `k ≤ 9`, `N ≥ 2²⁰`.
-/

namespace Sarkozy.TailCorr

open Finset Sarkozy.FiveType Sarkozy.PartVLaws

variable {F : Type*} [Fintype F] [DecidableEq F] {Q : Type*} [Fintype Q] [DecidableEq Q]

/-! ## The general falling-factorial defect -/

/-- **`2((a + k)_k - (a)_k)/(a + k)_k ≤ 4k·k/(a - k)`** when `k < a` and `k·k/(a - k) ≤ 1/2`. -/
theorem defect_le_gen {a k : ℕ} (hka : k < a)
    (hsmall : (k : ℝ) * ((k : ℝ) / ((a : ℝ) - k)) ≤ 1 / 2) :
    2 * ((((a + k).descFactorial k : ℝ) - a.descFactorial k) / (a + k).descFactorial k) ≤
      4 * (k : ℝ) * ((k : ℝ) / ((a : ℝ) - k)) := by
  have hM : (0 : ℝ) < a.descFactorial k := by
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => by
      rw [Nat.descFactorial_eq_zero_iff_lt] at h0
      omega
  have hA : (0 : ℝ) < (a + k).descFactorial k := by
    exact_mod_cast Nat.pos_of_ne_zero fun h0 => by
      rw [Nat.descFactorial_eq_zero_iff_lt] at h0
      omega
  have hratio := descFactorial_ratio hka k le_rfl
  set ε := (k : ℝ) / ((a : ℝ) - k) with hε
  have hε0 : 0 ≤ ε := by
    have : (k : ℝ) < a := by exact_mod_cast hka
    exact div_nonneg (Nat.cast_nonneg _) (by linarith)
  have hpow := one_add_pow_le hε0 k hsmall
  have hA_le : ((a + k).descFactorial k : ℝ) ≤ (1 + 2 * k * ε) * a.descFactorial k :=
    hratio.trans (mul_le_mul_of_nonneg_right hpow hM.le)
  have hMA : (a.descFactorial k : ℝ) ≤ (a + k).descFactorial k := by
    exact_mod_cast Nat.descFactorial_le _ (by omega)
  have hkε : 0 ≤ 2 * (k : ℝ) * ε := by positivity
  have h2 : ((a + k).descFactorial k : ℝ) - a.descFactorial k ≤
      2 * k * ε * (a + k).descFactorial k := by
    have : 2 * k * ε * (a.descFactorial k : ℝ) ≤ 2 * k * ε * (a + k).descFactorial k :=
      mul_le_mul_of_nonneg_left hMA hkε
    nlinarith
  have h3 : (((a + k).descFactorial k : ℝ) - a.descFactorial k) / (a + k).descFactorial k ≤
      2 * k * ε := by
    rw [div_le_iff₀ hA]
    exact h2
  linarith

/-! ## The pair law -/

variable (F Q) in
/-- `A = (N)_k`: the injective configurations. -/
def cntA2 : ℕ := (Fintype.card F).descFactorial (Fintype.card Q)

variable (F Q) in
/-- `M = (N - k)_k`: the injective configurations avoiding the values of an injective one. -/
def cntM2 : ℕ := (Fintype.card F - Fintype.card Q).descFactorial (Fintype.card Q)

/-- `#{x : x injective} = A`. -/
theorem card_inj1 : (univ.filter fun x : Q → F => Function.Injective x).card = cntA2 F Q := by
  have e : (univ.filter fun x : Q → F => Function.Injective x) =
      univ.filter fun x : Q → F => Function.Injective x ∧ ∀ q, x q ∉ (∅ : Finset F) := by
    ext x
    simp
  rw [e, card_avoid, card_empty, Nat.sub_zero]
  rfl

omit [Fintype F] [DecidableEq Q] in
/-- `(x, y)` injective iff `(y, x)` injective. -/
theorem inj2_swap (x y : Q → F) : JInj ![x, y] ↔ JInj ![y, x] := by
  rw [inj2_iff, inj2_iff]
  constructor
  · rintro ⟨hy, hx, hxy⟩
    refine ⟨hx, hy, fun q hq => ?_⟩
    obtain ⟨q', -, hq'⟩ := mem_image.mp hq
    exact hxy q' (mem_image.mpr ⟨q, mem_univ _, hq'.symm⟩)
  · rintro ⟨hx, hy, hyx⟩
    refine ⟨hy, hx, fun q hq => ?_⟩
    obtain ⟨q', -, hq'⟩ := mem_image.mp hq
    exact hyx q' (mem_image.mpr ⟨q, mem_univ _, hq'.symm⟩)

/-- `#{y : (x, y) injective} = M` for injective `x`. -/
theorem card_pair {x : Q → F} (hx : Function.Injective x) :
    (univ.filter fun y : Q → F => JInj ![x, y]).card = cntM2 F Q := by
  have e : (univ.filter fun y : Q → F => JInj ![x, y]) =
      univ.filter fun y : Q → F => Function.Injective y ∧ ∀ q, y q ∉ univ.image x := by
    ext y
    simp only [mem_filter, mem_univ, true_and]
    rw [inj2_swap, inj2_iff]
    simp only [hx, true_and]
  rw [e, card_avoid, card_image_of_injective _ hx, card_univ]
  rfl

/-- The uniform law on the injective configurations. -/
noncomputable def injLaw (hA : 0 < cntA2 F Q) : FiniteLaw (Q → F) where
  weight x := if Function.Injective x then (cntA2 F Q : ℝ)⁻¹ else 0
  nonneg x := by
    split_ifs
    · positivity
    · exact le_rfl
  total := by
    rw [sum_ite_const, card_inj1]
    have : (0 : ℝ) < cntA2 F Q := by exact_mod_cast hA
    field_simp

/-- The cut kernel `T(x, y) = (A/M)[(x, y) injective]` on the injective pairs. -/
noncomputable def pairKernel (x y : Q → F) : ℝ :=
  if Function.Injective x ∧ Function.Injective y then
    (if JInj ![x, y] then (cntA2 F Q : ℝ) / cntM2 F Q else 0) else 0

/-- **`μ(x) μ(y) T(x, y) = [(x, y) injective]/(A M)`.** -/
theorem pair_weight (hA : 0 < cntA2 F Q) (hM : 0 < cntM2 F Q) (x y : Q → F) :
    (injLaw hA).weight x * (injLaw hA).weight y * pairKernel x y =
      if JInj ![x, y] then ((cntA2 F Q : ℝ) * cntM2 F Q)⁻¹ else 0 := by
  have hA' : (0 : ℝ) < cntA2 F Q := by exact_mod_cast hA
  have hM' : (0 : ℝ) < cntM2 F Q := by exact_mod_cast hM
  change (if Function.Injective x then (cntA2 F Q : ℝ)⁻¹ else 0) *
    (if Function.Injective y then (cntA2 F Q : ℝ)⁻¹ else 0) * pairKernel x y = _
  unfold pairKernel
  by_cases hxy : JInj ![x, y]
  · have hy := ((inj2_iff x y).mp hxy).1
    have hx := ((inj2_iff x y).mp hxy).2.1
    simp only [hx, hy, hxy, and_self, ↓reduceIte]
    field_simp
  · simp only [hxy, ↓reduceIte]
    split_ifs <;> simp

/-- **Every row of `|T - 1|` has `μ`-mass `2(A - M)/A`.** -/
theorem pair_rowSum (hA : 0 < cntA2 F Q) (hM : 0 < cntM2 F Q) {x : Q → F}
    (hx : Function.Injective x) :
    ∑ y, (injLaw hA).weight y * |pairKernel x y - 1| =
      2 * (((cntA2 F Q : ℝ) - cntM2 F Q) / cntA2 F Q) := by
  have hA' : (0 : ℝ) < cntA2 F Q := by exact_mod_cast hA
  have hM' : (0 : ℝ) < cntM2 F Q := by exact_mod_cast hM
  have hMA : (cntM2 F Q : ℝ) ≤ cntA2 F Q := by
    exact_mod_cast Nat.descFactorial_le _ (Nat.sub_le _ _)
  have hterm : ∀ y, (injLaw hA).weight y * |pairKernel x y - 1| =
      (if JInj ![x, y] then (cntA2 F Q : ℝ)⁻¹ * ((cntA2 F Q : ℝ) / cntM2 F Q - 1) else 0) +
        (if Function.Injective y ∧ ¬ JInj ![x, y] then (cntA2 F Q : ℝ)⁻¹ else 0) := by
    intro y
    change (if Function.Injective y then (cntA2 F Q : ℝ)⁻¹ else 0) * |pairKernel x y - 1| = _
    unfold pairKernel
    by_cases hy : Function.Injective y
    · by_cases hxy : JInj ![x, y]
      · simp only [hy, hxy, hx, and_self, ↓reduceIte, not_true_eq_false, and_false, add_zero]
        rw [abs_of_nonneg]
        rw [sub_nonneg, le_div_iff₀ hM', one_mul]
        exact hMA
      · simp only [hy, hxy, hx, and_self, ↓reduceIte, not_false_eq_true, zero_add,
          zero_sub, abs_neg, abs_one, mul_one]
    · have hxy : ¬ JInj ![x, y] := fun h => hy ((inj2_iff x y).mp h).1
      simp only [hy, hxy, ↓reduceIte, zero_mul, add_zero, false_and]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib, sum_ite_const, sum_ite_const, card_pair hx]
  have hsplit : ((univ.filter fun y : Q → F => Function.Injective y ∧ ¬ JInj ![x, y]).card : ℝ) =
      cntA2 F Q - cntM2 F Q := by
    have hsub : (univ.filter fun y : Q → F => JInj ![x, y]) ⊆
        univ.filter fun y : Q → F => Function.Injective y := by
      intro y hy
      simp only [mem_filter, mem_univ, true_and] at hy ⊢
      exact ((inj2_iff x y).mp hy).1
    have hfilt : (univ.filter fun y : Q → F => Function.Injective y ∧ ¬ JInj ![x, y]) =
        (univ.filter fun y : Q → F => Function.Injective y) \
          univ.filter fun y : Q → F => JInj ![x, y] := by
      ext y
      simp only [mem_filter, mem_univ, true_and, mem_sdiff]
    rw [hfilt, card_sdiff_of_subset hsub, card_inj1, card_pair hx, Nat.cast_sub]
    rw [← card_inj1, ← card_pair hx]
    exact card_le_card hsub
  rw [hsplit]
  field_simp
  ring

/-- **`‖T - J‖ ≤ 2(A - M)/A` on `L²(μ)`.** -/
theorem uniform2_normBound (hA : 0 < cntA2 F Q) (hM : 0 < cntM2 F Q) :
    NormBound (injLaw hA) pairKernel (2 * (((cntA2 F Q : ℝ) - cntM2 F Q) / cntA2 F Q)) := by
  have hA' : (0 : ℝ) < cntA2 F Q := by exact_mod_cast hA
  have hMA : (cntM2 F Q : ℝ) ≤ cntA2 F Q := by
    exact_mod_cast Nat.descFactorial_le _ (Nat.sub_le _ _)
  have hsupp : ∀ x, (injLaw (F := F) (Q := Q) hA).weight x ≠ 0 → Function.Injective x := by
    intro x hx
    by_contra h
    exact hx (by
      change (if Function.Injective x then (cntA2 F Q : ℝ)⁻¹ else 0) = 0
      simp only [h, ↓reduceIte])
  refine normBound_of_rowSums _ _ (by
    have : (0 : ℝ) ≤ ((cntA2 F Q : ℝ) - cntM2 F Q) / cntA2 F Q :=
      div_nonneg (by linarith) hA'.le
    linarith) (fun x hx => le_of_eq (pair_rowSum hA hM (hsupp x hx)))
    (fun y hy => le_of_eq ?_)
  rw [← pair_rowSum hA hM (hsupp y hy)]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold pairKernel
  have e1 : (Function.Injective x ∧ Function.Injective y) ↔
      (Function.Injective y ∧ Function.Injective x) := and_comm
  simp only [e1, inj2_swap x y]

omit [DecidableEq F] [DecidableEq Q] in
/-- **`2(A - M)/A ≤ N^{-1/2}`** for `k ≤ 9` and `N ≥ 2²⁰`. -/
theorem defect2_le_sqrt (hk : Fintype.card Q ≤ 9) (hN : (2 : ℝ) ^ 20 ≤ Fintype.card F) :
    2 * (((cntA2 F Q : ℝ) - cntM2 F Q) / cntA2 F Q) ≤ 1 / Real.sqrt (Fintype.card F) := by
  set k := Fintype.card Q with hkdef
  set N := Fintype.card F with hNdef
  have hk' : (k : ℝ) ≤ 9 := by exact_mod_cast hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have h2 : 2 * k < N := by
    have : (2 * k : ℝ) < N := by linarith
    exact_mod_cast this
  have hka : k < N - k := by omega
  have ha : N - k + k = N := by omega
  have hcast : ((N - k : ℕ) : ℝ) - k = (N : ℝ) - 2 * k := by
    rw [Nat.cast_sub (by omega)]
    ring
  have hden : (2 : ℝ) ^ 20 - 18 ≤ (N : ℝ) - 2 * k := by linarith
  have hden0 : (0 : ℝ) < (N : ℝ) - 2 * k := lt_of_lt_of_le (by norm_num) hden
  have hsmall : (k : ℝ) * ((k : ℝ) / (((N - k : ℕ) : ℝ) - k)) ≤ 1 / 2 := by
    rw [hcast, mul_div_assoc', div_le_iff₀ hden0]
    nlinarith
  have hgen := defect_le_gen hka hsmall
  rw [ha, hcast] at hgen
  change 2 * ((((N).descFactorial k : ℝ) - (N - k).descFactorial k) / (N).descFactorial k) ≤ _
  refine hgen.trans ?_
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
  have hkk : 4 * (k : ℝ) * k ≤ 324 := by nlinarith
  calc 4 * (k : ℝ) * k * Real.sqrt N ≤ 324 * Real.sqrt N :=
        mul_le_mul_of_nonneg_right hkk hs0.le
    _ ≤ (N : ℝ) - 2 * k := by nlinarith

end Sarkozy.TailCorr

module

public import Sarkozy.L20Cap.GapComplement

/-!
# The bound `τ_g` on the range of `𝐯'` (`prop:l20-pair-gap`)

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-pair-gap`: the Gram
`(𝖱𝐯')^*𝖱𝐯'` is the scalar `2qE[(\bar𝖪 - 16q)²(16\bar𝖪 - \bar𝖪²)]/((1 - q)²(1 - 2q))`, and
`E[(\bar𝖪 - 16q)²(16\bar𝖪 - \bar𝖪²)] ≤ M_g = 15 + 44𝔪₊ + (42 + 12η)η²`. Notation of
`Sarkozy.L20Cap.GapComplement`.

The paper reads the scalar off the commutant of the square-affine maps (`lem:spec:affpair`(d)).
Here the same fact is proved by the orbit argument: the kernel
`M(z, z') = E_C[ψ(C)²𝖪(z, C)𝖪(z', C)]`, `ψ = 2(\bar𝖪 - 16q)/(1 - q)`, is invariant under the
square-affine maps and symmetric, hence constant off the diagonal (`pair_const`) and on it, so
its form on mean-zero `h` is `(d - o)∑h²` (`form_Mker`), with `d - o` from its trace and its total
mass.

* **`Rvop_sq`**: `‖𝖱 vOp h‖² = E[ψ²(16\bar𝖪 - \bar𝖪²)] ∑h²/(p(p - 1))`;
* `weight_le`: `(\bar𝖪 - 16q)²(16\bar𝖪 - \bar𝖪²) ≤ 16\bar𝖪³ - \bar𝖪⁴` (`\bar𝖪 = 16nq`), and
  `Mg_bound`: its mean is at most `M_g`;
* **`hA_proved`**: `‖𝖱_c vOp h‖ ≤ τ_g‖vOp h‖`, `τ_g² = 2qM_g/((1 - q)²(1 - 2q))`, the hypothesis
  `hA` of `pair_gap_ranges`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- The affine bijection `z ↦ αz + β` of `F` (`α ≠ 0`). -/
def affEquiv {α : F} (hα : α ≠ 0) (β : F) : F ≃ F :=
  (Equiv.mulLeft₀ α hα).trans (Equiv.addRight β)

omit [Fintype F] [DecidableEq F] [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem affEquiv_apply {α : F} (hα : α ≠ 0) (β z : F) : affEquiv hα β z = α * z + β := rfl

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem Kbar_affine {α : F} (hα : quadraticChar F α = 1) (β : F) (C : Fin 4 → F) :
    Kbar (affCore α β C) = Kbar C := by
  unfold Kbar
  congr 1
  rw [← Equiv.sum_comp (affEquiv (ne_zero_of_chi hα) β)]
  exact sum_congr rfl fun z _ => by rw [affEquiv_apply, Kz_affine hα]

/-- `ψ(C) = 2(\bar𝖪(C) - 16q)/(1 - q)`. -/
noncomputable def psiR (C : CoreT F) : ℝ :=
  2 * (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹)

/-- `M(z, z') = E_C[ψ(C)² 𝖪(z, C) 𝖪(z', C)]`. -/
noncomputable def Mker (z z' : F) : ℝ :=
  (coreLaw (F := F)).expect fun C => psiR C ^ 2 * Kz z C.1 * Kz z' C.1

omit [Nonempty (PairT F)] in
theorem Mker_affine (α β : F) (hα : quadraticChar F α = 1) (z z' : F) :
    Mker (α * z + β) (α * z' + β) = Mker z z' := by
  unfold Mker coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv hα β)]
  refine sum_congr rfl fun C _ => ?_
  simp only [affCoreEquiv, Equiv.coe_fn_mk, psiR, Kbar_affine hα, Kz_affine hα]

omit [Nonempty (PairT F)] in
theorem Mker_symm (z z' : F) : Mker z' z = Mker z z' := by
  unfold Mker
  exact (coreLaw (F := F)).expect_congr fun C => by ring

omit [Nonempty (PairT F)] in
/-- **The form of `M` on mean-zero `h`**: `∑_{z,z'} h(z)h(z')M(z, z') = (M(0,0) - M(0,1))∑h²`. -/
theorem form_Mker (hm1 : quadraticChar F (-1) = -1) (h : F → ℝ) (h0 : ∑ z, h z = 0) :
    ∑ z, ∑ z', h z * h z' * Mker z z' = (Mker (0 : F) 0 - Mker (0 : F) 1) * ∑ z, h z ^ 2 := by
  have hdiag : ∀ z : F, Mker z z = Mker (0 : F) 0 := by
    intro z
    have := Mker_affine (F := F) 1 (-z) (map_one _) z z
    simp only [one_mul, add_neg_cancel] at this
    exact this.symm
  have hoff : ∀ z z' : F, z ≠ z' → Mker z z' = Mker (0 : F) 1 := fun z z' h =>
    pair_const hm1 (m := Mker) (fun α β hα y y' => Mker_affine α β hα y y')
      (fun y y' => Mker_symm y y') h zero_ne_one
  have e : ∀ z z' : F, h z * h z' * Mker z z' =
      Mker (0 : F) 1 * (h z * h z') + (if z = z' then (Mker (0 : F) 0 - Mker (0 : F) 1) * h z ^ 2
        else 0) := by
    intro z z'
    by_cases hz : z = z'
    · subst hz; rw [hdiag]; simp only [↓reduceIte]; ring
    · rw [hoff z z' hz]; simp only [hz, ↓reduceIte]; ring
  simp only [e, sum_add_distrib, ← mul_sum]
  rw [← sum_mul, h0]
  simp only [sum_ite_eq, mem_univ, ↓reduceIte]
  rw [← mul_sum]
  ring

omit [Nonempty (PairT F)] in
theorem Mker_diag (z : F) : Mker z z = Mker (0 : F) 0 := by
  have := Mker_affine (F := F) 1 (-z) (map_one _) z z
  simp only [one_mul, add_neg_cancel] at this
  exact this.symm

omit [Nonempty (PairT F)] in
theorem Mker_off (hm1 : quadraticChar F (-1) = -1) {z z' : F} (h : z ≠ z') :
    Mker z z' = Mker (0 : F) 1 :=
  pair_const hm1 (m := Mker) (fun α β hα y y' => Mker_affine α β hα y y')
    (fun y y' => Mker_symm y y') h zero_ne_one

omit [Nonempty (PairT F)] in
theorem Mker_trace (hm1 : quadraticChar F (-1) = -1) :
    ∑ z : F, Mker z z =
      16 * Fintype.card F * (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1) := by
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Mker
  rw [← expect_sum', ← FiniteLaw.expect_const_mul]
  refine (coreLaw (F := F)).expect_congr fun C => ?_
  have e : ∀ z, psiR C ^ 2 * Kz z C.1 * Kz z C.1 = psiR C ^ 2 * Kz z C.1 ^ 2 := fun z => by ring
  rw [sum_congr rfl fun z _ => e z, ← mul_sum, sum_Kz_sq hm1 C.2, Kbar]
  field_simp

omit [Nonempty (PairT F)] in
theorem Mker_total :
    ∑ z : F, ∑ z' : F, Mker z z' =
      (Fintype.card F : ℝ) ^ 2 *
        (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1 ^ 2) := by
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  unfold Mker
  simp only [← expect_sum']
  rw [← FiniteLaw.expect_const_mul]
  refine (coreLaw (F := F)).expect_congr fun C => ?_
  have e : ∑ z : F, ∑ z' : F, psiR C ^ 2 * Kz z C.1 * Kz z' C.1 =
      psiR C ^ 2 * ((∑ z, Kz z C.1) * ∑ z', Kz z' C.1) := by
    rw [sum_mul_sum, mul_sum]
    exact sum_congr rfl fun z _ => by rw [mul_sum]; exact sum_congr rfl fun z' _ => by ring
  rw [e, Kbar]
  field_simp

omit [Nonempty (PairT F)] in
/-- `M(0,0) - M(0,1) = p E[ψ²(16\bar𝖪 - \bar𝖪²)]/(p - 1)`. -/
theorem Mker_gap (hm1 : quadraticChar F (-1) = -1) :
    Mker (0 : F) 0 - Mker (0 : F) 1 =
      Fintype.card F * (coreLaw (F := F)).expect
        (fun C => psiR C ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) / (Fintype.card F - 1) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  set d := Mker (0 : F) 0 with hd_def
  set o := Mker (0 : F) 1 with ho_def
  have htr : ∑ z : F, Mker z z = Fintype.card F * d := by
    rw [sum_congr rfl fun z _ => Mker_diag z, sum_const, card_univ, nsmul_eq_mul]
  have htot : ∑ z : F, ∑ z' : F, Mker z z' =
      Fintype.card F * d + Fintype.card F * (Fintype.card F - 1) * o := by
    have e : ∀ z z' : F, Mker z z' = o + (if z = z' then d - o else 0) := by
      intro z z'
      by_cases hz : z = z'
      · subst hz; rw [Mker_diag]; simp only [↓reduceIte]; ring
      · rw [Mker_off hm1 hz, ← ho_def]; simp [hz]
    simp only [e, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq, mem_univ,
      ↓reduceIte]
    ring
  have hE1 := Mker_trace (F := F) hm1
  have hE2 := Mker_total (F := F)
  rw [htr] at hE1
  rw [htot] at hE2
  have hlin : (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) =
      16 * (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1) -
        (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1 ^ 2) := by
    rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_sub]
    exact (coreLaw (F := F)).expect_congr fun C => by ring
  rw [hlin]
  have hd : d = 16 * (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1) := by
    field_simp at hE1 ⊢
    linarith
  have ho : o = (Fintype.card F * (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1 ^ 2) -
      16 * (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * Kbar C.1)) / (Fintype.card F - 1) := by
    rw [hd] at hE2
    field_simp
    nlinarith [hE2]
  rw [hd, ho]
  field_simp
  ring

/-- **`‖𝖱 vOp h‖² = E[ψ²(16\bar𝖪 - \bar𝖪²)] ∑h²/(p(p - 1))`** for mean-zero `h` (the scalar Gram
of `(𝖱𝐯)^*𝖱𝐯` on `𝓗`). -/
theorem Rvop_sq (hm1 : quadraticChar F (-1) = -1) (h : F → ℝ) (h0 : ∑ z, h z = 0) :
    (coreLaw (F := F)).expect
        (fun C => ((pairLaw (F := F)).expect (fun b => Rk C b * vOp h b)) ^ 2) =
      (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) *
        (∑ z, h z ^ 2) / ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hR : ∀ C : CoreT F, (pairLaw (F := F)).expect (fun b => Rk C b * vOp h b) =
      psiR C * ((∑ z, Kz z C.1 * h z) / Fintype.card F) := by
    intro C
    have := Rv_exact hm1 C h
    simp only [vOp]
    rw [this]
    rfl
  have e : ∀ C : CoreT F, ((pairLaw (F := F)).expect (fun b => Rk C b * vOp h b)) ^ 2 =
      ((Fintype.card F : ℝ)⁻¹) ^ 2 *
        ∑ z, ∑ z', h z * h z' * (psiR C ^ 2 * Kz z C.1 * Kz z' C.1) := by
    intro C
    rw [hR]
    have hS : (∑ z, Kz z C.1 * h z) ^ 2 = ∑ z, ∑ z', (Kz z C.1 * h z) * (Kz z' C.1 * h z') := by
      rw [sq, sum_mul_sum]
    calc (psiR C * ((∑ z, Kz z C.1 * h z) / Fintype.card F)) ^ 2
        = ((Fintype.card F : ℝ)⁻¹) ^ 2 * (psiR C ^ 2 * (∑ z, Kz z C.1 * h z) ^ 2) := by ring
      _ = ((Fintype.card F : ℝ)⁻¹) ^ 2 *
          ∑ z, ∑ z', h z * h z' * (psiR C ^ 2 * Kz z C.1 * Kz z' C.1) := by
          rw [hS, mul_sum]
          congr 1
          refine sum_congr rfl fun z _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun z' _ => by ring
  rw [(coreLaw (F := F)).expect_congr e, FiniteLaw.expect_const_mul, expect_sum']
  simp only [expect_sum', FiniteLaw.expect_const_mul]
  have hM : ∀ z z' : F, (coreLaw (F := F)).expect
      (fun C => psiR C ^ 2 * Kz z C.1 * Kz z' C.1) = Mker z z' := fun z z' => rfl
  simp only [hM]
  rw [form_Mker hm1 h h0, Mker_gap hm1]
  field_simp

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
/-- `(\bar𝖪 - 16q)²(16\bar𝖪 - \bar𝖪²) ≤ 16\bar𝖪³ - \bar𝖪⁴` (`\bar𝖪 = 16nq`: `\bar𝖪 = 0` or
`16q ≤ \bar𝖪 ≤ 16`). -/
theorem weight_le (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) :
    (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2) ≤
      16 * Kbar C.1 ^ 3 - Kbar C.1 ^ 4 := by
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hK0 : 0 ≤ Kbar C.1 := Kbar_nonneg hm1 C.2
  have hK16 : Kbar C.1 ≤ 16 := by
    unfold Kbar
    rw [div_le_iff₀ hp0]
    calc ∑ z, Kz z C.1 ≤ ∑ _z : F, (16 : ℝ) := sum_le_sum fun z _ => Kz_le hm1 C.2 z
      _ = 16 * Fintype.card F := by simp [mul_comm]
  by_cases hall : ∀ z, Kz z C.1 = 0
  · have : Kbar C.1 = 0 := by unfold Kbar; simp [hall]
    rw [this]; norm_num
  · push Not at hall
    obtain ⟨z₀, hz₀⟩ := hall
    have h16 : Kz z₀ C.1 = 16 := by
      rcases Kz_cases hm1 C.2 z₀ with ⟨h, -⟩ | h
      · exact h
      · exact absurd h hz₀
    have hlow : 16 * (Fintype.card F : ℝ)⁻¹ ≤ Kbar C.1 := by
      unfold Kbar
      rw [div_eq_mul_inv]
      have : (16 : ℝ) ≤ ∑ z, Kz z C.1 := by
        rw [← h16]
        exact single_le_sum (f := fun z => Kz z C.1) (fun z _ => Kz_nonneg hm1 C.2 z) (mem_univ z₀)
      exact mul_le_mul_of_nonneg_right this (inv_nonneg.mpr hp0.le)
    have hq0 : 0 ≤ 16 * (Fintype.card F : ℝ)⁻¹ := by positivity
    have ha : 0 ≤ Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹ := by linarith
    have hb : 0 ≤ 16 * Kbar C.1 - Kbar C.1 ^ 2 := by nlinarith
    have hsq : (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) ^ 2 ≤ Kbar C.1 ^ 2 :=
      pow_le_pow_left₀ ha (by linarith) 2
    have := mul_le_mul_of_nonneg_right hsq hb
    nlinarith [this]

omit [Nonempty (PairT F)] in
/-- **`E[(\bar𝖪 - 16q)²(16\bar𝖪 - \bar𝖪²)] ≤ M_g = 15 + 44𝔪 + (42 + 12η)η²`** (proof of
`prop:l20-pair-gap`). -/
theorem Mg_bound (hm1 : quadraticChar F (-1) = -1) {η m : ℝ}
    (hη : ∀ C : CoreT F, |Kbar C.1 - 1| ≤ η)
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m) :
    (coreLaw (F := F)).expect (fun C =>
        (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) ≤
      15 + 44 * m + (42 + 12 * η) * η ^ 2 := by
  have hpt : ∀ C : CoreT F, (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) ^ 2 *
      (16 * Kbar C.1 - Kbar C.1 ^ 2) ≤ 15 + 44 * (Kbar C.1 - 1) + (42 + 12 * η) * η ^ 2 := by
    intro C
    refine (weight_le hm1 C).trans ?_
    set y := Kbar C.1 - 1 with hy
    have hK : Kbar C.1 = 1 + y := by rw [hy]; ring
    have hyb := hη C
    rw [← hy] at hyb
    have hy2 : y ^ 2 ≤ η ^ 2 := sq_le_sq' (abs_le.mp hyb).1 (abs_le.mp hyb).2
    have hy3 : y ^ 3 ≤ η ^ 3 := by
      have : |y| ^ 3 ≤ η ^ 3 := pow_le_pow_left₀ (abs_nonneg y) hyb 3
      have h' : y ^ 3 ≤ |y| ^ 3 := by rw [← abs_pow]; exact le_abs_self _
      linarith
    rw [hK]
    nlinarith [sq_nonneg (y ^ 2)]
  calc (coreLaw (F := F)).expect (fun C =>
        (Kbar C.1 - 16 * (Fintype.card F : ℝ)⁻¹) ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2))
      ≤ (coreLaw (F := F)).expect (fun C => 15 + 44 * (Kbar C.1 - 1) + (42 + 12 * η) * η ^ 2) :=
        (coreLaw (F := F)).expect_mono hpt
    _ = 15 + 44 * (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) + (42 + 12 * η) * η ^ 2 := by
        rw [FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const,
          FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
    _ ≤ 15 + 44 * m + (42 + 12 * η) * η ^ 2 := by linarith

/-- **`hA` of `pair_gap_ranges`** (`prop:l20-pair-gap`): for mean-zero `h`,
`‖𝖱_c vOp h‖ ≤ τ_g‖vOp h‖` with `τ_g² = 2qM_g/((1 - q)²(1 - 2q))`,
`M_g = 15 + 44𝔪 + (42 + 12η)η²`. -/
theorem hA_proved (hm1 : quadraticChar F (-1) = -1) (h5 : 5 ≤ Fintype.card F) {η m : ℝ}
    (hη : ∀ C : CoreT F, |Kbar C.1 - 1| ≤ η)
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m) (h : F → ℝ) (h0 : ∑ z, h z = 0) :
    nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
      Real.sqrt (2 * (Fintype.card F : ℝ)⁻¹ * (15 + 44 * m + (42 + 12 * η) * η ^ 2) /
        ((1 - (Fintype.card F : ℝ)⁻¹) ^ 2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹))) *
        nrm (pairLaw (F := F)) (vOp h) := by
  have hp5 : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast h5
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  set q := (Fintype.card F : ℝ)⁻¹ with hqdef
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq5 : q ≤ 1 / 5 := by rw [hqdef, one_div]; exact inv_anti₀ (by norm_num) hp5
  set Mg := 15 + 44 * m + (42 + 12 * η) * η ^ 2 with hMg
  -- `𝖱_c vOp h = 𝖱 vOp h`
  have hRc : recOp (pairLaw (F := F)) Rc (vOp h) =
      fun C => (pairLaw (F := F)).expect (fun b => Rk C b * vOp h b) := by
    funext C
    unfold recOp Rc
    have e : ∀ b, (Rk C b - rmass C) * vOp h b = Rk C b * vOp h b - rmass C * vOp h b :=
      fun b => by ring
    rw [(pairLaw (F := F)).expect_congr e, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      expect_vOp h h0, mul_zero, sub_zero]
  rw [hRc]
  have hW := Mg_bound hm1 hη hm
  have hpsi : (coreLaw (F := F)).expect (fun C => psiR C ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) =
      4 / (1 - q) ^ 2 * (coreLaw (F := F)).expect (fun C =>
        (Kbar C.1 - 16 * q) ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) := by
    rw [← FiniteLaw.expect_const_mul]
    refine (coreLaw (F := F)).expect_congr fun C => ?_
    unfold psiR
    rw [← hqdef]
    have : 1 - q ≠ 0 := by linarith
    field_simp
    ring
  have hsq := Rvop_sq hm1 h h0
  rw [hpsi] at hsq
  have hv : (pairLaw (F := F)).expect (fun b => vOp h b ^ 2) =
      2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, h z ^ 2) / Fintype.card F) := vfeat_sq (F := F) h h0
  set S := ∑ z, h z ^ 2 with hS
  have hS0 : 0 ≤ S := sum_nonneg fun z _ => sq_nonneg _
  have h1q : 0 < 1 - q := by linarith
  have h12q : 0 < 1 - 2 * q := by linarith
  have hMg0 : 0 ≤ Mg := le_trans (by
    exact (coreLaw (F := F)).expect_nonneg fun C =>
      mul_nonneg (sq_nonneg _) (by
        have hK0 : 0 ≤ Kbar C.1 := Kbar_nonneg hm1 C.2
        have hK16 : Kbar C.1 ≤ 16 := by
          unfold Kbar
          rw [div_le_iff₀ hp0]
          calc ∑ z, Kz z C.1 ≤ ∑ _z : F, (16 : ℝ) := sum_le_sum fun z _ => Kz_le hm1 C.2 z
            _ = 16 * Fintype.card F := by simp [mul_comm]
        nlinarith)) hW
  apply nrm_le_of_sq_le _ _ (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (by positivity), nrm_sq_expect, nrm_sq_expect, hsq, hv]
  have hp1' : (Fintype.card F : ℝ) - 1 = Fintype.card F * (1 - q) := by
    rw [hqdef]; field_simp
  rw [hp1']
  have hE := hW
  have key : 4 / (1 - q) ^ 2 * (coreLaw (F := F)).expect (fun C =>
      (Kbar C.1 - 16 * q) ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) ≤ 4 / (1 - q) ^ 2 * Mg :=
    mul_le_mul_of_nonneg_left hE (by positivity)
  have hden : 0 < (Fintype.card F : ℝ) * (Fintype.card F * (1 - q)) := by positivity
  calc 4 / (1 - q) ^ 2 * (coreLaw (F := F)).expect (fun C =>
        (Kbar C.1 - 16 * q) ^ 2 * (16 * Kbar C.1 - Kbar C.1 ^ 2)) * S /
          ((Fintype.card F : ℝ) * (Fintype.card F * (1 - q)))
      ≤ 4 / (1 - q) ^ 2 * Mg * S / ((Fintype.card F : ℝ) * (Fintype.card F * (1 - q))) := by
        apply div_le_div_of_nonneg_right _ hden.le
        exact mul_le_mul_of_nonneg_right key hS0
    _ = 2 * q * Mg / ((1 - q) ^ 2 * (1 - 2 * q)) *
          (2 * (1 - 2 * q) / (1 - q) * (S / Fintype.card F)) := by
        have hp : (Fintype.card F : ℝ) = q⁻¹ := by rw [hqdef, inv_inv]
        rw [hp]
        have h1 : 1 - q ≠ 0 := by linarith
        have h2 : 1 - 2 * q ≠ 0 := by linarith
        have h2' : 1 - q * 2 ≠ 0 := by linarith
        have h3 : q ≠ 0 := hq0.ne'
        field_simp
        ring

end Sarkozy.L20Cap

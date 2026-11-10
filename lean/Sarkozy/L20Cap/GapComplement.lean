module

public import Sarkozy.L20Cap.GapSplit
public import Sarkozy.L20Cap.Rank4
public import Sarkozy.L20Cap.Mellin

/-!
# The complement bound `l_g = 2r + N_A` of `prop:l20-pair-gap`

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-pair-gap`: on the orthogonal
complement of the range of `𝐯'` in the mean-zero functions of the pair,
`𝖱_c = 2r𝐰𝐞^* + 𝖱_∘`, of norm at most `l_g = 2r + N_A` since `‖𝐰‖, ‖𝐞‖ ≤ 1`. Notation of
`Sarkozy.L20Cap.GapSplit`.

* `Nrect C b = (𝖪(b₀, C) - 1)(𝖪(b₁, C) - 1) - ∑_k χ(b₀ - x_k)χ(b₁ - x_k)`, the sum of the `221`
  nonstar terms of `𝖱` (`thm:rectangle-gram`'s `N`);
* `Wop`: `(Wh)(b) = E_y χ(b₀ - y)χ(b₁ - y)h(y)` (`W_{23}`), with **`Wop_sq`**:
  `‖Wh‖² = q(1 - 2q - q²)/(1 - q)‖h‖²` on mean-zero `h` (`lem:general-star`(a) for `S = {b₀, b₁}`,
  here by a direct count), so `‖𝐞‖ ≤ 1`;
* `phiG`: `φ_g(y) = E_b[χ(b₀ - y)χ(b₁ - y)g(b)]` (`r𝐞^*g`), `phiG_norm`: `‖φ_g‖ ≤ r‖g‖`;
* `corePair_norm`: `‖C ↦ ∑_k φ_g(C_k)‖ ≤ 2r‖g‖` (`2r𝐰𝐞^*`, with `wvec_sq`);
* **`hB_of_nonstar`**: if `‖C ↦ E_b[N(C; b)g(b)]‖ ≤ N_A‖g‖` on the complement, then
  `‖𝖱_c g‖ ≤ (2r + N_A)‖g‖` there: the hypothesis `hB` of `pair_gap_ranges` with `l_g = 2r + N_A`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (PairT F)]

/-- The sum of the nonstar terms of `𝖱`. -/
noncomputable def Nrect (C : CoreT F) (b : PairT F) : ℝ :=
  (Kz b.1.1 C.1 - 1) * (Kz b.1.2 C.1 - 1) - ∑ k, chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k)

/-- `(Wh)(b) = E_y χ(b₀ - y)χ(b₁ - y)h(y)`. -/
noncomputable def Wop (h : F → ℝ) (b : PairT F) : ℝ :=
  (Fintype.card F : ℝ)⁻¹ * ∑ y, chi (b.1.1 - y) * chi (b.1.2 - y) * h y

/-- `φ_g(y) = E_b[χ(b₀ - y)χ(b₁ - y)g(b)]`. -/
noncomputable def phiG (g : PairT F → ℝ) (y : F) : ℝ :=
  (pairLaw (F := F)).expect fun b => chi (b.1.1 - y) * chi (b.1.2 - y) * g b

omit [Nonempty (PairT F)] in
theorem sum_sq_conv (hF : ringChar F ≠ 2) (h : F → ℝ) (h0 : ∑ y, h y = 0) :
    ∑ z : F, ∑ z' : F, (∑ y, chi (z - y) * chi (z' - y) * h y) ^ 2 =
      (Fintype.card F : ℝ) * (Fintype.card F - 2) * ∑ y, h y ^ 2 := by
  -- expand and integrate `z`, `z'` first
  have e : ∀ z z' : F, (∑ y, chi (z - y) * chi (z' - y) * h y) ^ 2 =
      ∑ y, ∑ y', h y * h y' * ((chi (z - y) * chi (z - y')) * (chi (z' - y) * chi (z' - y'))) := by
    intro z z'
    rw [sq, sum_mul_sum]
    exact sum_congr rfl fun y _ => sum_congr rfl fun y' _ => by ring
  simp only [e]
  rw [sum_comm]
  have e2 : ∀ z' : F, ∑ z : F, ∑ y, ∑ y', h y * h y' *
      ((chi (z - y) * chi (z - y')) * (chi (z' - y) * chi (z' - y'))) =
      ∑ y, ∑ y', h y * h y' * ((if y = y' then (Fintype.card F : ℝ) - 1 else -1) *
        (chi (z' - y) * chi (z' - y'))) := by
    intro z'
    rw [sum_comm]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun y' _ => ?_
    rw [← sum_chi_mul_chi hF y y', sum_mul, mul_sum]
  simp only [e2]
  rw [sum_comm]
  have e3 : ∀ y : F, ∑ z' : F, ∑ y', h y * h y' *
      ((if y = y' then (Fintype.card F : ℝ) - 1 else -1) *
      (chi (z' - y) * chi (z' - y'))) =
      ∑ y', h y * h y' * (if y = y' then (Fintype.card F : ℝ) - 1 else -1) ^ 2 := by
    intro y
    rw [sum_comm]
    refine sum_congr rfl fun y' _ => ?_
    rw [← mul_sum, ← mul_sum, sum_chi_mul_chi hF y y']
    ring
  simp only [e3]
  have e4 : ∀ y : F, ∑ y', h y * h y' * (if y = y' then (Fintype.card F : ℝ) - 1 else -1) ^ 2 =
      ((Fintype.card F - 1) ^ 2 - 1) * h y ^ 2 + h y * ∑ y', h y' := by
    intro y
    have : ∀ y', h y * h y' * (if y = y' then (Fintype.card F : ℝ) - 1 else -1) ^ 2 =
        (if y = y' then ((Fintype.card F - 1) ^ 2 - 1) * (h y * h y') else 0) + h y * h y' := by
      intro y'; split_ifs <;> ring
    rw [sum_congr rfl fun y' _ => this y', sum_add_distrib, sum_ite_eq univ y, ← mul_sum]
    simp only [mem_univ, ↓reduceIte]
    ring
  simp only [e4, h0, mul_zero, add_zero, ← mul_sum]
  ring

/-- **`‖Wh‖² = q(1 - 2q - q²)/(1 - q)‖h‖²`** on mean-zero `h` (`lem:general-star`(a) for the pair
support `S = {b₀, b₁}`; `‖h‖² = (∑h²)/p`). -/
theorem Wop_sq (hF : ringChar F ≠ 2) (h : F → ℝ) (h0 : ∑ y, h y = 0) :
    (pairLaw (F := F)).expect (fun b => Wop h b ^ 2) =
      (Fintype.card F : ℝ)⁻¹ * (1 - 2 * (Fintype.card F : ℝ)⁻¹ - (Fintype.card F : ℝ)⁻¹ ^ 2) /
        (1 - (Fintype.card F : ℝ)⁻¹) * ((∑ y, h y ^ 2) / Fintype.card F) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have h1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  set G : F × F → ℝ := fun z => ((Fintype.card F : ℝ)⁻¹ *
    ∑ y, chi (z.1 - y) * chi (z.2 - y) * h y) ^ 2 with hG
  have e : (pairLaw (F := F)).expect (fun b => Wop h b ^ 2) =
      (pairLaw (F := F)).expect (fun b => G b.1) := rfl
  rw [e, pairLaw_expect G]
  simp only [hG, mul_pow, ← mul_sum]
  rw [sum_sq_conv hF h h0]
  have hdiag : ∑ z : F, (∑ y, chi (z - y) * chi (z - y) * h y) ^ 2 = ∑ y, h y ^ 2 := by
    have : ∀ z : F, ∑ y, chi (z - y) * chi (z - y) * h y = -h z := by
      intro z
      have e1 : ∀ y, chi (z - y) * chi (z - y) * h y = h y - if y = z then h y else 0 := by
        intro y
        by_cases hy : y = z
        · subst hy; simp [chi_zero]
        · simp only [hy, ↓reduceIte, sub_zero]
          rw [← sq, chi_sq_of_ne (sub_ne_zero.mpr (Ne.symm hy)), one_mul]
      rw [sum_congr rfl fun y _ => e1 y, sum_sub_distrib, h0, sum_ite_eq' univ z]
      simp
    simp only [this, neg_sq]
  rw [hdiag]
  field_simp

/-- The adjoint: `E_b[(Wh)(b)g(b)] = E_y h(y)φ_g(y)`. -/
theorem Wop_adj (h : F → ℝ) (g : PairT F → ℝ) :
    (pairLaw (F := F)).expect (fun b => Wop h b * g b) =
      (Fintype.card F : ℝ)⁻¹ * ∑ y, h y * phiG g y := by
  unfold Wop phiG FiniteLaw.expect
  simp only [mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun b _ => by ring

/-- `φ_g` has mean zero when `g` does. -/
theorem phiG_mean (hF : ringChar F ≠ 2) (g : PairT F → ℝ) (hg0 : (pairLaw (F := F)).expect g = 0) :
    ∑ y, phiG g y = 0 := by
  unfold phiG FiniteLaw.expect
  rw [sum_comm]
  have : ∀ b : PairT F, ∑ y : F, (pairLaw (F := F)).weight b *
      (chi (b.1.1 - y) * chi (b.1.2 - y) * g b) = -((pairLaw (F := F)).weight b * g b) := by
    intro b
    have e : ∀ y : F, (pairLaw (F := F)).weight b * (chi (b.1.1 - y) * chi (b.1.2 - y) * g b) =
        ((pairLaw (F := F)).weight b * g b) * (chi (b.1.1 - y) * chi (b.1.2 - y)) := fun y => by
      ring
    rw [sum_congr rfl fun y _ => e y, ← mul_sum, sum_chi_rev hF]
    simp only [b.2, ↓reduceIte]
    ring
  rw [sum_congr rfl fun b _ => this b, sum_neg_distrib]
  unfold FiniteLaw.expect at hg0
  rw [hg0, neg_zero]

/-- **`‖φ_g‖² ≤ q(1 - 2q - q²)/(1 - q)‖g‖²`**, i.e. `‖𝐞^*‖ ≤ 1` for `𝐞 = W/r`. -/
theorem phiG_norm (hF : ringChar F ≠ 2) (h5 : 5 ≤ Fintype.card F) (g : PairT F → ℝ)
    (hg0 : (pairLaw (F := F)).expect g = 0) :
    (∑ y, phiG g y ^ 2) / Fintype.card F ≤
      (Fintype.card F : ℝ)⁻¹ * (1 - 2 * (Fintype.card F : ℝ)⁻¹ - (Fintype.card F : ℝ)⁻¹ ^ 2) /
        (1 - (Fintype.card F : ℝ)⁻¹) * nrm (pairLaw (F := F)) g ^ 2 := by
  set c := (Fintype.card F : ℝ)⁻¹ * (1 - 2 * (Fintype.card F : ℝ)⁻¹ - (Fintype.card F : ℝ)⁻¹ ^ 2) /
    (1 - (Fintype.card F : ℝ)⁻¹) with hc
  set A := (∑ y, phiG g y ^ 2) / Fintype.card F with hA
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hA0 : 0 ≤ A := div_nonneg (sum_nonneg fun y _ => sq_nonneg _) hp0.le
  -- `A = ⟨Wφ, g⟩ ≤ ‖Wφ‖ ‖g‖ = √(cA) ‖g‖`
  have hadj := Wop_adj (F := F) (phiG g) g
  have hAeq : A = (pairLaw (F := F)).expect (fun b => Wop (phiG g) b * g b) := by
    rw [hadj, hA, div_eq_inv_mul]
    congr 1
    exact sum_congr rfl fun y _ => by ring
  have hW := Wop_sq (F := F) hF (phiG g) (phiG_mean hF g hg0)
  have hWn : nrm (pairLaw (F := F)) (Wop (phiG g)) ^ 2 = c * A := by
    rw [nrm_sq_expect, hW]
  have hcs : A ≤ nrm (pairLaw (F := F)) (Wop (phiG g)) * nrm (pairLaw (F := F)) g := by
    rw [hAeq]
    have := abs_ip_le (pairLaw (F := F)) (Wop (phiG g)) g
    unfold ip at this
    exact (le_abs_self _).trans this
  have hsq : A ^ 2 ≤ c * A * nrm (pairLaw (F := F)) g ^ 2 := by
    have h2 := pow_le_pow_left₀ hA0 hcs 2
    rw [mul_pow, hWn] at h2
    exact h2
  by_cases hA' : A = 0
  · rw [hA']
    have : 0 ≤ c := by
      rw [hc]
      have hq : (Fintype.card F : ℝ)⁻¹ ≤ 1 / 5 := by
        have h2 : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast h5
        rw [one_div]; exact inv_anti₀ (by norm_num) h2
      have hq0 : 0 < (Fintype.card F : ℝ)⁻¹ := inv_pos.mpr hp0
      apply div_nonneg
      · apply mul_nonneg hq0.le; nlinarith
      · linarith
    positivity
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA')
    nlinarith

omit [Field F] [DecidableEq F] [Nonempty (PairT F)] in
theorem expect_sum' {ι : Type*} [Fintype ι] {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω)
    (f : ι → Ω → ℝ) : μ.expect (fun ω => ∑ k, f k ω) = ∑ k, μ.expect (f k) := by
  unfold FiniteLaw.expect
  simp only [mul_sum]
  rw [sum_comm]

variable [Nonempty (CoreT F)]

/-- **The core-pair stars `2r𝐰𝐞^*`**: `‖C ↦ ∑_k φ_g(C_k)‖ ≤ 2r‖g‖` for `g` of mean zero
(`‖𝐰‖ ≤ 1` from `core_lin_sq`, `‖𝐞^*‖ ≤ 1` from `phiG_norm`). -/
theorem corePair_norm (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (h5 : 5 ≤ Fintype.card F) (g : PairT F → ℝ) (hg0 : (pairLaw (F := F)).expect g = 0) :
    nrm (coreLaw (F := F)) (fun C => ∑ k, phiG g (C.1 k)) ≤
      2 * (Real.sqrt (Fintype.card F))⁻¹ * nrm (pairLaw (F := F)) g := by
  have hp5 : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast h5
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  have hφ0 := phiG_mean hF g hg0
  have hl := core_lin_sq hm1 hF (phiG g) hφ0 (fun _ => 1)
  simp only [one_mul, one_pow, sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one] at hl
  have hn := phiG_norm hF h5 g hg0
  set A := (∑ y, phiG g y ^ 2) / Fintype.card F
  have hA0 : 0 ≤ A := div_nonneg (sum_nonneg fun y _ => sq_nonneg _) hp0.le
  have hcoef : ((4 : ℕ) : ℝ) - (((4 : ℕ) : ℝ) ^ 2 - (4 : ℕ)) / ((Fintype.card F : ℝ) - 1) ≤ 4 := by
    have : 0 ≤ (((4 : ℕ) : ℝ) ^ 2 - (4 : ℕ)) / ((Fintype.card F : ℝ) - 1) :=
      div_nonneg (by norm_num) (by linarith)
    push_cast at this ⊢
    linarith
  have hq : (Fintype.card F : ℝ)⁻¹ * (1 - 2 * (Fintype.card F : ℝ)⁻¹ - (Fintype.card F : ℝ)⁻¹ ^ 2) /
      (1 - (Fintype.card F : ℝ)⁻¹) ≤ (Fintype.card F : ℝ)⁻¹ := by
    have hq0 : 0 < (Fintype.card F : ℝ)⁻¹ := inv_pos.mpr hp0
    have hq1 : (Fintype.card F : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hsq : nrm (coreLaw (F := F)) (fun C => ∑ k, phiG g (C.1 k)) ^ 2 ≤
      (2 * (Real.sqrt (Fintype.card F))⁻¹) ^ 2 * nrm (pairLaw (F := F)) g ^ 2 := by
    rw [nrm_sq_expect, hl]
    have hr2 : (2 * (Real.sqrt (Fintype.card F))⁻¹) ^ 2 = 4 * (Fintype.card F : ℝ)⁻¹ := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hp0.le]; ring
    rw [hr2]
    have hg2 : 0 ≤ nrm (pairLaw (F := F)) g ^ 2 := sq_nonneg _
    calc (((4 : ℕ) : ℝ) - (((4 : ℕ) : ℝ) ^ 2 - (4 : ℕ)) / ((Fintype.card F : ℝ) - 1)) * A
        ≤ 4 * A := mul_le_mul_of_nonneg_right hcoef hA0
      _ ≤ 4 * ((Fintype.card F : ℝ)⁻¹ * nrm (pairLaw (F := F)) g ^ 2) := by
          have := hn.trans (mul_le_mul_of_nonneg_right hq hg2)
          linarith
      _ = 4 * (Fintype.card F : ℝ)⁻¹ * nrm (pairLaw (F := F)) g ^ 2 := by ring
  exact nrm_le_of_sq_le _ _ (by positivity) hsq

/-- **`hB` from the nonstar bound** (`prop:l20-pair-gap`, `l_g = 2r + N_A`): on the mean-zero
functions of the pair orthogonal to the range of `𝐯'`, if the nonstar part satisfies
`‖C ↦ E_b[N(C; b)g(b)]‖ ≤ N_A‖g‖`, then `‖𝖱_c g‖ ≤ (2r + N_A)‖g‖`. -/
theorem hB_of_nonstar (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (h5 : 5 ≤ Fintype.card F) {NA : ℝ}
    (hN : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
        NA * nrm (pairLaw (F := F)) g)
    (g : PairT F → ℝ) (hg0 : (pairLaw (F := F)).expect g = 0)
    (horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) :
    nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc g) ≤
      (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) * nrm (pairLaw (F := F)) g := by
  have e : recOp (pairLaw (F := F)) Rc g = fun C =>
      (pairLaw (F := F)).expect (fun b => Nrect C b * g b) + ∑ k, phiG g (C.1 k) := by
    funext C
    rw [Rc_complement g hg0 horth C]
    unfold phiG Nrect
    rw [← expect_sum' (pairLaw (F := F))
      (fun k b => chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k) * g b), ← FiniteLaw.expect_add]
    refine (pairLaw (F := F)).expect_congr fun b => ?_
    have hs : ∑ k, chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k) * g b =
        (∑ k, chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k)) * g b := by rw [sum_mul]
    rw [hs]
    ring
  rw [e]
  refine (nrm_add_le _ _ _).trans ?_
  have h1 := hN g hg0 horth
  have h2 := corePair_norm hm1 hF h5 g hg0
  linarith

end Sarkozy.L20Cap

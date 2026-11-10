module

public import Sarkozy.NormBoundsPaper3.MatchPrime

@[expose] public section

/-!
# The reference matching law `K^E_0` on triples and its centred norm (NB3)

`paper/sections/21_middle_records.tex`, `subsec:record:e_side`: "At `ι` the reference's two-layer
matching record is the uniform law of pairs of disjoint halves, `K^E_0 = I_×/z^E_0`, with both half
marginals `ν_E`"; `lem:record:e-law`(b): "on mean-zero functions `K^E_0` has norm at most
`k^E_old = 9q/(1 − 9q)` … the Schur test with row sums `E_y(1 − I_×) ≤ 9q`".

V1's `E` law (six injective labels) read at the two layers is `C0`:

* `C0_eq`: `C0 x y = [asm x y injective]/|Inj|` (the graph has no edges);
* `C0_row`, `C0_col`: both half marginals are `ν_E` (`tw_match`);
* `F6`: the number of halves disjoint from an injective half; `F6_lower`: `F6 ≥ M − 9p²`
  (`M = p(p − 1)(p − 2)`; each of the nine coincidences `x_i = y_j` has at most `p²` solutions);
* **`C0_form`**: on mean-zero `u, v`, `|⟨u, C0 v⟩| ≤ 2(1 − F6/M) ‖u‖ ‖v‖` (Schur's test on the
  centred kernel); **`C0_centred`**: the centred norm of `K^E_0` is at most `18p/((p − 1)(p − 2))`
  for `p ≥ 23` (a crude form of the paper's `k^E_p = 3/(p − 3)`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper2 (centredNorm_of_form schur_le)
open Sarkozy.SignedGram (CentredNorm)

variable {p : ℕ} [Fact p.Prime]

section Old

variable (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)

/-- **`K^E_0` read at the two layers.** -/
noncomputable def C0 : Matrix ((ZMod p × ZMod p) × ZMod p) ((ZMod p × ZMod p) × ZMod p) ℝ :=
  cmT (graphLaw (matchGraph (Fin 2)) hne) (lay 0) (lay 1)

theorem C0_nonneg (x y : (ZMod p × ZMod p) × ZMod p) : 0 ≤ C0 hne x y := cmT_nonneg _ _ _ x y

theorem C0_row (hp : 3 ≤ p) (x : (ZMod p × ZMod p) × ZMod p) : ∑ y, C0 hne x y = m3 p x := by
  unfold C0; rw [cmT_row, tw_match hne hp]

theorem C0_col (hp : 3 ≤ p) (y : (ZMod p × ZMod p) × ZMod p) : ∑ x, C0 hne x y = m3 p y := by
  unfold C0; rw [cmT_col, tw_match hne hp]

/-- `[asm x y injective]`. -/
noncomputable def ind6 (x y : (ZMod p × ZMod p) × ZMod p) : ℝ :=
  if Function.Injective (asm x y) then 1 else 0

/-- The number of injective two-layer labellings. -/
noncomputable def NL : ℝ := ((injLabellings (ZMod p) (matchGraph (Fin 2))).card : ℝ)

theorem NL_pos (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) :
    0 < NL (p := p) := by
  unfold NL; exact_mod_cast card_pos.mpr hne

theorem mem_inj_iff (z : Fin 3 × Fin 2 → ZMod p) :
    z ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) ↔ Function.Injective z := by
  rw [mem_injLabellings_iff_feasible]
  constructor
  · rintro ⟨h1, -⟩ u v e
    exact h1 u (mem_univ _) v (mem_univ _) e
  · intro h
    exact ⟨fun u _ v _ e => h e, fun e he => absurd he (Finset.notMem_empty _)⟩

theorem C0_eq (x y : (ZMod p × ZMod p) × ZMod p) : C0 hne x y = ind6 x y / NL (p := p) := by
  unfold C0 cmT
  rw [sum_eq_single (asm x y)]
  · rw [ite_eq_left_iff.mpr (fun h => absurd ((rd_asm_iff _ x y).mpr rfl) h), mul_one]
    change (if asm x y ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) then
      1 / ((injLabellings (ZMod p) (matchGraph (Fin 2))).card : ℝ) else 0) = _
    unfold ind6 NL
    by_cases hz : Function.Injective (asm x y)
    · simp [(mem_inj_iff _).mpr hz, hz]
    · simp [mt (mem_inj_iff _).mp hz, hz]
  · intro z _ hz
    rw [ite_eq_right_iff.mpr (fun h => absurd ((rd_asm_iff z x y).mp h) hz), mul_zero]
  · exact fun h => absurd (mem_univ _) h

end Old

omit [Fact p.Prime] in
theorem ind6_le (x y : (ZMod p × ZMod p) × ZMod p) : ind6 x y ≤ ind3 x * ind3 y := by
  unfold ind6
  by_cases hz : Function.Injective (asm x y)
  · have hx : Inj3 x := by
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
      · exact absurd (hz (show asm x y (0, 0) = asm x y (1, 0) from e)) (by decide)
      · exact absurd (hz (show asm x y (2, 0) = asm x y (0, 0) from e)) (by decide)
      · exact absurd (hz (show asm x y (2, 0) = asm x y (1, 0) from e)) (by decide)
    have hy : Inj3 y := by
      refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
      · exact absurd (hz (show asm x y (0, 1) = asm x y (1, 1) from e)) (by decide)
      · exact absurd (hz (show asm x y (2, 1) = asm x y (0, 1) from e)) (by decide)
      · exact absurd (hz (show asm x y (2, 1) = asm x y (1, 1) from e)) (by decide)
    simp [hz, ind3, hx, hy]
  · simp only [hz, ↓reduceIte]
    exact mul_nonneg (ind3_nonneg x) (ind3_nonneg y)

omit [Fact p.Prime] in
theorem ind6_nonneg (x y : (ZMod p × ZMod p) × ZMod p) : 0 ≤ ind6 x y := by
  unfold ind6; split_ifs <;> norm_num

omit [Fact p.Prime] in
theorem ind6_sq (x y : (ZMod p × ZMod p) × ZMod p) : ind6 x y * ind6 x y = ind6 x y := by
  unfold ind6; split_ifs <;> norm_num

/-- `[a = b]`. -/
noncomputable def dE (a b : ZMod p) : ℝ := if a = b then 1 else 0

omit [Fact p.Prime] in
theorem dE_nonneg (a b : ZMod p) : 0 ≤ dE a b := by unfold dE; split_ifs <;> norm_num

omit [Fact p.Prime] in
theorem ne_of_dE {a b : ZMod p} (h : dE a b < 1) : a ≠ b := fun e => by simp [dE, e] at h

/-- The nine coincidences `x_i = y_j`. -/
noncomputable def coinc (x y : (ZMod p × ZMod p) × ZMod p) : ℝ :=
  dE x.1.1 y.1.1 + dE x.1.1 y.1.2 + dE x.1.1 y.2 + dE x.1.2 y.1.1 + dE x.1.2 y.1.2 +
    dE x.1.2 y.2 + dE x.2 y.1.1 + dE x.2 y.1.2 + dE x.2 y.2

omit [Fact p.Prime] in
theorem inj_asm (x y : (ZMod p × ZMod p) × ZMod p) (hx : Inj3 x) (hy : Inj3 y)
    (h00 : x.1.1 ≠ y.1.1) (h01 : x.1.1 ≠ y.1.2) (h02 : x.1.1 ≠ y.2) (h10 : x.1.2 ≠ y.1.1)
    (h11 : x.1.2 ≠ y.1.2) (h12 : x.1.2 ≠ y.2) (h20 : x.2 ≠ y.1.1) (h21 : x.2 ≠ y.1.2)
    (h22 : x.2 ≠ y.2) :
    Function.Injective (asm x y) := by
  obtain ⟨hx1, hx2, hx3⟩ := hx
  obtain ⟨hy1, hy2, hy3⟩ := hy
  rintro ⟨a, ℓ⟩ ⟨b, m⟩ e
  fin_cases a <;> fin_cases ℓ <;> fin_cases b <;> fin_cases m <;>
    simp_all [asm, eq_comm]

omit [Fact p.Prime] in
theorem ind6_ge (x y : (ZMod p × ZMod p) × ZMod p) (hx : Inj3 x) :
    ind3 y - coinc x y ≤ ind6 x y := by
  have h0 := ind6_nonneg x y
  have n1 := dE_nonneg x.1.1 y.1.1
  have n2 := dE_nonneg x.1.1 y.1.2
  have n3 := dE_nonneg x.1.1 y.2
  have n4 := dE_nonneg x.1.2 y.1.1
  have n5 := dE_nonneg x.1.2 y.1.2
  have n6 := dE_nonneg x.1.2 y.2
  have n7 := dE_nonneg x.2 y.1.1
  have n8 := dE_nonneg x.2 y.1.2
  have n9 := dE_nonneg x.2 y.2
  by_cases hy : Inj3 y
  · have hi : ind3 y = 1 := by simp [ind3, hy]
    by_cases hz : Function.Injective (asm x y)
    · have : ind6 x y = 1 := by simp [ind6, hz]
      unfold coinc; linarith
    · by_contra hlt
      push Not at hlt
      have h6 : ind6 x y = 0 := by simp [ind6, hz]
      apply hz
      unfold coinc at hlt
      apply inj_asm x y hx hy <;> apply ne_of_dE <;> linarith
  · have : ind3 y = 0 := by simp [ind3, hy]
    have : 0 ≤ coinc x y := by unfold coinc; linarith
    linarith

theorem sum_dE (c : ZMod p) : ∑ a : ZMod p, dE c a = 1 := by unfold dE; simp

theorem sd0 (c : ZMod p) : ∑ y : (ZMod p × ZMod p) × ZMod p, dE c y.1.1 = (p : ℝ) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  rw [← mul_sum, ← mul_sum, sum_dE]
  ring

theorem sd1 (c : ZMod p) : ∑ y : (ZMod p × ZMod p) × ZMod p, dE c y.1.2 = (p : ℝ) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  rw [← mul_sum, sum_dE]
  ring

theorem sd2 (c : ZMod p) : ∑ y : (ZMod p × ZMod p) × ZMod p, dE c y.2 = (p : ℝ) ^ 2 := by
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  simp only [sum_dE, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  ring

theorem sum_coinc (x : (ZMod p × ZMod p) × ZMod p) :
    ∑ y, coinc x y = 9 * (p : ℝ) ^ 2 := by
  unfold coinc
  simp only [sum_add_distrib, sd0, sd1, sd2]
  ring

section Fibre

/-- The number of halves disjoint from an injective half, `|Inj|/M`. -/
noncomputable def F6 : ℝ := NL (p := p) / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))

theorem row_ind6 (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (hp : 3 ≤ p)
    (x : (ZMod p × ZMod p) × ZMod p) :
    ∑ y, ind6 x y = ind3 x * F6 (p := p) := by
  have h := C0_row hne hp x
  simp only [C0_eq, ← sum_div] at h
  unfold m3 at h
  unfold F6
  have hM := M3_pos (p := p) hp
  have hN := NL_pos hne
  rw [div_eq_div_iff hN.ne' hM.ne'] at h
  rw [mul_div_assoc', eq_div_iff hM.ne']
  linarith

theorem col_ind6 (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (hp : 3 ≤ p)
    (y : (ZMod p × ZMod p) × ZMod p) :
    ∑ x, ind6 x y = ind3 y * F6 (p := p) := by
  have h := C0_col hne hp y
  simp only [C0_eq, ← sum_div] at h
  unfold m3 at h
  unfold F6
  have hM := M3_pos (p := p) hp
  have hN := NL_pos hne
  rw [div_eq_div_iff hN.ne' hM.ne'] at h
  rw [mul_div_assoc', eq_div_iff hM.ne']
  linarith

theorem F6_le (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (hp : 3 ≤ p) :
    F6 (p := p) ≤ (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) := by
  obtain ⟨x, hx⟩ : ∃ x : (ZMod p × ZMod p) × ZMod p, Inj3 x := by
    have h := sum_ind3 (p := p)
    by_contra hc
    push Not at hc
    have : ∑ x : (ZMod p × ZMod p) × ZMod p, ind3 x = 0 :=
      sum_eq_zero fun x _ => by unfold ind3; simp [hc x]
    have := M3_pos (p := p) hp
    linarith
  have h := row_ind6 hne hp x
  have hix : ind3 x = 1 := by unfold ind3; simp [hx]
  rw [hix, one_mul] at h
  rw [← h, ← sum_ind3]
  exact sum_le_sum fun y _ => (ind6_le x y).trans (by rw [hix, one_mul])

theorem F6_lower (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (hp : 3 ≤ p) :
    (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) - 9 * (p : ℝ) ^ 2 ≤ F6 (p := p) := by
  obtain ⟨x, hx⟩ : ∃ x : (ZMod p × ZMod p) × ZMod p, Inj3 x := by
    have h := sum_ind3 (p := p)
    by_contra hc
    push Not at hc
    have : ∑ x : (ZMod p × ZMod p) × ZMod p, ind3 x = 0 :=
      sum_eq_zero fun x _ => by unfold ind3; simp [hc x]
    have := M3_pos (p := p) hp
    linarith
  have h := row_ind6 hne hp x
  have hix : ind3 x = 1 := by unfold ind3; simp [hx]
  rw [hix, one_mul] at h
  rw [← h, ← sum_ind3, ← sum_coinc x, ← sum_sub_distrib]
  exact sum_le_sum fun y _ => ind6_ge x y hx

/-- **The form of `K^E_0` on mean-zero functions** (Schur's test on the centred kernel). -/
theorem C0_form (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (hp : 3 ≤ p)
    (u v : (ZMod p × ZMod p) × ZMod p → ℝ)
    (hu : ∑ x, m3 p x * u x = 0) (hv : ∑ x, m3 p x * v x = 0) :
    |u ⬝ᵥ (C0 hne *ᵥ v)| ≤ 2 * (1 - F6 (p := p) / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) *
      Real.sqrt (∑ x, m3 p x * u x ^ 2) * Real.sqrt (∑ x, m3 p x * v x ^ 2) := by
  have hM0 := (M3_pos (p := p) hp).ne'
  have hNL : NL (p := p) = F6 (p := p) * ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
    unfold F6; rw [div_mul_cancel₀ _ hM0]
  set M := (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)
  have hM : 0 < M := M3_pos hp
  have hN := NL_pos hne
  set c := F6 (p := p) / M
  have hF0 : 0 ≤ F6 (p := p) := by unfold F6; exact div_nonneg hN.le hM.le
  have hc0 : 0 ≤ c := div_nonneg hF0 hM.le
  have hc1 : c ≤ 1 := by rw [div_le_one hM]; exact F6_le hne hp
  -- the centred kernel on the injective triples
  set U : (ZMod p × ZMod p) × ZMod p → ℝ := fun x => ind3 x * u x
  set V : (ZMod p × ZMod p) × ZMod p → ℝ := fun x => ind3 x * v x
  set K : (ZMod p × ZMod p) × ZMod p → (ZMod p × ZMod p) × ZMod p → ℝ :=
    fun x y => ind6 x y - c * (ind3 x * ind3 y)
  have hU0 : ∑ x, U x = 0 := by rw [m3_sum_eq hp, hu, mul_zero]
  have hV0 : ∑ x, V x = 0 := by rw [m3_sum_eq hp, hv, mul_zero]
  have hform : u ⬝ᵥ (C0 hne *ᵥ v) = (1 / NL (p := p)) * ∑ x, ∑ y, U x * K x y * V y := by
    have e1 : ∑ x, ∑ y, U x * (ind3 x * ind3 y) * V y = 0 := by
      have : ∀ x, ∑ y, U x * (ind3 x * ind3 y) * V y = U x * ind3 x * ∑ y, ind3 y * V y := by
        intro x; rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
      simp only [this]
      have h2 : ∑ y, ind3 y * V y = ∑ y, V y := sum_congr rfl fun y _ => by
        simp only [V]; rw [← mul_assoc, ind3_mul_self]
      rw [h2, hV0]; simp
    have e2 : ∑ x, ∑ y, U x * ind6 x y * V y = ∑ x, ∑ y, u x * ind6 x y * v y := by
      refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
      have h1 := ind6_le x y
      have h0 := ind6_nonneg x y
      simp only [U, V]
      by_cases hx : Inj3 x <;> by_cases hy : Inj3 y
      · simp [ind3, hx, hy]
      · have : ind6 x y = 0 := by
          have : ind3 y = 0 := by simp [ind3, hy]
          rw [this, mul_zero] at h1; linarith
        simp [this]
      · have : ind6 x y = 0 := by
          have : ind3 x = 0 := by simp [ind3, hx]
          rw [this, zero_mul] at h1; linarith
        simp [this]
      · have : ind6 x y = 0 := by
          have : ind3 x = 0 := by simp [ind3, hx]
          rw [this, zero_mul] at h1; linarith
        simp [this]
    have e3 : ∑ x, ∑ y, U x * K x y * V y =
        ∑ x, ∑ y, U x * ind6 x y * V y - c * ∑ x, ∑ y, U x * (ind3 x * ind3 y) * V y := by
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun x _ => ?_
      rw [mul_sum, ← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by simp only [K]; ring
    rw [e3, e1, mul_zero, sub_zero, e2]
    simp only [dotProduct, Matrix.mulVec, C0_eq, mul_sum]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    ring
  -- Schur's test
  have hKa : ∀ x y, |K x y| = ind6 x y * (1 - c) + (ind3 x * ind3 y - ind6 x y) * c := by
    intro x y
    have h1 := ind6_le x y
    simp only [K]
    unfold ind6 at h1 ⊢
    by_cases hz : Function.Injective (asm x y)
    · simp only [hz, ↓reduceIte] at h1 ⊢
      have : ind3 x * ind3 y = 1 := by
        have a := ind3_le_one x
        have b := ind3_le_one y
        have a0 := ind3_nonneg x
        have b0 := ind3_nonneg y
        nlinarith
      rw [this, abs_of_nonneg (by linarith)]
      ring
    · simp only [hz, ↓reduceIte] at h1 ⊢
      have a0 := ind3_nonneg x
      have b0 := ind3_nonneg y
      rw [abs_of_nonpos (by nlinarith)]
      ring
  set R := 2 * F6 (p := p) * (1 - c)
  have hrow : ∀ x, ∑ y, |K x y| ≤ R := by
    intro x
    simp only [hKa, sum_add_distrib, ← sum_mul, sum_sub_distrib, ← mul_sum, row_ind6 hne hp,
      sum_ind3]
    have a := ind3_le_one x
    have a0 := ind3_nonneg x
    have hcM : c * M = F6 (p := p) := by simp only [c]; field_simp
    have e : ind3 x * F6 (p := p) * (1 - c) + (ind3 x * M - ind3 x * F6 (p := p)) * c =
        ind3 x * R := by simp only [R]; rw [← hcM]; ring
    rw [e]
    have : 0 ≤ R := by
      simp only [R]; exact mul_nonneg (mul_nonneg (by norm_num) hF0) (by linarith)
    nlinarith
  have hcol : ∀ y, ∑ x, |K x y| ≤ R := by
    intro y
    simp only [hKa, sum_add_distrib, ← sum_mul, sum_sub_distrib, col_ind6 hne hp,
      sum_ind3]
    have a := ind3_le_one y
    have a0 := ind3_nonneg y
    have hcM : c * M = F6 (p := p) := by simp only [c]; field_simp
    have e : ind3 y * F6 (p := p) * (1 - c) + (M * ind3 y - ind3 y * F6 (p := p)) * c =
        ind3 y * R := by simp only [R]; rw [← hcM]; ring
    rw [e]
    have : 0 ≤ R := by
      simp only [R]; exact mul_nonneg (mul_nonneg (by norm_num) hF0) (by linarith)
    nlinarith
  have hR0 : 0 ≤ R := mul_nonneg (mul_nonneg (by norm_num) hF0) (by linarith)
  have hS := schur_le (fun x y => |K x y|) (fun x y => abs_nonneg _) hR0 hrow hcol U V
  have hUU : ∑ x, U x ^ 2 = M * ∑ x, m3 p x * u x ^ 2 := by
    rw [← m3_sq_eq hp]
    exact sum_congr rfl fun x _ => by simp only [U]; rw [mul_pow, sq (ind3 x), ind3_mul_self]
  have hVV : ∑ x, V x ^ 2 = M * ∑ x, m3 p x * v x ^ 2 := by
    rw [← m3_sq_eq hp]
    exact sum_congr rfl fun x _ => by simp only [V]; rw [mul_pow, sq (ind3 x), ind3_mul_self]
  have habs : |∑ x, ∑ y, U x * K x y * V y| ≤ ∑ x, ∑ y, |U x| * |K x y| * |V y| :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => (abs_sum_le_sum_abs _ _).trans
      (le_of_eq (sum_congr rfl fun y _ => by rw [abs_mul, abs_mul])))
  rw [hUU, hVV, Real.sqrt_mul hM.le, Real.sqrt_mul hM.le] at hS
  have hMs : Real.sqrt M * Real.sqrt M = M := Real.mul_self_sqrt hM.le
  rw [hform, abs_mul, abs_of_pos (one_div_pos.mpr hN)]
  have hF6pos : 0 < F6 (p := p) := by rw [hNL] at hN; exact pos_of_mul_pos_left hN hM.le
  calc 1 / NL (p := p) * |∑ x, ∑ y, U x * K x y * V y|
      ≤ 1 / NL (p := p) * (R * (Real.sqrt M * Real.sqrt (∑ x, m3 p x * u x ^ 2)) *
          (Real.sqrt M * Real.sqrt (∑ x, m3 p x * v x ^ 2))) :=
        mul_le_mul_of_nonneg_left (habs.trans hS) (one_div_pos.mpr hN).le
    _ = (R * (Real.sqrt M * Real.sqrt M) / NL (p := p)) * Real.sqrt (∑ x, m3 p x * u x ^ 2) *
          Real.sqrt (∑ x, m3 p x * v x ^ 2) := by ring
    _ = _ := by
        rw [hMs, hNL]
        simp only [R]
        field_simp

/-- **The centred norm of `K^E_0`**: at most `18p/((p − 1)(p − 2))`. -/
theorem C0_centred (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (hp : 3 ≤ p) :
    CentredNorm (m3 p) (C0 hne) (18 * (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
  have hp' : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have hM := M3_pos (p := p) hp
  have h12 : 0 < ((p : ℝ) - 1) * ((p : ℝ) - 2) := by nlinarith
  refine centredNorm_of_form (m3_nonneg hp) (C0_nonneg hne) (C0_row hne hp) (C0_col hne hp)
    (by positivity) fun u v hu hv => ?_
  refine ((C0_form hne hp u v hu hv).trans ?_)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  have hL := F6_lower hne hp
  have e : 18 * (p : ℝ) / (((p : ℝ) - 1) * ((p : ℝ) - 2)) =
      2 * (9 * (p : ℝ) ^ 2 / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))) := by
    field_simp
    ring
  rw [e]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  rw [sub_le_comm, one_sub_div hM.ne', div_le_div_iff_of_pos_right hM]
  linarith

end Fibre

end Sarkozy.NormBoundsPaper3

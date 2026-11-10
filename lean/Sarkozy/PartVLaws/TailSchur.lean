module

public import Sarkozy.PartVLaws.TailCounts
public import Sarkozy.PartVLaws.TailInputs

@[expose] public section

/-!
# The Schur rows of the tail datum, reduced to the correlations (`it:record:upper-F5`(b))

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`, items (F1), (F3), (F4),
(F5)(b); `paper/sections/27_tail_index.tex`, proof of `lem:tail-law`(i) ("the rows are those of
(F5)(b), with `t_Y = 1/50` and `M = 21/20`").

The Schur-row data (`SchurRowData`) of a row datum have ten fields. For the two-layer row data of
the coordinate `0` of the tail law at a prime `p ≥ P₄`, under H1, eight of them are now proved:
* `nonneg` and `exactE` (structural: `TF_nonneg`, `rowD0_exactE`);
* the mass bounds, with `H = ρ^{144}`, `ρ = 1 + 2²⁸/√p` (`tail_foldMass_bounds`, (F3));
* the marginal densities `φ₀ = T_F^b 𝟙/m_b`, `φ₂ = (T_F^b)^* 𝟙/m_b` at most `R_m = ρ^{288}`, and
  their distance to `𝟙` at most `υ = ρ^{288} - 1` (`tail_margL_le`, `tail_margR_le`,
  `tail_devL`, `tail_devR`, from `tail_kone_bounds`, `tail_kone'_bounds`; (F1)).

The remaining two are the **correlations** (F4): the maximal correlation `ρ_F` of the fold kernel
and the bound `‖T_E^b - J‖ ≤ ρ_E`. **`tail_schurInputs_of_correlations`** gives the Schur inputs
`SchurInputs` of the tail datum (the hypothesis of `tailLaw_familyPositive_schur`) from them
alone, with `H ≤ 50` and `H + 1/50 ≤ M` proved; the two remaining inequalities are the paper's
`f_Schur ≤ f_φ`, `ρ_E/r ≤ h_φ` with these `H, R_m, υ`.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

omit [DecidableEq 𝔛] in
/-- The `L²(μ)` norm of a function is at most its sup on the support. -/
theorem nrm_le_of_abs_le (μ : FiniteLaw 𝔛) (f : 𝔛 → ℝ) {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ x, μ.weight x ≠ 0 → |f x| ≤ c) : nrm μ f ≤ c := by
  unfold nrm ip FiniteLaw.expect
  have hsum : ∑ x, μ.weight x * (f x * f x) ≤ c ^ 2 := by
    calc ∑ x, μ.weight x * (f x * f x) ≤ ∑ x, μ.weight x * c ^ 2 := by
          refine sum_le_sum fun x _ => ?_
          by_cases hx : μ.weight x = 0
          · rw [hx, zero_mul, zero_mul]
          · refine mul_le_mul_of_nonneg_left ?_ (μ.nonneg x)
            have := h x hx
            rw [← sq, ← sq_abs]
            exact pow_le_pow_left₀ (abs_nonneg _) this 2
      _ = c ^ 2 := by rw [← sum_mul, μ.total, one_mul]
  calc Real.sqrt (∑ x, μ.weight x * (f x * f x)) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsum
    _ = c := Real.sqrt_sq hc

theorem abs_sub_one_le {a z : ℝ} (ha : 1 ≤ a) (hz1 : a⁻¹ ≤ z) (hz2 : z ≤ a) : |z - 1| ≤ a - 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le zero_lt_one ha
  have hinv : 1 - a⁻¹ ≤ a - 1 := by
    have : a⁻¹ ≤ 1 := inv_le_one_of_one_le₀ ha
    have h2 : a⁻¹ * a = 1 := inv_mul_cancel₀ ha0.ne'
    nlinarith
  rw [abs_le]
  constructor <;> linarith

section Tail

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f' : FieldTy)

/-- The ratio bounds of a quotient. -/
theorem div_bounds {u v ρ : ℝ} (hρ : 1 ≤ ρ) (hu1 : ρ⁻¹ ≤ u) (hu2 : u ≤ ρ) (hv1 : ρ⁻¹ ≤ v)
    (hv2 : v ≤ ρ) : (ρ ^ 2)⁻¹ ≤ u / v ∧ u / v ≤ ρ ^ 2 := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le zero_lt_one hρ
  have hv0 : 0 < v := lt_of_lt_of_le (inv_pos.mpr hρ0) hv1
  constructor
  · rw [le_div_iff₀ hv0]
    calc (ρ ^ 2)⁻¹ * v ≤ (ρ ^ 2)⁻¹ * ρ := mul_le_mul_of_nonneg_left hv2 (by positivity)
      _ = ρ⁻¹ := by field_simp
      _ ≤ u := hu1
  · rw [div_le_iff₀ hv0]
    calc u ≤ ρ := hu2
      _ = ρ ^ 2 * ρ⁻¹ := by field_simp
      _ ≤ ρ ^ 2 * v := mul_le_mul_of_nonneg_left hv1 (by positivity)

/-- **The left marginal density of the tail fold kernel** is within `[ρ^{-288}, ρ^{288}]`. -/
theorem tail_margL_bounds (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (b : f'.Obj × ZMod 2 → ZMod p)
    (hb : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0)
    (x : f'.Obj × ZMod 2 → ZMod p)
    (hx : ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b).weight x ≠ 0) :
    (countRho p ^ 288)⁻¹ ≤ margL ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) x ∧
      margL ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) x ≤ countRho p ^ 288 := by
  obtain ⟨k1, k2⟩ := tail_kone_bounds p hne f' hW hp h b hb x hx
  obtain ⟨m1, m2⟩ := tail_foldMass_bounds p hne f' hW hp h b hb
  have hρ : 1 ≤ countRho p ^ 144 := one_le_pow₀ (one_le_countRho p)
  have := div_bounds hρ k1 k2 m1 m2
  rw [← pow_mul] at this
  exact this

/-- **The right marginal density of the tail fold kernel** is within `[ρ^{-288}, ρ^{288}]`. -/
theorem tail_margR_bounds (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (b : f'.Obj × ZMod 2 → ZMod p)
    (hb : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0)
    (y : f'.Obj × ZMod 2 → ZMod p)
    (hy : ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b).weight y ≠ 0) :
    (countRho p ^ 288)⁻¹ ≤ margR ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) y ∧
      margR ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) y ≤ countRho p ^ 288 := by
  obtain ⟨k1, k2⟩ := tail_kone'_bounds p hne f' hW hp h b hb y hy
  obtain ⟨m1, m2⟩ := tail_foldMass_bounds p hne f' hW hp h b hb
  have hρ : 1 ≤ countRho p ^ 144 := one_le_pow₀ (one_le_countRho p)
  have := div_bounds hρ k1 k2 m1 m2
  rw [← pow_mul] at this
  exact this

/-- **The count-type Schur-row data of the tail rows** (`SchurRowData` minus the correlations):
the mass, the marginal densities and their distance to `𝟙`. -/
theorem tail_schurRowData (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (b : f'.Obj × ZMod 2 → ZMod p)
    (hb : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0) {ρF ρE : ℝ}
    (hcorr : ∀ g g' : (f'.Obj × ZMod 2 → ZMod p) → ℝ,
      |kf ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        (covKernel ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
          ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)) g g'| ≤
        ρF * Real.sqrt (wvar ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
          (margL ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
            ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)) g) *
        Real.sqrt (wvar ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
          (margR ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
            ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)) g'))
    (hnormE : NormBound ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
      ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TE b) ρE) :
    SchurRowData ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
      ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)
      ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TE b)
      (countRho p ^ 144) (countRho p ^ 288 - 1) (countRho p ^ 288) ρF ρE := by
  obtain ⟨m1, m2⟩ := tail_foldMass_bounds p hne f' hW hp h b hb
  have hρ288 : 1 ≤ countRho p ^ 288 := one_le_pow₀ (one_le_countRho p)
  have hυ : 0 ≤ countRho p ^ 288 - 1 := by linarith
  refine ⟨m1, m2, (rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF_nonneg b,
    fun x hx => (tail_margL_bounds p hne f' hW hp h b hb x hx).2,
    fun y hy => (tail_margR_bounds p hne f' hW hp h b hb y hy).2, ?_, ?_, hcorr,
    rowD0_exactE _ f' h b hb, hnormE⟩
  · refine nrm_le_of_abs_le _ _ hυ fun x hx => ?_
    obtain ⟨l1, l2⟩ := tail_margL_bounds p hne f' hW hp h b hb x hx
    exact abs_sub_one_le hρ288 l1 l2
  · refine nrm_le_of_abs_le _ _ hυ fun y hy => ?_
    obtain ⟨l1, l2⟩ := tail_margR_bounds p hne f' hW hp h b hb y hy
    exact abs_sub_one_le hρ288 l1 l2

/-- `ρ^{144} ≤ 1 + 2⁻²⁰⁰` at the tail primes. -/
theorem countRho_pow_le (hp : P4 ≤ p) {n : ℕ} (hn : n ≤ 288) :
    countRho p ^ n ≤ 1 + 1 / 2 ^ 200 := by
  have hs := sqrt_ge_of_P4 p hp
  rw [ZMod.card] at hs
  have hs0 : (0 : ℝ) < Real.sqrt p := lt_of_lt_of_le (by positivity) hs
  have hε : (0 : ℝ) ≤ 2 ^ 28 / Real.sqrt p := div_nonneg (by positivity) hs0.le
  have hsmall : (2 : ℝ) ^ 28 / Real.sqrt p ≤ 1 / 2 ^ 228 := by
    rw [div_le_div_iff₀ hs0 (by positivity)]
    calc (2 : ℝ) ^ 28 * 2 ^ 228 = 2 ^ 256 := by norm_num
      _ ≤ Real.sqrt p := hs
      _ = 1 * Real.sqrt p := (one_mul _).symm
  have hn' : (n : ℝ) ≤ 288 := by exact_mod_cast hn
  have hnε : (n : ℝ) * (2 ^ 28 / Real.sqrt p) ≤ 1 / 2 := by
    calc (n : ℝ) * (2 ^ 28 / Real.sqrt p) ≤ 288 * (1 / 2 ^ 228) :=
          mul_le_mul hn' hsmall hε (by norm_num)
      _ ≤ 1 / 2 := by norm_num
  have h1 := one_add_pow_le hε n hnε
  unfold countRho
  calc (1 + 2 ^ 28 / Real.sqrt p) ^ n ≤ 1 + 2 * n * (2 ^ 28 / Real.sqrt p) := h1
    _ ≤ 1 + 2 * 288 * (1 / 2 ^ 228) := by
        have : 2 * (n : ℝ) * (2 ^ 28 / Real.sqrt p) ≤ 2 * 288 * (1 / 2 ^ 228) := by
          have h2 : 2 * (n : ℝ) ≤ 2 * 288 := by linarith
          exact mul_le_mul h2 hsmall hε (by norm_num)
        linarith
    _ ≤ 1 + 1 / 2 ^ 200 := by norm_num

/-- **The Schur inputs of the tail rows from the correlations alone** (`it:record:upper-F5`(b),
`lem:tail-law`(i) for this family of rows): at every prime `p ≥ P₄`, under Weil's bound, if at
every middle value the fold kernel has maximal correlation at most `ρ_F` and the matching kernel
`‖T_E^b - J‖ ≤ ρ_E` ((F4)), and the paper's two inequalities `f_Schur ≤ f_φ`, `ρ_E/r ≤ h_φ` hold
with the counted constants `H = ρ^{144}`, `R_m = ρ^{288}`, `υ = ρ^{288} - 1`, then the two-layer
rows of the coordinate `0` at `𝔣'` have the Schur inputs of the tail datum. -/
theorem tail_schurInputs_of_correlations (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') {ρF ρE : ℝ} (hρF : 0 ≤ ρF)
    (hcorr : ∀ b, (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0 →
      ∀ g g' : (f'.Obj × ZMod 2 → ZMod p) → ℝ,
      |kf ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        (covKernel ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
          ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)) g g'| ≤
        ρF * Real.sqrt (wvar ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
          (margL ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
            ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)) g) *
        Real.sqrt (wvar ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
          (margR ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
            ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b)) g'))
    (hnormE : ∀ b, (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0 →
      NormBound ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TE b) ρE)
    (hf : (countRho p ^ 144 * countRho p ^ 288 * ρF +
        (countRho p ^ 144 + 50 * (countRho p ^ 144) ^ 2) * (countRho p ^ 288 - 1) ^ 2) /
          tailR p ≤ ((tailOrd f').f : ℝ))
    (hh : ρE / tailR p ≤ ((tailOrd f').h : ℝ)) :
    SchurInputs (rowD0 (lam2 (tailFieldLaws p hne)) f' h) (tailR p) (tailOrd f') := by
  have hH1 : 1 ≤ countRho p ^ 144 := one_le_pow₀ (one_le_countRho p)
  have hH2 := countRho_pow_le p hp (n := 144) (by norm_num)
  have hM : ((tailOrd f').M : ℝ) = 21 / 20 := by
    cases f' <;> norm_num [tailOrd, tailOrdinary, toFType]
  refine ⟨countRho p ^ 144, countRho p ^ 288 - 1, countRho p ^ 288, ρF, ρE,
    lt_of_lt_of_le zero_lt_one hH1, ?_, ?_, le_trans zero_le_one (one_le_pow₀ (one_le_countRho p)),
    hρF, hf, hh, fun b hb => tail_schurRowData p hne f' hW hp h b hb (hcorr b hb) (hnormE b hb)⟩
  · have : (1 : ℝ) + 1 / 2 ^ 200 ≤ 50 := by norm_num
    linarith
  · rw [hM]
    have : (1 : ℝ) + 1 / 2 ^ 200 + 1 / 50 ≤ 21 / 20 := by norm_num
    linarith

end Tail

end Sarkozy.PartVLaws

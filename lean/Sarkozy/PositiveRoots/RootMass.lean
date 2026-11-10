module

public import Sarkozy.PositiveRoots.SquareL20

@[expose] public section

/-!
# The mass of the rectangle in the linear prices (`lem:root-linear`, "Linear prices")

`paper/sections/20b_positive_roots.tex`, the paragraph "Linear prices" before `lem:root-linear`:

* `Kbar_expansion`: **"in the expansion of `\bar𝖪 − 1` the single terms vanish and the pair terms
  sum to exactly `2q`"**: for a core with distinct labels,
  `\bar𝖪 − 1 = 2q + E_z ∑_{|S| ≥ 3} σ_Sψ_S(z)` (the higher terms are the `𝒲/p` of
  `lem:record:weighted-moment`); `sig_pairs`: `∑_{|S| = 2} σ_S = −2` for the signs
  `(−1, −1, 1, 1)`, by `decide`;
* `rmass_sub_one`: **`(1 − q)(𝔯 − 1) = (\bar𝖪 − 1)(\bar𝖪 + 1 − 16q) − 15q`** (from W3's
  `rmass_eq`);
* `nrm_rmass_sub_one_le`: **`‖𝔯 − 1‖₂ ≤ d_𝔯 = ((2 + η + 16q)d_𝖪 + 15q)/(1 − q)`**, given
  `‖\bar𝖪 − 1‖₂ ≤ d_𝖪` (`lem:record:weighted-moment`(b), a hypothesis) and `|\bar𝖪 − 1| ≤ η`
  (W3's `Kbar_dev`, Weil).

The bound `d_𝖪` itself (the density `P_adm D₄/Z₄` and `lem:record:weighted-moment`(b)) and the
multiplier claims `‖f𝒰_S‖ ≤ ‖f‖₂/√(1 − q)` (`lem:spec:affpair`(d)) are not formalized here.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Cuts Sarkozy.Recentering Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The core signs as integers. -/
def sgnZ4 : Fin 4 → ℤ := ![-1, -1, 1, 1]

theorem sig_eq_int (S : Finset (Fin 4)) : sig S = ((∏ k ∈ S, sgnZ4 k : ℤ) : ℝ) := by
  unfold sig
  push_cast
  refine Finset.prod_congr rfl fun k _ => ?_
  fin_cases k <;> simp [sgn, sgnZ4]

theorem sig_pairs_int : ∑ S ∈ higher.filter (fun S : Finset (Fin 4) => S.card = 2),
    ∏ k ∈ S, sgnZ4 k = -2 := by decide

/-- `∑_{|S| = 2} σ_S = −2` for the core signs `s = (−1, −1, 1, 1)`. -/
theorem sig_pairs : ∑ S ∈ higher.filter (fun S : Finset (Fin 4) => S.card = 2), sig S = -2 := by
  simp only [sig_eq_int]
  rw [← Int.cast_sum, sig_pairs_int]
  norm_num

/-- `∑_z ψ_S(z) = −1` for a pair `S` of distinct labels (`eq:two-root`). -/
theorem sum_psi_pair (hF : ringChar F ≠ 2) {C : Fin 4 → F} (hC : Function.Injective C)
    {S : Finset (Fin 4)} (hS : S.card = 2) : ∑ z, psi S z C = -1 := by
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hS
  unfold psi
  simp only [Finset.prod_pair hij]
  rw [sum_chi_mul_chi hF (C i) (C j)]
  simp [hC.ne hij]

/-- `∑_z χ(z − a) = 0`. -/
theorem sum_chi_shift (hF : ringChar F ≠ 2) (a : F) : ∑ z, chi (z - a) = 0 := by
  have e : ∑ z, chi (z - a) = ∑ s, chi s := Fintype.sum_equiv (Equiv.subRight a) _ _ fun z => rfl
  rw [e]
  unfold chi
  rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]

/-- **The expansion of `ar𝖪 − 1`** ("Linear prices"): for a core with distinct labels,
`ar𝖪 − 1 = 2q + E_z ∑_{|S| ≥ 3} σ_Sψ_S(z)` (the supports with at least two elements and not
exactly two): the single terms vanish and the pair terms sum to exactly `2q`. -/
theorem Kbar_expansion (hF : ringChar F ≠ 2) {C : Fin 4 → F} (hC : Function.Injective C) :
    Kbar C - 1 = 2 / (Fintype.card F : ℝ) +
      (∑ z, ∑ S ∈ higher.filter (fun S : Finset (Fin 4) => ¬ S.card = 2), sig S * psi S z C) /
        (Fintype.card F : ℝ) := by
  have hn : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hsplit : ∀ z, Kz z C = 1 + ell z C +
      (∑ S ∈ higher.filter (fun S : Finset (Fin 4) => S.card = 2), sig S * psi S z C +
        ∑ S ∈ higher.filter (fun S : Finset (Fin 4) => ¬ S.card = 2), sig S * psi S z C) := by
    intro z
    rw [Finset.sum_filter_add_sum_filter_not, ← Kstar_eq]
    unfold Kstar
    ring
  have hell : ∑ z, ell z C = 0 := by
    unfold ell
    rw [Finset.sum_comm]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [← Finset.mul_sum, sum_chi_shift hF (C k), mul_zero]
  have hs2 : ∑ z, ∑ S ∈ higher.filter (fun S : Finset (Fin 4) => S.card = 2), sig S * psi S z C =
      2 := by
    rw [Finset.sum_comm]
    have : ∀ S ∈ higher.filter (fun S : Finset (Fin 4) => S.card = 2),
        ∑ z, sig S * psi S z C = -sig S := by
      intro S hS
      rw [← Finset.mul_sum, sum_psi_pair hF hC (Finset.mem_filter.mp hS).2]
      ring
    rw [Finset.sum_congr rfl this, Finset.sum_neg_distrib, sig_pairs]
    norm_num
  have e1 : ∑ z, Kz z C = (Fintype.card F : ℝ) + 2 +
      ∑ z, ∑ S ∈ higher.filter (fun S : Finset (Fin 4) => ¬ S.card = 2), sig S * psi S z C := by
    rw [Finset.sum_congr rfl fun z _ => hsplit z]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    rw [hell, hs2]
    ring
  unfold Kbar
  rw [e1]
  field_simp
  ring

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

omit [Nonempty (CoreT F)] in
/-- **`(1 − q)(𝔯 − 1) = (\bar𝖪 − 1)(\bar𝖪 + 1 − 16q) − 15q`** ("Linear prices"). -/
theorem rmass_sub_one (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) :
    (1 - (Fintype.card F : ℝ)⁻¹) * (rmass C - 1) =
      (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * (Fintype.card F : ℝ)⁻¹) -
        15 * (Fintype.card F : ℝ)⁻¹ := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hq : 1 - (Fintype.card F : ℝ)⁻¹ ≠ 0 := by
    have : (Fintype.card F : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  rw [rmass_eq hm1 C]
  have h1 : (1 - (Fintype.card F : ℝ)⁻¹) *
      ((Kbar C.1 ^ 2 - 16 * (Fintype.card F : ℝ)⁻¹ * Kbar C.1) / (1 - (Fintype.card F : ℝ)⁻¹)) =
        Kbar C.1 ^ 2 - 16 * (Fintype.card F : ℝ)⁻¹ * Kbar C.1 :=
    mul_div_cancel₀ _ hq
  linear_combination h1

/-- **`‖𝔯 − 1‖₂ ≤ d_𝔯 = ((2 + η + 16q)d_𝖪 + 15q)/(1 − q)`** ("Linear prices"), given
`‖\bar𝖪 − 1‖₂ ≤ d_𝖪` (`lem:record:weighted-moment`(b)) and `|\bar𝖪 − 1| ≤ η` on every core. -/
theorem nrm_rmass_sub_one_le (hm1 : quadraticChar F (-1) = -1) {η dK : ℝ}
    (hη : ∀ C : CoreT F, |Kbar C.1 - 1| ≤ η)
    (hdK : nrm (coreLaw (F := F)) (fun C => Kbar C.1 - 1) ≤ dK) :
    nrm (coreLaw (F := F)) (fun C => rmass C - 1) ≤
      ((2 + η + 16 * (Fintype.card F : ℝ)⁻¹) * dK + 15 * (Fintype.card F : ℝ)⁻¹) /
        (1 - (Fintype.card F : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  set q := (Fintype.card F : ℝ)⁻¹ with hqdef
  have hq0 : 0 < q := inv_pos.mpr (by linarith)
  have hq1 : 0 < 1 - q := by
    have : q < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hη0 : 0 ≤ η := by
    obtain ⟨C⟩ := (inferInstance : Nonempty (CoreT F))
    exact (abs_nonneg _).trans (hη C)
  -- pointwise: `𝔯 − 1 = ((\bar𝖪 − 1)(\bar𝖪 + 1 − 16q) − 15q)/(1 − q)`
  have hsub : ∀ C : CoreT F, (1 - q) * (rmass C - 1) =
      (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q := fun C => by
    rw [hqdef]; exact rmass_sub_one hm1 C
  have hpt : (fun C : CoreT F => rmass C - 1) = fun C =>
      ((Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q) / (1 - q) := by
    funext C
    rw [eq_div_iff hq1.ne', mul_comm, hsub C]
  rw [hpt]
  -- the norm of the quotient
  have hdiv : nrm (coreLaw (F := F)) (fun C => ((Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q) /
      (1 - q)) = nrm (coreLaw (F := F))
        (fun C => (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q) / (1 - q) := by
    have e : (fun C : CoreT F => ((Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q) / (1 - q)) =
        fun C => (1 - q)⁻¹ * ((Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q) := by
      funext C; field_simp
    rw [e, nrm_smul, abs_of_pos (inv_pos.mpr hq1)]
    field_simp
  rw [hdiv]
  apply div_le_div_of_nonneg_right _ hq1.le
  -- the triangle inequality and the multiplier bound `|\bar𝖪 + 1 − 16q| ≤ 2 + η + 16q`
  have htri := nrm_add_le (coreLaw (F := F)) (fun C => (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q))
    (fun _ => -(15 * q))
  have e2 : (fun C : CoreT F => (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) - 15 * q) =
      fun C => (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q) + -(15 * q) := by
    funext C; ring
  rw [e2]
  have hconst : nrm (coreLaw (F := F)) (fun _ => -(15 * q)) = 15 * q := by
    have := nrm_smul (coreLaw (F := F)) (-(15 * q)) (fun _ => 1)
    simp only [mul_one] at this
    rw [this, nrm_one, mul_one, abs_neg, abs_of_pos (by positivity)]
  have hmul : nrm (coreLaw (F := F)) (fun C => (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q)) ≤
      (2 + η + 16 * q) * dK := by
    have hb : ∀ C : CoreT F, |Kbar C.1 + 1 - 16 * q| ≤ 2 + η + 16 * q := by
      intro C
      have h1 := hη C
      have : Kbar C.1 + 1 - 16 * q = (Kbar C.1 - 1) + (2 - 16 * q) := by ring
      rw [this]
      calc |(Kbar C.1 - 1) + (2 - 16 * q)| ≤ |Kbar C.1 - 1| + |2 - 16 * q| := abs_add_le _ _
        _ ≤ η + (2 + 16 * q) := by
            refine add_le_add h1 ?_
            rw [abs_le]
            constructor <;> linarith
        _ = 2 + η + 16 * q := by ring
    -- `‖fg‖ ≤ sup|g| ‖f‖`
    have hsq : nrm (coreLaw (F := F)) (fun C => (Kbar C.1 - 1) * (Kbar C.1 + 1 - 16 * q)) ^ 2 ≤
        ((2 + η + 16 * q) * nrm (coreLaw (F := F)) (fun C => Kbar C.1 - 1)) ^ 2 := by
      rw [mul_pow, nrm_sq_expect, nrm_sq_expect, ← FiniteLaw.expect_const_mul]
      refine FiniteLaw.expect_mono _ fun C => ?_
      have hbC := hb C
      have : (Kbar C.1 + 1 - 16 * q) ^ 2 ≤ (2 + η + 16 * q) ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hbC 2
      rw [mul_pow]
      nlinarith [sq_nonneg (Kbar C.1 - 1)]
    have h0 : 0 ≤ (2 + η + 16 * q) * nrm (coreLaw (F := F)) (fun C => Kbar C.1 - 1) := by
      have := nrm_nonneg (coreLaw (F := F)) (fun C => Kbar C.1 - 1)
      positivity
    have hle := (abs_le_of_sq_le_sq' hsq h0).2
    calc _ ≤ _ := hle
      _ ≤ (2 + η + 16 * q) * dK := mul_le_mul_of_nonneg_left hdK (by positivity)
  linarith

end Sarkozy.PositiveRoots

module

public import Sarkozy.SpectralC.DegreeOne

@[expose] public section

/-!
# Operator-norm bounds for the degree-one block (`lem:spec:degone`(b))

Operator norms of matrices on `ℂ^{U⁺}` are expressed by bilinear bounds:
`NormLe M λ` means `|w^* M z| ≤ λ |w| |z|` for all `w, z`, that is `‖M‖ ≤ λ`.

* `normLe_add`, `normLe_smul`: the triangle inequality and scaling;
* `normLe_schur`: the Schur test, `‖M‖ ≤ max_k ∑_l B_kl` for `|M_kl| ≤ B_kl`, `B` symmetric;
* `normLe_ones`: `‖𝟙𝟙ᵀ‖ ≤ n`.

`lem:spec:degone`(b) (`degone_block`): `𝐐(ξ)/r = 𝐀₀(ξ) + E_Q(ξ)` with `𝐀₀(ξ) = χ(ξ)ε_G Δ^E`,
`E_Q(ξ)` explicit, `‖E_Q(ξ)‖ ≤ η_Q` and `‖𝐀₀(ξ)‖ ≤ Λ_D`, given the certified bound
`‖Δ^E‖ ≤ Λ_D`, the cross constraints (`δ^×_kl = χ(ς_kl)` for `ς_kl ≠ 0`, from
`chi_mean_of_square`) and the small pair bounds `|δ^×_kl| ≤ min(δ^×_k, δ^×_l)` for `ς_kl = 0`
(`lem:spec:small`(a), `small_pair_bound`); `errQ_hermitian` (`E_Q(ξ)` is Hermitian).

`lem:spec:degone`(c), the bound: `‖𝐍(ξ) − I‖ ≤ ε_V` (`degoneN_sub_one`).

For `cor:spec2:coupling`: `|Mz| ≤ ‖M‖|z|` (`normLe_mulV`) and
`|𝐐(ξ)w|² ≥ r²(|𝐀₀(ξ)w|² − 2Λ_D η_Q|w|²)` (`degone_Q_lower`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {U : Type*} [Fintype U]

/-- The bilinear form `w^* M z = ∑_{k,l} \overline{w_k} M_kl z_l`. -/
noncomputable def bform (M : U → U → ℂ) (w z : U → ℂ) : ℂ := ∑ k, ∑ l, conj (w k) * M k l * z l

/-- The Euclidean norm `|w|`. -/
noncomputable def vnorm (w : U → ℂ) : ℝ := Real.sqrt (∑ k, ‖w k‖ ^ 2)

/-- `‖M‖ ≤ λ`, as a bilinear bound. -/
def NormLe (M : U → U → ℂ) (lam : ℝ) : Prop :=
  ∀ w z : U → ℂ, ‖bform M w z‖ ≤ lam * vnorm w * vnorm z

lemma vnorm_nonneg (w : U → ℂ) : 0 ≤ vnorm w := Real.sqrt_nonneg _

lemma bform_add (M M' : U → U → ℂ) (w z : U → ℂ) :
    bform (fun k l => M k l + M' k l) w z = bform M w z + bform M' w z := by
  unfold bform
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro k _
  rw [← sum_add_distrib]
  apply sum_congr rfl; intro l _
  ring

lemma bform_smul (c : ℂ) (M : U → U → ℂ) (w z : U → ℂ) :
    bform (fun k l => c * M k l) w z = c * bform M w z := by
  unfold bform
  rw [mul_sum]
  apply sum_congr rfl; intro k _
  rw [mul_sum]
  apply sum_congr rfl; intro l _
  ring

theorem normLe_add {M M' : U → U → ℂ} {a b : ℝ} (h : NormLe M a) (h' : NormLe M' b) :
    NormLe (fun k l => M k l + M' k l) (a + b) := by
  intro w z
  rw [bform_add]
  calc ‖bform M w z + bform M' w z‖ ≤ ‖bform M w z‖ + ‖bform M' w z‖ := norm_add_le _ _
    _ ≤ a * vnorm w * vnorm z + b * vnorm w * vnorm z := add_le_add (h w z) (h' w z)
    _ = (a + b) * vnorm w * vnorm z := by ring

theorem normLe_smul {M : U → U → ℂ} {a : ℝ} (h : NormLe M a) (c : ℂ) :
    NormLe (fun k l => c * M k l) (‖c‖ * a) := by
  intro w z
  rw [bform_smul, norm_mul]
  calc ‖c‖ * ‖bform M w z‖ ≤ ‖c‖ * (a * vnorm w * vnorm z) :=
        mul_le_mul_of_nonneg_left (h w z) (norm_nonneg _)
    _ = ‖c‖ * a * vnorm w * vnorm z := by ring

/-- **The Schur test**: if `|M_kl| ≤ B_kl` with `B` symmetric and `∑_l B_kl ≤ ρ` for every `k`,
then `‖M‖ ≤ ρ`. -/
theorem normLe_schur (M : U → U → ℂ) (B : U → U → ℝ) (hB0 : ∀ k l, 0 ≤ B k l)
    (hBsym : ∀ k l, B k l = B l k) (hMB : ∀ k l, ‖M k l‖ ≤ B k l) {ρ : ℝ}
    (hrow : ∀ k, ∑ l, B k l ≤ ρ) : NormLe M ρ := by
  intro w z
  -- weighted Cauchy--Schwarz over pairs
  have h1 : ‖bform M w z‖ ≤ ∑ k, ∑ l, B k l * ‖w k‖ * ‖z l‖ := by
    unfold bform
    refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => (norm_sum_le _ _).trans
      (sum_le_sum fun l _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have := hMB k l
    have hw := norm_nonneg (w k)
    have hz := norm_nonneg (z l)
    nlinarith [mul_nonneg hw hz]
  have h2 : ∑ k, ∑ l, B k l * ‖w k‖ * ‖z l‖ ≤
      Real.sqrt (∑ k, ∑ l, B k l * ‖w k‖ ^ 2) * Real.sqrt (∑ k, ∑ l, B k l * ‖z l‖ ^ 2) := by
    rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt univ
      (fun kl : U × U => Real.sqrt (B kl.1 kl.2) * ‖w kl.1‖)
      (fun kl : U × U => Real.sqrt (B kl.1 kl.2) * ‖z kl.2‖)
    have e1 : ∀ kl : U × U, Real.sqrt (B kl.1 kl.2) * ‖w kl.1‖ *
        (Real.sqrt (B kl.1 kl.2) * ‖z kl.2‖) = B kl.1 kl.2 * ‖w kl.1‖ * ‖z kl.2‖ := by
      intro kl
      rw [show Real.sqrt (B kl.1 kl.2) * ‖w kl.1‖ * (Real.sqrt (B kl.1 kl.2) * ‖z kl.2‖) =
        (Real.sqrt (B kl.1 kl.2) * Real.sqrt (B kl.1 kl.2)) * ‖w kl.1‖ * ‖z kl.2‖ by ring,
        Real.mul_self_sqrt (hB0 _ _)]
    have e2 : ∀ kl : U × U, (Real.sqrt (B kl.1 kl.2) * ‖w kl.1‖) ^ 2 =
        B kl.1 kl.2 * ‖w kl.1‖ ^ 2 := by
      intro kl; rw [mul_pow, Real.sq_sqrt (hB0 _ _)]
    have e3 : ∀ kl : U × U, (Real.sqrt (B kl.1 kl.2) * ‖z kl.2‖) ^ 2 =
        B kl.1 kl.2 * ‖z kl.2‖ ^ 2 := by
      intro kl; rw [mul_pow, Real.sq_sqrt (hB0 _ _)]
    simp only [e1, e2, e3] at hcs
    exact hcs
  have h3 : ∑ k, ∑ l, B k l * ‖w k‖ ^ 2 ≤ ρ * ∑ k, ‖w k‖ ^ 2 := by
    rw [mul_sum]
    apply sum_le_sum; intro k _
    rw [← sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow k) (sq_nonneg _)
  have h4 : ∑ k, ∑ l, B k l * ‖z l‖ ^ 2 ≤ ρ * ∑ l, ‖z l‖ ^ 2 := by
    rw [sum_comm, mul_sum]
    apply sum_le_sum; intro l _
    rw [← sum_mul]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    calc ∑ k, B k l = ∑ k, B l k := sum_congr rfl fun k _ => hBsym k l
      _ ≤ ρ := hrow l
  by_cases hρ : 0 ≤ ρ
  · calc ‖bform M w z‖
        ≤ Real.sqrt (∑ k, ∑ l, B k l * ‖w k‖ ^ 2) * Real.sqrt (∑ k, ∑ l, B k l * ‖z l‖ ^ 2) :=
          h1.trans h2
      _ ≤ Real.sqrt (ρ * ∑ k, ‖w k‖ ^ 2) * Real.sqrt (ρ * ∑ l, ‖z l‖ ^ 2) :=
          mul_le_mul (Real.sqrt_le_sqrt h3) (Real.sqrt_le_sqrt h4) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = ρ * vnorm w * vnorm z := by
          unfold vnorm
          rw [Real.sqrt_mul hρ, Real.sqrt_mul hρ]
          have := Real.mul_self_sqrt hρ
          rw [show Real.sqrt ρ * Real.sqrt (∑ k, ‖w k‖ ^ 2) * (Real.sqrt ρ *
            Real.sqrt (∑ l, ‖z l‖ ^ 2)) = (Real.sqrt ρ * Real.sqrt ρ) *
              Real.sqrt (∑ k, ‖w k‖ ^ 2) * Real.sqrt (∑ l, ‖z l‖ ^ 2) by ring, this]
  · have hU : IsEmpty U := by
      by_contra hne
      rw [not_isEmpty_iff] at hne
      obtain ⟨k⟩ := hne
      have h5 := hrow k
      have h6 : 0 ≤ ∑ l, B k l := sum_nonneg fun l _ => hB0 k l
      exact hρ (h6.trans h5)
    have hb : bform M w z = 0 := by unfold bform; simp [Finset.univ_eq_empty]
    have hv : vnorm w = 0 := by unfold vnorm; simp [Finset.univ_eq_empty]
    rw [hb, hv]
    simp

theorem normLe_of_isEmpty [IsEmpty U] (M : U → U → ℂ) (lam : ℝ) : NormLe M lam := by
  intro w z
  have hb : bform M w z = 0 := by unfold bform; simp [Finset.univ_eq_empty]
  have hv : vnorm w = 0 := by unfold vnorm; simp [Finset.univ_eq_empty]
  rw [hb, hv]
  simp

theorem normLe_mono {M : U → U → ℂ} {a b : ℝ} (h : NormLe M a) (hab : a ≤ b) : NormLe M b := by
  intro w z
  exact (h w z).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hab
    (vnorm_nonneg w)) (vnorm_nonneg z))

/-- `‖𝟙𝟙ᵀ‖ ≤ n`. -/
theorem normLe_ones : NormLe (fun _ _ : U => (1 : ℂ)) (Fintype.card U) :=
  normLe_schur _ (fun _ _ => 1) (fun _ _ => zero_le_one) (fun _ _ => rfl)
    (fun _ _ => by simp) (fun k => by simp)

/-! ## The degree-one block (`lem:spec:degone`(b)) -/

variable [DecidableEq U] {p : ℕ} [Fact p.Prime]

/-- `Δ^E_kl = χ(ς_kl)` if `ς_kl ≠ 0`, else `0`. -/
noncomputable def deltaE (ς : U → U → ZMod p) (k l : U) : ℂ :=
  if ς k l ≠ 0 then chiC p (ς k l) else 0

/-- `𝐀₀(ξ) = χ(ξ) ε_G Δ^E`. -/
noncomputable def azero (ς : U → U → ZMod p) (ξ : ZMod p) (k l : U) : ℂ :=
  chiC p ξ * epsG p * deltaE ς k l

/-- `E_Q(ξ) = 𝐐(ξ)/r − 𝐀₀(ξ)`. -/
noncomputable def errQ (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (ς : U → U → ZMod p)
    (ξ : ZMod p) (k l : U) : ℂ :=
  degoneQ Λ ξ k l / (rp p : ℂ) - azero ς ξ k l

lemma rp_ne_zero : (rp p : ℂ) ≠ 0 := by
  unfold rp
  have : (0 : ℝ) < Real.sqrt p := Real.sqrt_pos.mpr (by exact_mod_cast (Fact.out : p.Prime).pos)
  exact_mod_cast (inv_pos.mpr this).ne'

lemma norm_chi_eps_le (hp2 : p ≠ 2) (ξ : ZMod p) : ‖chiC p ξ * epsG p‖ ≤ 1 := by
  rw [norm_mul, norm_epsG hp2, mul_one]
  by_cases hξ : ξ = 0
  · rw [hξ, chiC_zero, norm_zero]; exact zero_le_one
  · rw [norm_chiC hξ]

omit [DecidableEq U] in
/-- **`lem:spec:degone`(b), the norm of `𝐀₀`**: `‖𝐀₀(ξ)‖ = ‖Δ^E‖` for `ξ ≠ 0`. -/
theorem normLe_azero_iff (hp2 : p ≠ 2) (ς : U → U → ZMod p) {ξ : ZMod p} (hξ : ξ ≠ 0)
    (lam : ℝ) : NormLe (azero ς ξ) lam ↔ NormLe (deltaE ς) lam := by
  have h1 : ‖chiC p ξ * epsG p‖ = 1 := by rw [norm_mul, norm_epsG hp2, norm_chiC hξ, mul_one]
  constructor
  · intro h w z
    have := h w z
    unfold azero at this
    rw [bform_smul (chiC p ξ * epsG p) (deltaE ς), norm_mul, h1, one_mul] at this
    exact this
  · intro h w z
    unfold azero
    rw [bform_smul (chiC p ξ * epsG p) (deltaE ς), norm_mul, h1, one_mul]
    exact h w z

/-- **`lem:spec:degone`(b)**: with the certified `‖Δ^E‖ ≤ Λ_D`, the cross constraints and the
small pair bounds `|δ^×_kl| ≤ m_kl` (`m` symmetric, row sums `≤ ρ`, `lem:spec:small`(a)),
`‖E_Q(ξ)‖ ≤ η_Q = Λ_D/(p − 1) + (p/(p − 1)) ρ + n/((p − 1) r)`. -/
theorem degone_block (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (ς : U → U → ZMod p) (hςsym : ∀ k l, ς k l = 0 ↔ ς l k = 0)
    {ΛD : ℝ} (hD : NormLe (deltaE ς) ΛD) (hΛD : 0 ≤ ΛD)
    (hcross : ∀ k l, ς k l ≠ 0 → deltaX Λ k l = chiC p (ς k l))
    (m : U → U → ℝ) (hm0 : ∀ k l, 0 ≤ m k l) (hmsym : ∀ k l, m k l = m l k)
    (hsmall : ∀ k l, ς k l = 0 → ‖deltaX Λ k l‖ ≤ m k l) {ρ : ℝ}
    (hrow : ∀ k, ∑ l, (if ς k l = 0 then m k l else 0) ≤ ρ) (ξ : ZMod p) :
    NormLe (errQ Λ ς ξ) (ΛD / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * ρ +
      (Fintype.card U : ℝ) / (((p : ℝ) - 1) * rp p)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hr0 : (0 : ℝ) < rp p := by
    unfold rp; exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hpC1 : (p : ℂ) - 1 ≠ 0 := by
    have : ((p : ℝ) - 1 : ℝ) ≠ 0 := hp1'.ne'
    exact_mod_cast this
  have hrC := rp_ne_zero (p := p)
  set Dsm : U → U → ℂ := fun k l => if ς k l = 0 then deltaX Λ k l else 0 with hDsm
  set ce : ℂ := chiC p ξ * epsG p with hce
  -- the entrywise decomposition
  have hdec : ∀ k l, errQ Λ ς ξ k l =
      (ce / ((p : ℂ) - 1)) * deltaE ς k l + ((p : ℂ) / ((p : ℂ) - 1) * ce) * Dsm k l +
        (-(1 / (((p : ℂ) - 1) * (rp p : ℂ)))) * 1 := by
    intro k l
    unfold errQ azero degoneQ
    rw [gaussEig]
    have hδ : deltaX Λ k l = deltaE ς k l + Dsm k l := by
      unfold deltaE
      simp only [hDsm]
      by_cases h : ς k l = 0
      · rw [ite_eq_right (not_not.mpr h), ite_eq_left h, zero_add]
      · rw [ite_eq_left h, ite_eq_right h, add_zero, hcross k l h]
    rw [hδ]
    simp only [hce]
    field_simp
    ring
  have hE : ∀ w z, bform (errQ Λ ς ξ) w z = bform (fun k l =>
      (ce / ((p : ℂ) - 1)) * deltaE ς k l + ((p : ℂ) / ((p : ℂ) - 1) * ce) * Dsm k l +
        (-(1 / (((p : ℂ) - 1) * (rp p : ℂ)))) * 1) w z := by
    intro w z
    unfold bform
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro l _
    rw [hdec]
  -- the three parts
  have hce1 : ‖ce‖ ≤ 1 := norm_chi_eps_le hp2 ξ
  have N1 : NormLe (fun k l => (ce / ((p : ℂ) - 1)) * deltaE ς k l) (ΛD / ((p : ℝ) - 1)) := by
    refine normLe_mono (normLe_smul hD _) ?_
    rw [norm_div, show ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 by
      rw [show (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hp1'.le]]
    rw [div_mul_eq_mul_div]
    apply div_le_div_of_nonneg_right _ hp1'.le
    nlinarith
  by_cases hU : IsEmpty U
  · exact normLe_of_isEmpty _ _
  rw [not_isEmpty_iff] at hU
  obtain ⟨k₀⟩ := hU
  have hρ0 : 0 ≤ ρ :=
    (sum_nonneg fun l _ => by split_ifs <;> simp [hm0]).trans (hrow k₀)
  have N2 : NormLe (fun k l => ((p : ℂ) / ((p : ℂ) - 1) * ce) * Dsm k l)
      ((p : ℝ) / ((p : ℝ) - 1) * ρ) := by
    have hS : NormLe Dsm ρ := by
      apply normLe_schur Dsm (fun k l => if ς k l = 0 then m k l else 0)
      · intro k l; split_ifs <;> simp [hm0]
      · intro k l
        by_cases h : ς k l = 0
        · rw [ite_eq_left h, ite_eq_left ((hςsym k l).mp h), hmsym]
        · rw [ite_eq_right h, ite_eq_right (fun h' => h ((hςsym k l).mpr h'))]
      · intro k l
        simp only [hDsm]
        by_cases h : ς k l = 0
        · rw [ite_eq_left h, ite_eq_left h]; exact hsmall k l h
        · rw [ite_eq_right h, ite_eq_right h, norm_zero]
      · exact hrow
    refine normLe_mono (normLe_smul hS _) ?_
    have hnorm : ‖(p : ℂ) / ((p : ℂ) - 1) * ce‖ ≤ (p : ℝ) / ((p : ℝ) - 1) := by
      rw [norm_mul, norm_div, Complex.norm_natCast, show ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 by
        rw [show (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
          Real.norm_of_nonneg hp1'.le]]
      have : 0 ≤ (p : ℝ) / ((p : ℝ) - 1) := by positivity
      nlinarith
    exact mul_le_mul_of_nonneg_right hnorm hρ0
  have N3 : NormLe (fun _ _ : U => (-(1 / (((p : ℂ) - 1) * (rp p : ℂ)))) * 1)
      ((Fintype.card U : ℝ) / (((p : ℝ) - 1) * rp p)) := by
    refine normLe_mono (normLe_smul normLe_ones _) (le_of_eq ?_)
    rw [norm_neg, norm_div, norm_one, show ((p : ℂ) - 1) * (rp p : ℂ) =
      ((((p : ℝ) - 1) * rp p : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    ring
  intro w z
  rw [hE]
  exact (normLe_add (normLe_add N1 N2) N3) w z

/-- **`lem:spec:degone`(b)**: `E_Q(ξ)` is Hermitian (with `ς_lk = −ς_kl` and a swap-invariant
`λ`). -/
theorem errQ_hermitian (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (hswap : ∀ z, Λ (z.2, z.1) = Λ z) (ς : U → U → ZMod p) (hanti : ∀ k l, ς l k = -ς k l)
    (ξ : ZMod p) (k l : U) : conj (errQ Λ ς ξ l k) = errQ Λ ς ξ k l := by
  unfold errQ
  rw [map_sub, map_div₀, degoneQ_hermitian hp2 Λ hswap ξ k l, Complex.conj_ofReal]
  congr 1
  unfold azero deltaE
  have heps : conj (epsG p) = chiC p (-1) * epsG p := by
    unfold epsG
    rw [map_div₀, conj_Gchi hp2, Complex.conj_ofReal]
    ring
  have h1 : chiC p (-1) * chiC p (-1) = 1 := by rw [← map_mul]; norm_num
  by_cases h : ς k l = 0
  · have h' : ς l k = 0 := by rw [hanti, h, neg_zero]
    rw [ite_eq_right (not_not.mpr h'), ite_eq_right (not_not.mpr h)]
    simp
  · have h' : ς l k ≠ 0 := by rw [hanti]; exact neg_ne_zero.mpr h
    rw [ite_eq_left h', ite_eq_left h, map_mul, map_mul, conj_chiC, conj_chiC, heps, hanti,
      show -ς k l = -1 * ς k l by ring, map_mul]
    linear_combination (chiC p ξ * epsG p * chiC p (ς k l)) * h1

/-- **`lem:spec:degone`(c), the bound `‖𝐍(ξ) − I‖ ≤ ε_V`**: with `|Δ^μ_kl| ≤ m_kl` for `k ≠ l`
(`m` symmetric, `m_kl = 1` on the internal edges and `min(δ^μ_k, δ^μ_l)` otherwise,
`lem:spec:small`(b)) and row sums `∑_{l ≠ k} m_kl ≤ ρ`,
`‖𝐍(ξ) − I‖ ≤ (n − 1)/(p − 1) + (p/(p − 1)) r ρ`. -/
theorem degoneN_sub_one (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (m : U → U → ℝ)
    (hm0 : ∀ k l, 0 ≤ m k l) (hmsym : ∀ k l, m k l = m l k)
    (hΔ : ∀ k l, k ≠ l → ‖deltaMu μ k l‖ ≤ m k l) {ρ : ℝ}
    (hrow : ∀ k, ∑ l, (if k = l then 0 else m k l) ≤ ρ) (ξ : ZMod p) :
    NormLe (fun k l => degoneN μ ξ k l - (if k = l then 1 else 0))
      (((Fintype.card U : ℝ) - 1) / ((p : ℝ) - 1) + (p : ℝ) / ((p : ℝ) - 1) * rp p * ρ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpC1 : (p : ℂ) - 1 ≠ 0 := by
    have : ((p : ℝ) - 1 : ℝ) ≠ 0 := hp1'.ne'
    exact_mod_cast this
  by_cases hU : IsEmpty U
  · exact normLe_of_isEmpty _ _
  rw [not_isEmpty_iff] at hU
  obtain ⟨k₀⟩ := hU
  have hρ0 : 0 ≤ ρ := (sum_nonneg fun l _ => by split_ifs <;> simp [hm0]).trans (hrow k₀)
  -- the decomposition `𝐍 − I = −(𝟙𝟙ᵀ − I)/(p − 1) + (p/(p − 1)) c_ξ Δ^μ`
  set Off : U → U → ℂ := fun k l => if k = l then 0 else 1 with hOff
  have hdec : ∀ k l, degoneN μ ξ k l - (if k = l then 1 else 0) =
      (-(1 / ((p : ℂ) - 1))) * Off k l + ((p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ) * deltaMu μ k l := by
    intro k l
    unfold degoneN
    simp only [hOff]
    by_cases h : k = l
    · simp [h]
    · simp [h]
  have N1 : NormLe (fun k l => (-(1 / ((p : ℂ) - 1))) * Off k l)
      (((Fintype.card U : ℝ) - 1) / ((p : ℝ) - 1)) := by
    have hS : NormLe Off ((Fintype.card U : ℝ) - 1) := by
      apply normLe_schur Off (fun k l => if k = l then 0 else 1)
      · intro k l; split_ifs <;> norm_num
      · intro k l
        by_cases h : k = l
        · rw [ite_eq_left h, ite_eq_left h.symm]
        · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
      · intro k l; simp only [hOff]; split_ifs <;> simp
      · intro k
        rw [sum_ite, sum_const_zero, zero_add, sum_const, nsmul_eq_mul, mul_one]
        have : (univ.filter (fun l => ¬ k = l)).card = Fintype.card U - 1 := by
          have h1 : univ.filter (fun l => ¬ k = l) = univ.erase k := by
            ext l; simp [eq_comm]
          rw [h1, card_erase_of_mem (mem_univ _), card_univ]
        rw [this]
        have hcard : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨k⟩
        rw [Nat.cast_sub hcard, Nat.cast_one]
    refine normLe_mono (normLe_smul hS _) (le_of_eq ?_)
    rw [norm_neg, norm_div, norm_one, show ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 by
      rw [show (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hp1'.le]]
    ring
  have N2 : NormLe (fun k l => ((p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ) * deltaMu μ k l)
      ((p : ℝ) / ((p : ℝ) - 1) * rp p * ρ) := by
    have hS : NormLe (deltaMu μ) ρ := by
      apply normLe_schur (deltaMu μ) (fun k l => if k = l then 0 else m k l)
      · intro k l; split_ifs <;> simp [hm0]
      · intro k l
        by_cases h : k = l
        · rw [ite_eq_left h, ite_eq_left h.symm]
        · rw [ite_eq_right h, ite_eq_right (Ne.symm h), hmsym]
      · intro k l
        by_cases h : k = l
        · rw [ite_eq_left h]; unfold deltaMu; rw [ite_eq_left h, norm_zero]
        · rw [ite_eq_right h]; exact hΔ k l h
      · exact hrow
    refine normLe_mono (normLe_smul hS _) ?_
    apply mul_le_mul_of_nonneg_right _ hρ0
    rw [norm_mul, norm_div, Complex.norm_natCast, show ‖(p : ℂ) - 1‖ = (p : ℝ) - 1 by
      rw [show (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
        Real.norm_of_nonneg hp1'.le]]
    exact mul_le_mul_of_nonneg_left (norm_gaussEig_le hp2 ξ) (by positivity)
  intro w z
  have hE : bform (fun k l => degoneN μ ξ k l - (if k = l then 1 else 0)) w z =
      bform (fun k l => (-(1 / ((p : ℂ) - 1))) * Off k l +
        ((p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ) * deltaMu μ k l) w z := by
    unfold bform
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro l _
    dsimp only
    rw [hdec]
  rw [hE]
  exact (normLe_add N1 N2) w z

/-! ## Vector bounds (`|Mz| ≤ ‖M‖|z|`) and the lower bound used in `cor:spec2:coupling` -/

omit [DecidableEq U] in
/-- `(Mz)_k = ∑_l M_kl z_l`. -/
noncomputable def mulV (M : U → U → ℂ) (z : U → ℂ) (k : U) : ℂ := ∑ l, M k l * z l

omit [DecidableEq U] in
lemma bform_mulV (M : U → U → ℂ) (y z : U → ℂ) :
    bform M y z = ∑ k, conj (y k) * mulV M z k := by
  unfold bform mulV
  refine sum_congr rfl fun k _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun l _ => by ring

omit [DecidableEq U] in
lemma vnorm_sq (w : U → ℂ) : vnorm w ^ 2 = ∑ k, ‖w k‖ ^ 2 :=
  Real.sq_sqrt (sum_nonneg fun _ _ => sq_nonneg _)

omit [DecidableEq U] in
/-- `‖M‖ ≤ λ` gives `|Mz| ≤ λ|z|`. -/
theorem normLe_mulV {M : U → U → ℂ} {lam : ℝ} (h : NormLe M lam) (hlam : 0 ≤ lam)
    (z : U → ℂ) : vnorm (mulV M z) ≤ lam * vnorm z := by
  set y := mulV M z with hy
  have h1 : vnorm y ^ 2 ≤ lam * vnorm y * vnorm z := by
    have h0 := h y z
    rw [bform_mulV] at h0
    have h2 : ∑ k, conj (y k) * mulV M z k = ((vnorm y ^ 2 : ℝ) : ℂ) := by
      rw [vnorm_sq]
      push_cast
      exact sum_congr rfl fun k _ => Complex.conj_mul' (y k)
    rw [h2, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)] at h0
    exact h0
  have hy0 := vnorm_nonneg y
  have hz0 := vnorm_nonneg z
  by_cases hyz : vnorm y = 0
  · rw [hyz]; positivity
  · have hpos : 0 < vnorm y := lt_of_le_of_ne hy0 (Ne.symm hyz)
    nlinarith

/-- **`lem:spec:degone`(b), the lower bound used in `cor:spec2:coupling`**: with
`‖Δ^E‖ ≤ Λ_D` and `‖E_Q(ξ)‖ ≤ η`, `|𝐐(ξ)w|² ≥ r²(|𝐀₀(ξ)w|² − 2Λ_D η|w|²)`. -/
theorem degone_Q_lower (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (ς : U → U → ZMod p) {ξ : ZMod p} (hξ : ξ ≠ 0) {ΛD η : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η)
    (hD : NormLe (deltaE ς) ΛD) (hE : NormLe (errQ Λ ς ξ) η) (w : U → ℂ) :
    rp p ^ 2 * (vnorm (mulV (azero ς ξ) w) ^ 2 - 2 * ΛD * η * vnorm w ^ 2) ≤
      vnorm (mulV (degoneQ Λ ξ) w) ^ 2 := by
  have hrC := rp_ne_zero (p := p)
  set a := mulV (azero ς ξ) w with ha
  set e := mulV (errQ Λ ς ξ) w with he
  have hQ : ∀ k, mulV (degoneQ Λ ξ) w k = (rp p : ℂ) * (a k + e k) := by
    intro k
    simp only [ha, he, mulV]
    rw [← sum_add_distrib, mul_sum]
    refine sum_congr rfl fun l _ => ?_
    unfold errQ
    field_simp
    ring
  have hnorm : vnorm (mulV (degoneQ Λ ξ) w) ^ 2 = rp p ^ 2 * ∑ k, ‖a k + e k‖ ^ 2 := by
    rw [vnorm_sq, mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [hQ, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  have hpt : ∀ k, ‖a k‖ ^ 2 - 2 * (‖a k‖ * ‖e k‖) ≤ ‖a k + e k‖ ^ 2 := by
    intro k
    have h1 : ‖a k‖ - ‖e k‖ ≤ ‖a k + e k‖ := by
      have := norm_add_le (a k + e k) (-(e k))
      rw [add_neg_cancel_right, norm_neg] at this
      linarith
    have h0 := norm_nonneg (a k + e k)
    have he0 := norm_nonneg (e k)
    by_cases hle : ‖e k‖ ≤ ‖a k‖
    · nlinarith
    · nlinarith [norm_nonneg (a k)]
  have hCS : ∑ k, ‖a k‖ * ‖e k‖ ≤ vnorm a * vnorm e :=
    Real.sum_mul_le_sqrt_mul_sqrt univ (fun k => ‖a k‖) (fun k => ‖e k‖)
  have hA : vnorm a ≤ ΛD * vnorm w :=
    normLe_mulV ((normLe_azero_iff hp2 ς hξ ΛD).mpr hD) hΛD w
  have hEb : vnorm e ≤ η * vnorm w := normLe_mulV hE hη w
  have hprod : vnorm a * vnorm e ≤ ΛD * η * vnorm w ^ 2 := by
    have := mul_le_mul hA hEb (vnorm_nonneg e) (mul_nonneg hΛD (vnorm_nonneg w))
    nlinarith [this]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  calc vnorm a ^ 2 - 2 * ΛD * η * vnorm w ^ 2
      ≤ ∑ k, ‖a k‖ ^ 2 - 2 * ∑ k, ‖a k‖ * ‖e k‖ := by
        rw [vnorm_sq]; nlinarith [hCS, hprod]
    _ = ∑ k, (‖a k‖ ^ 2 - 2 * (‖a k‖ * ‖e k‖)) := by rw [sum_sub_distrib, mul_sum]
    _ ≤ ∑ k, ‖a k + e k‖ ^ 2 := sum_le_sum fun k _ => hpt k

end Sarkozy.SpectralC

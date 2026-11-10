module

public import Sarkozy.ExtractionK.PinnedExtractionCore

@[expose] public section

/-!
# Pinned compressed classes, II: `eq:push:pinnedclass` and `N^pin` (`prop:pinned-extraction`)

`paper/sections/16_extraction.tex`, `prop:pinned-extraction`, from the class bound
`pe_class_sum_le` of `PinnedExtractionCore.lean`, in the setting of `subsec:push:pinnedremainder`
(`PinnedCollision.lean`).

* `peGamma` (`γ_pin = ((2n + z)/2) r² + (Δ_pin/4) r`), `peRpin` (`R_pin`), `peLambda0`
  (`Λ^pin_0 = R_pin² exp(r² n² 2^{Δ_pin}) (1 - e^pin_ϖ)^{-(n+2)}`), `peOc` (`oc^pin = ∑_v 2^{h_v}`
  over the non-witness vertices, `h_v` counted in `N_X` on the row side and in `N_Y` on the column
  side); `Δ_pin` enters through hypotheses `ϖ + |N_X(i)| ≤ Δ`, `ϖ + |N_Y(i)| ≤ Δ` (any upper bound
  of the paper's `Δ_pin` works).
* `peF_le`, `peF_le_exp`: `F^pin_v ≤ (1 + e^pin_{ϖ_v+h_v} + r² n 2^{ϖ_v+h_v})/(1 - e^pin_ϖ)
  ≤ exp(2^ϖ 2^{h_v} 2γ_pin + r² n 2^{Δ_pin})/(1 - e^pin_ϖ)`; `peFactor_le`: the product over the
  `2(n - k)` non-witness vertices.
* `pinned_extraction_sum_le`, **`pinned_extraction`** (`eq:push:pinnedclass`, for a class
  `𝒞(P, A)` with a witness of size `k` (`IsWitness`) and a cover (`IsCover`); the paper has
  `k = 2`, `c_ker ∈ {1, 2}`):
  `‖T_𝒞‖ ≤ c_ker r^k 2^{ex^pin(𝒞)/2 + kϖ} Λ^pin_0 exp(γ_pin 2^ϖ oc^pin(𝒞))`, as a bound of
  `|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ|` by this constant times `‖f‖_μ ‖h‖_μ`, `μ` uniform on `𝓘_pin`
  (`E_μ = |𝓘_pin|⁻¹ ∑`), `ex^pin = f_V + f_W`.
* **`pinned_extraction_buckets`**: the bucket sum `N^pin` over an exact partition of the nonstar
  subsets into classes with witnesses of size two (`IsExactPartition`), bucket indices
  `𝔟 ≥ oc^pin(𝒞) 2^{-𝔮}`.

## Deviations from the paper

* `e^pin_ϖ < 1` suffices (the paper assumes `< 1/2`).
* The class bound is proved without `R_pin` (counting route); `R_pin² ≥ 1` is inserted to match
  `Λ^pin_0`, and so is `(1 - e^pin_ϖ)^{-2}` (the bound has `(1 - e^pin_ϖ)^{-n}`).
* Not formalized: the closing admissibility statement (`lem:majorant`) of
  `prop:pinned-collision` about `N^pin/r²`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section PeConst

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `γ_pin = ((2n + z)/2) r² + (Δ_pin/4) r`. -/
noncomputable def peGamma (q : ℝ) (n z Δ : ℕ) : ℝ :=
  (2 * n + z : ℝ) / 2 * (Real.sqrt q)⁻¹ ^ 2 + (Δ : ℝ) / 4 * (Real.sqrt q)⁻¹

/-- `R_pin = ((1 + e^pin_ϖ)/(1 - e^pin_ϖ))^n`. -/
noncomputable def peRpin (q : ℝ) (n z ϖ : ℕ) : ℝ :=
  ((1 + ePin q n z ϖ) / (1 - ePin q n z ϖ)) ^ n

/-- `Λ^pin_0 = R_pin² exp(r² n² 2^{Δ_pin}) / (1 - e^pin_ϖ)^{n+2}`. -/
noncomputable def peLambda0 (q : ℝ) (n z ϖ Δ : ℕ) : ℝ :=
  peRpin q n z ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) /
    (1 - ePin q n z ϖ) ^ (n + 2)

/-- `oc^pin(𝒞) = ∑_v 2^{h_v}` over the `2(n - k)` non-witness vertices (`h_v` counted in `N_X`
on the row side, in `N_Y` on the column side). -/
noncomputable def peOc {n : ℕ} (Fr : Finset (Fin n × Fin n)) (V W Cx Cz : Finset (Fin n)) : ℝ :=
  (∑ u ∈ univ \ (V ∪ Cx), (2 : ℝ) ^ (intH Fr u).card) + (∑ b ∈ Cz, (2 : ℝ) ^ (peColH Fr b).card) +
    (∑ u ∈ univ \ (W ∪ Cz), (2 : ℝ) ^ (peColH Fr u).card) +
      ∑ b ∈ Cx, (2 : ℝ) ^ (intH Fr b).card

theorem peF_le {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1) (ϖj h : ℕ) :
    peF q n z ϖ ϖj h ≤
      (1 + ePin q n z (ϖj + h) + (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ (ϖj + h)) / (1 - ePin q n z ϖ) := by
  unfold peF peNum peLow
  have h1e : 0 < 1 - ePin q n z ϖ := by linarith
  have hc := coarseError_le_ePin q n z (ϖj + h)
  have hpos : 0 < q * (2 : ℝ)⁻¹ ^ ϖj := by positivity
  rw [div_le_div_iff₀ (mul_pos hpos h1e) h1e]
  have hr : (Real.sqrt q)⁻¹ ^ 2 * q = 1 := by
    rw [inv_pow, Real.sq_sqrt hq.le, inv_mul_cancel₀ hq.ne']
  have h2 : (2 : ℝ)⁻¹ ^ ϖj * 2 ^ ϖj = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  have key : (n : ℝ) * 2 ^ h = q * (2 : ℝ)⁻¹ ^ ϖj * ((Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ (ϖj + h)) := by
    rw [pow_add]
    calc (n : ℝ) * 2 ^ h = ((Real.sqrt q)⁻¹ ^ 2 * q) * ((2 : ℝ)⁻¹ ^ ϖj * 2 ^ ϖj) * (n * 2 ^ h) := by
          rw [hr, h2]; ring
      _ = _ := by ring
  rw [key]
  have : q * (2 : ℝ)⁻¹ ^ ϖj * (1 + coarseError (ϖj + h) q (2 * n + z)) ≤
      q * (2 : ℝ)⁻¹ ^ ϖj * (1 + ePin q n z (ϖj + h)) :=
    mul_le_mul_of_nonneg_left (by linarith) hpos.le
  nlinarith [this, h1e]

/-- `e^pin_{ϖ_v + h} ≤ 2^ϖ 2^h · 2γ_pin` and `r² n 2^{ϖ_v + h} ≤ r² n 2^{Δ}` when
`ϖ_v ≤ ϖ` and `ϖ + h ≤ Δ`. -/
theorem peF_le_exp {q : ℝ} (hq : 0 < q) {n z ϖ Δ : ℕ} (he : ePin q n z ϖ < 1) {ϖj h : ℕ}
    (hϖj : ϖj ≤ ϖ) (hΔ : ϖ + h ≤ Δ) :
    peF q n z ϖ ϖj h ≤
      Real.exp (2 ^ ϖ * 2 ^ h * (2 * peGamma q n z Δ) + (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ) /
        (1 - ePin q n z ϖ) := by
  have h1e : 0 < 1 - ePin q n z ϖ := by linarith
  refine (peF_le hq he ϖj h).trans ?_
  refine div_le_div_of_nonneg_right ?_ h1e.le
  have hr : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hE : ePin q n z (ϖj + h) ≤ 2 ^ ϖ * 2 ^ h * (2 * peGamma q n z Δ) := by
    unfold ePin peGamma
    have hp : (2 : ℝ) ^ (ϖj + h) ≤ 2 ^ ϖ * 2 ^ h := by
      rw [← pow_add]
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have hd : ((ϖj + h : ℕ) : ℝ) ≤ Δ := by exact_mod_cast (by omega : ϖj + h ≤ Δ)
    have h0 : 0 ≤ (2 * n + z : ℝ) * (Real.sqrt q)⁻¹ ^ 2 + ((ϖj + h : ℕ) : ℝ) / 2 * (Real.sqrt q)⁻¹ :=
      by positivity
    have h3 : (2 * n + z : ℝ) * (Real.sqrt q)⁻¹ ^ 2 + ((ϖj + h : ℕ) : ℝ) / 2 * (Real.sqrt q)⁻¹ ≤
        2 * ((2 * n + z : ℝ) / 2 * (Real.sqrt q)⁻¹ ^ 2 + (Δ : ℝ) / 4 * (Real.sqrt q)⁻¹) := by
      have : ((ϖj + h : ℕ) : ℝ) / 2 * (Real.sqrt q)⁻¹ ≤ (Δ : ℝ) / 2 * (Real.sqrt q)⁻¹ :=
        mul_le_mul_of_nonneg_right (by linarith) hr
      linarith
    calc (2 : ℝ) ^ (ϖj + h) * ((2 * n + z : ℝ) * (Real.sqrt q)⁻¹ ^ 2 +
          ((ϖj + h : ℕ) : ℝ) / 2 * (Real.sqrt q)⁻¹)
        ≤ (2 ^ ϖ * 2 ^ h) * (2 * ((2 * n + z : ℝ) / 2 * (Real.sqrt q)⁻¹ ^ 2 +
            (Δ : ℝ) / 4 * (Real.sqrt q)⁻¹)) := mul_le_mul hp h3 h0 (by positivity)
      _ = _ := by ring
  have hR : (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ (ϖj + h) ≤ (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ :=
    mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) (by omega)) (by positivity)
  have := Real.add_one_le_exp (2 ^ ϖ * 2 ^ h * (2 * peGamma q n z Δ) +
    (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ)
  linarith

omit [Field F] [Fintype F] [DecidableEq F] in
theorem pe_prod_le_exp {n : ℕ} {S : Finset (Fin n)} {a x : Fin n → ℝ} {D : ℝ}
    (ha : ∀ v ∈ S, 0 ≤ a v) (h : ∀ v ∈ S, a v ≤ Real.exp (x v) / D) :
    ∏ v ∈ S, a v ≤ Real.exp (∑ v ∈ S, x v) / D ^ S.card := by
  calc ∏ v ∈ S, a v ≤ ∏ v ∈ S, Real.exp (x v) / D := prod_le_prod₀ ha h
    _ = Real.exp (∑ v ∈ S, x v) / D ^ S.card := by
        rw [prod_div_distrib, Real.exp_sum, prod_const]

theorem pe_intH_card_le {n : ℕ} {ς : Fin n → Fin n → ℤ} {Fr : Finset (Fin n × Fin n)}
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (u : Fin n) : (intH Fr u).card ≤ (pinNX ς u).card := by
  refine card_le_card fun b hb => ?_
  simp only [intH, pinNX, mem_filter, mem_univ, true_and] at hb ⊢
  exact hFrς (u, b) hb

theorem pe_colH_card_le {n : ℕ} {ς : Fin n → Fin n → ℤ} {Fr : Finset (Fin n × Fin n)}
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) (b : Fin n) : (peColH Fr b).card ≤ (pinNY ς b).card := by
  refine card_le_card fun a ha => ?_
  simp only [peColH, pinNY, mem_filter, mem_univ, true_and] at ha ⊢
  exact hFrς (a, b) ha

omit [Field F] [DecidableEq F] in
/-- `∏_v F^pin_v ≤ (exp(γ_pin 2^ϖ oc^pin + (n - k) r² n 2^{Δ_pin}) / (1 - e^pin_ϖ)^{n-k})²` over the
`2(n - k)` non-witness vertices (`1 + x ≤ e^x`). -/
theorem peFactor_le {q : ℝ} (hq : 0 < q) {n z ϖ Δ : ℕ} (he : ePin q n z ϖ < 1)
    (pin : Fin n → F → ℤ) (hϖ : ∀ j, pinCount pin j ≤ ϖ) (ς : Fin n → Fin n → ℤ)
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Fr : Finset (Fin n × Fin n)) (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ}
    (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k) (hWk : W.card = k)
    (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz) :
    peFactor q n z ϖ pin Fr V W Cx Cz ≤
      (Real.exp (peGamma q n z Δ * 2 ^ ϖ * peOc Fr V W Cx Cz +
          ((n - k : ℕ) : ℝ) * ((Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ)) /
        (1 - ePin q n z ϖ) ^ (n - k)) ^ 2 := by
  set e := ePin q n z ϖ
  set R := (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ
  set γ := peGamma q n z Δ
  have h1e : 0 < 1 - e := by linarith
  set xr : ℕ → ℝ := fun h => 2 ^ ϖ * 2 ^ h * (2 * γ) + R with hxr
  have hX : ∀ (S : Finset (Fin n)) (hh : Fin n → ℕ), (∀ v ∈ S, ϖ + hh v ≤ Δ) →
      ∏ v ∈ S, peF q n z ϖ (pinCount pin v) (hh v) ≤
        Real.exp (∑ v ∈ S, xr (hh v)) / (1 - e) ^ S.card := by
    intro S hh hS
    exact pe_prod_le_exp (fun v _ => peF_nonneg hq he _ _)
      (fun v hv => peF_le_exp hq he (hϖ v) (hS v hv))
  have h1 := hX (univ \ (V ∪ Cx)) (fun u => (intH Fr u).card)
    (fun u _ => (Nat.add_le_add_left (pe_intH_card_le hFrς u) ϖ).trans (hΔX u))
  have h2 := hX Cz (fun b => (peColH Fr b).card)
    (fun b _ => (Nat.add_le_add_left (pe_colH_card_le hFrς b) ϖ).trans (hΔY b))
  have h3 := hX (univ \ (W ∪ Cz)) (fun u => (peColH Fr u).card)
    (fun u _ => (Nat.add_le_add_left (pe_colH_card_le hFrς u) ϖ).trans (hΔY u))
  have h4 := hX Cx (fun b => (intH Fr b).card)
    (fun b _ => (Nat.add_le_add_left (pe_intH_card_le hFrς b) ϖ).trans (hΔX b))
  have hcard : (univ \ (V ∪ Cx)).card + Cz.card + (univ \ (W ∪ Cz)).card + Cx.card =
      2 * (n - k) := by
    rw [card_sdiff_of_subset (subset_univ _), card_sdiff_of_subset (subset_univ _),
      card_union_of_disjoint (disjoint_left.mpr hVC), card_union_of_disjoint (disjoint_left.mpr hWC),
      card_univ, Fintype.card_fin, hVk, hWk]
    have e1 : k + Cx.card ≤ n := by
      rw [← hVk, ← card_union_of_disjoint (disjoint_left.mpr hVC)]
      exact (card_le_univ _).trans (by simp)
    have e2 : k + Cz.card ≤ n := by
      rw [← hWk, ← card_union_of_disjoint (disjoint_left.mpr hWC)]
      exact (card_le_univ _).trans (by simp)
    omega
  have hP0 : ∀ (S : Finset (Fin n)) (hh : Fin n → ℕ),
      0 ≤ ∏ v ∈ S, peF q n z ϖ (pinCount pin v) (hh v) :=
    fun S hh => prod_nonneg fun v _ => peF_nonneg hq he _ _
  unfold peFactor
  calc (∏ u ∈ univ \ (V ∪ Cx), peF q n z ϖ (pinCount pin u) (intH Fr u).card) *
        (∏ b ∈ Cz, peF q n z ϖ (pinCount pin b) (peColH Fr b).card) *
        (∏ u ∈ univ \ (W ∪ Cz), peF q n z ϖ (pinCount pin u) (peColH Fr u).card) *
        ∏ b ∈ Cx, peF q n z ϖ (pinCount pin b) (intH Fr b).card
      ≤ (Real.exp (∑ v ∈ univ \ (V ∪ Cx), xr (intH Fr v).card) /
            (1 - e) ^ (univ \ (V ∪ Cx)).card) *
          (Real.exp (∑ v ∈ Cz, xr (peColH Fr v).card) / (1 - e) ^ Cz.card) *
          (Real.exp (∑ v ∈ univ \ (W ∪ Cz), xr (peColH Fr v).card) /
            (1 - e) ^ (univ \ (W ∪ Cz)).card) *
          (Real.exp (∑ v ∈ Cx, xr (intH Fr v).card) / (1 - e) ^ Cx.card) := by
        have hE0 : ∀ (S : Finset (Fin n)) (hh : Fin n → ℕ),
            0 ≤ Real.exp (∑ v ∈ S, xr (hh v)) / (1 - e) ^ S.card :=
          fun S hh => div_nonneg (Real.exp_pos _).le (pow_nonneg h1e.le _)
        refine mul_le_mul (mul_le_mul (mul_le_mul h1 h2 (hP0 _ _) (hE0 _ _)) h3 (hP0 _ _)
          (mul_nonneg (hE0 _ _) (hE0 _ _))) h4 (hP0 _ _)
          (mul_nonneg (mul_nonneg (hE0 _ _) (hE0 _ _)) (hE0 _ _))
    _ = Real.exp (2 * (γ * 2 ^ ϖ * peOc Fr V W Cx Cz + ((n - k : ℕ) : ℝ) * R)) /
          (1 - e) ^ (2 * (n - k)) := by
        rw [← hcard, pow_add, pow_add, pow_add]
        have hsum : (∑ v ∈ univ \ (V ∪ Cx), xr (intH Fr v).card) +
            (∑ v ∈ Cz, xr (peColH Fr v).card) + (∑ v ∈ univ \ (W ∪ Cz), xr (peColH Fr v).card) +
            (∑ v ∈ Cx, xr (intH Fr v).card) =
            2 * (γ * 2 ^ ϖ * peOc Fr V W Cx Cz + ((n - k : ℕ) : ℝ) * R) := by
          have hnk : (((n - k : ℕ) : ℝ)) * 2 = (((univ \ (V ∪ Cx)).card + Cz.card +
              (univ \ (W ∪ Cz)).card + Cx.card : ℕ) : ℝ) := by
            rw [hcard]; push_cast; ring
          simp only [hxr, sum_add_distrib, sum_const, nsmul_eq_mul, ← mul_sum, ← sum_mul]
          unfold peOc
          have : ((n - k : ℕ) : ℝ) * R * 2 = (((univ \ (V ∪ Cx)).card + Cz.card +
              (univ \ (W ∪ Cz)).card + Cx.card : ℕ) : ℝ) * R := by rw [← hnk]; ring
          push_cast at this
          linear_combination (-1 : ℝ) * this
        rw [← hsum, Real.exp_add, Real.exp_add, Real.exp_add]
        field_simp
    _ = _ := by
        rw [div_pow, ← Real.exp_nat_mul, ← pow_mul]
        congr 1
        congr 1
        ring

/-- **`eq:push:pinnedclass`** (`prop:pinned-extraction`, the class bound in the paper's form, any
witness size `k`; the paper has `k = 2`): under `e^pin_ϖ < 1` and `Δ_pin ≥ ϖ + |N_X(i)|,
ϖ + |N_Y(i)|`,
`|E_{x,y∼μ} f(x) K_𝒞(x, y) h(y)| ≤ c_ker r^k 2^{ex^pin/2 + kϖ} Λ^pin_0 exp(γ_pin 2^ϖ oc^pin)
‖f‖_μ ‖h‖_μ`, `ex^pin = f_V + f_W`, `2^{ex^pin/2}` written `√(2^{ex^pin})`. -/
theorem pinned_extraction_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (P Fr : Finset (Fin n × Fin n))
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * classKer ς P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  refine (pe_class_sum_le hW M pin hpin hpinM ϖ hϖ he ς hς P Fr hFrς V W Cx Cz hVk hWk hVC hWC
    hP hFr hcker hker f h).trans ?_
  set e := ePin q n M.card ϖ
  set ex := (Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card
  set tV := ∑ v ∈ V, pinCount pin v
  set tW := ∑ v ∈ W, pinCount pin v
  set R := (Real.sqrt q)⁻¹ ^ 2 * n * 2 ^ Δ
  set γ := peGamma q n M.card Δ
  set oc := peOc Fr V W Cx Cz
  set PF := peFactor q n M.card ϖ pin Fr V W Cx Cz
  have h1e : 0 < 1 - e := by linarith
  have he0 : 0 ≤ e := ePin_nonneg _ _ _ _
  set Sf := Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card)
  set Sh := Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)
  have hSf : 0 ≤ Sf := Real.sqrt_nonneg _
  have hSh : 0 ≤ Sh := Real.sqrt_nonneg _
  have hPF := peFactor_le hq0 he pin hϖ ς hΔX hΔY Fr hFrς V W Cx Cz hVk hWk hVC hWC
  have hPF0 : 0 ≤ PF := mul_nonneg (mul_nonneg (mul_nonneg
    (prod_nonneg fun u _ => peF_nonneg hq0 he _ _) (prod_nonneg fun u _ => peF_nonneg hq0 he _ _))
    (prod_nonneg fun u _ => peF_nonneg hq0 he _ _)) (prod_nonneg fun u _ => peF_nonneg hq0 he _ _)
  set E := Real.exp (γ * 2 ^ ϖ * oc + ((n - k : ℕ) : ℝ) * R) / (1 - e) ^ (n - k)
  have hE0 : 0 ≤ E := div_nonneg (Real.exp_pos _).le (pow_nonneg h1e.le _)
  have hsqPF : Real.sqrt PF ≤ E := by
    rw [← Real.sqrt_sq hE0]
    exact Real.sqrt_le_sqrt hPF
  have htV : tV ≤ k * ϖ := by
    calc tV ≤ ∑ _v ∈ V, ϖ := sum_le_sum fun v _ => hϖ v
      _ = k * ϖ := by rw [sum_const, hVk, smul_eq_mul]
  have htW : tW ≤ k * ϖ := by
    calc tW ≤ ∑ _v ∈ W, ϖ := sum_le_sum fun v _ => hϖ v
      _ = k * ϖ := by rw [sum_const, hWk, smul_eq_mul]
  have hsq2 : Real.sqrt ((2 : ℝ) ^ (tV + tW)) ≤ 2 ^ (k * ϖ) := by
    rw [show (2 : ℝ) ^ (k * ϖ) = Real.sqrt ((2 ^ (k * ϖ)) ^ 2) from
      (Real.sqrt_sq (by positivity)).symm]
    apply Real.sqrt_le_sqrt
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hsplit : Real.sqrt (2 ^ (ex + tV + tW) * PF) =
      Real.sqrt ((2 : ℝ) ^ ex) * Real.sqrt ((2 : ℝ) ^ (tV + tW)) * Real.sqrt PF := by
    rw [show ex + tV + tW = ex + (tV + tW) by ring, pow_add, Real.sqrt_mul (by positivity),
      Real.sqrt_mul (by positivity)]
  rw [hsplit]
  -- the constants
  have hR0 : 0 ≤ R := by positivity
  have hnk : ((n - k : ℕ) : ℝ) * R ≤ (Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ := by
    have : ((n - k : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.sub_le n k
    calc ((n - k : ℕ) : ℝ) * R ≤ n * R := mul_le_mul_of_nonneg_right this hR0
      _ = _ := by simp only [R]; ring
  have hRpin : 1 ≤ peRpin q n M.card ϖ := by
    unfold peRpin
    exact one_le_pow₀ (by rw [one_le_div h1e]; linarith)
  have hkn : k ≤ n := hVk ▸ (card_le_univ V).trans (by simp)
  have hconst : E / (1 - e) ^ k ≤ peLambda0 q n M.card ϖ Δ * Real.exp (γ * 2 ^ ϖ * oc) := by
    have hpow1 : (1 - e) ^ (n + 2) ≤ (1 - e) ^ (n - k) * (1 - e) ^ k := by
      rw [← pow_add]
      exact pow_le_pow_of_le_one h1e.le (by linarith) (by omega)
    have hexp : Real.exp (((n - k : ℕ) : ℝ) * R) ≤
        Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) := Real.exp_le_exp.mpr hnk
    have hC : 0 < (1 - e) ^ (n + 2) := pow_pos h1e _
    have hR2 : 1 ≤ peRpin q n M.card ϖ ^ 2 := one_le_pow₀ hRpin
    have hnum : Real.exp (γ * 2 ^ ϖ * oc) * Real.exp (((n - k : ℕ) : ℝ) * R) ≤
        peRpin q n M.card ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) *
          Real.exp (γ * 2 ^ ϖ * oc) := by
      have h3 : Real.exp (((n - k : ℕ) : ℝ) * R) ≤
          peRpin q n M.card ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ) :=
        hexp.trans (le_mul_of_one_le_left (Real.exp_pos _).le hR2)
      calc Real.exp (γ * 2 ^ ϖ * oc) * Real.exp (((n - k : ℕ) : ℝ) * R)
          ≤ Real.exp (γ * 2 ^ ϖ * oc) *
              (peRpin q n M.card ϖ ^ 2 * Real.exp ((Real.sqrt q)⁻¹ ^ 2 * n ^ 2 * 2 ^ Δ)) :=
            mul_le_mul_of_nonneg_left h3 (Real.exp_pos _).le
        _ = _ := by ring
    have key := div_le_div₀ (by positivity) hnum hC hpow1
    calc E / (1 - e) ^ k
        = Real.exp (γ * 2 ^ ϖ * oc) * Real.exp (((n - k : ℕ) : ℝ) * R) /
            ((1 - e) ^ (n - k) * (1 - e) ^ k) := by
          simp only [E]
          rw [Real.exp_add, div_div]
      _ ≤ _ := key
      _ = _ := by
          unfold peLambda0
          ring
  have hc0 : 0 ≤ cker * (Real.sqrt q)⁻¹ ^ k := by positivity
  have h2ex : 0 ≤ Real.sqrt ((2 : ℝ) ^ ex) := Real.sqrt_nonneg _
  calc cker * (Real.sqrt q)⁻¹ ^ k *
        (Real.sqrt ((2 : ℝ) ^ ex) * Real.sqrt ((2 : ℝ) ^ (tV + tW)) * Real.sqrt PF) /
        (1 - e) ^ k * Sf * Sh
      = (cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt ((2 : ℝ) ^ ex)) *
          (Real.sqrt ((2 : ℝ) ^ (tV + tW)) * (Real.sqrt PF / (1 - e) ^ k)) * Sf * Sh := by ring
    _ ≤ (cker * (Real.sqrt q)⁻¹ ^ k * Real.sqrt ((2 : ℝ) ^ ex)) *
          (2 ^ (k * ϖ) * (peLambda0 q n M.card ϖ Δ * Real.exp (γ * 2 ^ ϖ * oc))) * Sf * Sh := by
        refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left ?_ (mul_nonneg hc0 h2ex)) hSf) hSh
        refine mul_le_mul hsq2 ?_ (div_nonneg (Real.sqrt_nonneg _) (pow_nonneg h1e.le _))
          (by positivity)
        calc Real.sqrt PF / (1 - e) ^ k ≤ E / (1 - e) ^ k :=
              div_le_div_of_nonneg_right hsqPF (pow_nonneg h1e.le _)
          _ ≤ _ := hconst
    _ = _ := by ring

/-- **`prop:pinned-extraction`, the class bound `eq:push:pinnedclass`** for a class `𝒞(P, A)` of
`Ex ⊆ E_×` with a witness `w` of size `k` (`IsWitness`) and a cover (`IsCover`; any orders): with
the pinned law `μ` uniform on `𝓘_pin` and `‖𝖶‖ ≤ c_ker r^k` on injective tuples,
`|∑_{S ∈ 𝒞} ⟨f, T_S h⟩_μ| ≤ c_ker r^k 2^{ex^pin(𝒞)/2 + kϖ} Λ^pin_0 exp(γ_pin 2^ϖ oc^pin(𝒞))
‖f‖_μ ‖h‖_μ` (the paper: `k = 2`, `c_ker ∈ {1, 2}`), written with `E_μ = |𝓘_pin|⁻¹ ∑`. -/
theorem pinned_extraction (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex P A : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (hcls : IsClassDatum Ex (P, A)) {k : ℕ} (w : Fin k → Fin n × Fin n)
    (hw : IsWitness Ex P A w) (Cx Cz : Finset (Fin n)) (hcov : IsCover Ex P A w Cx Cz)
    {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F (witV w)) (injTuples F (witW w))
      (rectKer ς P (witV w) (witW w)) (cker * Real.sqrt (Fintype.card F) ^ k))
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x y) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ (((Ex \ (P ∪ A)).filter (fun e => e.1 ∈ witV w)).card +
          ((Ex \ (P ∪ A)).filter (fun e => e.2 ∈ witW w)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ *
          peOc (Ex \ (P ∪ A)) (witV w) (witW w) Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨hP, -, hPA⟩ := hcls
  have hK : ∀ x y : Fin n → F, ∑ S ∈ cls Ex P A, ∏ e ∈ S, chiPair ς e x y =
      classKer ς P (Ex \ (P ∪ A)) x y := fun x y => sum_cls_eq_classKer ς Ex P A hP hPA x y
  simp only [hK]
  set Fr := Ex \ (P ∪ A) with hFr
  have hrect : ∀ e : Fin n × Fin n, e.1 ∈ witV w ∧ e.2 ∈ witW w ↔
      (∃ i, (w i).1 = e.1) ∧ ∃ l, (w l).2 = e.2 := by
    intro e
    simp [witV, witW]
  have hFrEx : ∀ e ∈ Fr, e ∈ Ex := fun e he => (mem_sdiff.mp he).1
  have hP' : ∀ e ∈ P, (e.1 ∈ witV w ∧ e.2 ∈ witW w) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    by_cases hr : e.1 ∈ witV w ∧ e.2 ∈ witW w
    · exact Or.inl hr
    · exact Or.inr (hcov.cover e (mem_union_left _ he) (by rwa [← hrect]))
  have hFr' : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz := by
    intro e he
    refine hcov.cover e (mem_union_right _ he) fun hr => ?_
    have := hw.decided e (hFrEx e he) hr.1 hr.2
    exact (mem_sdiff.mp he).2 (mem_union.mpr this)
  have hVC : ∀ u ∈ witV w, u ∉ Cx := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.fst_not_mem i
  have hWC : ∀ u ∈ witW w, u ∉ Cz := by
    intro u hu
    obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hcov.snd_not_mem i
  have hVk : (witV w).card = k := by
    unfold witV
    rw [card_image_of_injective _ hw.injective_fst, card_univ, Fintype.card_fin]
  have hWk : (witW w).card = k := by
    unfold witW
    rw [card_image_of_injective _ hw.injective_snd, card_univ, Fintype.card_fin]
  exact pinned_extraction_sum_le hW M pin hpin hpinM ϖ hϖ he ς hς hΔX hΔY P Fr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' hcker
    hker f h

/-- **`prop:pinned-extraction`, the bucket sum `N^pin`**: for an exact partition `𝔓` of the
nonstar subsets of `Ex` into classes with witnesses of size two, covers and kernel constants
`c_ker(𝒞)`, and bucket indices `𝔟 ≥ oc^pin(𝒞) 2^{-𝔮}`, the nonstar part of the pinned row satisfies
`|∑_{S nonstar} ⟨f, T_S h⟩_μ| ≤ r² Λ^pin_0 2^{2ϖ} ∑_𝔟 (∑_{𝒞 ↦ 𝔟} c_ker(𝒞) 2^{ex^pin(𝒞)/2})
exp(γ_pin 2^ϖ 𝔟 2^𝔮) ‖f‖_μ ‖h‖_μ` (the paper's `𝖺_𝔟 + 𝖻_𝔟 √2` is the inner sum). -/
theorem pinned_extraction_buckets (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (Ex : Finset (Fin n × Fin n)) (hEx : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (𝔓 : Finset (Finset (Fin n × Fin n) × Finset (Fin n × Fin n)))
    (h𝔓 : IsExactPartition Ex 𝔓 (nonstars Ex))
    (wit : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Fin 2 → Fin n × Fin n)
    (cx cz : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → Finset (Fin n))
    (ck : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℝ)
    (bucket : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) → ℕ) (𝔮 : ℕ)
    (hwit : ∀ c ∈ 𝔓, IsWitness Ex c.1 c.2 (wit c))
    (hcov : ∀ c ∈ 𝔓, IsCover Ex c.1 c.2 (wit c) (cx c) (cz c))
    (hck : ∀ c ∈ 𝔓, 0 ≤ ck c)
    (hker : ∀ c ∈ 𝔓, Sarkozy.Influence.OpBound (injTuples F (witV (wit c)))
      (injTuples F (witW (wit c))) (rectKer ς c.1 (witV (wit c)) (witW (wit c)))
      (ck c * Real.sqrt (Fintype.card F) ^ 2))
    (hbucket : ∀ c ∈ 𝔓, peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c) (cz c) ≤
      (bucket c : ℝ) * 2 ^ 𝔮)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x y) * h y) /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      (Real.sqrt (Fintype.card F))⁻¹ ^ 2 * peLambda0 (Fintype.card F) n M.card ϖ Δ * 2 ^ (2 * ϖ) *
        (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
            ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))) *
          Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * (b * 2 ^ 𝔮))) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨hdat, hdisj, hunion⟩ := h𝔓
  set I := pinLab M pin
  set N : ℝ := (I.card : ℝ)
  set r := (Real.sqrt (Fintype.card F))⁻¹
  set L := peLambda0 (Fintype.card F) n M.card ϖ Δ
  set γ := peGamma (Fintype.card F) n M.card Δ
  set Nf := Real.sqrt ((∑ x ∈ I, f x ^ 2) / N)
  set Nh := Real.sqrt ((∑ x ∈ I, h x ^ 2) / N)
  set exc := fun c : Finset (Fin n × Fin n) × Finset (Fin n × Fin n) =>
    Real.sqrt (2 ^ (((Ex \ (c.1 ∪ c.2)).filter (fun e => e.1 ∈ witV (wit c))).card +
      ((Ex \ (c.1 ∪ c.2)).filter (fun e => e.2 ∈ witW (wit c))).card))
  have hsplit : ∀ x y : Fin n → F, (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x y) =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y := by
    intro x y
    rw [← hunion, sum_biUnion hdisj]
  have hform : (∑ x ∈ I, ∑ y ∈ I, f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x y) * h y) /
      N ^ 2 = ∑ c ∈ 𝔓, (∑ x ∈ I, ∑ y ∈ I,
        f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y) * h y) / N ^ 2 := by
    rw [← sum_div]
    congr 1
    have hT : ∀ x y : Fin n → F, f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x y) * h y =
        ∑ c ∈ 𝔓, f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y) * h y := by
      intro x y
      rw [hsplit, mul_sum, sum_mul]
    calc ∑ x ∈ I, ∑ y ∈ I, f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x y) * h y
        = ∑ x ∈ I, ∑ y ∈ I, ∑ c ∈ 𝔓,
            f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y) * h y :=
          sum_congr rfl fun x _ => sum_congr rfl fun y _ => hT x y
      _ = ∑ x ∈ I, ∑ c ∈ 𝔓, ∑ y ∈ I,
            f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y) * h y :=
          sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hform]
  have hγ : 0 ≤ γ := by
    simp only [γ, peGamma]
    positivity
  have hL : 0 ≤ L := by
    have h1e : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
    simp only [L, peLambda0, peRpin]
    have : 0 ≤ (1 + ePin (Fintype.card F) n M.card ϖ) /
        (1 - ePin (Fintype.card F) n M.card ϖ) :=
      div_nonneg (by linarith [ePin_nonneg (Fintype.card F : ℝ) n M.card ϖ]) h1e.le
    positivity
  have hclass : ∀ c ∈ 𝔓, |(∑ x ∈ I, ∑ y ∈ I,
      f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y) * h y) / N ^ 2| ≤
      r ^ 2 * L * 2 ^ (2 * ϖ) * (ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) *
        Nf * Nh := by
    intro c hc
    have hb := pinned_extraction hW M pin hpin hpinM ϖ hϖ he ς hς hΔX hΔY Ex c.1 c.2 hEx
      (hdat c hc) (wit c) (hwit c hc) (cx c) (cz c) (hcov c hc) (hck c hc) (hker c hc) f h
    refine hb.trans ?_
    have hexp : Real.exp (γ * 2 ^ ϖ * peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c))
        (cx c) (cz c)) ≤ Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hbucket c hc) (by positivity))
    have h0 : 0 ≤ ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L := by
      have := hck c hc
      positivity
    have hN : 0 ≤ Nf * Nh := by positivity
    calc ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L *
          Real.exp (γ * 2 ^ ϖ * peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
            (cz c)) * Nf * Nh
        = (ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L) *
          Real.exp (γ * 2 ^ ϖ * peOc (Ex \ (c.1 ∪ c.2)) (witV (wit c)) (witW (wit c)) (cx c)
            (cz c)) * (Nf * Nh) := by ring
      _ ≤ (ck c * r ^ 2 * exc c * 2 ^ (2 * ϖ) * L) *
            Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮)) * (Nf * Nh) := by
          gcongr
      _ = _ := by ring
  calc |∑ c ∈ 𝔓, (∑ x ∈ I, ∑ y ∈ I,
        f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, chiPair ς e x y) * h y) / N ^ 2|
      ≤ ∑ c ∈ 𝔓, r ^ 2 * L * 2 ^ (2 * ϖ) *
          (ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) * Nf * Nh :=
        (abs_sum_le_sum_abs _ _).trans (sum_le_sum hclass)
    _ = r ^ 2 * L * 2 ^ (2 * ϖ) *
          (∑ c ∈ 𝔓, ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) * Nf * Nh := by
        rw [mul_sum, sum_mul, sum_mul]
    _ = r ^ 2 * L * 2 ^ (2 * ϖ) * (∑ b ∈ 𝔓.image bucket, (∑ c ∈ 𝔓.filter (fun c => bucket c = b),
          ck c * exc c) * Real.exp (γ * 2 ^ ϖ * (b * 2 ^ 𝔮))) * Nf * Nh := by
        congr 3
        rw [← sum_fiberwise_of_maps_to (fun c hc => mem_image_of_mem bucket hc)]
        refine sum_congr rfl fun b _ => ?_
        rw [sum_mul]
        refine sum_congr rfl fun c hc => ?_
        rw [(mem_filter.mp hc).2]

end PeConst

end Sarkozy.ExtractionK

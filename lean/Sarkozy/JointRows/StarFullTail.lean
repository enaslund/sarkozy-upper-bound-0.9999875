module

public import Sarkozy.JointRows.StarUncenteredTerm
public import Sarkozy.SpectralD.TailErrorBounds

/-! Full star operator bounds used for the normalizer and marginal errors in the tail. -/

@[expose] public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

set_option maxHeartbeats 800000

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

universe u

variable {p : ℕ} [Fact p.Prime] {X : Type u} [Fintype X] [DecidableEq X]

theorem raw_star_tail_term (hp : 2 ^ 512 ≤ p) (hn : Fintype.card X ≤ 12)
    (ν : X → FiniteLaw (ZMod p))
    (hdens : ∀ i t, (ν i).weight t ≤ 32 / p)
    (hm : ∀ i j t, (ν i).weight t ≠ 0 → |mchi (ν j) t| ≤ 1024 * (Real.sqrt p)⁻¹)
    (i : X) (T : Finset X) (hT : T.Nonempty) {c : ℝ} (hc : |c| ≤ 1)
    (f g : (X → ZMod p) → ℝ) :
    |bform ν ν (fun x y => c * ∏ j ∈ T, chiR p (x i - y j)) f g| ≤
      2 ^ 24 * (Real.sqrt p)⁻¹ * nrm (blockLaw ν) f * nrm (blockLaw ν) g := by
  have hβ : (1024 : ℝ) * (Real.sqrt p)⁻¹ ≤ 1 := by
    have hr := mul_le_mul_of_nonneg_left (SpectralD.tail_rp_le hp)
      (by norm_num : (0 : ℝ) ≤ 1024)
    exact hr.trans (by norm_num)
  have h := row_star_full_bound (by omega) ν ν i T hT hc (by norm_num) (by positivity)
    hβ (hdens i) (fun j _ => hdens j) (fun j _ => hm i j) f g
  have ht : (2 : ℝ) ^ T.card ≤ 2 ^ 12 := pow_le_pow_right₀ (by norm_num)
    ((card_le_univ T).trans hn)
  have hr := inv_nonneg.mpr (Real.sqrt_nonneg (p : ℝ))
  have hnum := mul_le_mul_of_nonneg_right ht
    (show (0 : ℝ) ≤ 32 * (Real.sqrt p)⁻¹ + 1024 * (Real.sqrt p)⁻¹ by positivity)
  have hcoef : (2 : ℝ) ^ T.card *
      (32 * (Real.sqrt p)⁻¹ + 1024 * (Real.sqrt p)⁻¹) ≤ 2 ^ 24 * (Real.sqrt p)⁻¹ := by
    nlinarith
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (FiveType.nrm_nonneg _ _))
    (FiveType.nrm_nonneg _ _))

theorem star_full_tail (hp : 2 ^ 512 ≤ p) (hn : Fintype.card X ≤ 12)
    (ν : X → FiniteLaw (ZMod p)) (D : X → X → ℝ)
    (hD : ∀ i j, |D i j| ≤ 1)
    (hdens : ∀ i t, (ν i).weight t ≤ 32 / p)
    (hm : ∀ i j t, (ν i).weight t ≠ 0 → |mchi (ν j) t| ≤ 1024 * (Real.sqrt p)⁻¹) :
    FormBound (blockLaw ν) (starKernel D (sets2 X)) (2 ^ 42 * (Real.sqrt p)⁻¹) := by
  intro f g
  rw [kf_eq_bform]
  let B : ℝ := 2 ^ 24 * (Real.sqrt p)⁻¹ * nrm (blockLaw ν) f * nrm (blockLaw ν) g
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤
    2 ^ 24 * (Real.sqrt p)⁻¹) (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)
  have hrow (i : X) (T : Finset X) (hT : T.Nonempty) :
      |bform ν ν (fun x y => ∏ j ∈ T, D i j * chiR p (y j - x i)) f g| ≤ B := by
    have heq : (fun (x y : X → ZMod p) => ∏ j ∈ T, D i j * chiR p (y j - x i)) =
        fun x y => rowParityCoef (p := p) D i T * ∏ j ∈ T, chiR p (x i - y j) := by
      funext x y
      have h1 (j : X) : D i j * chiR p (y j - x i) =
          (chiR p (-1) * D i j) * chiR p (x i - y j) := by
        rw [show y j - x i = -(x i - y j) by ring, chiR_neg_all]
        ring
      rw [prod_congr rfl fun j _ => h1 j, prod_mul_distrib]
      simp only [rowParityCoef, prod_mul_distrib, prod_const]
    rw [heq]
    exact raw_star_tail_term hp hn ν hdens hm i T hT (abs_rowParityCoef_le_one D hD i T) f g
  have hcol (j : X) (T : Finset X) (hT : T.Nonempty) :
      |bform ν ν (fun x y => ∏ i ∈ T, D i j * chiR p (y j - x i)) f g| ≤ B := by
    rw [bform_swap]
    have heq : (fun (y x : X → ZMod p) => ∏ i ∈ T, D i j * chiR p (y j - x i)) =
        fun y x => coefB D j T * ∏ i ∈ T, chiR p (y j - x i) := by
      funext y x
      rw [prod_mul_distrib]
      rfl
    rw [heq]
    have h := raw_star_tail_term hp hn ν hdens hm j T hT (abs_coefB_le_one D hD j T) g f
    convert h using 1
    dsimp [B]
    ring
  have hsingle (i j : X) :
      |bform ν ν (fun x y => D i j * chiR p (y j - x i)) f g| ≤ B := by
    simpa only [prod_singleton] using hrow i {j} (singleton_nonempty j)
  have hT (T : Finset X) (h : T ∈ sets2 X) : T.Nonempty :=
    card_pos.mp (by have := mem_sets2.mp h; omega)
  have sum_bound {I J : Type u} (s : Finset I) (t : Finset J) (a : I → J → ℝ)
      (ha : ∀ i ∈ s, ∀ j ∈ t, |a i j| ≤ B) :
      |∑ i ∈ s, ∑ j ∈ t, a i j| ≤ (s.card : ℝ) * t.card * B := by
    calc
      _ ≤ ∑ i ∈ s, ∑ j ∈ t, |a i j| := (abs_sum_le_sum_abs _ _).trans
        (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _i ∈ s, ∑ _j ∈ t, B := sum_le_sum fun i hi =>
        sum_le_sum fun j hj => ha i hi j hj
      _ = _ := by simp; ring
  have h1 : |∑ i : X, ∑ j : X,
      bform ν ν (fun x y => D i j * chiR p (y j - x i)) f g| ≤
      (Fintype.card X : ℝ) * Fintype.card X * B := by
    simpa only [card_univ] using sum_bound (univ : Finset X) (univ : Finset X)
      (fun i j => bform ν ν (fun x y => D i j * chiR p (y j - x i)) f g)
      (fun i _ j _ => hsingle i j)
  have h2 : |∑ i : X, ∑ T ∈ sets2 X,
      bform ν ν (fun x y => ∏ j ∈ T, D i j * chiR p (y j - x i)) f g| ≤
      (Fintype.card X : ℝ) * (sets2 X).card * B := by
    simpa only [card_univ] using sum_bound (univ : Finset X) (sets2 X)
      (fun i T => bform ν ν (fun x y => ∏ j ∈ T, D i j * chiR p (y j - x i)) f g)
      (fun i _ T h => hrow i T (hT T h))
  have h3 : |∑ j : X, ∑ T ∈ sets2 X,
      bform ν ν (fun x y => ∏ i ∈ T, D i j * chiR p (y j - x i)) f g| ≤
      (Fintype.card X : ℝ) * (sets2 X).card * B := by
    simpa only [card_univ] using sum_bound (univ : Finset X) (sets2 X)
      (fun j T => bform ν ν (fun x y => ∏ i ∈ T, D i j * chiR p (y j - x i)) f g)
      (fun j _ T h => hcol j T (hT T h))
  have hnR : (Fintype.card X : ℝ) ≤ 12 := by exact_mod_cast hn
  have hs : ((sets2 X).card : ℝ) ≤ 2 ^ 12 := by
    exact_mod_cast (calc
      (sets2 X).card ≤ Fintype.card (Finset X) := card_le_univ _
      _ = 2 ^ Fintype.card X := Fintype.card_finset
      _ ≤ 2 ^ 12 := Nat.pow_le_pow_right (by omega) hn)
  have hcoef : (Fintype.card X : ℝ) * Fintype.card X +
      2 * Fintype.card X * (sets2 X).card ≤ 2 ^ 18 := by
    have ha : (Fintype.card X : ℝ) * Fintype.card X ≤ 12 * 12 := by gcongr
    have hb : (2 : ℝ) * Fintype.card X * (sets2 X).card ≤ 2 * 12 * 2 ^ 12 := by gcongr
    linarith
  unfold starKernel
  simp only [bform_add, bform_sum]
  have hnum := mul_le_mul_of_nonneg_right hcoef hB
  apply (abs_add_le _ _).trans
  apply (add_le_add (abs_add_le _ _) le_rfl).trans
  dsimp [B] at h1 h2 h3 hnum
  nlinarith

end Sarkozy.JointRows.StarOps

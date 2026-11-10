module

public import Sarkozy.SpectralD.SmallExtractionScalars

/-!
# A uniform nonstar estimate for the smaller tail cuts

For a half with at most eighteen vertices and at most ninety-six cross
edges, singleton extraction bounds every nonstar monomial by 2^100/p.
Summing over all subsets gives 2^196/p, hence at most 2^(-50)/sqrt(p)
at p ≥ 2^512. No enumeration certificate is needed for this estimate.
-/

@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.SpectralD

open Finset Sarkozy.Extraction Sarkozy.ExtractionK Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

theorem small_nonstar_monomial (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hn : Fintype.card U ≤ 18)
    (hne : (injLabellings (ZMod p) G).Nonempty) (S : Finset (U × U))
    (hS : IsNonstar S) (hsign : ∀ e ∈ S, ς e.1 e.2 ≠ 0)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      2 ^ 100 * (Real.sqrt p)⁻¹ ^ 2 *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  obtain ⟨w, hw⟩ := singleton_witness hS
  have hb := extraction_compressed_class_two (by omega) h4 hW G ς hς hanti hne hn
    (ehat := 1 / 100)
    (fun i => by simpa only [ZMod.card, Nat.cast_ofNat] using small_count_error G hn hp i)
    (by norm_num) (small_cmpDeg G ς hn) S S ∅ hsign
    ⟨le_rfl, empty_subset _, by simp⟩ w hw
    (univ \ witV w) (univ \ witW w) (singleton_cover S w) f h
  simp only [cls_singleton, sum_singleton, union_empty, sdiff_self, bot_eq_empty,
    ZMod.card] at hb
  have hk : (2 : ℝ) ^ twoCycleCount (witnessIdx S w) ≤ 2 := by
    simpa only [pow_one] using
      pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (cmp_twoCycleCount_le_one (witnessIdx S w))
  have hs : Real.sqrt ((2 : ℝ) ^ cmpEx G ∅ (witV w) (witW w)
      (univ \ witV w) (univ \ witW w)) ≤ 2 ^ 36 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc _ ≤ (2 : ℝ) ^ 72 := pow_le_pow_right₀ (by norm_num) (small_cmpEx_empty G hn hw)
      _ = _ := by norm_num
  have hL0 : 0 ≤ cmpLambda0 G ς p 18 (1 / 100) 2 := by
    unfold cmpLambda0
    apply div_nonneg (by positivity)
    apply mul_nonneg (by norm_num)
    exact prod_nonneg fun i _ => by
      norm_num only [Nat.cast_ofNat]
      linarith [small_count_error G hn hp i]
  have h1 := mul_le_mul hk hs (Real.sqrt_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have h2 := mul_le_mul h1 (small_cmpLambda G ς hn hp) hL0 (by positivity)
  have h3 := mul_le_mul h2 (small_occupancy_exp G hn hp (witV w) (witW w))
    (Real.exp_pos _).le (by positivity)
  have hc := mul_le_mul_of_nonneg_left h3 (sq_nonneg ((Real.sqrt p)⁻¹))
  have hcoef :
      2 ^ twoCycleCount (witnessIdx S w) * (Real.sqrt p)⁻¹ ^ 2 *
        Real.sqrt ((2 : ℝ) ^ cmpEx G ∅ (witV w) (witW w)
          (univ \ witV w) (univ \ witW w)) *
        cmpLambda0 G ς p 18 (1 / 100) 2 *
        Real.exp (cmpGamma p 18 36 * cmpOc G ∅ (witV w) (witW w)
          (univ \ witV w) (univ \ witW w)) ≤ 2 ^ 100 * (Real.sqrt p)⁻¹ ^ 2 := by
    nlinarith [sq_nonneg ((Real.sqrt p)⁻¹)]
  exact hb.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

theorem small_nonstar_bound (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hn : Fintype.card U ≤ 18)
    (hne : (injLabellings (ZMod p) G).Nonempty) (Ex : Finset (U × U))
    (hEx : Ex.card ≤ 96) (hsign : ∀ e ∈ Ex, ς e.1 e.2 ≠ 0)
    (f h : (U → ZMod p) → ℝ) :
    |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
        (∑ S ∈ nonstars Ex, ∏ e ∈ S, chiPair ς e x x') * h x'))| ≤
      2 ^ 196 * (Real.sqrt p)⁻¹ ^ 2 *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
  have hc : (nonstars Ex).card ≤ 2 ^ 96 := by
    calc _ ≤ Ex.powerset.card := card_filter_le _ _
      _ = 2 ^ Ex.card := card_powerset Ex
      _ ≤ _ := Nat.pow_le_pow_right (by omega) hEx
  have hcR : ((nonstars Ex).card : ℝ) ≤ 2 ^ 96 := by exact_mod_cast hc
  simp_rw [sum_mul, cmp_expect_sum, mul_sum]
  rw [cmp_expect_sum]
  calc _ ≤ ∑ S ∈ nonstars Ex,
        |(graphLaw G hne).expect (fun x => f x * (graphLaw G hne).expect (fun x' =>
          (∏ e ∈ S, chiPair ς e x x') * h x'))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _S ∈ nonstars Ex, 2 ^ 100 * (Real.sqrt p)⁻¹ ^ 2 *
        Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)) := by
          apply sum_le_sum
          intro S hS
          exact small_nonstar_monomial hW h4 hp G ς hς hanti hn hne S (mem_nonstars.mp hS).2
            (fun e he => hsign e ((mem_nonstars.mp hS).1 he)) f h
    _ ≤ _ := by
          rw [sum_const, nsmul_eq_mul]
          have hh := mul_le_mul_of_nonneg_right hcR
            (by positivity : 0 ≤ 2 ^ 100 * (Real.sqrt p)⁻¹ ^ 2 *
              Real.sqrt ((graphLaw G hne).expect (fun x => f x ^ 2)) *
              Real.sqrt ((graphLaw G hne).expect (fun x => h x ^ 2)))
          convert hh using 1
          ring

omit [Fact p.Prime] in
theorem small_nonstar_tail_scalar (hp : 2 ^ 512 ≤ p) :
    (2 : ℝ) ^ 196 * (Real.sqrt p)⁻¹ ^ 2 ≤ 2⁻¹ ^ 50 * (Real.sqrt p)⁻¹ := by
  have hr := mul_le_mul_of_nonneg_right (tail_rp_le hp)
    (by positivity : 0 ≤ (Real.sqrt p)⁻¹)
  have hs := mul_le_mul_of_nonneg_left hr (by positivity : (0 : ℝ) ≤ 2 ^ 196)
  nlinarith [inv_nonneg.mpr (Real.sqrt_nonneg p)]

end Sarkozy.SpectralD

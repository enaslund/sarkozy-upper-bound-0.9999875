module

public import Sarkozy.SpectralD.SmallTailCriterion

/-!
# Tighter allowances for the smaller tail spectra

The constants c = 1/1000, eta_Q = 1/100000 and eta_B = 1/100
leave enough margin for the paper's smallest chamber bound, five.
All estimates retain the actual p-dependent operators and densities.
-/

@[expose] public section

namespace Sarkozy.SpectralD.AtMost

open Finset Sarkozy.Labellings Sarkozy.SecondOrder Sarkozy.Extraction Sarkozy.SpectralC

theorem tail_perpendicular_tight {r m n d : ℝ} (hr0 : 0 ≤ r)
    (hr : r ≤ 2⁻¹ ^ 256) (hm0 : 0 ≤ m) (hn0 : 0 ≤ n) (hd0 : 0 ≤ d)
    (hm : m ≤ 2 ^ 84 * r) (hn : n ≤ 2⁻¹ ^ 50 * r) (hd : d ≤ 2⁻¹ ^ 50 * r) :
    (n + d) / (1 - 1 / 100) + ((m + n + d) / (1 - 1 / 100)) ^ 2 ≤ 1 / 1000 * r := by
  have hnd : n + d ≤ 2⁻¹ ^ 49 * r := by
    calc _ ≤ 2⁻¹ ^ 50 * r + 2⁻¹ ^ 50 * r := add_le_add hn hd
      _ = _ := by ring
  have hn' : (n + d) / (1 - 1 / 100) ≤ 2⁻¹ ^ 48 * r := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 100)).mpr
    calc n + d ≤ 2⁻¹ ^ 49 * r := hnd
      _ ≤ (2⁻¹ ^ 48 * (1 - 1 / 100)) * r :=
          mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = _ := by ring
  have hm' : (m + n + d) / (1 - 1 / 100) ≤ 2 ^ 86 * r := by
    apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 1 - 1 / 100)).mpr
    calc m + n + d = m + (n + d) := by ring
      _ ≤ 2 ^ 84 * r + 2⁻¹ ^ 49 * r := add_le_add hm hnd
      _ = (2 ^ 84 + 2⁻¹ ^ 49) * r := by ring
      _ ≤ (2 ^ 86 * (1 - 1 / 100)) * r :=
          mul_le_mul_of_nonneg_right (by norm_num) hr0
      _ = _ := by ring
  have hs := pow_le_pow_left₀ (div_nonneg (by linarith : 0 ≤ m + n + d)
    (by norm_num : (0 : ℝ) ≤ 1 - 1 / 100)) hm' 2
  calc _ ≤ 2⁻¹ ^ 48 * r + (2 ^ 86 * r) ^ 2 := add_le_add hn' hs
    _ = (2⁻¹ ^ 48 + 2 ^ 172 * r) * r := by ring
    _ ≤ (2⁻¹ ^ 48 + 2 ^ 172 * (2⁻¹ ^ 256)) * r := by gcongr
    _ ≤ 1 / 1000 * r := mul_le_mul_of_nonneg_right (by norm_num) hr0


theorem tail_coupling_entry_tight {p t : ℕ} (hp : 2 ^ 512 ≤ p) (ht : t ≤ 12)
    {e R : ℝ} (he0 : 0 ≤ e) (he : e ≤ 2⁻¹ ^ 50)
    (hR1 : 1 ≤ R) (hR : R ≤ 1 + 2⁻¹ ^ 40) :
    (2 : ℝ) ^ t * (1 + e) * devConst R e ^ 2 + 36 * 4 ^ t / p ≤ 2⁻¹ ^ 60 := by
  have hdev := tail_devConst he0 he hR1 hR
  have h1 : (2 : ℝ) ^ t * (1 + e) * devConst R e ^ 2 ≤
      2 ^ 12 * (1 + (2 : ℝ)⁻¹ ^ 50) * ((2 : ℝ)⁻¹ ^ 38) ^ 2 :=
    mul_le_mul (mul_le_mul (pow_le_pow_right₀ (by norm_num) ht)
      (by linarith) (by linarith) (by positivity))
      (pow_le_pow_left₀ hdev.1 hdev.2 2) (sq_nonneg _) (by positivity)
  have h2 : 36 * (4 : ℝ) ^ t / p ≤ 36 * 4 ^ 12 * (2 : ℝ)⁻¹ ^ 128 := by
    rw [div_eq_mul_inv]
    exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (by norm_num) ht)
      (by norm_num)) (tail_inv_prime hp) (by positivity) (by positivity)
  exact (add_le_add h1 h2).trans (by norm_num)


theorem tail_etaQ_tight {p : ℕ} (hp : 2 ^ 512 ≤ p) {d : ℝ} (hd : d ≤ 12) :
    d / ((p : ℝ) - 1) + (p : ℝ) / (p - 1) * 2⁻¹ ^ 40 +
      36 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹) ≤ 1 / 100000 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have h1 : d / ((p : ℝ) - 1) ≤ 12 * (2 : ℝ)⁻¹ ^ 40 := by
    calc _ ≤ 12 / ((p : ℝ) - 1) := div_le_div_of_nonneg_right hd (by linarith)
      _ = 12 * (1 / ((p : ℝ) - 1)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_inv_sub_one hp) (by norm_num)
  have h2 := mul_le_mul_of_nonneg_right (tail_prime_ratio hp)
    (by positivity : (0 : ℝ) ≤ 2⁻¹ ^ 40)
  have h3 : 36 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹) ≤ 72 * (2 : ℝ)⁻¹ ^ 40 := by
    calc _ = 36 * (1 / (((p : ℝ) - 1) * (Real.sqrt p)⁻¹)) := by ring
      _ ≤ 36 * (2 * (Real.sqrt p)⁻¹) :=
          mul_le_mul_of_nonneg_left (tail_root_quotient hp) (by norm_num)
      _ = 72 * (Real.sqrt p)⁻¹ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (tail_rp_le40 hp) (by norm_num)
  exact (add_le_add (add_le_add h1 h2) h3).trans (by norm_num)


theorem etaB_tail_with_parity_tight {p : ℕ} (hp : 2 ^ 512 ≤ p)
    {R Lp L ρ D ζ Λnc : ℝ} (hR : R ≤ 1 + 2⁻¹ ^ 40)
    (hLp0 : 0 ≤ Lp) (hLp : Lp ≤ 12384) (hL : L ≤ 8928)
    (hρ0 : 0 ≤ ρ) (hρ : ρ ≤ 301768740) (hD0 : 0 ≤ D) (hD : D ≤ 12)
    (hζ0 : 0 ≤ ζ) (hnc0 : 0 ≤ Λnc) (hpar : ζ * Λnc ≤ 2⁻¹ ^ 38) :
    Cx.etaBcx p R Lp (1 / 1000) 64 ρ (1 / 10000000000000000) L ζ Λnc
      (1 / 100000) D (1 / 100000) ≤ 1 / 100 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (show 1 < p by omega)
  have hfac : R * p / ((p : ℝ) - 1) ≤ 1 + 1 / 1000000000 := by
    calc _ = R * ((p : ℝ) / (p - 1)) := by ring
      _ ≤ (1 + (2 : ℝ)⁻¹ ^ 40) * (1 + (2 : ℝ)⁻¹ ^ 40) :=
          mul_le_mul hR (tail_prime_ratio_sharp hp)
            (div_nonneg (by linarith) (by linarith)) (by positivity)
      _ ≤ 1 + 1 / 1000000000 := by norm_num
  have hsqrt : Real.sqrt (1 / 10000000000000000 * (L + 1 / 1000)) ≤ 1 / 100000 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by norm_num, ?_⟩
    linarith
  have hrho : rp p * 64 * ρ ≤ (2 : ℝ)⁻¹ ^ 256 * 64 * 301768740 :=
    mul_le_mul (mul_le_mul_of_nonneg_right (tail_rp_le hp) (by norm_num))
      hρ hρ0 (by positivity)
  have hpar' : (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc ≤ 2⁻¹ ^ 38 := by
    split_ifs
    · simpa only [one_mul] using hpar
    · simp only [zero_mul]; positivity
  have hpz : 0 ≤ (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc := by
    split_ifs <;> positivity
  have hsum : 1 / 1000 + rp p * 64 * ρ +
      (2 * Real.sqrt (1 / 10000000000000000 * (L + 1 / 1000)) + 1 / 10000000000000000) +
      (if p % 4 = 1 then (1 : ℝ) else 0) * ζ * Λnc ≤ 1 / 500 := by
    norm_num only at hrho hpar'
    linarith
  have h1 : (R * p / ((p : ℝ) - 1) - 1) * Lp ≤ (1 / 1000000000) * 12384 := by
    calc _ ≤ (1 / 1000000000) * Lp := mul_le_mul_of_nonneg_right (by linarith) hLp0
      _ ≤ _ := mul_le_mul_of_nonneg_left hLp (by norm_num)
  have hrp0 : 0 ≤ rp p := by unfold rp; positivity
  have h2 := mul_le_mul hfac hsum (by positivity)
    (by norm_num : (0 : ℝ) ≤ 1 + 1 / 1000000000)
  have h3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hD0 hD 2)
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  have h4 := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hD (by norm_num : (0 : ℝ) ≤ 2))
    (by norm_num : (0 : ℝ) ≤ 1 / 100000)
  exact (add_le_add (add_le_add (add_le_add h1 h2) h3) h4).trans (by norm_num)


variable {p : ℕ} [Fact p.Prime] {U W : Type*}
  [Fintype U] [DecidableEq U] [Fintype W] [DecidableEq W]

omit [DecidableEq U] in
theorem coupling_error_tail_tight (N : U → Finset U) (R : U → ℝ) (hp : 2 ^ 512 ≤ p)
    (hn : Fintype.card U ≤ 36) (hr : ∀ k, (N k).card ≤ 12)
    (hR1 : ∀ k, 1 ≤ R k) (hR : ∀ k, R k ≤ 1 + 2⁻¹ ^ 40) :
    ∑ k, ((2 : ℝ) ^ (N k).card *
        (1 + TraceMixing.coarseErr p (N k).card (Fintype.card U)) *
        devConst (R k) (TraceMixing.coarseErr p (N k).card (Fintype.card U)) ^ 2 +
      (Fintype.card U : ℝ) * 4 ^ (N k).card / p) ≤ 1 / 10000000000000000 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc _ ≤ ∑ _k : U, (2 : ℝ)⁻¹ ^ 60 := sum_le_sum fun k _ => by
        have hnR : (Fintype.card U : ℝ) ≤ 36 := by exact_mod_cast hn
        have hterm : (Fintype.card U : ℝ) * 4 ^ (N k).card / p ≤
            36 * 4 ^ (N k).card / p := by gcongr
        apply (add_le_add le_rfl hterm).trans
        exact tail_coupling_entry_tight hp (hr k) (TraceMixing.coarseErr_nonneg hp0 _ _)
          (coarseErr_tail hp ((hr k).trans (by norm_num)) (by omega)) (hR1 k) (hR k)
    _ ≤ 36 * (2 : ℝ)⁻¹ ^ 60 := SecondOrder.AtMost.sum_const_bound hn (by positivity)
    _ ≤ 1 / 10000000000000000 := by norm_num


theorem small_tail_expansion_bounds_tight (D : Cuts.SpecData W) [LinearOrder D.cut.Half]
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (hp : 2 ^ 512 ≤ p) (hn : Fintype.card D.cut.Half ≤ 18)
    (hm : D.crossPairs.card ≤ 96)
    (hd : ∀ i, nbrCount D.halfGraph (univ.erase i) i ≤ 10)
    (hr : ∀ i, (D.Nset i).card ≤ 12)
    (hne : (injLabellings (ZMod p) D.G).Nonempty)
    (he : ∀ i, graphCountError (p := p) D.halfGraph i < 1) :
    let r := (Real.sqrt p)⁻¹
    let a := 2⁻¹ ^ 50 * r
    let L := graphPinned hW D.halfGraph (D.half_nonempty hne) he
    (∀ v, ‖Cx.nsOp D hne v‖ ≤ a * ‖v‖) ∧
    (∀ v, ‖Cx.collOp D hne v‖ ≤ a * ‖v‖) ∧
    2 * Spectral.starZstar L D.Nset (Spectral.starCoef (p := p) D) + a + a ≤ 1 / 100 ∧
    (a + a) / (1 - 1 / 100) +
      ((Spectral.starMstar L D.Nset (Spectral.starCoef (p := p) D) + a + a) /
        (1 - 1 / 100)) ^ 2 ≤ 1 / 1000 * r := by
  have hn36 : Fintype.card D.cut.Half ≤ 36 := by omega
  have hd' : ∀ i, (graphNbrs D.halfGraph i).card ≤ 10 := fun i => by
    rw [← nbrCount_erase_self]
    exact hd i
  have he' : ∀ i, graphCountError (p := p) D.halfGraph i ≤ 1 / 2 := fun i =>
    (graphCountError_bound D.halfGraph hn36 hd' (by omega) i).trans (by norm_num)
  dsimp only
  refine ⟨small_nsOp_tail D hW h4 hp hn hm hne, ?_, ?_, ?_⟩
  · intro v
    have h := collOp_uniform D hW (by omega) hne hn36
      (fun i => by rw [rowsDeg0_eq_full_nbrCount]; exact hd i) hr v
    apply h.trans (mul_le_mul_of_nonneg_right _ (norm_nonneg _))
    exact (collision_tail_scalar hp).trans
      (mul_le_mul_of_nonneg_right (by norm_num) (by positivity))
  · apply tail_normalizer_scalar (by positivity) (tail_rp_le hp) _ le_rfl le_rfl
    simpa only [one_div] using SecondOrder.AtMost.starZstar_uniform
      (graphPinned hW D.halfGraph (D.half_nonempty hne) he) D.Nset
      (Spectral.starCoef (p := p) D) (Spectral.starCoef_abs_le D) hn36 hn36 hd' he'
  · apply tail_perpendicular_tight (by positivity) (tail_rp_le hp)
      (Real.sqrt_nonneg _) (by positivity) (by positivity) _ le_rfl le_rfl
    simpa only [Spectral.starMstar, one_div] using SecondOrder.AtMost.starMstar_uniform
      (graphPinned hW D.halfGraph (D.half_nonempty hne) he) D.Nset
      (Spectral.starCoef (p := p) D) (Spectral.starCoef_abs_le D) hn36 hn36 hd' he'


end Sarkozy.SpectralD.AtMost

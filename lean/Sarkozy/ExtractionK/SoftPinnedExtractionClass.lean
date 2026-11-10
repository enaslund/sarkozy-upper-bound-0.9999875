module

public import Sarkozy.ExtractionK.SoftPinnedExtractionGeneral

@[expose] public section

/-!
# Soft pinned classes, the general class bound (`cor:soft-kernels`(c), `prop:pinned-extraction`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(c) for the general class bound of
`prop:pinned-extraction` (`pe_class_sum_le`, any witness size `k`, with the product `peFactor` of
the pinned vertex factors `F^pin_v`):

* `spe_peNum_mono`, `spe_peF_mono`, `spe_peFactor_mono`, `spe_class_bound_mono`: the bound of
  `pe_class_sum_le` is nondecreasing in the free set (`F^pin_v` is nondecreasing in `h_v`);
* `spe_soft_class_sum_le` (`χ(-1) = -1` at the free pairs with `D_e < 0`; no condition when
  `D ≥ 0` on the free pairs), `spe_soft_class_sum_le_g` (a non-square integer `ν`, signs nonzero in
  `F`), **`spe_soft_class_sum_le_zmod`** (`𝔽_p`, `p` odd, all `|D_e| ≤ 1`, no sign condition): the
  soft class kernel `skSoftKer` satisfies the bound of the Boolean class.

The proof is that of `SoftPinnedExtraction.lean` (`spe_soft_le_of_sub`, `spe_soft_le_of_subN`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SpeFactor

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem spe_peNum_mono {q : ℝ} (hq : 0 ≤ q) (n z ϖj : ℕ) {h h' : ℕ} (hh : h ≤ h') :
    peNum q n z ϖj h ≤ peNum q n z ϖj h' := by
  unfold peNum
  have he := coarseError_mono (q := q) (by positivity : (0 : ℝ) ≤ 2 * n + z)
    (Nat.add_le_add_left hh ϖj)
  have h2 : (2 : ℝ) ^ h ≤ 2 ^ h' := pow_le_pow_right₀ (by norm_num) hh
  have h0 : (0 : ℝ) ≤ q * (2 : ℝ)⁻¹ ^ ϖj := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : 1 + coarseError (ϖj + h) q (2 * n + z) ≤
    1 + coarseError (ϖj + h') q (2 * n + z)) h0
  have := mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg (α := ℝ) n)
  linarith

omit [Field F] [Fintype F] [DecidableEq F] in
theorem spe_peF_mono {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1) (ϖj : ℕ)
    {h h' : ℕ} (hh : h ≤ h') : peF q n z ϖ ϖj h ≤ peF q n z ϖ ϖj h' :=
  div_le_div_of_nonneg_right (spe_peNum_mono hq.le n z ϖj hh) (peLow_pos hq he ϖj).le

omit [Field F] [DecidableEq F] in
/-- The product of the pinned vertex factors is nondecreasing in the free set. -/
theorem spe_peFactor_mono {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1)
    (pin : Fin n → F → ℤ) {T Fr : Finset (Fin n × Fin n)} (hT : T ⊆ Fr)
    (V W Cx Cz : Finset (Fin n)) :
    peFactor q n z ϖ pin T V W Cx Cz ≤ peFactor q n z ϖ pin Fr V W Cx Cz := by
  unfold peFactor
  have hI : ∀ S : Finset (Fin n), ∏ u ∈ S, peF q n z ϖ (pinCount pin u) (intH T u).card ≤
      ∏ u ∈ S, peF q n z ϖ (pinCount pin u) (intH Fr u).card := fun S =>
    prod_le_prod₀ (fun u _ => peF_nonneg hq he _ _)
      (fun u _ => spe_peF_mono hq he _ (card_le_card (sk_intH_mono hT u)))
  have hC : ∀ S : Finset (Fin n), ∏ u ∈ S, peF q n z ϖ (pinCount pin u) (peColH T u).card ≤
      ∏ u ∈ S, peF q n z ϖ (pinCount pin u) (peColH Fr u).card := fun S =>
    prod_le_prod₀ (fun u _ => peF_nonneg hq he _ _)
      (fun u _ => spe_peF_mono hq he _ (card_le_card (spe_peColH_mono hT u)))
  have h0I : ∀ (S : Finset (Fin n)) (G : Finset (Fin n × Fin n)),
      0 ≤ ∏ u ∈ S, peF q n z ϖ (pinCount pin u) (intH G u).card := fun S G =>
    prod_nonneg fun u _ => peF_nonneg hq he _ _
  have h0C : ∀ (S : Finset (Fin n)) (G : Finset (Fin n × Fin n)),
      0 ≤ ∏ u ∈ S, peF q n z ϖ (pinCount pin u) (peColH G u).card := fun S G =>
    prod_nonneg fun u _ => peF_nonneg hq he _ _
  refine mul_le_mul (mul_le_mul (mul_le_mul (hI _) (hC _) (h0C _ _) (h0I _ _)) (hC _)
    (h0C _ _) (mul_nonneg (h0I _ _) (h0C _ _))) (hI _) (h0I _ _)
    (mul_nonneg (mul_nonneg (h0I _ _) (h0C _ _)) (h0C _ _))

omit [Field F] [DecidableEq F] in
/-- The bound of `pe_class_sum_le` is nondecreasing in the free set. -/
theorem spe_class_bound_mono {q : ℝ} (hq : 0 < q) {n z ϖ : ℕ} (he : ePin q n z ϖ < 1)
    (pin : Fin n → F → ℤ) {T Fr : Finset (Fin n × Fin n)} (hT : T ⊆ Fr)
    (V W Cx Cz : Finset (Fin n)) :
    Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card +
        ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) * peFactor q n z ϖ pin T V W Cx Cz) ≤
      Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
        ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor q n z ϖ pin Fr V W Cx Cz) := by
  have h0 : 0 ≤ peFactor q n z ϖ pin T V W Cx Cz := by
    unfold peFactor
    refine mul_nonneg (mul_nonneg (mul_nonneg ?_ ?_) ?_) ?_ <;>
      exact prod_nonneg fun u _ => peF_nonneg hq he _ _
  refine Real.sqrt_le_sqrt (mul_le_mul ?_ (spe_peFactor_mono hq he pin hT V W Cx Cz) h0
    (by positivity))
  refine pow_le_pow_right₀ (by norm_num) ?_
  have := spe_ex_mono hT V W
  omega

end SpeFactor

section SpeClassSoft

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`cor:soft-kernels`(c), the general pinned class bound** (`pe_class_sum_le`, any witness size
`k`): the soft class kernel `skSoftKer` (`|D_e| ≤ 1`) of a pinned row satisfies the bound
`c_ker r^k (2^{f_V + f_W + ϖ_V + ϖ_W} ∏_v F^pin_v)^{1/2} (1 - e^pin_ϖ)^{-k} ‖f‖ ‖h‖` of the
Boolean class, provided `χ(-1) = -1` at the free pairs with a negative coefficient. -/
theorem spe_soft_class_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hPFr : Disjoint P Fr)
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : Fin n × Fin n → ℝ) (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1)
    (hneg : ∀ e ∈ Fr, D e < 0 → quadraticChar F (-1) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * skSoftKer ς D P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  refine spe_soft_le_of_sub (pinLab M pin) ς D P Fr hPFr hneg hDP hDF f h ?_
  intro T hT
  rw [mem_powerset] at hT
  have hker' : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W)
      (rectKer (skFlip ς D Fr) P V W) (cker * Real.sqrt (Fintype.card F) ^ k) := by
    rw [sk_rectKer_flip ς D P Fr hPFr V W]
    exact hker
  have hb := pe_class_sum_le hW M pin hpin hpinM ϖ hϖ he (skFlip ς D Fr)
    (skFlip_values ς hς D Fr) P T
    (fun e he' => (skFlip_ne_zero_iff ς D Fr e.1 e.2).mpr (hFrς e (hT he'))) V W Cx Cz hVk hWk
    hVC hWC hP (fun e he' => hFr e (hT he')) hcker hker' f h
  refine hb.trans ?_
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hm := spe_class_bound_mono hq0 he pin hT V W Cx Cz
  have h1e : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
  have h1 : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
  have h2 : 0 ≤ Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
      Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by positivity
  have h3 : 0 < (1 - ePin (Fintype.card F) n M.card ϖ) ^ k := pow_pos h1e k
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin T V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)
      = (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin T V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by ring
    _ ≤ (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by
      gcongr
    _ = _ := by ring

/-- **`cor:soft-kernels`(c), the general pinned class bound, any nonzero signs**: as
`spe_soft_class_sum_le` with a non-square integer `ν` in place of the condition `χ(-1) = -1`. -/
theorem spe_soft_class_sum_le_g (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j ≠ 0 → ((ς i j : ℤ) : F) ≠ 0) (P Fr : Finset (Fin n × Fin n))
    (hPFr : Disjoint P Fr)
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W) (rectKer ς P V W)
      (cker * Real.sqrt (Fintype.card F) ^ k))
    (D : Fin n × Fin n → ℝ) (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1)
    {ν : ℤ} (hν : quadraticChar F (ν : F) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * skSoftKer ς D P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  refine spe_soft_le_of_subN (pinLab M pin) ς D P Fr hPFr hν hDP hDF f h ?_
  intro T hT
  rw [mem_powerset] at hT
  have hker' : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W)
      (rectKer (skFlipN ς D Fr ν) P V W) (cker * Real.sqrt (Fintype.card F) ^ k) := by
    rw [sk_rectKer_flipN ς D P Fr hPFr ν V W]
    exact hker
  have hb := speg_class_sum_le hW M pin hpin hpinM ϖ hϖ he (skFlipN ς D Fr ν)
    (skFlipN_castF ς hς D Fr hν) P T
    (fun e he' => (skFlipN_ne_zero_iff ς D Fr hν e.1 e.2).mpr (hFrς e (hT he'))) V W Cx Cz hVk
    hWk hVC hWC hP (fun e he' => hFr e (hT he')) hcker hker' f h
  refine hb.trans ?_
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hm := spe_class_bound_mono hq0 he pin hT V W Cx Cz
  have h1e : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
  have h1 : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
  have h2 : 0 ≤ Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
      Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by positivity
  have h3 : 0 < (1 - ePin (Fintype.card F) n M.card ϖ) ^ k := pow_pos h1e k
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin T V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)
      = (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin T V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by ring
    _ ≤ (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card F) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card F) n M.card ϖ) ^ k *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by
      gcongr
    _ = _ := by ring

end SpeClassSoft

section SpeClassZMod

variable {p : ℕ} [Fact p.Prime]

/-- **`cor:soft-kernels`(c), the general pinned class bound over `𝔽_p`, no sign condition.** -/
theorem spe_soft_class_sum_le_zmod (hp2 : p ≠ 2) (hW : WeilBound (ZMod p)) {n : ℕ}
    (M : Finset (ZMod p)) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card (ZMod p)) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (P Fr : Finset (Fin n × Fin n))
    (hPFr : Disjoint P Fr)
    (hFrς : ∀ e ∈ Fr, ς e.1 e.2 ≠ 0) {k : ℕ} (V W Cx Cz : Finset (Fin n)) (hVk : V.card = k)
    (hWk : W.card = k) (hVC : ∀ u ∈ V, u ∉ Cx) (hWC : ∀ u ∈ W, u ∉ Cz)
    (hP : ∀ e ∈ P, (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ Cx ∨ e.2 ∈ Cz)
    (hFr : ∀ e ∈ Fr, e.1 ∈ Cx ∨ e.2 ∈ Cz) {cker : ℝ} (hcker : 0 ≤ cker)
    (hker : Sarkozy.Influence.OpBound (injTuples (ZMod p) V) (injTuples (ZMod p) W)
      (rectKer ς P V W) (cker * Real.sqrt (Fintype.card (ZMod p)) ^ k))
    (D : Fin n × Fin n → ℝ) (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1)
    (f h : (Fin n → ZMod p) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ x' ∈ pinLab M pin, f x * skSoftKer ς D P Fr x x' * h x') /
        ((pinLab M pin).card : ℝ) ^ 2| ≤
      cker * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ^ k *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card +
            ∑ v ∈ V, pinCount pin v + ∑ v ∈ W, pinCount pin v) *
          peFactor (Fintype.card (ZMod p)) n M.card ϖ pin Fr V W Cx Cz) /
        (1 - ePin (Fintype.card (ZMod p)) n M.card ϖ) ^ k *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨ν, hν⟩ := sk_exists_nonsquare_int (p := p) hp2
  exact spe_soft_class_sum_le_g hW M pin hpin hpinM ϖ hϖ he ς (spe_castF_of_pm hς) P Fr hPFr
    hFrς V W Cx Cz hVk hWk hVC hWC hP hFr hcker hker D hDP hDF hν f h

end SpeClassZMod

end Sarkozy.ExtractionK

module

public import Sarkozy.ExtractionK.PinnedExtraction
public import Sarkozy.ExtractionK.SoftCore

@[expose] public section

/-!
# Soft cross factors in pinned compressed classes (`cor:soft-kernels`(c), `prop:pinned-extraction`)

`paper/sections/16_extraction.tex`, `cor:soft-kernels`(c): "the bounds of
`prop:pinned-extraction` … hold when the cross factors are `1 + D_{ij} χ_{ij}` with `|D_{ij}| ≤ 1`".

* `spe_soft_extraction_sum_le`: the soft class kernel `∑_{S ∈ 𝒞} D_S χ_S` (`skSoftKer`) of a
  pinned row satisfies the bound `eq:push:pinnedclass` of the Boolean class
  (`pinned_extraction_sum_le`, any witness size `k`);
* `spe_soft_pinned_extraction`: the same for a class `𝒞(P, A)` with a witness and a cover
  (`pinned_extraction`);
* `spe_soft_pinned_extraction_buckets`: the soft nonstar part `∑_{S nonstar} D_S T_S` satisfies
  the bucket bound `N^pin` (`pinned_extraction_buckets`).

Each holds when `χ(-1) = -1` at the (free) pairs with a negative coefficient (`hneg`): for every
`D` when `p ≡ 3 (mod 4)`, and for every field when `D ≥ 0` on the free pairs.

## Proof

As in `SoftCore.lean` (`sk_softKer_expand`): `1 + D_e χ_e = (1 - |D_e|) + |D_e| (1 + χ'_e)` with
the sign of a free pair flipped when `D_e < 0` (`skFlip`; `χ'_e = -χ_e` needs `χ(-1) = -1`), so the
soft kernel is `∏_{e ∈ P} D_e` times a convex combination (`skW`) of the Boolean kernels of the
sub-classes `𝒞(P, A ∪ (F \ T))` with the flipped signs (`spe_soft_sum_eq`, `spe_soft_le_of_sub`).
The pinned bound of a sub-class needs no symmetry of the signs (Step 8 uses `pinSwap`), depends on
the signs only through their support (`spe_pinNX_flip`, `spe_pinNY_flip`; `sk_rectKer_flip` for
the kernel), and is nondecreasing in the free set (`spe_ex_mono` for `ex^pin = f_V + f_W`,
`spe_peOc_mono` for `oc^pin`).

## Not covered here

`χ(-1) = 1` (`p ≡ 1 (mod 4)`) with a negative coefficient on a free pair: the flip then needs a
non-square integer sign `ν ∉ {±1}`; `SoftPinnedExtractionGeneral.lean` restates the pinned chain
for signs merely nonzero in `F` and proves the bounds over `𝔽_p` for every odd `p` with no sign
condition. The soft analogue of the general class bound `pe_class_sum_le` (with `peFactor`) is not
stated.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section SpeMono

theorem spe_peColH_mono {n : ℕ} {Fr Fr' : Finset (Fin n × Fin n)} (h : Fr ⊆ Fr') (b : Fin n) :
    peColH Fr b ⊆ peColH Fr' b := by
  intro a ha
  simp only [peColH, mem_filter, mem_univ, true_and] at ha ⊢
  exact h ha

/-- `oc^pin(𝒞)` is nondecreasing in the free set. -/
theorem spe_peOc_mono {n : ℕ} {T Fr : Finset (Fin n × Fin n)} (hT : T ⊆ Fr)
    (V W Cx Cz : Finset (Fin n)) : peOc T V W Cx Cz ≤ peOc Fr V W Cx Cz := by
  unfold peOc
  have h1 : ∀ S : Finset (Fin n), ∑ u ∈ S, (2 : ℝ) ^ (intH T u).card ≤
      ∑ u ∈ S, (2 : ℝ) ^ (intH Fr u).card := fun S =>
    sum_le_sum fun u _ => pow_le_pow_right₀ (by norm_num) (card_le_card (sk_intH_mono hT u))
  have h2 : ∀ S : Finset (Fin n), ∑ u ∈ S, (2 : ℝ) ^ (peColH T u).card ≤
      ∑ u ∈ S, (2 : ℝ) ^ (peColH Fr u).card := fun S =>
    sum_le_sum fun u _ => pow_le_pow_right₀ (by norm_num) (card_le_card (spe_peColH_mono hT u))
  have := h1 (univ \ (V ∪ Cx))
  have := h2 Cz
  have := h2 (univ \ (W ∪ Cz))
  have := h1 Cx
  linarith

/-- `ex^pin(𝒞) = f_V + f_W` is nondecreasing in the free set. -/
theorem spe_ex_mono {n : ℕ} {T Fr : Finset (Fin n × Fin n)} (hT : T ⊆ Fr) (V W : Finset (Fin n)) :
    (T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card ≤
      (Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card :=
  Nat.add_le_add (card_le_card (filter_subset_filter _ hT)) (card_le_card (filter_subset_filter _ hT))

theorem spe_pinNX_flip {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (Fr : Finset (Fin n × Fin n)) (i : Fin n) : pinNX (skFlip ς D Fr) i = pinNX ς i := by
  unfold pinNX
  exact filter_congr fun j _ => skFlip_ne_zero_iff ς D Fr i j

theorem spe_pinNY_flip {n : ℕ} (ς : Fin n → Fin n → ℤ) (D : Fin n × Fin n → ℝ)
    (Fr : Finset (Fin n × Fin n)) (j : Fin n) : pinNY (skFlip ς D Fr) j = pinNY ς j := by
  unfold pinNY
  exact filter_congr fun i _ => skFlip_ne_zero_iff ς D Fr i j

end SpeMono

section SpeSoft

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The bilinear sum of the soft kernel over any finite set of labellings is the weighted sum of
the Boolean sub-class sums (`sk_softKer_expand`). -/
theorem spe_soft_sum_eq {n : ℕ} (I : Finset (Fin n → F)) (ς : Fin n → Fin n → ℤ)
    (D : Fin n × Fin n → ℝ) (P Fr : Finset (Fin n × Fin n)) (hPFr : Disjoint P Fr)
    (hneg : ∀ e ∈ Fr, D e < 0 → quadraticChar F (-1) = -1) (f h : (Fin n → F) → ℝ) :
    ∑ x ∈ I, ∑ x' ∈ I, f x * skSoftKer ς D P Fr x x' * h x' =
      (∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
        ∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlip ς D Fr) P T x x' * h x' := by
  simp only [sk_softKer_expand ς D P Fr hPFr hneg]
  calc ∑ x ∈ I, ∑ x' ∈ I,
        f x * ((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset,
          skW D Fr T * classKer (skFlip ς D Fr) P T x x') * h x'
      = ∑ x ∈ I, ∑ x' ∈ I, ∑ T ∈ Fr.powerset,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlip ς D Fr) P T x x' * h x')) := by
        refine sum_congr rfl fun x _ => sum_congr rfl fun x' _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        exact sum_congr rfl fun T _ => by ring
    _ = ∑ x ∈ I, ∑ T ∈ Fr.powerset, ∑ x' ∈ I,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlip ς D Fr) P T x x' * h x')) :=
        sum_congr rfl fun x _ => sum_comm
    _ = ∑ T ∈ Fr.powerset, ∑ x ∈ I, ∑ x' ∈ I,
          (∏ e ∈ P, D e) * (skW D Fr T *
            (f x * classKer (skFlip ς D Fr) P T x x' * h x')) := sum_comm
    _ = _ := by
        rw [mul_sum]
        refine sum_congr rfl fun T _ => ?_
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun x _ => ?_
        rw [mul_sum, mul_sum]

/-- The convexity step: if every sub-class form is bounded by `B ≥ 0`, so is the soft form. -/
theorem spe_soft_le_of_sub {n : ℕ} (I : Finset (Fin n → F)) (ς : Fin n → Fin n → ℤ)
    (D : Fin n × Fin n → ℝ) (P Fr : Finset (Fin n × Fin n)) (hPFr : Disjoint P Fr)
    (hneg : ∀ e ∈ Fr, D e < 0 → quadraticChar F (-1) = -1)
    (hDP : ∀ e ∈ P, |D e| ≤ 1) (hDF : ∀ e ∈ Fr, |D e| ≤ 1) (f h : (Fin n → F) → ℝ) {B : ℝ}
    (hB : ∀ T ∈ Fr.powerset,
      |(∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlip ς D Fr) P T x x' * h x') /
        (I.card : ℝ) ^ 2| ≤ B) :
    |(∑ x ∈ I, ∑ x' ∈ I, f x * skSoftKer ς D P Fr x x' * h x') / (I.card : ℝ) ^ 2| ≤ B := by
  rw [spe_soft_sum_eq I ς D P Fr hPFr hneg f h]
  have hc : |∏ e ∈ P, D e| ≤ 1 := by
    rw [abs_prod]
    exact prod_le_one₀ (fun e _ => abs_nonneg _) (fun e he => hDP e he)
  have hw0 : ∀ T ∈ Fr.powerset, 0 ≤ skW D Fr T := fun T _ => skW_nonneg hDF T
  calc |((∏ e ∈ P, D e) * ∑ T ∈ Fr.powerset, skW D Fr T *
          (∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlip ς D Fr) P T x x' * h x')) /
            (I.card : ℝ) ^ 2|
      = |∏ e ∈ P, D e| * |∑ T ∈ Fr.powerset, skW D Fr T *
          ((∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlip ς D Fr) P T x x' * h x') /
            (I.card : ℝ) ^ 2)| := by
        rw [mul_div_assoc, abs_mul, sum_div]
        congr 2
        exact sum_congr rfl fun T _ => by ring
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T *
          |(∑ x ∈ I, ∑ x' ∈ I, f x * classKer (skFlip ς D Fr) P T x x' * h x') /
            (I.card : ℝ) ^ 2| := by
        refine mul_le_mul hc ?_ (abs_nonneg _) zero_le_one
        refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
        exact sum_congr rfl fun T hT => by rw [abs_mul, abs_of_nonneg (hw0 T hT)]
    _ ≤ 1 * ∑ T ∈ Fr.powerset, skW D Fr T * B := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun T hT' => ?_) zero_le_one
        exact mul_le_mul_of_nonneg_left (hB T hT') (hw0 T hT')
    _ = B := by rw [← sum_mul, skW_sum, one_mul, one_mul]

end SpeSoft

section SpeMain

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem spe_peGamma_nonneg (q : ℝ) (n z Δ : ℕ) : 0 ≤ peGamma q n z Δ := by
  unfold peGamma
  positivity

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction`, sum form**: the soft class kernel
`K^D_𝒞 = ∑_{S ∈ 𝒞} D_S χ_S` (`skSoftKer`, `|D_e| ≤ 1`) of a pinned row satisfies the bound
`eq:push:pinnedclass` of the Boolean class (`pinned_extraction_sum_le`), provided `χ(-1) = -1`
at the free pairs with a negative coefficient (`hneg`; no condition when `D ≥ 0` on the free
pairs). -/
theorem spe_soft_extraction_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) {Δ : ℕ}
    (hΔX : ∀ i, ϖ + (pinNX ς i).card ≤ Δ) (hΔY : ∀ i, ϖ + (pinNY ς i).card ≤ Δ)
    (P Fr : Finset (Fin n × Fin n)) (hPFr : Disjoint P Fr)
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
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card + (Fr.filter (fun e => e.2 ∈ W)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by
  refine spe_soft_le_of_sub (pinLab M pin) ς D P Fr hPFr hneg hDP hDF f h ?_
  intro T hT
  rw [mem_powerset] at hT
  have hker' : Sarkozy.Influence.OpBound (injTuples F V) (injTuples F W)
      (rectKer (skFlip ς D Fr) P V W) (cker * Real.sqrt (Fintype.card F) ^ k) := by
    rw [sk_rectKer_flip ς D P Fr hPFr V W]
    exact hker
  have hb := pinned_extraction_sum_le hW M pin hpin hpinM ϖ hϖ he (skFlip ς D Fr)
    (skFlip_values ς hς D Fr) (fun i => by rw [spe_pinNX_flip]; exact hΔX i)
    (fun i => by rw [spe_pinNY_flip]; exact hΔY i) P T
    (fun e he => (skFlip_ne_zero_iff ς D Fr e.1 e.2).mpr (hFrς e (hT he))) V W Cx Cz hVk hWk
    hVC hWC hP (fun e he => hFr e (hT he)) hcker hker' f h
  refine hb.trans ?_
  have hL0 : 0 ≤ peLambda0 (Fintype.card F) n M.card ϖ Δ := by
    unfold peLambda0 peRpin
    have he0 := ePin_nonneg (Fintype.card F : ℝ) n M.card ϖ
    have h1 : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
    exact div_nonneg (mul_nonneg (pow_nonneg (pow_nonneg (div_nonneg (by linarith) h1.le) _) _)
      (Real.exp_pos _).le) (pow_pos h1 _).le
  have hγ := spe_peGamma_nonneg (Fintype.card F : ℝ) n M.card Δ
  have hex : Real.sqrt ((2 : ℝ) ^ ((T.filter (fun e => e.1 ∈ V)).card +
      (T.filter (fun e => e.2 ∈ W)).card)) ≤
      Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card +
        (Fr.filter (fun e => e.2 ∈ W)).card)) :=
    Real.sqrt_le_sqrt (pow_le_pow_right₀ (by norm_num) (spe_ex_mono hT V W))
  have hoc : Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc T V W Cx Cz) ≤
      Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (spe_peOc_mono hT V W Cx Cz) (by positivity))
  have h1 : 0 ≤ cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k := by positivity
  have h2 : 0 ≤ Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
      Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card) := by positivity
  have h3 : (0 : ℝ) ≤ 2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ := by positivity
  calc cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card)) *
        2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc T V W Cx Cz) *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)
      = (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((T.filter (fun e => e.1 ∈ V)).card + (T.filter (fun e => e.2 ∈ W)).card)) *
        (2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ) *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc T V W Cx Cz) *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by ring
    _ ≤ (cker * (Real.sqrt (Fintype.card F))⁻¹ ^ k) *
        Real.sqrt (2 ^ ((Fr.filter (fun e => e.1 ∈ V)).card +
          (Fr.filter (fun e => e.2 ∈ W)).card)) *
        (2 ^ (k * ϖ) * peLambda0 (Fintype.card F) n M.card ϖ Δ) *
        Real.exp (peGamma (Fintype.card F) n M.card Δ * 2 ^ ϖ * peOc Fr V W Cx Cz) *
        (Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, h x ^ 2) / (pinLab M pin).card)) := by
      gcongr
    _ = _ := by ring

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction`, `eq:push:pinnedclass`**: for a class
`𝒞(P, A)` of `Ex ⊆ E_×` with a witness and a cover, and coefficients `|D_e| ≤ 1` on `Ex`, the soft
class sum `∑_{S ∈ 𝒞} D_S ⟨f, T_S h⟩_μ` (pinned law `μ`) satisfies the bound of
`pinned_extraction`, provided `χ(-1) = -1` at the free pairs with a negative coefficient
(`hneg`; e.g. `p ≡ 3 (mod 4)`, or `D ≥ 0` on the free pairs). -/
theorem spe_soft_pinned_extraction (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
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
    (D : Fin n × Fin n → ℝ) (hD : ∀ e ∈ Ex, |D e| ≤ 1)
    (hneg : ∀ e ∈ Ex \ (P ∪ A), D e < 0 → quadraticChar F (-1) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) /
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
  have hK : ∀ x y : Fin n → F, ∑ S ∈ cls Ex P A, ∏ e ∈ S, (D e * chiPair ς e x y) =
      skSoftKer ς D P (Ex \ (P ∪ A)) x y := fun x y =>
    sk_sum_cls_eq Ex P A hP hPA (fun e => D e * chiPair ς e x y)
  simp only [hK]
  set Fr := Ex \ (P ∪ A) with hFr
  have hPFr : Disjoint P Fr := by
    rw [disjoint_left]
    intro e heP heF
    exact (mem_sdiff.mp heF).2 (mem_union_left _ heP)
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
  exact spe_soft_extraction_sum_le hW M pin hpin hpinM ϖ hϖ he ς hς hΔX hΔY P Fr hPFr
    (fun e he => hEx e (hFrEx e he)) (witV w) (witW w) Cx Cz hVk hWk hVC hWC hP' hFr' hcker
    hker D (fun e he => hD e (hP he)) (fun e he => hD e (hFrEx e he)) hneg f h

/-- **`cor:soft-kernels`(c) for `prop:pinned-extraction`, the bucket sum `N^pin`**: for an exact
partition of the nonstar subsets of `Ex` and coefficients `|D_e| ≤ 1` on `Ex`, the soft nonstar
part `∑_{S nonstar} D_S T_S` of a pinned row satisfies the bound of `pinned_extraction_buckets`,
provided `χ(-1) = -1` at the pairs with a negative coefficient (`hneg`). -/
theorem spe_soft_pinned_extraction_buckets (hW : WeilBound F) {n : ℕ} (M : Finset F)
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
    (D : Fin n × Fin n → ℝ) (hD : ∀ e ∈ Ex, |D e| ≤ 1)
    (hneg : ∀ e ∈ Ex, D e < 0 → quadraticChar F (-1) = -1)
    (f h : (Fin n → F) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) /
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
  have hsplit : ∀ x y : Fin n → F, (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) =
      ∑ c ∈ 𝔓, ∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y) := by
    intro x y
    rw [← hunion, sum_biUnion hdisj]
  have hform : (∑ x ∈ I, ∑ y ∈ I,
      f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2 =
      ∑ c ∈ 𝔓, (∑ x ∈ I, ∑ y ∈ I,
        f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2 := by
    rw [← sum_div]
    congr 1
    have hT : ∀ x y : Fin n → F,
        f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y =
        ∑ c ∈ 𝔓, f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y := by
      intro x y
      rw [hsplit, mul_sum, sum_mul]
    calc ∑ x ∈ I, ∑ y ∈ I, f x * (∑ S ∈ nonstars Ex, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y
        = ∑ x ∈ I, ∑ y ∈ I, ∑ c ∈ 𝔓,
            f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y :=
          sum_congr rfl fun x _ => sum_congr rfl fun y _ => hT x y
      _ = ∑ x ∈ I, ∑ c ∈ 𝔓, ∑ y ∈ I,
            f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y :=
          sum_congr rfl fun x _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [hform]
  have hγ : 0 ≤ γ := spe_peGamma_nonneg _ _ _ _
  have hL : 0 ≤ L := by
    have h1e : 0 < 1 - ePin (Fintype.card F) n M.card ϖ := by linarith
    simp only [L, peLambda0, peRpin]
    have : 0 ≤ (1 + ePin (Fintype.card F) n M.card ϖ) /
        (1 - ePin (Fintype.card F) n M.card ϖ) :=
      div_nonneg (by linarith [ePin_nonneg (Fintype.card F : ℝ) n M.card ϖ]) h1e.le
    positivity
  have hclass : ∀ c ∈ 𝔓, |(∑ x ∈ I, ∑ y ∈ I,
      f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2| ≤
      r ^ 2 * L * 2 ^ (2 * ϖ) * (ck c * exc c * Real.exp (γ * 2 ^ ϖ * (bucket c * 2 ^ 𝔮))) *
        Nf * Nh := by
    intro c hc
    have hb := spe_soft_pinned_extraction hW M pin hpin hpinM ϖ hϖ he ς hς hΔX hΔY Ex c.1 c.2
      hEx (hdat c hc) (wit c) (hwit c hc) (cx c) (cz c) (hcov c hc) (hck c hc) (hker c hc) D hD
      (fun e he' => hneg e (mem_sdiff.mp he').1) f h
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
        f x * (∑ S ∈ cls Ex c.1 c.2, ∏ e ∈ S, (D e * chiPair ς e x y)) * h y) / N ^ 2|
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

end SpeMain

end Sarkozy.ExtractionK

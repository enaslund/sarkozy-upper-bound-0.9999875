module

public import Sarkozy.NormBoundsPaper3.MatchBlock

@[expose] public section

/-!
# The field `Ea` at the paper's constant (`lem:record:exact-marginal-e`(ii); NB3)

`paper/sections/21_middle_records.tex`, `lem:record:exact-marginal-e`(ii): "Let `𝔅` be a block of a
piece starting at `X ≥ 2^20`, with least prime `b` …
`a_E(X) = a^E/r = (1 + 2q_X)/((1 − q_X)(1 − 2q_X))`
… Then the block differences … have … skew part of norm at most `a_E(X) b^{-1/2}`"; "For
`p ∈ 𝔅`, `q_p ≤ q_X` and `r_p ≤ b^{-1/2} ≤ X^{-1/2}`, so by (i) … `a^E_p ≤ a_E(X) r_p`"; "On a
sector `S` with `|S| ≥ 3` … the skew part is that of the new tensor (`lem:sector`(b)), of norm at
most `(κ_E(X) b^{-1/2})³ < r_E(X) b^{-3/2}` … `< b^{-1/2} ≤ a_E(X) b^{-1/2}`."

* **`match_skew`**: the skew field of the matching records `E_s`, for any `e ≥ aEp p` at every
  prime and `ρ ≥ rhoE p`, `ρ ≤ 1`, `ρ² ≤ e` (`change_le` with `(½, −½, 0)`; the singleton sectors
  by `P3_skew`, the larger sectors by `P3_centred`);
* numbers: `fX` (`X(X + 2)/(X² − 3X + 4)`), **`f_mono`**, `one_le_fX`, `aEp_le`, `rhoE_le`,
  **`fX_le_paper`** (`fX X ≤ (1 + 2q_X)/((1 − q_X)(1 − 2q_X))`, the paper's `a_E(X)`);
* **`match_skew_paper`**: the field `Ea` of `NormBoundsRest2` at `a_E · b^{-1/2}`, for a piece start
  `16 ≤ X ≤ b`, `2^8 ≤ b ≤ p` and `fX X ≤ a_E`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper2 (ip chg chg1 change_le centredNorm_mono)

/-! ## Numbers -/

/-- `f(X) = X(X + 2)/(X² − 3X + 4)`. -/
noncomputable def fX (X : ℝ) : ℝ := X * (X + 2) / (X ^ 2 - 3 * X + 4)

theorem fX_den_pos (X : ℝ) : 0 < X ^ 2 - 3 * X + 4 := by nlinarith [sq_nonneg (X - 3 / 2)]

/-- **`f` decreases** on `[4, ∞)`. -/
theorem f_mono {X q : ℝ} (hX : 4 ≤ X) (hXq : X ≤ q) : fX q ≤ fX X := by
  unfold fX
  rw [div_le_div_iff₀ (fX_den_pos q) (fX_den_pos X)]
  have key : X * (X + 2) * (q ^ 2 - 3 * q + 4) - q * (q + 2) * (X ^ 2 - 3 * X + 4) =
      (q - X) * (5 * X * q - 4 * q - 4 * X - 8) := by ring
  have h1 : 0 ≤ q - X := by linarith
  have h2 : 0 ≤ 5 * X * q - 4 * q - 4 * X - 8 := by nlinarith
  nlinarith [mul_nonneg h1 h2]

theorem one_le_fX {X : ℝ} (hX : 1 ≤ X) : 1 ≤ fX X := by
  unfold fX
  rw [le_div_iff₀ (fX_den_pos X)]
  nlinarith

/-- `fX X` is below the paper's `a_E(X) = (1 + 2q)/((1 − q)(1 − 2q))`, `q = 1/X`. -/
theorem fX_le_paper {X : ℝ} (hX : 3 ≤ X) :
    fX X ≤ (1 + 2 * (1 / X)) / ((1 - 1 / X) * (1 - 2 * (1 / X))) := by
  have hX0 : 0 < X := by linarith
  have e : (1 + 2 * (1 / X)) / ((1 - 1 / X) * (1 - 2 * (1 / X))) =
      X * (X + 2) / ((X - 1) * (X - 2)) := by
    field_simp
  rw [e]
  unfold fX
  have h1 : 0 < (X - 1) * (X - 2) := by nlinarith
  exact div_le_div_of_nonneg_left (by positivity) h1 (by nlinarith)

/-- `aEp p ≤ fX X · b^{-1/2}` for `4 ≤ X ≤ b ≤ p`. -/
theorem aEp_le {p : ℕ} {X b' : ℝ} (hX : 4 ≤ X) (hXb : X ≤ b') (hbp : b' ≤ p) :
    aEp p ≤ fX X * (1 / Real.sqrt b') := by
  have hp : (4 : ℝ) ≤ p := by linarith
  have hb0 : 0 < b' := by linarith
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  have hsb : 0 < Real.sqrt b' := Real.sqrt_pos.mpr hb0
  have hss : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt (by linarith)
  have hD := fX_den_pos (p : ℝ)
  have e : aEp p = fX p * (1 / Real.sqrt p) := by
    unfold aEp fX
    rw [mul_one_div, div_div, div_eq_div_iff hD.ne' (mul_pos hD hsp).ne']
    have : Real.sqrt p * ((p : ℝ) + 2) * (((p : ℝ) ^ 2 - 3 * p + 4) * Real.sqrt p) =
        (Real.sqrt p * Real.sqrt p) * ((p : ℝ) + 2) * ((p : ℝ) ^ 2 - 3 * p + 4) := by ring
    rw [this, hss]
  rw [e]
  have h1 : fX p ≤ fX X := f_mono hX (hXb.trans hbp)
  have h2 : 1 / Real.sqrt p ≤ 1 / Real.sqrt b' :=
    one_div_le_one_div_of_le hsb (Real.sqrt_le_sqrt hbp)
  have h3 : 0 ≤ fX p := by unfold fX; exact div_nonneg (by positivity) (fX_den_pos _).le
  have h4 : 0 ≤ fX X := by unfold fX; exact div_nonneg (by positivity) (fX_den_pos _).le
  exact mul_le_mul h1 h2 (by positivity) h4

theorem rhoE_nonneg (p : ℕ) : 0 ≤ rhoE p := by
  unfold rhoE
  exact div_nonneg (by positivity) (fX_den_pos _).le

/-- `rhoE p ≤ 4 p^{-1/2}` for `p ≥ 16`. -/
theorem rhoE_le {p : ℕ} (hp : (16 : ℝ) ≤ p) : rhoE p ≤ 4 * (1 / Real.sqrt p) := by
  unfold rhoE
  set s := Real.sqrt p
  have hs : s * s = p := Real.mul_self_sqrt (by linarith)
  have hs4 : 4 ≤ s := by
    rw [show (4 : ℝ) = Real.sqrt 16 by rw [show (16 : ℝ) = 4 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hp
  have hs0 : 0 < s := by linarith
  rw [← hs, mul_one_div, div_le_div_iff₀ (by nlinarith) hs0]
  nlinarith [mul_pos hs0 hs0, mul_pos (mul_pos hs0 hs0) hs0, mul_nonneg (sub_nonneg.mpr hs4)
    (mul_pos (mul_pos hs0 hs0) hs0).le]

/-! ## The block bound -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **`lem:record:exact-marginal-e`(ii), skew part**: the skew part of the change of the matching
record `E_s` has norm at most `e`, for `e` above the prime skew constants `aEp p` and above `ρ²`,
`ρ ≤ 1` above the prime centred constants `rhoE p`. -/
theorem match_skew (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ) {e ρ : ℝ}
    (he : 0 ≤ e) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hρe : ρ ^ 2 ≤ e)
    (hρp : ∀ i, rhoE (pr i) ≤ ρ) (hap : ∀ i, aEp (pr i) ≤ e) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl s)))
      (foldChange pr h hne root W I hr b C t (.inr (.inl s)) .skew) e := by
  refine ⟨he, fun F G => ?_⟩
  change |_| ≤ e * Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (lawE pr hne) (midEmission (matching s))).weight) F) *
    Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (lawE pr hne) (midEmission (matching s))).weight) G)
  rw [form_match_skew pr h hne root W I hr b s C t F G, hsq_oldE pr hne s F, hsq_oldE pr hne s G]
  have hp7 : ∀ i, 7 ≤ pr i := h.ge7
  have hp3 : ∀ i, 3 ≤ pr i := fun i => by have := hp7 i; omega
  have hcp : IsCoupling (fun i => m3 (pr i)) (fun i => P3 (blockE_nonempty pr h i)) :=
    ⟨fun i a => P3_row _ (hp7 i) (h.mod4 i) a, fun i b => P3_col _ (hp7 i) (h.mod4 i) b⟩
  have hcent : ∀ i, CentredNorm (m3 (pr i)) (P3 (blockE_nonempty pr h i)) ρ := fun i =>
    centredNorm_mono (m3_nonneg (hp3 i)) (P3_centred _ (hp7 i) (h.mod4 i)) (rhoE_nonneg _)
      (hρp i)
  refine change_le (fun i => m3_nonneg (hp3 i)) (fun i => sum_m3 (hp3 i)) hcp hcp
    (fun i => P3_nonneg _) (fun i => P3_nonneg _) (by norm_num) hρ0 hρ1 hρ0 hρ1 hcent hcent he
    ?_ (fun i u v hu hv => ?_) (fun _ => ((0, 0), 0)) _ _
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_of_neg (by norm_num : (-1 / 2 : ℝ) < 0),
      abs_zero]
    nlinarith
  · refine (P3_skew _ (hp7 i) (h.mod4 i) u v hu hv).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (hap i) (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)

/-- **The field `Ea` at the paper's constant** (`lem:record:exact-marginal-e`(ii)): `a_E · b^{-1/2}`
for a piece start `16 ≤ X ≤ b`, `2^8 ≤ b` below every prime of the block, and
`X(X + 2)/(X² − 3X + 4) ≤ a_E` (implied by the paper's `a_E(X)`, `fX_le_paper`). -/
theorem match_skew_paper (C : FoldComponents pr hne) (t : ℝ) {b' aE X : ℝ} (hX : 16 ≤ X)
    (hXb : X ≤ b') (hb : 2 ^ 8 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (haE : fX X ≤ aE) (s : Fin 2) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inl s)))
      (foldChange pr h hne root W I hr b C t (.inr (.inl s)) .skew) (aE * (1 / Real.sqrt b')) := by
  have hb0 : 0 < b' := by linarith
  have hsb : 0 < Real.sqrt b' := Real.sqrt_pos.mpr hb0
  have hsb16 : 16 ≤ Real.sqrt b' := by
    rw [show (16 : ℝ) = Real.sqrt (2 ^ 8) by rw [show ((2 : ℝ) ^ 8) = 16 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt hb
  have hf1 : 1 ≤ fX X := one_le_fX (by linarith)
  have haE1 : 1 ≤ aE := hf1.trans haE
  have hinv : 0 < 1 / Real.sqrt b' := one_div_pos.mpr hsb
  have hinv16 : 16 * (1 / Real.sqrt b') ≤ 1 := by
    rw [mul_one_div, div_le_one hsb]; exact hsb16
  refine match_skew pr h hne root W I hr b s C t (ρ := 4 * (1 / Real.sqrt b'))
    (by positivity) (by positivity) (by linarith) ?_ (fun i => ?_) (fun i => ?_)
  · calc (4 * (1 / Real.sqrt b')) ^ 2 = (16 * (1 / Real.sqrt b')) * (1 / Real.sqrt b') := by ring
      _ ≤ 1 * (1 / Real.sqrt b') := mul_le_mul_of_nonneg_right hinv16 hinv.le
      _ ≤ aE * (1 / Real.sqrt b') := mul_le_mul_of_nonneg_right haE1 hinv.le
  · have hp : (16 : ℝ) ≤ pr i := by linarith [hbp i]
    refine (rhoE_le hp).trans (mul_le_mul_of_nonneg_left ?_ (by norm_num))
    exact one_div_le_one_div_of_le hsb (Real.sqrt_le_sqrt (hbp i))
  · refine (aEp_le (by linarith) hXb (hbp i)).trans ?_
    exact mul_le_mul_of_nonneg_right haE hinv.le

end Frame

end Sarkozy.NormBoundsPaper3

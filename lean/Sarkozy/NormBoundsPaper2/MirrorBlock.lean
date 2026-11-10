module

public import Sarkozy.NormBoundsPaper2.MirrorPrime
public import Sarkozy.NormBoundsPaper2.Merge2Sym

@[expose] public section

/-!
# The mirror-edge merge replacements on the block (`lem:merge-repair`, `Ms`, `Ma`)

`paper/sections/21_middle_records.tex`, `lem:merge-repair`: for a block with least prime `b`, the
mirror-edge replacement minus the source has symmetric norm `≤ s_b` and skew norm `≤ a_b`
relative to the product of the actual half laws.

The proof is the paper's, "Products over primes": "For `p ≥ 2^24` the displayed formulas imply
`α^G_p ≤ 2p^{-1/2}`, … `s^G_p ≥ 5/p`, `a^G_p ≥ 4/p` … All the bounds decrease with `p`. On singleton
supports use the prime bounds. On a support of size at least two, the mirror difference has
symmetric norm at most `α_b² + d_b² ≤ 5/b ≤ s_b`, and skew norm at most `α_b² ≤ 4/b ≤ a_b`, since
the source is self-adjoint."

* numbers: `aG_split`, `sG_mono`, `aG_mono` ("all the bounds decrease with `p`"), `aG_ge`,
  **`alpha_le`** (`α^G_p ≤ 2p^{-1/2}` for `p ≥ 2^24`; in fact for `√p ≥ 64`), `mirror_multi_sym`,
  `mirror_multi_skew`;
* `form_newMirror_cm`, **`form_mirror_sym`**, **`form_mirror_skew`**: the symmetric and skew parts
  of the mirror change are the forms `chg (⊗ P^c) (⊗ D) (½, ½, 1)` and `(½, −½, 0)`;
* **`mirror_sym_paper`**, **`mirror_skew_paper`**: the fields `Ms`, `Ma` of B8's `NormBounds`, for
  `2^24 ≤ b ≤ p` at every prime of the block (`change_le` with `ρ = 2 b^{-1/2}`, `d = d_b`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (oldM mh form_oldM_symm form_emit_gen newM_half newM_flip)
open Sarkozy.MiddleRecords (dG etaG sG aG)

/-! ## Numbers -/

/-- `D(q) = (1 − 2/q)(1 − 3/q)`. -/
noncomputable def Dq (q : ℝ) : ℝ := (1 - 2 / q) * (1 - 3 / q)

theorem Dq_pos {q : ℝ} (hq : 4 ≤ q) : 0 < Dq q := by
  unfold Dq
  have h1 : 2 / q < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 3 / q < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact mul_pos (by linarith) (by linarith)

theorem Dq_le_one {q : ℝ} (hq : 4 ≤ q) : Dq q ≤ 1 := by
  unfold Dq
  have h1 : 2 / q < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 3 / q < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h1' : 0 ≤ 2 / q := by positivity
  have h2' : 0 ≤ 3 / q := by positivity
  nlinarith

theorem Dq_mono {b q : ℝ} (hb : 4 ≤ b) (hbq : b ≤ q) : Dq b ≤ Dq q := by
  unfold Dq
  have e1 : 2 / q ≤ 2 / b := div_le_div_of_nonneg_left (by norm_num) (by linarith) hbq
  have e2 : 3 / q ≤ 3 / b := div_le_div_of_nonneg_left (by norm_num) (by linarith) hbq
  have h1 : 2 / b < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 3 / b < 1 := by rw [div_lt_one (by linarith)]; linarith
  exact mul_le_mul (by linarith) (by linarith) (by linarith) (by linarith)

/-- `a^G_q = q^{-1/2}/D(q) + 2 q^{-1}(4 − 6/q)/D(q)`. -/
theorem aG_split {q : ℝ} (hq : 4 ≤ q) :
    aG q = (1 / Real.sqrt q) / Dq q + (2 * (1 / q) * (4 - 6 / q)) / Dq q := by
  have hs : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt (by linarith)
  have hs0 : Real.sqrt q ≠ 0 := (Real.sqrt_pos.mpr (by linarith)).ne'
  unfold aG
  rw [← add_div]
  congr 1
  field_simp
  linear_combination (-(2 * (4 * q - 6))) * hs

/-- "All the bounds decrease with `p`": `s^G`. -/
theorem sG_mono {b q : ℝ} (hb : 7 ≤ b) (hbq : b ≤ q) : sG q ≤ sG b := by
  unfold sG
  rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
  have h1 : 0 ≤ q - b := by linarith
  have h2 : 0 ≤ 5 * b * q - 6 * q - 6 * b := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- "All the bounds decrease with `p`": `a^G`. -/
theorem aG_mono {b q : ℝ} (hb : 7 ≤ b) (hbq : b ≤ q) : aG q ≤ aG b := by
  rw [aG_split (by linarith), aG_split (by linarith)]
  have hDb := Dq_pos (show (4 : ℝ) ≤ b by linarith)
  have hDbq := Dq_mono (show (4 : ℝ) ≤ b by linarith) hbq
  have hDq : 0 < Dq q := lt_of_lt_of_le hDb hDbq
  refine add_le_add ?_ ?_
  · have e : 1 / Real.sqrt q ≤ 1 / Real.sqrt b :=
      one_div_le_one_div_of_le (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt hbq)
    exact div_le_div₀ (by positivity) e hDb hDbq
  · have e : 2 * (1 / q) * (4 - 6 / q) ≤ 2 * (1 / b) * (4 - 6 / b) := by
      have hq0 : 0 < q := by linarith
      have hb0 : 0 < b := by linarith
      rw [show 2 * (1 / q) * (4 - 6 / q) = (8 * q - 12) / q ^ 2 by field_simp; ring,
        show 2 * (1 / b) * (4 - 6 / b) = (8 * b - 12) / b ^ 2 by field_simp; ring,
        div_le_div_iff₀ (by positivity) (by positivity)]
      have h1 : 0 ≤ q - b := by linarith
      have h2 : 0 ≤ 8 * b * q - 12 * b - 12 * q := by nlinarith
      nlinarith [mul_nonneg h1 h2]
    have e0 : 0 ≤ 2 * (1 / b) * (4 - 6 / b) := by
      have : 6 / b ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
      have : 0 ≤ 1 / b := by positivity
      nlinarith
    exact div_le_div₀ e0 e hDb hDbq

/-- `a^G_b ≥ b^{-1/2}`. -/
theorem aG_ge {b : ℝ} (hb : 7 ≤ b) : 1 / Real.sqrt b ≤ aG b := by
  rw [aG_split (by linarith)]
  have hD := Dq_pos (show (4 : ℝ) ≤ b by linarith)
  have hD1 := Dq_le_one (show (4 : ℝ) ≤ b by linarith)
  have h1 : 1 / Real.sqrt b ≤ (1 / Real.sqrt b) / Dq b := by
    rw [le_div_iff₀ hD]
    have : 0 ≤ 1 / Real.sqrt b := by positivity
    nlinarith
  have h2 : 0 ≤ (2 * (1 / b) * (4 - 6 / b)) / Dq b := by
    have : 6 / b ≤ 4 := by rw [div_le_iff₀ (by linarith)]; linarith
    have : 0 ≤ 1 / b := by positivity
    exact div_nonneg (by nlinarith) hD.le
  linarith

/-- **`α^G_q = d_q + s^G_q + a^G_q ≤ 2 q^{-1/2}`** for `√q ≥ 64` (in particular `q ≥ 2^24`). -/
theorem alpha_le {q : ℝ} (hq : 64 ≤ Real.sqrt q) : dG q + sG q + aG q ≤ 2 / Real.sqrt q := by
  set s := Real.sqrt q
  have hq0 : 0 ≤ q := by
    by_contra h
    push Not at h
    have : Real.sqrt q = 0 := Real.sqrt_eq_zero'.mpr h.le
    linarith
  have hs2 : s ^ 2 = q := Real.sq_sqrt hq0
  have hq4 : 4096 ≤ q := by nlinarith
  rw [aG_eq (by linarith)]
  have hd : dG q ≤ 1 / 10 / s := by
    unfold dG
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hs0 : 0 ≤ s := by linarith
  have hsg : sG q ≤ 1 / 10 / s := by
    unfold sG
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
    rw [← hs2]
    nlinarith [mul_le_mul_of_nonneg_right hq (pow_nonneg hs0 3), pow_nonneg hs0 3]
  have ha : (q * s + 8 * q - 12) / ((q - 2) * (q - 3)) ≤ 3 / 2 / s := by
    rw [div_le_div_iff₀ (by nlinarith) (by linarith)]
    rw [← hs2]
    nlinarith [pow_pos (show (0 : ℝ) < s by linarith) 3, pow_pos (show (0 : ℝ) < s by linarith) 4]
  have : 1 / 10 / s + 1 / 10 / s + 3 / 2 / s ≤ 2 / s := by
    rw [← add_div, ← add_div]
    exact div_le_div_of_nonneg_right (by norm_num) (by linarith)
  linarith

theorem sqrt_ge_of {b : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b) : 4096 ≤ Real.sqrt b := by
  rw [show (4096 : ℝ) = Real.sqrt (2 ^ 24) by
    rw [show (2 : ℝ) ^ 24 = 4096 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt hb

/-- On supports of at least two primes, the mirror symmetric difference:
`(2 b^{-1/2})² + d_b² ≤ 5/b ≤ s_b`. -/
theorem mirror_multi_sym {b : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b) :
    (|(1 / 2 : ℝ)| + |(1 / 2 : ℝ)|) * (2 / Real.sqrt b) ^ 2 + |(1 : ℝ)| * dG b ^ 2 ≤ sG b := by
  have hb0 : 0 ≤ b := by linarith
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_one, div_pow, Real.sq_sqrt hb0]
  unfold dG sG
  rw [div_pow]
  have hb2 : 0 < b - 2 := by linarith
  have hb3 : 0 < b - 3 := by linarith
  have e : (1 / 2 + 1 / 2) * (2 ^ 2 / b) + 1 * (2 ^ 2 / (b - 2) ^ 2) =
      (4 * (b - 2) ^ 2 + 4 * b) / (b * (b - 2) ^ 2) := by
    field_simp
    ring
  rw [e, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_pos hb2 hb3, mul_pos (mul_pos hb2 hb2) hb3]

/-- On supports of at least two primes, the mirror skew part: `(2 b^{-1/2})² = 4/b ≤ a_b`. -/
theorem mirror_multi_skew {b : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b) :
    (|(1 / 2 : ℝ)| + |-(1 / 2 : ℝ)|) * (2 / Real.sqrt b) ^ 2 + |(0 : ℝ)| * dG b ^ 2 ≤ aG b := by
  have hb0 : 0 ≤ b := by linarith
  have hs := sqrt_ge_of hb
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_neg,
    abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
    abs_zero, zero_mul, add_zero]
  refine le_trans ?_ (aG_ge (by linarith))
  have hsq : Real.sqrt b * Real.sqrt b = b := Real.mul_self_sqrt hb0
  have key : 4 / b ≤ 1 / Real.sqrt b := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  rw [div_pow, Real.sq_sqrt hb0]
  calc (1 / 2 + 1 / 2) * (2 ^ 2 / b) = 4 / b := by norm_num
    _ ≤ _ := key

theorem two_div_sqrt_le_one {b : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b) : 2 / Real.sqrt b ≤ 1 := by
  have hs := sqrt_ge_of hb
  rw [div_le_one (by linarith)]
  linarith

/-! ## The records at the reserved cut -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

omit [Fintype ι] [DecidableEq ι] in
theorem mP_coupling_mir (hm : ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty)
    (h7 : ∀ i, 7 ≤ pr i) (h3 : ∀ i, pr i % 4 = 3) :
    IsCoupling (fun i => mP (pr i)) (fun i => mirC (hm i)) where
  row i a := (mirC_coupling (hm i) (h7 i) (h3 i) a).1
  col i b := (mirC_coupling (hm i) (h7 i) (h3 i) b).2

/-- The mirror-edge replacement's form is the form of `⊗_p P^c_p`. -/
theorem form_newMirror_cm (s : Fin 2) {k : Fin 3} (hk : k ≠ 2)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (mergeRec pr h (s, k)).weight) F G =
      lift (mh pr s k F) ⬝ᵥ
        (piKron (fun i => mirC (blockMirror_nonempty pr h i)) *ᵥ lift (mh pr s k G)) := by
  unfold mergeRec
  rw [form_emit_gen _ _ _ _ (newM_half s k) (newM_flip s k)]
  unfold blockMergeRepLaw
  rw [expect_tensor_cm _ (0, 0) (1, 0) (0, 1) (1, 1) (mh pr s k F) (mh pr s k G)]
  have hl : ∀ i, mergeRepLaw (h.ringChar_ne i) (blockMirror_nonempty pr h i) k =
      mirrorLaw (blockMirror_nonempty pr h i) := fun i => by
    unfold mergeRepLaw
    simp [hk]
  simp only [hl]
  rfl

theorem hS_sub (L₁ L₂ : SlotMeasure (BlockLabel pr))
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G := rfl

/-- **The symmetric part of the mirror change** is `Sym(⊗ P^c) − ⊗ D`. -/
theorem form_mirror_sym (s : Fin 2) {k : Fin 3} (hk : k ≠ 2) (C : FoldComponents pr hne) (t : ℝ)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .sym)
        F G =
      chg (fun i => mirC (blockMirror_nonempty pr h i)) (fun i => srcC (hne.E2 i)) (1 / 2) (1 / 2)
        1 (lift (mh pr s k F)) (lift (mh pr s k G)) := by
  change reservedCut.form (symPart reservedCut
    (signedIntegral (mergeRec pr h (s, k)).weight - oldM pr hne s k)) F G = _
  unfold symPart
  rw [form_smul, form_add, form_reflect, hS_sub, hS_sub, form_oldM_symm pr hne s k F G,
    form_newMirror_cm pr h s hk, form_newMirror_cm pr h s hk, form_oldM_cm]
  unfold chg
  ring

/-- **The skew part of the mirror change** is `Skew(⊗ P^c)` (the source is symmetric). -/
theorem form_mirror_skew (s : Fin 2) {k : Fin 3} (hk : k ≠ 2) (C : FoldComponents pr hne) (t : ℝ)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .skew)
        F G =
      chg (fun i => mirC (blockMirror_nonempty pr h i)) (fun i => srcC (hne.E2 i)) (1 / 2)
        (-(1 / 2)) 0 (lift (mh pr s k F)) (lift (mh pr s k G)) := by
  change reservedCut.form (skewPart reservedCut
    (signedIntegral (mergeRec pr h (s, k)).weight - oldM pr hne s k)) F G = _
  unfold skewPart
  rw [form_smul, hS_sub, form_reflect, hS_sub, hS_sub, form_oldM_symm pr hne s k F G,
    form_newMirror_cm pr h s hk, form_newMirror_cm pr h s hk]
  unfold chg
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem mir_centred_block (hm : ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty)
    (h7 : ∀ i, 7 ≤ pr i) (h3 : ∀ i, pr i % 4 = 3)
    (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    {b' : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (i : ι) :
    CentredNorm (mP (pr i)) (mirC (hm i)) (2 / Real.sqrt b') := by
  have hp7 : (7 : ℝ) ≤ pr i := by have := h7 i; exact_mod_cast this
  have hsq : 4096 ≤ Real.sqrt (pr i : ℝ) := sqrt_ge_of (hb.trans (hbp i))
  have hα := alpha_le (q := (pr i : ℝ)) (by linarith)
  have hd0 : 0 ≤ dG (pr i : ℝ) := by unfold dG; exact div_nonneg (by norm_num) (by linarith)
  have hs0 : 0 ≤ sG (pr i : ℝ) := by
    unfold sG; exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have ha0 : 0 ≤ aG (pr i : ℝ) := le_trans (by positivity) (aG_ge hp7)
  refine centredNorm_mono mP_nonneg (mir_centred (hm i) (h7 i) (h3 i) (hE i))
    (by linarith) (hα.trans ?_)
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith [sqrt_ge_of hb])
    (Real.sqrt_le_sqrt (hbp i))

omit [Fintype ι] [DecidableEq ι] in
theorem src_centred_block (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (h7 : ∀ i, 7 ≤ pr i) {b' : ℝ} (hb7 : 7 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) (i : ι) :
    CentredNorm (mP (pr i)) (srcC (hE i)) (dG b') := by
  have hp5 : 5 ≤ pr i := by have := h7 i; omega
  refine centredNorm_mono mP_nonneg (src_centred _ hp5) ?_ (dG_mono hb7 (hbp i))
  unfold dG
  have : (7 : ℝ) ≤ pr i := hb7.trans (hbp i)
  exact div_nonneg (by norm_num) (by linarith)

/-- **`lem:merge-repair`, symmetric norm of the mirror-edge replacement**: `s_b`, for
`2^24 ≤ b` below every prime of the block. -/
theorem mirror_sym_paper (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (s : Fin 2) (k : Fin 3) (hk : k ≠ 2) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, k)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .sym) (sG b') := by
  have hb7 : 7 ≤ b' := le_trans (by norm_num) hb
  obtain ⟨hd0, hd1, -⟩ := merge_numbers hb7
  have he : 0 ≤ sG b' := by
    unfold sG; exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  refine ⟨he, fun F G => ?_⟩
  change |_| ≤ sG b' * Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s k u).castSucc))).weight) F) *
    Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s k u).castSucc))).weight) G)
  rw [form_mirror_sym pr h hne root W I hr b s hk C t F G, hsq_merge_ip pr hne s k F,
    hsq_merge_ip pr hne s k G]
  have hp5 : ∀ i, 5 ≤ pr i := fun i => by have := h.ge7 i; omega
  refine change_le (fun i => mP_nonneg) (fun i => sum_mP)
    (mP_coupling_mir pr (blockMirror_nonempty pr h) h.ge7 h.mod4) (mP_coupling_src pr hne.E2)
    (fun i => mirC_nonneg _) (fun i => srcC_nonneg _) (by norm_num) (by positivity)
    (two_div_sqrt_le_one hb) hd0 hd1
    (mir_centred_block pr (blockMirror_nonempty pr h) h.ge7 h.mod4 hne.E2 hb hbp)
    (src_centred_block pr hne.E2 h.ge7 hb7 hbp) he (mirror_multi_sym hb) (fun i u v _ _ => ?_)
    (fun _ => (0, 0)) _ _
  refine (mir_single_sym _ (hp5 i) (h.mod4 i) (hne.E2 i) u v).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  exact sG_mono hb7 (hbp i)

/-- **`lem:merge-repair`, skew norm of the mirror-edge replacement**: `a_b`, for `2^24 ≤ b`
below every prime of the block. -/
theorem mirror_skew_paper (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ} (hb : (2 : ℝ) ^ 24 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (s : Fin 2) (k : Fin 3) (hk : k ≠ 2) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, k)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, k)))) .skew) (aG b') := by
  have hb7 : 7 ≤ b' := le_trans (by norm_num) hb
  obtain ⟨hd0, hd1, -⟩ := merge_numbers hb7
  have he : 0 ≤ aG b' := le_trans (by positivity) (aG_ge hb7)
  refine ⟨he, fun F G => ?_⟩
  change |_| ≤ aG b' * Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s k u).castSucc))).weight) F) *
    Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s k u).castSucc))).weight) G)
  rw [form_mirror_skew pr h hne root W I hr b s hk C t F G, hsq_merge_ip pr hne s k F,
    hsq_merge_ip pr hne s k G]
  have hp5 : ∀ i, 5 ≤ pr i := fun i => by have := h.ge7 i; omega
  refine change_le (fun i => mP_nonneg) (fun i => sum_mP)
    (mP_coupling_mir pr (blockMirror_nonempty pr h) h.ge7 h.mod4) (mP_coupling_src pr hne.E2)
    (fun i => mirC_nonneg _) (fun i => srcC_nonneg _) (by norm_num) (by positivity)
    (two_div_sqrt_le_one hb) hd0 hd1
    (mir_centred_block pr (blockMirror_nonempty pr h) h.ge7 h.mod4 hne.E2 hb hbp)
    (src_centred_block pr hne.E2 h.ge7 hb7 hbp) he (mirror_multi_skew hb) (fun i u v hu hv => ?_)
    (fun _ => (0, 0)) _ _
  refine (mir_single_skew _ (hp5 i) (h.mod4 i) (hne.E2 i) u v hu hv).trans ?_
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)
  exact aG_mono hb7 (hbp i)

end Frame

end Sarkozy.NormBoundsPaper2

module

public import Sarkozy.NormBoundsPaper2.PrimeBounds

@[expose] public section

/-!
# The symmetric norm of the first-coordinate merge replacements (`lem:merge-repair`, `Ms₂`)

`paper/sections/21_middle_records.tex`, `lem:merge-repair`: for a block with least prime `b`, "the
differences between the product replacement and the product source have symmetric … norms at
most … first-coordinate replacement: `d_b + η_b`", relative to the product of the actual half laws.

The proof is the paper's:
* the block forms of the old record `G_{s2}` (V1's `E` law) and of its replacement (V3's
  `firstLaw`) are the forms of the product couplings `⊗_p D_p` and `⊗_p P^s_p` on
  `∏_p (𝔽_p × 𝔽_p)` (`expect_tensor_cm`, `form_oldM_cm`, `form_newM_cm`), and the actual half law
  is `⊗_p m_p` (`hsq_oldM_ip`);
* the old record is symmetric at the cut (HN's `form_oldM_symm`), so the symmetric part of the
  change is `Sym(⊗ P^s) − ⊗ D` (`form_merge2_sym`);
* "Every operator is Markov in the same actual half law, so it preserves the orthogonal
  decomposition by exact nonconstant prime support. … On singleton supports use the prime bounds"
  (`first_single`: `d_p + η^G_p`). "For the first-coordinate difference the corresponding bounds
  are `ρ_b² + d_b²`" on supports of at least two primes (the prime centred norms `src_centred`,
  `first_centred`), and `ρ_b² + d_b² ≤ d_b + η_b` (`merge_numbers`). This is `change_le`.

**`merge2_sym_paper`** is the field `Ms₂` of B8's `NormBounds`, for every `b ≥ 7` below the primes
of the block (no `p ≥ 2^24` restriction; no Weil bound).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.IndexSupport Sarkozy.Mixing Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (invN KD hf oldM mh form_oldM_symm form_emit_gen oldM_half oldM_flip
  newM_half newM_flip hsq_oldM invN_pos rho paper_numbers prime_le_least)
open Sarkozy.MiddleRecords (dG etaG)

/-! ## Pair functions on the block -/

section Bridge

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

/-- `∏_i (𝔽_{p_i} × 𝔽_{p_i}) ≃ (∏_i 𝔽_{p_i})²`. -/
def pairEquiv : (∀ i, ZMod (pr i) × ZMod (pr i)) ≃ BlockLabel pr × BlockLabel pr where
  toFun x := (fun i => (x i).1, fun i => (x i).2)
  invFun q i := (q.1 i, q.2 i)
  left_inv _ := rfl
  right_inv _ := rfl

/-- A pair function on the block as a function on `∏_i (𝔽_{p_i} × 𝔽_{p_i})`. -/
def lift (φ : BlockLabel pr → BlockLabel pr → ℝ) : (∀ i, ZMod (pr i) × ZMod (pr i)) → ℝ :=
  fun x => φ (fun i => (x i).1) (fun i => (x i).2)

theorem sum_lift (H : BlockLabel pr → BlockLabel pr → ℝ) :
    ∑ x : ∀ i, ZMod (pr i) × ZMod (pr i), H (fun i => (x i).1) (fun i => (x i).2) =
      ∑ a, ∑ a₁, H a a₁ := by
  exact (Fintype.sum_equiv pairEquiv (fun x => H (fun i => (x i).1) (fun i => (x i).2))
    (fun q => H q.1 q.2) (fun _ => rfl)).trans (Fintype.sum_prod_type _)

omit [DecidableEq ι] in
theorem prod_ite01 {κ : Type} [Fintype κ] (c : κ → Prop) [∀ i, Decidable (c i)]
    [Decidable (∀ i, c i)] : ∏ i, (if c i then (1 : ℝ) else 0) = if ∀ i, c i then 1 else 0 := by
  split_ifs with hc
  · exact prod_eq_one fun i _ => by simp [hc i]
  · push Not at hc
    obtain ⟨i, hi⟩ := hc
    exact prod_eq_zero (mem_univ i) (by simp [hi])

/-- **The form of a tensor law read at two pairs is the form of the product coupling.** -/
theorem expect_tensor_cm {W : Type} [Fintype W] [DecidableEq W]
    (μ : ∀ i, FiniteLaw (W → ZMod (pr i))) (u₀ u₁ v₀ v₁ : W)
    (φ ψ : BlockLabel pr → BlockLabel pr → ℝ) :
    (FiniteLaw.tensor μ).expect (fun y => φ (y u₀) (y u₁) * ψ (y v₀) (y v₁)) =
      lift φ ⬝ᵥ (piKron (fun i => cm (μ i) u₀ u₁ v₀ v₁) *ᵥ lift ψ) := by
  rw [expect_tensor_eq_sum]
  set X : (∀ i, W → ZMod (pr i)) → ∀ i, ZMod (pr i) × ZMod (pr i) :=
    fun z i => (z i u₀, z i u₁)
  set Y : (∀ i, W → ZMod (pr i)) → ∀ i, ZMod (pr i) × ZMod (pr i) :=
    fun z i => (z i v₀, z i v₁)
  have key : ∀ x y : ∀ i, ZMod (pr i) × ZMod (pr i),
      ∏ i, cm (μ i) u₀ u₁ v₀ v₁ (x i) (y i) =
        ∑ z : ∀ i, W → ZMod (pr i), (∏ i, (μ i).weight (z i)) *
          (if x = X z ∧ y = Y z then 1 else 0) := by
    intro x y
    unfold cm
    rw [Fintype.prod_sum]
    refine sum_congr rfl fun z _ => ?_
    rw [prod_mul_distrib, prod_ite01]
    congr 1
    refine if_congr ?_ rfl rfl
    constructor
    · intro hc
      refine ⟨funext fun i => ?_, funext fun i => ?_⟩
      · obtain ⟨h1, h2, -, -⟩ := hc i
        exact Prod.ext h1.symm h2.symm
      · obtain ⟨-, -, h3, h4⟩ := hc i
        exact Prod.ext h3.symm h4.symm
    · rintro ⟨hx, hy⟩ i
      subst hx hy
      exact ⟨rfl, rfl, rfl, rfl⟩
  simp only [dotProduct, Matrix.mulVec, piKron_apply, key, sum_mul, mul_sum]
  have inner : ∀ x, ∑ y, ∑ z, lift φ x * ((∏ i, (μ i).weight (z i)) *
      (if x = X z ∧ y = Y z then (1 : ℝ) else 0) * lift ψ y) =
      ∑ z, ∑ y, lift φ x * ((∏ i, (μ i).weight (z i)) *
      (if x = X z ∧ y = Y z then (1 : ℝ) else 0) * lift ψ y) := fun x => sum_comm
  rw [sum_congr rfl fun x _ => inner x, sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [sum_eq_single (X z)]
  · rw [sum_eq_single (Y z)]
    · simp only [and_self, ↓reduceIte, mul_one]
      unfold lift
      ring
    · intro y _ hy
      simp [hy]
    · exact fun h => absurd (mem_univ _) h
  · intro x _ hx
    refine sum_eq_zero fun y _ => ?_
    simp [hx]
  · exact fun h => absurd (mem_univ _) h

omit [DecidableEq ι] in
theorem prodW_mP (x : ∀ i, ZMod (pr i) × ZMod (pr i)) :
    prodW (fun i => mP (pr i)) x =
      invN pr * KD pr ((fun i => (x i).2) - fun i => (x i).1) := by
  unfold prodW mP invN KD
  rw [← prod_mul_distrib]
  rfl

theorem ip_lift (φ : BlockLabel pr → BlockLabel pr → ℝ) :
    ip (fun i => mP (pr i)) (lift φ) (lift φ) =
      invN pr * ∑ a, ∑ a₁, KD pr (a₁ - a) * φ a a₁ ^ 2 := by
  unfold ip
  simp only [dotProduct, Matrix.mulVec_diagonal, prodW_mP]
  rw [show invN pr * ∑ a, ∑ a₁, KD pr (a₁ - a) * φ a a₁ ^ 2 =
    ∑ a, ∑ a₁, invN pr * (KD pr (a₁ - a) * φ a a₁ ^ 2) by simp only [mul_sum]]
  rw [← sum_lift (fun a a₁ => invN pr * (KD pr (a₁ - a) * φ a a₁ ^ 2))]
  refine sum_congr rfl fun x _ => ?_
  unfold lift
  ring

end Bridge

/-! ## The block couplings -/

section Couplings

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
theorem mP_coupling_src (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty) :
    IsCoupling (fun i => mP (pr i)) (fun i => srcC (hE i)) where
  row i a := src_coupling_row (hE i) a
  col i b := src_coupling_col (hE i) b

omit [Fintype ι] [DecidableEq ι] in
theorem mP_coupling_first (h : ClassThreeBlock pr) :
    IsCoupling (fun i => mP (pr i)) (fun i => firstC (h.ringChar_ne i)) where
  row i a := first_coupling_row (h.ringChar_ne i) (by have := h.ge7 i; omega) a
  col i b := first_coupling_col (h.ringChar_ne i) (by have := h.ge7 i; omega) b

end Couplings

/-! ## Numbers -/

theorem centredNorm_mono {B : Type} [Fintype B] {μ : B → ℝ} {C : Matrix B B ℝ} {δ δ' : ℝ}
    (hμ : ∀ a, 0 ≤ μ a) (h : CentredNorm μ C δ) (hδ : 0 ≤ δ) (hδδ : δ ≤ δ') :
    CentredNorm μ C δ' := by
  intro f hf
  refine (h f hf).trans (mul_le_mul_of_nonneg_right ?_ (sum_nonneg fun a _ =>
    mul_nonneg (hμ a) (sq_nonneg _)))
  exact pow_le_pow_left₀ hδ hδδ 2

theorem dG_mono {b p : ℝ} (hb : 7 ≤ b) (hbp : b ≤ p) : dG p ≤ dG b := by
  unfold dG
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

theorem etaG_mono {b p : ℝ} (hb : 7 ≤ b) (hbp : b ≤ p) : etaG p ≤ etaG b := by
  unfold etaG
  exact div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- **The numerical facts of the proof of `lem:merge-repair`** for the first-coordinate
difference, `b ≥ 7`: `d_b ≤ 1` and `ρ_b² + d_b² ≤ d_b + η_b`. -/
theorem merge_numbers {b : ℝ} (hb : 7 ≤ b) :
    0 ≤ dG b ∧ dG b ≤ 1 ∧ rho b ^ 2 + dG b ^ 2 ≤ dG b + etaG b := by
  have hb2 : 0 < b - 2 := by linarith
  have hb1 : 0 < b - 1 := by linarith
  have hρ2 : rho b ^ 2 = (b + 1) / (b - 1) ^ 2 := Real.sq_sqrt (by positivity)
  refine ⟨by unfold dG; positivity, ?_, ?_⟩
  · unfold dG; rw [div_le_one hb2]; linarith
  · rw [hρ2]
    unfold dG etaG
    rw [div_add_div _ _ hb2.ne' hb1.ne', div_pow, div_add_div _ _ (by positivity) (by positivity),
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos hb1 hb2, mul_pos (mul_pos hb1 hb2) (mul_pos hb1 hb2),
      mul_pos (mul_pos (mul_pos hb1 hb2) (mul_pos hb1 hb2)) (by linarith : (0 : ℝ) < b - 7 + 1)]

/-! ## The records at the reserved cut -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- The old merge record's form is the form of `⊗_p D_p`. -/
theorem form_oldM_cm (s : Fin 2) (k : Fin 3) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (oldM pr hne s k) F G =
      lift (mh pr s k F) ⬝ᵥ (piKron (fun i => srcC (hne.E2 i)) *ᵥ lift (mh pr s k G)) := by
  rw [form_emit_gen _ _ _ _ (oldM_half s k) (oldM_flip s k)]
  unfold blockGraphLaw
  exact expect_tensor_cm _ (0, 0) (1, 0) (0, 1) (1, 1) (mh pr s k F) (mh pr s k G)

/-- The first-coordinate replacement's form is the form of `⊗_p P^s_p`. -/
theorem form_newM_cm (s : Fin 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (mergeRec pr h (s, 2)).weight) F G =
      lift (mh pr s 2 F) ⬝ᵥ
        (piKron (fun i => firstC (h.ringChar_ne i)) *ᵥ lift (mh pr s 2 G)) := by
  unfold mergeRec
  rw [form_emit_gen _ _ _ _ (newM_half s 2) (newM_flip s 2)]
  unfold blockMergeRepLaw
  rw [expect_tensor_cm _ (0, 0) (1, 0) (0, 1) (1, 1) (mh pr s 2 F) (mh pr s 2 G)]
  rfl

/-- **The symmetric part of the first-coordinate change** is `Sym(⊗ P^s) − ⊗ D`. -/
theorem form_merge2_sym (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .sym)
        F G =
      chg (fun i => firstC (h.ringChar_ne i)) (fun i => srcC (hne.E2 i)) (1 / 2) (1 / 2) 1
        (lift (mh pr s 2 F)) (lift (mh pr s 2 G)) := by
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  change reservedCut.form (symPart reservedCut
    (signedIntegral (mergeRec pr h (s, 2)).weight - oldM pr hne s 2)) F G = _
  unfold symPart
  rw [form_smul, form_add, form_reflect, hS, hS, form_oldM_symm pr hne s 2 F G, form_newM_cm,
    form_newM_cm, form_oldM_cm]
  unfold chg
  ring

theorem hsq_merge_ip (s : Fin 2) (k : Fin 3) (F : (reservedCut.Half → BlockLabel pr) → ℝ) :
    hsq reservedCut (plusMarginal reservedCut (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
        (midEmission (fun u => (merge s k u).castSucc))).weight) F =
      ip (fun i => mP (pr i)) (lift (mh pr s k F)) (lift (mh pr s k F)) := by
  rw [hsq_oldM pr hne s k F, ip_lift]

/-- **`lem:merge-repair`, symmetric norm of the first-coordinate replacement**: `d_b + η_b` for
every `b ≥ 7` below the primes of the block. -/
theorem merge2_sym (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ}
    (hb7 : 7 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .sym)
      (dG b' + etaG b') := by
  obtain ⟨hd0, hd1, hnum⟩ := merge_numbers hb7
  obtain ⟨hρ0, -, hρ1, -, -, -⟩ := paper_numbers hb7
  have he : 0 ≤ dG b' + etaG b' := by
    have : 0 ≤ etaG b' := by unfold etaG; exact div_nonneg (by norm_num) (by linarith)
    linarith
  refine ⟨he, fun F G => ?_⟩
  change |_| ≤ (dG b' + etaG b') * Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s 2 u).castSucc))).weight) F) *
    Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s 2 u).castSucc))).weight) G)
  rw [form_merge2_sym pr h hne root W I hr b s C t F G, hsq_merge_ip pr hne s 2 F,
    hsq_merge_ip pr hne s 2 G]
  have hp5 : ∀ i, 5 ≤ pr i := fun i => by have := h.ge7 i; omega
  refine change_le (fun i => mP_nonneg) (fun i => sum_mP) (mP_coupling_first pr h)
    (mP_coupling_src pr hne.E2) (fun i => firstC_nonneg _) (fun i => srcC_nonneg _)
    (by norm_num) hρ0 hρ1 hd0 hd1 (fun i => ?_) (fun i => ?_) he ?_ (fun i u v hu hv => ?_)
    (fun _ => (0, 0)) _ _
  · -- the prime centred norms of the replacement
    refine centredNorm_mono mP_nonneg (first_centred _ (h.mod4 i)) (Real.sqrt_nonneg _) ?_
    calc Real.sqrt (((pr i : ℝ) + 1) / ((pr i : ℝ) - 1) ^ 2) ≤ Real.sqrt (rho b' ^ 2) :=
          Real.sqrt_le_sqrt (prime_le_least hb7 (hbp i)).2.2
      _ = rho b' := Real.sqrt_sq hρ0
  · -- the prime centred norms of the source
    refine centredNorm_mono mP_nonneg (src_centred _ (hp5 i)) ?_ (dG_mono hb7 (hbp i))
    unfold dG
    have : (7 : ℝ) ≤ pr i := hb7.trans (hbp i)
    exact div_nonneg (by norm_num) (by linarith)
  · rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), abs_one]
    linarith
  · -- the singleton supports
    refine (first_single (hne.E2 i) (h.ringChar_ne i) (hp5 i) (h.mod4 i) u v hu hv).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
    exact add_le_add (dG_mono hb7 (hbp i)) (etaG_mono hb7 (hbp i))

/-- **The field `Ms₂` of `NormBounds` at the paper's constant** (`lem:merge-repair`):
`d_b + η_b`, `b ≥ 7` below every prime of the block. -/
theorem merge2_sym_paper (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ} (hb7 : 7 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (s : Fin 2) :
    FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .sym)
      (dG b' + etaG b') :=
  merge2_sym pr h hne root W I hr b s C t hb7 hbp

end Frame

end Sarkozy.NormBoundsPaper2

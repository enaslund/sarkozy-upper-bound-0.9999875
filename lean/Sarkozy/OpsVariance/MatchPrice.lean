module

public import Sarkozy.OpsVariance.MatchFront
public import Sarkozy.UpperComparison.Transfer

@[expose] public section

/-!
# The two matching records of a middle block have the same price

`paper/sections/22_variance.tex`, `lem:var-gain` (a common price `γ` on a class),
`cor:var-classes`(ii) (aligned pairs `E^X_0`, `E^X_1`); `paper/sections/21_middle_records.tex`,
`lem:middle-comparison-prices`.

B8's `ofFold` prices the change of a record by its optimal norm (`optNorm`) at `ι`, relative to the
record's half marginal. The prices of `E₀` and `E₁` are therefore not equal by definition. They
are equal because `E₁(u) = E₀(u − 1)` (`matching_one`): the slot shift `u₀ ↦ u₀ − 1` preserves
the reserved cut `ι` (which flips only the layer), and it carries the replacement `⊗_p K₁` and the
record `Π_{E₁}` to those of `E₀`. So the cut forms and the half-marginal norms correspond under
`H ↦ H(· ∘ shift)`, a bijection, and the optimal norms agree.

* `matching_one`, `shiftH`, `readT_one`; **`form_emit_shift`**, `hsq_shift`, `optNorm_shift`;
* **`N_match_shift`**, **`piT_match_shift`**: at B8's `ofFold` atom, `N(E₁, e) = N(E₀, e)` and
  the prices `π̃(E₁, e) = π̃(E₀, e)` (the coefficients `w_S r` agree);
* **`matchPrice_atom`**, **`matchPrice_CL`**: all matching records of a block have the same price,
  at B7's atom and at B2's comparison law;
* RP (9 November 2026): the front prices the middle records at their bounds (`ofFoldM`,
  `N = max(optNorm, boundN)`); `N_match_shiftM`, `piT_match_shiftM`, `piT_match_eqM`,
  `matchPrice_atomM` are the twins (the bound of a matching does not depend on `s`; under the
  twelve norm bounds the price is the bound itself, `ofFoldM_N_eq`), and `matchPrice_CL` uses them;
* `InMatch`, **`alignedPrice_front`**: at the obligations' data, an aligned pair `{ω₀, ω₁}` (same
  support, same change types, matching records) has a common price `π̃_{ω₀} = π̃_{ω₁}` (`hγ` of
  `hres_of_restoration` and `hres_aligned`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.FirstStagePaper Sarkozy.ComparisonLawPaper
open Sarkozy.PartVLaws Sarkozy.MiddleComparison Sarkozy.SignedComponents Sarkozy.Variance
open Sarkozy.Labellings (matchGraph matching)
open Sarkozy.CancellationSteps (PaperJ0 PaperJt paperM0 paperTail)
open Sarkozy.BlockSpecPaper (PaperAnalyticInputs paperIn blockLeast)

/-! ## The slot shift -/

/-- `E₁(u) = E₀(u − 1)`. -/
theorem matching_one (u : ZMod 6) : matching 1 u = matching 0 (u - 1) := by
  fin_cases u <;> rfl

theorem mem_half_iff (a a' : Chamber) (b : Chamber × Layer) :
    ((a, b) : Slot) ∈ reservedCut.half ↔ ((a', b) : Slot) ∈ reservedCut.half := by
  simp [reservedCut, ReflectionCut.prodRight, Finset.mem_product]

/-- The shift `u₀ ↦ u₀ − 1` on the plus half of `ι`. -/
def shiftH : reservedCut.Half ≃ reservedCut.Half where
  toFun v := ⟨(v.1.1 - 1, v.1.2), (mem_half_iff v.1.1 _ v.1.2).mp v.2⟩
  invFun v := ⟨(v.1.1 + 1, v.1.2), (mem_half_iff v.1.1 _ v.1.2).mp v.2⟩
  left_inv v := by
    apply Subtype.ext
    simp
  right_inv v := by
    apply Subtype.ext
    simp

theorem readT_one {F : Type} (t : Fin 3 → F) :
    readT (matching 1) t = readT (matching 0) t ∘ shiftH := by
  funext v
  change t (matching 1 v.1.1) = t (matching 0 (v.1.1 - 1))
  rw [matching_one]

section Shift

variable {F : Type} [Fintype F] [DecidableEq F]

/-- Precomposition with the shift, on functions of a half. -/
def preS (H : (reservedCut.Half → F) → ℝ) : (reservedCut.Half → F) → ℝ :=
  fun x => H (x ∘ shiftH)

/-- Its inverse. -/
def postS (H : (reservedCut.Half → F) → ℝ) : (reservedCut.Half → F) → ℝ :=
  fun x => H (x ∘ shiftH.symm)

omit [Fintype F] [DecidableEq F] in
theorem preS_postS (H : (reservedCut.Half → F) → ℝ) : preS (postS H) = H := by
  funext x
  change H ((x ∘ shiftH) ∘ shiftH.symm) = H x
  congr 1
  funext v
  simp

/-- **The cut form of an `E₁`-emitted law is that of the `E₀`-emitted law, shifted.** -/
theorem form_emit_shift (lam : FiniteLaw (Fin 3 × Fin 2 → F)) (H K : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (midEmission (matching 1))).weight) H K =
      reservedCut.form (signedIntegral (emit lam (midEmission (matching 0))).weight)
        (preS H) (preS K) := by
  rw [form_emit_eq, form_emit_eq]
  refine sum_congr rfl fun y _ => ?_
  rw [readT_one, readT_one]
  rfl

/-- The same for the change parts of a difference of two emitted laws. -/
theorem form_change_shift (e : ChangeType) (lam lam' : FiniteLaw (Fin 3 × Fin 2 → F))
    (H K : (reservedCut.Half → F) → ℝ) :
    reservedCut.form (changePart e (signedIntegral (emit lam (midEmission (matching 1))).weight -
        signedIntegral (emit lam' (midEmission (matching 1))).weight)) H K =
      reservedCut.form (changePart e (signedIntegral (emit lam (midEmission (matching 0))).weight -
        signedIntegral (emit lam' (midEmission (matching 0))).weight)) (preS H) (preS K) := by
  cases e
  · change reservedCut.form (symPart reservedCut _) H K =
      reservedCut.form (symPart reservedCut _) (preS H) (preS K)
    rw [UpperComparison.form_symPart, UpperComparison.form_symPart]
    simp only [form_sub_law, form_emit_shift]
  · change reservedCut.form (skewPart reservedCut _) H K =
      reservedCut.form (skewPart reservedCut _) (preS H) (preS K)
    rw [UpperComparison.form_skewPart, UpperComparison.form_skewPart]
    simp only [form_sub_law, form_emit_shift]

/-- The half-marginal norms correspond under the shift. -/
theorem hsq_shift (lam : FiniteLaw (Fin 3 × Fin 2 → F)) (H : (reservedCut.Half → F) → ℝ) :
    hsq reservedCut (plusMarginal reservedCut (emit lam (midEmission (matching 1))).weight) H =
      hsq reservedCut (plusMarginal reservedCut (emit lam (midEmission (matching 0))).weight)
        (preS H) := by
  unfold hsq
  rw [← form_signedIntegral_one_right, ← form_signedIntegral_one_right, form_emit_shift]
  rfl

omit [DecidableEq F] in
/-- **Equal optimal norms** under a bijective correspondence of the forms and the norms. -/
theorem optNorm_shift (m₁ m₀ : (reservedCut.Half → F) → ℝ)
    (L₁ L₀ : ((Slot → F) → ℝ) →ₗ[ℝ] ℝ)
    (hQ : ∀ H K, reservedCut.form L₁ H K = reservedCut.form L₀ (preS H) (preS K))
    (hm : ∀ H, hsq reservedCut m₁ H = hsq reservedCut m₀ (preS H)) :
    optNorm reservedCut m₁ L₁ = optNorm reservedCut m₀ L₀ := by
  unfold optNorm
  congr 1
  ext C
  simp only [Set.mem_ofPred_eq, FormBound]
  constructor
  · rintro ⟨hC, h⟩
    refine ⟨hC, fun H K => ?_⟩
    have := h (postS H) (postS K)
    rwa [hQ, hm, hm, preS_postS, preS_postS] at this
  · rintro ⟨hC, h⟩
    refine ⟨hC, fun H K => ?_⟩
    rw [hQ, hm, hm]
    exact h _ _

end Shift

/-! ## At B8's `ofFold` atom -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **`N(E₁, e) = N(E₀, e)`** at B8's `ofFold` data. -/
theorem N_match_shift (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (e : ChangeType) :
    (ofFold pr h hne root W I hr bm C t ht0 ht1).N (.inr (.inl 1)) e =
      (ofFold pr h hne root W I hr bm C t ht0 ht1).N (.inr (.inl 0)) e := by
  change optNorm reservedCut
      (plusMarginal reservedCut
        (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2) (midEmission (matching 1))).weight)
      (changePart e (signedIntegral (emit (FiniteLaw.tensor fun i => eLaw (blockE_nonempty pr h i))
          (midEmission (matching 1))).weight -
        signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
          (midEmission (matching 1))).weight)) =
    optNorm reservedCut
      (plusMarginal reservedCut
        (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2) (midEmission (matching 0))).weight)
      (changePart e (signedIntegral (emit (FiniteLaw.tensor fun i => eLaw (blockE_nonempty pr h i))
          (midEmission (matching 0))).weight -
        signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
          (midEmission (matching 0))).weight))
  exact optNorm_shift _ _ _ _ (form_change_shift e _ _) (hsq_shift _)

/-- **`π̃(E₁, e) = π̃(E₀, e)`** at B8's `ofFold` atom. -/
theorem piT_match_shift (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (e : ChangeType) :
    (ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.piT (.inl (.inr (.inl 1))) e =
      (ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.piT (.inl (.inr (.inl 0))) e := by
  change _ * _ * (ofFold pr h hne root W I hr bm C t ht0 ht1).N (.inr (.inl 1)) e =
    _ * _ * (ofFold pr h hne root W I hr bm C t ht0 ht1).N (.inr (.inl 0)) e
  rw [N_match_shift]
  rfl

/-- All matching records of B8's `ofFold` atom have the same price. -/
theorem piT_match_eq (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (s s' : Fin 2) (e : ChangeType) :
    (ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.piT (.inl (.inr (.inl s))) e =
      (ofFold pr h hne root W I hr bm C t ht0 ht1).toReplacements.piT
        (.inl (.inr (.inl s'))) e := by
  rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨s', rfl⟩ with rfl | rfl
  · rfl
  · exact (piT_match_shift pr h hne root W I hr bm C ht0 ht1 e).symm
  · exact piT_match_shift pr h hne root W I hr bm C ht0 ht1 e
  · rfl

/-- **`N(E₁, e) = N(E₀, e)` at the data priced at the bounds** (`ofFoldM`, RP): the bound
`boundN` of a matching does not depend on `s`, and the optimal norms agree (`N_match_shift`). -/
theorem N_match_shiftM (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (b' sF aF ℓ sE aE : ℝ) (e : ChangeType) :
    (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).N (.inr (.inl 1)) e =
      (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).N (.inr (.inl 0)) e := by
  change max _ (boundN r b' sF aF ℓ sE aE (.inr (.inl 1)) e) =
    max _ (boundN r b' sF aF ℓ sE aE (.inr (.inl 0)) e)
  rw [N_match_shift pr h hne root W I hr bm C ht0 ht1 e]
  cases e <;> rfl

/-- **`π̃(E₁, e) = π̃(E₀, e)`** at the data priced at the bounds (`ofFoldM`, RP). -/
theorem piT_match_shiftM (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (b' sF aF ℓ sE aE : ℝ) (e : ChangeType) :
    (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.piT
        (.inl (.inr (.inl 1))) e =
      (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.piT
        (.inl (.inr (.inl 0))) e := by
  change _ * _ * (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).N
      (.inr (.inl 1)) e =
    _ * _ * (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).N (.inr (.inl 0)) e
  rw [N_match_shiftM]
  rfl

/-- All matching records of the data priced at the bounds (`ofFoldM`, RP) have the same price. -/
theorem piT_match_eqM (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (bm : ℝ) (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t)
    (ht1 : t ≤ 1) (b' sF aF ℓ sE aE : ℝ) (s s' : Fin 2) (e : ChangeType) :
    (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.piT
        (.inl (.inr (.inl s))) e =
      (ofFoldM pr h hne root W I hr bm C t ht0 ht1 b' sF aF ℓ sE aE).toReplacements.piT
        (.inl (.inr (.inl s'))) e := by
  rcases Fin.exists_fin_two.mp ⟨s, rfl⟩ with rfl | rfl <;>
    rcases Fin.exists_fin_two.mp ⟨s', rfl⟩ with rfl | rfl
  · rfl
  · exact (piT_match_shiftM pr h hne root W I hr bm C ht0 ht1 b' sF aF ℓ sE aE e).symm
  · exact piT_match_shiftM pr h hne root W I hr bm C ht0 ht1 b' sF aF ℓ sE aE e
  · rfl

end Frame

/-! ## At B7's atom and at the comparison law -/

section Spec

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
variable (hW : Target.Weil) (In : FirstStageInputs blockOf)

omit [Fintype B] in
/-- **All matching records of the atom of a class-three block have the same price.** -/
theorem matchPrice_atom {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S)
    (t₁ t₂ : (MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).T)
    (h₁ : t₁ ∈ matchIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC))
    (h₂ : t₂ ∈ matchIdx hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)) (e : ChangeType) :
    (MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).πt t₁ e =
      (MiddleRefinement.atomOf hW In S (FoldSpec.toSpecData hW In ht0 ht1 S FC)).πt t₂ e := by
  cases S with
  | upper U => exact absurd h₁ (notMem_empty _)
  | middleUniform M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp h₁
    obtain ⟨s', -, rfl⟩ := mem_image.mp h₂
    exact piT_match_eq _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b) FC.down
      ht0 ht1 s s' e
  | middleIndividual M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp h₁
    obtain ⟨s', -, rfl⟩ := mem_image.mp h₂
    exact piT_match_eq _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b) FC.down
      ht0 ht1 s s' e
  | middleCoherent M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp h₁
    obtain ⟨s', -, rfl⟩ := mem_image.mp h₂
    exact piT_match_eq _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b) FC.down
      ht0 ht1 s s' e

omit [Fintype B] in
/-- **`matchPrice_atom` at the data priced at the bounds** (`FoldSpec.toSpecDataM`, RP;
`piT_match_eqM`). -/
theorem matchPrice_atomM {b : B} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (bl sF aF ℓ sE aE : ℝ)
    (S : PaperBlockSpec blockOf b) (FC : FoldSpec hW S)
    (t₁ t₂ : (MiddleRefinement.atomOf hW In S
      (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).T)
    (h₁ : t₁ ∈ matchIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC))
    (h₂ : t₂ ∈ matchIdx hW In S (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC))
    (e : ChangeType) :
    (MiddleRefinement.atomOf hW In S
        (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).πt t₁ e =
      (MiddleRefinement.atomOf hW In S
        (FoldSpec.toSpecDataM hW In ht0 ht1 bl sF aF ℓ sE aE S FC)).πt t₂ e := by
  cases S with
  | upper U => exact absurd h₁ (notMem_empty _)
  | middleUniform M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp h₁
    obtain ⟨s', -, rfl⟩ := mem_image.mp h₂
    exact piT_match_eqM _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b) FC.down
      ht0 ht1 bl sF aF ℓ sE aE s s' e
  | middleIndividual M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp h₁
    obtain ⟨s', -, rfl⟩ := mem_image.mp h₂
    exact piT_match_eqM _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b) FC.down
      ht0 ht1 bl sF aF ℓ sE aE s s' e
  | middleCoherent M =>
    obtain ⟨s, -, rfl⟩ := mem_image.mp h₁
    obtain ⟨s', -, rfl⟩ := mem_image.mp h₂
    exact piT_match_eqM _ (classThree_blockPrimes b) M.hne _ M.W M.I M.hr (In.bmin b) FC.down
      ht0 ht1 bl sF aF ℓ sE aE s s' e

end Spec

section CL

open Sarkozy.MainFinalF1 (ComparisonParts bOf specF Blk)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.AnalyticCells (f1Cell)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {A : PaperAnalyticInputs f1Cell}

/-- **All matching records of a block of the paper's comparison law have the same price**, for
each change type. -/
theorem matchPrice_CL (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) (b : Blk)
    (t₁ t₂ : C.toK1.CL.T L (.inl (.inr b))) (h₁ : t₁ ∈ matchCL C L b) (h₂ : t₂ ∈ matchCL C L b)
    (e : ChangeType) :
    C.toK1.CL.πt L (.inl (.inr b)) t₁ e = C.toK1.CL.πt L (.inl (.inr b)) t₂ e := by
  unfold matchCL at h₁ h₂
  unfold ComparisonParts.CL ComparisonLawPaper.comparisonLawTarget at *
  exact matchPrice_atomM hW (paperIn f1Cell) tPaper_nonneg tPaper_le_one _ _ _ _ _ _
    (specF hW A b) _ t₁ t₂ h₁ h₂ e

/-- **The matching records of the comparison law**: `matchCL` at the middle blocks; nothing at
the other atoms. -/
def InMatch (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ) :
    (b : BlockAtom (PaperAtom Blk) (PaperJt) L) → C.toK1.CL.T L b → Prop
  | .inl (.inr b), t => t ∈ matchCL C L b
  | _, _ => False

theorem price_eq_of_inMatch (C : ComparisonPartsTC hW hMR hFour A) (L : ℕ)
    (b : BlockAtom (PaperAtom Blk) (PaperJt) L) (t₁ t₂ : C.toK1.CL.T L b)
    (h₁ : InMatch C L b t₁) (h₂ : InMatch C L b t₂) (e : ChangeType) :
    C.toK1.CL.πt L b t₁ e = C.toK1.CL.πt L b t₂ e := by
  rcases b with (q | b) | j
  · exact absurd h₁ id
  · exact matchPrice_CL C L b t₁ t₂ h₁ h₂ e
  · exact absurd h₁ id

end CL

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {UpT : UpperCapsPaper.UpperRecordTables}

/-- **An aligned pair has a common price** (`hγ` of `hres_of_restoration`, at the obligations'
data): if `ω₀`, `ω₁` have the same support and the same change types, and select matching records
at every block of the support, then `π̃_{ω₀} = π̃_{ω₁}`. -/
theorem alignedPrice_front (F : CompanionND.CompanionFrontND hW hMR hFour UpT)
    (hB : Target.BMOR) (hRR : Target.ThetaSmallRR) (L : ℕ)
    (ω₀ ω₁ : Choice ((F.X hB hRR).data.CL.T L))
    (h : ∀ b, (ω₀ b = none ∧ ω₁ b = none) ∨ ∃ t₀ t₁ e, ω₀ b = some (t₀, e) ∧
      ω₁ b = some (t₁, e) ∧ InMatch (F.toK.Up.toCmp hMR hFour) L b t₀ ∧
      InMatch (F.toK.Up.toCmp hMR hFour) L b t₁) :
    monomial ((F.X hB hRR).data.CL.πt L) ω₀ = monomial ((F.X hB hRR).data.CL.πt L) ω₁ := by
  unfold monomial
  refine prod_congr rfl fun b _ => ?_
  rcases h b with ⟨h₀, h₁⟩ | ⟨t₀, t₁, e, h₀, h₁, m₀, m₁⟩
  · rw [h₀, h₁]
  · rw [h₀, h₁]
    exact price_eq_of_inMatch (F.toK.Up.toCmp hMR hFour) L b t₀ t₁ m₀ m₁ e

end Sarkozy.OpsVariance

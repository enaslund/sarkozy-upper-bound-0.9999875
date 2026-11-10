module

public import Sarkozy.EnvelopeEnergiesPaper.MiddleMoments

@[expose] public section

/-!
# The sharp folds of the middle first stage (`lem:density:middle-catalog`, "own private sharp fold")

The last per-block input of `SF` was `MiddleRemaining`: for each middle block and tag `s`, a sharp
decomposition of `κ'_s − κ_s` relative to `κ_s` at `tagCut s` whose normalized full folded laws
have unit mixed `L^{72/θ}`. This file proves it, for every `0 < θ ≤ 12/11`:

* the decomposition is A1's own (one shared-label class, `S = Unit`): `κ_s = c · matchRec s`,
  `κ'_s − κ_s = c · (plusRec s − matchRec s)`; its sharp bound `matchRec_sharp` is A1's proof of
  `blockSharp_of_block`, restated for this explicit witness (A1's theorem only gives the
  existential `HasSharpBound`);
* **`diagonalLaw_halfMarginalPlus_emit`** (and the minus form): the full folded law of an emitted
  law is the emission along the folded emission `σ ∘ fold±` (each slot reads its partner on the
  kept half);
* the folded emissions of the matching pattern at `tagCut s` read two objects at `48` and `24`
  slots (checked by `decide`), so by M1's `emit_mixed_of_two_labels` the folded laws have unit
  mixed `L^{60}` at every prime (`72 − 24/2`), hence on the block (tensor) and at `72/θ`;
* **`middleRemaining_proved`**, **`specRemaining_proved`**: the per-block input, for every middle
  block of the paper.
-/

open Finset Function
open scoped BigOperators Matrix

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.PartV Sarkozy.DensityMoments Sarkozy.DensityUpgrade Sarkozy.TheoremC
  Sarkozy.Labellings Sarkozy.Comparison Sarkozy.FirstStagePaper Sarkozy.PartVRecords

/-! ## Full folded laws of emitted laws -/

section Fold

variable {X I : Type} [Fintype X] [DecidableEq X] [Fintype I] [DecidableEq I]

/-- **The plus full folded law of an emitted law is an emission**: `Diag(m₊(emit λ σ)) =
emit λ (σ ∘ fold₊)`. -/
theorem diagonalLaw_halfMarginalPlus_emit (c : ReflectionCut Slot) (lam : FiniteLaw (I → X))
    (σ : Slot → I) :
    c.diagonalLaw (halfMarginalPlus c (signedIntegral (emit lam σ).weight)) =
      signedIntegral (emit lam (fun v => σ (c.foldPlus v))).weight := by
  apply LinearMap.ext
  intro F
  change (∑ x, halfMarginalPlus c (signedIntegral (emit lam σ).weight) x * F (c.join x x)) =
    (emit lam (fun v => σ (c.foldPlus v))).expect F
  rw [expect_emit]
  have hm : ∀ x, halfMarginalPlus c (signedIntegral (emit lam σ).weight) x =
      lam.expect (fun y => if (fun v : c.Half => y (σ v.1)) = x then 1 else 0) := by
    intro x
    unfold halfMarginalPlus
    rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    rfl
  simp only [hm]
  unfold FiniteLaw.expect
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (fun v : c.Half => y (σ v.1))]
  · simp only [↓reduceIte, mul_one]
    congr 2
    funext v
    unfold ReflectionCut.join ReflectionCut.foldPlus
    by_cases hv : v ∈ c.half
    · simp [hv]
    · simp [hv]
  · intro x _ hx
    simp only [Ne.symm hx, ↓reduceIte, mul_zero, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

/-- **The minus full folded law of an emitted law is an emission**: `Diag(m₋(emit λ σ)) =
emit λ (σ ∘ fold₋)`. -/
theorem diagonalLaw_halfMarginalMinus_emit (c : ReflectionCut Slot) (lam : FiniteLaw (I → X))
    (σ : Slot → I) :
    c.diagonalLaw (halfMarginalMinus c (signedIntegral (emit lam σ).weight)) =
      signedIntegral (emit lam (fun v => σ (c.foldMinus v))).weight := by
  apply LinearMap.ext
  intro F
  change (∑ x, halfMarginalMinus c (signedIntegral (emit lam σ).weight) x * F (c.join x x)) =
    (emit lam (fun v => σ (c.foldMinus v))).expect F
  rw [expect_emit]
  have hm : ∀ x, halfMarginalMinus c (signedIntegral (emit lam σ).weight) x =
      lam.expect (fun y => if (fun v : c.Half => y (σ (c.flip v.1))) = x then 1 else 0) := by
    intro x
    unfold halfMarginalMinus
    rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    rfl
  simp only [hm]
  unfold FiniteLaw.expect
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [Finset.sum_eq_single (fun v : c.Half => y (σ (c.flip v.1)))]
  · simp only [↓reduceIte, mul_one]
    congr 2
    funext v
    unfold ReflectionCut.join ReflectionCut.foldMinus
    by_cases hv : v ∈ c.half
    · simp [hv]
    · simp [hv, c.flip_flip]
  · intro x _ hx
    simp only [Ne.symm hx, ↓reduceIte, mul_zero, zero_mul]
  · intro h
    exact absurd (mem_univ _) h

end Fold

/-! ## The rows of the folded laws -/

section FoldRows

variable {p : ℕ} [Fact p.Prime]

/-- A graph law emitted to the 72 slots along any emission that reads two distinct vertices at
`≥ t` slots each has unit mixed `L^{72 − t/2}` (M1's `emit_mixed_of_two_labels`). -/
theorem graphLaw_two_labels (hp2 : p ≠ 2) (hp64 : (64 : ℝ) ≤ p) {W : Type} [Fintype W]
    [DecidableEq W] (G : OrientedGraph W) (hne : (injLabellings (ZMod p) G).Nonempty)
    (π : Slot → W) {i j : W} (hij : i ≠ j) {t : ℕ} (ht : 0 < t)
    (hti : t ≤ (univ.filter (fun v => π v = i)).card)
    (htj : t ≤ (univ.filter (fun v => π v = j)).card) :
    MixedLpBound (emit (graphLaw G hne) π) ((72 : ℝ) - t / 2) 1 := by
  have h := emit_mixed_of_two_labels hp2 hp64 (graphLaw G hne) π hij ht hti htj
    (fun w hw => graphLaw_pair_dist G hne hij w hw)
    (fun s u hs hsq w => graphLaw_pair_affine G hne _ _ s u hs hsq w)
    (fun l f => PartV.graphLaw_vertex_uniform G hne l f)
  rw [card_slot] at h
  push_cast at h
  exact h

/-- The folded matching emissions at the tag cut read two objects at `48` and `24` slots. -/
theorem foldPlus_counts (s : Fin 2) :
    24 ≤ (univ.filter (fun v : Slot =>
        midDiagEmission (Labellings.matching s) ((tagCut s).foldPlus v) = (1, 0))).card ∧
      24 ≤ (univ.filter (fun v : Slot =>
        midDiagEmission (Labellings.matching s) ((tagCut s).foldPlus v) = (2, 0))).card := by
  fin_cases s <;> decide

theorem foldMinus_counts (s : Fin 2) :
    24 ≤ (univ.filter (fun v : Slot =>
        midDiagEmission (Labellings.matching s) ((tagCut s).foldMinus v) = (0, 0))).card ∧
      24 ≤ (univ.filter (fun v : Slot =>
        midDiagEmission (Labellings.matching s) ((tagCut s).foldMinus v) = (2, 0))).card := by
  fin_cases s <;> decide

end FoldRows

section Middle

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The sharp bound of A1's explicit witness** (`lem:record:one-stage-folded-e`(e)): the
difference `plusRec s − matchRec s` is sharp at `tagCut s` with constant `k_new(X) b^{-1/2}`
relative to the half marginals of `matchRec s` itself. This is the body of A1's
`blockSharp_of_block`, which only states the existential `BlockSharp`; the proof is A1's. -/
theorem matchRec_sharp (h : ClassThreeBlock pr) (hne : MiddleNonempty pr) {X b : ℝ}
    (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b) (hbp : ∀ i, b ≤ (pr i : ℝ)) (s : Fin 2) :
    Sharp (tagCut s) (plusRec pr h s - matchRec pr hne s)
      (halfMarginalPlus (tagCut s) (matchRec pr hne s))
      (halfMarginalMinus (tagCut s) (matchRec pr hne s)) (blockConst X b) := by
  intro F G
  set fC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => F (hpF s (fun i => (a i).1) c) with hfC
  set gC : ∀ c : BlockLabel pr, (∀ i, Vc (c i)) → ℝ :=
    fun c a => G (hmF s (fun i => (a i).1) c) with hgC
  have hform : (tagCut s).form (plusRec pr h s - matchRec pr hne s) F G =
      kappaN pr * ∑ c : BlockLabel pr, gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c) := by
    have hsub : (tagCut s).form (plusRec pr h s - matchRec pr hne s) F G =
        (tagCut s).form (plusRec pr h s) F G - (tagCut s).form (matchRec pr hne s) F G := rfl
    rw [hsub, plusRec, matchRec, form_emit, form_emit]
    simp only [emit_plus_half, emit_minus_half]
    have e1 := blockPlus_expect pr h (fun a0 a1 c => F (hpF s a1 c) * G (hmF s a0 c))
    have e2 := blockMatch_expect pr hne (fun a0 a1 c => F (hpF s a1 c) * G (hmF s a0 c))
    rw [sum3_comm] at e1 e2
    rw [e1, e2, ← sum_sub_distrib, mul_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [← sum_pair_diff pr c (fun a1 => F (hpF s a1 c)) (fun a0 => G (hmF s a0 c)),
      ← sum_sub_distrib]
    refine sum_congr rfl fun a0 _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun a1 _ => ?_
    ring
  have hmp : ∑ x, halfMarginalPlus (tagCut s) (matchRec pr hne s) x * F x ^ 2 =
      kappaN pr * ∑ c : BlockLabel pr, fC c ⬝ᵥ fC c := by
    rw [sum_halfPlus, matchRec, ← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    simp only [Function.comp_apply, emit_plus_half]
    have e2 := blockMatch_expect pr hne (fun _ a1 c => F (hpF s a1 c) ^ 2)
    rw [e2, sum3_comm, mul_sum]
    exact sum_congr rfl fun c _ => sum_sq_one pr h c (fun a1 => F (hpF s a1 c))
  have hmm : ∑ y, halfMarginalMinus (tagCut s) (matchRec pr hne s) y * G y ^ 2 =
      kappaN pr * ∑ c : BlockLabel pr, gC c ⬝ᵥ gC c := by
    rw [sum_halfMinus, matchRec, ← FiniteLaw.expect_eq_signedIntegral, expect_emit]
    simp only [Function.comp_apply, emit_minus_half]
    have e2 := blockMatch_expect pr hne (fun a0 _ c => G (hmF s a0 c) ^ 2)
    rw [e2, sum3_comm, mul_sum]
    exact sum_congr rfl fun c _ => sum_sq_zero pr h c (fun a0 => G (hmF s a0 c))
  rw [hform, hmp, hmm]
  have hκ := kappaN_nonneg pr
  have hD : 0 ≤ blockConst X b := by
    have hX0 : 0 < X := by linarith
    unfold blockConst
    exact mul_nonneg (le_trans zero_le_one (one_le_knew (by positivity)
      (by rw [div_le_div_iff₀ hX0 (by norm_num)]; linarith) (by positivity))) (by positivity)
  have hterm : ∀ c, |gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)| ≤
      blockConst X b * Real.sqrt (gC c ⬝ᵥ gC c) * Real.sqrt (fC c ⬝ᵥ fC c) :=
    fun c => block_delta_form_le pr h hX hXb hbp c (gC c) (fC c)
  have hff : ∀ c, 0 ≤ fC c ⬝ᵥ fC c := fun c => Sarkozy.IndexSupport.dotProduct_self_nonneg _
  have hgg : ∀ c, 0 ≤ gC c ⬝ᵥ gC c := fun c => Sarkozy.IndexSupport.dotProduct_self_nonneg _
  calc |kappaN pr * ∑ c, gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)|
      = kappaN pr * |∑ c, gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)| := by
        rw [abs_mul, abs_of_nonneg hκ]
    _ ≤ kappaN pr * ∑ c, |gC c ⬝ᵥ ((blockKp pr c - blockK0 pr c) *ᵥ fC c)| :=
        mul_le_mul_of_nonneg_left (abs_sum_le_sum_abs _ _) hκ
    _ ≤ kappaN pr * ∑ c, blockConst X b * Real.sqrt (gC c ⬝ᵥ gC c) *
          Real.sqrt (fC c ⬝ᵥ fC c) :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun c _ => hterm c) hκ
    _ = blockConst X b * (kappaN pr * ∑ c, Real.sqrt (fC c ⬝ᵥ fC c) *
          Real.sqrt (gC c ⬝ᵥ gC c)) := by
        rw [mul_sum, mul_sum, mul_sum]
        refine sum_congr rfl fun c _ => ?_
        ring
    _ ≤ blockConst X b * (kappaN pr * (Real.sqrt (∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (∑ c, gC c ⬝ᵥ gC c))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (sum_sqrt_mul_le univ _ _ hff hgg) hκ) hD
    _ = blockConst X b * Real.sqrt (kappaN pr * ∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (kappaN pr * ∑ c, gC c ⬝ᵥ gC c) := by
        rw [Real.sqrt_mul hκ, Real.sqrt_mul hκ]
        have hs : Real.sqrt (kappaN pr) * Real.sqrt (kappaN pr) = kappaN pr :=
          Real.mul_self_sqrt hκ
        linear_combination (-(blockConst X b * Real.sqrt (∑ c, fC c ⬝ᵥ fC c) *
          Real.sqrt (∑ c, gC c ⬝ᵥ gC c))) * hs

variable (h64 : ∀ i, (64 : ℝ) ≤ pr i)

include h64 in
/-- The plus full folded law of the folded matching record has unit mixed `L^{60}` on the block. -/
theorem block_fold_plus (hp2 : ∀ i, pr i ≠ 2) (hne : MiddleNonempty pr) (s : Fin 2) :
    MixedLpBound (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
      (fun v => midDiagEmission (Labellings.matching s) ((tagCut s).foldPlus v))) 60 1 := by
  have h := mixedLpBound_emit_tensor (fun i => graphLaw (matchGraph (Fin 1)) (hne.E1 i))
    (fun v => midDiagEmission (Labellings.matching s) ((tagCut s).foldPlus v))
    (by norm_num : (0 : ℝ) < 72 - ((24 : ℕ) : ℝ) / 2)
    (fun i => graphLaw_two_labels (hp2 i) (h64 i) _ (hne.E1 i) _ (i := (1, 0)) (j := (2, 0))
      (by decide) (by norm_num) (foldPlus_counts s).1 (foldPlus_counts s).2)
  norm_num at h
  exact h

include h64 in
/-- The minus full folded law of the folded matching record has unit mixed `L^{60}` on the
block. -/
theorem block_fold_minus (hp2 : ∀ i, pr i ≠ 2) (hne : MiddleNonempty pr) (s : Fin 2) :
    MixedLpBound (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
      (fun v => midDiagEmission (Labellings.matching s) ((tagCut s).foldMinus v))) 60 1 := by
  have h := mixedLpBound_emit_tensor (fun i => graphLaw (matchGraph (Fin 1)) (hne.E1 i))
    (fun v => midDiagEmission (Labellings.matching s) ((tagCut s).foldMinus v))
    (by norm_num : (0 : ℝ) < 72 - ((24 : ℕ) : ℝ) / 2)
    (fun i => graphLaw_two_labels (hp2 i) (h64 i) _ (hne.E1 i) _ (i := (0, 0)) (j := (2, 0))
      (by decide) (by norm_num) (foldMinus_counts s).1 (foldMinus_counts s).2)
  norm_num at h
  exact h

end Middle

/-! ## The sharp-fold data -/

/-- The one-point probability law. -/
noncomputable def unitLaw : FiniteLaw Unit where
  weight _ := 1
  nonneg _ := zero_le_one
  total := by simp

section Assemble

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem dec_unit (c : ℝ) (K : SlotMeasure X) (hK : mass K = 1) :
    c • K = mass (c • K) • ∑ u : Unit, unitLaw.weight u • K := by
  have hm : mass (c • K) = c := by
    change c * mass K = c
    rw [hK, mul_one]
  rw [hm, Fintype.sum_unique]
  change c • K = c • ((1 : ℝ) • K)
  rw [one_smul]

omit [DecidableEq X] in
theorem dec_unit_sub (c : ℝ) (K P : SlotMeasure X) (hK : mass K = 1) :
    c • P - c • K = mass (c • K) • ∑ u : Unit, unitLaw.weight u • (P - K) := by
  have hm : mass (c • K) = c := by
    change c * mass K = c
    rw [hK, mul_one]
  rw [hm, Fintype.sum_unique]
  change c • P - c • K = c • ((1 : ℝ) • (P - K))
  rw [one_smul, smul_sub]

end Assemble

section MiddleData

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h64 : ∀ i, (64 : ℝ) ≤ pr i)
  (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ) (h : ClassThreeBlock pr)

include h64 in
/-- **The sharp folds of a middle block** (`lem:density:middle-catalog`, "the additional first-stage
matching law … its own private sharp fold has the actual uniform ordered-distinct pair, with
multiplicities `8, 4`"): A1's decomposition, with the folded laws of unit mixed `L^{60}`, hence
`L^{72/θ}` for `θ ≤ 6/5`. -/
noncomputable def middleRemaining_proved {X b : ℝ} (hX : 2 ^ 24 ≤ X) (hXb : X ≤ b)
    (hbp : ∀ i, b ≤ (pr i : ℝ)) {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11) :
    MiddleRemaining pr hne root W I hr bmin h (blockConst X b) θ := fun s =>
  have hp2 : ∀ i, pr i ≠ 2 := fun i => by have := h.mod4 i; omega
  have h60 : (60 : ℝ) ≤ 72 / θ := by
    rw [le_div_iff₀ hθ]
    linarith
  { S := Unit
    π := unitLaw
    κs := fun _ => matchRec pr hne s
    Ks := fun _ => plusRec pr h s - matchRec pr hne s
    prob := fun _ => ⟨isNonneg_law _, mass_law _⟩
    dec_κ := by
      rw [middle_oldRec]
      exact dec_unit _ _ (mass_law _)
    dec_ζ := by
      rw [middle_oldRec, middle_newRecN]
      exact dec_unit_sub _ _ _ (mass_law _)
    sharp := fun _ => matchRec_sharp pr h hne hX hXb hbp s
    lp := emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
      (fun v => midDiagEmission (Labellings.matching s) ((tagCut s).foldPlus v))
    lm := emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
      (fun v => midDiagEmission (Labellings.matching s) ((tagCut s).foldMinus v))
    hlp := fun x => by
      unfold foldedLawPlus
      rw [Fintype.sum_unique]
      change 1 * lawDensity ((tagCut s).diagonalLaw (halfMarginalPlus (tagCut s)
        (signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
          (midDiagEmission (Labellings.matching s))).weight))) x = _
      rw [diagonalLaw_halfMarginalPlus_emit, Structured.lawDensity_signedIntegral_eq, one_mul]
    hlm := fun x => by
      unfold foldedLawMinus
      rw [Fintype.sum_unique]
      change 1 * lawDensity ((tagCut s).diagonalLaw (halfMarginalMinus (tagCut s)
        (signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
          (midDiagEmission (Labellings.matching s))).weight))) x = _
      rw [diagonalLaw_halfMarginalMinus_emit, Structured.lawDensity_signedIntegral_eq, one_mul]
    mp := MixedLpBound.mono_exponent (block_fold_plus pr h64 hp2 hne s) zero_le_one
      (by norm_num) h60
    mm := MixedLpBound.mono_exponent (block_fold_minus pr h64 hp2 hne s) zero_le_one
      (by norm_num) h60 }

end MiddleData

/-! ## The paper's blocks: `MB` proved -/

section Paper

open Sarkozy.CancellationSteps Sarkozy.PartVLaws

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **The remaining per-block input, proved for every class-three block of the paper**, at every
`0 < θ ≤ 12/11`. -/
noncomputable def specRemaining_proved (In : FirstStageInputs blockOf) {θ : ℝ} (hθ : 0 < θ)
    (hθ' : θ ≤ 12 / 11) {b : B} : (S : PaperBlockSpec blockOf b) → SpecRemaining blockOf In θ S
  | .upper _ => PUnit.unit
  | .middleUniform M => middleRemaining_proved (blockPrimes blockOf b) (paper_blockPrimes_ge64 b)
      M.hne _ M.W M.I M.hr (In.bmin b) (classThree_blockPrimes b) (In.hX b) (In.hXb b) (In.hbp b)
      hθ hθ'
  | .middleIndividual M => middleRemaining_proved (blockPrimes blockOf b)
      (paper_blockPrimes_ge64 b) M.hne _ M.W M.I M.hr (In.bmin b) (classThree_blockPrimes b)
      (In.hX b) (In.hXb b) (In.hbp b) hθ hθ'
  | .middleCoherent M => middleRemaining_proved (blockPrimes blockOf b)
      (paper_blockPrimes_ge64 b) M.hne _ M.W M.I M.hr (In.bmin b) (classThree_blockPrimes b)
      (In.hX b) (In.hXb b) (In.hbp b) hθ hθ'

/-- **The per-block moment inputs of the paper's first stage, proved** (`lem:density:middle-catalog`
with M1's rows): for every class-three block, every `0 < θ ≤ 12/11`. -/
noncomputable def paperStageMoments_proved (hW : Target.Weil) (In : FirstStageInputs blockOf)
    {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ 12 / 11) (spec : ∀ b, PaperBlockSpec blockOf b) (b : B) :
    AtomStageMoments (specStage hW In (spec b)) θ :=
  specStageMoments hW In hθ hθ' (spec b) (specRemaining_proved In hθ hθ' (spec b))

end Paper

end Sarkozy.EnvelopeEnergiesPaper

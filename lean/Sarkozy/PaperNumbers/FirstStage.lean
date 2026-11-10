module

public import Sarkozy.PaperNumbers.Main

@[expose] public section

/-!
# The first-stage sums of the paper's construction by piece (`lem:record:middle-prices`)

`paper/sections/20c_middle_frame.tex`, `lem:record:middle-prices`.

A1's `hL₀_of_prices` and A2's `hB_of_charges` take the first-stage sums over the atoms: the
variation prices `∑_β p_β ≤ P'` and the tag sums `∑_β d_{β,j} ≤ d'_j`, `∑_β v_{β,j} ≤ v'_j`. The
square-clique atoms and the upper blocks carry the trivial first stage (all prices `0`), and a
middle block of piece `i` has (A1's `middleStage_pvar`, `_dTag`, `_vTag`, with the frame
normalization `P(r) ≥ 1` dropped, `one_le_midPoly`)
* `p_𝔅 ≤ (4 v_D r² + 2 |f₁ + h₁| v_D r³) q_𝔅^{2a}`;
* `d_{𝔅,j} ≤ (v_S + v_D) r² · k_new(X_i) b_𝔅^{-1/2} · q_𝔅^{2a}`
  `= (v_S + v_D) k_new(X_i) r³ q_𝔅^{2a}`;
* `v_{𝔅,j} ≤ 2 (v_S + v_D) r² q_𝔅^{2a}`,

with `r = b_𝔅^{-1/2}` and the ALLp weights and inputs of the piece. Summed by piece
(**`sum_pvar_le`**, **`sum_dTag_le`**, **`sum_vTag_le`**) these are linear in the block charges
`b₂(i)`, `b₃(i)`. With `b_d(i) ≤ c_d(i)` (`blockCharge_le_pieceBound`), all three first-stage sums,
hence `hB` and `hL₀`, depend only on the 66 numbers `c_d(i)`
(**`main_target_paper_joint_N1_numbers`**).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.PaperNumbers

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper
  Sarkozy.BlockSpecPaper Sarkozy.MainTarget Sarkozy.PartVRecords Sarkozy.TheoremC
  Sarkozy.RecordExpansion Sarkozy.JointClosing
open Sarkozy.TargetLedger (targetDecay targetLedger)

/-- B1's block scale `r = b_𝔅^{-1/2}`. -/
local notation "rB" => BlockSpecPaper.blockScale

/-! ## A middle block -/

section Middle

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (bmin : ℝ) (h : ClassThreeBlock pr)
  (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
  {d : ℝ} (hd : 0 ≤ d) (hs : BlockSharp pr hne h d)

theorem frameP_inv (hr : 0 ≤ r) :
    0 ≤ (middleFrame pr hne root W I hr bmin h).P⁻¹ ∧
      (middleFrame pr hne root W I hr bmin h).P⁻¹ ≤ 1 := by
  have hP : 1 ≤ (middleFrame pr hne root W I hr bmin h).P := one_le_midPoly W hr
  exact ⟨inv_nonneg.mpr (by linarith), inv_le_one_of_one_le₀ hP⟩

/-- `p_𝔅 ≤ (4 v_D r² + 2 |f₁ + h₁| v_D r³) sel` (`lem:record:middle-prices`, `P(r) ≥ 1`). -/
theorem middleStage_pvar_le {sel : ℝ} (hsel : 0 ≤ sel) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).pvar sel ≤
      (4 * W.v .D * r ^ 2 + 2 * |I.f₁ + I.h₁| * W.v .D * r ^ 3) * sel := by
  rw [middleStage_pvar]
  obtain ⟨hP0, hP1⟩ := frameP_inv pr hne root W I bmin h hr
  have hvD := W.v_nonneg .D
  unfold coefD coefG
  simp only [abs_mul, abs_of_nonneg hP0, abs_of_nonneg hr, abs_of_nonneg hvD,
    abs_of_nonneg (pow_nonneg hr 2)]
  apply mul_le_mul_of_nonneg_right _ hsel
  have hX : 0 ≤ 4 * W.v .D * r ^ 2 + 2 * |I.f₁ + I.h₁| * W.v .D * r ^ 3 := by positivity
  calc _ = (middleFrame pr hne root W I hr bmin h).P⁻¹ *
          (4 * W.v .D * r ^ 2 + 2 * |I.f₁ + I.h₁| * W.v .D * r ^ 3) := by ring
    _ ≤ 1 * (4 * W.v .D * r ^ 2 + 2 * |I.f₁ + I.h₁| * W.v .D * r ^ 3) :=
        mul_le_mul_of_nonneg_right hP1 hX
    _ = _ := one_mul _

/-- `d_{𝔅,j} ≤ (v_S + v_D) r² d sel` (`lem:record:middle-prices`, `P(r) ≥ 1`). -/
theorem middleStage_dTag_le {sel : ℝ} (hsel : 0 ≤ sel) (j : Fin 2) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).dTag sel j ≤
      (W.v .S + W.v .D) * r ^ 2 * d * sel := by
  rw [middleStage_dTag]
  obtain ⟨hP0, hP1⟩ := frameP_inv pr hne root W I bmin h hr
  have hX : 0 ≤ (W.v .S + W.v .D) * r ^ 2 * d * sel := by
    have := W.v_nonneg .S
    have := W.v_nonneg .D
    positivity
  calc (middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2) * d * sel
      = (middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2 * d * sel) := by
        ring
    _ ≤ 1 * ((W.v .S + W.v .D) * r ^ 2 * d * sel) := mul_le_mul_of_nonneg_right hP1 hX
    _ = _ := one_mul _

/-- `v_{𝔅,j} ≤ 2 (v_S + v_D) r² sel` (`lem:record:middle-prices`, `P(r) ≥ 1`). -/
theorem middleStage_vTag_le {sel : ℝ} (hsel : 0 ≤ sel) (j : Fin 2) :
    (middleStage pr hne root W I hr bmin h hrows₁ hd hs).vTag sel j ≤
      2 * ((W.v .S + W.v .D) * r ^ 2) * sel := by
  rw [middleStage_vTag]
  obtain ⟨hP0, hP1⟩ := frameP_inv pr hne root W I bmin h hr
  have hX : 0 ≤ 2 * ((W.v .S + W.v .D) * r ^ 2) * sel := by
    have := W.v_nonneg .S
    have := W.v_nonneg .D
    positivity
  calc 2 * ((middleFrame pr hne root W I hr bmin h).P⁻¹ * ((W.v .S + W.v .D) * r ^ 2)) * sel
      = (middleFrame pr hne root W I hr bmin h).P⁻¹ * (2 * ((W.v .S + W.v .D) * r ^ 2) * sel) := by
        ring
    _ ≤ 1 * (2 * ((W.v .S + W.v .D) * r ^ 2) * sel) := mul_le_mul_of_nonneg_right hP1 hX
    _ = _ := one_mul _

end Middle

/-! ## The coefficients of a piece -/

/-- `4 v_D` (the degree-2 coefficient of `p_𝔅`). -/
noncomputable def fsP2 (i : Fin 33) : ℝ := 4 * (allpWeights i).v .D

/-- `2 |f₁ + h₁| v_D` (the degree-3 coefficient of `p_𝔅`). -/
noncomputable def fsP3 (i : Fin 33) : ℝ :=
  2 * |(allpInputs i).f₁ + (allpInputs i).h₁| * (allpWeights i).v .D

/-- `(v_S + v_D) k_new(X_i)` (the degree-3 coefficient of `d_{𝔅,j}`). -/
noncomputable def fsD3 (i : Fin 33) : ℝ :=
  ((allpWeights i).v .S + (allpWeights i).v .D) *
    PartVRecords.knew (1 / (pieceStart i : ℝ)) (1 / Real.sqrt (pieceStart i : ℝ))

/-- `2 (v_S + v_D)` (the degree-2 coefficient of `v_{𝔅,j}`). -/
noncomputable def fsV2 (i : Fin 33) : ℝ := 2 * ((allpWeights i).v .S + (allpWeights i).v .D)

variable {cell : ℕ → ℕ}

/-- `r² · k_new(X) b^{-1/2} = k_new(X) r³` for `r = b^{-1/2}`. -/
theorem blockConst_scale (b : PaperBlock cell) (X : ℝ) :
    rB b ^ 2 * blockConst X (blockLeast b) =
      PartVRecords.knew (1 / X) (1 / Real.sqrt X) * rB b ^ 3 := by
  unfold blockConst
  have h : 1 / Real.sqrt (blockLeast b : ℝ) = rB b := by
    unfold BlockSpecPaper.blockScale
    rw [Real.sqrt_eq_rpow, Real.rpow_neg (blockLeast_pos b).le, one_div]
  rw [h]
  ring

theorem paperIn_X {b : PaperBlock cell} {i : Fin 33} (hs : blockSite b = .inl i) :
    (paperIn cell).X b = pieceStart i := by
  change ((siteStart (blockSite b) : ℕ) : ℝ) = _
  rw [hs]
  rfl

/-- The first-stage bounds of a block at its site: `(α r² + β r³) sel` on piece `i`, `0` on a
band. -/
noncomputable def siteLin (α β : Fin 33 → ℝ) (b : PaperBlock cell) (x : ℝ) : Site → ℝ
  | .inl i => (α i * rB b ^ 2 + β i * rB b ^ 3) * x
  | .inr _ => 0

/-- **Grouping by piece** (as B1's `sum_paperSpec_ubound`). -/
theorem sum_siteLin (α β : Fin 33 → ℝ) (f : PaperBlock cell → ℝ) :
    ∑ b, siteLin α β b (f b) (blockSite b) =
      ∑ i : Fin 33, (α i * blockCharge f 2 i + β i * blockCharge f 3 i) := by
  have hb : ∀ b : PaperBlock cell, siteLin α β b (f b) (blockSite b) = ∑ i : Fin 33,
      if blockSite b = .inl i then
        (α i * rB b ^ 2 + β i * rB b ^ 3) * f b else 0 := by
    intro b
    rcases h : blockSite b with i | k
    · simp only [siteLin, Sum.inl.injEq]
      rw [Finset.sum_ite_eq]
      simp
    · simp [siteLin]
  simp_rw [hb]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_filter]
  unfold blockCharge
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun b _ => ?_
  ring

/-! ## A block of the construction -/

theorem trivial_prices {X : Type} [Fintype X] [DecidableEq X] (μ : SlotMeasure X)
    (cut : Fin 2 → ReflectionCut Slot) (ϑ₀ : ReflectionCut Slot) (sel : ℝ) (j : Fin 2) :
    (AtomStage.trivial μ (Fin 2) cut ϑ₀).pvar sel = 0 ∧
      (AtomStage.trivial μ (Fin 2) cut ϑ₀).dTag sel j = 0 ∧
      (AtomStage.trivial μ (Fin 2) cut ϑ₀).vTag sel j = 0 := by
  refine ⟨Finset.sum_eq_zero fun i _ => i.elim, Finset.sum_eq_zero fun i _ => i.elim,
    Finset.sum_eq_zero fun i _ => i.elim⟩

/-- **The first-stage prices of a middle block of piece `i`** (both roots). -/
theorem middleSpec_stage_le (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (i : Fin 33) (hs : blockSite b = .inl i) {sel : ℝ} (hsel : 0 ≤ sel) :
    ∀ o hu, (specStage hW (paperIn cell) (middleSpec hW A b i hs o hu)).pvar sel ≤
        (fsP2 i * rB b ^ 2 + fsP3 i * rB b ^ 3) * sel ∧
      (∀ j, (specStage hW (paperIn cell) (middleSpec hW A b i hs o hu)).dTag sel j ≤
        (0 * rB b ^ 2 + fsD3 i * rB b ^ 3) * sel) ∧
      (∀ j, (specStage hW (paperIn cell) (middleSpec hW A b i hs o hu)).vTag sel j ≤
        (fsV2 i * rB b ^ 2 + 0 * rB b ^ 3) * sel) := by
  have hX := paperIn_X (cell := cell) hs
  intro o hu
  cases o with
  | none =>
    refine ⟨?_, fun j => ?_, fun j => ?_⟩
    · refine (middleStage_pvar_le _ _ _ _ _ _ _ _
        ((A.uniform b i hs hu).rows₁ (blockNonempty hW b)) _
        ((paperIn cell).sharp b (blockNonempty hW b)) hsel).trans (le_of_eq ?_)
      unfold fsP2 fsP3
      ring
    · refine (middleStage_dTag_le _ _ _ _ _ _ _ _
        ((A.uniform b i hs hu).rows₁ (blockNonempty hW b)) _
        ((paperIn cell).sharp b (blockNonempty hW b)) hsel j).trans (le_of_eq ?_)
      change ((allpWeights i).v .S + (allpWeights i).v .D) * rB b ^ 2 *
        blockConst ((paperIn cell).X b) (blockLeast b) * sel = _
      rw [hX, mul_assoc ((allpWeights i).v .S + (allpWeights i).v .D), blockConst_scale]
      unfold fsD3
      ring
    · refine (middleStage_vTag_le _ _ _ _ _ _ _ _
        ((A.uniform b i hs hu).rows₁ (blockNonempty hW b)) _
        ((paperIn cell).sharp b (blockNonempty hW b)) hsel j).trans (le_of_eq ?_)
      unfold fsV2
      ring
  | some u =>
    refine ⟨?_, fun j => ?_, fun j => ?_⟩
    · refine (middleStage_pvar_le _ _ _ _ _ _ _ _
        ((A.individual b i u hs hu).rows₁ (blockNonempty hW b))
        _ ((paperIn cell).sharp b (blockNonempty hW b)) hsel).trans (le_of_eq ?_)
      unfold fsP2 fsP3
      ring
    · refine (middleStage_dTag_le _ _ _ _ _ _ _ _
        ((A.individual b i u hs hu).rows₁ (blockNonempty hW b))
        _ ((paperIn cell).sharp b (blockNonempty hW b)) hsel j).trans (le_of_eq ?_)
      change ((allpWeights i).v .S + (allpWeights i).v .D) * rB b ^ 2 *
        blockConst ((paperIn cell).X b) (blockLeast b) * sel = _
      rw [hX, mul_assoc ((allpWeights i).v .S + (allpWeights i).v .D), blockConst_scale]
      unfold fsD3
      ring
    · refine (middleStage_vTag_le _ _ _ _ _ _ _ _
        ((A.individual b i u hs hu).rows₁ (blockNonempty hW b))
        _ ((paperIn cell).sharp b (blockNonempty hW b)) hsel j).trans (le_of_eq ?_)
      unfold fsV2
      ring

theorem siteSpec_stage_le (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    {sel : ℝ} (hsel : 0 ≤ sel) :
    ∀ s (hs : blockSite b = s),
      (specStage hW (paperIn cell) (siteSpec hW A b s hs)).pvar sel ≤ siteLin fsP2 fsP3 b sel s ∧
      (∀ j, (specStage hW (paperIn cell) (siteSpec hW A b s hs)).dTag sel j ≤
        siteLin (fun _ => 0) fsD3 b sel s) ∧
      (∀ j, (specStage hW (paperIn cell) (siteSpec hW A b s hs)).vTag sel j ≤
        siteLin fsV2 (fun _ => 0) b sel s)
  | .inl i, hs => middleSpec_stage_le hW A b i hs hsel _ rfl
  | .inr _, _ => ⟨(trivial_prices _ _ _ sel 0).1.le, fun j => (trivial_prices _ _ _ sel j).2.1.le,
      fun j => (trivial_prices _ _ _ sel j).2.2.le⟩

/-! ## The sums -/

variable (hW : Target.Weil) (hMR : Target.MovingRoot) (hFour : Target.FourCycle)
  (A : PaperAnalyticInputs cell)

/-- The selection factors of the paper's atoms are nonnegative. -/
theorem paperSel_nonneg (β : PaperAtom (PaperBlock cell)) :
    0 ≤ paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β :=
  zero_le_one.trans (one_le_paperSelAt _ TargetLedger.targetDecay_nonneg β)

/-- **The price sum by piece** (`lem:record:middle-prices`):
`∑_β p_β ≤ ∑_i (4 v_D b₂(i) + 2 |f₁ + h₁| v_D b₃(i))`. -/
theorem sum_pvar_le :
    ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).pvar
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) ≤
    ∑ i : Fin 33, (fsP2 i * blockCharge
        (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 2 i +
      fsP3 i * blockCharge
        (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 3 i) := by
  rw [← sum_siteLin, Fintype.sum_sum_type]
  have h0 : ∀ q, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) (.inl q)).pvar
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inl q)) = 0 :=
    fun q => (trivial_prices _ _ _ _ 0).1
  simp only [h0, Finset.sum_const_zero, zero_add]
  exact sum_le_sum fun b _ =>
    (siteSpec_stage_le hW A b (paperSel_nonneg (.inr b)) _ rfl).1

/-- **The sharp tag sums by piece**: `∑_β d_{β,j} ≤ ∑_i (v_S + v_D) k_new(X_i) b₃(i)`. -/
theorem sum_dTag_le (j : Fin 2) :
    ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).dTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤
    ∑ i : Fin 33, (0 * blockCharge
        (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 2 i +
      fsD3 i * blockCharge
        (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 3 i) := by
  rw [← sum_siteLin, Fintype.sum_sum_type]
  have h0 : ∀ q, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) (.inl q)).dTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inl q)) j = 0 :=
    fun q => (trivial_prices _ _ _ _ j).2.1
  simp only [h0, Finset.sum_const_zero, zero_add]
  exact sum_le_sum fun b _ =>
    (siteSpec_stage_le hW A b (paperSel_nonneg (.inr b)) _ rfl).2.1 j

/-- **The variation tag sums by piece**: `∑_β v_{β,j} ≤ ∑_i 2 (v_S + v_D) b₂(i)`. -/
theorem sum_vTag_le (j : Fin 2) :
    ∑ β, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) β).vTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay β) j ≤
    ∑ i : Fin 33, (fsV2 i * blockCharge
        (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 2 i +
      0 * blockCharge
        (fun b => paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inr b)) 3 i) := by
  rw [← sum_siteLin, Fintype.sum_sum_type]
  have h0 : ∀ q, (paperStage (paperBlockOf cell) hW (paperSpec hW A)
      (TailCorrCore.tailInputsCorr hW hMR hFour) (paperIn cell) (.inl q)).vTag
      (paperSelAt (paperAtomMap (paperBlockOf cell)) targetDecay (.inl q)) j = 0 :=
    fun q => (trivial_prices _ _ _ _ j).2.2
  simp only [h0, Finset.sum_const_zero, zero_add]
  exact sum_le_sum fun b _ =>
    (siteSpec_stage_le hW A b (paperSel_nonneg (.inr b)) _ rfl).2.2 j

/-! ## The first-stage sums from the charges -/

theorem knew_nonneg (i : Fin 33) :
    0 ≤ PartVRecords.knew (1 / (pieceStart i : ℝ)) (1 / Real.sqrt (pieceStart i : ℝ)) := by
  have hX : (2 : ℝ) ^ 24 ≤ pieceStart i := by
    have : 2 ^ 24 ≤ pieceStart i := le_trans (by norm_num [Q3]) (pieceStart_ge_Q3 i)
    exact_mod_cast this
  have h := blockConst_nonneg hX 1
  unfold blockConst at h
  simpa using h

theorem fsP2_nonneg (i : Fin 33) : 0 ≤ fsP2 i :=
  mul_nonneg (by norm_num) ((allpWeights i).v_nonneg _)

theorem fsP3_nonneg (i : Fin 33) : 0 ≤ fsP3 i :=
  mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg _)) ((allpWeights i).v_nonneg _)

theorem fsD3_nonneg (i : Fin 33) : 0 ≤ fsD3 i :=
  mul_nonneg (add_nonneg ((allpWeights i).v_nonneg _) ((allpWeights i).v_nonneg _)) (knew_nonneg i)

theorem fsV2_nonneg (i : Fin 33) : 0 ≤ fsV2 i :=
  mul_nonneg (by norm_num) (add_nonneg ((allpWeights i).v_nonneg _) ((allpWeights i).v_nonneg _))

theorem sum_lin_le {α β c₂ c₃ b₂ b₃ : Fin 33 → ℝ} (hα : ∀ i, 0 ≤ α i) (hβ : ∀ i, 0 ≤ β i)
    (h₂ : ∀ i, b₂ i ≤ c₂ i) (h₃ : ∀ i, b₃ i ≤ c₃ i) :
    ∑ i, (α i * b₂ i + β i * b₃ i) ≤ ∑ i, (α i * c₂ i + β i * c₃ i) :=
  sum_le_sum fun i _ => add_le_add (mul_le_mul_of_nonneg_left (h₂ i) (hα i))
    (mul_le_mul_of_nonneg_left (h₃ i) (hβ i))

/-- **The main statement at the paper's partition with `hB` and `hL₀` from 66 numbers**
(`main_target_paper_joint_N1_prices` with the first-stage sums from `sum_pvar_le`, `sum_dTag_le`,
`sum_vTag_le` and the charges): the per-piece numbers `c₂(i)`, `c₃(i)` with
`pieceBound a_T d i ≤ c_d(i)` (M2's explicit bound for the paper's blocks; *hypotheses*,
numerical) and the two cost inequalities at
`P = ∑_i (4 v_D c₂ + 2 |f₁ + h₁| v_D c₃)`, `D_j = ∑_i (v_S + v_D) k_new(X_i) c₃`,
`V_j = ∑_i 2 (v_S + v_D) c₂` (*hypotheses*, numerical):
`e^{∑ (U₂ c₂ + U₃ c₃)} (1 + 𝔗(D, V)) ≤ B^{ledger}` and `e^P 𝔗(D, V) ≤ L₀^{ledger}`. The other
inputs are the hypotheses H1, H2, H4, H5, `thm:dl:K`, H2″, the lemma families `hU`, `hM`, `hI`,
and the 9 fields `Dv` (`CL`, `ME`, `SM`), `hT`, `hSA`, `JB`, `SF`, `fix`, `env`. -/
theorem main_target_paper_joint_N1_numbers (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (hU : ∀ k, UpperBandLemma k) (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (Dv : N1JointBlockData hWeil hMovingRoot hFourCycle hU hM hI) {c₂ c₃ : Fin 33 → ℝ}
    (h₂ : ∀ i, pieceBound targetDecay 2 i ≤ c₂ i) (h₃ : ∀ i, pieceBound targetDecay 3 i ≤ c₃ i)
    (hcostB : Real.exp (∑ i : Fin 33, (chargeU2 i * c₂ i + chargeU3 i * c₃ i)) *
      (1 + tagSeries (fun _ : Fin 2 => ∑ i, (0 * c₂ i + fsD3 i * c₃ i))
        (fun _ : Fin 2 => ∑ i, (fsV2 i * c₂ i + 0 * c₃ i))) ≤ targetLedger.B)
    (hcostL : TheoremC.firstStageCost (∑ i, (fsP2 i * c₂ i + fsP3 i * c₃ i))
      (fun _ : Fin 2 => ∑ i, (0 * c₂ i + fsD3 i * c₃ i))
      (fun _ : Fin 2 => ∑ i, (fsV2 i * c₂ i + 0 * c₃ i)) ≤ targetLedger.L₀)
    (hT : Dv.toJoint.data.ME.T ≤ targetLedger.T)
    (hSA : Dv.toJoint.data.CL.S + Dv.toJoint.data.CL.A ≤ targetLedger.S + targetLedger.A)
    (JB : JointBound Dv.toJoint.data targetLedger.jointConstant)
    (SF : EnvelopeInputsBlock.SharpFirstInputs Dv.toJoint.data)
    (fix : EnvelopeInputsBlock.FixedIntervalInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data)
    (env : EnvelopeInputsBlock.EnvelopeEnergyInputs
      (BlockAnchor.index_coprime_block Dv.toJoint.data) Dv.toJoint.data) :
    Target.SarkozyBound TargetLedger.targetSaving := by
  have hb₂ : ∀ i, blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf paperCell))
      targetDecay (.inr b)) 2 i ≤ c₂ i := fun i =>
    (blockCharge_le_pieceBound hBMOR i TargetLedger.targetDecay_nonneg (Or.inl rfl)).trans (h₂ i)
  have hb₃ : ∀ i, blockCharge (fun b => paperSelAt (paperAtomMap (paperBlockOf paperCell))
      targetDecay (.inr b)) 3 i ≤ c₃ i := fun i =>
    (blockCharge_le_pieceBound hBMOR i TargetLedger.targetDecay_nonneg
      (Or.inr (Or.inl rfl))).trans (h₃ i)
  exact main_target_paper_joint_N1_prices hWeil hBMOR hMovingRoot hFourCycle
    hThetaSmallRR hU hM hI Dv h₂ h₃
    ((sum_pvar_le hWeil hMovingRoot hFourCycle (paperA hU hM hI)).trans
      (sum_lin_le fsP2_nonneg fsP3_nonneg hb₂ hb₃))
    (fun j => (sum_dTag_le hWeil hMovingRoot hFourCycle (paperA hU hM hI) j).trans
      (sum_lin_le (fun _ => le_refl 0) fsD3_nonneg hb₂ hb₃))
    (fun j => (sum_vTag_le hWeil hMovingRoot hFourCycle (paperA hU hM hI) j).trans
      (sum_lin_le fsV2_nonneg (fun _ => le_refl 0) hb₂ hb₃))
    hcostB hcostL hT hSA JB SF fix env

end Sarkozy.PaperNumbers

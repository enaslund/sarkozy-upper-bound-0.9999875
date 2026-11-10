module

public import Sarkozy.JointRows.RowsC
public import Sarkozy.FiveType.BlocksRP

/-!
# `cor:joint-completion-blocks` without hypotheses from 16_extraction

Sources: `paper/sections/17_completion_repair.tex`, `cor:joint-completion-blocks`;
`paper/sections/16_extraction.tex`, `lem:joint-rows` (b), (c).

The headline theorems of `FiveType/JointBlocks.lean` and `FiveType/BlocksRP.lean` took
`lem:joint-rows` (b), (c) as the hypotheses `Blocks.JointRowsB`, `Blocks.JointRowsC`. These are now
theorems (`jointRowsB_holds`, `jointRowsC_holds`), so the results are restated without them:

* `joint_completion_blocks'`: the joint data of `lem:five-type`(f) on a block, exact marginals of
  `T_E^b`, and `E_T ≤ (2υ + υ²)(e^{n c_F r} - 1)`;
* `blockJointData'`: the joint data themselves;
* `joint_blocks_rp'`: block rows at every `b ∈ supp ν` and the completion inequalities give a
  five-type measure reflection positive at every chamber cut.

The remaining hypotheses are the per-prime inputs of the corollary (norm bounds of `C_{F,p}`,
`C_{E,p}`, the joint block at each prime, which is `lem:joint-rows`(a) or `lem:joint-potential`,
and the block bounds `m_b ∈ [H⁻¹, H]`, `‖U_L - 𝟙‖, ‖U_R - 𝟙‖ ≤ υ`, `E_𝔅 ⪰ -hrI`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]
  [∀ i, DecidableEq (Xp i)]

/-- **`cor:joint-completion-blocks`**, with `lem:joint-rows` (b), (c) proved. -/
theorem joint_completion_blocks' (νp : ∀ i, FiniteLaw (Xp i)) (TEp TFp : ∀ i, Xp i → Xp i → ℝ)
    (rp : ι → ℝ) {r cF cE kJ h H υ mb : ℝ}
    (hTE : ∀ i, ExactMarginals (νp i) (TEp i)) (hTEsymm : ∀ i x y, TEp i x y = TEp i y x)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1)
    (hr : 0 ≤ r) (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ r) (hcF : 0 ≤ cF) (hcE : 0 ≤ cE)
    (hCF : ∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (cF * rp i))
    (hCE : ∀ i, FormBound (νp i) (matchCov (TEp i)) (cE * rp i))
    (hJp : ∀ i, JointBlockLower (νp i) (matchCov (TEp i)) (foldCov (νp i) (TFp i)) (kJ * rp i))
    (hcFr : cF * r < 1) (hcEr : cE * r < 1) (hkJ : (cF ^ 2 + cE ^ 2) * r ≤ kJ)
    (hm0 : H⁻¹ ≤ mb) (hm1 : mb ≤ H)
    (hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ)
    (hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ)
    (hEB : ∀ Φ, -(h * r) * nrm (blockLaw νp) Φ ^ 2 ≤ kf (blockLaw νp) (EB TEp) Φ Φ) :
    ExactMarginals (blockLaw νp) (prodKernel TEp) ∧
    (∃ J : JointData (blockLaw νp) (prodKernel TEp) (fun x y => mb * prodKernel TFp x y) H υ
        (ET υ cF rp) (h * r) (kJ * r),
      J.m = mb ∧ J.φ0 = UL νp TFp ∧ J.φ2 = UR νp TFp ∧ J.C = CB νp TFp ∧ J.R = RB νp TFp) ∧
    ∀ n : ℕ, Fintype.card ι ≤ n → ET υ cF rp ≤ (2 * υ + υ ^ 2) * (Real.exp (n * cF * r) - 1) :=
  joint_completion_blocks νp TEp TFp rp hTE hTEsymm hTF hr hrp hcF hcE hCF hCE hJp hcFr hcEr hkJ
    hm0 hm1 hUL hUR hEB (jointRowsB_holds νp _ _) (jointRowsC_holds νp TFp)

/-- **The joint data of `lem:five-type`(f) on a block**, with `lem:joint-rows` (b), (c) proved. -/
noncomputable def blockJointData' (νp : ∀ i, FiniteLaw (Xp i)) (TEp TFp : ∀ i, Xp i → Xp i → ℝ)
    (rp : ι → ℝ) {r cF cE kJ h H υ mb : ℝ}
    (hTE : ∀ i, ExactMarginals (νp i) (TEp i)) (hTEsymm : ∀ i x y, TEp i x y = TEp i y x)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1)
    (hr : 0 ≤ r) (hrp : ∀ i, rp i ≤ r) (hcF : 0 ≤ cF) (hcE : 0 ≤ cE)
    (hCF : ∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (cF * rp i))
    (hCE : ∀ i, FormBound (νp i) (matchCov (TEp i)) (cE * rp i))
    (hJp : ∀ i, JointBlockLower (νp i) (matchCov (TEp i)) (foldCov (νp i) (TFp i)) (kJ * rp i))
    (hcFr : cF * r < 1) (hcEr : cE * r < 1) (hkJ : (cF ^ 2 + cE ^ 2) * r ≤ kJ)
    (hm0 : H⁻¹ ≤ mb) (hm1 : mb ≤ H)
    (hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ)
    (hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ)
    (hEB : ∀ Φ, -(h * r) * nrm (blockLaw νp) Φ ^ 2 ≤ kf (blockLaw νp) (EB TEp) Φ Φ) :
    JointData (blockLaw νp) (prodKernel TEp) (fun x y => mb * prodKernel TFp x y) H υ
      (ET υ cF rp) (h * r) (kJ * r) :=
  blockJointData νp TEp TFp rp hTE hTEsymm hTF hr hrp hcF hcE hCF hCE hJp hcFr hcEr hkJ hm0 hm1
    hUL hUR hEB (jointRowsB_holds νp _ _) (jointRowsC_holds νp TFp)

/-- **Block rows give a reflection positive completion** (`cor:joint-completion-blocks` with
`lem:five-type`(f), graded form), with `lem:joint-rows` (b), (c) proved. -/
theorem joint_blocks_rp' (D : Datum ((i : ι) → Xp i))
    (νp : ((i : ι) → Xp i) → ∀ i, FiniteLaw (Xp i))
    (TEp TFp : ((i : ι) → Xp i) → ∀ i, Xp i → Xp i → ℝ) (mb : ((i : ι) → Xp i) → ℝ)
    (rp : ι → ℝ) {r cF cE kJ h H υ εT tY d M f : ℝ} {w : Ty → ℝ}
    (hnub : ∀ b, D.nu.weight b ≠ 0 → D.nub b = blockLaw (νp b))
    (hTEb : ∀ b, D.nu.weight b ≠ 0 → D.TE b = prodKernel (TEp b))
    (hTFb : ∀ b, D.nu.weight b ≠ 0 → D.TF b = fun x y => mb b * prodKernel (TFp b) x y)
    (hTE : ∀ b, D.nu.weight b ≠ 0 → ∀ i, ExactMarginals (νp b i) (TEp b i))
    (hTEsymm : ∀ b, D.nu.weight b ≠ 0 → ∀ i x y, TEp b i x y = TEp b i y x)
    (hTF : ∀ b, D.nu.weight b ≠ 0 → ∀ i,
      kf (νp b i) (TFp b i) (fun _ => 1) (fun _ => 1) = 1)
    (hr : 0 < r) (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ r) (hcF : 0 ≤ cF) (hcE : 0 ≤ cE)
    (hCF : ∀ b, D.nu.weight b ≠ 0 → ∀ i,
      FormBound (νp b i) (foldCov (νp b i) (TFp b i)) (cF * rp i))
    (hCE : ∀ b, D.nu.weight b ≠ 0 → ∀ i, FormBound (νp b i) (matchCov (TEp b i)) (cE * rp i))
    (hJp : ∀ b, D.nu.weight b ≠ 0 → ∀ i,
      JointBlockLower (νp b i) (matchCov (TEp b i)) (foldCov (νp b i) (TFp b i)) (kJ * rp i))
    (hcFr : cF * r < 1) (hcEr : cE * r < 1) (hkJ : (cF ^ 2 + cE ^ 2) * r ≤ kJ)
    (hm0 : ∀ b, D.nu.weight b ≠ 0 → H⁻¹ ≤ mb b) (hm1 : ∀ b, D.nu.weight b ≠ 0 → mb b ≤ H)
    (hUL : ∀ b, D.nu.weight b ≠ 0 →
      nrm (blockLaw (νp b)) (fun x => UL (νp b) (TFp b) x - 1) ≤ υ)
    (hUR : ∀ b, D.nu.weight b ≠ 0 →
      nrm (blockLaw (νp b)) (fun x => UR (νp b) (TFp b) x - 1) ≤ υ)
    (hEB : ∀ b, D.nu.weight b ≠ 0 → ∀ Φ,
      -(h * r) * nrm (blockLaw (νp b)) Φ ^ 2 ≤ kf (blockLaw (νp b)) (EB (TEp b)) Φ Φ)
    (hET : ET υ cF rp ≤ εT) (hεT : 0 ≤ εT) (hh : 0 ≤ h)
    (hw : ∀ t, 0 ≤ w t) (hwD : 0 < w .D) (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hM : H + tY ≤ M)
    (hf : fJ H kJ h r εT tY υ ≤ f) (h2 : M * w .D ≤ w .S) (h3 : f * w .D + h * w .S ≤ w .R)
    (h4 : w .R ^ 2 ≤ w .C * w .S)
    (hroot : w .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧ d * w .L ≤ w .D)) :
    RPAll (D.Q (graded w r)) :=
  D.joint_blocks_rp νp TEp TFp mb rp hnub hTEb hTFb hTE hTEsymm hTF hr hrp hcF hcE hCF hCE hJp
    hcFr hcEr hkJ hm0 hm1 hUL hUR hEB (fun b _ => jointRowsB_holds (νp b) _ _)
    (fun b _ => jointRowsC_holds (νp b) (TFp b)) hET hεT hh hw hwD htY htH hM hf h2 h3 h4 hroot

end Sarkozy.JointRows

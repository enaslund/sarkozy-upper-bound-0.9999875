module

public import Sarkozy.FiveType.Graded
public import Sarkozy.FiveType.JointBlocks

/-!
# From block rows to a reflection positive completion (`cor:joint-completion-blocks` with (f))

Source: `paper/sections/17_completion_repair.tex`, `cor:joint-completion-blocks` ("Consequently,
if this holds at every `b ∈ supp ν` ...") and `lem:five-type`(f).

`Datum.joint_blocks_rp` composes the corollary (`Blocks.blockJointData`, with `lem:joint-rows`
(b), (c) as hypotheses) with the graded joint criterion (`Datum.joint_rp_graded`). Take a
five-type datum on the block space `∏_p X_p` whose conditional objects at every `b ∈ supp ν` are
block products: `ν^b = ⊗_p ν_p^b`, `T_E^b = ⊗_p T^b_{E,p}`, `T_F^b = m_b ⊗_p T^b_{F,p}`. Suppose the
per-prime hypotheses of the corollary hold at every `b`, with the same constants, and `E_T ≤ ε_T`.
Then the completion inequalities `w_D ≥ d w_L`, `w_S ≥ M w_D`, `w_R ≥ f w_D + h w_S`,
`w_C w_S ≥ w_R²`, with `M ≥ H + t_Y`, `f ≥ f_J`, `0 < t_Y ≤ H⁻¹`, make the five-type measure with
the graded weights reflection positive at every chamber cut. This is how the bands of the upper
range use the corollary (`rem:five-type-certificates`).

`JointData.monoT` raises `ε_T` to a uniform bound.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Blocks

/-- Joint data stay joint data with a larger `ε_T`. -/
def JointData.monoT {𝔛 : Type*} [Fintype 𝔛] {μ : FiniteLaw 𝔛} {TE K : 𝔛 → 𝔛 → ℝ}
    {H υ εT εT' εE κJ : ℝ} (J : JointData μ TE K H υ εT εE κJ) (h : εT ≤ εT') :
    JointData μ TE K H υ εT' εE κJ :=
  { J with normR := Blocks.FormBound.mono J.normR h }

namespace Datum

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]
  [∀ i, DecidableEq (Xp i)]

/-- **Block rows give a reflection positive completion** (`cor:joint-completion-blocks` composed
with `lem:five-type`(f), graded form). `lem:joint-rows` (b), (c) enter as `hJRb`, `hJRc`. -/
theorem joint_blocks_rp (D : Datum ((i : ι) → Xp i))
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
    (hJRb : ∀ b, D.nu.weight b ≠ 0 →
      JointRowsB (νp b) (fun i => matchCov (TEp b i)) (fun i => foldCov (νp b i) (TFp b i)))
    (hJRc : ∀ b, D.nu.weight b ≠ 0 → JointRowsC (νp b) (TFp b))
    (hET : ET υ cF rp ≤ εT) (hεT : 0 ≤ εT) (hh : 0 ≤ h)
    (hw : ∀ t, 0 ≤ w t) (hwD : 0 < w .D) (htY : 0 < tY) (htH : tY ≤ H⁻¹) (hM : H + tY ≤ M)
    (hf : fJ H kJ h r εT tY υ ≤ f) (h2 : M * w .D ≤ w .S) (h3 : f * w .D + h * w .S ≤ w .R)
    (h4 : w .R ^ 2 ≤ w .C * w .S)
    (hroot : w .L = 0 ∨ ((chamberCut 0).Below (-(d * r) • D.compF 0) D.compL ∧ d * w .L ≤ w .D)) :
    RPAll (D.Q (graded w r)) := by
  have hJ : ∀ b, D.nu.weight b ≠ 0 →
      JointData (D.nub b) (D.TE b) (D.TF b) H υ εT (h * r) (kJ * r) := by
    intro b hb
    exact ((blockJointData (νp b) (TEp b) (TFp b) rp (hTE b hb) (hTEsymm b hb) (hTF b hb) hr.le
      (fun i => (hrp i).2) hcF hcE (hCF b hb) (hCE b hb) (hJp b hb) hcFr hcEr hkJ (hm0 b hb)
      (hm1 b hb) (hUL b hb) (hUR b hb) (hEB b hb) (hJRb b hb) (hJRc b hb)).monoT hET).transport
      (hnub b hb).symm (hTEb b hb).symm (hTFb b hb).symm
  have hTEx : ∀ b, D.nu.weight b ≠ 0 → ExactMarginals (D.nub b) (D.TE b) := by
    intro b hb
    rw [hnub b hb, hTEb b hb]
    exact prodKernel_exactMarginals (νp b) (TEp b) (hTE b hb)
  obtain ⟨-, hS, hR, -, -⟩ := joint_completion_graded (d := d) htH hM hf hwD.le
    (hroot.elim (fun h0 => by rw [h0, mul_zero]; exact hw .D) (fun h' => h'.2)) h2 h3 h4
  exact D.joint_rp_graded hw hwD hr hh hεT hTEx hJ htY htH hS hR h4 hroot

end Datum

end Sarkozy.FiveType

module

public import Sarkozy.BlockRows.Joint

@[expose] public section

/-!
# Block rows, VI: the joint rows of a block from per-prime joint rows

`paper/sections/17_completion_repair.tex`, `cor:joint-completion-blocks`;
`paper/sections/25_upper_reference.tex`, `def:record:upper-bands` (F3), (F5)(a) and its block form
("the densities and chi-square defects multiply and the correlations are maximized over the
primes").

For laws of three objects that are products over the primes (`IsProd3`), the per-prime inputs
of `cor:joint-completion-blocks` at every middle value give the joint data of `lem:five-type`(f)
at the block, through `joint_completion_blocks'` and `JointData.transport`:

* `JointPrimeCert piE piF rp ℓ cmar cF cE kJ h` (**the per-prime input**, at one prime with
  `r_p = rp`): at every `ξ ∈ supp ν`, the middle density `m = ⟨𝟙, T_F^ξ 𝟙⟩` has
  `|log m| ≤ ℓ` ((F3), `ℓ_mid`); the marginal densities `u_L = T𝟙`, `u_R = T*𝟙` of the fold kernel
  of mass one `T = T_F^ξ/m` have `‖u - 𝟙‖ ≤ c_mar r_p` ((F3), `c_mar`); `‖C_F‖ ≤ c_F r_p`,
  `‖C_E‖ ≤ c_E r_p` and the joint block `⪰ -k_J r_p` (`lem:joint-rows`(a), `lem:joint-pins`); and
  the centred matching kernel has norm at most `h r_p` (the `E` row);
* **`jointData_of_primeCerts`**: the joint data of the block at every `ξ ∈ supp ν`, with
  `H = e^{n ℓ}`, `υ = (e^{n c_mar² r²} - 1)^{1/2}`, `ε_T = E_T`, `ε_E = h r`, `κ_J = k_J r`
  (`n ≥ |𝔅|`, `r ≥ r_p`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.BlockRows

open Sarkozy Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.PartV Sarkozy.Cuts Sarkozy.Peyre
  Sarkozy.JointRows

section Generic

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- The middle density `m_ξ = ⟨𝟙, T_F^ξ 𝟙⟩_{ν^ξ}`. -/
noncomputable def midDens (piE piF : FiniteLaw (Fin 3 → 𝔛)) (ξ : 𝔛) : ℝ :=
  kf (nubOf piE ξ) (kernelOf piE piF ξ) (fun _ => 1) (fun _ => 1)

/-- The fold kernel of mass one, `T_F^ξ / m_ξ`. -/
noncomputable def foldUnit (piE piF : FiniteLaw (Fin 3 → 𝔛)) (ξ : 𝔛) (x y : 𝔛) : ℝ :=
  kernelOf piE piF ξ x y / midDens piE piF ξ

/-- **The per-prime joint rows** (the per-prime hypotheses of `cor:joint-completion-blocks` and the
per-prime quantities `ℓ_mid`, `c_mar` of (F3)) of the laws `piE`, `piF` of three objects at one
prime, with `r_p = rp`. *Hypothesis* (per prime). -/
structure JointPrimeCert (piE piF : FiniteLaw (Fin 3 → 𝔛)) (rp ℓ cmar cF cE kJ h : ℝ) :
    Prop where
  /-- `|log m_ξ| ≤ ℓ_mid` ((F3), the middle log ratio). -/
  mid : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    Real.exp (-ℓ) ≤ midDens piE piF ξ ∧ midDens piE piF ξ ≤ Real.exp ℓ
  /-- `‖u_L - 𝟙‖ ≤ c_mar r_p` ((F3), the marginal coefficient). -/
  marL : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    nrm (nubOf piE ξ) (fun x => kone (nubOf piE ξ) (foldUnit piE piF ξ) x - 1) ≤ cmar * rp
  /-- `‖u_R - 𝟙‖ ≤ c_mar r_p`. -/
  marR : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    nrm (nubOf piE ξ) (fun y => kone' (nubOf piE ξ) (foldUnit piE piF ξ) y - 1) ≤ cmar * rp
  /-- `‖C_F‖ ≤ c_F r_p` (`lem:joint-rows`). -/
  foldC : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    FormBound (nubOf piE ξ) (foldCov (nubOf piE ξ) (foldUnit piE piF ξ)) (cF * rp)
  /-- `‖C_E‖ ≤ c_E r_p` (`lem:joint-rows`). -/
  matchC : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    FormBound (nubOf piE ξ) (matchCov (kernelOf piE piE ξ)) (cE * rp)
  /-- The joint block `(C_E C_F; C_F* C_E) ⪰ -k_J r_p` (`lem:joint-rows`(a), `lem:joint-pins`). -/
  joint : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    JointBlockLower (nubOf piE ξ) (matchCov (kernelOf piE piE ξ))
      (foldCov (nubOf piE ξ) (foldUnit piE piF ξ)) (kJ * rp)
  /-- The `E` row: the centred matching kernel has norm at most `h r_p` ((F5)(a), (F4)). -/
  rowE : ∀ ξ, (nuOf piE).weight ξ ≠ 0 →
    FormBound (nubOf piE ξ) (matchCov (kernelOf piE piE ξ)) (h * rp)

theorem kernelOf_symm (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (ξ x y : 𝔛) : kernelOf piE piE ξ x y = kernelOf piE piE ξ y x := by
  unfold kernelOf
  have hw : piE.weight ![x, ξ, y] = piE.weight ![y, ξ, x] := PartVLaws.piE_swap02 piE hexch x ξ y
  have hc : (nuOf piE).weight ξ * (nubOf piE ξ).weight x * (nubOf piE ξ).weight y =
      (nuOf piE).weight ξ * (nubOf piE ξ).weight y * (nubOf piE ξ).weight x := by ring
  rw [hc, hw]

omit [DecidableEq 𝔛] in
theorem kf_div (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (m : ℝ) (Φ Ψ : 𝔛 → ℝ) :
    kf μ (fun x y => T x y / m) Φ Ψ = kf μ T Φ Ψ / m := by
  unfold kf
  rw [sum_div]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_div]
  exact sum_congr rfl fun y _ => by ring

/-- **The centred matching kernel bounds the conditional correlation**: if
`‖T_E^ξ - J‖ ≤ ε` on `L²(ν^ξ)`, then `ρ(y₀; y₂ | y₁ = ξ) ≤ ε`. -/
theorem maxCorr_le_of_matchCov (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    {ξ : 𝔛} (hξ : (nuOf piE).weight ξ ≠ 0) {ε : ℝ} (hε : 0 ≤ ε)
    (h : FormBound (nubOf piE ξ) (matchCov (kernelOf piE piE ξ)) ε) :
    maxCorr (condLaw piE ξ) Prod.fst Prod.snd ≤ ε := by
  apply maxCorr_le_of_corrLe hε
  intro f g hf hg
  have hm := condLaw_exact piE hexch hξ
  have hfl : (condLaw piE ξ).expect (fun q => f q.1) = (nubOf piE ξ).expect f := by
    rw [hm.left f]
    exact (nubOf piE ξ).expect_congr fun x => one_mul _
  have hgr : (condLaw piE ξ).expect (fun q => g q.2) = (nubOf piE ξ).expect g := by
    rw [hm.right g]
    exact (nubOf piE ξ).expect_congr fun x => one_mul _
  have hf2 : (condLaw piE ξ).expect (fun q => f q.1 ^ 2) =
      (nubOf piE ξ).expect (fun x => f x * f x) := by
    rw [hm.left (fun x => f x ^ 2)]
    exact (nubOf piE ξ).expect_congr fun x => by ring
  have hg2 : (condLaw piE ξ).expect (fun q => g q.2 ^ 2) =
      (nubOf piE ξ).expect (fun x => g x * g x) := by
    rw [hm.right (fun x => g x ^ 2)]
    exact (nubOf piE ξ).expect_congr fun x => by ring
  have hkf := kf_kernelOf_eq piE piE (PartVLaws.gamSupported_self piE (hexch (Equiv.swap 0 2))) hξ
    rfl f g
  have hb := h f g
  unfold matchCov at hb
  rw [kf_sub_one, hkf] at hb
  rw [hfl] at hf
  rw [hgr] at hg
  rw [hf, hg, mul_zero, sub_zero] at hb
  rw [hf2, hg2]
  exact hb

end Generic

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Y : ι → Type*} [∀ i, Fintype (Y i)]
  [∀ i, DecidableEq (Y i)] {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **The joint data of a block from the per-prime joint rows** (`cor:joint-completion-blocks`
with the block forms of (F3)): for product laws `piE`, `piF` (through `s`) whose factors carry
`JointPrimeCert` at `r_p ≤ r`, at every `ξ ∈ supp ν` the joint data of `lem:five-type`(f) hold
with `H = e^{n ℓ}`, `υ = (e^{n c_mar² r²} - 1)^{1/2}`, `ε_T = E_T`, `ε_E = h r`, `κ_J = k_J r`,
for any `n ≥ |𝔅|`. -/
theorem jointData_of_primeCerts (s : 𝔛 ≃ ∀ i, Y i) {piE piF : FiniteLaw (Fin 3 → 𝔛)}
    {piEp piFp : ∀ i, FiniteLaw (Fin 3 → Y i)} (hPE : IsProd3 s piE piEp)
    (hPF : IsProd3 s piF piFp)
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (hexchp : ∀ i (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Y i),
      (piEp i).weight (ω ∘ σ) = (piEp i).weight ω)
    (rp : ι → ℝ) {r n ℓ cmar cF cE kJ h : ℝ} (hr : 0 ≤ r) (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ r)
    (hcard : (Fintype.card ι : ℝ) ≤ n) (hℓ : 0 ≤ ℓ) (hcmar : 0 ≤ cmar) (hcF : 0 ≤ cF)
    (hcE : 0 ≤ cE) (hh : 0 ≤ h) (hcFr : cF * r < 1) (hcEr : cE * r < 1)
    (hkJ : (cF ^ 2 + cE ^ 2) * r ≤ kJ)
    (hc : ∀ i, JointPrimeCert (piEp i) (piFp i) (rp i) ℓ cmar cF cE kJ h) {ξ : 𝔛}
    (hξ : (nuOf piE).weight ξ ≠ 0) :
    Nonempty (JointData (nubOf piE ξ) (kernelOf piE piE ξ) (kernelOf piE piF ξ)
      (Real.exp (n * ℓ)) √(Real.exp (n * cmar ^ 2 * r ^ 2) - 1)
      (ET √(Real.exp (n * cmar ^ 2 * r ^ 2) - 1) cF rp) (h * r) (kJ * r)) := by
  set υ : ℝ := √(Real.exp (n * cmar ^ 2 * r ^ 2) - 1) with hυ
  have hξi := nu_prod_ne_zero hPE hξ
  set νp : ∀ i, FiniteLaw (Y i) := fun i => nubOf (piEp i) (s ξ i) with hνp
  set TEp : ∀ i, Y i → Y i → ℝ := fun i => kernelOf (piEp i) (piEp i) (s ξ i) with hTEp
  set mp : ι → ℝ := fun i => midDens (piEp i) (piFp i) (s ξ i) with hmp
  set TFp : ∀ i, Y i → Y i → ℝ := fun i => foldUnit (piEp i) (piFp i) (s ξ i) with hTFp
  have hm := fun i => (hc i).mid _ (hξi i)
  have hmpos : ∀ i, 0 < mp i := fun i => lt_of_lt_of_le (Real.exp_pos _) (hm i).1
  have hn0 : 0 ≤ n := le_trans (Nat.cast_nonneg _) hcard
  -- the per-prime hypotheses of `cor:joint-completion-blocks`
  have hTE : ∀ i, ExactMarginals (νp i) (TEp i) := fun i =>
    PartVLaws.kernelOf_exactE (piEp i) (hexchp i) (hξi i)
  have hTEsymm : ∀ i x y, TEp i x y = TEp i y x := fun i x y =>
    kernelOf_symm (piEp i) (hexchp i) _ x y
  have hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1 := fun i => by
    simp only [hνp, hTFp]
    rw [show foldUnit (piEp i) (piFp i) (s ξ i) = fun x y =>
      kernelOf (piEp i) (piFp i) (s ξ i) x y / midDens (piEp i) (piFp i) (s ξ i) from rfl, kf_div]
    exact div_self (hmpos i).ne'
  -- the middle density of the block
  have hm0 : (Real.exp (n * ℓ))⁻¹ ≤ ∏ i, mp i := by
    rw [← Real.exp_neg]
    calc Real.exp (-(n * ℓ)) ≤ Real.exp (-((Fintype.card ι : ℝ) * ℓ)) :=
          Real.exp_le_exp.mpr (by nlinarith)
      _ = ∏ _i : ι, Real.exp (-ℓ) := by
          rw [prod_const, card_univ, ← Real.exp_nat_mul]
          ring_nf
      _ ≤ ∏ i, mp i := prod_le_prod₀ (fun _ _ => (Real.exp_pos _).le) (fun i _ => (hm i).1)
  have hm1 : ∏ i, mp i ≤ Real.exp (n * ℓ) := by
    calc ∏ i, mp i ≤ ∏ _i : ι, Real.exp ℓ :=
          prod_le_prod₀ (fun i _ => (hmpos i).le) (fun i _ => (hm i).2)
      _ = Real.exp ((Fintype.card ι : ℝ) * ℓ) := by
          rw [prod_const, card_univ, ← Real.exp_nat_mul]
      _ ≤ Real.exp (n * ℓ) := Real.exp_le_exp.mpr (by nlinarith)
  -- the block marginal densities
  have hchi : ∀ u : ∀ i, Y i → ℝ, (∀ i, (νp i).expect (u i) = 1) →
      (∀ i, nrm (νp i) (fun x => u i x - 1) ≤ cmar * rp i) →
      nrm (blockLaw νp) (fun x => (∏ i, u i (x i)) - 1) ≤ υ := by
    intro u hu1 hu
    have ht := chiSq_tensor_eq νp u hu1
    have hle : ∏ i, (1 + (νp i).expect (fun y => (u i y - 1) ^ 2)) ≤
        Real.exp (n * cmar ^ 2 * r ^ 2) := by
      have h1 : ∀ i, (νp i).expect (fun y => (u i y - 1) ^ 2) ≤ cmar ^ 2 * r ^ 2 := by
        intro i
        have hn := hu i
        have hsq : nrm (νp i) (fun x => u i x - 1) ^ 2 =
            (νp i).expect (fun y => (u i y - 1) ^ 2) := by
          unfold nrm ip
          rw [Real.sq_sqrt ((νp i).expect_nonneg fun y => mul_self_nonneg _)]
          exact (νp i).expect_congr fun y => by ring
        rw [← hsq]
        have h0 := FiveType.nrm_nonneg (νp i) (fun x => u i x - 1)
        have h2 : cmar * rp i ≤ cmar * r := mul_le_mul_of_nonneg_left (hrp i).2 hcmar
        nlinarith [mul_nonneg hcmar (hrp i).1]
      calc ∏ i, (1 + (νp i).expect (fun y => (u i y - 1) ^ 2))
          ≤ ∏ _i : ι, Real.exp (cmar ^ 2 * r ^ 2) := by
            refine prod_le_prod₀ (fun i _ => ?_) (fun i _ => ?_)
            · have := (νp i).expect_nonneg (f := fun y => (u i y - 1) ^ 2) fun y => sq_nonneg _
              linarith
            · linarith [h1 i, Real.add_one_le_exp (cmar ^ 2 * r ^ 2)]
        _ = Real.exp ((Fintype.card ι : ℝ) * (cmar ^ 2 * r ^ 2)) := by
            rw [prod_const, card_univ, ← Real.exp_nat_mul]
        _ ≤ Real.exp (n * cmar ^ 2 * r ^ 2) := by
            apply Real.exp_le_exp.mpr
            have : 0 ≤ cmar ^ 2 * r ^ 2 := by positivity
            nlinarith
    rw [hυ]
    unfold nrm ip
    apply Real.sqrt_le_sqrt
    have e : (blockLaw νp).expect (fun x => ((∏ i, u i (x i)) - 1) * ((∏ i, u i (x i)) - 1)) =
        (FiniteLaw.pi νp).expect (fun x => ((∏ i, u i (x i)) - 1) ^ 2) := by
      unfold FiniteLaw.expect
      exact sum_congr rfl fun x _ => by
        rw [show (blockLaw νp).weight x = (FiniteLaw.pi νp).weight x from rfl]
        ring
    rw [e]
    linarith
  have hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ :=
    hchi (fun i => kone (νp i) (TFp i)) (fun i => by rw [expect_kone]; exact hTF i)
      (fun i => (hc i).marL _ (hξi i))
  have hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ :=
    hchi (fun i => kone' (νp i) (TFp i)) (fun i => by rw [expect_kone']; exact hTF i)
      (fun i => (hc i).marR _ (hξi i))
  -- the block matching row
  have hμ : ∀ x, (nubOf piE ξ).weight x = (blockLaw νp).weight (s x) := fun x =>
    nub_prod hPE hξ x
  have hTEb : ∀ x y, kernelOf piE piE ξ x y = prodKernel TEp (s x) (s y) := fun x y =>
    kernelOf_prod hPE hPE hξ x y
  have hEB : ∀ Φ, -(h * r) * nrm (blockLaw νp) Φ ^ 2 ≤ kf (blockLaw νp) (EB TEp) Φ Φ := by
    intro Φ
    have hEBk : ∀ x y, kernelOf piE piE ξ x y - 1 = EB TEp (s x) (s y) := by
      intro x y
      rw [hTEb]
      unfold EB sectorKernel matchCov prodKernel
      congr 1
      exact prod_congr rfl fun i _ => by ring
    have h1 := kf_equiv s hμ hEBk (fun x => Φ (s x)) (fun x => Φ (s x))
    have h2 := nrm_equiv s hμ (fun x => Φ (s x))
    simp only [Equiv.apply_symm_apply] at h1 h2
    rw [← h1, ← h2, kf_sub_one,
      kf_kernelOf_eq piE piE (PartVLaws.gamSupported_self piE (hexch (Equiv.swap 0 2))) hξ rfl]
    have hρC : maxCorr (condLaw piE ξ) Prod.fst Prod.snd ≤ h * r :=
      maxCorr_split_le s _ _ (condLaw_prod hPE hξ) (mul_nonneg hh hr) fun i =>
        (maxCorr_le_of_matchCov (piEp i) (hexchp i) (hξi i) (mul_nonneg hh (hrp i).1)
          ((hc i).rowE _ (hξi i))).trans (mul_le_mul_of_nonneg_left (hrp i).2 hh)
    have hb := exact_rows (nubOf piE ξ) (condLaw piE ξ) (condLaw_exact piE hexch hξ) hρC
      (mul_nonneg hh hr) (fun x => Φ (s x)) (fun x => Φ (s x))
    have hab := neg_abs_le ((condLaw piE ξ).expect (fun q => Φ (s q.1) * Φ (s q.2)) -
      (nubOf piE ξ).expect (fun x => Φ (s x)) * (nubOf piE ξ).expect (fun x => Φ (s x)))
    nlinarith
  obtain ⟨-, ⟨J, -⟩, -⟩ := joint_completion_blocks' νp TEp TFp rp (r := r) (cF := cF) (cE := cE)
    (kJ := kJ) (h := h) (H := Real.exp (n * ℓ)) (υ := υ) (mb := ∏ i, mp i) hTE hTEsymm hTF hr hrp
    hcF hcE (fun i => (hc i).foldC _ (hξi i)) (fun i => (hc i).matchC _ (hξi i))
    (fun i => (hc i).joint _ (hξi i)) hcFr hcEr hkJ hm0 hm1 hUL hUR hEB
  have hK : ∀ x y, kernelOf piE piF ξ x y = (∏ i, mp i) * prodKernel TFp (s x) (s y) := by
    intro x y
    rw [kernelOf_prod hPE hPF hξ, prodKernel, ← prod_mul_distrib]
    refine prod_congr rfl fun i _ => ?_
    have hmi : mp i ≠ 0 := (hmpos i).ne'
    show _ = mp i * (kernelOf (piEp i) (piFp i) (s ξ i) (s x i) (s y i) / mp i)
    field_simp
  exact ⟨JointData.transport s hμ hTEb hK J⟩

end Block

end Sarkozy.BlockRows

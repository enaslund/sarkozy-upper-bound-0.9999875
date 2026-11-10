module

public import Sarkozy.SpectralD.CxTransfer

@[expose] public section

/-!
# Instance (A) of `def:coupling-data` for the cut

`paper/sections/14_spectral.tex`, `def:coupling-data`, instance (A): `ν = m_p`, and
`P_k(· | x)` the conditional law of `x'_k` given `x` under `λ`. For WP-P's cut data (`Cuts.SpecData`)
over `𝔽_p`, with `μ = λ(G⁺)`, the kernel `K/Z` (`cutKn`), `ϱ = Op 1` (`rhoK`) and
`P_k = condP` (on `𝓘⁺ = Inj_p(G⁺)`, `0` off it), `couplingDataA` builds the `CouplingData`
structure. Proved here: `ν ≥ 0`, `∑_{𝓘⁺} ν = 1`, `ν = 0` off `𝓘⁺`, `P ≥ 0`, `∑_a P_k = 1`,
`P_k` supported on the allowed set `Φ_k(x)` (`condP_supp`: a label outside `Φ_k(x)` violates
`CutOK`), `𝓘⁺` and `ν` invariant, the covariance (ii). Taken as hypotheses (the counting
content of instance (A)): `ϱ > 0` on `𝓘⁺`, the density ratio `c ≤ ϱ ≤ R c` of (i), and the
densities `|Φ_k(x)| P_k ∈ [1/R'_k, R'_k]` of (iii) (`eq:spec:Rprime`).

`couplingBound_supp` is fork B's `coupling_block_concrete` in the complex realization with the
instance-(A) relation `Op F_V = ϱ·𝒫F_V` required only on the support of `μ`; with
`couplingDataA` and `opFun_degFun_eq` it gives `couplingBound_cut`, the coupling bound
`CouplingBoundCx` for the cut, which is the remaining input `hbound` of `cut_lower_real_of_real`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace Matrix

/-! ## `eq:spec:coupling` with the instance-(A) relation on the support -/

section Support

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- **`eq:spec:coupling` in the complex realization**, as `couplingBound_cx`, but with
`Op F_V = ϱ·𝒫F_V` and `ϱ ≤ R` required only where `μ ≠ 0`. -/
theorem couplingBound_supp (Adj : U → U → Prop) [DecidableRel Adj] (hp2 : p ≠ 2)
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ) (hΛ1 : ∑ z, cutLaw μ k z = 1)
    (hΛinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      cutLaw μ k (affLab s c z.1, affLab s c z.2) = cutLaw μ k z)
    (hΛinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (a b : U), cutLaw μ k z ≠ 0 → z.1 a ≠ z.2 b)
    {N : U → Finset U} {ς : U → U → ZMod p} {Iplus : Finset (U → ZMod p)}
    (D : CouplingData p U N ς Iplus μ) (ϱ : (U → ZMod p) → ℝ) (hϱ0 : ∀ x, 0 ≤ ϱ x) {R : ℝ}
    (hR0 : 0 ≤ R) (hR : ∀ x, μ x ≠ 0 → ϱ x ≤ R) (hνϱ : ∀ x, D.ν x = μ x * ϱ x)
    (hA : ∀ g : U → ZMod p → ℂ, (∀ l, ∑ a, g l a = 0) →
      ∀ x, μ x ≠ 0 → opFun μ k (degFun g) x = (ϱ x : ℂ) * condField D.P g x)
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : U → ℂ, ∑ x, D.ν x * l2sq (fun a => ∑ l, w l *
      ((p : ℂ) * (D.P l x a : ℂ) - starProd N ς l x a)) ≤ ΓE * ∑ l, ‖w l‖ ^ 2)
    (Dj : U → ℝ) (hpiv : ∀ j x t, D.ν x ≠ 0 → condLaw D.ν j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ l, ((2 : ℝ) ^ (N l).card - 1) * ∑ l', ((2 : ℝ) ^ (N l').card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset U, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ D.ν J‖ ≤ ζ * rp p)
    (hHt : ∀ w : U → ℂ, (qform (gramΓ D.ν (psiField D.P)) w).re ≤
      (qform (PaleyB.modelHC N ς) w).re + εH * ∑ l, ‖w l‖ ^ 2)
    (hlam : ∀ w : U → ℂ, (qform (PaleyB.modelHC N ς) w).re ≤ lamH * ∑ l, ‖w l‖ ^ 2)
    (hnc : ∀ w : U → ℂ, PaleyB.hncQ Adj N ς w ≤ Λnc * ∑ l, ‖w l‖ ^ 2)
    (hplus : ∀ w : U → ℂ, (qform (PaleyB.modelHC N ς) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj N ς w ≤ Λp * ∑ l, ‖w l‖ ^ 2)
    {ΛD η εV : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η) (hDE : NormLe (deltaE ς) ΛD)
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (errQ (cutLaw μ k) ς ξ) η)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (fun k l => degoneN μ ξ k l - if k = l then 1 else 0) εV) (hεV : 0 ≤ εV) :
    CouplingBoundCx μ k (qXcx Adj N ς)
      (etaBcx p R Λp εH θ ρ ΓE lamH ζ Λnc εV ΛD η) := by
  classical
  intro g hg
  set ϱ' : (U → ZMod p) → ℝ := fun x => if μ x = 0 then 0 else ϱ x with hϱ'
  set OpF : (U → ZMod p) → ℂ := fun x => if μ x = 0 then 0 else opFun μ k (degFun g) x
    with hOpF
  have hϱ'0 : ∀ x, 0 ≤ ϱ' x := fun x => by
    simp only [hϱ']; split_ifs
    · exact le_refl 0
    · exact hϱ0 x
  have hϱ'R : ∀ x, ϱ' x ≤ R := fun x => by
    simp only [hϱ']; split_ifs with h
    · exact hR0
    · exact hR x h
  have hνϱ' : ∀ x, D.ν x = μ x * ϱ' x := fun x => by
    rw [hνϱ]; simp only [hϱ']; split_ifs with h
    · rw [h, zero_mul, mul_zero]
    · rfl
  have hOp : ∀ x, OpF x = (ϱ' x : ℂ) * condField D.P g x := fun x => by
    simp only [hOpF, hϱ']; split_ifs with h
    · simp
    · exact hA g hg x h
  have hTF : ‖kernelOpC μ k (degMap μ g)‖ ^ 2 = ∑ x, μ x * ‖OpF x‖ ^ 2 := by
    rw [hTF_degMap μ hμ0 k g]
    refine sum_congr rfl fun x _ => ?_
    simp only [hOpF]; split_ifs with h
    · rw [h, zero_mul, zero_mul]
    · rfl
  exact PaleyB.coupling_block_concrete Adj (kernelOpC μ k) (degSpace μ) (degMap μ g) D hp2
    hμ0 hμ1 ϱ' hϱ'0 hϱ'R hνϱ' g hg OpF hOp hTF
    hΓ0 hΛ0 hΓ Dj hpiv hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus (cutLaw μ k) hΛD hη hDE hE
    (stepTwoVec μ (cutLaw μ k) g) (stepTwo_mem μ (cutLaw μ k) hg)
    (stepTwo_inner hp2 μ hμ0 k hΛ1 hΛinv hΛinj hg)
    (stepTwo_norm hp2 μ hμ0 hμ1 hinv hinj hN (cutLaw μ k) hg) hεV

end Support

/-! ## The coupling data of the cut -/

section Cut

variable {p : ℕ} [Fact p.Prime] {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- The cross signs `ς_jk` in `𝔽_p`. -/
def sgnZ (j k : D.cut.Half) : ZMod p := ((D.sgn j k : ℤ) : ZMod p)

/-- `ν = m_p = ϱ μ`. -/
noncomputable def nuA (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x : D.cut.Half → ZMod p) : ℝ :=
  (D.halfLaw hne).weight x * rhoK (D.halfLaw hne).weight (cutKn D hne) x

/-- `P_k(a | x)`: the conditional law on `𝓘⁺`, `0` off it. -/
noncomputable def PA (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) (i : D.cut.Half)
    (x : D.cut.Half → ZMod p) (a : ZMod p) : ℝ :=
  if x ∈ Labellings.injLabellings (ZMod p) D.halfGraph then
    condP (D.halfLaw hne).weight (cutKn D hne) i x a else 0

lemma cutKn_nonneg (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x x' : D.cut.Half → ZMod p) : 0 ≤ cutKn D hne x x' :=
  div_nonneg (D.cutK_nonneg x x') (D.cutZ_pos hne).le

lemma rhoK_nonneg (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (x : D.cut.Half → ZMod p) : 0 ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x :=
  sum_nonneg fun x' _ => mul_nonneg ((D.halfLaw hne).nonneg x') (cutKn_nonneg D hne x x')

lemma halfLaw_weight_off (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    {x : D.cut.Half → ZMod p} (hx : x ∉ Labellings.injLabellings (ZMod p) D.halfGraph) :
    (D.halfLaw hne).weight x = 0 := by
  classical
  show (Labellings.graphLaw D.halfGraph (D.half_nonempty hne)).weight x = 0
  unfold Labellings.graphLaw
  simp only [hx, ↓reduceIte]

/-- `ϱ` is invariant under the square-affine maps. -/
lemma rhoK_affLab (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {s : ZMod p}
    (hs : s ≠ 0) (hsq : IsSquare s) (c : ZMod p) (x : D.cut.Half → ZMod p) :
    rhoK (D.halfLaw hne).weight (cutKn D hne) (affLab s c x) =
      rhoK (D.halfLaw hne).weight (cutKn D hne) x := by
  obtain ⟨-, -, hinv, -⟩ := halfLaw_hyps D hne
  unfold rhoK
  rw [← (affLab_bijective hs c).sum_comp]
  refine sum_congr rfl fun y _ => ?_
  unfold cutKn
  rw [hinv s c y hs hsq, cutK_affLab D hs hsq]

/-- **Support of `P_k`**: a label outside the allowed set `Φ_k(x)` violates the cut
constraints (a collision with `x`, or a failed cross constraint at `k`). -/
lemma condP_supp (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) (i : D.cut.Half)
    (x : D.cut.Half → ZMod p) (a : ZMod p) (ha : a ∉ allowedSet D.Nset (sgnZ D) i x) :
    condP (D.halfLaw hne).weight (cutKn D hne) i x a = 0 := by
  classical
  unfold condP
  have h0 : ∀ x' : D.cut.Half → ZMod p,
      (if x' i = a then (D.halfLaw hne).weight x' * cutKn D hne x x' else 0) = 0 := by
    intro x'
    by_cases hx' : x' i = a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hx')]
      have hK : D.cutK x x' = 0 := by
        unfold Cuts.SpecData.cutK
        have hnot : ¬ D.CutOK x x' := by
          rintro ⟨hd, hc⟩
          apply ha
          simp only [allowedSet, mem_filter, mem_univ, true_and]
          refine ⟨?_, fun j hj => ?_⟩
          · intro hmem
            rw [disjoint_left] at hd
            exact hd hmem (mem_image.mpr ⟨i, mem_univ _, hx'⟩)
          · have hjk : (j, i) ∈ D.crossPairs := by
              simp only [Cuts.SpecData.crossPairs, mem_filter, mem_univ, true_and]
              simp only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] at hj
              exact hj
            have hq := hc (j, i) hjk
            simp only at hq
            rw [hx'] at hq
            have hne0 : (sgnZ D j i : ZMod p) * (a - x j) ≠ 0 := by
              intro h0
              unfold sgnZ at h0
              rw [h0, quadraticChar_zero] at hq
              exact zero_ne_one hq
            exact ⟨hne0, (quadraticChar_one_iff_isSquare hne0).mp hq⟩
        simp only [hnot, ↓reduceIte]
      unfold cutKn
      rw [hK, zero_div, mul_zero]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hx')]
  rw [sum_eq_zero fun x' _ => h0 x', zero_div]

/-- **Instance (A) of `def:coupling-data` for the cut.** The counting content of (A) is taken
as hypotheses: `ϱ > 0` on `𝓘⁺` (`hρpos`), the density ratio `c ≤ ϱ ≤ R c` of (i) (`hdens`;
the paper's `R_ν = R_cut`), and the densities (iii) with the `R'_k` of `eq:spec:Rprime`
(`hPdens`). -/
noncomputable def couplingDataA (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (hρpos : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      0 < rhoK (D.halfLaw hne).weight (cutKn D hne) x)
    (c R : ℝ) (hc : 0 < c) (hR : 1 ≤ R)
    (hdens : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      c ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ R * c)
    (Rp : D.cut.Half → ℝ) (hRp : ∀ i, 1 ≤ Rp i)
    (hPdens : ∀ i, ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      ∀ a ∈ allowedSet D.Nset (sgnZ D) i x,
        (Rp i)⁻¹ ≤ PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ∧
          PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ≤ Rp i) :
    CouplingData p D.cut.Half D.Nset (sgnZ D) (Labellings.injLabellings (ZMod p) D.halfGraph)
      (D.halfLaw hne).weight := by
  classical
  exact {
  ν := nuA D hne
  P := PA D hne
  ν_nonneg := fun x => mul_nonneg ((D.halfLaw hne).nonneg x) (rhoK_nonneg D hne x)
  ν_total := by
    have e : ∑ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph, nuA D hne x =
        ∑ x, nuA D hne x := by
      refine sum_subset (subset_univ _) fun x _ hx => ?_
      unfold nuA
      rw [halfLaw_weight_off D hne hx, zero_mul]
    rw [e]
    have h1 := cutLaw_total D hne
    rw [Fintype.sum_prod_type] at h1
    rw [← h1]
    refine sum_congr rfl fun x _ => ?_
    unfold nuA rhoK cutLaw
    rw [mul_sum]
    exact sum_congr rfl fun x' _ => by ring
  ν_supp := fun x hx => by unfold nuA; rw [halfLaw_weight_off D hne hx, zero_mul]
  P_nonneg := fun i x a => by
    unfold PA
    split_ifs
    · unfold condP
      exact div_nonneg (sum_nonneg fun x' _ => by
        split_ifs
        · exact mul_nonneg ((D.halfLaw hne).nonneg x') (cutKn_nonneg D hne x x')
        · exact le_refl 0) (rhoK_nonneg D hne x)
    · exact le_refl 0
  P_total := fun i x hx => by
    have e : ∀ a, PA D hne i x a = condP (D.halfLaw hne).weight (cutKn D hne) i x a := by
      intro a; unfold PA; simp only [hx, ↓reduceIte]
    simp only [e]
    unfold condP
    rw [← sum_div, sum_comm]
    have h2 : ∀ x' : D.cut.Half → ZMod p, ∑ a, (if x' i = a then
        (D.halfLaw hne).weight x' * cutKn D hne x x' else 0) =
        (D.halfLaw hne).weight x' * cutKn D hne x x' := by
      intro x'; rw [sum_ite_eq]; simp
    rw [sum_congr rfl fun x' _ => h2 x']
    exact div_self (hρpos x hx).ne'
  P_supp := fun i x hx a ha => by
    unfold PA
    simp only [hx, ↓reduceIte]
    exact condP_supp D hne i x a ha
  P_off := fun i x a hx => by unfold PA; simp only [hx, ↓reduceIte]
  I_inv := fun s c x hs hsq => by
    have hq : quadraticChar (ZMod p) s = 1 := (quadraticChar_one_iff_isSquare hs).mpr hsq
    exact Cuts.affine_mem_inj D.halfGraph hq c x
  ν_inv := fun s c x hs hsq => by
    obtain ⟨-, -, hinv, -⟩ := halfLaw_hyps D hne
    unfold nuA
    rw [hinv s c x hs hsq, rhoK_affLab D hne hs hsq]
  dens_c := c
  dens_R := R
  dens_c_pos := hc
  dens_R_ge := hR
  dens := fun x hx => by
    obtain ⟨h1, h2⟩ := hdens x hx
    have hμ := (D.halfLaw hne).nonneg x
    unfold nuA
    constructor
    · rw [mul_comm]; exact mul_le_mul_of_nonneg_left h1 hμ
    · calc (D.halfLaw hne).weight x * rhoK (D.halfLaw hne).weight (cutKn D hne) x
          ≤ (D.halfLaw hne).weight x * (R * c) := mul_le_mul_of_nonneg_left h2 hμ
        _ = R * c * (D.halfLaw hne).weight x := by ring
  P_cov := fun i s c x hx a hs hsq => by
    have hq : quadraticChar (ZMod p) s = 1 := (quadraticChar_one_iff_isSquare hs).mpr hsq
    have hx' : affLab s c x ∈ Labellings.injLabellings (ZMod p) D.halfGraph :=
      (Cuts.affine_mem_inj D.halfGraph hq c x).mpr hx
    obtain ⟨-, -, hinv, -⟩ := halfLaw_hyps D hne
    unfold PA
    simp only [hx, hx', ↓reduceIte]
    unfold condP
    rw [rhoK_affLab D hne hs hsq]
    congr 1
    rw [← (affLab_bijective hs c).sum_comp]
    refine sum_congr rfl fun y _ => ?_
    have e : (affLab s c y i = s * a + c) ↔ (y i = a) := by
      unfold affLab
      constructor
      · intro h; exact mul_left_cancel₀ hs (add_right_cancel h)
      · intro h; rw [h]
    by_cases hy : y i = a
    · rw [ite_eq_left_of_eq_true _ _ (eq_true (e.mpr hy)), ite_eq_left_of_eq_true _ _ (eq_true hy)]
      unfold cutKn
      rw [hinv s c y hs hsq, cutK_affLab D hs hsq]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h => hy (e.mp h))),
        ite_eq_right_of_eq_false _ _ (eq_false hy)]
  Rp := Rp
  Rp_ge := hRp
  P_dens := hPdens }

/-- **The coupling bound for the cut** (`cor:spec2:coupling`, `eq:spec:coupling`, complex
realization): `CouplingBoundCx` for `μ = λ(G⁺)` and `K/Z`, from the instance-(A) coupling data
`couplingDataA` (hypotheses: the counting content of instance (A)) and the paper's numbers
(`Γ_E`, `D_j`, `θ`, `ρ_row`, `ζ̄`, the model bounds, `Λ_D`, `η_Q`, `ε_V`), stated for
`ν = nuA` and `P = PA`. This is the input `hbound` of `cut_lower_real_of_real`. -/
theorem couplingBound_cut (Adj : D.cut.Half → D.cut.Half → Prop) [DecidableRel Adj]
    (hp2 : p ≠ 2) (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
    (hρpos : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      0 < rhoK (D.halfLaw hne).weight (cutKn D hne) x)
    (c R : ℝ) (hc : 0 < c) (hR : 1 ≤ R)
    (hdens : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      c ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
        rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ R * c)
    (Rp : D.cut.Half → ℝ) (hRp : ∀ i, 1 ≤ Rp i)
    (hPdens : ∀ i, ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
      ∀ a ∈ allowedSet D.Nset (sgnZ (p := p) D) i x,
        (Rp i)⁻¹ ≤ PA D hne i x a * (allowedSet D.Nset (sgnZ (p := p) D) i x).card ∧
          PA D hne i x a * (allowedSet D.Nset (sgnZ (p := p) D) i x).card ≤ Rp i)
    {ΓE lamH εH : ℝ} (hΓ0 : 0 ≤ ΓE) (hΛ0 : 0 ≤ lamH + εH)
    (hΓ : ∀ w : D.cut.Half → ℂ, ∑ x, nuA D hne x * l2sq (fun a => ∑ l, w l *
      ((p : ℂ) * (PA D hne l x a : ℂ) - starProd D.Nset (sgnZ (p := p) D) l x a)) ≤
        ΓE * ∑ l, ‖w l‖ ^ 2)
    (Dj : D.cut.Half → ℝ) (hpiv : ∀ j x t, nuA D hne x ≠ 0 → condLaw (nuA D hne) j x t ≤ Dj j / p)
    {θ : ℝ} (hθ0 : 0 ≤ θ) (hθ : ∀ j, Dj j - 1 ≤ θ ^ 2)
    {ρ : ℝ} (hρ : ∀ l, ((2 : ℝ) ^ (D.Nset l).card - 1) *
      ∑ l', ((2 : ℝ) ^ (D.Nset l').card - 1) ≤ ρ)
    {ζ Λnc Λp : ℝ} (hζ0 : 0 ≤ ζ)
    (hζ : p % 4 = 1 → ∀ J : Finset D.cut.Half, 2 ≤ J.card → ¬ PaleyB.Coverable Adj J →
      ‖PaleyB.tJ (nuA D hne) J‖ ≤ ζ * rp p)
    (hHt : ∀ w : D.cut.Half → ℂ, (qform (gramΓ (nuA D hne) (psiField (PA D hne))) w).re ≤
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re + εH * ∑ l, ‖w l‖ ^ 2)
    (hlam : ∀ w : D.cut.Half → ℂ,
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re ≤ lamH * ∑ l, ‖w l‖ ^ 2)
    (hnc : ∀ w : D.cut.Half → ℂ, PaleyB.hncQ Adj D.Nset (sgnZ (p := p) D) w ≤ Λnc * ∑ l, ‖w l‖ ^ 2)
    (hplus : ∀ w : D.cut.Half → ℂ, (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re +
      (if p % 4 = 1 then (1 : ℝ) else 0) * PaleyB.hcovQ Adj D.Nset (sgnZ (p := p) D) w ≤
        Λp * ∑ l, ‖w l‖ ^ 2)
    {ΛD η εV : ℝ} (hΛD : 0 ≤ ΛD) (hη : 0 ≤ η) (hDE : NormLe (deltaE (sgnZ (p := p) D)) ΛD)
    (hE : ∀ ξ : ZMod p, ξ ≠ 0 →
      NormLe (errQ (cutLaw (D.halfLaw hne).weight (cutKn D hne)) (sgnZ (p := p) D) ξ) η)
    (hN : ∀ ξ : ZMod p, ξ ≠ 0 → NormLe (fun k l => degoneN (D.halfLaw hne).weight ξ k l -
      if k = l then 1 else 0) εV) (hεV : 0 ≤ εV) :
    CouplingBoundCx (D.halfLaw hne).weight (cutKn D hne) (qXcx Adj D.Nset (sgnZ (p := p) D))
      (etaBcx p (R * c) Λp εH θ ρ ΓE lamH ζ Λnc εV ΛD η) := by
  obtain ⟨h0, h1, hinv, hinj⟩ := halfLaw_hyps D hne
  have hmem : ∀ x, (D.halfLaw hne).weight x ≠ 0 →
      x ∈ Labellings.injLabellings (ZMod p) D.halfGraph := fun x hx => by
    by_contra h; exact hx (halfLaw_weight_off D hne h)
  refine couplingBound_supp Adj hp2 (D.halfLaw hne).weight h0 h1 hinv hinj (cutKn D hne)
    (cutLaw_total D hne) (fun s c z hs hsq => cutLaw_inv D hne s c z hs hsq)
    (fun z a b hz => cutLaw_inj D hne z a b hz)
    (couplingDataA D hne hρpos c R hc hR hdens Rp hRp hPdens)
    (rhoK (D.halfLaw hne).weight (cutKn D hne)) (rhoK_nonneg D hne)
    (by positivity) (fun x hx => (hdens x (hmem x hx)).2) (fun x => rfl) ?_
    hΓ0 hΛ0 hΓ Dj hpiv hθ0 hθ hρ hζ0 hζ hHt hlam hnc hplus hΛD hη hDE hE hN hεV
  intro g _ x hx
  rw [opFun_degFun_eq (D.halfLaw hne).weight h0 (cutKn D hne) (cutKn_nonneg D hne) g x]
  congr 1
  unfold condField
  refine sum_congr rfl fun i _ => sum_congr rfl fun a _ => ?_
  show _ = ((PA D hne i x a : ℝ) : ℂ) * g i a
  unfold PA
  simp only [hmem x hx, ↓reduceIte]

/-- `qX ξ 0 = 0` for the coupling form, the side condition `hqX0` of `cx_coupling`,
`routeAInputs_cut` and `cut_lower_real_of_real` (with `qX = qXcx Adj D.Nset sgnZ` from
`couplingBound_cut`). -/
theorem qXcx_zero {U : Type*} [Fintype U] [DecidableEq U] (Adj : U → U → Prop)
    [DecidableRel Adj] (N : U → Finset U) (ς : U → U → ZMod p) (ξ : ZMod p) :
    qXcx Adj N ς ξ 0 = 0 := by
  have h1 : ((azero ς ξ : Matrix U U ℂ) *ᵥ (0 : U → ℂ)) = 0 := Matrix.mulVec_zero _
  have h2 : ((PaleyB.hplusM Adj N ς : Matrix U U ℂ) *ᵥ (0 : U → ℂ)) = 0 :=
    Matrix.mulVec_zero _
  unfold qXcx Sarkozy.Spectral.qform Sarkozy.Spectral.sqn
  rw [h1, h2]
  simp

end Cut

end Sarkozy.SpectralD.Cx

module

public import Sarkozy.TheoremCBlock.Main
public import Sarkozy.TheoremC.Cancellation

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCBlock

open Sarkozy.TheoremC
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-! ## The statement of `lem:record:density-can` -/

section DensityCan

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The input `g^{I_b, M₀, s}` of `def:record:functional`(f) at the index
`(b, s) ∈ ℤ/Kℤ × ℤ/M₀ℤ` (`Sarkozy.Functional.indexedInput`), read on the atom labels. -/
noncomputable def indexInputAt (L : ℕ) (A : Finset ℤ)
    (ω : ZMod blockScale × ZMod (modulus pr h)) (x : ∀ b, BlockLabel m₀ blk p L b) : ℝ :=
  indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L (modulus pr h)
    A ω (blockGroupEquiv m₀ blk p L x)

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] [Fintype Bk] [DecidableEq Bk] in
/-- The query input in the CRT coordinates is the input at the index `(b, s)`. -/
theorem atomInput_eq_indexInputAt (L : ℕ) (A : Finset ℤ) {E : Type} (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) :
    blockInput m₀ blk p pr h hcop L A e η =
      indexInputAt m₀ blk p pr h L A ((crtEquiv blockScale pr h hcop).symm η) := rfl

/-- The inputs of `def:record:functional`(f) that occur in the coupled forms, read on the atom
labels: `F_A = g^{[N],1,0}` (`atomLift`), or `g^{I_b, M₀, s}` at an index `(b, s)`
(`indexInputAt`). -/
def IsQueryInput (L : ℕ) (A : Finset ℤ) (G : (∀ b, BlockLabel m₀ blk p L b) → ℝ) : Prop :=
  G = blockLift m₀ blk p L A ∨
    ∃ ω : ZMod blockScale × ZMod (modulus pr h), G = indexInputAt m₀ blk p pr h L A ω

/-- **`lem:record:density-can`** (accepted-pair cancellation with a density factor), over the
objects of `Sarkozy.PaperFrame`. There is a constant `C_can` with the following property.
Let `L ≥ L_*`, `N = KL`, let `A ⊆ [N]` be square-difference-free and `α = |A|/N`. Let
`ϱ = ⊗_𝔟 ϱ_𝔟` be a product of probability measures, each with uniform one-slot marginals.
Let `(u, v)` be an ordered pair of distinct slots such that
(a) at every tail prime `p ≥ P₅` the `(u,v)`-marginal of `ϱ_p` is uniform and `ϱ_p` is
`(γ, (u,v))`-mixing (the hypothesis of `lem:tr:pairsupport`, `γ = 255/1024`);
(b) at the atoms below `P₅` (the prefix and the tail primes `p < P₅`), `ϱ`-almost surely
`z_v − z_u` is accepted (`AcceptedPair`: a nonzero square at the primes with `e_p = 1`; at a
prefix prime nonzero, of even valuation `2j < e_p`, with a square unit part).
Let `1 ≤ b ≤ K − 1` (`b ≠ 0` in `ℤ/Kℤ`; `b = 0` is the interval `I_K`), `s ∈ ℤ/M₀ℤ`, and let
`r ∈ ℤ/M₀ℤ` be a nonvanishing square class (`def:nonvanishing-square-class`,
`IsNonvanishingSquareClass`). Let `G_u = g^{I_b, M₀, s}`, `G_v = g^{I_{b+1}, M₀, s+r}`, and
let `G_w` (`w ≠ u, v`) be inputs of `def:record:functional`. Then
`|∫ ∏_w G_w(z_w) dϱ(z)| ≤ 2 C_can L^{-σ} α`.

Specialisation (recorded in the report): the prefix blocks are merged into one atom
(`X_pre` is the prefix together with the tail primes below `P₅`), and the inputs `G_w` at the
other slots range over `IsQueryInput` (`F_A` and the `g^{I_b, M₀, s}`), which is all that the
coupled forms use; so the paper's lemma implies this statement. The paper's intermediate
bound `C_can N^{72δ} α (N^{-γ t_an} + N^{-1/120 + t_an(1/2−γ)})` is WP-K's
`Sarkozy.Cancellation.density_can_stage`. -/
def DensityCancellation (P5 : ℕ) (pp ep : J₀ → ℕ) : Prop :=
  ∃ Ccan : ℝ, 0 ≤ Ccan ∧ ∃ Lstar : ℕ, ∀ L : ℕ, Lstar ≤ L → ∀ A : Finset ℤ,
    Admissible (blockScale * L) A →
    ∀ ϱ : ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b),
    (∀ b, HasUniformMarginals (ϱ b)) →
    ∀ u v : Slot, u ≠ v →
    (∀ j : J L, P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (Sum.inr j)) u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (Sum.inr j)) {u, v}) →
    (∀ b : BlockAtom Bk J L, (∀ j, b = Sum.inr j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ blk p pp ep L b (z u) (z v)) →
    ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
    IsNonvanishingSquareClass (modulus pr h) r →
    ∀ G : Slot → (∀ b, BlockLabel m₀ blk p L b) → ℝ,
    G u = indexInputAt m₀ blk p pr h L A (bI, s) →
    G v = indexInputAt m₀ blk p pr h L A (bI + 1, s + r) →
    (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ blk p pr h L A (G w)) →
    |multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b).weight) G| ≤
      remainder (2 * Ccan) L A

end DensityCan

/-! ## Nonvanishing square classes in CRT coordinates -/

/-! ## Unfolding a coupled form -/

section Unfolding

variable {E : Type} {Ωi : Type} {X : Type}

open Classical in
/-- The slot function of a product half-function at the plus-half slot `v`: the input of the
query whose source is `v`, or `F` if there is none. -/
noncomputable def halfInput (u : E → reservedCut.Half) (φ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω : E → Ωi) (v : reservedCut.Half) : X → ℝ :=
  if hv : ∃ e, u e = v then φ hv.choose (ω hv.choose) else F

end Unfolding

/-! ## Product components and the index kernels -/

/-! ## The nonwrapping terms are cancellation remainders -/

section Main

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

namespace ComparisonData

/-- **The nonwrapping terms of `lem:record:wrap-expansion` are cancellation remainders**
(the step "Nonwrapping terms" of its proof). If `lem:record:density-can` holds
(`DensityCancellation`, at the threshold `P₅` of (CP1) and the prefix data of (CP0)) and the
coefficients of the product components are bounded, `∏_𝔟 ∑_i |c_{𝔟,i}| ν_{𝔟,i}(1) ≤ C_ν` at
every scale (the paper bounds them by `𝔳_ν e^{P+S}`), then every coupled form
`I_{ν,𝒮,𝒲}` with `𝒲 ⊊ 𝒮` is at most `C_ν · 2 C_can L^{-σ} α`. The proof: pick a
nonwrapping active query `e ∈ 𝒮 \ 𝒲`; every pair of indices `(ω, ω')` charged by the
coupled transition has `1 ≤ b_e ≤ K − 1` and `ω'_e = (b_e + 1, s_e + r_e)` with `r_e` a
nonvanishing square class ((CP0)(d)); the cut form is the multilinear integral of the slot
inputs (`form_productHalf`), with `g^{I_{b_e}, M₀, s_e}` at `u_e` and
`g^{I_{b_e+1}, M₀, s_e + r_e}` at `v_e`; each product component of `ν` is a product of
probability laws satisfying (a), (b) of `lem:record:density-can` by (CP4)(a); and the
coupled transition is substochastic. -/
theorem nonwrappingCancellation_of_densityCancellation (D : ComparisonData a m₀ blk p pr h E)
    (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hcoef : ∃ Cν : ℝ, ∀ L, ∏ b, ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i ≤ Cν) :
    D.NonwrappingCancellation hcop := by
  obtain ⟨Ccan, hCcan, Lstar, hDC⟩ := hDC
  obtain ⟨Cν, hCν⟩ := hcoef
  have hCν0 : 0 ≤ Cν := le_trans (prod_nonneg fun b _ => sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (D.CL.cmass_pos 0 b i).le) (hCν 0)
  refine ⟨Cν * (2 * Ccan), mul_nonneg hCν0 (by positivity), ?_⟩
  unfold Param.AtCounterexamples
  filter_upwards [eventually_ge_atTop Lstar] with L hL
  intro C _ _ A hA _ S W hWS hne
  obtain ⟨e, heS, heW⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hWS, hne⟩)
  rw [remainder_mul]
  have hrem0 : 0 ≤ remainder (2 * Ccan) L A := remainder_nonneg (by positivity) L A
  have hB0 : 0 ≤ Cν * remainder (2 * Ccan) L A := mul_nonneg hCν0 hrem0
  -- the coupled transition is substochastic
  have hfac : ∀ e' : E,
      (∀ x y, 0 ≤ (if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) x y) ∧
      ∀ x, ∑ y, (if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) x y ≤ 1 := by
    intro e'
    split_ifs
    · exact coordTransitionWith_substochastic pr h (wrapShift_substochastic blockScale)
        (D.S.index.hμ e') (D.S.index.hμ1 e')
    · exact coordTransitionWith_substochastic pr h (nowrapShift_substochastic blockScale)
        (D.S.index.hμ e') (D.S.index.hμ1 e')
    · exact meanMatrix_substochastic _
  have hK := piKron_substochastic _ (fun e' => (hfac e').1) (fun e' => (hfac e').2)
  -- the bound at one pair of indices charged by the coupled transition
  have hbound : ∀ ω η : E → ∀ j, CoordSpace blockScale pr h j,
      piKron (fun e' => if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η ≠ 0 →
      |reservedCut.form (tensorLaw (D.CL.ν L))
          (productHalf D.S.Q.u (fun e => blockInput m₀ blk p pr h hcop L A e)
              (blockLift m₀ blk p L A) ω)
          (productHalf D.S.Q.w (fun e => blockInput m₀ blk p pr h hcop L A e)
              (blockLift m₀ blk p L A) η)| ≤
        Cν * remainder (2 * Ccan) L A := by
    intro ω η hk
    have he := (prod_ne_zero_iff.mp hk) e (mem_univ e)
    beta_reduce at he
    rw [ite_eq_right heW, ite_eq_left heS] at he
    obtain ⟨hb, hη, hr⟩ := nowrap_support pr h he
    set r : ∀ q, ZMod (pr q ^ h q) := fun q => η e (some q) - ω e (some q) with hrdef
    have hrsq : ∀ q, IsNonvanishingSquareCoord (pr q) (h q) (r q) :=
      fun q => D.S.index.hsq e q _ (hr q)
    have hst : D.S.Q.source e ≠ D.S.Q.target e := by
      intro heq
      have h1 : D.S.Q.source e ∈ reservedCut.half := (D.S.Q.u e).2
      have h2 : D.S.Q.target e ∉ reservedCut.half := reservedCut.flip_not_mem (D.S.Q.w e).2
      exact h2 (heq ▸ h1)
    rw [form_productHalf _ D.S.Q.hu D.S.Q.hw]
    have hcomp := abs_multilinear_le_components (fun b i => D.CL.cc L b i * D.CL.cmass L b i)
      (D.CL.claw L)
      (pairInputs D.S.Q.u D.S.Q.w (fun e => blockInput m₀ blk p pr h hcop L A e)
        (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A) ω η)
      (M := remainder (2 * Ccan) L A) (fun σ => by
        refine hDC L hL A hA (fun b => D.CL.claw L b (σ b)) (fun b => D.CL.unif L b (σ b))
          (D.S.Q.source e) (D.S.Q.target e) hst
          (fun j hj => (D.CL.mixing L j (σ (Sum.inr j)) hj).2 e)
          (fun b _ z hz => D.CL.accept L b (σ b) z hz e)
          ((crtEquiv blockScale pr h hcop).symm (ω e)).1
          ((crtEquiv blockScale pr h hcop).symm (ω e)).2
          ((ZMod.prodEquivPi (fun q => pr q ^ h q) hcop).symm r) hb
          (isNonvanishingSquareClass_crt pr h hcop D.S.pr_prime D.S.pr_inj D.S.h_two r hrsq)
          _ ?_ ?_ ?_
        · show pairInputs D.S.Q.u D.S.Q.w _ _ _ ω η ((D.S.Q.u e : Slot)) = _
          rw [pairInputs_plus, halfInput_source D.S.Q.hu]
          rfl
        · show pairInputs D.S.Q.u D.S.Q.w _ _ _ ω η (reservedCut.flip (D.S.Q.w e : Slot)) = _
          rw [pairInputs_minus, halfInput_source D.S.Q.hw, atomInput_eq_indexInputAt, hη,
            crtEquiv_symm_nextIndex]
        · intro w' _ _
          rcases pairInputs_cases D.S.Q.u D.S.Q.w (fun e => blockInput m₀ blk p pr h hcop L A e)
              (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A) ω η w' with
            h1 | ⟨e', h1⟩ | ⟨e', h1⟩
          · exact Or.inl h1
          · exact Or.inr ⟨(crtEquiv blockScale pr h hcop).symm (ω e'), h1⟩
          · exact Or.inr ⟨(crtEquiv blockScale pr h hcop).symm (η e'), h1⟩)
    refine hcomp.trans (mul_le_mul_of_nonneg_right ?_ hrem0)
    have habs : ∀ b, ∑ i, |D.CL.cc L b i * D.CL.cmass L b i| =
        ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i := fun b =>
      sum_congr rfl fun i _ => by rw [abs_mul, abs_of_pos (D.CL.cmass_pos L b i)]
    simp only [habs]
    exact hCν L
  -- assemble: the expectation over the indices and the sum over the coupled indices
  unfold blockWrapForm
  apply FiniteLaw.abs_expect_le_const
  intro ω
  have hact : act (piKron (fun e' => if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)))
        (productHalf D.S.Q.w (fun e => blockInput m₀ blk p pr h hcop L A e)
            (blockLift m₀ blk p L A)) ω =
      ∑ η, (piKron (fun e' => if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η) •
        productHalf D.S.Q.w (fun e => blockInput m₀ blk p pr h hcop L A e)
            (blockLift m₀ blk p L A) η := by
    funext a
    simp only [act, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hact, ← cutBilin_apply, map_sum]
  simp only [map_smul, cutBilin_apply, smul_eq_mul]
  calc |∑ η, _ * _| ≤ ∑ η : E → ∀ j, CoordSpace blockScale pr h j, |_ * _| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ η : E → ∀ j, CoordSpace blockScale pr h j,
          piKron (fun e' => if e' ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
          else if e' ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η *
            (Cν * remainder (2 * Ccan) L A) := by
        apply sum_le_sum
        intro η _
        rw [abs_mul, abs_of_nonneg (hK.1 ω η)]
        by_cases hk : piKron (fun e' => if e' ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
          else if e' ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η = 0
        · rw [hk, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hbound ω η hk) (hK.1 ω η)
    _ = (∑ η : E → ∀ j, CoordSpace blockScale pr h j,
          piKron (fun e' => if e' ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
          else if e' ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η) *
            (Cν * remainder (2 * Ccan) L A) := by rw [sum_mul]
    _ ≤ 1 * (Cν * remainder (2 * Ccan) L A) := mul_le_mul_of_nonneg_right (hK.2 ω) hB0
    _ = Cν * remainder (2 * Ccan) L A := one_mul _

end ComparisonData

end Main

/-! ## The coefficients of the product components (the mass of `ν`) -/

section Coefficients

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

namespace ComparisonData

variable (D : ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
theorem one_le_selectionFactor (ha : 0 ≤ a) (L : ℕ) (b : BlockAtom Bk J L) :
    1 ≤ selectionFactor a p D.S.selPre L b := by
  cases b with
  | inl β => exact D.S.one_le_selPre β
  | inr j =>
      exact Real.one_le_rpow (by exact_mod_cast (D.S.p_prime L j).one_lt.le)
        (mul_nonneg zero_le_two ha)

omit [DecidableEq P] in
theorem mass_refLaw (L : ℕ) (b : BlockAtom Bk J L) : mass (D.R.law p L b) = 1 := by
  cases b with
  | inl β => exact mass_signedIntegral (D.R.μ₀ β)
  | inr j => exact mass_signedIntegral (D.R.μp (p L j))

omit [DecidableEq P] in
/-- On a first-stage atom `λ_𝔟(1) = 1 + (ρ_𝔟 − μ_𝔟)(1) ≤ 1 + p_𝔟`: the record differences of
(CP2)(b) have mass zero. -/
theorem mass_lam_le (ha : 0 ≤ a) (L : ℕ) (b : BlockAtom Bk J L) : mass
    (D.FS.lam L b) ≤ 1 + D.FS.pvar L b := by
  have hlam : mass (D.FS.lam L b) = mass (D.FS.ρ L b) := by
    unfold FirstStage.lam mass
    rw [LinearMap.add_apply, LinearMap.sum_apply]
    have h0 : ∀ i, (D.FS.κ' L b i - D.FS.κ L b i) (fun _ => 1) = 0 := fun i => by
      rw [LinearMap.sub_apply]
      exact sub_eq_zero.mpr (D.FS.mass_eq L b i)
    simp only [h0, sum_const_zero, add_zero]
  have hρ := congrArg mass (D.FS.ρ_sub L b)
  have hμ := D.mass_refLaw L b
  unfold mass at hρ hμ hlam ⊢
  rw [LinearMap.sub_apply, LinearMap.sum_apply, hμ] at hρ
  simp only [LinearMap.smul_apply, smul_eq_mul] at hρ
  rw [hlam]
  unfold FirstStage.pvar
  have hle : ∑ i, D.FS.ca L b i * D.FS.κa L b i (fun _ => 1) ≤
      ∑ i, |D.FS.ca L b i| * mass (D.FS.κa L b i) * selectionFactor a p D.S.selPre L b := by
    apply sum_le_sum
    intro i _
    have hm : 0 ≤ mass (D.FS.κa L b i) := mass_nonneg_of_nonneg (D.FS.κa_pos L b i).1
    calc D.FS.ca L b i * D.FS.κa L b i (fun _ => 1)
        ≤ |D.FS.ca L b i| * mass (D.FS.κa L b i) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hm
      _ ≤ |D.FS.ca L b i| * mass (D.FS.κa L b i) * selectionFactor a p D.S.selPre L b :=
          le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) hm) (D.one_le_selectionFactor ha L b)
  linarith

omit [DecidableEq P] in
/-- The mass of `ν_𝔟`: `ν_𝔟(1) ≤ 1 + p_𝔟 + s_𝔟` (the skew parts have mass zero and the
bracket of (CP4)(b) at the all-ones vector gives `|ζ^s_{𝔟,t}(1)| ≤ π̃^s_{𝔟,t}`). -/
theorem mass_nu_le (ha : 0 ≤ a) (L : ℕ) (b : BlockAtom Bk J L) :
    mass (D.CL.ν L b) ≤ 1 + D.FS.pvar L b + symTotal (D.CL.π L) b := by
  have hch := congrArg mass (D.CL.change L b)
  have hsum : mass (∑ t, D.CL.Δ L b t) = ∑ t, mass (D.CL.ζ L b t .sym) := by
    unfold mass
    rw [LinearMap.sum_apply]
    apply sum_congr rfl
    intro t _
    have h1 := symPart_add_skewPart reservedCut (D.CL.Δ L b t)
    have h2 := mass_skewPart (D.CL.Δ L b t)
    unfold mass at h2
    rw [← h1, LinearMap.add_apply, h2, add_zero]
    rfl
  have hν : mass (D.CL.ν L b) = mass (D.FS.lam L b) + ∑ t, mass (D.CL.ζ L b t .sym) := by
    rw [← hsum, ← hch]
    unfold mass
    rw [LinearMap.sub_apply]
    unfold ComparisonLaw.ν
    ring
  have hζ : ∀ t, mass (D.CL.ζ L b t .sym) ≤ D.CL.π L b t .sym := fun t => by
    have h1 := abs_mass_le_of_bracket (D.CL.πt_nonneg L b t .sym) (D.CL.D_prob L b t .sym).2
      (D.CL.bracket L b t .sym)
    calc mass (D.CL.ζ L b t .sym) ≤ D.CL.πt L b t .sym := (le_abs_self _).trans h1
      _ ≤ D.CL.π L b t .sym :=
          le_mul_of_one_le_right (D.CL.πt_nonneg L b t .sym) (D.one_le_selectionFactor ha L b)
  rw [hν]
  have := D.mass_lam_le ha L b
  have hs : ∑ t, mass (D.CL.ζ L b t .sym) ≤ symTotal (D.CL.π L) b := sum_le_sum fun t _ => hζ t
  linarith

omit [DecidableEq P] in
theorem mass_nu_eq (L : ℕ) (b : BlockAtom Bk J L) :
    mass (D.CL.ν L b) = ∑ i, D.CL.cc L b i * D.CL.cmass L b i := by
  unfold ComparisonLaw.ν
  unfold mass
  rw [LinearMap.sum_apply]
  apply sum_congr rfl
  intro i _
  rw [LinearMap.smul_apply, smul_eq_mul]
  have h1 := mass_signedIntegral (D.CL.claw L b i)
  unfold mass at h1
  rw [h1, mul_one]

omit [DecidableEq P] in
/-- **The coefficients of the product components** (proof of `lem:record:wrap-expansion`,
"The mass of `ν`"): `∏_𝔟 |ν|_𝔟 ≤ 𝔳_ν ν(1) ≤ 𝔳_ν e^{P+S}`, at every scale. -/
theorem coefficient_bound (ha : 0 ≤ a) (L : ℕ) :
    ∏ b, ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i ≤ D.CL.vfac * Real.exp (D.FS.P + D.CL.S) := by
  have hpos : ∀ b, 0 < ∑ i, D.CL.cc L b i * D.CL.cmass L b i := D.CL.mass_pos L
  have hsplit : ∏ b, ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i =
      (∏ b, (∑ i, |D.CL.cc L b i| * D.CL.cmass L b i) / (∑ i, D.CL.cc L b i * D.CL.cmass L b i)) *
        ∏ b, ∑ i, D.CL.cc L b i * D.CL.cmass L b i := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b _ => (div_mul_cancel₀ _ (hpos b).ne').symm
  rw [hsplit]
  have hratio0 : 0 ≤ ∏ b, (∑ i, |D.CL.cc L b i| * D.CL.cmass L b i) /
      (∑ i, D.CL.cc L b i * D.CL.cmass L b i) :=
    prod_nonneg fun b _ => div_nonneg (sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (D.CL.cmass_pos L b i).le) (hpos b).le
  have hvfac0 : 0 ≤ D.CL.vfac := hratio0.trans (D.CL.vfac_bound L)
  have hsym0 : ∀ b, 0 ≤ symTotal (D.CL.π L) b := fun b => sum_nonneg fun t _ =>
    mul_nonneg (D.CL.πt_nonneg L b t .sym) (D.selectionFactor_nonneg L b)
  have hmass : ∏ b, ∑ i, D.CL.cc L b i * D.CL.cmass L b i ≤ Real.exp (D.FS.P + D.CL.S) := by
    calc ∏ b, ∑ i, D.CL.cc L b i * D.CL.cmass L b i
        ≤ ∏ b, Real.exp (D.FS.pvar L b + symTotal (D.CL.π L) b) := by
          apply prod_le_prod₀ (fun b _ => (hpos b).le)
          intro b _
          have h1 := D.mass_nu_le ha L b
          rw [D.mass_nu_eq L b] at h1
          have h2 := Real.add_one_le_exp (D.FS.pvar L b + symTotal (D.CL.π L) b)
          linarith
      _ = Real.exp (∑ b, (D.FS.pvar L b + symTotal (D.CL.π L) b)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (D.FS.P + D.CL.S) := by
          apply Real.exp_le_exp.mpr
          rw [sum_add_distrib]
          exact add_le_add (D.FS.P_total L) (D.CL.S_total L)
  exact mul_le_mul (D.CL.vfac_bound L) hmass (prod_nonneg fun b _ => (hpos b).le) hvfac0

end ComparisonData

end Coefficients

section Corollaries

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

namespace ComparisonData

/-- **The nonwrapping terms from `lem:record:density-can` alone**: with the coefficient bound
`𝔳_ν e^{P+S}` of the proof of `lem:record:wrap-expansion` (`coefficient_bound`), the
hypothesis `NonwrappingCancellation` of Theorem C follows from `DensityCancellation`. -/
theorem nonwrappingCancellation_of_densityCancellation' (D : ComparisonData a m₀ blk p pr h E)
    (ha : 0 ≤ a)
    (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep) :
    D.NonwrappingCancellation hcop :=
  D.nonwrappingCancellation_of_densityCancellation hcop hDC ⟨_, D.coefficient_bound ha⟩

/-- **Theorem C with `lem:record:density-can` as the analytic input of the nonwrapping
terms** (`theoremC` with `NonwrappingCancellation` replaced by `DensityCancellation`). -/
theorem theoremC_of_densityCancellation (hP : (Params.ofDecay a).Valid)
    (D : ComparisonData a m₀ blk p pr h E) (ha : 0 ≤ a) {𝓔 : ℝ}
    (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1) (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) :=
  D.theoremC hcop hP h𝓔 hΘ hE1 hSF
      (D.nonwrappingCancellation_of_densityCancellation' hcop ha hDC) hwr
    henv hunit

end ComparisonData

end Corollaries

end Sarkozy.TheoremCBlock

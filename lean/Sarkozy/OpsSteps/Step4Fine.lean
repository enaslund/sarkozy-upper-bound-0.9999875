module

public import Sarkozy.OpsSteps.FineGroup
public import Sarkozy.EnvelopesPaper.Matching

@[expose] public section

/-!
# Step 4 in form (i) of `thm:envelopes`, assembled (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 4 and "(iii) and (i)";
`lem:oct24:invariant-background`(v).

**`step4_fine`**: the field `step4` of B11's `DegreeOps` with the background
`W_Z = (∑_ω π̃_ω C_X (κ_H(ω) e^{U₀} − (κ_H(ω) − κ_b(ω)) e^{tU})) Y` (the paper's (i)), from

* the averaging inputs (`ha`, `hinv`, `hK`); the positivity of `Ñ^inv`, `G` is proved
  (`NinvOf_positive`, `GOf_positive`);
* the caps: `κ_b(ω)` on the invariant monomials (after the additional averages, `hextra`) and
  `κ_H(ω)` elsewhere (`hcap`, `lem:oct24:mask-schur`(b));
* the upper prices `m ≥ v`, `n ≥ w` with `∑ m = tU`, `∑(m + n) ≤ U₀`
  (`lem:oct24:invariant-background`(v), F);
* the identification of the diagonals with the norm envelopes (`hD`).

The finer (E1) is **proved** (`FineGroup.hfine_of_fine`); the remainders
`r₄ = ∑_ω π̃ ∑_Z cap ∑_{g ∈ T(Z)} fX` are summed by **`step4_fine_rem`** (`fX_summable`).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.E1Closure Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
  (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)

omit [DecidableEq P] in
theorem finePr_nonneg (b : BlockAtom Bk PaperJt L) (o : Option (D.CL.T L b × ChangeType))
    (y : Option Bool) : 0 ≤ finePr D L isG b o y := by
  rcases y with _ | g
  · exact zero_le_one
  · unfold finePr
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
        (isPositiveRecord_sum _ _ fun i _ => D.GB.κu_pos L b i).1) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
/-- **`G = ∑_{isG} κu ⪰_ι 0`** (`def:cp3`: positive reserved-diagonal records). -/
theorem GOf_positive (b : BlockAtom Bk PaperJt L) : reservedCut.Positive (GOf D L isG b) :=
  ReflectionCut.Positive.sum _ fun i _ =>
    EnvelopesPaper.positive_of_nonneg_diagonal (D.GB.κu_pos L b i).1 (D.GB.κu_diag L b i)

omit [DecidableEq P] in
/-- **`Ñ^inv = μ + ∑_{¬isG} κu ⪰_ι 0`** (`lem:oct24:invariant-background`(iv) for this split). -/
theorem NinvOf_positive (b : BlockAtom Bk PaperJt L) : reservedCut.Positive (NinvOf D L isG b) :=
  (D.law_positive (Or.inr (Or.inr rfl)) L b).add (ReflectionCut.Positive.sum _ fun i _ =>
    EnvelopesPaper.positive_of_nonneg_diagonal (D.GB.κu_pos L b i).1 (D.GB.κu_diag L b i))

/-- The cap of the outside set `Z`: `κ_b` on the invariant monomials (`Z = ∅`), `κ_H` elsewhere. -/
noncomputable def capZ {S : Finset (BlockAtom Bk PaperJt L)} (κH κb : ℝ)
    (f : {b // b ∉ S} → Bool) : ℝ :=
  if f = (fun _ => false) then κb else κH

omit [DecidableEq P] in
/-- **Step 4 in form (i)** (see the module docstring). -/
theorem step4_fine (A : Finset ℤ) (S : Finset (BlockAtom Bk PaperJt L)) (hY : 0 ≤ D.Y L A)
    (hR : ZMod 6) (hinv : ∀ b ∉ S, slotPush (slotREquiv hR) (D.GB.N₀ L b) = D.GB.N₀ L b)
    (𝒞 : Finset (Choice (D.CL.T L))) (hS : ∀ ω ∈ 𝒞, Choice.support ω = S)
    (bar : Choice (D.CL.T L) → Choice (D.CL.T L)) (hbar𝒞 : ∀ ω ∈ 𝒞, bar ω ∈ 𝒞)
    (hbar : ∀ ω ∈ 𝒞, bar (bar ω) = ω) (wt : Choice (D.CL.T L) → ℝ)
    (hwtb : ∀ ω ∈ 𝒞, wt (bar ω) = wt ω) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (O : {b // b ∈ S} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (mb : ∀ b, O b → ℝ)
    (φb : Choice (D.CL.T L) → ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    (hD : ∀ ω ∈ 𝒞, ∀ b (hb : b ∈ S), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (mb ⟨b, hb⟩) (φb ω ⟨b, hb⟩)) = D.CL.D L b t e)
    (ψ : Choice (D.CL.T L) → (∀ b, O b) ≃ (∀ b, O b))
    (hm : ∀ ω ∈ 𝒞, ∀ x, prodWeight mb (ψ ω x) = prodWeight mb x)
    (ha : ∀ ω ∈ 𝒞, ∀ x, (fun v => prodPlace reservedCut (φb (bar ω)) x
        (halfPerm reservedCut (slotREquiv hR) (slotR_half hR) v)) =
      prodPlace reservedCut (φb ω) (ψ ω x))
    (T : Choice (D.CL.T L) →
      (((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)) →ₗ[ℝ] (((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)))
    (K : Choice (D.CL.T L) → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hK : ∀ ω ∈ 𝒞, K (bar ω) = T ω (K ω))
    (Kx : Choice (D.CL.T L) → ({b // b ∉ S} → Bool) → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (κH κb : Choice (D.CL.T L) → ℝ) {κM : ℝ}
    (hκb : ∀ ω ∈ 𝒞, 0 ≤ κb ω) (hκbH : ∀ ω ∈ 𝒞, κb ω ≤ κH ω) (hκM : ∀ ω ∈ 𝒞, κH ω ≤ κM)
    (hextra : ∀ ω ∈ 𝒞, ∀ f, paperEO L A S (NinvOf D L isG) (GOf D L isG) f
      (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω))
        ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))) =
        paperEO L A S (NinvOf D L isG) (GOf D L isG) f
          (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω)) (Kx ω f)))
    (hcap : ∀ ω ∈ 𝒞, ∀ f, OpLE (prodWeight mb) (Kx ω f) (capZ L (κH ω) (κb ω) f • LinearMap.id))
    {m n : {b // b ∉ S} → ℝ} {U₀ tU z : ℝ}
    (hvm : ∀ c, finePr D L isG c.1 none (some false) ≤ m c)
    (hwn : ∀ c, finePr D L isG c.1 none (some true) ≤ n c)
    (hmt : ∑ c, m c = tU) (hU : ∑ c, (m c + n c) ≤ U₀)
    (hz : sfEps D L * κM * Real.exp U₀ ≤ z)
    (YN0 : Choice (D.CL.T L) → ℝ)
    (hYN0 : ∀ ω ∈ 𝒞, YN0 ω = paperEN0 D L A S
      (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω)) (K ω))) :
    ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤
      (∑ ω ∈ 𝒞, wt ω * (∏ b ∈ Choice.support ω,
          TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU)) * D.Y L A +
        z * (∑ ω ∈ 𝒞, wt ω * (∏ b ∈ Choice.support ω,
          TheoremCBlock.selectionFactor a paperTail D.S.selPre L b)) * D.Y L A +
        ∑ ω ∈ 𝒞, wt ω * ∑ f : {b // b ∉ S} → Bool, capZ L (κH ω) (κb ω) f *
          ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g := by
  set CX : Choice (D.CL.T L) → ℝ :=
    fun ω => ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b
    with hCX
  refine step4_of_caps_finset D L A S hR hinv 𝒞 bar hbar𝒞 hbar wt hwtb hwt (prodWeight mb)
    (fun ω => prodPlace reservedCut (φb ω)) ψ hm ha T K hK (NinvOf D L isG) (GOf D L isG)
    (fun b _ => N₀_eq_split D L isG b) (fun b _ => NinvOf_positive D L isG b)
    (fun b _ => GOf_positive D L isG b) Kx (fun ω f => capZ L (κH ω) (κb ω) f) hextra
    hcap CX YN0 hYN0 ?_
  exact heval_of_finer 𝒞 wt CX κH κb
    (fun ω f => paperEO L A S (NinvOf D L isG) (GOf D L isG) f
      (reservedCut.diagonalLaw (push (prodWeight mb) (prodPlace reservedCut (φb ω)))))
    (fun ω f => ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g)
    (v := fun c => finePr D L isG c.1 none (some false))
    (w := fun c => finePr D L isG c.1 none (some true))
    (fun c => finePr_nonneg D L isG c.1 none _) (fun c => finePr_nonneg D L isG c.1 none _)
    hvm hwn hmt hU (sfEps_nonneg D L) hwt
    (fun ω _ => mul_nonneg (prod_nonneg fun b _ => D.selectionFactor_nonneg L b) hY)
    hκb hκbH hκM hz
    (fun ω hω f => hfine_of_fine D L isG (sfEps D) A ω S (hS ω hω) O mb (φb ω) (hD ω hω) f)

omit [DecidableEq P] in
/-- **The remainders of Step 4 (i) sum to a remainder**: on the paper's tails there is `c ≥ 0` such
that at every least counterexample, for every split `isG`, every set `𝒞` of selections, weights
`0 ≤ w ≤ K₁ π̃` and caps `0 ≤ κ_b ≤ κ_H ≤ κ_M` (`0 ≤ κ_M`),
`∑_ω w_ω ∑_Z cap_Z ∑_{g ∈ T(Z)} fX ≤ κ_M K₁ c L^{-σ} α`. -/
theorem step4_fine_rem
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)
        (S : Finset (BlockAtom Bk PaperJt L)) (𝒞 : Finset (Choice (D.CL.T L))),
      (∀ ω ∈ 𝒞, IsSelection ω) →
      ∀ (wt : Choice (D.CL.T L) → ℝ) (K₁ : ℝ), 0 ≤ K₁ → (∀ ω ∈ 𝒞, 0 ≤ wt ω) →
      (∀ ω ∈ 𝒞, wt ω ≤ K₁ * monomial (D.CL.πt L) ω) →
      ∀ (κH κb : Choice (D.CL.T L) → ℝ) (κM : ℝ), 0 ≤ κM →
      (∀ ω ∈ 𝒞, 0 ≤ κb ω) → (∀ ω ∈ 𝒞, κb ω ≤ κH ω) → (∀ ω ∈ 𝒞, κH ω ≤ κM) →
      ∑ ω ∈ 𝒞, wt ω * ∑ f : {b // b ∉ S} → Bool, capZ L (κH ω) (κb ω) f *
          ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g ≤
        remainder (κM * K₁ * c) L A) := by
  obtain ⟨c, hc, hsum⟩ := fX_summable D hpair ha hpar hsel hne
  refine ⟨c, hc, ?_⟩
  filter_upwards [hsum] with L hL
  intro C hC hk A hA hY isG S 𝒞 h𝒞 wt K₁ hK₁ hwt0 hwt κH κb κM hM0 hκb hκbH hκM
  have hS := hL C hC hk A hA hY isG
  have hX0 : ∀ ω g, 0 ≤ fX D L isG (sfEps D) A ω g := fun ω g => le_max_left _ _
  have hper : ∀ ω ∈ 𝒞, wt ω * ∑ f : {b // b ∉ S} → Bool, capZ L (κH ω) (κb ω) f *
      ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g ≤
      (κM * K₁) * (monomial (D.CL.πt L) ω *
        ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g) := by
    intro ω hω
    have hcap : ∀ f : {b // b ∉ S} → Bool, capZ L (κH ω) (κb ω) f ≤ κM := fun f => by
      unfold capZ
      split_ifs
      · exact (hκbH ω hω).trans (hκM ω hω)
      · exact hκM ω hω
    have hcap0 : ∀ f : {b // b ∉ S} → Bool, 0 ≤ capZ L (κH ω) (κb ω) f := fun f => by
      unfold capZ
      split_ifs
      · exact hκb ω hω
      · exact (hκb ω hω).trans (hκbH ω hω)
    have h1 : ∑ f : {b // b ∉ S} → Bool, capZ L (κH ω) (κb ω) f *
        ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g ≤
        κM * ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g := by
      calc _ ≤ ∑ f : {b // b ∉ S} → Bool, κM *
            ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g :=
            sum_le_sum fun f _ => mul_le_mul_of_nonneg_right (hcap f)
              (sum_nonneg fun g _ => hX0 ω g)
        _ = κM * ∑ f : {b // b ∉ S} → Bool,
            ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g := by
            rw [mul_sum]
        _ ≤ _ := mul_le_mul_of_nonneg_left (sum_rZ_le D L isG (sfEps D) A ω S) hM0
    have hs0 : 0 ≤ ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g :=
      sum_nonneg fun g _ => hX0 ω g
    calc _ ≤ wt ω * (κM * ∑ g : BlockAtom Bk PaperJt L → Option Bool,
          fX D L isG (sfEps D) A ω g) := mul_le_mul_of_nonneg_left h1 (hwt0 ω hω)
      _ ≤ (K₁ * monomial (D.CL.πt L) ω) * (κM * ∑ g : BlockAtom Bk PaperJt L → Option Bool,
          fX D L isG (sfEps D) A ω g) :=
          mul_le_mul_of_nonneg_right (hwt ω hω) (mul_nonneg hM0 hs0)
      _ = _ := by ring
  have hsub : 𝒞 ⊆ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω) :=
    fun ω hω => mem_filter.mpr ⟨mem_univ _, h𝒞 ω hω⟩
  calc _ ≤ ∑ ω ∈ 𝒞, (κM * K₁) * (monomial (D.CL.πt L) ω *
        ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g) :=
        sum_le_sum hper
    _ ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), (κM * K₁) *
        (monomial (D.CL.πt L) ω *
          ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g) :=
        sum_le_sum_of_subset_of_nonneg hsub fun ω _ _ => mul_nonneg (mul_nonneg hM0 hK₁)
          (mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (sum_nonneg fun g _ => hX0 ω g))
    _ = (κM * K₁) * ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          ∑ g : BlockAtom Bk PaperJt L → Option Bool, fX D L isG (sfEps D) A ω g := by
        rw [mul_sum]
    _ ≤ (κM * K₁) * remainder c L A := mul_le_mul_of_nonneg_left hS (mul_nonneg hM0 hK₁)
    _ = remainder (κM * K₁ * c) L A := by unfold remainder; ring

end Sarkozy.OpsSteps

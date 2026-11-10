module

public import Sarkozy.OpsSteps.E1Diag
public import Sarkozy.OpsSteps.Step3

@[expose] public section

/-!
# B11's `paperDegreeOps` with `hE1` and `step3` discharged (OPS-S)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i), Steps 1 and 3.

**`paperDegreeOpsS`** is B11's `paperDegreeOps` at product objects
(`Obj ω = ∏_{𝔟 ∈ X} O_{ω,𝔟}`, `m_ω = ⊗ m_{ω,𝔟}`, `φ_ω = ∏ φ_{ω,𝔟}`, as in the paper), in which

* `hE1` is **proved** by `hE1_of_envelope`, with `B = e^{U₀} + R_err` (`D.B`),
  `C_X = ∏_{𝔟 ∈ X} q_𝔟^{2a}` and `r₁' = r_E`, from the envelope bound of the selections at the
  counterexample (`hEB`, the first part of `ComparisonData.EnvelopeBoundNonneg`, proved at the
  paper's data by `envelopeBoundNonneg_front`), `ε_E ≤ z`, `Y ≥ 0`, and the identification
  `D^ε_{𝔟,t} = Diag_ι(m_{t,𝔟})` (`hD`, `def:cp4`(b));
* `step3` is **proved** by `step3_orbit`, with `Y^{Ñ₀}[[D_ω]]` (`YN0`), `M_ω = M(D_ω)`
  (`couplingMass`), `M_{h,ω} = M_h(D_ω)` (`orbitMass`) and `r₃ = ∑ |c(C)| r_C`, from the coupling
  expansion of `D_ω`, `R_{h*}[C] = [hC]`, the per-coupling bounds and the improved bound on the
  `R_h`-invariant orbit averages (`lem:orbit-coupon`(i)).

The other fields are B11's, unchanged; `step4` is stated on `YN0` (`Step4.step4_of_caps_finset`
reduces it). The construction type-checks, so the two theorems plug in as they are.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.Envelopes

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- `C_X = ∏_{𝔟 ∈ X} q_𝔟^{2a}` of a selection. -/
noncomputable abbrev cX (L : ℕ) (ω : Choice (D.CL.T L)) : ℝ :=
  ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b

omit [DecidableEq P] in
/-- **B11's `paperDegreeOps` with `hE1` and `step3` proved** (see the module docstring). -/
noncomputable def paperDegreeOpsS (L : ℕ) (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ 𝒞, IsSelection ω) (π ρ rr : Choice (D.CL.T L) → ℝ) (WZ z K : ℝ)
    (hY : 0 ≤ D.Y L A)
    -- the product objects
    (Ob : ∀ ω : Choice (D.CL.T L), {b // b ∈ Choice.support ω} → Type)
    [∀ ω b, Fintype (Ob ω b)] [∀ ω b, DecidableEq (Ob ω b)]
    (mb : ∀ ω b, Ob ω b → ℝ) (φb : ∀ ω b, Ob ω b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    -- the operators and B11's Steps 1–2 inputs
    (Lop Υop Dop : ∀ ω, ((∀ b, Ob ω b) → ℝ) →ₗ[ℝ] ((∀ b, Ob ω b) → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (prodWeight (mb ω)) (Lop ω) (Dop ω) ∧
      OpLE (prodWeight (mb ω)) (-Lop ω) (Dop ω))
    (υ : Choice (D.CL.T L) → ℝ) (hυ : ∀ ω ∈ 𝒞, 0 ≤ υ ω)
    (hΥsym : ∀ ω ∈ 𝒞, ∀ f g,
      ip (prodWeight (mb ω)) f (Υop ω g) = ip (prodWeight (mb ω)) g (Υop ω f))
    (hΥ : ∀ ω ∈ 𝒞, ∀ f, |ip (prodWeight (mb ω)) f (Υop ω f)| ≤ υ ω * ip (prodWeight (mb ω)) f f)
    -- (E1): the envelope bound and the identification of the norm envelopes
    (hD : ∀ ω ∈ 𝒞, ∀ b (hb : b ∈ Choice.support ω), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (mb ω ⟨b, hb⟩) (φb ω ⟨b, hb⟩)) = D.CL.D L b t e)
    {εE : ℝ} (rE : Choice (D.CL.T L) → ℝ) (hz : εE ≤ z)
    (hEB : ∀ ω : Choice (D.CL.T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) ≤
        (D.B + εE) * cX D L ω * D.Y L A + rE ω)
    -- (N4)
    (wt : Choice (D.CL.T L) → ℝ) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (hN4 : ∀ ω ∈ 𝒞, selTensor D L ω = wt ω •
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Lop ω) +
        place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Υop ω)))
    -- Step 3: the coupling expansion and the orbit coupon
    (ι : Choice (D.CL.T L) → Type) [∀ ω, Fintype (ι ω)] (coef : ∀ ω, ι ω → ℝ)
    (Cop : ∀ ω, ι ω → ((∀ b, Ob ω b) → ℝ) →ₗ[ℝ] ((∀ b, Ob ω b) → ℝ))
    (hDk : ∀ ω ∈ 𝒞, ∀ x y, kern (prodWeight (mb ω)) (Dop ω) x y =
      ∑ i, coef ω i * kern (prodWeight (mb ω)) (Cop ω i) x y)
    (hR : ZMod 6) (hC : ∀ ω, ι ω → ι ω) (hh : ∀ ω ∈ 𝒞, ∀ i, hC ω (hC ω i) = i)
    (hpush : ∀ ω ∈ 𝒞, ∀ i, slotPush (slotREquiv hR)
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i)) =
        place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω (hC ω i)))
    (Rerr z' tU tδ : ℝ) (hRerr : 0 ≤ Rerr) (htδ : 0 ≤ tδ) (r : ∀ ω, ι ω → ℝ)
    (herr : ∀ ω ∈ 𝒞, ∀ i,
      |paperEN D L A (Choice.support ω)
          (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i)) -
        paperEN0 D L A (Choice.support ω)
          (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i))| ≤
        (Rerr + z') * cX D L ω * D.Y L A + r ω i)
    (hsym : ∀ ω ∈ 𝒞, ∀ κ, slotPush (slotREquiv hR) κ = κ → ∀ i, κ = (1 / 2 : ℝ) •
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω i) +
        place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Cop ω (hC ω i))) →
      |paperEN D L A (Choice.support ω) κ - paperEN0 D L A (Choice.support ω) κ| ≤
        (Rerr - Real.exp tU * tδ + z') * cX D L ω * D.Y L A + r ω i)
    (hzc : ∀ ω ∈ 𝒞, couplingMass (coef ω) * z' ≤ z)
    -- Step 4 and the evaluations
    (r₄ M Minv : ℝ)
    (step4 : ∑ ω ∈ 𝒞, wt ω * paperEN0 D L A (Choice.support ω)
        (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Dop ω)) ≤
      WZ + z * (∑ ω ∈ 𝒞, wt ω * cX D L ω) * D.Y L A + r₄)
    (hM : ∑ ω ∈ 𝒞, wt ω * cX D L ω * couplingMass (coef ω) ≤ M * ∑ ω ∈ 𝒞, wt ω * cX D L ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * cX D L ω ≤
      ∑ ω ∈ 𝒞, wt ω * cX D L ω * orbitMass (hC ω) (coef ω))
    (hρ : (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * cX D L ω) +
      D.B * (∑ ω ∈ 𝒞, wt ω * υ ω * cX D L ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * cX D L ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, wt ω * (υ ω * rE ω + ∑ i, |coef ω i| * r ω i) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω) :
    DegreeOps reservedCut 𝒞 (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω)
      π ρ rr WZ (D.Y L A) z K :=
  paperDegreeOps D L A 𝒞 π ρ rr WZ z K (fun ω => ∀ b, Ob ω b) (fun ω => prodWeight (mb ω))
    (fun ω => prodPlace reservedCut (φb ω)) Lop Υop Dop hdom υ hυ hΥsym hΥ D.B (cX D L) rE
    (hE1_of_envelope D L A 𝒞 hsel Ob mb φb hD rE hz hY hEB) wt hwt hN4
    (fun ω => paperEN0 D L A (Choice.support ω)
      (place reservedCut (prodWeight (mb ω)) (prodPlace reservedCut (φb ω)) (Dop ω)))
    (fun ω => couplingMass (coef ω)) (fun ω => orbitMass (hC ω) (coef ω))
    (fun ω => ∑ i, |coef ω i| * r ω i) r₄ M Minv Rerr tU tδ hRerr htδ
    (fun ω hω => step3_orbit D L A (Choice.support ω) (prodWeight (mb ω))
      (prodPlace reservedCut (φb ω)) (coef ω) (Cop ω) (Dop ω) (hDk ω hω) hR (hC ω) (hh ω hω)
      (hpush ω hω) (r ω) (herr ω hω) (hsym ω hω) (hzc ω hω)
      (mul_nonneg (prod_selectionFactor_nonneg D L _) hY))
    step4 hM hMinv hρ hπ hrr

end Sarkozy.OpsSteps

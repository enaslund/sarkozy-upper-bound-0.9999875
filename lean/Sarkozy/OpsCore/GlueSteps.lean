module

public import Sarkozy.OpsCore.Evals
public import Sarkozy.OpsSteps.Plug

@[expose] public section

/-!
# Glue: OPS-S's `paperDegreeOpsS` at OPS-L's star objects (OPS-L)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i), Steps 1–3; `Sarkozy.OpsSteps.Plug`
(read-only). **`paperDegreeOpsL`** is OPS-S's `paperDegreeOpsS` (B11's `DegreeOps` with `hE1` and
`step3` proved from the envelope bound and the coupling expansion) at the product objects of the
half labellings (`Ob = HalfB`, `mb = selMarg`, `φb = id`). OPS-S's inputs `hN4`, `hΥ`, `hΥsym`
and `hD` are supplied by OPS-L (`StarOK.hN4`, `StarOK.hΥ`, `StarOK.hΥsym` from `LeadOK`, and
`hD_sel`). What remains: `LeadOK` per selection, the domination `hdom` (OPS-F), OPS-S's envelope
bound `hEB`, the coupling data, Step 4 and the evaluations.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.Envelopes Sarkozy.OpsSteps

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **OPS-S's `paperDegreeOpsS` at the star objects**: `hN4`, `hΥ`, `hΥsym`, `hD` from OPS-L. -/
noncomputable def paperDegreeOpsL (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ 𝒞, IsSelection ω) (π ρ rr : Choice (D.CL.T L) → ℝ) (WZ z K : ℝ)
    (hY : 0 ≤ D.Y L A)
    (G : ∀ ω, LeadData D L ω) (hG : ∀ ω ∈ 𝒞, LeadOK (G ω))
    (Dop : ∀ ω, (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ) →ₗ[ℝ]
      (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (G ω).star.m (G ω).star.Lop (Dop ω) ∧
      OpLE (G ω).star.m (-(G ω).star.Lop) (Dop ω))
    {εE : ℝ} (rE : Choice (D.CL.T L) → ℝ) (hz : εE ≤ z)
    (hEB : ∀ ω : Choice (D.CL.T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) ≤
        (D.B + εE) * cX D L ω * D.Y L A + rE ω)
    (ι : Choice (D.CL.T L) → Type) [∀ ω, Fintype (ι ω)] (coef : ∀ ω, ι ω → ℝ)
    (Cop : ∀ ω, ι ω → (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ) →ₗ[ℝ]
      (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ))
    (hDk : ∀ ω ∈ 𝒞, ∀ x y, kern (G ω).star.m (Dop ω) x y =
      ∑ i, coef ω i * kern (G ω).star.m (Cop ω i) x y)
    (hR : ZMod 6) (hC : ∀ ω, ι ω → ι ω) (hh : ∀ ω ∈ 𝒞, ∀ i, hC ω (hC ω i) = i)
    (hpush : ∀ ω ∈ 𝒞, ∀ i, slotPush (slotREquiv hR)
      (place reservedCut (G ω).star.m (G ω).star.φ (Cop ω i)) =
        place reservedCut (G ω).star.m (G ω).star.φ (Cop ω (hC ω i)))
    (Rerr z' tU tδ : ℝ) (hRerr : 0 ≤ Rerr) (htδ : 0 ≤ tδ) (r : ∀ ω, ι ω → ℝ)
    (herr : ∀ ω ∈ 𝒞, ∀ i,
      |paperEN D L A (Choice.support ω) (place reservedCut (G ω).star.m (G ω).star.φ (Cop ω i)) -
        paperEN0 D L A (Choice.support ω)
          (place reservedCut (G ω).star.m (G ω).star.φ (Cop ω i))| ≤
        (Rerr + z') * cX D L ω * D.Y L A + r ω i)
    (hsym : ∀ ω ∈ 𝒞, ∀ κ, slotPush (slotREquiv hR) κ = κ → ∀ i, κ = (1 / 2 : ℝ) •
      (place reservedCut (G ω).star.m (G ω).star.φ (Cop ω i) +
        place reservedCut (G ω).star.m (G ω).star.φ (Cop ω (hC ω i))) →
      |paperEN D L A (Choice.support ω) κ - paperEN0 D L A (Choice.support ω) κ| ≤
        (Rerr - Real.exp tU * tδ + z') * cX D L ω * D.Y L A + r ω i)
    (hzc : ∀ ω ∈ 𝒞, couplingMass (coef ω) * z' ≤ z)
    (r₄ M Minv : ℝ)
    (step4 : ∑ ω ∈ 𝒞, (G ω).star.wt * paperEN0 D L A (Choice.support ω)
        (place reservedCut (G ω).star.m (G ω).star.φ (Dop ω)) ≤
      WZ + z * (∑ ω ∈ 𝒞, (G ω).star.wt * cX D L ω) * D.Y L A + r₄)
    (hM : ∑ ω ∈ 𝒞, (G ω).star.wt * cX D L ω * couplingMass (coef ω) ≤
      M * ∑ ω ∈ 𝒞, (G ω).star.wt * cX D L ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, (G ω).star.wt * cX D L ω ≤
      ∑ ω ∈ 𝒞, (G ω).star.wt * cX D L ω * orbitMass (hC ω) (coef ω))
    (hρ : (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, (G ω).star.wt * cX D L ω) +
      D.B * (∑ ω ∈ 𝒞, (G ω).star.wt * (G ω).star.υ * cX D L ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, (G ω).star.wt * (2 + (G ω).star.υ) * cX D L ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, (G ω).star.wt * ((G ω).star.υ * rE ω + ∑ i, |coef ω i| * r ω i) + r₄ ≤
      ∑ ω ∈ 𝒞, rr ω) :
    DegreeOps reservedCut 𝒞 (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω)
      π ρ rr WZ (D.Y L A) z K :=
  paperDegreeOpsS D L A 𝒞 hsel π ρ rr WZ z K hY
    (fun ω b => HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b)
    (fun ω b => selMarg D L ω b.1) (fun _ _ => id)
    (fun ω => (G ω).star.Lop) (fun ω => (G ω).star.Υop) Dop hdom
    (fun ω => (G ω).star.υ) (fun ω hω => ((hG ω hω).starOK (hsel ω hω)).hυ)
    (fun ω hω => ((hG ω hω).starOK (hsel ω hω)).hΥsym)
    (fun ω hω => ((hG ω hω).starOK (hsel ω hω)).hΥ)
    (fun ω _ b _ t e he => hD_sel D L ω b t e he) rE hz hEB
    (fun ω => (G ω).star.wt) (fun ω hω => ((hG ω hω).starOK (hsel ω hω)).hwt)
    (fun ω hω => ((hG ω hω).starOK (hsel ω hω)).hN4)
    ι coef Cop hDk hR hC hh hpush Rerr z' tU tδ hRerr htδ r herr hsym hzc r₄ M Minv step4 hM hMinv
    hρ hπ hrr

end Sarkozy.OpsCore

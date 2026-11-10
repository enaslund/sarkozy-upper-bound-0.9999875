module

public import Sarkozy.OpsCore.Data
public import Sarkozy.EnvelopeSteps.PaperEnergy

@[expose] public section

/-!
# The assembly of `ops` from its remaining inputs (OPS-L)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i) and its proof (Steps 1–4);
`paper/sections/22_variance.tex`, `prop:background-variance`(a), `lem:var-gain`(b).

* **`DegreeInputs`**: the inputs of one degree class at one counterexample, at the paper's
  comparison data (B11's `paperDegreeOps`: the energies `paperElam`, `paperEN` on the support,
  (P5) proved), grouped by owner. Step 4 is split into the background bound `step4` with its own
  right side `Wbg` (any value) and the evaluation `hbg : Wbg ≤ Wd` against the class's diagonal
  budget `Wd`. **`DegreeInputs.toDegreeOps`**: B11's `DegreeOps` for every `WZ ≥ Wd`.
* **`OpsInputs`**: `ClassStepsOps`'s fields, with B11's `DegreeOps` at the per-class budget
  `Wd = (∑_{ω ∈ 𝒞} δ_ω π_ω) Y` for every degree class (from `DegreeInputs.toDegreeOps` at
  `WZ = Wd`, or from OPS-S's `paperDegreeOpsS`) and `VarStepsAt` at `WZ = 0`, `ρ = r π` for every
  variance class. **`OpsInputs.toOps`**: `ClassStepsOps` at the canonical data `Zs = zsUp`,
  `wc = wcCanon wc`, `ρ = r π` (`Data.lean`), by `DegreeOps.mono` and `wz_canon_ge`.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.EnvelopeSteps Sarkozy.MainFinal2
open Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

section Degree

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The remaining inputs of one degree class at one counterexample** (`thm:envelopes`(i), proof,
Steps 1–4, at the paper's comparison data `D`, scale `L`, set `A`). `π`, `ρ`, `rr` are the class's
prices, residuals and remainders; `Wd` is its diagonal budget (Step 4's target); `z`, `K` are
those of `ClassStepsOps`. Each group is marked with its kind, paper label and owner. -/
structure DegreeInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L))) (π ρ rr : Choice (D.CL.T L) → ℝ)
    (Wd z K : ℝ) where
  /-- **Objects and operators** (data; `subsec:reflection-averaging`, "Record assignments and
  placed measures"; `prop:signed-bounds`; owner OPS-L): the object type, the actual half marginal
  `m_ω`, the placement `φ_ω`, and `L_ω`, `Υ_ω`, `D_ω` on `L²(m_ω)`. -/
  Obj : Choice (D.CL.T L) → Type
  [instFO : ∀ ω, Fintype (Obj ω)]
  [instDO : ∀ ω, DecidableEq (Obj ω)]
  m : ∀ ω, Obj ω → ℝ
  φ : ∀ ω, Obj ω → (reservedCut.Half → EnvelopeSteps.PIn (m₀ := m₀) (blk := blk) (p := p) L
    (Choice.support ω))
  Lop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ)
  Υop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ)
  Dop : ∀ ω, (Obj ω → ℝ) →ₗ[ℝ] (Obj ω → ℝ)
  /-- **(N4)** (C/R; the star form `it:env:N4`, `subsec:envelope-tools`; owner OPS-L, through
  `hN4_of_records`): `⊗_{𝔅 ∈ X} ζ_{ω(𝔅),𝔅} = π̃_ω ([L_ω]_ω + [Υ_ω]_ω)`. -/
  wt : Choice (D.CL.T L) → ℝ
  hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω
  hN4 : ∀ ω ∈ 𝒞, selTensor D L ω =
    wt ω • (place reservedCut (m ω) (φ ω) (Lop ω) + place reservedCut (m ω) (φ ω) (Υop ω))
  /-- **`hΥ`** (R; `eq:oct24:star-tensor-error`, `prop:signed-bounds`(e); owner OPS-L):
  `Υ_ω` symmetric with `|⟨f, Υ_ω f⟩| ≤ υ_ω ‖f‖²` in `L²(m_ω)`. -/
  υ : Choice (D.CL.T L) → ℝ
  hυ : ∀ ω ∈ 𝒞, 0 ≤ υ ω
  hΥsym : ∀ ω ∈ 𝒞, ∀ f g, ip (m ω) f (Υop ω g) = ip (m ω) g (Υop ω f)
  hΥ : ∀ ω ∈ 𝒞, ∀ f, |ip (m ω) f (Υop ω f)| ≤ υ ω * ip (m ω) f f
  /-- **Domination** (C; `lem:oct24:mask-schur`(a), `lem:oct24:feature-block`(a); owner OPS-F):
  `±L_ω ⪯ D_ω` in `L²(m_ω)`. -/
  hdom : ∀ ω ∈ 𝒞, OpLE (m ω) (Lop ω) (Dop ω) ∧ OpLE (m ω) (-Lop ω) (Dop ω)
  /-- **(E1) for `Diag_ω`** (C; `it:record:E1`, `lem:bracket-energy`; owner OPS-S):
  `Y^Ñ[Diag_ω] ≤ (B + z) C_X Y + r₁'`. -/
  B : ℝ
  CX : Choice (D.CL.T L) → ℝ
  r₁' : Choice (D.CL.T L) → ℝ
  hE1 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
    (reservedCut.diagonalLaw (push (m ω) (φ ω))) ≤ (B + z) * CX ω * D.Y L A + r₁' ω
  /-- **Step 3** (C; `lem:orbit-coupon`, the coupling expansion; owner OPS-S):
  `Y^Ñ[[D_ω]] ≤ Y^{Ñ₀}_ω + (M_ω R_err − M_{h,ω} e^{tU} tδ + z) C_X Y + r₃`. -/
  YN0 : Choice (D.CL.T L) → ℝ
  Mω : Choice (D.CL.T L) → ℝ
  Mh : Choice (D.CL.T L) → ℝ
  r₃ : Choice (D.CL.T L) → ℝ
  Rerr : ℝ
  tU : ℝ
  tδ : ℝ
  hR : 0 ≤ Rerr
  htδ : 0 ≤ tδ
  step3 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω) (place reservedCut (m ω) (φ ω) (Dop ω)) ≤
    YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * D.Y L A + r₃ ω
  /-- **Step 4** (C; `lem:reflection-averaging`(d), `thm:envelopes`(iii),
  `lem:oct24:invariant-background`(iv),(v); owner OPS-S): the averaged background bound, with its
  own right side `Wbg`. -/
  Wbg : ℝ
  r₄ : ℝ
  step4 : ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ Wbg + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * D.Y L A + r₄
  /-- **The background against the class's diagonal budget** (evaluation, coupled to the labels;
  `cor:envelope-costs`, the residual table of `prop:joint-middle-mean`), with a part
  `spill · (∑ π̃ C_X) Y` of the background moved to the residual (`hρ`). The spill needs
  `R_err ≠ 0` (it is carried by the coupling mass, `M_ω ↦ M_ω + spill/R_err`). -/
  spill : ℝ
  hspill : Rerr ≠ 0 ∨ spill = 0
  hbg : Wbg ≤ Wd + spill * (∑ ω ∈ 𝒞, wt ω * CX ω) * D.Y L A
  /-- **The class averages and the residual** (evaluation; `thm:envelopes`(i), the definitions of
  `M`, `M^inv`; `cor:envelope-costs`). -/
  M : ℝ
  Minv : ℝ
  hM : ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω
  hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω
  hρ : (M * Rerr - Minv * Real.exp tU * tδ + spill) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
    B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω
  /-- **The error weights and the remainders** (R; `thm:envelopes`(i), last paragraph). -/
  hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω ≤ K * π ω
  hrr : ∑ ω ∈ 𝒞, wt ω * (υ ω * r₁' ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω

attribute [instance] DegreeInputs.instFO DegreeInputs.instDO

omit [DecidableEq P] in
/-- **B11's `DegreeOps` from the remaining inputs**, for any Step 4 target `WZ ≥ Wd`
(`paperDegreeOps`; (P5) and the identification of `I_ω` proved there). The spill of the
background into the residual is carried by the coupling mass: `Y^{Ñ₀}_ω ↦ Y^{Ñ₀}_ω − spill C_X Y`,
`M_ω ↦ M_ω + spill/R_err`, `M ↦ M + spill/R_err`. -/
noncomputable def DegreeInputs.toDegreeOps {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {L : ℕ} {A : Finset ℤ} {𝒞 : Finset (Choice (D.CL.T L))} {π ρ rr : Choice (D.CL.T L) → ℝ}
    {Wd z K : ℝ} (H : DegreeInputs D L A 𝒞 π ρ rr Wd z K) {WZ : ℝ} (hW : Wd ≤ WZ) :
    DegreeOps reservedCut 𝒞 (termAt (D := D) L A) π ρ rr WZ (D.Y L A) z K :=
  have hs : H.spill / H.Rerr * H.Rerr = H.spill := by
    rcases H.hspill with h | h
    · exact div_mul_cancel₀ _ h
    · rw [h, zero_div, zero_mul]
  paperDegreeOps D L A 𝒞 π ρ rr WZ z K H.Obj H.m H.φ H.Lop H.Υop H.Dop H.hdom H.υ H.hυ H.hΥsym
    H.hΥ H.B H.CX H.r₁' H.hE1 H.wt H.hwt H.hN4
    (fun ω => H.YN0 ω - H.spill * H.CX ω * D.Y L A) (fun ω => H.Mω ω + H.spill / H.Rerr) H.Mh H.r₃
    H.r₄ (H.M + H.spill / H.Rerr) H.Minv H.Rerr H.tU H.tδ H.hR H.htδ
    (fun ω hω => (H.step3 ω hω).trans_eq (by
      rw [show (H.Mω ω + H.spill / H.Rerr) * H.Rerr = H.Mω ω * H.Rerr + H.spill by
        rw [add_mul, hs]]
      ring))
    (by
      have h4 := H.step4
      have hb := H.hbg
      have e : ∑ ω ∈ 𝒞, H.wt ω * (H.YN0 ω - H.spill * H.CX ω * D.Y L A) =
          ∑ ω ∈ 𝒞, H.wt ω * H.YN0 ω - H.spill * (∑ ω ∈ 𝒞, H.wt ω * H.CX ω) * D.Y L A := by
        rw [mul_sum, sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun ω _ => by ring
      rw [e]
      linarith)
    (by
      have e : ∑ ω ∈ 𝒞, H.wt ω * H.CX ω * (H.Mω ω + H.spill / H.Rerr) =
          ∑ ω ∈ 𝒞, H.wt ω * H.CX ω * H.Mω ω + H.spill / H.Rerr * ∑ ω ∈ 𝒞, H.wt ω * H.CX ω := by
        rw [mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun ω _ => by ring
      rw [e]
      linarith [H.hM])
    H.hMinv
    (by
      have e : (H.M + H.spill / H.Rerr) * H.Rerr = H.M * H.Rerr + H.spill := by rw [add_mul, hs]
      rw [e]
      linarith [H.hρ])
    H.hπ H.hrr

omit [DecidableEq P] in
/-- The form that `OpsInputs` takes: `DegreeOps` at the budget `Wd` itself. -/
theorem DegreeInputs.nonempty_degreeOps {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {L : ℕ} {A : Finset ℤ} {𝒞 : Finset (Choice (D.CL.T L))} {π ρ rr : Choice (D.CL.T L) → ℝ}
    {Wd z K : ℝ} (H : Nonempty (DegreeInputs D L A 𝒞 π ρ rr Wd z K)) :
    Nonempty (DegreeOps reservedCut 𝒞 (termAt (D := D) L A) π ρ rr Wd (D.Y L A) z K) :=
  let ⟨H⟩ := H
  ⟨H.toDegreeOps le_rfl⟩

end Degree

section Ops

open Sarkozy.MeanCredit Sarkozy.Companion Sarkozy.ClassSlack Sarkozy.ClassData
open Sarkozy.CancellationSteps (PaperJ0)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **The remaining inputs of `ops`** at the canonical data (`thm:envelopes`(i) on every degree
class, `prop:background-variance`(a)/`lem:var-gain`(b) on every variance class), with the labels
`labS`, `labK` and the residual coefficients `r` of the obligations: `ClassStepsOps`'s data
`z → 0`, `Kπ`, `c₀ ≥ 0`, `rr ≥ 0`, and at every counterexample
* B11's `DegreeOps` for every degree class, at `ρ = r π` and the diagonal budget
  `Wd = (∑_{ω ∈ 𝒞} δ_ω π_ω) Y` (`δ` the coefficient that `hcomp` charges), e.g.
  `DegreeInputs.toDegreeOps le_rfl`;
* `VarStepsAt` for every variance class, at `ρ = r π` and `WZ = 0` (the class pays from `ρ`);
* the summed remainders. -/
structure OpsInputs (D : CD blockOf) (cd : ClassData D.CL) {K : Type} [Fintype K]
    [DecidableEq K] (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (r : ∀ L, Choice (D.CL.T L) → ℝ) where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hz : Tendsto z atTop (𝓝 0)
  Kπ : ℝ
  c₀ : ℝ
  hc₀ : 0 ≤ c₀
  rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ
  hrr0 : ∀ L A ω, 0 ≤ rr L A ω
  /-- Per counterexample: the inputs of every degree class, the variance steps of every variance
  class, the summed remainders. -/
  H : Param.AtCounterexamples (Param.Params.ofDecay TargetLedger.targetDecay) D.Y fun L A =>
    (∀ n : {n // n ∈ cd.N}, Nonempty (DegreeOps reservedCut (cd.clsSel L (.inl n))
      (termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (rhoOf r L) (rr L A)
      ((∑ ω ∈ cd.clsSel L (.inl n), delta labS labK L ω * monomial (D.CL.π L) ω) * D.Y L A)
      (D.Y L A) (z L) Kπ)) ∧
    (∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (termAt (D := D) L A)
      (fun ω => monomial (D.CL.π L) ω) (rhoOf r L) (rr L A) 0 (D.Y L A) (z L) Kπ)) ∧
    ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A

/-- **`ops` at the canonical data from the remaining inputs**: `Zs = zsUp`, `wc = wcCanon wc`,
`ρ = r π`. The degree classes by `DegreeOps.mono` and `wz_canon_ge`, the variance classes by
`VarStepsAt.mono` (their budget is nonnegative). -/
noncomputable def OpsInputs.toOps {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K]
    [DecidableEq K] {labS : ∀ L, Choice (D.CL.T L) → Option K} {labK : K → PaperDiag}
    {r : ∀ L, Choice (D.CL.T L) → ℝ} (O : OpsInputs D cd labS labK r)
    (wc : ∀ L, cd.ι L → K → ℝ) (hwc : ∀ L i k, 0 ≤ wc L i k) :
    ClassStepsOps cd (fun _ => K) (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (zsUp D L A))
      (wcCanon cd labS labK wc) (rhoOf r) where
  z := O.z
  hz0 := O.hz0
  hz := O.hz
  K := O.Kπ
  c₀ := O.c₀
  hc₀ := O.hc₀
  rr := O.rr
  hrr0 := O.hrr0
  H := by
    filter_upwards [O.H] with L hL
    intro C hC hind A hA hcount
    obtain ⟨hdeg, hvar, hrs⟩ := hL C hC hind A hA hcount
    have hY : max (D.Y L A) 0 = D.Y L A :=
      max_eq_left (Param.counterexample_pos _ hC hcount).le
    refine ⟨fun n => ?_, fun v => ?_, hrs⟩
    · obtain ⟨Hn⟩ := hdeg n
      have hW := wz_canon_ge (cd := cd) labS labK hwc L A (.inl n)
      rw [hY] at hW
      exact ⟨DegreeOps.mono Hn hW le_rfl le_rfl⟩
    · obtain ⟨Hv⟩ := hvar v
      refine ⟨VarStepsAt.mono Hv ?_ le_rfl le_rfl⟩
      refine sum_nonneg fun k _ => mul_nonneg (wcCanon_nonneg labS labK hwc L _ k) ?_
      exact agg_nonneg _ _ (fun _ => wtHalf_nonneg K _) (fun ω _ => zsUp_nonneg cd L A ω) k

end Ops

end Sarkozy.OpsCore

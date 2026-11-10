module

public import Sarkozy.OpsVariance.Forms
public import Sarkozy.ClassInputsPaper.VarianceRecords
public import Sarkozy.EnvelopeSteps.Constructor

@[expose] public section

/-!
# The variance interface of a selection at its norm envelopes

`paper/sections/09_comparison_theorem.tex`, `def:record:comparison-law`(b): every record change
`ζ^ε_{𝔅,t}` has a reserved-diagonal probability norm envelope `D^ε_{𝔅,t}` with
`(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0` ("diagonal copies of actual half marginals of `t`, in the
applications"); `paper/sections/10_comparison_lemmas.tex`, `lem:record:variance-interface`(i);
`paper/sections/22_variance.tex`, proof of `lem:var-gain`(b) and of
`prop:background-variance`(a), "The class cost".

For a selection `ω` of comparison data `D` put, at every block `𝔅` of its support `X`,

* `m_{ω,𝔅}` (`envM`): the plus-half marginal of the norm envelope `D^{ε_𝔅}_{𝔅,t_𝔅}` of its record;
* `γ_{ω,𝔅} = π̃^{ε_𝔅}_{𝔅,t_𝔅}` (`entryPrice`), so that `∏_𝔅 γ_{ω,𝔅} = π̃_ω`
  (`prod_entryPrice_support`) and `π̃_ω C_X = π_ω` with `C_X = ∏_{𝔅 ∈ X} q_𝔅^{2a}`
  (`monomial_π_eq`).

Then, **from the fields of `D` alone**:

* `diagonalLaw_envM`: `Diag_ι(m_{ω,𝔅}) = D^{ε_𝔅}_{𝔅,t_𝔅}` (the norm envelope is reserved diagonal,
  `D_diag`; `eq_diagonalLaw_of_isDiagonalAt`). So the paper's identification "the norm envelope is
  the diagonal copy of the half marginal" holds by construction for `m = envM`;
* `varDiag_envM`: B10's `Y[Diag_X ⊗ Ñ]` at `envM` is the energy of the envelope law of `ω`, the
  left side of (E1) for the selections (`ComparisonData.EnvelopeBoundNonneg`);
* `abs_term_le_envelope_paper`: `|I_ω| ≤ π̃_ω Y[(⊗_X D) ⊗ Ñ]` (`lem:record:record-expansion`(i):
  the brackets of (CP3) and (CP4)(b)), the bound with no variance credit;
* **`abs_term_le_envVariance`**: if the record changes of `ω` have zero marginals
  (`eq:record:zero-marginal`, `RecordsZeroMarginal`), then
  `|I_ω| ≤ π̃_ω (Y[Diag_X ⊗ Ñ] − Y[J_X ⊗ Ñ])` at `m = envM`: `lem:record:variance-interface`(i)
  with `γ_𝔅 = π̃_𝔅` the coefficient of the norm envelope, as in the proof of `lem:var-gain`(b).
  The per-record bilinear bound `hζ` of B10's `VarStepsAt.ofRecords` is proved
  (`hζ_envM`, from the bracket of (CP4)(b) and `abs_form_le_variance_of_bracket`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- **The half marginals of the norm envelopes of a choice**: at a block `𝔅` with record `t` and
type `ε`, the plus-half marginal at `ι` of `D^ε_{𝔅,t}`; `0` off the support. -/
noncomputable def envM (L : ℕ) (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) :
    (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ :=
  (ω b).elim 0 fun te => halfMarginalPlus reservedCut (D.CL.D L b te.1 te.2)

/-- `C_X = ∏_{𝔅 ∈ X} q_𝔅^{2a}`, the selection factor of a choice. -/
noncomputable abbrev selProd (L : ℕ) (ω : Choice (D.CL.T L)) : ℝ :=
  ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b

/-- **Zero marginals of the record changes of a choice** (`eq:record:zero-marginal`): at every block
of the support, the change `Δ_{𝔅,t}` of the selected record annihilates the constants on both sides
of `ι`. -/
def RecordsZeroMarginal (L : ℕ) (ω : Choice (D.CL.T L)) : Prop :=
  ∀ b t e, ω b = some (t, e) → ZeroMarginals reservedCut (D.CL.Δ L b t)

variable {D}

omit [DecidableEq P] in
theorem envM_nonneg (L : ℕ) (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L)
    (x : reservedCut.Half → BlockLabel m₀ blk p L b) : 0 ≤ envM D L ω b x := by
  unfold envM
  rcases ω b with _ | ⟨t, e⟩
  · exact le_refl _
  · exact (D.CL.D_prob L b t e).1 _ fun _ => by split_ifs <;> norm_num

omit [DecidableEq P] in
/-- **The norm envelope is the diagonal copy of `envM`** (`def:cp4`(b), from `D_diag`). -/
theorem diagonalLaw_envM {L : ℕ} {ω : Choice (D.CL.T L)} {b : BlockAtom Bk J L} {t : D.CL.T L b}
    {e : ChangeType} (hω : ω b = some (t, e)) :
    reservedCut.diagonalLaw (envM D L ω b) = D.CL.D L b t e := by
  unfold envM
  rw [hω]
  exact (eq_diagonalLaw_of_isDiagonalAt reservedCut (D.CL.D_diag L b t e)).symm

omit [DecidableEq P] in
theorem eq_none_of_not_mem_support' {L : ℕ} {ω : Choice (D.CL.T L)} {b : BlockAtom Bk J L}
    (hb : b ∉ Choice.support ω) : ω b = none := by
  unfold Choice.support at hb
  simpa using hb

omit [DecidableEq P] in
/-- **`Y[Diag_X ⊗ Ñ]` at `envM` is the energy of the envelope law of `ω`** (the left side of (E1)
for the selections; so the field `hDN` of `VarStepsAt` is (E1) for the envelopes). -/
theorem varDiag_envM (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    varDiag D L A ω (envM D L ω) =
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) := by
  unfold varDiag envelopeLaw
  congr 2
  funext b
  by_cases hb : b ∈ Choice.support ω
  · simp only [hb, ↓reduceIte]
    rcases hω : ω b with _ | ⟨t, e⟩
    · exact absurd (by simpa [Choice.support] using hb) (by simp [hω])
    · exact diagonalLaw_envM hω
  · simp only [hb, ↓reduceIte]
    rw [eq_none_of_not_mem_support' hb]
    rfl

omit [DecidableEq P] in
/-- `∏_{𝔅 ∈ X} π̃_{ω(𝔅)} = π̃_ω`. -/
theorem prod_entryPrice_support (L : ℕ) (ω : Choice (D.CL.T L)) :
    ∏ b ∈ Choice.support ω, entryPrice (D.CL.πt L b) (ω b) = monomial (D.CL.πt L) ω := by
  unfold monomial Choice.support
  rw [prod_filter]
  apply prod_congr rfl
  intro b _
  rcases ω b with _ | ⟨t, e⟩
  · rfl
  · rfl

omit [DecidableEq P] in
/-- **`π_ω = π̃_ω C_X`** (`π^ε_{𝔅,t} = π̃^ε_{𝔅,t} q_𝔅^{2a}`). -/
theorem monomial_π_eq (L : ℕ) (ω : Choice (D.CL.T L)) :
    monomial (D.CL.π L) ω = monomial (D.CL.πt L) ω * selProd D L ω :=
  monomial_mul_selectionFactor (D.CL.πt L) (fun b => selectionFactor a p D.S.selPre L b) ω

omit [DecidableEq P] in
theorem selProd_nonneg (L : ℕ) (ω : Choice (D.CL.T L)) : 0 ≤ selProd D L ω :=
  prod_nonneg fun b _ => ComparisonData.selectionFactor_nonneg D L b

omit [DecidableEq P] in
theorem monomial_πt_nonneg (L : ℕ) (ω : Choice (D.CL.T L)) : 0 ≤ monomial (D.CL.πt L) ω :=
  monomial_nonneg (D.CL.πt_nonneg L) ω

omit [DecidableEq P] in
theorem monomial_π_nonneg (L : ℕ) (ω : Choice (D.CL.T L)) : 0 ≤ monomial (D.CL.π L) ω := by
  rw [monomial_π_eq]
  exact mul_nonneg (monomial_πt_nonneg L ω) (selProd_nonneg L ω)

omit [DecidableEq P] in
/-- **The bound with no variance credit** (`lem:record:record-expansion`(i), the brackets of (CP3)
and (CP4)(b); the field `hI` of `VarStepsAt` at `JN = 0`): `|I_ω| ≤ π̃_ω Y[(⊗_X D) ⊗ Ñ]`. -/
theorem abs_term_le_envelope_paper (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    |termAt (D := D) L A ω| ≤ monomial (D.CL.πt L) ω *
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) :=
  abs_term_le_envelope (c := reservedCut) (fun b => D.GB.bracket L b)
    (fun b t e => D.CL.bracket L b t e) (blockLift m₀ blk p L A) ω

omit [DecidableEq P] in
/-- **The per-record bilinear bound at the norm envelope** (the hypothesis `hζ` of B10's
`abs_term_le_variance`): with zero marginals, the selected change `ζ^ε_{𝔅,t}` satisfies
`|Q_ζ(G, H)| ≤ π̃^ε_{𝔅,t} ‖G − E G‖_{m} ‖H − E H‖_{m}`, `m = envM`, from the bracket
`(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0` of (CP4)(b). -/
theorem hζ_envM {L : ℕ} {ω : Choice (D.CL.T L)} (hz : RecordsZeroMarginal D L ω)
    (b : BlockAtom Bk J L) (hb : b ∈ Choice.support ω)
    (G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) :
    |reservedCut.form (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)) G H| ≤
      entryPrice (D.CL.πt L b) (ω b) *
        Real.sqrt (reservedCut.form (reservedCut.diagonalLaw (envM D L ω b) -
          indepLaw reservedCut (envM D L ω b)) G G) *
        Real.sqrt (reservedCut.form (reservedCut.diagonalLaw (envM D L ω b) -
          indepLaw reservedCut (envM D L ω b)) H H) := by
  rcases hω : ω b with _ | ⟨t, e⟩
  · exact absurd (by simpa [Choice.support] using hb) (by simp [hω])
  · have hD := diagonalLaw_envM hω
    have hzΔ := hz b t e hω
    have hzζ : ZeroMarginals reservedCut (D.CL.ζ L b t e) := by
      cases e
      · exact zeroMarginals_symPart reservedCut hzΔ
      · exact zeroMarginals_skewPart reservedCut hzΔ
    have hbr := D.CL.bracket L b t e
    rw [← hD] at hbr
    exact abs_form_le_variance_of_bracket reservedCut (envM_nonneg L ω b) (D.CL.πt_nonneg L b t e)
      hbr hzζ G H

omit [DecidableEq P] in
/-- **`lem:record:variance-interface`(i) at the norm envelopes** (proof of `lem:var-gain`(b); the
field `hI` of `VarStepsAt`): for a selection whose record changes have zero marginals,
`|I_ω| ≤ π̃_ω (Y[Diag_X ⊗ Ñ] − Y[J_X ⊗ Ñ])` with the half marginals `envM` of the norm envelopes. -/
theorem abs_term_le_envVariance (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (hω : IsSelection ω) (hz : RecordsZeroMarginal D L ω) :
    |termAt (D := D) L A ω| ≤ monomial (D.CL.πt L) ω *
      (varDiag D L A ω (envM D L ω) - varJ D L A ω (envM D L ω)) := by
  have h := abs_term_le_variance D L A ω hω (envM D L ω) (fun b _ x => envM_nonneg L ω b x)
    (fun b => entryPrice (D.CL.πt L b) (ω b))
    (fun b _ => entryPrice_nonneg (D.CL.πt_nonneg L b) (ω b)) (hζ_envM hz)
  rwa [prod_entryPrice_support] at h

end Sarkozy.OpsVariance

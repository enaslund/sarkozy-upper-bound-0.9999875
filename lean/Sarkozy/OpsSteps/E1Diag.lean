module

public import Sarkozy.EnvelopeSteps.PaperAveraging
public import Sarkozy.TheoremCBlock.Classes

@[expose] public section

/-!
# (E1) for the diagonals `Diag_ω` from the envelope bound (E1) of the selections (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 1 ("`(P5)` and `(E1)` give
`|Y_{[Υ_ω]_ω ⊗ λ_{-X}}| ≤ υ_ω Y^Ñ[Diag_ω] ≤ υ_ω (B + o(1)) C_X Y`");
`paper/sections/22_variance.tex`, `prop:background-variance`(a)
(`Y[Diag_X ⊗ Ñ] ≤ (B + o(1)) C_X Y`);
`paper/sections/09_comparison_theorem.tex`, `def:cp4`(b): the norm envelopes `D^ε_{𝔟,t}` are
"reserved-diagonal probability laws … with uniform one-slot marginals (**diagonal copies of actual
half marginals of `t`, in the applications**)"; `paper/sections/10_comparison_lemmas.tex`,
`lem:bracket-energy`, (E1).

B11's `paperDegreeOps` and B10's `VarStepsAt.ofRecords` take (E1) for the diagonal of the product
half marginal as an input (`hE1`, `hDN`). The comparison data already carry the (E1) bound of the
envelopes of **all** selections, `ComparisonData.EnvelopeBoundNonneg`:

`Y[(⊗_{𝔟 ∈ X} D^{ε_𝔟}_{𝔟,t_𝔟}) ⊗ Ñ_{-X}] ≤ (B + ε_E) C_X Y + r_E(ω)`,
`∑_ω π̃_ω r_E(ω) ≤ c_E L^{-σ} α`,

which EC proved at the paper's data (`E1Proved.lean`). Since `D^ε_{𝔟,t} = Diag_ι(m_{t,𝔟})` in
the applications, the diagonal `Diag_ω` of a selection **is** its envelope law, and (E1) for
`Diag_ω` is the envelope bound at `ω`. This file proves that:

* `varDiag_eq_envelope`: B10's `varDiag` (`Y[Diag_X ⊗ Ñ]`) is the energy of the envelope law of
  `ω` when the diagonals of the half marginals are the norm envelopes `D^{ε_𝔟}_{𝔟,t_𝔟}`;
* **`hDN_of_envelope`**: the input `hDN` of `VarStepsAt.ofRecords` from the envelope bound;
* `paperEN_diag_eq_envelope`, **`hE1_of_envelope`**: the input `hE1` of `paperDegreeOps` (B11),
  with product objects, `B = e^{U₀} + R_err`, `C_X = ∏_{𝔟 ∈ X} q_𝔟^{2a}` and `r₁' = r_E`;
* the remainders: **`sum_rem_le`** (`∑_{ω ∈ 𝒞} w_ω r_E(ω) ≤ K ∑_ω π̃_ω r_E(ω)` when
  `w_ω ≤ K π̃_ω`), and `wt_le_of_hπ`, `γ_le_of_hπ`: these weight conditions follow from the price
  fields `hπ` of `DegreeOps` and `VarStepsAt` (`C_X > 0`, `selectionFactor_pos`).

The one remaining condition is the identification `hD`: at every block of the selection, the
diagonal copy of the actual half marginal of its record is the norm envelope `D^{ε}_{𝔟,t}` of
`def:cp4`(b). It is a property of the objects (`Obj`, `m`, `φ`) chosen for the class, as the paper
states it; in the Lean data the middle-block envelopes `D` are free data of the comparison law
(`ComparisonLawPaper.Blocks`: "not constructed in Lean").
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps

section Paper

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- An atom outside the support of a choice carries no record. -/
theorem eq_none_of_not_mem_support {L : ℕ} {ω : Choice (D.CL.T L)} {b : BlockAtom Bk J L}
    (hb : b ∉ Choice.support ω) : ω b = none := by
  unfold Choice.support at hb
  simpa using hb

omit [DecidableEq P] in
/-- **`Y[Diag_X ⊗ Ñ]` is the energy of the envelope law** when, at every block of the support,
the diagonal of the half marginal is the norm envelope of the selected record
(`def:cp4`(b): `D^ε_{𝔟,t} = Diag_ι(m_{t,𝔟})`). -/
theorem varDiag_eq_envelope (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hD : ∀ b ∈ Choice.support ω, ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (m b) = D.CL.D L b t e) :
    varDiag D L A ω m =
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) := by
  unfold varDiag envelopeLaw
  congr 2
  funext b
  by_cases hb : b ∈ Choice.support ω
  · simp only [hb, ↓reduceIte]
    rcases hω : ω b with _ | ⟨t, e⟩
    · exact absurd (by simpa [Choice.support] using hb) (by simp [hω])
    · exact hD b hb t e hω
  · simp only [hb, ↓reduceIte]
    rw [eq_none_of_not_mem_support D hb]
    rfl

omit [DecidableEq P] in
/-- `C_X = ∏_{𝔟 ∈ X} q_𝔟^{2a} ≥ 0`. -/
theorem prod_selectionFactor_nonneg (L : ℕ) (S : Finset (BlockAtom Bk J L)) :
    0 ≤ ∏ b ∈ S, selectionFactor a p D.S.selPre L b :=
  prod_nonneg fun b _ => ComparisonData.selectionFactor_nonneg D L b

omit [DecidableEq P] in
/-- `q_𝔟^{2a} > 0` (the prefix factors are at least `1`, `(CP8)`). -/
theorem selectionFactor_pos (L : ℕ) (b : BlockAtom Bk J L) :
    0 < selectionFactor a p D.S.selPre L b := by
  cases b with
  | inl β => exact lt_of_lt_of_le zero_lt_one (D.S.one_le_selPre β)
  | inr j =>
    exact Real.rpow_pos_of_pos (by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne (p L j))) _

omit [DecidableEq P] in
/-- **The input `hDN` of B10's `VarStepsAt.ofRecords` from the envelope bound** ((E1) for the
diagonals, `prop:background-variance`(a)): if the envelope law of `ω` satisfies
`Y[env_ω] ≤ (B + ε_E) C_X Y + r_E` (`EnvelopeBoundNonneg`, first part), `ε_E ≤ z`, `Y ≥ 0`, and the
diagonals of the half marginals are the norm envelopes (`hD`), then
`Y[Diag_X ⊗ Ñ] ≤ (B + z) C_X Y + r_E`. -/
theorem hDN_of_envelope {L : ℕ} {A : Finset ℤ} (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hD : ∀ b ∈ Choice.support ω, ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (m b) = D.CL.D L b t e)
    {εE z rE : ℝ} (hz : εE ≤ z) (hY : 0 ≤ D.Y L A)
    (hEB : diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) ≤
      (D.B + εE) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A + rE) :
    varDiag D L A ω m ≤
      (D.B + z) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A + rE := by
  rw [varDiag_eq_envelope D L A ω m hD]
  have hCY : 0 ≤ (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A :=
    mul_nonneg (prod_selectionFactor_nonneg D L _) hY
  nlinarith [mul_le_mul_of_nonneg_right hz hCY]

omit [DecidableEq P] in
/-- **`Y^Ñ[Diag_ω]` is the energy of the envelope law** of `ω`, for product objects whose
diagonals are the norm envelopes (`paperEN_diag_eq_varDiag`, `varDiag_eq_envelope`). -/
theorem paperEN_diag_eq_envelope (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (O : {b // b ∈ Choice.support ω} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (m : ∀ b, O b → ℝ) (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (hD : ∀ b (hb : b ∈ Choice.support ω), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) = D.CL.D L b t e) :
    paperEN D L A (Choice.support ω)
        (reservedCut.diagonalLaw (push (prodWeight m) (prodPlace reservedCut φ))) =
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) := by
  rw [paperEN_diag_eq_varDiag D L A ω O m φ]
  apply varDiag_eq_envelope
  intro b hb t e hω
  simp only [hb, ↓reduceDIte]
  exact hD b hb t e hω

omit [DecidableEq P] in
/-- **The input `hE1` of B11's `paperDegreeOps` from the envelope bound** (`thm:envelopes`(i),
Step 1, (E1)). For a family `𝒞` of selections with product objects `O ω 𝔟`, half marginals
`m ω 𝔟` and placements `φ ω 𝔟` whose diagonals are the norm envelopes of the selected records
(`hD`, `def:cp4`(b)), the pointwise envelope bound (`EnvelopeBoundNonneg`, first part, at the
counterexample `(L, A)`), `ε_E ≤ z` and `Y ≥ 0` give, for every `ω ∈ 𝒞`,

`Y^Ñ[Diag_ω] ≤ (B + z) C_X Y + r_E(ω)`, `B = e^{U₀} + R_err`, `C_X = ∏_{𝔟 ∈ X} q_𝔟^{2a}`,

which is `hE1` with `Obj ω = ∏_𝔟 O ω 𝔟`, `m ω = prodWeight (m ω)`,
`φ ω = prodPlace ι (φ ω)`, `B := D.B`, `CX ω := C_X`, `r₁' := r_E`. -/
theorem hE1_of_envelope (L : ℕ) (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ 𝒞, IsSelection ω)
    (O : ∀ ω : Choice (D.CL.T L), {b // b ∈ Choice.support ω} → Type)
    [∀ ω b, Fintype (O ω b)] [∀ ω b, DecidableEq (O ω b)]
    (m : ∀ ω b, O ω b → ℝ) (φ : ∀ ω b, O ω b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (hD : ∀ ω ∈ 𝒞, ∀ b (hb : b ∈ Choice.support ω), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ω ⟨b, hb⟩) (φ ω ⟨b, hb⟩)) = D.CL.D L b t e)
    {εE z : ℝ} (rE : Choice (D.CL.T L) → ℝ) (hz : εE ≤ z) (hY : 0 ≤ D.Y L A)
    (hEB : ∀ ω : Choice (D.CL.T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) ≤
        (D.B + εE) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A +
          rE ω) :
    ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
        (reservedCut.diagonalLaw (push (prodWeight (m ω)) (prodPlace reservedCut (φ ω)))) ≤
      (D.B + z) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A +
        rE ω := by
  intro ω hω
  rw [paperEN_diag_eq_envelope D L A ω (O ω) (m ω) (φ ω) (hD ω hω)]
  have hCY : 0 ≤ (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A :=
    mul_nonneg (prod_selectionFactor_nonneg D L _) hY
  nlinarith [hEB ω (hsel ω hω), mul_le_mul_of_nonneg_right hz hCY]

omit [DecidableEq P] in
/-- **`hE1_of_envelope` at any `B ≥ e^{U₀} + R_err`** (e.g. the ledger's `B'`, so that the class
bound of B10's `consistent_degree` uses one constant). -/
theorem hE1_of_envelope_le (L : ℕ) (A : Finset ℤ) (𝒞 : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ 𝒞, IsSelection ω)
    (O : ∀ ω : Choice (D.CL.T L), {b // b ∈ Choice.support ω} → Type)
    [∀ ω b, Fintype (O ω b)] [∀ ω b, DecidableEq (O ω b)]
    (m : ∀ ω b, O ω b → ℝ) (φ : ∀ ω b, O ω b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (hD : ∀ ω ∈ 𝒞, ∀ b (hb : b ∈ Choice.support ω), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ω ⟨b, hb⟩) (φ ω ⟨b, hb⟩)) = D.CL.D L b t e)
    {εE z B : ℝ} (hB : D.B ≤ B) (rE : Choice (D.CL.T L) → ℝ) (hz : εE ≤ z) (hY : 0 ≤ D.Y L A)
    (hEB : ∀ ω : Choice (D.CL.T L), IsSelection ω →
      diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A) ≤
        (D.B + εE) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A +
          rE ω) :
    ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
        (reservedCut.diagonalLaw (push (prodWeight (m ω)) (prodPlace reservedCut (φ ω)))) ≤
      (B + z) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A +
        rE ω := by
  intro ω hω
  have h := hE1_of_envelope D L A 𝒞 hsel O m φ hD rE hz hY hEB ω hω
  have hCY : 0 ≤ (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A :=
    mul_nonneg (prod_selectionFactor_nonneg D L _) hY
  nlinarith [mul_le_mul_of_nonneg_right hB hCY]

/-! ## The remainders -/

omit [DecidableEq P] in
/-- `π_ω = π̃_ω C_X` (`monomial_mul_selectionFactor` at the prices of the comparison law). -/
theorem monomial_π_eq (L : ℕ) (ω : Choice (D.CL.T L)) :
    monomial (D.CL.π L) ω = monomial (D.CL.πt L) ω *
      ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
  monomial_mul_selectionFactor (D.CL.πt L) (fun b => selectionFactor a p D.S.selPre L b) ω

omit [DecidableEq P] in
/-- **The weight of the Step-1 remainder is dominated by the skew-price monomial**, from the field
`hπ` of `DegreeOps` (`π̃^arm (2 + υ) C_X ≤ K π_ω`, `thm:envelopes`(i), last paragraph): with
`C_X = ∏ q^{2a} > 0` and `π̃^arm ≥ 0`, `π̃^arm υ ≤ K π̃_ω`. -/
theorem wt_le_of_hπ (L : ℕ) (ω : Choice (D.CL.T L)) {wt υ K : ℝ} (hwt : 0 ≤ wt)
    (hπ : wt * (2 + υ) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) ≤
      K * monomial (D.CL.π L) ω) :
    wt * υ ≤ K * monomial (D.CL.πt L) ω := by
  set C := ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b with hC
  have hC0 : 0 < C := prod_pos fun b _ => selectionFactor_pos D L b
  rw [monomial_π_eq D L ω, ← hC] at hπ
  have h1 : wt * υ * C ≤ K * monomial (D.CL.πt L) ω * C := by nlinarith
  exact le_of_mul_le_mul_right h1 hC0

omit [DecidableEq P] in
/-- **The same for a variance class**, from the field `hπ` of `VarStepsAt` (`3 γ C_X ≤ K π_ω`):
`γ ≤ (K/3) π̃_ω`. -/
theorem γ_le_of_hπ (L : ℕ) (ω : Choice (D.CL.T L)) {γ K : ℝ}
    (hπ : 3 * (γ * ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) ≤
      K * monomial (D.CL.π L) ω) :
    γ ≤ K / 3 * monomial (D.CL.πt L) ω := by
  set C := ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b with hC
  have hC0 : 0 < C := prod_pos fun b _ => selectionFactor_pos D L b
  rw [monomial_π_eq D L ω, ← hC] at hπ
  have h1 : γ * C ≤ K / 3 * monomial (D.CL.πt L) ω * C := by nlinarith
  exact le_of_mul_le_mul_right h1 hC0

omit [DecidableEq P] in
/-- **The class sum of the (E1) remainders is a part of the summed envelope remainder**
(`def:robust`): for a set `S` of selections with weights `w_ω ≤ K π̃_ω` (e.g. `π̃^arm υ` by
`wt_le_of_hπ`, or `γ` by `γ_le_of_hπ`) and `r_E ≥ 0`,
`∑_{ω ∈ S} w_ω r_E(ω) ≤ K ∑_{ω selection} π̃_ω r_E(ω)`, which is at most `K c_E L^{-σ} α` by
`EnvelopeBoundNonneg` (second part). The classes are disjoint sets of selections, so the same bound
holds for the sum over all classes. -/
theorem sum_rem_le (L : ℕ) (S : Finset (Choice (D.CL.T L))) (hsel : ∀ ω ∈ S, IsSelection ω)
    (w rE : Choice (D.CL.T L) → ℝ) {K : ℝ} (hK : 0 ≤ K) (hrE : ∀ ω, 0 ≤ rE ω)
    (hw : ∀ ω ∈ S, w ω ≤ K * monomial (D.CL.πt L) ω) :
    ∑ ω ∈ S, w ω * rE ω ≤
      K * ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω * rE ω := by
  have hS : S ⊆ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω) :=
    fun ω hω => mem_filter.mpr ⟨mem_univ _, hsel ω hω⟩
  rw [mul_sum]
  calc ∑ ω ∈ S, w ω * rE ω ≤ ∑ ω ∈ S, K * (monomial (D.CL.πt L) ω * rE ω) :=
        sum_le_sum fun ω hω => by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right (hw ω hω) (hrE ω)
    _ ≤ _ := sum_le_sum_of_subset_of_nonneg hS fun ω _ _ =>
        mul_nonneg hK (mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (hrE ω))

end Paper

end Sarkozy.OpsSteps

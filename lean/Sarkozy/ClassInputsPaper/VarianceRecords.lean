module

public import Sarkozy.ClassInputsPaper.Energy
public import Sarkozy.Variance.ClassCostBlocks

@[expose] public section

/-!
# The variance classes at the records of the construction

`paper/sections/22_variance.tex`, `lem:record:variance-interface`(i), `prop:background-variance`(a),
`lem:var-gain`(b), `cor:var-classes`; `paper/sections/10_comparison_lemmas.tex`, (E2).

W1's `Variance.abs_energy_le_variance_blocks` (`lem:record:variance-interface`(i) with each block
its own factor) and `Variance.energy_nonneg_of_positive` ((E2)) are stated for any tensor of
measures with selected factors `ζ_j` on a set `X` and the bracket `Ñ_j` outside. Here they are
applied to the terms of the record expansion of the construction:

* `term_eq_support`: the term `I_ω` of a choice is the energy of the tensor with the records of `ω`
  on its support and `λ` elsewhere;
* **`abs_term_le_variance`**: for a selection `ω` of any comparison data, if every record of `ω`
  satisfies the bilinear bound `|⟨ζ_𝔟 G, H⟩_ι| ≤ γ_𝔟 ‖G‖_{m_𝔟} ‖H‖_{m_𝔟}` of
  `lem:record:variance-interface` against the variance form of a half marginal `m_𝔟 ≥ 0`, then
  `|I_ω| ≤ (∏ γ_𝔟) (Y[Diag_X ⊗ Ñ] − Y[J_X ⊗ Ñ])` (W1, with (CP3)'s bracket `Ñ` from
  `GramBracket.bracket`);
* `varJ_nonneg`: `Y[J_X ⊗ Ñ] ≥ 0` ((E2), from W1's positivity of `J` and of the bracket);
* **`VarStepsAt.ofRecords`**: the class-cost step of a variance class with `hI` and `hJN0`
  **proved** from the per-record bilinear bounds; what remains is (E1) for the diagonals (`hDN`),
  the comparison of `Ñ` with `Ñ₀` (`hJN`), the restoration bound (`hres`) and the evaluations
  (`hρ`, `hπ`, `hrr`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassInputsPaper

open Sarkozy.ClassBoundsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

section Generic

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]

omit [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)] in
/-- The term of a choice is the energy of the tensor with its records on its support and `λ`
elsewhere. -/
theorem term_eq_support (lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, X b) → ℝ) (ω : Choice T) :
    term lam ζ F ω = diagonalIntegral (tensorLaw fun j =>
      if j ∈ Choice.support ω then entryFactor (lam j) (ζ j) (ω j) else lam j) F := by
  unfold term choiceLaw
  congr 2
  funext j
  by_cases hj : j ∈ Choice.support ω
  · simp only [hj, ↓reduceIte]
  · simp only [hj, ↓reduceIte]
    have h : ω j = none := by
      unfold Choice.support at hj
      simpa using hj
    rw [h]
    rfl

end Generic

section Paper

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- The energy `Y[Diag_X ⊗ Ñ]` of a selection: the diagonal laws of the half marginals `m_𝔟`
on the support, the bracket `Ñ` of (CP3) elsewhere. -/
noncomputable def varDiag (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw fun b => if b ∈ Choice.support ω then
    reservedCut.diagonalLaw (m b) else D.GB.N L b) (blockLift m₀ blk p L A)

/-- The energy `Y[J_X ⊗ Ñ]` of a selection: the product laws of the half marginals on the
support, the bracket `Ñ` elsewhere. -/
noncomputable def varJ (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw fun b => if b ∈ Choice.support ω then
    indepLaw reservedCut (m b) else D.GB.N L b) (blockLift m₀ blk p L A)

omit [DecidableEq P] in
/-- **`lem:record:variance-interface`(i) at a term of the construction** (W1's
`abs_energy_le_variance_blocks` with the bracket of (CP3)). -/
theorem abs_term_le_variance (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) (hω : IsSelection ω)
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hm : ∀ b ∈ Choice.support ω, ∀ x, 0 ≤ m b x) (γ : BlockAtom Bk J L → ℝ)
    (hγ : ∀ b ∈ Choice.support ω, 0 ≤ γ b)
    (hζ : ∀ b ∈ Choice.support ω, ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
      |reservedCut.form (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)) G H| ≤
        γ b * Real.sqrt (reservedCut.form (reservedCut.diagonalLaw (m b) -
          indepLaw reservedCut (m b)) G G) *
        Real.sqrt (reservedCut.form (reservedCut.diagonalLaw (m b) -
          indepLaw reservedCut (m b)) H H)) :
    |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
      (∏ b ∈ Choice.support ω, γ b) * (varDiag D L A ω m - varJ D L A ω m) := by
  rw [term_eq_support]
  exact Variance.abs_energy_le_variance_blocks reservedCut (D.GB.N L) (D.FS.lam L)
    (Choice.support ω) ((Choice.support_nonempty_iff ω).mpr hω.1) (fun b _ => D.GB.bracket L b)
    m hm γ hγ (fun b => entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)) hζ
    (blockLift m₀ blk p L A)

omit [DecidableEq P] in
/-- **(E2) for `Y[J_X ⊗ Ñ]`**: it is nonnegative (W1's `energy_nonneg_of_positive`, with the
positivity of `J` and of the bracket of (CP3)). -/
theorem varJ_nonneg (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hm : ∀ b ∈ Choice.support ω, ∀ x, 0 ≤ m b x) : 0 ≤ varJ D L A ω m := by
  unfold varJ
  apply Variance.energy_nonneg_of_positive reservedCut
  intro b
  by_cases hb : b ∈ Choice.support ω
  · simp only [hb, ↓reduceIte]
    exact positive_indepLaw reservedCut (hm b hb)
  · simp only [hb, ↓reduceIte]
    exact (D.GB.bracket L b).left_positive

variable {D}

omit [DecidableEq P] in
/-- **The class-cost step of a variance class at the records of the construction**: `VarStepsAt`
with `DN = Y[Diag_X ⊗ Ñ]`, `JN = Y[J_X ⊗ Ñ]`, `γ_ω = ∏_𝔟 γ_{ω,𝔟}`; `hI` is
`abs_term_le_variance` and `hJN0` is `varJ_nonneg`. The remaining inputs are (E1) for the
diagonals (`hDN`), the comparison with `Ñ₀` (`hJN`, `lem:oct24:invariant-background`), the
restoration bound (`hres`, `lem:record:restoration`, `lem:var-gain`(a), `cor:var-classes`) and
the evaluations `hρ`, `hπ`, `hrr`. -/
noncomputable def VarStepsAt.ofRecords {L : ℕ} {A : Finset ℤ} (Rc : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ Rc, IsSelection ω) (π ρ rr : Choice (D.CL.T L) → ℝ) {WZ z K : ℝ}
    (m : Choice (D.CL.T L) → ∀ b : BlockAtom Bk J L,
      (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hm : ∀ ω ∈ Rc, ∀ b ∈ Choice.support ω, ∀ x, 0 ≤ m ω b x)
    (γ : Choice (D.CL.T L) → BlockAtom Bk J L → ℝ)
    (hγ : ∀ ω ∈ Rc, ∀ b ∈ Choice.support ω, 0 ≤ γ ω b)
    (hζ : ∀ ω ∈ Rc, ∀ b ∈ Choice.support ω,
      ∀ G H : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ,
      |reservedCut.form (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)) G H| ≤
        γ ω b * Real.sqrt (reservedCut.form (reservedCut.diagonalLaw (m ω b) -
          indepLaw reservedCut (m ω b)) G G) *
        Real.sqrt (reservedCut.form (reservedCut.diagonalLaw (m ω b) -
          indepLaw reservedCut (m ω b)) H H))
    (CX : Choice (D.CL.T L) → ℝ) (hCX : ∀ ω ∈ Rc, 0 ≤ CX ω)
    (JO rD rJ : Choice (D.CL.T L) → ℝ) (r₀ Bf Rerr Rstar bt : ℝ) (hr₀ : 0 ≤ r₀)
    (hrJ : ∀ ω ∈ Rc, 0 ≤ rJ ω) (hRs : Rerr ≤ Rstar)
    (hDN : ∀ ω ∈ Rc, varDiag D L A ω (m ω) ≤ (Bf + z) * CX ω * D.Y L A + rD ω)
    (hJN : ∀ ω ∈ Rc, JO ω - (Rerr + z) * CX ω * D.Y L A - rJ ω ≤ varJ D L A ω (m ω))
    (hres : (bt - z) * (∑ ω ∈ Rc, (∏ b ∈ Choice.support ω, γ ω b) * CX ω) * D.Y L A - r₀ ≤
      ∑ ω ∈ Rc, (∏ b ∈ Choice.support ω, γ ω b) * JO ω)
    (hWZ : 0 ≤ WZ)
    (hρ : (Bf - max 0 (bt - Rstar)) * (∑ ω ∈ Rc, (∏ b ∈ Choice.support ω, γ ω b) * CX ω) ≤
      ∑ ω ∈ Rc, ρ ω)
    (hπ : ∀ ω ∈ Rc, 3 * ((∏ b ∈ Choice.support ω, γ ω b) * CX ω) ≤ K * π ω)
    (hrr : ∑ ω ∈ Rc, (∏ b ∈ Choice.support ω, γ ω b) * (rD ω + rJ ω) + r₀ ≤ ∑ ω ∈ Rc, rr ω) :
    VarStepsAt Rc (fun ω => term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω) π ρ rr
      WZ (D.Y L A) z K where
  DN ω := varDiag D L A ω (m ω)
  JN ω := varJ D L A ω (m ω)
  JO := JO
  γ ω := ∏ b ∈ Choice.support ω, γ ω b
  CX := CX
  rD := rD
  rJ := rJ
  r₀ := r₀
  Bf := Bf
  Rerr := Rerr
  Rstar := Rstar
  bt := bt
  hγ ω hω := prod_nonneg (hγ ω hω)
  hCX := hCX
  hr₀ := hr₀
  hrJ := hrJ
  hRs := hRs
  hI ω hω := abs_term_le_variance D L A ω (hsel ω hω) (m ω) (hm ω hω) (γ ω) (hγ ω hω) (hζ ω hω)
  hJN0 ω hω := varJ_nonneg D L A ω (m ω) (hm ω hω)
  hDN := hDN
  hJN := hJN
  hres := hres
  hWZ := hWZ
  hρ := hρ
  hπ := hπ
  hrr := hrr

end Paper

end Sarkozy.ClassInputsPaper

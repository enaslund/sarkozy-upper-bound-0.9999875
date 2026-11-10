module

public import Sarkozy.OpsVariance.Selection

@[expose] public section

/-!
# The class-cost step of a variance class at the paper's objects (`VarStepsAt`)

`paper/sections/22_variance.tex`, `prop:background-variance`(a) ("The class cost"),
`lem:var-gain`(b),
`cor:var-classes`, `lem:record:restoration`; `paper/sections/10_comparison_lemmas.tex`,
`lem:record:variance-interface`(i),(ii), (E1), (E2).

B10's `VarStepsAt R I π ρ rr WZ Y z K` is the second conjunct of `ClassStepsOps.H`
(`MainFinal2/Bundles.lean`), with `I = termAt`, `π = monomial (D.CL.π L)`. Its data are free; here
they are fixed to the paper's objects of the selections `ω ∈ R`:

| field | value | where it comes from |
|---|---|---|
| `γ ω` | `π̃_ω = monomial (D.CL.πt L) ω` | (CP4)(b) |
| `CX ω` | `C_X = ∏_{𝔅 ∈ X} q_𝔅^{2a}` (`selProd`) | `def:price` |
| `DN ω` | `Y[Diag_X ⊗ Ñ] = Y[(⊗_X D) ⊗ Ñ]` (`varDiag_envM`) | the norm envelopes |
| `JN ω` | `Y[J_X ⊗ Ñ]` (`varJ` at `envM`) | `lem:record:variance-interface` |
| `JO ω` | `Y[J_X ⊗ Ñ₀]` (`varJ0` at `envM`) | `prop:background-variance`(a) |
| `Bf` | `B = e^{U₀} + R_err` (`D.B`) | (CP3) |
| `Rerr` | `R_err = e^{U₀} 𝔗(d, v)` (`D.GB.Rerr`) | (CP3) |

so that `γ ω · CX ω = π_ω` (`monomial_π_eq`), and the price field `hπ` holds for every `K ≥ 3`.

Two constructors:

* **`varStepsAt_noCredit`** (`g = 0`): every field is proved except (E1) for the envelopes of the
  selections (`hEnv`, the paper's `EnvelopeBoundNonneg`, proved at the paper's data by EC), the
  residual `ρ ≥ B π` and the remainder budget. This is the case `b̃ ≤ R_*` of the proof of
  `prop:background-variance`(a) ("`g_E(m) = 0` and `|I_{ω_s}| ≤ γ Y^Ñ[Diag] ≤ (B + o(1)) π Y`").
* **`varStepsAt_credit`** (gain `[b̃ − R_*]_+`): `hI` (`abs_term_le_envVariance`, given zero
  marginals), `hJN0` ((E2)), `hDN` (from `hEnv`), `hπ`, `hRs` are proved; the inputs are the zero
  marginals of the selected record changes (`eq:record:zero-marginal`), the comparison
  `Y[J_X ⊗ Ñ] ≥ Y[J_X ⊗ Ñ₀] − (R_err + z) C_X Y − r_J` (`hJN`, the last bound of (E1)), the
  restoration lower bound `hres` and the residual `hρ`.

`hres_of_average` turns the paper's averaged form of the restoration (`lem:var-gain`(a):
`|R|⁻¹ ∑_φ Y[J_φ] ≥ (l̄ − o(1)) C_X Y`; `prop:background-variance`(a):
`½ ∑_s Y^{Ñ₀}[J_s] ≥ (C_m b̃ − o(1)) Y`) into `hres`, for a class with common prices (the
hypothesis of `lem:var-gain` and `cor:var-classes`).
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

/-- The energy `Y[J_X ⊗ Ñ₀]` of a selection: the product laws of the half marginals on the
support, the background `Ñ₀` of (CP3) elsewhere (`prop:background-variance`(a)). -/
noncomputable def varJ0 (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (m : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw fun b => if b ∈ Choice.support ω then
    indepLaw reservedCut (m b) else D.GB.N₀ L b) (blockLift m₀ blk p L A)

/-- The envelope energy `Y[(⊗_X D^{ε}_{𝔅,t}) ⊗ Ñ]` of a selection (the left side of (E1)). -/
noncomputable abbrev envEnergy (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) : ℝ :=
  diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (blockLift m₀ blk p L A)

variable {D}

omit [DecidableEq P] in
/-- `∑_R γ C_X = ∑_R π`. -/
theorem sum_gam_CX (L : ℕ) (R : Finset (Choice (D.CL.T L))) :
    ∑ ω ∈ R, monomial (D.CL.πt L) ω * selProd D L ω = ∑ ω ∈ R, monomial (D.CL.π L) ω :=
  sum_congr rfl fun ω _ => (monomial_π_eq L ω).symm

omit [DecidableEq P] in
/-- **The class-cost step of a variance class with no credit** (`g = 0`; the case `b̃ ≤ R_*` of the
proof of `prop:background-variance`(a), and of `lem:var-gain`(b)). `γ = π̃_ω`, `C_X`,
`DN = Y[(⊗_X D) ⊗ Ñ]`, `JN = JO = 0`, `b̃ = R_err = R_* = 0`, `Bf = B`. Every field is proved
except:
* `hEnv`: (E1) for the envelopes of the selections of `R` (`lem:bracket-energy`; the paper's
  `ComparisonData.EnvelopeBoundNonneg`, proved at the paper's data by EC);
* `hρ`: the residual carries the full cost, `B π_ω ≤ ρ_ω`;
* `hrr`: the remainder budget `∑_R π̃_ω r_D(ω) ≤ ∑_R rr`. -/
theorem varStepsAt_noCredit {L : ℕ} {A : Finset ℤ} (R : Finset (Choice (D.CL.T L)))
    (ρ rr rD : Choice (D.CL.T L) → ℝ) {WZ z K : ℝ} (hz : 0 ≤ z) (hY : 0 ≤ D.Y L A)
    (hEnv : ∀ ω ∈ R, envEnergy D L A ω ≤ (D.B + z) * selProd D L ω * D.Y L A + rD ω)
    (hWZ : 0 ≤ WZ) (hρ : ∀ ω ∈ R, D.B * monomial (D.CL.π L) ω ≤ ρ ω) (hK : 3 ≤ K)
    (hrr : ∑ ω ∈ R, monomial (D.CL.πt L) ω * rD ω ≤ ∑ ω ∈ R, rr ω) :
    Nonempty (VarStepsAt R (termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) ρ rr WZ
      (D.Y L A) z K) := by
  refine ⟨{
    DN := fun ω => envEnergy D L A ω
    JN := fun _ => 0
    JO := fun _ => 0
    γ := fun ω => monomial (D.CL.πt L) ω
    CX := fun ω => selProd D L ω
    rD := rD
    rJ := fun _ => 0
    r₀ := 0
    Bf := D.B
    Rerr := 0
    Rstar := 0
    bt := 0
    hγ := fun ω _ => monomial_πt_nonneg L ω
    hCX := fun ω _ => selProd_nonneg L ω
    hr₀ := le_refl 0
    hrJ := fun _ _ => le_refl 0
    hRs := le_refl 0
    hI := fun ω _ => by
      rw [sub_zero]
      exact abs_term_le_envelope_paper L A ω
    hJN0 := fun _ _ => le_refl 0
    hDN := hEnv
    hJN := fun ω _ => by
      have := mul_nonneg (mul_nonneg (zero_add z ▸ hz) (selProd_nonneg L ω)) hY
      linarith
    hres := by
      simp only [zero_sub, mul_zero, sum_const_zero, sub_zero]
      have h1 : 0 ≤ ∑ ω ∈ R, monomial (D.CL.πt L) ω * selProd D L ω :=
        sum_nonneg fun ω _ => mul_nonneg (monomial_πt_nonneg L ω) (selProd_nonneg L ω)
      have := mul_nonneg (mul_nonneg hz h1) hY
      linarith
    hWZ := hWZ
    hρ := ?_
    hπ := ?_
    hrr := ?_ }⟩
  · simp only [sub_self, max_self, sub_zero]
    rw [sum_gam_CX, mul_sum]
    exact sum_le_sum hρ
  · intro ω _
    rw [← monomial_π_eq]
    exact mul_le_mul_of_nonneg_right hK (monomial_π_nonneg L ω)
  · simp only [add_zero]
    exact hrr

omit [DecidableEq P] in
/-- **The class-cost step of a variance class with the variance credit**
(`prop:background-variance`(a) "The class cost", `lem:var-gain`(b)), at the paper's objects:
`γ = π̃_ω`, `C_X`, `DN = Y[Diag_X ⊗ Ñ]`, `JN = Y[J_X ⊗ Ñ]`, `JO = Y[J_X ⊗ Ñ₀]` with the half
marginals `envM` of the norm envelopes, `Bf = B`, `Rerr = R_err`. Proved: `hI`
(`lem:record:variance-interface`(i), `abs_term_le_envVariance`), `hJN0` ((E2)), `hDN` (from `hEnv`),
`hπ` (`K ≥ 3`). Inputs:
* `hz0`: the zero marginals of the selected record changes (`eq:record:zero-marginal`);
* `hEnv`: (E1) for the envelopes of the selections (`lem:bracket-energy`);
* `hJN`: `Y[J_X ⊗ Ñ] ≥ Y[J_X ⊗ Ñ₀] − (R_err + z) C_X Y − r_J` (`lem:record:variance-interface`(ii),
  the last bound of (E1) at `J_X`);
* `hres`: the restoration lower bound `∑_R π̃ Y[J_X ⊗ Ñ₀] ≥ (b̃ − z)(∑_R π) Y − r₀`
  (`lem:record:restoration`, `lem:var-gain`(a), `prop:background-variance`(a) displayed bound);
* `hρ`: the residual carries the class cost, `(B − [b̃ − R_*]_+) π_ω ≤ ρ_ω`;
* `hrr`: the remainder budget. -/
theorem varStepsAt_credit {L : ℕ} {A : Finset ℤ} (R : Finset (Choice (D.CL.T L)))
    (hsel : ∀ ω ∈ R, IsSelection ω) (ρ rr rD rJ : Choice (D.CL.T L) → ℝ) {WZ z K : ℝ}
    (r₀ Rstar bt : ℝ) (hr₀ : 0 ≤ r₀) (hrJ : ∀ ω ∈ R, 0 ≤ rJ ω) (hRs : D.GB.Rerr ≤ Rstar)
    (hz0 : ∀ ω ∈ R, RecordsZeroMarginal D L ω)
    (hEnv : ∀ ω ∈ R, envEnergy D L A ω ≤ (D.B + z) * selProd D L ω * D.Y L A + rD ω)
    (hJN : ∀ ω ∈ R, varJ0 D L A ω (envM D L ω) - (D.GB.Rerr + z) * selProd D L ω * D.Y L A -
      rJ ω ≤ varJ D L A ω (envM D L ω))
    (hres : (bt - z) * (∑ ω ∈ R, monomial (D.CL.π L) ω) * D.Y L A - r₀ ≤
      ∑ ω ∈ R, monomial (D.CL.πt L) ω * varJ0 D L A ω (envM D L ω))
    (hWZ : 0 ≤ WZ)
    (hρ : ∀ ω ∈ R, (D.B - max 0 (bt - Rstar)) * monomial (D.CL.π L) ω ≤ ρ ω) (hK : 3 ≤ K)
    (hrr : ∑ ω ∈ R, monomial (D.CL.πt L) ω * (rD ω + rJ ω) + r₀ ≤ ∑ ω ∈ R, rr ω) :
    Nonempty (VarStepsAt R (termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) ρ rr WZ
      (D.Y L A) z K) := by
  refine ⟨{
    DN := fun ω => varDiag D L A ω (envM D L ω)
    JN := fun ω => varJ D L A ω (envM D L ω)
    JO := fun ω => varJ0 D L A ω (envM D L ω)
    γ := fun ω => monomial (D.CL.πt L) ω
    CX := fun ω => selProd D L ω
    rD := rD
    rJ := rJ
    r₀ := r₀
    Bf := D.B
    Rerr := D.GB.Rerr
    Rstar := Rstar
    bt := bt
    hγ := fun ω _ => monomial_πt_nonneg L ω
    hCX := fun ω _ => selProd_nonneg L ω
    hr₀ := hr₀
    hrJ := hrJ
    hRs := hRs
    hI := fun ω hω => abs_term_le_envVariance L A ω (hsel ω hω) (hz0 ω hω)
    hJN0 := fun ω _ => varJ_nonneg D L A ω (envM D L ω) fun b _ x => envM_nonneg L ω b x
    hDN := fun ω hω => by
      rw [varDiag_envM]
      exact hEnv ω hω
    hJN := hJN
    hres := by
      rw [sum_gam_CX]
      exact hres
    hWZ := hWZ
    hρ := ?_
    hπ := ?_
    hrr := hrr }⟩
  · rw [sum_gam_CX, mul_sum]
    exact sum_le_sum hρ
  · intro ω _
    rw [← monomial_π_eq]
    exact mul_le_mul_of_nonneg_right hK (monomial_π_nonneg L ω)

/-- **The restoration bound from its averaged form, for a class with common prices**
(`lem:var-gain`(a), `prop:background-variance`(a): the prices `π̃_ω = γ₀` and `C_X = C₀` are the
same for every selection of the class, `cor:var-classes`): if
`(C_m b̃ − z_b) Y |R| ≤ ∑_R JO` with `b̃ ≥ 0`, `1 ≤ C₀ ≤ C_m`, `0 ≤ z_b ≤ z`, then
`(b̃ − z) (∑_R γ C_X) Y ≤ ∑_R γ JO` (`hres` with `r₀ = 0`). This is the step "`C_m b̃ ≥ C_X b̃` for
`b̃ > 0`, and `o(1) Y ≤ o(1) C_X Y` as `C_X ≥ 1`" of the paper's class cost. -/
theorem hres_of_average {ι : Type*} (R : Finset ι) (γ CX JO : ι → ℝ) {γ₀ C₀ Cm bt zb z Y : ℝ}
    (hγ : ∀ ω ∈ R, γ ω = γ₀) (hCX : ∀ ω ∈ R, CX ω = C₀) (hγ₀ : 0 ≤ γ₀) (hC₀ : 1 ≤ C₀)
    (hCm : C₀ ≤ Cm) (hbt : 0 ≤ bt) (hzb : 0 ≤ zb) (hzz : zb ≤ z) (hY : 0 ≤ Y)
    (havg : (Cm * bt - zb) * Y * R.card ≤ ∑ ω ∈ R, JO ω) :
    (bt - z) * (∑ ω ∈ R, γ ω * CX ω) * Y - 0 ≤ ∑ ω ∈ R, γ ω * JO ω := by
  have e1 : ∑ ω ∈ R, γ ω * CX ω = R.card * (γ₀ * C₀) := by
    rw [sum_congr rfl fun ω hω => by rw [hγ ω hω, hCX ω hω], sum_const, nsmul_eq_mul]
  have e2 : ∑ ω ∈ R, γ ω * JO ω = γ₀ * ∑ ω ∈ R, JO ω := by
    rw [mul_sum]
    exact sum_congr rfl fun ω hω => by rw [hγ ω hω]
  rw [e1, e2, sub_zero]
  have hcard : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  -- `(b̃ − z) C₀ ≤ C_m b̃ − z_b`
  have hk : (bt - z) * C₀ ≤ Cm * bt - zb := by
    have h1 : C₀ * bt ≤ Cm * bt := mul_le_mul_of_nonneg_right hCm hbt
    have h2 : zb ≤ z * C₀ := by nlinarith
    nlinarith
  have hk' : (bt - z) * C₀ * Y * R.card ≤ (Cm * bt - zb) * Y * R.card :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hk hY) hcard
  have := mul_le_mul_of_nonneg_left (hk'.trans havg) hγ₀
  nlinarith [this]

end Sarkozy.OpsVariance

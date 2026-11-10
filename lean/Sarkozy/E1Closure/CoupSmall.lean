module

public import Sarkozy.E1Closure.CoupFolded

@[expose] public section

/-!
# The coupled pieces with a small union, proved (`lem:sharp-first`, term `T′`) (EC)

EC, 8 November 2026. **`e1CoupSmallPT_proved`**: on the paper's tails, with `a ≥ 0`, the parity
condition, `blockSel ≤ selPre` and nonempty blocks, there is `c ≥ 0` with
`E1CoupSmallPT D u c` (`u = sfEps D = u_L`). That is, at every least counterexample, every
coupled piece `f` (selection `ω`, choice `σ ≠ ∅`, tag `j` present, nonzero coefficients) with a
small union satisfies `|𝔈_{ω,f}| ≤ (∏_𝔟 g_𝔟)(1 + u_L) Y + (∏_𝔟 cM_𝔟) C_dc L^{-σ} α`.

The proof is the paper's proof of `lem:sharp-first` for one term `T′`:

* `lem:record:folded-energy` at the cut `c_j` (`folded_energy_tensor`, with the brackets
  `e_bracket`): `|𝔈| ≤ (∏ d) √𝔈₊ √𝔈₋`, `d = d̃` at the whole differences;
* `prop:record:density-structured` once for each folded energy (SR's `whole_chain`; the folded
  laws are positive records equal to `μ_𝔟` off the union `E`, and `q_E ≤ N^τ` gives the modulus
  conditions through DC3's `moduli_paper`):
  `𝔈_± ≤ (∏ m)((1 + u_L) sq(D_E)^a Y + C_dc L^{-σ} α)`;
* `√𝔈₊ √𝔈₋ ≤ (𝔈₊ + 𝔈₋)/2` and the price bookkeeping `(∏ d)(∏ m) sq(D_E)^a ≤ ∏ g`
  (`coupPrice_le`), `(∏ d)(∏ m) ≤ ∏ cM` (`coupRem_le`).

With `e1CoupSmall_of_perTerm` this gives **`e1CoupSmall_proved`**: `E1CoupSmall` at `ε_E = u_L`.
-/

namespace Sarkozy.E1Closure

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg whole_chain)

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E)

omit [DecidableEq P] in
/-- **`E1CoupSmallPT`, proved** (the term `T′` of `lem:sharp-first` with a small union; see the
module docstring). -/
theorem e1CoupSmallPT_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ E1CoupSmallPT D (sfEps D) c := by
  classical
  obtain ⟨C1, C71, hC1, hC71, hdcb⟩ := density_dc_block' (1 / 10 : ℝ) (by norm_num)
  have hM0 : 1 ≤ modulus pr h := Nat.one_le_iff_ne_zero.mpr (NeZero.ne _)
  have hQ1 : 1 ≤ cliqueConstant m₀ D.S.ep :=
    Nat.one_le_iff_ne_zero.mpr (prod_ne_zero_iff.mpr fun i _ => NeZero.ne _)
  set Cdc := dcConstant (prefixConductor (m₀ := m₀) blk D.R.P5) Sarkozy.AnalyticStage.γ
    (modulus pr h) (Fintype.card (ResidueSpace (blockModulus m₀ blk))) C1 C71 with hCdc
  have hCdc0 : 0 ≤ Cdc := dcConstant_nonneg (by exact_mod_cast (prefixConductor_pos blk _).le)
    (Nat.cast_nonneg _) hC1.le hC71.le
  refine ⟨Cdc, hCdc0, ?_⟩
  unfold E1CoupSmallPT
  filter_upwards [eventually_scaleConditions blockScale (modulus pr h) (cliqueConstant m₀ D.S.ep)
    1 0 0 (by norm_num [blockScale]) hM0 hQ1, eventually_ge_atTop 2] with L hsc hL
  intro C hC hk A hA hY ω hω σ _ j _ f hcf hs
  have hcex : IsLeastCounterexample D.Y a densityExponent C L A :=
    ⟨hA, hY, fun ℓ h1 h2 => hk ℓ h1 h2⟩
  have hC0 : (0 : ℝ) ≤ C := zero_le_one.trans hC
  have hcd : (0 : ℝ) ≤ Sarkozy.cancellationDecay := by
    unfold Sarkozy.cancellationDecay; norm_num
  have hY0 : 0 ≤ D.Y L A := (Param.counterexample_pos (Params.ofDecay a) hC hY).le
  set dec : DecFamily D L := Classical.choice (nonempty_decFamily D L) with hdec
  set g := blockLift m₀ blk paperTail L A with hgdef
  -- the folded factorization
  have hfe := folded_energy_tensor (D.FS.cut j) (fun b => eK D L j b (ω b) (f b))
    (fun b => eLp D L dec j b (ω b) (f b)) (fun b => eLm D L dec j b (ω b) (f b))
    (fun b => eD D L b (f b)) (fun b => eD_nonneg D L b (f b))
    (fun b => eLp_positive D L dec j b (ω b) (f b)) (fun b => eLm_positive D L dec j b (ω b) (f b))
    (fun b => e_bracket D L dec j b (ω b) (f b)) (fun _ => g)
  obtain ⟨hFp0, hFm0, hfold⟩ := hfe
  set Fp := multilinearIntegral (tensorLaw fun b => eLp D L dec j b (ω b) (f b))
    ((fun _ => g) ∘ (D.FS.cut j).foldPlus) with hFp
  set Fm := multilinearIntegral (tensorLaw fun b => eLm D L dec j b (ω b) (f b))
    ((fun _ => g) ∘ (D.FS.cut j).foldMinus) with hFm
  have hK : coupInt D L A ω f =
      multilinearIntegral (tensorLaw fun b => eK D L j b (ω b) (f b)) (fun _ => g) := by
    unfold coupInt diagonalIntegral
    congr 2
    funext b
    exact ecpieceK_eq_eK D L j ω σ b (f b) (hcf b)
  -- the modulus conditions
  obtain ⟨qE, cE, hDE, hqE, hcE, hcE0, hcQ, hcopE, hqN⟩ : ∃ qE cE : ℕ,
      ∏ b ∈ coupAtoms D L ω f, crtModuli m₀ blk paperTail L b = qE * cE ∧ Squarefree qE ∧
      IsSquare cE ∧ cE ≠ 0 ∧ cE ≤ cliqueConstant m₀ D.S.ep ∧ qE.Coprime cE ∧
      (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau := by
    rcases moduli_paper D hpair hpar le_rfl L (((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (coupAtoms D L ω f) with h1 | h1
    · exact h1
    · exfalso
      rw [← prod_coupQ_eq] at h1
      exact absurd hs (not_le.mpr h1)
  have hEne := prod_crtModuli_ne_one D hne (coupAtoms_nonempty D hω f)
  have hEp : ∀ b ∉ coupAtoms D L ω f, eLp D L dec j b (ω b) (f b) = D.R.law paperTail L b :=
    fun b hb => eLp_of_mu D L dec j b (ω b) (f b) (by
      simpa [coupAtoms] using hb)
  have hEm : ∀ b ∉ coupAtoms D L ω f, eLm D L dec j b (ω b) (f b) = D.R.law paperTail L b :=
    fun b hb => eLm_of_mu D L dec j b (ω b) (f b) (by
      simpa [coupAtoms] using hb)
  have hchp := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0
    (fun b => eLp D L dec j b (ω b) (f b)) (coupAtoms D L ω f) hEp
    (fun b _ => isPositiveRecord_eLp D L dec j (D.S.p_prime L) b (ω b) (f b)) hEne hDE hqE hcE
    hcE0 hcQ hcopE hqN hcd S1_at_cancellationDecay
  have hchm := whole_chain hdcb D hpair hcex ha hC0 hL hsc hM0
    (fun b => eLm D L dec j b (ω b) (f b)) (coupAtoms D L ω f) hEm
    (fun b _ => isPositiveRecord_eLm D L dec j (D.S.p_prime L) b (ω b) (f b)) hEne hDE hqE hcE
    hcE0 hcQ hcopE hqN hcd S1_at_cancellationDecay
  obtain ⟨hmp, hmm⟩ := prod_mass_coupAtoms D L dec j ω f
  rw [hmp] at hchp
  rw [hmm] at hchm
  set m := ∏ b, eMass D L b (f b) with hmdef
  set dd := ∏ b, eD D L b (f b) with hdd
  set s := ((leastSquare (∏ b ∈ coupAtoms D L ω f, crtModuli m₀ blk paperTail L b) : ℕ) : ℝ) ^ a
    with hsdef
  set u := sfEps D L with hudef
  set K := Cdc * (L : ℝ) ^ (-Sarkozy.cancellationDecay) * density (blockScale * L) A with hKdef
  set M := m * ((1 + u) * s * D.Y L A + K) with hMdef
  have hFpM : Fp ≤ M := (le_abs_self _).trans hchp
  have hFmM : Fm ≤ M := (le_abs_self _).trans hchm
  have hdd0 : 0 ≤ dd := prod_nonneg fun b _ => eD_nonneg D L b (f b)
  have hgeo : Real.sqrt Fp * Real.sqrt Fm ≤ M := by
    refine (Sarkozy.LargeSums.sqrt_mul_sqrt_le_abs Fp Fm).trans ?_
    rw [abs_of_nonneg hFp0, abs_of_nonneg hFm0]
    linarith
  have h1 : |coupInt D L A ω f| ≤ dd * M := by
    rw [hK]
    refine hfold.trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hgeo hdd0
  have hpr := coupPrice_le D hpair hpar hsel L ω f
  have hrm := coupRem_le D L f
  have hu0 := sfEps_nonneg D L
  have hK0 : 0 ≤ K := mul_nonneg (mul_nonneg hCdc0 (Real.rpow_nonneg (Nat.cast_nonneg _) _))
    (density_nonneg _ _)
  have hcY : 0 ≤ (1 + u) * D.Y L A := mul_nonneg (by linarith) hY0
  have h2 : dd * M ≤ (∏ b, ecpieceG D L ω b (f b)) * ((1 + u) * D.Y L A) +
      (∏ b, cM D L b (f b)) * K := by
    have e : dd * M = (dd * m * s) * ((1 + u) * D.Y L A) + (dd * m) * K := by
      rw [hMdef]
      ring
    rw [e]
    exact add_le_add (mul_le_mul_of_nonneg_right hpr hcY) (mul_le_mul_of_nonneg_right hrm hK0)
  have hrem : remainder Cdc L A = K := rfl
  change |coupInt D L A ω f| ≤ coupMain D (sfEps D) L A ω f + (∏ b, cM D L b (f b)) *
    remainder Cdc L A
  rw [hrem]
  exact h1.trans h2

omit [DecidableEq P] in
/-- **`E1CoupSmall`, proved** at `ε_E = u_L` (`e1CoupSmallPT_proved`,
`e1CoupSmall_of_perTerm`). -/
theorem e1CoupSmall_proved
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (paperTail L) i).Coprime
      (joinModuli m₀ (paperTail L) j))
    (ha : 0 ≤ a) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (hne : ∀ β, ∃ i, blk i = β) :
    ∃ c : ℝ, 0 ≤ c ∧ E1CoupSmall D (sfEps D) c := by
  obtain ⟨c₁, hc₁, h⟩ := e1CoupSmallPT_proved D hpair ha hpar hsel hne
  exact ⟨_, mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le) hc₁,
    e1CoupSmall_of_perTerm D ha hc₁ h⟩

end Sarkozy.E1Closure

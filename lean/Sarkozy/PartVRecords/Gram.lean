module

public import Sarkozy.PartVRecords.Frame

@[expose] public section

/-!
# The `2 × 2` block dominating `λ` at `ι` (`lem:record:gram`)

`paper/sections/20c_middle_frame.tex`, `subsec:middle-gram`, `lem:record:gram`.

For the frame of a middle block (`Sarkozy.PartVRecords.FrameData`):

* (i) `μ ⪯_ι Ñ₀`, and `Ñ₀ - μ = E_add + G + H` is a nonnegative reserved-diagonal measure
  (`gram_i`);
* (ii) `Ñ = Ñ₀ + δ_E = λ + F_fold + H` is nonnegative (`Nbr_nonneg`), `λ` is symmetric at `ι`
  (`lam_symmetric`), and `Ñ ± λ ⪰_ι 0` (`Nbr_sub_lam_positive`, `Nbr_add_lam_positive`), so the
  block `(Ñ λ; λ Ñ)` is positive at `ι` (`gram_bracket`, as `ReflectionCut.Bracket`, the form of
  `def:cp3` used by `TheoremC.GramBracket`); in particular `-Ñ ⪯_ι λ ⪯_ι Ñ`.

The proof of `Ñ + λ ⪰_ι 0` is the paper's, summand by summand in `2 μ̃_𝔅`
(`twoMu_reserved_positive`):
* the folds `Π_{F_s}`, `s = 1, 2`: `2 w_D r Π_{F_s} + v_D r² Diag_ι(Π⁽¹⁾_{F_s}) ⪰_ι 0` is the
  protection `lem:front12:reference`(iv) (V1's `middle_protection`, from the D layer caps and
  `eq:protection`);
* the matchings `Π_{E_s}`: `2 w_S r (Π_{E_s} + 3/(b - 3) Diag_ι(Π⁽¹⁾_{E_s})) ⪰_ι 0` is the
  disjoint-triple bound of `sec:frontier:empty-triple-negative`(c) on the block, **taken as a
  hypothesis** (`MatchingReservedBound`; the one-prime bound `T̄ ⪰ -3/(n-3)` is WP-S's
  `Sarkozy.TraceMixing.tripleOp_ge`, the tensor step over the primes of the block is not
  formalized here);
* every other component (the root, the aligned fold `Π_{F₀}`, the merges, the constants) keeps
  its two-layer part and its folded part, positive together at `ι` by the layer caps of
  `lem:front12:reference`(ii) (V1's `MiddleLayerCaps`, a hypothesis) and the third line
  `v_𝔱 ≥ k_𝔱 w_𝔱` of the thirteen inequalities.

Only the caps of the types `L, D, R, C` are used (the S caps are not), but the hypothesis is V1's
`MiddleLayerCaps` for all types, as stated in the paper. The symmetry of `λ` uses the layer-swap
invariance of the two-layer field laws (V1's `middleTilde_layerSwap`; proved by V1 for the uniform
and the individual-square roots).

`gram_cp3` packages the per-block facts in the shape of the fields of `TheoremC.GramBracket`
(`κu_pos`, `κu_diag`, `N₀_sub`, `lam_sym`, `N_nonneg`, `bracket`), with `Ñ₀ - μ` written as a sum
of six positive reserved-diagonal records.
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.TheoremC Sarkozy.RecordExpansion

variable {X : Type} [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
theorem isSymmetricAt_sub {c : ReflectionCut Slot} {L M : SlotMeasure X}
    (hL : IsSymmetricAt c L) (hM : IsSymmetricAt c M) : IsSymmetricAt c (L - M) := by
  have h := hL.add (hM.smul (-1))
  have he : L + (-1 : ℝ) • M = L - M := by
    apply LinearMap.ext
    intro f
    simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_eq_mul]
    ring
  rwa [he] at h

namespace FrameData

variable (D : FrameData X)

/-- **The disjoint-triple bound for the matching components at `ι`**
(`sec:frontier:empty-triple-negative`(c) on the block, used in the proof of `lem:record:gram`(ii)):
`Π_{E_s} + 3/(b - 3) Diag_ι(Π⁽¹⁾_{E_s}) ⪰_ι 0` for `s = 0, 1`. The cut operator of `Π_{E_s}` at `ι`
relative to its actual half law (the uniform law on injective triples, the half law of
`Π⁽¹⁾_{E_s}`) is the disjoint-triple operator at each prime, whose spectrum on the block lies in
`[-3/(b - 3), 1]`. **Hypothesis.** -/
def MatchingReservedBound : Prop :=
  ∀ s : Fin 2, reservedCut.Positive (D.two .S s + (3 / (D.b - 3)) • D.diag .S s)

/-- **`lem:record:gram`(i)**: `μ ⪯_ι Ñ₀`, and `Ñ₀ - μ = E_add + G + H` (divided by `P(r)`) is a
nonnegative reserved-diagonal measure. -/
theorem gram_i (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) :
    reservedCut.Below D.mu D.Nbr0 ∧ D.Nbr0 - D.mu = D.P⁻¹ • (D.Eadd + D.Gpol + D.Hdiag) ∧
      IsNonneg (D.Nbr0 - D.mu) ∧ IsDiagonalAt reservedCut (D.Nbr0 - D.mu) := by
  obtain ⟨-, -, hEa, hG, hH, -⟩ := D.records_reserved_positive hfh hb
  obtain ⟨-, -, nEa, nG, nH, -⟩ := D.records_nonneg hfh hb
  obtain ⟨-, -, dEa, dG, dH, -⟩ := D.records_diagonal
  have hP := inv_nonneg.mpr D.P_pos.le
  refine ⟨?_, D.Nbr0_sub_mu, ?_, ?_⟩
  · change reservedCut.Positive (D.Nbr0 - D.mu)
    rw [D.Nbr0_sub_mu]
    exact ((hEa.add hG).add hH).smul hP
  · rw [D.Nbr0_sub_mu]
    exact nonneg_smul (nonneg_add (nonneg_add nEa nG) nH) hP
  · rw [D.Nbr0_sub_mu]
    exact diagonal_smul (diagonal_add (diagonal_add dEa dG) dH) _

/-- **`Ñ` is a nonnegative measure** (`lem:record:gram`(ii)). -/
theorem Nbr_nonneg (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) : IsNonneg D.Nbr := by
  obtain ⟨nF, -, -, -, nH, -⟩ := D.records_nonneg hfh hb
  exact nonneg_add (D.lam_nonneg hfh hb)
    (nonneg_smul (nonneg_add nF nH) (inv_nonneg.mpr D.P_pos.le))

/-- **`Ñ - λ = F_fold + H ⪰_ι 0`** (`lem:record:gram`(ii)). -/
theorem Nbr_sub_lam_positive (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b) :
    reservedCut.Positive (D.Nbr - D.lam) := by
  obtain ⟨hF, -, -, -, hH, -⟩ := D.records_reserved_positive hfh hb
  rw [D.Nbr_sub_lam]
  exact (hF.add hH).smul (inv_nonneg.mpr D.P_pos.le)

/-- One pattern of `μ̃_𝔅` is positive at `ι` under its layer cap and `v_𝔱 ≥ k_𝔱 w_𝔱` (the fold
pairing of `lem:five-type`(e), as in V1's `middleTilde_reserved_positive`). -/
theorem pairTerm_reserved_positive (hcap : MiddleLayerCaps D.F D.I.k D.r)
    (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t) (s : Σ t : PType, t.Pat) :
    reservedCut.Positive (D.pairTerm s) := by
  rcases s with ⟨t, φ⟩
  set A := signedIntegral (midComponent D.F (true, ⟨t, φ⟩)).weight
  set B := signedIntegral (midComponent D.F (false, ⟨t, φ⟩)).weight
  have key : D.pairTerm ⟨t, φ⟩ = (D.W.w t * D.r ^ t.deg) • (A - (-(D.I.k t * D.r)) • B) +
      ((D.W.v t - D.I.k t * D.W.w t) * D.r ^ (t.deg + 1)) • B := by
    apply LinearMap.ext
    intro f
    simp only [pairTerm, midCoeff, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sub_apply,
      smul_eq_mul, pow_succ, A, B]
    ring
  rw [key]
  exact ((hcap t φ).smul (mul_nonneg (D.W.w_nonneg t) (pow_nonneg D.r_nonneg _))).add
    ((middleDiag_reserved_positive D.F t φ).smul
      (mul_nonneg (sub_nonneg.mpr (hdom t)) (pow_nonneg D.r_nonneg _)))

/-- **`2 μ̃_𝔅 - F_fold - 2 E_fold + H ⪰_ι 0`**, summand by summand (the core of the proof of
`lem:record:gram`(ii)). -/
theorem twoMu_reserved_positive (hcap : MiddleLayerCaps D.F D.I.k D.r)
    (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t) (hP : D.W.Protects D.I)
    (hE : D.MatchingReservedBound) :
    reservedCut.Positive ((2 : ℝ) • D.muT - D.Ffold - (2 : ℝ) • D.Efold + D.Hdiag) := by
  have hexp := D.muT_eq_sum
  rw [sum_sigma_pType] at hexp
  have hD (j : Fin 3) : D.pairTerm ⟨.D, j⟩ =
      (D.W.w .D * D.r) • D.two .D j + (D.W.v .D * D.r ^ 2) • D.diag .D j := by
    simp only [pairTerm, midCoeff, PType.deg, pow_one]
    rfl
  have hS (s : Fin 2) : D.pairTerm ⟨.S, s⟩ =
      (D.W.w .S * D.r) • D.two .S s + (D.W.v .S * D.r ^ 2) • D.diag .S s := by
    simp only [pairTerm, midCoeff, PType.deg, pow_one]
    rfl
  have key : (2 : ℝ) • D.muT - D.Ffold - (2 : ℝ) • D.Efold + D.Hdiag =
      (2 : ℝ) • D.pairTerm ⟨.L, ()⟩ + (2 : ℝ) • D.pairTerm ⟨.D, (0 : Fin 3)⟩ +
      ((2 * D.W.w .D * D.r) • D.two .D (1 : Fin 3) + (D.W.v .D * D.r ^ 2) • D.diag .D (1 : Fin 3)) +
      ((2 * D.W.w .D * D.r) • D.two .D (2 : Fin 3) + (D.W.v .D * D.r ^ 2) • D.diag .D (2 : Fin 3)) +
      (2 * D.W.w .S * D.r) • (D.two .S (0 : Fin 2) + (3 / (D.b - 3)) • D.diag .S (0 : Fin 2)) +
      (2 * D.W.w .S * D.r) • (D.two .S (1 : Fin 2) + (3 / (D.b - 3)) • D.diag .S (1 : Fin 2)) +
      (2 : ℝ) • (∑ φ : PType.Pat .R, D.pairTerm ⟨.R, φ⟩ +
        ∑ φ : PType.Pat .C, D.pairTerm ⟨.C, φ⟩) := by
    rw [hexp, hD 0, hD 1, hD 2, hS 0, hS 1]
    apply LinearMap.ext
    intro f
    simp only [Ffold, Efold, Hdiag, hCoef, LinearMap.add_apply, LinearMap.sub_apply,
      LinearMap.smul_apply, smul_eq_mul]
    ring
  rw [key]
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hwS : 0 ≤ 2 * D.W.w .S * D.r :=
    mul_nonneg (mul_nonneg h2 (D.W.w_nonneg _)) D.r_nonneg
  have hRC : reservedCut.Positive
      (∑ φ : PType.Pat .R, D.pairTerm ⟨.R, φ⟩ + ∑ φ : PType.Pat .C, D.pairTerm ⟨.C, φ⟩) :=
    (ReflectionCut.Positive.sum _ fun φ _ => D.pairTerm_reserved_positive hcap hdom _).add
      (ReflectionCut.Positive.sum _ fun φ _ => D.pairTerm_reserved_positive hcap hdom _)
  refine (((((((D.pairTerm_reserved_positive hcap hdom _).smul h2).add
    ((D.pairTerm_reserved_positive hcap hdom _).smul h2)).add
    (middle_protection D.F D.W D.I D.r_nonneg hcap hP 1)).add
    (middle_protection D.F D.W D.I D.r_nonneg hcap hP 2)).add
    ((hE 0).smul hwS)).add ((hE 1).smul hwS)).add (hRC.smul h2)

/-- **`Ñ + λ ⪰_ι 0`** (`lem:record:gram`(ii)): `Ñ + λ = 2μ - F_fold - 2E_fold + H + 2E_new + 2G`
with `2μ̃ - F_fold - 2E_fold + H ⪰_ι 0` and `E_new`, `G` nonnegative reserved diagonal. -/
theorem Nbr_add_lam_positive (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b)
    (hcap : MiddleLayerCaps D.F D.I.k D.r) (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t)
    (hP : D.W.Protects D.I) (hE : D.MatchingReservedBound) :
    reservedCut.Positive (D.Nbr + D.lam) := by
  obtain ⟨-, -, -, hG, -, hN⟩ := D.records_reserved_positive hfh hb
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  rw [D.Nbr_add_lam]
  exact (((D.twoMu_reserved_positive hcap hdom hP hE).add (hN.smul h2)).add (hG.smul h2)).smul
    (inv_nonneg.mpr D.P_pos.le)

/-- **The block `(Ñ λ; λ Ñ)` is positive at `ι`** (`lem:record:gram`(ii), in the form
`ReflectionCut.Bracket Ñ λ Ñ` of `def:cp3`): conjugation by `2^{-1/2}(1 1; 1 -1)` turns it into
`diag(Ñ + λ, Ñ - λ)`. In particular `-Ñ ⪯_ι λ ⪯_ι Ñ`. -/
theorem gram_bracket (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b)
    (hcap : MiddleLayerCaps D.F D.I.k D.r) (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t)
    (hP : D.W.Protects D.I) (hE : D.MatchingReservedBound) :
    reservedCut.Bracket D.Nbr D.lam D.Nbr :=
  ReflectionCut.bracket_of_add_sub_positive (D.Nbr_add_lam_positive hfh hb hcap hdom hP hE)
    (D.Nbr_sub_lam_positive hfh hb)

/-- `μ̃_𝔅` is symmetric at `ι` when the two-layer field laws are invariant under the layer swap
(V1's `middleTilde_layerSwap`). -/
theorem muT_symmetric
    (hF : ∀ (f : FType) (H : (f.Obj × Fin 2 → X) → ℝ),
      (D.F.two f).expect (fun y => H (y ∘ layerSwapMap f.Obj)) = (D.F.two f).expect H) :
    IsSymmetricAt reservedCut D.muT := by
  apply LinearMap.ext
  intro f
  rw [reflect_apply]
  exact middleTilde_layerSwap D.F D.W D.r hF f

/-- **`λ_𝔅` is symmetric at `ι`** (`lem:record:gram`(ii)): the reference is invariant under the
layer swap and all records are reserved diagonal. -/
theorem lam_symmetric
    (hF : ∀ (f : FType) (H : (f.Obj × Fin 2 → X) → ℝ),
      (D.F.two f).expect (fun y => H (y ∘ layerSwapMap f.Obj)) = (D.F.two f).expect H) :
    IsSymmetricAt reservedCut D.lam := by
  obtain ⟨sF, sE, -, sG, -, sN⟩ := D.records_symmetric
  exact ((isSymmetricAt_sub (isSymmetricAt_sub (D.muT_symmetric hF) sF) sE).add sN |>.add sG).smul _

/-- `Ñ_𝔅` is symmetric at `ι` as well. -/
theorem Nbr_symmetric
    (hF : ∀ (f : FType) (H : (f.Obj × Fin 2 → X) → ℝ),
      (D.F.two f).expect (fun y => H (y ∘ layerSwapMap f.Obj)) = (D.F.two f).expect H) :
    IsSymmetricAt reservedCut D.Nbr := by
  obtain ⟨sF, -, -, -, sH, -⟩ := D.records_symmetric
  exact (D.lam_symmetric hF).add ((sF.add sH).smul _)

/-! ## The (CP3) interface -/

/-- The six positive reserved-diagonal records of `Ñ₀ - μ = E_add + G + H` (divided by `P(r)`):
the two halves of `E_add`, the two merge records of `G`, and the two half diagonals of `H`. -/
noncomputable def bracketRec : Fin 6 → SlotMeasure X
  | 0 => (D.P⁻¹ * (D.W.v .D * D.r ^ 2)) • D.diag .S (0 : Fin 2)
  | 1 => (D.P⁻¹ * (D.W.v .D * D.r ^ 2)) • D.diag .S (1 : Fin 2)
  | 2 => (D.P⁻¹ * ((D.I.f₁ + D.I.h₁) * D.r * (D.W.v .D * D.r ^ 2))) •
      D.diag .R ((0 : Fin 2), (0 : Fin 3))
  | 3 => (D.P⁻¹ * ((D.I.f₁ + D.I.h₁) * D.r * (D.W.v .D * D.r ^ 2))) •
      D.diag .R ((1 : Fin 2), (1 : Fin 3))
  | 4 => (D.P⁻¹ * D.hCoef) • D.diag .S (0 : Fin 2)
  | 5 => (D.P⁻¹ * D.hCoef) • D.diag .S (1 : Fin 2)

theorem Nbr0_sub_mu_eq_sum : D.Nbr0 - D.mu = ∑ i, D.bracketRec i := by
  rw [D.Nbr0_sub_mu, Fin.sum_univ_six]
  apply LinearMap.ext
  intro f
  simp only [bracketRec, Eadd, Gpol, Ge, Go, Hdiag, LinearMap.add_apply, LinearMap.smul_apply,
    smul_eq_mul]
  ring

/-- **`lem:record:gram` in the shape of (CP3)** (`def:cp3`, `TheoremC.GramBracket`) on one middle
block: `Ñ₀ - μ` is a sum of positive reserved-diagonal records (`κu_pos`, `κu_diag`, `N₀_sub`),
`λ` is symmetric at `ι` (`lam_sym`), `Ñ = Ñ₀ + δ_E` is nonnegative (`N_nonneg`) and the block
`(Ñ λ; λ Ñ)` is positive at `ι` (`bracket`). The positive-record property needs uniform vertex
marginals of the one-layer field laws. -/
theorem gram_cp3 [Nonempty X] (hfh : 0 ≤ D.I.f₁ + D.I.h₁) (hb : 3 < D.b)
    (hcap : MiddleLayerCaps D.F D.I.k D.r) (hdom : ∀ t, D.I.k t * D.W.w t ≤ D.W.v t)
    (hP : D.W.Protects D.I) (hE : D.MatchingReservedBound)
    (hF : ∀ (f : FType) (H : (f.Obj × Fin 2 → X) → ℝ),
      (D.F.two f).expect (fun y => H (y ∘ layerSwapMap f.Obj)) = (D.F.two f).expect H)
    (h1 : ∀ f (o : f.Obj × Fin 1) (g : X → ℝ),
      (D.F.one f).expect (fun y => g (y o)) = (FiniteLaw.uniform X).expect g) :
    (∀ i, IsPositiveRecord (D.bracketRec i)) ∧ (∀ i, IsDiagonalAt reservedCut (D.bracketRec i)) ∧
      D.Nbr0 - D.mu = ∑ i, D.bracketRec i ∧ IsSymmetricAt reservedCut D.lam ∧
      D.Nbr = D.Nbr0 + D.deltaE ∧ IsNonneg (D.Nbr0 + D.deltaE) ∧
      reservedCut.Bracket (D.Nbr0 + D.deltaE) D.lam (D.Nbr0 + D.deltaE) := by
  have hPi := inv_nonneg.mpr D.P_pos.le
  have hv := D.coef2_nonneg .D
  have hG : 0 ≤ (D.I.f₁ + D.I.h₁) * D.r * (D.W.v .D * D.r ^ 2) :=
    mul_nonneg (mul_nonneg hfh D.r_nonneg) hv
  have hH := D.hCoef_nonneg hb
  refine ⟨fun i => ?_, fun i => ?_, D.Nbr0_sub_mu_eq_sum, D.lam_symmetric hF,
    D.Nbr_eq_Nbr0_add_deltaE, ?_, ?_⟩
  · fin_cases i
    · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hv)
    · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hv)
    · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hG)
    · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hG)
    · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hH)
    · exact D.isPositiveRecord_diag h1 _ _ (mul_nonneg hPi hH)
  · fin_cases i <;> exact diagonal_smul (D.diag_diagonal _ _) _
  · rw [← D.Nbr_eq_Nbr0_add_deltaE]
    exact D.Nbr_nonneg hfh hb
  · rw [← D.Nbr_eq_Nbr0_add_deltaE]
    exact D.gram_bracket hfh hb hcap hdom hP hE

end FrameData

end Sarkozy.PartVRecords

module

public import Sarkozy.TheoremCParam.MainEnvelope

@[expose] public section

/-!
# Compatibility: the hard-coded Theorem C is the instance at the record exponent

Every structure of comparison data of `Sarkozy.TheoremC` (at the hard-coded `decay`) is, field
by field, the corresponding structure of `Sarkozy.TheoremCParam` at `a = decay`
(`FirstStage.ofRecord`, …, `ComparisonData.ofRecord`; each field is the same term, its type
agrees by unfolding). The hard-coded `theoremC_reduced`, `theoremC_energy_reduced` and
`theoremC_classes_reduced` are then re-proved, with exactly their statements (`type_of% @…`),
from the parametrized versions at the record exponent. This checks that the mechanical
generalization changed nothing but the exponent.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

section Data

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

/-- The hard-coded `TheoremC.FirstStage` is `FirstStage` at the record exponent. -/
noncomputable def FirstStage.ofRecord {selPre : ℝ} {R : Reference m₀}
    (FS : TheoremC.FirstStage m₀ p selPre R) :
    FirstStage decay m₀ p selPre R where
  fs := FS.fs
  Tag := FS.Tag
  tagFintype := FS.tagFintype
  tagDecEq := FS.tagDecEq
  cut := FS.cut
  cut_family := FS.cut_family
  ϑ₀ := FS.ϑ₀
  ϑ₀_family := FS.ϑ₀_family
  ρ := FS.ρ
  Ia := FS.Ia
  IaFintype := FS.IaFintype
  ca := FS.ca
  κa := FS.κa
  κa_pos := FS.κa_pos
  ρ_sub := FS.ρ_sub
  ρ_ge := FS.ρ_ge
  ρ_off := FS.ρ_off
  Ib := FS.Ib
  IbFintype := FS.IbFintype
  IbDecEq := FS.IbDecEq
  κ := FS.κ
  κ' := FS.κ'
  κ_pos := FS.κ_pos
  κ'_pos := FS.κ'_pos
  mass_eq := FS.mass_eq
  tag := FS.tag
  dconst := FS.dconst
  dconst_nonneg := FS.dconst_nonneg
  sharp := FS.sharp
  off := FS.off
  P := FS.P
  dT := FS.dT
  vT := FS.vT
  P_total := FS.P_total
  dT_total := FS.dT_total
  vT_total := FS.vT_total

/-- The hard-coded `TheoremC.GramBracket` is `GramBracket` at the record exponent. -/
noncomputable def GramBracket.ofRecord {selPre : ℝ} {R : Reference m₀}
    {FS : TheoremC.FirstStage m₀ p selPre R}
    (GB : TheoremC.GramBracket m₀ p selPre FS) :
    GramBracket decay m₀ p selPre (FirstStage.ofRecord FS) where
  Iu := GB.Iu
  IuFintype := GB.IuFintype
  κu := GB.κu
  κu_pos := GB.κu_pos
  κu_diag := GB.κu_diag
  N₀ := GB.N₀
  N₀_sub := GB.N₀_sub
  N₀_off := GB.N₀_off
  lam_sym := GB.lam_sym
  N_nonneg := GB.N_nonneg
  bracket := GB.bracket
  U₀ := GB.U₀
  U₀_total := GB.U₀_total

/-- The hard-coded `TheoremC.ComparisonLaw` is `ComparisonLaw` at the record exponent. -/
noncomputable def ComparisonLaw.ofRecord {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀}
    {FS : TheoremC.FirstStage m₀ p S₀ R} (CL : TheoremC.ComparisonLaw m₀ p S₀ pp ep Q FS) :
    ComparisonLaw decay m₀ p S₀ pp ep Q (FirstStage.ofRecord FS) where
  Ic := CL.Ic
  IcFintype := CL.IcFintype
  cc := CL.cc
  cmass := CL.cmass
  claw := CL.claw
  cmass_pos := CL.cmass_pos
  mass_pos := CL.mass_pos
  nν := CL.nν
  nν_bound := CL.nν_bound
  accept := CL.accept
  unif := CL.unif
  mixing := CL.mixing
  T := CL.T
  TFintype := CL.TFintype
  TDecEq := CL.TDecEq
  Δ := CL.Δ
  change := CL.change
  D := CL.D
  D_prob := CL.D_prob
  D_diag := CL.D_diag
  D_unif := CL.D_unif
  πt := CL.πt
  πt_nonneg := CL.πt_nonneg
  bracket := CL.bracket
  S := CL.S
  A := CL.A
  S_total := CL.S_total
  A_total := CL.A_total
  vfac := CL.vfac
  vfac_bound := CL.vfac_bound

/-- The hard-coded `TheoremC.MatchingEnvelopes` is `MatchingEnvelopes` at the record exponent. -/
noncomputable def MatchingEnvelopes.ofRecord {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀}
    {FS : TheoremC.FirstStage m₀ p S₀ R} {GB : TheoremC.GramBracket m₀ p S₀ FS}
    {CL : TheoremC.ComparisonLaw m₀ p S₀ pp ep Q FS} (ME : TheoremC.MatchingEnvelopes m₀ p GB CL) :
    MatchingEnvelopes decay m₀ p (GramBracket.ofRecord GB) (ComparisonLaw.ofRecord CL) where
  IL := ME.IL
  ILFintype := ME.ILFintype
  IR := ME.IR
  IRFintype := ME.IRFintype
  cL := ME.cL
  cR := ME.cR
  cL_nonneg := ME.cL_nonneg
  cR_nonneg := ME.cR_nonneg
  κL := ME.κL
  κR := ME.κR
  κL_pos := ME.κL_pos
  κR_pos := ME.κR_pos
  κL_diag := ME.κL_diag
  κR_diag := ME.κR_diag
  bracket := ME.bracket
  T := ME.T
  TL_total := ME.TL_total
  TR_total := ME.TR_total

/-- The hard-coded `TheoremC.MeanCredit` is `MeanCredit` at the record exponent. -/
noncomputable def MeanCredit.ofRecord {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀}
    {FS : TheoremC.FirstStage m₀ p S₀ R} {GB : TheoremC.GramBracket m₀ p S₀ FS}
    {CL : TheoremC.ComparisonLaw m₀ p S₀ pp ep Q FS} {ME : TheoremC.MatchingEnvelopes m₀ p GB CL}
    (MC : TheoremC.MeanCredit m₀ p ME) :
    MeanCredit decay m₀ p (MatchingEnvelopes.ofRecord ME) where
  m := MC.m
  bound := MC.bound

/-- The hard-coded `TheoremC.Summability` is `Summability` at the record exponent. -/
noncomputable def Summability.ofRecord {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀}
    {FS : TheoremC.FirstStage m₀ p S₀ R} {GB : TheoremC.GramBracket m₀ p S₀ FS}
    {CL : TheoremC.ComparisonLaw m₀ p S₀ pp ep Q FS} {ME : TheoremC.MatchingEnvelopes m₀ p GB CL}
    (SM : TheoremC.Summability m₀ p ME) :
    Summability decay m₀ p (MatchingEnvelopes.ofRecord ME) where
  bound := SM.bound
  summable := SM.summable

/-- The hard-coded `TheoremC.ClassBounds` are `ClassBounds` at the record exponent. -/
noncomputable def ClassBounds.ofRecord {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀} {FS : TheoremC.FirstStage m₀ p S₀ R}
    {CL : TheoremC.ComparisonLaw m₀ p S₀ pp ep Q FS} (CB : TheoremC.ClassBounds m₀ p CL) :
    ClassBounds decay m₀ p (ComparisonLaw.ofRecord CL) where
  ι := CB.ι
  ιFintype := CB.ιFintype
  ιDecEq := CB.ιDecEq
  cls := CB.cls
  nmax := CB.nmax
  nmax_bound := CB.nmax_bound
  Jaux := CB.Jaux
  JauxFintype := CB.JauxFintype
  JauxDecEq := CB.JauxDecEq
  y := CB.y
  y_nonneg := CB.y_nonneg
  attach := CB.attach
  coeff := CB.coeff
  coeff_nonneg := CB.coeff_nonneg
  coeff_support := CB.coeff_support
  robust := CB.robust

end Data

section Main

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The hard-coded comparison data are comparison data at the record exponent. -/
noncomputable def ComparisonData.ofRecord (D : TheoremC.ComparisonData m₀ p pr h E) :
    ComparisonData decay m₀ p pr h E where
  S := D.S
  R := D.R
  FS := FirstStage.ofRecord D.FS
  GB := GramBracket.ofRecord D.GB
  CL := ComparisonLaw.ofRecord D.CL
  ME := MatchingEnvelopes.ofRecord D.ME
  MC := MeanCredit.ofRecord D.MC
  SM := Summability.ofRecord D.SM

end Main

/-- **Compatibility**: the hard-coded `Sarkozy.TheoremC.ComparisonData.theoremC_reduced` (same
statement, by `type_of%`) is `theoremC_reduced` at the record exponent. -/
theorem theoremC_reduced_viaParam :
    type_of% @Sarkozy.TheoremC.ComparisonData.theoremC_reduced := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ E _ _ D hcop 𝓔 h𝓔 hΘ hE1 hSF hDC hfix henv hunit
  exact Param.powerSavingBound_paper.mp
    ((ComparisonData.ofRecord D).theoremC_reduced hcop Params.paper_valid Sarkozy.decay_pos.le
      h𝓔 hΘ hE1 hSF hDC hfix henv hunit)

/-- **Compatibility**: the hard-coded `theoremC_energy_reduced` is `theoremC_energy_reduced` at
the record exponent. -/
theorem theoremC_energy_reduced_viaParam :
    type_of% @Sarkozy.TheoremC.ComparisonData.theoremC_energy_reduced := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ E _ _ D hcop 𝓔 h𝓔 hΘ hE1 hSF hDC hfix henv hunit
  exact (ComparisonData.ofRecord D).theoremC_energy_reduced hcop Params.paper_valid
    Sarkozy.decay_pos.le h𝓔 hΘ hE1 hSF hDC hfix henv hunit

/-- **Compatibility**: the hard-coded `theoremC_classes_reduced` is `theoremC_classes_reduced` at
the record exponent. -/
theorem theoremC_classes_reduced_viaParam :
    type_of% @Sarkozy.TheoremC.ComparisonData.theoremC_classes_reduced := by
  intro J₀ _ _ m₀ _ J _ _ p _ P _ _ pr h _ E _ _ D hcop CB 𝓔 hΨ hΘ hE1 hCB hSF hDC hfix henv
    hunit
  exact Param.powerSavingBound_paper.mp
    ((ComparisonData.ofRecord D).theoremC_classes_reduced hcop Params.paper_valid
      Sarkozy.decay_pos.le (ClassBounds.ofRecord CB) hΨ hΘ hE1 hCB hSF hDC hfix henv hunit)

end Sarkozy.TheoremCParam

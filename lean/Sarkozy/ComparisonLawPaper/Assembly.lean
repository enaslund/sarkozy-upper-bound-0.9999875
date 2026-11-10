module

public import Sarkozy.GramBracketPaper.Assembly

@[expose] public section

/-!
# (CP4) from per-atom data (`def:cp4`)

`paper/sections/09_comparison_theorem.tex`, `def:cp4` (`def:record:comparison-law`). The comparison
law of Theorem C is a product `ν = ⊗_𝔟 ν_𝔟`: every clause of `def:cp4` except the totals `S`, `A`,
`n_ν` and `𝔳_ν` concerns one atom. On the block atoms `BlockAtom Bk J L = Bk ⊕ J L`, over A1's first
stage `firstStageOfAtoms … A` (one `AtomStage` per prefix atom, trivial data at the tail atoms), the
comparison law is assembled here from one `AtomComparison` per prefix atom and one per tail atom.

* `AtomComparison lam acc Q`: the data of `def:cp4`(a), (b) at one atom with first-stage law
  `lam = λ_𝔟` and acceptance relation `acc` (the clause "the difference `z_{v_e} - z_{u_e}` is …" of
  (a)): components `ν_{𝔟,i} = w_i ν̄_i` (`w_i > 0`, `ν̄_i` a probability law) with real coefficients
  `c_i` and `ν_𝔟(1) = ∑ c_i w_i > 0`; every component accepts every query and has uniform one-slot
  marginals; the changes `Δ_t` with `ν_𝔟 - λ_𝔟 = ∑_t Δ_t`; for each change and type a
  reserved-diagonal probability law `D` with uniform one-slot marginals and `π̃ ≥ 0` with
  `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0`.
* `AtomComparison.sprice`, `aprice`: the atom's prices `s_𝔟 = ∑_t π̃^s_t q^{2a}`,
  `a_𝔟 = ∑_t π̃^a_t q^{2a}`; `vratio = |ν|_𝔟/ν_𝔟(1)`; `IsSingle` (`|I_𝔟| = 1` with a nonnegative
  coefficient), for which `vratio = 1` (`vratio_of_single`).
* `prefixAccepted`, `tailAccepted`: the acceptance relations of `TheoremCBlock.AcceptedPair` at a
  prefix block and at a tail prime, written without the scale.
* `TailMixing`: the part of (R4) that concerns `ν̄` at a tail prime (`def:cp4`(a)): slot mixing,
  `Unif(Ω_p)` query pairs, pair mixing.
* **`comparisonLawOfAtoms`**: the structure `TheoremCBlock.ComparisonLaw` from the atom data, with
  `S = ∑_β s_β + S_tail`, `A = ∑_β a_β + A_tail`, `n_ν = ∏_β |I_β|`, `𝔳_ν = ∏_β |ν|_β/ν_β(1)`. The
  tail atoms are required to be single nonnegative components (the paper: "every other atom law is
  nonnegative", after `def:cp4`), and their price sums at every scale bounded by `S_tail`, `A_tail`
  (`lem:tail-prices`(iv) in the paper's construction). Every field of `def:cp4` is checked here;
  `comparisonLawOfAtoms_S`, `_A` record the totals.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.ComparisonLawPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.FirstStagePaper

/-! ## The data at one atom -/

/-- **The (CP4) data of one atom** (`def:cp4`(a), (b)), relative to the atom's first-stage law
`lam = λ_𝔟`, an acceptance relation `acc` on pairs of labels, and the queries `Q`. -/
structure AtomComparison {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] (lam : SlotMeasure X)
    (acc : X → X → Prop) {E : Type} (Q : Queries E) where
  /-- The components `I_𝔟`. -/
  I : Type
  [IFintype : Fintype I]
  /-- The real coefficients `c_{𝔟,i}`. -/
  c : I → ℝ
  /-- The masses `w_{𝔟,i} = ν_{𝔟,i}(1)`. -/
  w : I → ℝ
  /-- The normalized components `ν̄_{𝔟,i}`. -/
  law : I → FiniteLaw (Slot → X)
  w_pos : ∀ i, 0 < w i
  /-- `ν_𝔟(1) > 0`. -/
  mass_pos : 0 < ∑ i, c i * w i
  /-- (a) Every query is accepted by every component, almost surely. -/
  accept : ∀ i (z : Slot → X), (law i).weight z ≠ 0 → ∀ e, acc (z (Q.source e)) (z (Q.target e))
  /-- (a) All one-slot marginals of every component are uniform. -/
  unif : ∀ i, HasUniformMarginals (law i)
  /-- (b) The records `𝒯_𝔟` that the comparison law changes. -/
  T : Type
  [TFintype : Fintype T]
  [TDecEq : DecidableEq T]
  /-- (b) The changes `Δ_{𝔟,t}`. -/
  Δ : T → SlotMeasure X
  /-- (b) `ν_𝔟 - λ_𝔟 = ∑_t Δ_{𝔟,t}`. -/
  change : (∑ i, (c i * w i) • signedIntegral (law i).weight) - lam = ∑ t, Δ t
  /-- (b) The norm envelopes `D^ε_{𝔟,t}`. -/
  D : T → ChangeType → SlotMeasure X
  D_prob : ∀ t e, IsProbability (D t e)
  D_diag : ∀ t e, TheoremC.IsDiagonalAt reservedCut (D t e)
  D_unif : ∀ t e, HasUniformSlotMarginals (D t e)
  /-- (b) The unpriced prices `π̃^ε_{𝔟,t}`. -/
  πt : T → ChangeType → ℝ
  πt_nonneg : ∀ t e, 0 ≤ πt t e
  /-- (b) `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0` for the symmetric and the skew part `ζ` of the change. -/
  bracket : ∀ t e, reservedCut.Bracket (πt t e • D t e) (changePart e (Δ t)) (πt t e • D t e)

attribute [instance] AtomComparison.IFintype AtomComparison.TFintype AtomComparison.TDecEq

namespace AtomComparison

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] {lam : SlotMeasure X}
  {acc : X → X → Prop} {E : Type} {Q : Queries E} (C : AtomComparison lam acc Q)

/-- The symmetric price `s_𝔟 = ∑_t π̃^s_{𝔟,t} q_𝔟^{2a}` at the selection factor `sel`. -/
noncomputable def sprice (sel : ℝ) : ℝ := ∑ t, C.πt t .sym * sel

/-- The skew price `a_𝔟 = ∑_t π̃^a_{𝔟,t} q_𝔟^{2a}` at the selection factor `sel`. -/
noncomputable def aprice (sel : ℝ) : ℝ := ∑ t, C.πt t .skew * sel

/-- The mass `ν_𝔟(1) = ∑_i c_i w_i`. -/
noncomputable def numass : ℝ := ∑ i, C.c i * C.w i

/-- The variation `|ν|_𝔟 = ∑_i |c_i| w_i`. -/
noncomputable def absmass : ℝ := ∑ i, |C.c i| * C.w i

/-- The variation ratio `|ν|_𝔟/ν_𝔟(1)` (a factor of `𝔳_ν`). -/
noncomputable def vratio : ℝ := C.absmass / C.numass

/-- The atom law is one nonnegative component: `|I_𝔟| = 1` with coefficient `c ≥ 0`. -/
def IsSingle : Prop := Fintype.card C.I = 1 ∧ ∀ i, 0 ≤ C.c i

theorem sprice_nonneg {sel : ℝ} (hsel : 0 ≤ sel) : 0 ≤ C.sprice sel :=
  sum_nonneg fun t _ => mul_nonneg (C.πt_nonneg t _) hsel

theorem aprice_nonneg {sel : ℝ} (hsel : 0 ≤ sel) : 0 ≤ C.aprice sel :=
  sum_nonneg fun t _ => mul_nonneg (C.πt_nonneg t _) hsel

/-- `|ν|_𝔟 = ν_𝔟(1)` when every coefficient is nonnegative. -/
theorem absmass_eq_of_nonneg (h : ∀ i, 0 ≤ C.c i) : C.absmass = C.numass :=
  sum_congr rfl fun i _ => by rw [abs_of_nonneg (h i)]

/-- A single nonnegative component has variation ratio one. -/
theorem vratio_of_single (h : C.IsSingle) : C.vratio = 1 := by
  unfold vratio
  rw [C.absmass_eq_of_nonneg h.2]
  exact div_self C.mass_pos.ne'

/-- Every variation ratio is at least one (`def:cp4`, last sentence). -/
theorem one_le_vratio : 1 ≤ C.vratio := by
  unfold vratio absmass numass
  rw [le_div_iff₀ C.mass_pos, one_mul]
  exact sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (le_abs_self _) (C.w_pos i).le

end AtomComparison

/-! ## Acceptance and mixing without the scale -/

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)

/-- **Acceptance at a prefix block** (`def:cp4`(a), `(R5)`): at every prime of the block the
difference `y - x` is nonzero, of even valuation `2j < e_p`, with a square unit part. This is
`TheoremCBlock.AcceptedPair` at `.inl β`, which does not depend on the scale. -/
def prefixAccepted (pp ep : J₀ → ℕ) (β : Bk) (x y : BlockRes m₀ blk β) : Prop :=
  ∀ i : BlockIdx blk β, y i - x i ≠ 0 ∧ ∃ jj : ℕ, 2 * jj < ep i.1 ∧
    ∃ r : ZMod (m₀ i.1), IsUnit r ∧ IsSquare r ∧
      y i - x i = ((pp i.1 : ℕ) : ZMod (m₀ i.1)) ^ (2 * jj) * r

/-- **Acceptance at a tail prime** (`def:cp4`(a), `(R5)`): `y - x` is a nonzero square. -/
def tailAccepted (q : ℕ) (x y : ZMod q) : Prop := y - x ≠ 0 ∧ IsSquare (y - x)

/-- **The part of (R4) that concerns `ν̄` at a tail prime `q`** (`def:cp4`(a),
`hyp:record:reference`(R4)): `ν̄` is `(γ, v)`-mixing at every slot, and at every query `e` its
`(u_e, v_e)`-marginal is `Unif(Ω_q)` and it is `(γ, {u_e, v_e})`-mixing. -/
def TailMixing (q : ℕ) [NeZero q] {E : Type} (Q : Queries E) (ν : FiniteLaw (Slot → ZMod q)) :
    Prop :=
  (∀ v : Slot, Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ ν {v}) ∧
    ∀ e, PairUniformOmega ν (Q.source e) (Q.target e) ∧
      Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ ν {Q.source e, Q.target e}

/-! ## The assembly -/

variable {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

variable (a) in
/-- **(CP4) from per-atom data** (`def:cp4`), over A1's first stage `firstStageOfAtoms … A`. At the
prefix atom `β` the data are `C β`, relative to `λ_β = ρ_β + δ_{E,β}`; at the tail atom `j` of the
scale `L` they are `Ct L j`, relative to `λ_p = μ_p`, a single nonnegative component (`ht1`) with
the mixing of (R4) at `p ≥ P₅` (`hmix`). The totals: `S = ∑_β s_β + S_tail`,
`A = ∑_β a_β + A_tail`,
where `S_tail`, `A_tail` bound the tail sums at every scale (`hSt`, `hAt`); `n_ν = ∏_β |I_β|` and
`𝔳_ν = ∏_β |ν|_β/ν_β(1)` (the tail factors are one). -/
noncomputable def comparisonLawOfAtoms (selPre : Bk → ℝ) (R : Reference m₀ blk) (Tag : Type)
    [Fintype Tag] [DecidableEq Tag] (cut : Tag → ReflectionCut Slot)
    (hcut : ∀ j, IsFamilyCut (cut j)) (ϑ₀ : ReflectionCut Slot) (hϑ₀ : IsFamilyCut ϑ₀)
    (A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀)
    (pp ep : J₀ → ℕ) {E : Type} (Q : Queries E)
    (C : ∀ β, AtomComparison ((A β).ρ + ∑ i, ((A β).κ' i - (A β).κ i))
      (prefixAccepted m₀ blk pp ep β) Q)
    (Ct : ∀ L (j : J L), AtomComparison (signedIntegral (R.μp (p L j)).weight)
      (tailAccepted (p L j)) Q)
    (ht1 : ∀ L j, (Ct L j).IsSingle)
    (hmix : ∀ L j i, R.P5 ≤ p L j → TailMixing (p L j) Q ((Ct L j).law i))
    (St At : ℝ)
    (hSt : ∀ L, ∑ j, (Ct L j).sprice (((p L j : ℕ) : ℝ) ^ (2 * a)) ≤ St)
    (hAt : ∀ L, ∑ j, (Ct L j).aprice (((p L j : ℕ) : ℝ) ^ (2 * a)) ≤ At) :
    ComparisonLaw a m₀ blk p selPre pp ep Q
      (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A) where
  Ic L b := match b with
    | .inl β => (C β).I
    | .inr j => (Ct L j).I
  IcFintype L b := match b with
    | .inl β => (C β).IFintype
    | .inr j => (Ct L j).IFintype
  cc L b := match b with
    | .inl β => (C β).c
    | .inr j => (Ct L j).c
  cmass L b := match b with
    | .inl β => (C β).w
    | .inr j => (Ct L j).w
  claw L b := match b with
    | .inl β => (C β).law
    | .inr j => (Ct L j).law
  cmass_pos L b := match b with
    | .inl β => (C β).w_pos
    | .inr j => (Ct L j).w_pos
  mass_pos L b := match b with
    | .inl β => (C β).mass_pos
    | .inr j => (Ct L j).mass_pos
  nν := ∏ β, Fintype.card (C β).I
  nν_bound L := by
    rw [Fintype.prod_sum_type]
    have h1 : ∏ j : J L, Fintype.card (Ct L j).I = 1 :=
      Finset.prod_eq_one fun j _ => (ht1 L j).1
    refine le_of_eq ?_
    change (∏ β, Fintype.card (C β).I) * (∏ j : J L, Fintype.card (Ct L j).I) = _
    rw [h1, mul_one]
  accept L b := match b with
    | .inl β => (C β).accept
    | .inr j => (Ct L j).accept
  unif L b := match b with
    | .inl β => (C β).unif
    | .inr j => (Ct L j).unif
  mixing L j i h := hmix L j i h
  T L b := match b with
    | .inl β => (C β).T
    | .inr j => (Ct L j).T
  TFintype L b := match b with
    | .inl β => (C β).TFintype
    | .inr j => (Ct L j).TFintype
  TDecEq L b := match b with
    | .inl β => (C β).TDecEq
    | .inr j => (Ct L j).TDecEq
  Δ L b := match b with
    | .inl β => (C β).Δ
    | .inr j => (Ct L j).Δ
  change L b := match b with
    | .inl β => (C β).change
    | .inr j => by
        rw [GramBracketPaper.fsOfAtoms_lam_inr]
        exact (Ct L j).change
  D L b := match b with
    | .inl β => (C β).D
    | .inr j => (Ct L j).D
  D_prob L b := match b with
    | .inl β => (C β).D_prob
    | .inr j => (Ct L j).D_prob
  D_diag L b := match b with
    | .inl β => (C β).D_diag
    | .inr j => (Ct L j).D_diag
  D_unif L b := match b with
    | .inl β => (C β).D_unif
    | .inr j => (Ct L j).D_unif
  πt L b := match b with
    | .inl β => (C β).πt
    | .inr j => (Ct L j).πt
  πt_nonneg L b := match b with
    | .inl β => (C β).πt_nonneg
    | .inr j => (Ct L j).πt_nonneg
  bracket L b := match b with
    | .inl β => (C β).bracket
    | .inr j => (Ct L j).bracket
  S := ∑ β, (C β).sprice (selPre β) + St
  A := ∑ β, (C β).aprice (selPre β) + At
  S_total L := by
    rw [Fintype.sum_sum_type]
    exact add_le_add le_rfl (hSt L)
  A_total L := by
    rw [Fintype.sum_sum_type]
    exact add_le_add le_rfl (hAt L)
  vfac := ∏ β, (C β).vratio
  vfac_bound L := by
    rw [Fintype.prod_sum_type]
    have h1 : ∏ j : J L, (Ct L j).vratio = 1 :=
      Finset.prod_eq_one fun j _ => (Ct L j).vratio_of_single (ht1 L j)
    refine le_of_eq ?_
    change (∏ β, (C β).absmass / (C β).numass) * (∏ j : J L, (Ct L j).vratio) = _
    rw [h1, mul_one]
    rfl

section Totals

variable {selPre : Bk → ℝ} {R : Reference m₀ blk} {Tag : Type} [Fintype Tag] [DecidableEq Tag]
  {cut : Tag → ReflectionCut Slot} {hcut : ∀ j, IsFamilyCut (cut j)} {ϑ₀ : ReflectionCut Slot}
  {hϑ₀ : IsFamilyCut ϑ₀} {A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀}
  {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
  {C : ∀ β, AtomComparison ((A β).ρ + ∑ i, ((A β).κ' i - (A β).κ i))
    (prefixAccepted m₀ blk pp ep β) Q}
  {Ct : ∀ L (j : J L), AtomComparison (signedIntegral (R.μp (p L j)).weight)
    (tailAccepted (p L j)) Q}
  {ht1 : ∀ L j, (Ct L j).IsSingle}
  {hmix : ∀ L j i, R.P5 ≤ p L j → TailMixing (p L j) Q ((Ct L j).law i)}
  {St At : ℝ}
  {hSt : ∀ L, ∑ j, (Ct L j).sprice (((p L j : ℕ) : ℝ) ^ (2 * a)) ≤ St}
  {hAt : ∀ L, ∑ j, (Ct L j).aprice (((p L j : ℕ) : ℝ) ^ (2 * a)) ≤ At}

omit [∀ L, DecidableEq (J L)] in
/-- The symmetric total of the assembled law: `S = ∑_β s_β + S_tail`. -/
theorem comparisonLawOfAtoms_S :
    (comparisonLawOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A pp ep Q C Ct ht1 hmix St At
      hSt hAt).S = ∑ β, (C β).sprice (selPre β) + St := rfl

omit [∀ L, DecidableEq (J L)] in
/-- The skew total of the assembled law: `A = ∑_β a_β + A_tail`. -/
theorem comparisonLawOfAtoms_A :
    (comparisonLawOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A pp ep Q C Ct ht1 hmix St At
      hSt hAt).A = ∑ β, (C β).aprice (selPre β) + At := rfl

omit [∀ L, DecidableEq (J L)] in
/-- The variation factor of the assembled law: `𝔳_ν = ∏_β |ν|_β/ν_β(1)`. -/
theorem comparisonLawOfAtoms_vfac :
    (comparisonLawOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A pp ep Q C Ct ht1 hmix St At
      hSt hAt).vfac = ∏ β, (C β).vratio := rfl

omit [∀ L, DecidableEq (J L)] in
/-- The number of product components of the assembled law: `n_ν = ∏_β |I_β|`. -/
theorem comparisonLawOfAtoms_nν :
    (comparisonLawOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A pp ep Q C Ct ht1 hmix St At
      hSt hAt).nν = ∏ β, Fintype.card (C β).I := rfl

end Totals

end Sarkozy.ComparisonLawPaper

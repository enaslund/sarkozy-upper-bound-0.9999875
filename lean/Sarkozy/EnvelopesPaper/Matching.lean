module

public import Sarkozy.TheoremCBlock.Data
public import Sarkozy.TheoremC.WrapTerms
public import Sarkozy.RecordExpansion.FirstStage

@[expose] public section

/-!
# (CP6) matching envelopes from a Gram bracket, a comparison law and a refinement

`paper/sections/09_comparison_theorem.tex`, `def:cp6`; `paper/sections/24_matching_mean.tex`,
`subsec:matching-envelopes` and `prop:record:matching`.

The paper builds the dominators `M_{s,𝔟}` (`s ∈ {L, R}`) in two layers
(`prop:record:matching`(i), proof):

* every record change `Δ_{𝔟,t}` of (CP4) that is *not* treated specially is enveloped by its
  own norm envelopes: the bracket `(π̃^ε D^ε; ζ^ε, π̃^ε D^ε) ⪰_ι 0` of
  `def:record:comparison-law` (the field `ComparisonLaw.bracket`), added to the bracket;
* on a middle block the two fold records (and the two matching records) are treated together
  with the bracket `Ñ` of (CP3): the paper decomposes `Ñ` (`lem:record:gram`(ii)), adds the block
  Grams of `prop:signed-sides`(i),(ii) with the chosen sides, and obtains
  `(Ñ + K_L, λ + ∑_{t replaced} Δ_t; ·, Ñ + K_R) ⪰_ι 0` with the chosen side diagonals `K_s`
  (and the chosen matching diagonal `Q_{E,𝔟}`, which dominates the norm envelopes of the two
  matching changes).

Here the second layer is an input, `EnvelopeRefinement GB CL`: a finite set `repl` of
*replaced* records at every atom, positive reserved-diagonal records `κK_i` with side
coefficients `kL_i, kR_i ≥ 0`, and the bracket
`(Ñ + ∑ kL κK, λ + ∑_{t ∈ repl} Δ_t; ·, Ñ + ∑ kR κK) ⪰_ι 0`. Everything else is proved, for
**any** Gram bracket `GB` and **any** comparison law `CL` of the right types:

* `EnvelopeRefinement.toME`: (CP6) with `M_s = Ñ + ∑ k_s κK + ∑_{t ∉ repl} ∑_ε π̃^ε D^ε`
  (`bracket_core_add`, by additivity of brackets); its matching exponent is any number `T` that
  bounds both side totals `∑_𝔟 priceL`, `∑_𝔟 priceR` (`sum_cL_eq`, `sum_cR_eq`: the price of
  `M_s - Ñ` is `∑_i k_{s,i} κK_i(1) q^{2a} + ∑_{t ∉ repl} (π^s_t + π^a_t)`).
* `trivialRefinement GB CL`: no replaced record, no added diagonal; its bracket is (CP3)'s.
  This is the non-vacuity check of `EnvelopeRefinement`: it is satisfiable for every `GB`, `CL`.
* **`normEnvelopes GB CL`**: (CP6) for any `GB`, `CL`, fully proved, with `T = S + A`
  (the envelope `wrapEnvelope` of `TheoremCBlock.WrapTerms`, as a `MatchingEnvelopes`). At the
  target ledger `S + A ≈ 0.981 > T ≈ 0.619`, so the paper's refinement is needed for `hT`.
* `otherPrice_eq`: the non-replaced price is the full (CP4) price minus the replaced prices.

Positivity facts used later (`Mean.lean`): a nonnegative reserved-diagonal measure is positive at
`ι` (`positive_of_nonneg_diagonal`), `Ñ ⪰_ι 0` (from the bracket of (CP3)), and the decomposition
`M_s = core_s + extra` with `core_s = Ñ + ∑ k_s κK ⪰_ι 0` and `extra ⪰_ι 0`.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopesPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.RecordExpansion (ChangeType sum_changeType symPart_add_skewPart symTotal skewTotal)

/-! ## Positivity of reserved-diagonal records -/

section Positivity

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A measure is the signed integral of its density. -/
theorem eq_signedIntegral_lawDensity (κ : SlotMeasure X) :
    κ = signedIntegral (lawDensity κ) := by
  apply LinearMap.ext
  intro f
  rw [linearFunctional_density κ f]
  rfl

/-- **(E3) of `lem:energy-toolkit` for one record**: a nonnegative measure that is diagonal at the
reserved cut is positive at `ι`. -/
theorem positive_of_nonneg_diagonal {κ : SlotMeasure X} (h : IsNonneg κ)
    (hd : TheoremC.IsDiagonalAt reservedCut κ) : reservedCut.Positive κ := by
  have hp := RecordExpansion.positive_of_diagonal_records reservedCut (univ : Finset (Fin 1))
    (fun _ => (1 : ℝ)) (fun _ => lawDensity κ) (fun _ _ => zero_le_one)
    (fun _ _ z => h _ fun y => by split_ifs <;> norm_num)
    (fun _ _ z hz => funext fun v => hd z hz v)
  simp only [Fin.sum_univ_one, one_smul] at hp
  rwa [← eq_signedIntegral_lawDensity] at hp

/-- A finite nonnegative combination of positive reserved-diagonal records is positive at `ι`. -/
theorem positive_sum_records {I : Type} [Fintype I] (c : I → ℝ) (κ : I → SlotMeasure X)
    (hc : ∀ i, 0 ≤ c i) (hκ : ∀ i, IsPositiveRecord (κ i))
    (hd : ∀ i, TheoremC.IsDiagonalAt reservedCut (κ i)) :
    reservedCut.Positive (∑ i, c i • κ i) :=
  ReflectionCut.Positive.sum _ fun i _ =>
    (positive_of_nonneg_diagonal (hκ i).1 (hd i)).smul (hc i)

end Positivity

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

/-! ## The refinement (input) -/

/-- **The refined part of the matching envelopes** (`prop:record:matching`(i), the middle-block
step; `prop:signed-sides`(i),(ii); `subsec:matching-envelopes`). At every atom `𝔟`:
* a finite set `repl` of *replaced* records `t` of (CP4) (in the paper: the two fold records, and
  the two matching records if their norm envelopes are replaced by `Q_{E,𝔟}`, on a middle block;
  empty elsewhere);
* positive reserved-diagonal records `κK_i` with side coefficients `kL_i, kR_i ≥ 0` (in the
  paper: `K_{L,𝔟} = r²(k_L D¹ + k_R D²)`, `K_{R,𝔟} = r²(k_R D¹ + k_L D²)` and `Q_{E,𝔟}`);
* the bracket `(Ñ_𝔟 + ∑ kL κK, λ_𝔟 + ∑_{t ∈ repl} Δ_t; ·, Ñ_𝔟 + ∑ kR κK) ⪰_ι 0`.

The bracket is the paper's middle-block computation (decomposition of `Ñ` by `lem:record:gram`(ii),
the signed fold Grams of `prop:signed-sides` with the chosen sides, the exchange of
`lem:record:asymmetric-gram`(c)); it is **used as a hypothesis** here. -/
structure EnvelopeRefinement (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) where
  /-- The replaced records. -/
  repl : ∀ L b, Finset (CL.T L b)
  /-- The added diagonals. -/
  IK : ∀ L, BlockAtom Bk J L → Type
  [IKFintype : ∀ L b, Fintype (IK L b)]
  kL : ∀ L b, IK L b → ℝ
  kR : ∀ L b, IK L b → ℝ
  kL_nonneg : ∀ L b i, 0 ≤ kL L b i
  kR_nonneg : ∀ L b i, 0 ≤ kR L b i
  κK : ∀ L b, IK L b → AtomMeasure m₀ blk p L b
  κK_pos : ∀ L b i, IsPositiveRecord (κK L b i)
  κK_diag : ∀ L b i, TheoremC.IsDiagonalAt reservedCut (κK L b i)
  /-- The refined bracket (`prop:record:matching`(i), middle-block step). -/
  bracket : ∀ L b, reservedCut.Bracket (GB.N L b + ∑ i, kL L b i • κK L b i)
    (FS.lam L b + ∑ t ∈ repl L b, CL.Δ L b t) (GB.N L b + ∑ i, kR L b i • κK L b i)

attribute [instance] EnvelopeRefinement.IKFintype

/-- **The trivial refinement**: nothing replaced, nothing added; the bracket is (CP3)'s. It shows
that `EnvelopeRefinement GB CL` is satisfiable for every `GB` and `CL` (non-vacuity). -/
noncomputable def trivialRefinement (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) : EnvelopeRefinement GB CL where
  repl _ _ := ∅
  IK _ _ := Empty
  IKFintype _ _ := inferInstanceAs (Fintype Empty)
  kL _ _ i := i.elim
  kR _ _ i := i.elim
  kL_nonneg _ _ i := i.elim
  kR_nonneg _ _ i := i.elim
  κK _ _ i := i.elim
  κK_pos _ _ i := i.elim
  κK_diag _ _ i := i.elim
  bracket L b := by
    simp only [Finset.univ_eq_empty, sum_empty, add_zero]
    exact GB.bracket L b

namespace EnvelopeRefinement

variable {GB : GramBracket a m₀ blk p S₀ FS} {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}
  (F : EnvelopeRefinement GB CL)

/-- The coefficient of the norm envelope `D^ε_{𝔟,t}` in `M_s`: `π̃^ε_{𝔟,t}` if `t` is not
replaced, `0` if it is. -/
noncomputable def normCoef (L : ℕ) (b : BlockAtom Bk J L) (t : CL.T L b) (e : ChangeType) : ℝ :=
  if t ∈ F.repl L b then 0 else CL.πt L b t e

theorem normCoef_nonneg (L : ℕ) (b : BlockAtom Bk J L) (t : CL.T L b) (e : ChangeType) :
    0 ≤ F.normCoef L b t e := by
  unfold normCoef
  split_ifs
  · exact le_refl 0
  · exact CL.πt_nonneg L b t e

/-- The core of the left envelope, `Ñ_𝔟 + ∑_i kL_i κK_i`. -/
noncomputable def coreL (L : ℕ) (b : BlockAtom Bk J L) : AtomMeasure m₀ blk p L b :=
  GB.N L b + ∑ i, F.kL L b i • F.κK L b i

/-- The core of the right envelope, `Ñ_𝔟 + ∑_i kR_i κK_i`. -/
noncomputable def coreR (L : ℕ) (b : BlockAtom Bk J L) : AtomMeasure m₀ blk p L b :=
  GB.N L b + ∑ i, F.kR L b i • F.κK L b i

/-- The norm envelopes of the non-replaced records, `∑_{t ∉ repl} ∑_ε π̃^ε D^ε`. -/
noncomputable def extra (L : ℕ) (b : BlockAtom Bk J L) : AtomMeasure m₀ blk p L b :=
  ∑ t, ∑ e, F.normCoef L b t e • CL.D L b t e

/-- The (CP4) price `π^s + π^a` of the non-replaced records of an atom. -/
noncomputable def otherPrice (L : ℕ) (b : BlockAtom Bk J L) : ℝ :=
  ∑ t, if t ∈ F.repl L b then 0 else (CL.π L b t .sym + CL.π L b t .skew)

/-- The price of `M_L - Ñ` at an atom: the added diagonals and the non-replaced norm envelopes. -/
noncomputable def priceL (L : ℕ) (b : BlockAtom Bk J L) : ℝ :=
  ∑ i, F.kL L b i * mass (F.κK L b i) * selectionFactor a p S₀ L b + F.otherPrice L b

/-- The price of `M_R - Ñ` at an atom. -/
noncomputable def priceR (L : ℕ) (b : BlockAtom Bk J L) : ℝ :=
  ∑ i, F.kR L b i * mass (F.κK L b i) * selectionFactor a p S₀ L b + F.otherPrice L b

/-- **The comparison law splits** along the replaced records:
`ν_𝔟 = (λ_𝔟 + ∑_{t ∈ repl} Δ_t) + ∑_t [t ∉ repl] ∑_ε ζ^ε_t`. -/
theorem nu_split (L : ℕ) (b : BlockAtom Bk J L) :
    CL.ν L b = (FS.lam L b + ∑ t ∈ F.repl L b, CL.Δ L b t) +
      ∑ t, (if t ∈ F.repl L b then 0 else ∑ e, changePart e (CL.Δ L b t)) := by
  have hch := CL.change L b
  have hpart : ∀ t, ∑ e, changePart e (CL.Δ L b t) = CL.Δ L b t := fun t => by
    rw [sum_changeType]
    exact symPart_add_skewPart reservedCut _
  simp only [hpart]
  have hsplit : ∑ t, CL.Δ L b t = ∑ t ∈ F.repl L b, CL.Δ L b t +
      ∑ t, (if t ∈ F.repl L b then 0 else CL.Δ L b t) := by
    have h1 : ∑ t ∈ F.repl L b, CL.Δ L b t =
        ∑ t, (if t ∈ F.repl L b then CL.Δ L b t else 0) := by
      rw [Finset.sum_ite_mem, Finset.univ_inter]
    rw [h1, ← sum_add_distrib]
    apply sum_congr rfl
    intro t _
    split_ifs <;> simp
  unfold TheoremCBlock.ComparisonLaw.ν
  rw [add_assoc, ← hsplit, ← hch]
  abel

/-- **The bracket of the envelopes** (`prop:record:matching`(i)): the refined bracket plus the
brackets of (CP4) of the non-replaced records,
`(coreL + extra, ν; ν*, coreR + extra) ⪰_ι 0`. -/
theorem bracket_core_add (L : ℕ) (b : BlockAtom Bk J L) :
    reservedCut.Bracket (F.coreL L b + F.extra L b) (CL.ν L b) (F.coreR L b + F.extra L b) := by
  rw [F.nu_split L b]
  refine bracket_add (F.bracket L b) (bracket_sum univ fun t _ => ?_)
  by_cases ht : t ∈ F.repl L b
  · simp only [normCoef, ht, ↓reduceIte, zero_smul, sum_const_zero]
    exact bracket_zero reservedCut
  · simp only [normCoef, ht, ↓reduceIte]
    exact bracket_sum univ fun e _ => CL.bracket L b t e

theorem extra_positive (L : ℕ) (b : BlockAtom Bk J L) : reservedCut.Positive (F.extra L b) :=
  ReflectionCut.Positive.sum _ fun t _ => ReflectionCut.Positive.sum _ fun e _ =>
    (positive_of_nonneg_diagonal (CL.D_prob L b t e).1 (CL.D_diag L b t e)).smul
      (F.normCoef_nonneg L b t e)

theorem coreL_positive (L : ℕ) (b : BlockAtom Bk J L) : reservedCut.Positive (F.coreL L b) :=
  (GB.bracket L b).left_positive.add (positive_sum_records _ _ (F.kL_nonneg L b) (F.κK_pos L b)
    (F.κK_diag L b))

theorem coreR_positive (L : ℕ) (b : BlockAtom Bk J L) : reservedCut.Positive (F.coreR L b) :=
  (GB.bracket L b).left_positive.add (positive_sum_records _ _ (F.kR_nonneg L b) (F.κK_pos L b)
    (F.κK_diag L b))

/-! ## The matching envelopes -/

/-- The records of `M_s - Ñ`: the added diagonals, then the norm envelopes `D^ε_t`. -/
abbrev Idx (L : ℕ) (b : BlockAtom Bk J L) : Type := F.IK L b ⊕ (CL.T L b × ChangeType)

/-- The records `κK_i`, `D^ε_t`. -/
noncomputable def recd (L : ℕ) (b : BlockAtom Bk J L) : F.Idx L b → AtomMeasure m₀ blk p L b :=
  Sum.elim (F.κK L b) (fun te => CL.D L b te.1 te.2)

/-- The left coefficients `kL_i`, `[t ∉ repl] π̃^ε_t`. -/
noncomputable def coefL (L : ℕ) (b : BlockAtom Bk J L) : F.Idx L b → ℝ :=
  Sum.elim (F.kL L b) (fun te => F.normCoef L b te.1 te.2)

/-- The right coefficients `kR_i`, `[t ∉ repl] π̃^ε_t`. -/
noncomputable def coefR (L : ℕ) (b : BlockAtom Bk J L) : F.Idx L b → ℝ :=
  Sum.elim (F.kR L b) (fun te => F.normCoef L b te.1 te.2)

theorem recd_pos (L : ℕ) (b : BlockAtom Bk J L) (i : F.Idx L b) : IsPositiveRecord (F.recd L b i) := by
  rcases i with i | ⟨t, e⟩
  · exact F.κK_pos L b i
  · exact ⟨(CL.D_prob L b t e).1, CL.D_unif L b t e⟩

theorem recd_diag (L : ℕ) (b : BlockAtom Bk J L) (i : F.Idx L b) :
    TheoremC.IsDiagonalAt reservedCut (F.recd L b i) := by
  rcases i with i | ⟨t, e⟩
  · exact F.κK_diag L b i
  · exact CL.D_diag L b t e

theorem sum_coefL_smul (L : ℕ) (b : BlockAtom Bk J L) :
    ∑ i, F.coefL L b i • F.recd L b i = ∑ i, F.kL L b i • F.κK L b i + F.extra L b := by
  simp only [Fintype.sum_sum_type, coefL, recd, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    extra]

theorem sum_coefR_smul (L : ℕ) (b : BlockAtom Bk J L) :
    ∑ i, F.coefR L b i • F.recd L b i = ∑ i, F.kR L b i • F.κK L b i + F.extra L b := by
  simp only [Fintype.sum_sum_type, coefR, recd, Sum.elim_inl, Sum.elim_inr, Fintype.sum_prod_type,
    extra]

/-- The non-replaced part of the price of `M_s - Ñ` is `otherPrice` (`D^ε_t` are probability
laws). -/
theorem sum_normCoef_price (L : ℕ) (b : BlockAtom Bk J L) :
    ∑ t, ∑ e, F.normCoef L b t e * mass (CL.D L b t e) * selectionFactor a p S₀ L b =
      F.otherPrice L b := by
  unfold otherPrice
  apply sum_congr rfl
  intro t _
  rw [sum_changeType]
  simp only [normCoef, (CL.D_prob L b t _).2, mul_one, TheoremCBlock.ComparisonLaw.π]
  split_ifs <;> ring

/-- **The price of `M_L - Ñ`** at an atom is `priceL`. -/
theorem sum_cL_eq (L : ℕ) (b : BlockAtom Bk J L) :
    ∑ i, F.coefL L b i * mass (F.recd L b i) * selectionFactor a p S₀ L b = F.priceL L b := by
  rw [Fintype.sum_sum_type]
  simp only [coefL, recd, Sum.elim_inl, Sum.elim_inr]
  rw [Fintype.sum_prod_type, F.sum_normCoef_price]
  rfl

/-- **The price of `M_R - Ñ`** at an atom is `priceR`. -/
theorem sum_cR_eq (L : ℕ) (b : BlockAtom Bk J L) :
    ∑ i, F.coefR L b i * mass (F.recd L b i) * selectionFactor a p S₀ L b = F.priceR L b := by
  rw [Fintype.sum_sum_type]
  simp only [coefR, recd, Sum.elim_inl, Sum.elim_inr]
  rw [Fintype.sum_prod_type, F.sum_normCoef_price]
  rfl

theorem coefL_nonneg (L : ℕ) (b : BlockAtom Bk J L) (i : F.Idx L b) : 0 ≤ F.coefL L b i := by
  rcases i with i | ⟨t, e⟩
  · exact F.kL_nonneg L b i
  · exact F.normCoef_nonneg L b t e

theorem coefR_nonneg (L : ℕ) (b : BlockAtom Bk J L) (i : F.Idx L b) : 0 ≤ F.coefR L b i := by
  rcases i with i | ⟨t, e⟩
  · exact F.kR_nonneg L b i
  · exact F.normCoef_nonneg L b t e

variable (a) in
/-- **(CP6) from a refinement** (`def:cp6`, `prop:record:matching`(i),(ii)):
`M_{s,𝔟} = Ñ_𝔟 + ∑_i k_{s,i} κK_i + ∑_{t ∉ repl} ∑_ε π̃^ε_t D^ε_t`, with any matching exponent `T`
that bounds both side totals. -/
noncomputable def toME (T : ℝ) (hL : ∀ L, ∑ b, F.priceL L b ≤ T)
    (hR : ∀ L, ∑ b, F.priceR L b ≤ T) : MatchingEnvelopes a m₀ blk p GB CL where
  IL := F.Idx
  ILFintype L b := inferInstanceAs (Fintype (F.IK L b ⊕ (CL.T L b × ChangeType)))
  IR := F.Idx
  IRFintype L b := inferInstanceAs (Fintype (F.IK L b ⊕ (CL.T L b × ChangeType)))
  cL := F.coefL
  cR := F.coefR
  cL_nonneg := F.coefL_nonneg
  cR_nonneg := F.coefR_nonneg
  κL := F.recd
  κR := F.recd
  κL_pos := F.recd_pos
  κR_pos := F.recd_pos
  κL_diag := F.recd_diag
  κR_diag := F.recd_diag
  bracket L b := by
    have h := F.bracket_core_add L b
    rw [F.sum_coefL_smul, F.sum_coefR_smul, ← add_assoc, ← add_assoc]
    exact h
  T := T
  TL_total L := by
    simp only [F.sum_cL_eq]
    exact hL L
  TR_total L := by
    simp only [F.sum_cR_eq]
    exact hR L

theorem toME_T (T : ℝ) (hL : ∀ L, ∑ b, F.priceL L b ≤ T) (hR : ∀ L, ∑ b, F.priceR L b ≤ T) :
    (F.toME a T hL hR).T = T := rfl

/-- The left envelope of `toME` is `coreL + extra`. -/
theorem toME_ML (T : ℝ) (hL : ∀ L, ∑ b, F.priceL L b ≤ T) (hR : ∀ L, ∑ b, F.priceR L b ≤ T)
    (L : ℕ) (b : BlockAtom Bk J L) : (F.toME a T hL hR).ML L b = F.coreL L b + F.extra L b := by
  change GB.N L b + ∑ i, F.coefL L b i • F.recd L b i = _
  rw [F.sum_coefL_smul, ← add_assoc]
  rfl

/-- The right envelope of `toME` is `coreR + extra`. -/
theorem toME_MR (T : ℝ) (hL : ∀ L, ∑ b, F.priceL L b ≤ T) (hR : ∀ L, ∑ b, F.priceR L b ≤ T)
    (L : ℕ) (b : BlockAtom Bk J L) : (F.toME a T hL hR).MR L b = F.coreR L b + F.extra L b := by
  change GB.N L b + ∑ i, F.coefR L b i • F.recd L b i = _
  rw [F.sum_coefR_smul, ← add_assoc]
  rfl

/-- **The non-replaced price** is the full (CP4) price of the atom minus the price of the
replaced records. -/
theorem otherPrice_eq (L : ℕ) (b : BlockAtom Bk J L) :
    F.otherPrice L b = (symTotal (CL.π L) b + skewTotal (CL.π L) b) -
      ∑ t ∈ F.repl L b, (CL.π L b t .sym + CL.π L b t .skew) := by
  have h1 : ∑ t ∈ F.repl L b, (CL.π L b t .sym + CL.π L b t .skew) =
      ∑ t, (if t ∈ F.repl L b then CL.π L b t .sym + CL.π L b t .skew else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : symTotal (CL.π L) b + skewTotal (CL.π L) b =
      ∑ t, (CL.π L b t .sym + CL.π L b t .skew) := by
    unfold symTotal skewTotal
    rw [sum_add_distrib]
  rw [h1, h2, eq_sub_iff_add_eq, otherPrice, ← sum_add_distrib]
  apply sum_congr rfl
  intro t _
  split_ifs <;> ring

end EnvelopeRefinement

/-! ## The norm envelopes: (CP6) for any `GB`, `CL`, with `T = S + A` -/

theorem trivialRefinement_priceL (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (L : ℕ) (b : BlockAtom Bk J L) :
    (trivialRefinement GB CL).priceL L b = symTotal (CL.π L) b + skewTotal (CL.π L) b := by
  unfold EnvelopeRefinement.priceL
  rw [EnvelopeRefinement.otherPrice_eq]
  change (∑ i : Empty, _) + ((symTotal (CL.π L) b + skewTotal (CL.π L) b) -
    ∑ t ∈ (∅ : Finset (CL.T L b)), _) = _
  simp

theorem trivialRefinement_priceR (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (L : ℕ) (b : BlockAtom Bk J L) :
    (trivialRefinement GB CL).priceR L b = symTotal (CL.π L) b + skewTotal (CL.π L) b := by
  unfold EnvelopeRefinement.priceR
  rw [EnvelopeRefinement.otherPrice_eq]
  change (∑ i : Empty, _) + ((symTotal (CL.π L) b + skewTotal (CL.π L) b) -
    ∑ t ∈ (∅ : Finset (CL.T L b)), _) = _
  simp

theorem sum_symTotal_add_skewTotal_le (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (L : ℕ) :
    ∑ b, (symTotal (CL.π L) b + skewTotal (CL.π L) b) ≤ CL.S + CL.A := by
  rw [sum_add_distrib]
  exact add_le_add (CL.S_total L) (CL.A_total L)

variable (a) in
/-- **(CP6) for any Gram bracket and any comparison law** (`def:cp6`; the outside-the-middle case
of `prop:record:matching`(i), at every atom): `M_L = M_R = Ñ + ∑_t ∑_ε π̃^ε_t D^ε_t`, with the
matching exponent `T = S + A`. Fully proved; no input. -/
noncomputable def normEnvelopes (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) : MatchingEnvelopes a m₀ blk p GB CL :=
  (trivialRefinement GB CL).toME a (CL.S + CL.A)
    (fun L => by
      simp only [trivialRefinement_priceL]
      exact sum_symTotal_add_skewTotal_le CL L)
    (fun L => by
      simp only [trivialRefinement_priceR]
      exact sum_symTotal_add_skewTotal_le CL L)

theorem normEnvelopes_T (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) :
    (normEnvelopes a GB CL).T = CL.S + CL.A := rfl

end Sarkozy.EnvelopesPaper

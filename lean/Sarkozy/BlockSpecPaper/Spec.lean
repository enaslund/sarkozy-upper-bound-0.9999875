module

public import Sarkozy.BlockSpecPaper.Layout
public import Sarkozy.BlockSpecPaper.AllpData
public import Sarkozy.PartVLaws.RecordedUpper
public import Sarkozy.GramBracketPaper.Paper

@[expose] public section








open Finset

namespace Sarkozy.BlockSpecPaper

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws Sarkozy.MiddleRecords Sarkozy.FirstStagePaper Sarkozy.GramBracketPaper
  Sarkozy.BlockSpecPaper.AllpData

/-! ## The ALLp records as weights and inputs -/

/-- The ALLp completion weights of piece `i` (`tab:data:middle-weights`, ALLp caps). -/
noncomputable def allpWeights (i : Fin 33) : MiddleWeights :=
  (allpRecord i).weights (allpRecord_nonneg i)

/-- The ALLp rational input caps of piece `i`. -/
noncomputable def allpInputs (i : Fin 33) : MiddleInputs := (allpRecord i).inputs

/-- **The thirteen completion inequalities on every ALLp piece** (`lem:front12:reference`(iv)). -/
theorem allpWeights_completes (i : Fin 33) : (allpWeights i).Completes (allpInputs i) :=
  (allpRecord i).completes_sound (allpRecord_nonneg i) (allpRecord_completes i)

/-- **The protection `v_D ≥ 2 k_D w_D` on every ALLp piece** (`eq:protection`). -/
theorem allpWeights_protects (i : Fin 33) : (allpWeights i).Protects (allpInputs i) :=
  (allpRecord i).protects_sound (allpRecord_nonneg i) (allpRecord_protects i)

theorem allpInputs_nonneg (i : Fin 33) :
    0 ≤ (allpInputs i).d ∧ 0 ≤ (allpInputs i).d₁ ∧ 0 ≤ (allpInputs i).f₁ ∧
      0 ≤ (allpInputs i).f₂ ∧ 0 ≤ (allpInputs i).h₁ ∧ 0 ≤ (allpInputs i).h₂ ∧
      ∀ t, 0 ≤ (allpInputs i).k t :=
  (allpRecord i).inputs_nonneg (allpRecord_nonneg i)

/-- **The ALLp root of a piece** (`TargetScope.lean`): `some u` for the individual-square root of
parameter `u` on the pieces `30` (`2³⁶`) and `31` (`2⁴⁰`), `none` (the uniform root) elsewhere. -/
def allpIndividual (i : Fin 33) : Option ℚ :=
  if i.val = 30 then some (3851 / 4096) else if i.val = 31 then some (4049 / 4096) else none

/-- The parameters agree with V1's `pieceRoot` (`def:record:parameters`(f)). -/
theorem allpIndividual_pieceRoot :
    pieceRoot 30 = .individualSquare (3851 / 4096) ∧
      pieceRoot 31 = .individualSquare (4049 / 4096) :=
  ⟨rfl, rfl⟩

variable {cell : ℕ → ℕ}

/-! ## The scale `r = b_𝔅^{-1/2}` -/

/-- **The scale of a block**, `r = b_𝔅^{-1/2}` with `b_𝔅` its least prime
(`lem:record:middle-prices`, `lem:upper-reference-rp`). -/
noncomputable def blockScale (b : PaperBlock cell) : ℝ := (blockLeast b : ℝ) ^ (-(1 / 2 : ℝ))

theorem blockLeast_pos (b : PaperBlock cell) : (0 : ℝ) < blockLeast b := by
  have h := two_pow_24_le_blockLeast b
  have h' : (0 : ℕ) < blockLeast b := lt_of_lt_of_le (by norm_num) h
  exact_mod_cast h'

theorem blockScale_pos (b : PaperBlock cell) : 0 < blockScale b :=
  Real.rpow_pos_of_pos (blockLeast_pos b) _

/-- `r² b_𝔅 = 1`. -/
theorem blockScale_sq_mul (b : PaperBlock cell) : blockScale b ^ 2 * (blockLeast b : ℝ) = 1 := by
  have hb := blockLeast_pos b
  unfold blockScale
  rw [← Real.rpow_natCast, ← Real.rpow_mul hb.le]
  have h2 : (-(1 / 2 : ℝ)) * ((2 : ℕ) : ℝ) = -1 := by norm_num
  rw [h2, Real.rpow_neg_one]
  exact inv_mul_cancel₀ hb.ne'

/-! ## The analytic inputs -/

/-- **The analytic inputs of an upper block of band `k`** (`lem:upper-reference-rp`(ii), (V1)–(V3)):
the root envelopes, valid rows and layer caps of the band's recorded ordinary and reserved inputs
and caps, for the block's field laws, at `r = b_𝔅^{-1/2}`. *Hypothesis* (spectral). -/
def UpperAnalytic (b : PaperBlock cell) (k : Fin 310) : Prop :=
  ∀ hne hW' hp', ValidInputs (upperBlockFieldLaws (blockPrimes (paperBlockOf cell) b) hne)
    (block_upperDatumHyp (blockPrimes (paperBlockOf cell) b) hW' hp' hne) (blockScale b)
    (UpperRecords.bandOrd k) (UpperRecords.bandRes k) (UpperRecords.bandCap k)

/-- **The analytic inputs of a middle block of piece `i` with the uniform root**
(`lem:front12:reference`(i),(ii)), at the ALLp caps of the piece and `r = b_𝔅^{-1/2}`: the two-layer
and one-layer rows, the root envelopes of L20 and L10, and the layer caps. *Hypothesis*
(spectral). 5 fields. -/
structure MiddleUniformAnalytic (b : PaperBlock cell) (i : Fin 33) : Prop where
  rows₂ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RowBounds (fieldDatum (middleBlock_datumHyp₂ (blockPrimes (paperBlockOf cell) b) hne))
      (allpInputs i).f₂ (allpInputs i).h₂ (blockScale b)
  rows₁ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes (paperBlockOf cell) b) hne))
      (allpInputs i).f₁ (allpInputs i).h₁ (blockScale b)
  root₂ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RootEnvelope (fieldDatum (middleBlock_datumHyp₂ (blockPrimes (paperBlockOf cell) b) hne))
      (allpInputs i).d (blockScale b)
  root₁ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes (paperBlockOf cell) b) hne))
      (allpInputs i).d₁ (blockScale b)
  caps : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    MiddleLayerCaps (middleBlockFieldLaws (blockPrimes (paperBlockOf cell) b) hne
      (uniformRoot (blockPrimes (paperBlockOf cell) b) hne)) (allpInputs i).k (blockScale b)

/-- **The analytic inputs of a middle block of piece `i` with the individual-square root of
parameter `u`** (`lem:front12:reference`(i),(ii), `def:positive-root`). *Hypothesis* (spectral).
5 fields. -/
structure MiddleIndividualAnalytic (b : PaperBlock cell) (i : Fin 33) (u : ℚ) : Prop where
  rows₂ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RowBounds (fieldDatum
      (middleBlock_datumHyp₂_individual (blockPrimes (paperBlockOf cell) b) hne u))
      (allpInputs i).f₂ (allpInputs i).h₂ (blockScale b)
  rows₁ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RowBounds (fieldDatum (middleBlock_datumHyp₁ (blockPrimes (paperBlockOf cell) b) hne))
      (allpInputs i).f₁ (allpInputs i).h₁ (blockScale b)
  root₂ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RootEnvelope (fieldDatum
      (middleBlock_datumHyp₂_individual (blockPrimes (paperBlockOf cell) b) hne u))
      (allpInputs i).d (blockScale b)
  root₁ : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    RootEnvelope (fieldDatum (middleBlock_datumHyp₁ (blockPrimes (paperBlockOf cell) b) hne))
      (allpInputs i).d₁ (blockScale b)
  caps : ∀ hne : MiddleNonempty (blockPrimes (paperBlockOf cell) b),
    MiddleLayerCaps (middleBlockFieldLaws (blockPrimes (paperBlockOf cell) b) hne
      (individualBlockRoot (blockPrimes (paperBlockOf cell) b) u hne.L2)) (allpInputs i).k
      (blockScale b)

variable (cell) in
/-- **The remaining analytic inputs of the block specification** of the paper's partition in the
ALLp configuration: `UpperAnalytic` on every block of a band, `MiddleUniformAnalytic` on every
block of a uniform-root piece, `MiddleIndividualAnalytic` on every block of the pieces `2³⁶`,
`2⁴⁰`. *Hypotheses* (spectral; `lem:upper-reference-rp`(ii), `lem:front12:reference`(i),(ii)).
3 families. -/
structure PaperAnalyticInputs : Prop where
  upper : ∀ (b : PaperBlock cell) (k : Fin 310), blockSite b = .inr k → UpperAnalytic b k
  uniform : ∀ (b : PaperBlock cell) (i : Fin 33), blockSite b = .inl i →
    allpIndividual i = none → MiddleUniformAnalytic b i
  individual : ∀ (b : PaperBlock cell) (i : Fin 33) (u : ℚ), blockSite b = .inl i →
    allpIndividual i = some u → MiddleIndividualAnalytic b i u

/-! ## The specification -/

/-- A block of band `k` lies above the band's recorded start. -/
theorem upper_hp {b : PaperBlock cell} {k : Fin 310} (hs : blockSite b = .inr k)
    (j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b}) :
    ((UpperRecords.CompletionData.record k).start : ℝ) ≤ blockPrimes (paperBlockOf cell) b j := by
  have h1 : (UpperRecords.CompletionData.record k).start = (bandOf k).1 :=
    congrArg Prod.fst (UpperRecords.CompletionData.record_endpoints k)
  have h2 := (mem_site j).1
  rw [hs] at h2
  have h3 : (UpperRecords.CompletionData.record k).start ≤ blockPrimes (paperBlockOf cell) b j := by
    rw [h1]
    exact h2
  exact_mod_cast h3

/-- **The six middle labelling sets of a block are nonempty** (`middleNonempty_explicit`, H1): the
primes of a block are at least `Q₃ > 2²⁰`. -/
theorem blockNonempty (hW : Target.Weil) (b : PaperBlock cell) :
    MiddleNonempty (blockPrimes (paperBlockOf cell) b) := by
  have hge : ∀ j, PartV.Q3 ≤ blockPrimes (paperBlockOf cell) b j := fun j =>
    (blockPrimes_mod_ge b j).2
  refine middleNonempty_explicit _ (fun j => weilBound_of_target hW _ ?_) (fun j => ?_)
  · have := hge j
    unfold PartV.Q3 at this
    omega
  · have h : ((2 ^ 20 : ℕ) : ℝ) ≤ blockPrimes (paperBlockOf cell) b j := by
      exact_mod_cast le_trans (by norm_num [PartV.Q3]) (hge j)
    exact_mod_cast h

/-- **The specification of a middle block of piece `i`** (`lem:front12:reference`(iii)): the ALLp
record of the piece, the root of `allpIndividual i`, the scale `b_𝔅^{-1/2}` and the analytic
inputs. -/
noncomputable def middleSpec (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (i : Fin 33) (hs : blockSite b = .inl i) :
    (o : Option ℚ) → allpIndividual i = o → PaperBlockSpec (paperBlockOf cell) b
  | none, hu => .middleUniform
      { hne := blockNonempty hW b
        W := allpWeights i
        I := allpInputs i
        r := blockScale b
        hr := (blockScale_pos b).le
        hW := allpWeights_completes i
        hf₂ := (allpInputs_nonneg i).2.2.2.1
        hf₁ := (allpInputs_nonneg i).2.2.1
        hrows₂ := (A.uniform b i hs hu).rows₂ (blockNonempty hW b)
        hrows₁ := (A.uniform b i hs hu).rows₁ (blockNonempty hW b)
        hroot₂ := (A.uniform b i hs hu).root₂ (blockNonempty hW b)
        hroot₁ := (A.uniform b i hs hu).root₁ (blockNonempty hW b)
        hcap := (A.uniform b i hs hu).caps (blockNonempty hW b) }
  | some u, hu => .middleIndividual
      { hne := blockNonempty hW b
        u := u
        W := allpWeights i
        I := allpInputs i
        r := blockScale b
        hr := (blockScale_pos b).le
        hW := allpWeights_completes i
        hf₂ := (allpInputs_nonneg i).2.2.2.1
        hf₁ := (allpInputs_nonneg i).2.2.1
        hrows₂ := (A.individual b i u hs hu).rows₂ (blockNonempty hW b)
        hrows₁ := (A.individual b i u hs hu).rows₁ (blockNonempty hW b)
        hroot₂ := (A.individual b i u hs hu).root₂ (blockNonempty hW b)
        hroot₁ := (A.individual b i u hs hu).root₁ (blockNonempty hW b)
        hcap := (A.individual b i u hs hu).caps (blockNonempty hW b) }

/-- The specification of a block by its site. -/
noncomputable def siteSpec (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell) :
    (s : Site) → blockSite b = s → PaperBlockSpec (paperBlockOf cell) b
  | .inl i, hs => middleSpec hW A b i hs (allpIndividual i) rfl
  | .inr k, hs =>
    .upper (UpperBlockInputs.ofBand k (upper_hp hs) (blockScale_pos b) (A.upper b k hs))

/-- **V2's `spec` for the paper's construction** (`def:construction`(b)), ALLp configuration, from
the analytic inputs `A`. -/
noncomputable def paperSpec (hW : Target.Weil) (A : PaperAnalyticInputs cell) :
    ∀ b, PaperBlockSpec (paperBlockOf cell) b :=
  fun b => siteSpec hW A b (blockSite b) rfl

/-! ## The Gram gate and the scale -/

theorem middleSpec_protects (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (i : Fin 33) (hs : blockSite b = .inl i) :
    ∀ o hu, specProtects (middleSpec hW A b i hs o hu)
  | none, _ => allpWeights_protects i
  | some _, _ => allpWeights_protects i

theorem siteSpec_protects (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell) :
    ∀ s hs, specProtects (siteSpec hW A b s hs)
  | .inl i, hs => middleSpec_protects hW A b i hs _ rfl
  | .inr _, _ => trivial

/-- **A2's `GramInputs` for the paper's construction**: the protection `v_D ≥ 2 k_D w_D`
(`eq:protection`) on every middle block, from the ALLp records. -/
theorem paperGi (hW : Target.Weil) (A : PaperAnalyticInputs cell) :
    GramInputs (paperBlockOf cell) (paperSpec hW A) :=
  ⟨fun b => siteSpec_protects hW A b _ rfl⟩

theorem middleSpec_scale (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell)
    (i : Fin 33) (hs : blockSite b = .inl i) :
    ∀ o hu, specScale (paperIn cell) (middleSpec hW A b i hs o hu)
  | none, _ => blockScale_sq_mul b
  | some _, _ => blockScale_sq_mul b

theorem siteSpec_scale (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell) :
    ∀ s hs, specScale (paperIn cell) (siteSpec hW A b s hs)
  | .inl i, hs => middleSpec_scale hW A b i hs _ rfl
  | .inr _, _ => trivial

/-- **The scale of every block is `r = b_𝔅^{-1/2}`** (`lem:record:middle-prices`), the hypothesis
`hsc` of A2's `hB_of_charges` and `gramBracketTarget_U₀_le`. -/
theorem paperSpec_scale (hW : Target.Weil) (A : PaperAnalyticInputs cell) (b : PaperBlock cell) :
    specScale (paperIn cell) (paperSpec hW A b) :=
  siteSpec_scale hW A b _ rfl

end Sarkozy.BlockSpecPaper

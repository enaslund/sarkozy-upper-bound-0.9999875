module

public import Sarkozy.OpsSteps.Sym
public import Sarkozy.OpsSteps.FineGroup

@[expose] public section

/-!
# The category `e_s` of `lem:orbit-coupon`(i), expanded and evaluated (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i) (ll. 1262–1295).

The input `hcat` of `Sym.hsym_of_category` is the bound of the category `e_s` (exactly one record
difference, of tag `s`) of an orbit average. The paper expands `Ñ_{0,𝔅} = μ + (E_add + H) + G` at
the other first-stage atoms, charges the `G`-free term with the symmetric price `s_{𝔅'}` and the
others with the sharp price `d_{𝔅'}`, and evaluates the polynomial
`d (∏(1 + v + w) − ∏(1 + v)) + s ∏(1 + v)` with upper prices. Here:

* `catLaw`, `catSet`, `catT`, **`avg_eq_sum_catT`**: the expansion: for a split `isG` of the bracket
  records, `½(E_σ(Q₁) + E_σ(Q₂)) = ∑_Z T_{σ,Z}`, `Z` the atoms carrying `G = ∑_{isG} κu`
  (`Ñ_{0,𝔅} = (μ + ∑_{¬isG} κu) + G`);
* **`cat_poly_le`**: the evaluation: per-term bounds with price `s` at `Z = ∅` and `d` otherwise
  give `|∑_Z T_Z| ≤ K (d e^{U₀} − (d − s) e^{tU}) + ∑ r` (`background_poly_eq`, `background_le`);
* **`hcat_of_terms`**, **`hsym_of_terms`**: hence `hcat` and `hsym`, from per-term bounds with
  the prices of the single difference (`tagWeight` at `p = 0`), the symmetric prices
  `0 ≤ s_{𝔟,i} ≤ d_{𝔟,i}`, the total `∑_{tag s} s_{𝔟,i} + tδ ≤ d_{T,s}` (`cert:envelopes`(d)),
  and upper prices (`lem:oct24:invariant-background`(v)).

The remaining inputs are the per-term bounds `hterm` (C): at `Z = ∅` the symmetric sharp bound
(`lem:record:one-stage-folded-e`(e), after `Sym.sym_swap`), at `Z ≠ ∅` `lem:sharp-first`'s per-term
bound with the `G` atoms priced apart, and the summation of their remainders.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeSteps Sarkozy.Envelopes
  Sarkozy.BlockFrame Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

/-! ## The evaluation of one category term -/

/-- **The polynomial of the proof of `lem:orbit-coupon`(i), evaluated**: if every term `T_Z` is at
most `K · price(Z) ∏_{Z} w ∏_{Zᶜ}(1 + v) + r_Z`, the price being `s` at `Z = ∅` and `d` otherwise,
then `|∑_Z T_Z| ≤ K (d e^{U₀} − (d − s) e^{tU}) + ∑_Z r_Z`. -/
theorem cat_poly_le {ι : Type*} [Fintype ι] [DecidableEq ι] (T r : (ι → Bool) → ℝ)
    {K dd ss U₀ tU : ℝ} {v w m n : ι → ℝ} (hK : 0 ≤ K) (hs : 0 ≤ ss) (hsd : ss ≤ dd)
    (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b) (hvm : ∀ b, v b ≤ m b) (hwn : ∀ b, w b ≤ n b)
    (hm : ∑ b, m b = tU) (hU : ∑ b, (m b + n b) ≤ U₀)
    (hT : ∀ f, |T f| ≤ K * ((if f = (fun _ => false) then ss else dd) *
      ∏ c, (if f c then w c else 1 + v c)) + r f) :
    |∑ f, T f| ≤ K * (dd * Real.exp U₀ - (dd - ss) * Real.exp tU) + ∑ f, r f := by
  have h1 : |∑ f, T f| ≤ ∑ f, (K * ((if f = (fun _ => false) then ss else dd) *
      ∏ c, (if f c then w c else 1 + v c)) + r f) :=
    (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun f _ => hT f)
  rw [sum_add_distrib, ← mul_sum, background_poly_eq v w dd ss] at h1
  have h2 := mul_le_mul_of_nonneg_left (background_le univ hs hsd hv hw hvm hwn hm hU) hK
  linarith

/-- The term of `e_s` in the tag series: `tagTerm d v e_s s = d_s`. -/
theorem tagTerm_single {Tag : Type*} [Fintype Tag] [DecidableEq Tag] (d v : Tag → ℝ) (s : Tag) :
    tagTerm d v (Pi.single s 1) s = d s := by
  rw [← tagMin_single d v s]
  have hts : tagsOf (Pi.single s 1 : Tag → ℕ) = {s} := by
    ext j
    by_cases hj : j = s
    · subst hj; simp [tagsOf]
    · simp [tagsOf, hj, Pi.single_apply]
  have hne : (tagsOf (Pi.single s 1 : Tag → ℕ)).Nonempty := by rw [hts]; exact singleton_nonempty s
  unfold tagMin
  rw [dite_eq_left hne]
  simp only [hts, inf'_singleton]

section Weight

variable {J : Type*} [Fintype J] [DecidableEq J] {I : J → Type*} [∀ b, Fintype (I b)]
  [∀ b, DecidableEq (I b)] {Tag : Type*} [Fintype Tag] [DecidableEq Tag]

omit [DecidableEq J] [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [Fintype Tag] in
theorem tagWeight_nonneg (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (hp : ∀ b, 0 ≤ p b) (j : Tag)
    (σ : ∀ b, Option (I b)) : 0 ≤ tagWeight tag d v p j σ := by
  unfold tagWeight
  refine prod_nonneg fun b _ => ?_
  rcases σ b with _ | i
  · simp only [Option.elim_none]
    linarith [hp b]
  · simp only [Option.elim_some]
    split_ifs
    · exact hd b i
    · exact hv b i

omit [DecidableEq J] [∀ b, Fintype (I b)] [∀ b, DecidableEq (I b)] [Fintype Tag] in
theorem tagWeight_mono (tag : ∀ b, I b → Tag) {d d' v : ∀ b, I b → ℝ} {p : J → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hdd : ∀ b i, d b i ≤ d' b i) (hv : ∀ b i, 0 ≤ v b i)
    (hp : ∀ b, 0 ≤ p b) (j : Tag) (σ : ∀ b, Option (I b)) :
    tagWeight tag d v p j σ ≤ tagWeight tag d' v p j σ := by
  unfold tagWeight
  refine prod_le_prod₀ (fun b _ => ?_) fun b _ => ?_
  · rcases σ b with _ | i
    · simp only [Option.elim_none]
      linarith [hp b]
    · simp only [Option.elim_some]
      split_ifs
      · exact hd b i
      · exact hv b i
  · rcases σ b with _ | i
    · exact le_rfl
    · simp only [Option.elim_some]
      split_ifs
      · exact hdd b i
      · exact le_rfl

/-- **The prices of the single differences of tag `s` add up to the tag total.** -/
theorem sum_single_tagWeight_le (tag : ∀ b, I b → Tag) {d v : ∀ b, I b → ℝ}
    (hd : ∀ b i, 0 ≤ d b i) (hv : ∀ b i, 0 ≤ v b i) (s : Tag)
    (𝒮 : Finset (∀ b, Option (I b)))
    (h𝒮 : ∀ σ ∈ 𝒮, countVec tag σ = Pi.single s 1) :
    ∑ σ ∈ 𝒮, tagWeight tag d v (fun _ => 0) s σ ≤ tagTotal tag d s := by
  have h0 : ∀ b : J, 0 ≤ (fun _ => (0 : ℝ)) b := fun _ => le_rfl
  have hsub : 𝒮 ⊆ univ.filter (fun σ : (∀ b, Option (I b)) => countVec tag σ = Pi.single s 1) :=
    fun σ hσ => mem_filter.mpr ⟨mem_univ _, h𝒮 σ hσ⟩
  refine (sum_le_sum_of_subset_of_nonneg hsub fun σ _ _ =>
    tagWeight_nonneg tag hd hv h0 s σ).trans ?_
  refine (sum_category_le tag hd hv h0 (Pi.single s 1) s).trans ?_
  rw [tagTerm_single]
  simp

end Weight

/-! ## The expansion at the paper's data -/

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (A : Finset ℤ)
  (isG : ∀ b : BlockAtom Bk J L, D.GB.Iu L b → Bool) (S : Finset (BlockAtom Bk J L))

/-- The law of an atom in the expanded category term: `Q` on `S`, the difference at a chosen atom,
and elsewhere `G = ∑_{isG} κu` (`y = true`) or `Ñ^inv = μ + ∑_{¬isG} κu` (`y = false`). -/
noncomputable def catLaw (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) (y : Bool) :
    TheoremCBlock.AtomMeasure m₀ blk p L b :=
  (σ b).elim
    (if decide (b ∈ S) then Qb b else if y then
      ∑ i ∈ univ.filter (fun i => isG b i = true), D.GB.κu L b i
    else D.R.law p L b + ∑ i ∈ univ.filter (fun i => isG b i = false), D.GB.κu L b i)
    (fun i => if decide (b ∈ S) then 0 else D.FS.κ' L b i - D.FS.κ L b i)

/-- The admissible values of `Z` at an atom: only `false` on `S` and at the differences. -/
def catSet (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) : Finset Bool :=
  if (σ b).isSome || decide (b ∈ S) then {false} else univ

/-- The term `T_{σ,Z}` of the orbit average (zero for an inadmissible `Z`). -/
noncomputable def catT (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (f : BlockAtom Bk J L → Bool) : ℝ :=
  if f ∈ Fintype.piFinset (catSet D L S σ) then
    (1 / 2 : ℝ) *
      (diagonalIntegral (tensorLaw fun b => catLaw D L isG S Q₁ σ b (f b))
          (blockLift m₀ blk p L A) +
        diagonalIntegral (tensorLaw fun b => catLaw D L isG S Q₂ σ b (f b))
          (blockLift m₀ blk p L A))
  else 0

omit [DecidableEq P] in
theorem sharpPiece_eq_sum (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) :
    sharpPiece D L Qb (fun b => decide (b ∈ S)) σ b =
      ∑ y ∈ catSet D L S σ b, catLaw D L isG S Qb σ b y := by
  unfold sharpPiece catSet catLaw
  rcases hσ : σ b with _ | i
  · by_cases hb : b ∈ S
    · simp [hb]
    · simp only [Option.elim_none, hb, decide_false, Bool.false_eq_true, ↓reduceIte,
        Option.isSome_none, Bool.or_self, Fintype.sum_bool]
      have e1 := sum_filter_add_sum_filter_not univ (fun i => isG b i = true)
        (fun i => D.GB.κu L b i)
      simp only [Bool.not_eq_true] at e1
      have hN : D.GB.N₀ L b = D.R.law p L b + ∑ i, D.GB.κu L b i := by
        rw [← D.GB.N₀_sub L b]
        abel
      rw [hN, ← e1]
      abel
  · simp

omit [DecidableEq P] in
/-- **The expansion of a sharp term over the `G` atoms.** -/
theorem Eσ_eq_sum (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) :
    Eσ D L A S Qb σ = ∑ f ∈ Fintype.piFinset (catSet D L S σ),
      diagonalIntegral (tensorLaw fun b => catLaw D L isG S Qb σ b (f b))
        (blockLift m₀ blk p L A) := by
  unfold Eσ
  have hL : sharpPiece D L Qb (fun b => decide (b ∈ S)) σ =
      fun b => ∑ y ∈ catSet D L S σ b, catLaw D L isG S Qb σ b y :=
    funext fun b => sharpPiece_eq_sum D L isG S Qb σ b
  rw [hL, tensorLaw_sum_finset, diagonalIntegral_sum]

omit [DecidableEq P] in
/-- **The orbit average of a sharp term is the sum of its `G`-expanded terms.** -/
theorem avg_eq_sum_catT (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) :
    (1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ) =
      ∑ f, catT D L A isG S Q₁ Q₂ σ f := by
  unfold catT
  rw [sum_ite_mem univ, univ_inter, Eσ_eq_sum D L A isG S Q₁ σ, Eσ_eq_sum D L A isG S Q₂ σ,
    ← sum_add_distrib, mul_sum]

/-- **The canonical remainder of an expanded category term**: the excess of `|T_{σ,Z}|` over its
priced main term (symmetric price at `Z = ∅`, sharp price otherwise). -/
noncomputable def rCat (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (v w : BlockAtom Bk J L → ℝ) (K : ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (f : BlockAtom Bk J L → Bool) : ℝ :=
  max 0 (|catT D L A isG S Q₁ Q₂ σ f| -
    K * ((if f = (fun _ => false) then
        tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
      else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
      ∏ c, (if f c then w c else 1 + v c)))

omit [DecidableEq P] in
theorem hterm_rCat (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (v w : BlockAtom Bk J L → ℝ) (K : ℝ)
    (σ : ∀ b, Option (D.FS.Ib L b)) (f : BlockAtom Bk J L → Bool) :
    |catT D L A isG S Q₁ Q₂ σ f| ≤
      K * ((if f = (fun _ => false) then
          tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
        else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
        ∏ c, (if f c then w c else 1 + v c)) + rCat D L A isG S Q₁ Q₂ s sym v w K σ f := by
  unfold rCat
  linarith [le_max_right (0 : ℝ) (|catT D L A isG S Q₁ Q₂ σ f| -
    K * ((if f = (fun _ => false) then
        tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
      else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
      ∏ c, (if f c then w c else 1 + v c)))]

omit [DecidableEq P] in
/-- **`hcat` from the per-term bounds** (`lem:orbit-coupon`(i), see the module docstring). With
`d_σ`, `s_σ` the sharp and symmetric prices of the single difference of `σ`, every expanded term
`T_{σ,Z}` of a choice `σ ∈ e_s` is assumed at most `K · (Z = ∅ ? s_σ : d_σ) ∏_Z w ∏_{Zᶜ}(1 + v) + r`
(`hterm`, C). Then the category satisfies the input `hcat` of `hsym_of_category`. -/
theorem hcat_of_terms (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    {K tU tδ : ℝ} (hK : 0 ≤ K)
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    {v w m n : BlockAtom Bk J L → ℝ} (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b)
    (hvm : ∀ b, v b ≤ m b) (hwn : ∀ b, w b ≤ n b)
    (hm : ∑ b, m b = tU) (hU : ∑ b, (m b + n b) ≤ D.GB.U₀)
    (r : (∀ b, Option (D.FS.Ib L b)) → (BlockAtom Bk J L → Bool) → ℝ)
    (hterm : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∀ f,
      |catT D L A isG S Q₁ Q₂ σ f| ≤
        K * ((if f = (fun _ => false) then
            tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
          else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
          ∏ c, (if f c then w c else 1 + v c)) + r σ f) :
    |∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
        (1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| ≤
      K * (D.FS.dT s * Real.exp D.GB.U₀ - Real.exp tU * tδ) +
        ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∑ f, r σ f := by
  set 𝒮 := (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
    (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1) with h𝒮def
  have h𝒮 : ∀ σ ∈ 𝒮, countVec (D.FS.tag L) σ = Pi.single s 1 :=
    fun σ hσ => (mem_filter.mp hσ).2
  have hd0 : ∀ b i, 0 ≤ D.FS.dprice L b i := fun b i => D.dprice_nonneg L b i
  have hv0 : ∀ b i, 0 ≤ D.FS.vprice L b i := fun b i => D.vprice_nonneg L b i
  have h0 : ∀ b : BlockAtom Bk J L, 0 ≤ (fun _ => (0 : ℝ)) b := fun _ => le_rfl
  have hper : ∀ σ ∈ 𝒮, |(1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| ≤
      K * (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
          Real.exp D.GB.U₀ -
        (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ -
          tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ) * Real.exp tU) +
        ∑ f, r σ f := by
    intro σ hσ
    rw [avg_eq_sum_catT D L A isG S Q₁ Q₂ σ]
    exact cat_poly_le _ (r σ) hK (tagWeight_nonneg _ hsym0 hv0 h0 s σ)
      (tagWeight_mono _ hsym0 hsymd hv0 h0 s σ) hv hw hvm hwn hm hU (hterm σ hσ)
  have hD : ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ ≤
      D.FS.dT s :=
    (sum_single_tagWeight_le _ hd0 hv0 s 𝒮 h𝒮).trans (D.FS.dT_total L s)
  have hS : ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ ≤
      tagTotal (D.FS.tag L) sym s := sum_single_tagWeight_le _ hsym0 hv0 s 𝒮 h𝒮
  have htU : tU ≤ D.GB.U₀ := by
    have e : ∑ b, (m b + n b) = tU + ∑ b, n b := by rw [sum_add_distrib, hm]
    have hn : 0 ≤ ∑ b, n b := sum_nonneg fun b _ => (hw b).trans (hwn b)
    linarith
  have hexp : Real.exp tU ≤ Real.exp D.GB.U₀ := Real.exp_le_exp.mpr htU
  set dS := ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ
    with hdS
  set sS := ∑ σ ∈ 𝒮, tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ with hsS
  have hdist : ∑ σ ∈ 𝒮, K *
      (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
          Real.exp D.GB.U₀ -
        (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ -
          tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ) * Real.exp tU) =
      K * ((Real.exp D.GB.U₀ - Real.exp tU) * dS + Real.exp tU * sS) := by
    simp only [hdS, hsS, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun σ _ => by ring
  have h1 : (Real.exp D.GB.U₀ - Real.exp tU) * dS ≤ (Real.exp D.GB.U₀ - Real.exp tU) * D.FS.dT s :=
    mul_le_mul_of_nonneg_left hD (by linarith)
  have h2 : Real.exp tU * sS ≤ Real.exp tU * (D.FS.dT s - tδ) :=
    mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have h3 := mul_le_mul_of_nonneg_left (add_le_add h1 h2) hK
  have h4 : K * ((Real.exp D.GB.U₀ - Real.exp tU) * D.FS.dT s + Real.exp tU * (D.FS.dT s - tδ)) =
      K * (D.FS.dT s * Real.exp D.GB.U₀ - Real.exp tU * tδ) := by ring
  calc _ ≤ ∑ σ ∈ 𝒮, |(1 / 2 : ℝ) * (Eσ D L A S Q₁ σ + Eσ D L A S Q₂ σ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ σ ∈ 𝒮, (K *
          (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ *
              Real.exp D.GB.U₀ -
            (tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ -
              tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ) * Real.exp tU) +
          ∑ f, r σ f) := sum_le_sum hper
    _ = K * ((Real.exp D.GB.U₀ - Real.exp tU) * dS + Real.exp tU * sS) +
          ∑ σ ∈ 𝒮, ∑ f, r σ f := by rw [sum_add_distrib, hdist]
    _ ≤ _ := by linarith

omit [DecidableEq P] in
/-- **`hsym` from the per-term bounds of the category `e_s`** (`hsym_of_category` with
`hcat_of_terms`): for the orbit average of two tensors on `S = supp ω`, with
`K = (1 + ε) C_X Y`,
`|Y^Ñ[κ̄] − Y^{Ñ₀}[κ̄]| ≤ (R_err − e^{tU} tδ) K + ∑_σ ½(rCan₁ + rCan₂) + ∑ r`. -/
theorem hsym_of_terms (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hY : 0 ≤ D.Y L A)
    (ω : Choice (D.CL.T L)) (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (s : D.FS.Tag) {tU tδ : ℝ}
    (sym : ∀ b, D.FS.Ib L b → ℝ) (hsym0 : ∀ b i, 0 ≤ sym b i)
    (hsymd : ∀ b i, sym b i ≤ D.FS.dprice L b i)
    (htot : tagTotal (D.FS.tag L) sym s + tδ ≤ D.FS.dT s)
    {v w m n : BlockAtom Bk J L → ℝ} (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b)
    (hvm : ∀ b, v b ≤ m b) (hwn : ∀ b, w b ≤ n b)
    (hm : ∑ b, m b = tU) (hU : ∑ b, (m b + n b) ≤ D.GB.U₀)
    (r : (∀ b, Option (D.FS.Ib L b)) → (BlockAtom Bk J L → Bool) → ℝ)
    (hterm : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∀ f,
      |catT D L A isG (Choice.support ω) Q₁ Q₂ σ f| ≤
        ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) *
          ((if f = (fun _ => false) then
              tagWeight (D.FS.tag L) sym (D.FS.vprice L) (fun _ => 0) s σ
            else tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (fun _ => 0) s σ) *
            ∏ c, (if f c then w c else 1 + v c)) + r σ f) :
    |paperEN D L A (Choice.support ω) ((1 / 2 : ℝ) •
        (tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₁ b.1) +
          tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₂ b.1))) -
      paperEN0 D L A (Choice.support ω) ((1 / 2 : ℝ) •
        (tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₁ b.1) +
          tensorLaw (fun b : {b // b ∈ Choice.support ω} => Q₂ b.1)))| ≤
      (D.GB.Rerr - Real.exp tU * tδ) *
          ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
            D.Y L A) +
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          (1 / 2 : ℝ) * (rCan D L A (Choice.support ω) Q₁
              ((1 + εE L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
                D.Y L A) σ +
            rCan D L A (Choice.support ω) Q₂
              ((1 + εE L) *
                (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
                D.Y L A) σ) +
        ∑ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
          (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1), ∑ f, r σ f := by
  have hK : 0 ≤ (1 + εE L) *
      (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) * D.Y L A :=
    mul_nonneg (mul_nonneg (by linarith [hε0 L])
      (prod_nonneg fun b _ => D.selectionFactor_nonneg L b)) hY
  exact hsym_of_category D L A εE hε0 hY ω Q₁ Q₂ s
    (hcat_of_terms D L A isG (Choice.support ω) Q₁ Q₂ s hK sym hsym0 hsymd htot hv hw hvm hwn
      hm hU r hterm)

end Sarkozy.OpsSteps

module

public import Sarkozy.Structured.EnvelopeEnergyGlue
public import Sarkozy.Functional.ConductorMoment

/-!
# The conductor price and `lem:hyb:moment` for WP-FI's coupled index law

`paper/sections/09_comparison_theorem.tex`, `def:hyb:coupled`(g) and `lem:hyb:moment`;
`paper/sections/10_comparison_lemmas.tex`, proof of `lem:envelope-energy`. At fixed depths `𝒥`
the energy of each subset term carries the conductor price
`Π_𝒥 = ∏_{e ∈ 𝒮} (K sq(D_{𝒥_e}))^{2a/d} κ_e^{2θ/d}`, `D_{𝒥_e} = ∏_p p^{𝒥_{e,p}}`, and only then
is it averaged: `E_𝒥 Π_𝒥 = R_I^{|𝒮|}` (uniform intervals, `κ_e = 1`).

WP-R's `Structured.envelopeEnergies_of_terms` and `fixedIntervalEnvelopeEnergies_of_terms` take
the price `Pj` as a free function and the moment `E_𝒥 E_ω Pj ≤ R_I^k` as a hypothesis (`hmom`).
Here `Pj` is the paper's price on WP-FI's depth vectors (the index law `D.index` of
`TheoremC.ComparisonData`: interval coordinate `none`, residue coordinates `some q`):

* `queryPrice`: `(K sq(D_J))^w` for one query, `D_J = ∏_q (pr q)^{J (some q)}`;
* `expect_queryPrice`: **`lem:hyb:moment` for this law**:
  `E (K sq(D_J))^w = K^w ∏_q momentFactor (pr q) (h q) δ_q w`, the depth law of one query being
  WP-S's `IndexSupport.depthLaw` (the interval coordinate is always revealed and does not
  enter); it uses WP-FI's `Functional.expect_pow_ceil_half` and `Tails.prob_ge`;
* `expect_conductorPrice`, `expect_fixedPrice`: the products over the queries (all of `E`, resp.
  the active set `𝒮`, with the fixed-interval factor `K^{2θ/d}`);
* `envelopeEnergies_of_conductor`, `fixedIntervalEnvelopeEnergies_of_conductor`: WP-R's two
  reductions with `Pj` the paper's price and `hmom` discharged.

`IndexLaw.R_I` is a free field in WP-FI's `TheoremC.IndexLaw` (with only `0 ≤ R_I`). Its
meaning, `R_I = E_J (K sq(D_J))^{2a/d}` (`def:hyb:coupled`(g)), enters as the hypothesis
`hRI`: the one-query moment of every query is at most `R_I` (`oneQueryBound`).
-/

@[expose] public section

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.EnvelopeInputs

open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison

section Price

variable {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

/-- The depth vectors of one query: the interval coordinate `none`, the residue coordinates
`some q`. -/
abbrev QueryDepth := ∀ j : Option P, Fin ((coordChain blockScale pr h j).depth + 1)

/-- The conductor `D_J = ∏_q (pr q)^{J_q}` of a depth vector. -/
def queryConductor (J : QueryDepth pr h) : ℕ :=
  ∏ q, pr q ^ ((J (some q) : ℕ))

/-- The one-query conductor price `(K sq(D_J))^w` (`def:hyb:coupled`(g), `w = 2a/d`). -/
noncomputable def queryPrice (w : ℝ) (J : QueryDepth pr h) : ℝ :=
  ((blockScale : ℝ) * (leastSquare (queryConductor pr h J) : ℝ)) ^ w

/-- The coordinate factors of the price: `K^w` on the interval coordinate, `(p^{2w})^⌈J_p/2⌉`
on the residue coordinate of `p`. -/
noncomputable def priceFactor (w : ℝ) :
    ∀ j : Option P, Fin ((coordChain blockScale pr h j).depth + 1) → ℝ
  | none => fun _ => (blockScale : ℝ) ^ w
  | some q => fun x => ((pr q : ℝ) ^ (2 * w)) ^ (((x : ℕ) + 1) / 2)

theorem queryPrice_eq_prod (hp : ∀ q, (pr q).Prime) (hinj : Injective pr) (w : ℝ)
    (J : QueryDepth pr h) :
    queryPrice pr h w J = ∏ j, priceFactor pr h w j (J j) := by
  rw [Fintype.prod_option]
  unfold queryPrice queryConductor
  rw [leastSquare_prod_univ_prime_pow pr (fun q => (J (some q) : ℕ)) hp hinj]
  push_cast
  rw [Real.mul_rpow (Nat.cast_nonneg _) (prod_nonneg fun i _ => by positivity),
    ← Real.finsetProd_rpow _ _ (fun i _ => by positivity)]
  congr 1
  apply prod_congr rfl
  intro q _
  exact rpow_two_mul_pow _ (Nat.cast_nonneg _) _ w

omit [DecidableEq P] in
theorem queryPrice_nonneg (w : ℝ) (J : QueryDepth pr h) : 0 ≤ queryPrice pr h w J :=
  Real.rpow_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _

/-- `E z^⌈J/2⌉` under the depth law of tails `t` is `momentFactor` (`lem:hyb:moment`, one prime). -/
theorem expect_tails_pow_ceil_half {hd : ℕ} (t : Tails hd) (q : ℕ) (w : ℝ) :
    t.law.expect (fun x : Fin (hd + 1) => ((q : ℝ) ^ (2 * w)) ^ (((x : ℕ) + 1) / 2)) =
      momentFactor q hd t.tail w := by
  rw [expect_pow_ceil_half]
  unfold momentFactor
  congr 2
  apply sum_congr rfl
  intro l hl
  congr 1
  have hl' := mem_Icc.mp hl
  have hle : 2 * l - 1 < hd + 1 := by omega
  have hprob := t.prob_ge ⟨2 * l - 1, hle⟩
  unfold depthTail
  rw [← hprob]
  apply FiniteLaw.expect_congr
  intro u
  simp only [Fin.le_iff_val_le_val]

/-- **`lem:hyb:moment` for one query of WP-FI's index law**: under WP-S's depth law with tails
`t`, `E (K sq(D_J))^w = K^w ∏_q momentFactor (pr q) (h q) δ_q w`. -/
theorem expect_queryPrice (hp : ∀ q, (pr q).Prime) (hinj : Injective pr) (w : ℝ)
    (t : ∀ j, Tails (coordChain blockScale pr h j).depth) :
    (IndexSupport.depthLaw (coordChain blockScale pr h) t).expect (queryPrice pr h w) =
      (blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t (some q)).tail w := by
  have hfun : queryPrice pr h w = fun J => ∏ j, priceFactor pr h w j (J j) :=
    funext (queryPrice_eq_prod pr h hp hinj w)
  rw [hfun]
  unfold IndexSupport.depthLaw
  rw [FiniteLaw.expect_pi_product, Fintype.prod_option]
  congr 1
  · simp only [priceFactor, FiniteLaw.expect_const]
  · apply prod_congr rfl
    intro q _
    exact expect_tails_pow_ceil_half (t (some q)) (pr q) w

/-- The one-query moment of the query `e` is at most `R`. -/
def oneQueryBound {E : Type} (t : E → ∀ j, Tails (coordChain blockScale pr h j).depth)
    (w R : ℝ) : Prop :=
  ∀ e, (blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t e (some q)).tail w ≤ R

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The conductor price of the index `Π_𝒥 = ∏_e (K sq(D_{𝒥_e}))^w` (uniform intervals). -/
noncomputable def conductorPrice (w : ℝ) (Jq : E → QueryDepth pr h) : ℝ :=
  ∏ e, queryPrice pr h w (Jq e)

/-- The fixed-interval price `Π_𝒮 = ∏_{e ∈ 𝒮} K^{2θ/d} (K sq(D_{𝒥_e}))^w` (`κ_e = K`). -/
noncomputable def fixedPrice (w : ℝ) (S : Finset E) (Jq : E → QueryDepth pr h) : ℝ :=
  ∏ e, if e ∈ S then (blockScale : ℝ) ^ (2 * densityExponent / 72) * queryPrice pr h w (Jq e)
    else 1

omit [DecidableEq P] [DecidableEq E] in
theorem conductorPrice_nonneg (w : ℝ) (Jq : E → QueryDepth pr h) :
    0 ≤ conductorPrice pr h w Jq :=
  prod_nonneg fun e _ => queryPrice_nonneg pr h w (Jq e)

omit [DecidableEq P] in
theorem fixedPrice_nonneg (w : ℝ) (S : Finset E) (Jq : E → QueryDepth pr h) :
    0 ≤ fixedPrice pr h w S Jq := by
  refine prod_nonneg fun e _ => ?_
  split_ifs
  · exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (queryPrice_nonneg pr h w (Jq e))
  · exact zero_le_one

/-- **`lem:hyb:moment`, all queries**: `E_𝒥 Π_𝒥 = ∏_e K^w ∏_q momentFactor`. -/
theorem expect_conductorPrice (hp : ∀ q, (pr q).Prime) (hinj : Injective pr) (w : ℝ)
    (t : E → ∀ j, Tails (coordChain blockScale pr h j).depth) :
    (queryLaw (fun (_ : E) => coordChain blockScale pr h) t).expect (conductorPrice pr h w) =
      ∏ e, ((blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t e (some q)).tail w) := by
  unfold queryLaw conductorPrice
  rw [FiniteLaw.expect_pi_product
    (fun e => IndexSupport.depthLaw (coordChain blockScale pr h) (t e))
    (fun _ J => queryPrice pr h w J)]
  exact prod_congr rfl fun e _ => expect_queryPrice pr h hp hinj w (t e)

omit [DecidableEq P] [Fintype E] [DecidableEq E] in
/-- The one-query moments are nonnegative (each factor is at least one). -/
theorem moment_nonneg (hp : ∀ q, (pr q).Prime) {w : ℝ} (hw : 0 ≤ w)
    (t : E → ∀ j, Tails (coordChain blockScale pr h j).depth) (e : E) :
    0 ≤ (blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t e (some q)).tail w :=
  mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (prod_nonneg fun q _ => zero_le_one.trans (one_le_momentFactor (hp q).one_lt.le
      (IsDepthTail.nonneg_le ⟨(t e (some q)).tail_zero, (t e (some q)).antitone,
        (t e (some q)).nonneg⟩) hw))

/-- The moment bound `E_𝒥 Π_𝒥 ≤ R^k`. -/
theorem expect_conductorPrice_le (hp : ∀ q, (pr q).Prime) (hinj : Injective pr) {w R : ℝ}
    (hw : 0 ≤ w) (t : E → ∀ j, Tails (coordChain blockScale pr h j).depth)
    (hR : oneQueryBound pr h t w R) :
    (queryLaw (fun (_ : E) => coordChain blockScale pr h) t).expect (conductorPrice pr h w) ≤
      R ^ Fintype.card E := by
  rw [expect_conductorPrice pr h hp hinj w t]
  calc ∏ e, ((blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t e (some q)).tail w)
      ≤ ∏ _e : E, R := prod_le_prod₀ (fun e _ => moment_nonneg pr h hp hw t e) (fun e _ => hR e)
    _ = R ^ Fintype.card E := by rw [prod_const, card_univ]

omit [Fintype E] in
/-- The expectation of the fixed-interval price at one query. -/
theorem expect_fixedFactor (hp : ∀ q, (pr q).Prime) (hinj : Injective pr) (w : ℝ) (S : Finset E)
    (t : E → ∀ j, Tails (coordChain blockScale pr h j).depth) (e : E) :
    (IndexSupport.depthLaw (coordChain blockScale pr h) (t e)).expect (fun J =>
        if e ∈ S then (blockScale : ℝ) ^ (2 * densityExponent / 72) * queryPrice pr h w J
        else 1) =
      if e ∈ S then (blockScale : ℝ) ^ (2 * densityExponent / 72) *
        ((blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t e (some q)).tail w) else 1 := by
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [FiniteLaw.expect_const_mul, expect_queryPrice pr h hp hinj w (t e)]
  · simp only [he, ↓reduceIte, FiniteLaw.expect_const]

/-- **`lem:hyb:moment` at fixed intervals**: `E_𝒥 Π_𝒮 ≤ (K^{2θ/d} R)^{|𝒮|}`. -/
theorem expect_fixedPrice_le (hp : ∀ q, (pr q).Prime) (hinj : Injective pr) {w R : ℝ}
    (hw : 0 ≤ w) (S : Finset E) (t : E → ∀ j, Tails (coordChain blockScale pr h j).depth)
    (hR : oneQueryBound pr h t w R) :
    (queryLaw (fun (_ : E) => coordChain blockScale pr h) t).expect (fixedPrice pr h w S) ≤
      ((blockScale : ℝ) ^ (2 * densityExponent / 72) * R) ^ S.card := by
  unfold queryLaw fixedPrice
  rw [FiniteLaw.expect_pi_product
    (fun e => IndexSupport.depthLaw (coordChain blockScale pr h) (t e))
    (fun e J => if e ∈ S then (blockScale : ℝ) ^ (2 * densityExponent / 72) * queryPrice pr h w J
      else 1)]
  rw [Finset.prod_congr rfl (fun e _ => expect_fixedFactor pr h hp hinj w S t e)]
  have hK : (0 : ℝ) ≤ (blockScale : ℝ) ^ (2 * densityExponent / 72) :=
    Real.rpow_nonneg (Nat.cast_nonneg _) _
  calc ∏ e, (if e ∈ S then (blockScale : ℝ) ^ (2 * densityExponent / 72) *
        ((blockScale : ℝ) ^ w * ∏ q, momentFactor (pr q) (h q) (t e (some q)).tail w) else 1)
      ≤ ∏ e, (if e ∈ S then (blockScale : ℝ) ^ (2 * densityExponent / 72) * R else 1) := by
        refine prod_le_prod₀ (fun e _ => ?_) (fun e _ => ?_)
        · split_ifs
          · exact mul_nonneg hK (moment_nonneg pr h hp hw t e)
          · exact zero_le_one
        · split_ifs
          · exact mul_le_mul_of_nonneg_left (hR e) hK
          · exact le_rfl
    _ = ((blockScale : ℝ) ^ (2 * densityExponent / 72) * R) ^ S.card := by
        rw [prod_ite_mem, univ_inter, prod_const]

end Price

section TheoremC

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The price exponent `w = 2a/d` of the conductor price (`a = decay`, `d = 72`). -/
noncomputable def priceExponent : ℝ := 2 * decay / 72

theorem priceExponent_nonneg : 0 ≤ priceExponent := by
  unfold priceExponent decay
  norm_num

/-- **The meaning of `R_I`** (`def:hyb:coupled`(g)): the conductor moment
`E_J (K sq(D_J))^{2a/d}` of every query of WP-FI's index law is at most `D.S.index.R_I`. By
`expect_queryPrice` the moment of the query `e` is `K^w ∏_q momentFactor (pr q) (h q) δ_{e,q} w`
(`lem:hyb:moment`). `IndexLaw.R_I` is otherwise unconstrained, so this is the one hypothesis
that ties it to the tails. -/
def IndexMomentBound (D : ComparisonData m₀ p pr h E) : Prop :=
  ∀ e, (blockScale : ℝ) ^ priceExponent *
    ∏ q, momentFactor (pr q) (h q) (D.S.index.t e q).tail priceExponent ≤ D.S.index.R_I

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **`EnvelopeEnergies` with the conductor price** (`lem:envelope-energy`, `lem:hyb:moment`):
WP-R's `Structured.envelopeEnergies_of_terms` with `Π_{𝒥,ω} = ∏_e (K sq(D_{𝒥_e}))^{2a/d}`, the
moment hypothesis `hmom` discharged by `lem:hyb:moment` (`expect_conductorPrice_le`) from
`IndexMomentBound`. Remaining inputs: the per-term bounds `htermL`, `htermR` with this price,
and the remainder summations `hremL`, `hremR`. -/
theorem envelopeEnergies_of_conductor (D : ComparisonData m₀ p pr h E)
    (hRI : IndexMomentBound D)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rL rR : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ)
    (htermL : AtCounterexamples D.Y (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then envIncL D L b else D.GB.N L b)
          (revealL hcop D L A Jq ω) (revealL hcop D L A Jq ω)| ≤
        (D.B + z L) * conductorPrice pr h priceExponent Jq * D.Y L A *
          ∏ b, (if f b then envPriceL D L b else 1) + rL L A Jq ω f))
    (htermR : AtCounterexamples D.Y (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then envIncR D L b else D.GB.N L b)
          (revealR hcop D L A Jq ω) (revealR hcop D L A Jq ω)| ≤
        (D.B + z L) * conductorPrice pr h priceExponent Jq * D.Y L A *
          ∏ b, (if f b then envPriceR D L b else 1) + rR L A Jq ω f))
    (hremL : AtCounterexamples D.Y (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A Jq ω f)) ≤ remainder c L A))
    (hremR : AtCounterexamples D.Y (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A Jq ω f)) ≤ remainder c L A)) :
    D.EnvelopeEnergies hcop := by
  refine envelopeEnergies_of_terms hcop D z hz0 hzt hc
    (fun _ Jq _ => conductorPrice pr h priceExponent Jq)
    (fun _ Jq _ => conductorPrice_nonneg pr h priceExponent Jq) (fun L => ?_) rL rR htermL htermR
    hremL hremR
  simp only [FiniteLaw.expect_const]
  exact expect_conductorPrice_le pr h D.S.pr_prime D.S.pr_inj priceExponent_nonneg D.index.t
    (fun e => hRI e)

/-- **`FixedIntervalEnvelopeEnergies` with the conductor price** (`lem:envelope-energy` at fixed
intervals, `lem:hyb:moment`): WP-R's `Structured.fixedIntervalEnvelopeEnergies_of_terms` with
`Π_𝒮 = ∏_{e ∈ 𝒮} K^{2θ/d} (K sq(D_{𝒥_e}))^{2a/d}`, the moment hypothesis discharged
(`expect_fixedPrice_le`) from `IndexMomentBound`. -/
theorem fixedIntervalEnvelopeEnergies_of_conductor (D : ComparisonData m₀ p pr h E)
    (hRI : IndexMomentBound D)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (rL rR : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ)
    (htermL : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then wrapInc D L b else D.GB.N L b)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapSourceHalf m₀ p pr h hcop D.S.Q.u L A S) ω)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapSourceHalf m₀ p pr h hcop D.S.Q.u L A S) ω)| ≤
        (D.B + z L) * fixedPrice pr h priceExponent S Jq * D.Y L A *
          ∏ b, (if f b then wrapPrice D L b else 1) + rL L A S Jq ω f))
    (htermR : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then wrapInc D L b else D.GB.N L b)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapTargetHalf m₀ p pr h hcop D.S.Q.w L A S) ω)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapTargetHalf m₀ p pr h hcop D.S.Q.w L A S) ω)| ≤
        (D.B + z L) * fixedPrice pr h priceExponent S Jq * D.Y L A *
          ∏ b, (if f b then wrapPrice D L b else 1) + rR L A S Jq ω f))
    (hremL : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rL L A S Jq ω f)) ≤ remainder c L A))
    (hremR : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rR L A S Jq ω f)) ≤ remainder c L A)) :
    D.FixedIntervalEnvelopeEnergies hcop := by
  refine fixedIntervalEnvelopeEnergies_of_terms hcop D z hz0 hzt hc
    (fun _ S Jq _ => fixedPrice pr h priceExponent S Jq)
    (fun _ S Jq _ => fixedPrice_nonneg pr h priceExponent S Jq) (fun L S => ?_) rL rR htermL
    htermR hremL hremR
  simp only [FiniteLaw.expect_const]
  exact expect_fixedPrice_le pr h D.S.pr_prime D.S.pr_inj priceExponent_nonneg S
    (fun e => coordTails blockScale pr h (D.S.index.t e)) (fun e => hRI e)

end TheoremC

end Sarkozy.EnvelopeInputs

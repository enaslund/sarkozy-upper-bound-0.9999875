module

public import Sarkozy.EnvelopesPaper.Matching

@[expose] public section

/-!
# (CP8)(c) summability for the envelopes of a refinement

`paper/sections/09_comparison_theorem.tex`, `def:cp8`(c): with `q_𝔟` the product of the primes of
`𝔟` with `e_p = 1` (`oneWeight`; the prime itself at a tail atom),
`∑_𝔟 q_𝔟^{1/4}(p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟 + s_𝔟 + a_𝔟 + T_{L,𝔟} + T_{R,𝔟})` is bounded at every scale.

For the matching envelopes `F.toME a T hL hR` of a refinement `F` (`Matching.lean`), the sum splits
into
* the **first-stage and bracket part** `p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟` (`stagePrice`): when it vanishes at
  the tail atoms (as for A1's first stage and the paper's bracket, which live on the prefix atoms
  only), its weighted sum is at most `W_pre (P + ∑_j (v_j + d_j) + U₀)` with
  `W_pre = ∑_β q_β^{1/4}` over the prefix atoms (`stage_weighted_le`) — proved;
* the **comparison and envelope part** `s_𝔟 + a_𝔟 + T_{L,𝔟} + T_{R,𝔟}`: since
  `T_{s,𝔟} ≤ K_{s,𝔟} + s_𝔟 + a_𝔟` (`priceL_le`, `priceR_le`, the prices of the non-replaced norm
  envelopes are part of the (CP4) prices), it is at most `3 (s_𝔟 + a_𝔟) + K_{L,𝔟} + K_{R,𝔟}`.

**The input** (`SummabilityInputs F`): the weighted summability of the (CP4) prices
(`∑_𝔟 q_𝔟^{1/4}(s_𝔟 + a_𝔟) ≤ σ_CL`) and of the added diagonals of the refinement
(`∑_𝔟 q_𝔟^{1/4}(K_{L,𝔟} + K_{R,𝔟}) ≤ σ_K`), uniformly in the scale. The first is `def:cp8`(c) for
the comparison law (in the paper: the tail prices of `prop:record:upper`(ii), which carry the
weight `p^{1/4}`); the second is trivial when `K` lives on finitely many prefix atoms with
scale-independent prices (the paper's middle blocks).

**`summabilityOf`**: (CP8)(c) for `F.toME a T hL hR`, with the bound
`W_pre (P + ∑_j (v_j + d_j) + U₀) + 3 σ_CL + σ_K`.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopesPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.RecordExpansion (ChangeType symTotal skewTotal)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R} {GB : GramBracket a m₀ blk p S₀ FS}
  {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

/-! ## Weights and prices -/

omit [DecidableEq J₀] [Fintype Bk] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
theorem oneWeight_nonneg (L : ℕ) (b : BlockAtom Bk J L) : 0 ≤ oneWeight blk p pp ep L b := by
  cases b with
  | inl β => exact prod_nonneg fun i _ => Nat.cast_nonneg _
  | inr j => exact Nat.cast_nonneg _

omit [DecidableEq J₀] [Fintype Bk] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
/-- The weight `q_𝔟^{1/4}` of (CP8)(c) is nonnegative. -/
theorem weight_nonneg (L : ℕ) (b : BlockAtom Bk J L) :
    0 ≤ oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) :=
  Real.rpow_nonneg (oneWeight_nonneg L b) _

variable (blk p pp ep) in
/-- `W_pre = ∑_β q_β^{1/4}`, the total weight of the prefix atoms (independent of the scale). -/
noncomputable def prefixWeight : ℝ :=
  ∑ β : Bk, oneWeight blk p pp ep 0 (.inl β : BlockAtom Bk J 0) ^ ((1 : ℝ) / 4)

omit [DecidableEq J₀] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
theorem prefixWeight_nonneg : 0 ≤ prefixWeight blk p pp ep :=
  sum_nonneg fun β _ => weight_nonneg 0 (.inl β)

omit [DecidableEq J₀] [∀ L, Fintype (J L)] [∀ L j, NeZero (p L j)] in
/-- Every prefix weight is at most `W_pre`, at every scale. -/
theorem weight_inl_le (L : ℕ) (β : Bk) :
    oneWeight blk p pp ep L (.inl β : BlockAtom Bk J L) ^ ((1 : ℝ) / 4) ≤
      prefixWeight blk p pp ep (J := J) := by
  have h : oneWeight blk p pp ep L (.inl β : BlockAtom Bk J L) =
      oneWeight blk p pp ep 0 (.inl β : BlockAtom Bk J 0) := rfl
  rw [h]
  exact single_le_sum (f := fun β : Bk =>
    oneWeight blk p pp ep 0 (.inl β : BlockAtom Bk J 0) ^ ((1 : ℝ) / 4))
    (fun β _ => weight_nonneg 0 (.inl β)) (mem_univ β)

variable (FS GB) in
/-- The first-stage and bracket prices of an atom, `p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟`. -/
noncomputable def stagePrice (L : ℕ) (b : BlockAtom Bk J L) : ℝ :=
  FS.pvar L b + ∑ i, FS.vprice L b i + ∑ i, FS.dprice L b i + GB.uprice L b

theorem mass_nonneg_of {X : Type} [Fintype X] {κ : SlotMeasure X} (h : IsNonneg κ) :
    0 ≤ mass κ :=
  h _ fun _ => zero_le_one

theorem stagePrice_nonneg (hsel : ∀ L b, 0 ≤ selectionFactor a p S₀ L b) (L : ℕ)
    (b : BlockAtom Bk J L) : 0 ≤ stagePrice FS GB L b := by
  unfold stagePrice TheoremCBlock.FirstStage.pvar TheoremCBlock.FirstStage.vprice
    TheoremCBlock.FirstStage.dprice TheoremCBlock.GramBracket.uprice
    sharpPrice
  have h1 : 0 ≤ ∑ i, |FS.ca L b i| * mass (FS.κa L b i) * selectionFactor a p S₀ L b :=
    sum_nonneg fun i _ => mul_nonneg (mul_nonneg (abs_nonneg _)
      (mass_nonneg_of (FS.κa_pos L b i).1)) (hsel L b)
  have h2 : 0 ≤ ∑ i, (mass (FS.κ L b i) + mass (FS.κ' L b i)) * selectionFactor a p S₀ L b :=
    sum_nonneg fun i _ => mul_nonneg (add_nonneg (mass_nonneg_of (FS.κ_pos L b i).1)
      (mass_nonneg_of (FS.κ'_pos L b i).1)) (hsel L b)
  have h3 : 0 ≤ ∑ i, mass (FS.κ L b i) * FS.dconst L b i * selectionFactor a p S₀ L b :=
    sum_nonneg fun i _ => mul_nonneg (mul_nonneg (mass_nonneg_of (FS.κ_pos L b i).1)
      (FS.dconst_nonneg L b i)) (hsel L b)
  have h4 : 0 ≤ ∑ i, mass (GB.κu L b i) * selectionFactor a p S₀ L b :=
    sum_nonneg fun i _ => mul_nonneg (mass_nonneg_of (GB.κu_pos L b i).1) (hsel L b)
  linarith

/-- `∑_𝔟 v_𝔟 ≤ ∑_j v_j`: the variation prices summed over the tags. -/
theorem sum_vprice_le (L : ℕ) : ∑ b, ∑ i, FS.vprice L b i ≤ ∑ j, FS.vT j := by
  have h : ∀ b, ∑ i, FS.vprice L b i =
      ∑ j, ∑ i, (if FS.tag L b i = j then FS.vprice L b i else 0) := fun b => by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_ite_eq]
    simp
  simp only [h]
  rw [sum_comm]
  exact sum_le_sum fun j _ => FS.vT_total L j

/-- `∑_𝔟 d_𝔟 ≤ ∑_j d_j`: the sharp prices summed over the tags. -/
theorem sum_dprice_le (L : ℕ) : ∑ b, ∑ i, FS.dprice L b i ≤ ∑ j, FS.dT j := by
  have h : ∀ b, ∑ i, FS.dprice L b i =
      ∑ j, ∑ i, (if FS.tag L b i = j then FS.dprice L b i else 0) := fun b => by
    rw [sum_comm]
    apply sum_congr rfl
    intro i _
    rw [sum_ite_eq]
    simp
  simp only [h]
  rw [sum_comm]
  exact sum_le_sum fun j _ => FS.dT_total L j

/-- `∑_𝔟 (p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟) ≤ P + ∑_j (v_j + d_j) + U₀`. -/
theorem sum_stagePrice_le (L : ℕ) :
    ∑ b, stagePrice FS GB L b ≤ FS.P + ∑ j, (FS.vT j + FS.dT j) + GB.U₀ := by
  unfold stagePrice
  simp only [sum_add_distrib]
  have h1 := FS.P_total L
  have h2 := sum_vprice_le (FS := FS) L
  have h3 := sum_dprice_le (FS := FS) L
  have h4 := GB.U₀_total L
  unfold TheoremCBlock.FirstStage.pvar
  unfold TheoremCBlock.GramBracket.uprice
  linarith

/-- **The first-stage and bracket part of (CP8)(c)**: if `p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟` vanishes at the
tail atoms, its weighted sum is at most `W_pre (P + ∑_j (v_j + d_j) + U₀)` at every scale. -/
theorem stage_weighted_le (hsel : ∀ L b, 0 ≤ selectionFactor a p S₀ L b)
    (htail : ∀ L (j : J L), stagePrice FS GB L (.inr j) = 0) (L : ℕ) :
    ∑ b, oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) * stagePrice FS GB L b ≤
      prefixWeight blk p pp ep (J := J) * (FS.P + ∑ j, (FS.vT j + FS.dT j) + GB.U₀) := by
  have hsplit : ∀ g : BlockAtom Bk J L → ℝ, (∀ j, g (.inr j) = 0) →
      ∑ b, g b = ∑ β, g (.inl β) := fun g hg => by
    rw [Fintype.sum_sum_type]
    simp [hg]
  rw [hsplit _ fun j => by rw [htail L j, mul_zero]]
  calc ∑ β, oneWeight blk p pp ep L (.inl β : BlockAtom Bk J L) ^ ((1 : ℝ) / 4) *
        stagePrice FS GB L (.inl β)
      ≤ ∑ β, prefixWeight blk p pp ep (J := J) * stagePrice FS GB L (.inl β) :=
        sum_le_sum fun β _ => mul_le_mul_of_nonneg_right (weight_inl_le L β)
          (stagePrice_nonneg hsel L _)
    _ = prefixWeight blk p pp ep (J := J) * ∑ b, stagePrice FS GB L b := by
        rw [← mul_sum, hsplit _ (htail L)]
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_stagePrice_le L) prefixWeight_nonneg

/-! ## The comparison and envelope part -/

namespace EnvelopeRefinement

variable (F : EnvelopeRefinement GB CL)

/-- The price of the added left diagonals of an atom, `K_{L,𝔟} = ∑_i kL_i κK_i(1) q^{2a}`. -/
noncomputable def KpriceL (L : ℕ) (b : BlockAtom Bk J L) : ℝ :=
  ∑ i, F.kL L b i * mass (F.κK L b i) * selectionFactor a p S₀ L b

/-- The price of the added right diagonals of an atom, `K_{R,𝔟}`. -/
noncomputable def KpriceR (L : ℕ) (b : BlockAtom Bk J L) : ℝ :=
  ∑ i, F.kR L b i * mass (F.κK L b i) * selectionFactor a p S₀ L b

theorem otherPrice_le (hsel : ∀ L b, 0 ≤ selectionFactor a p S₀ L b) (L : ℕ)
    (b : BlockAtom Bk J L) :
    F.otherPrice L b ≤ symTotal (CL.π L) b + skewTotal (CL.π L) b := by
  have h2 : symTotal (CL.π L) b + skewTotal (CL.π L) b =
      ∑ t, (CL.π L b t .sym + CL.π L b t .skew) := by
    unfold symTotal skewTotal
    rw [sum_add_distrib]
  rw [h2]
  apply sum_le_sum
  intro t _
  have h0 : 0 ≤ CL.π L b t .sym + CL.π L b t .skew :=
    add_nonneg (mul_nonneg (CL.πt_nonneg L b t _) (hsel L b))
      (mul_nonneg (CL.πt_nonneg L b t _) (hsel L b))
  split_ifs
  · exact h0
  · exact le_refl _

/-- `T_{L,𝔟} ≤ K_{L,𝔟} + s_𝔟 + a_𝔟`. -/
theorem priceL_le (hsel : ∀ L b, 0 ≤ selectionFactor a p S₀ L b) (L : ℕ) (b : BlockAtom Bk J L) :
    F.priceL L b ≤ F.KpriceL L b + (symTotal (CL.π L) b + skewTotal (CL.π L) b) := by
  unfold priceL KpriceL
  linarith [F.otherPrice_le hsel L b]

/-- `T_{R,𝔟} ≤ K_{R,𝔟} + s_𝔟 + a_𝔟`. -/
theorem priceR_le (hsel : ∀ L b, 0 ≤ selectionFactor a p S₀ L b) (L : ℕ) (b : BlockAtom Bk J L) :
    F.priceR L b ≤ F.KpriceR L b + (symTotal (CL.π L) b + skewTotal (CL.π L) b) := by
  unfold priceR KpriceR
  linarith [F.otherPrice_le hsel L b]

end EnvelopeRefinement

variable (pp ep) in
/-- **The input of (CP8)(c) for a refinement** (`def:cp8`(c)): uniformly in the scale,
* `σ_CL` bounds `∑_𝔟 q_𝔟^{1/4}(s_𝔟 + a_𝔟)`, the weighted (CP4) prices of the comparison law;
* `σ_K` bounds `∑_𝔟 q_𝔟^{1/4}(K_{L,𝔟} + K_{R,𝔟})`, the weighted prices of the added diagonals.
**Used as hypotheses.** -/
structure SummabilityInputs (F : EnvelopeRefinement GB CL) where
  σCL : ℝ
  hCL : ∀ L, ∑ b, oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
    (symTotal (CL.π L) b + skewTotal (CL.π L) b) ≤ σCL
  σK : ℝ
  hK : ∀ L, ∑ b, oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
    (F.KpriceL L b + F.KpriceR L b) ≤ σK

/-- **(CP8)(c) for the envelopes of a refinement** (`def:cp8`(c)): from the vanishing of the
first-stage and bracket prices at the tail atoms, the positivity of the selection factors and
`SummabilityInputs`, with the bound `W_pre (P + ∑_j (v_j + d_j) + U₀) + 3 σ_CL + σ_K`. -/
noncomputable def summabilityOf (F : EnvelopeRefinement GB CL) (T : ℝ)
    (hL : ∀ L, ∑ b, F.priceL L b ≤ T) (hR : ∀ L, ∑ b, F.priceR L b ≤ T)
    (hsel : ∀ L b, 0 ≤ selectionFactor a p S₀ L b)
    (htail : ∀ L (j : J L), stagePrice FS GB L (.inr j) = 0)
    (SI : SummabilityInputs pp ep F) : Summability a m₀ blk p (F.toME a T hL hR) where
  bound := prefixWeight blk p pp ep (J := J) * (FS.P + ∑ j, (FS.vT j + FS.dT j) + GB.U₀) +
    3 * SI.σCL + SI.σK
  summable L := by
    have hst := stage_weighted_le (pp := pp) (ep := ep) hsel htail L
    have hCL := SI.hCL L
    have hK := SI.hK L
    have hpt : ∀ b, oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
        (FS.pvar L b + ∑ i, FS.vprice L b i + ∑ i, FS.dprice L b i + GB.uprice L b +
          symTotal (CL.π L) b + skewTotal (CL.π L) b +
          ∑ i, (F.toME a T hL hR).cL L b i * mass ((F.toME a T hL hR).κL L b i) *
            selectionFactor a p S₀ L b +
          ∑ i, (F.toME a T hL hR).cR L b i * mass ((F.toME a T hL hR).κR L b i) *
            selectionFactor a p S₀ L b) ≤
        oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) * stagePrice FS GB L b +
          (3 * (oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
            (symTotal (CL.π L) b + skewTotal (CL.π L) b)) +
          oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) * (F.KpriceL L b + F.KpriceR L b)) := by
      intro b
      have e1 : ∑ i, (F.toME a T hL hR).cL L b i * mass ((F.toME a T hL hR).κL L b i) *
          selectionFactor a p S₀ L b = F.priceL L b := F.sum_cL_eq L b
      have e2 : ∑ i, (F.toME a T hL hR).cR L b i * mass ((F.toME a T hL hR).κR L b i) *
          selectionFactor a p S₀ L b = F.priceR L b := F.sum_cR_eq L b
      rw [e1, e2]
      have hw : 0 ≤ oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) := weight_nonneg L b
      have hl := F.priceL_le hsel L b
      have hr := F.priceR_le hsel L b
      unfold stagePrice
      have key : FS.pvar L b + ∑ i, FS.vprice L b i + ∑ i, FS.dprice L b i + GB.uprice L b +
          symTotal (CL.π L) b + skewTotal (CL.π L) b + F.priceL L b + F.priceR L b ≤
          (FS.pvar L b + ∑ i, FS.vprice L b i + ∑ i, FS.dprice L b i + GB.uprice L b) +
            (3 * (symTotal (CL.π L) b + skewTotal (CL.π L) b) +
              (F.KpriceL L b + F.KpriceR L b)) := by linarith
      have := mul_le_mul_of_nonneg_left key hw
      linarith
    calc _ ≤ ∑ b, (oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) * stagePrice FS GB L b +
          (3 * (oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
            (symTotal (CL.π L) b + skewTotal (CL.π L) b)) +
          oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) * (F.KpriceL L b + F.KpriceR L b))) :=
          sum_le_sum fun b _ => hpt b
      _ ≤ _ := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum]
        linarith

end Sarkozy.EnvelopesPaper

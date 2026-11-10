module

public import Sarkozy.BracketEnergy.EnvFirst
public import Sarkozy.EnvelopeInputs.AtomFolded

@[expose] public section

/-!
# The selected norms and `sq(D_E)^a` against the prices of the bundles

The chain bound of `EnvFirst` carries `∏_{𝔟 ∈ E} ‖Λ_𝔟‖ · sq(D_E)^a` (with
`E = f ∪ g`); `hfirst` asks the prices `∏_{f} u_𝔟 ∏_{g} u'_𝔟` (`envPriceL/R`, `GB.uprice`), which
are masses times the selection factors `q_𝔟^{2a}` (`selPre β` at a block, `p^{2a}` at a tail
prime). This file compares them, given at each atom `sq(D_𝔟)^a ≤ q_𝔟^{2a}`
(`hsel`; for a tail prime `sq(p) = p²`, for a block of primes `sq(D_β) = D_β²`):

* `sum_abs_lawDensity_comb_le`: `‖∑_i c_i κ_i‖ ≤ ∑_i c_i κ_i(1)` for `c ≥ 0`, `κ_i ≥ 0`;
* `envIncL_price_le`, `envIncR_price_le`, `recLaw_price_le`: `‖Q_𝔟‖ sq(D_𝔟)^a ≤ u_𝔟`;
* **`termPrice_le`**: `∏_{E} ‖Λ_𝔟‖ · sq(D_E)^a ≤ ∏_{f} u_𝔟 ∏_{g} u'_𝔟` for a valid term
  (`g ⊥ f`), the moduli being pairwise coprime.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper Sarkozy.Structured Sarkozy.Functional
  Sarkozy.FourierArithmetic Sarkozy.PaperFrame Sarkozy.BlockFrame Sarkozy.TheoremC

/-- The total variation of a nonnegative combination of nonnegative measures is at most the
combination of the masses. -/
theorem sum_abs_lawDensity_comb_le {X : Type} [Fintype X] [DecidableEq X] {ι : Type}
    [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (κ : ι → SlotMeasure X)
    (hκ : ∀ i, IsNonneg (κ i)) :
    ∑ z : Slot → X, |lawDensity (∑ i, c i • κ i) z| ≤ ∑ i, c i * mass (κ i) := by
  have hpt : ∀ z, |lawDensity (∑ i, c i • κ i) z| ≤ ∑ i, c i * |lawDensity (κ i) z| := by
    intro z
    rw [RecordExpansion.lawDensity_sum]
    refine (abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    apply sum_congr rfl
    intro i _
    rw [RecordExpansion.lawDensity_smul, abs_mul, abs_of_nonneg (hc i)]
  calc ∑ z : Slot → X, |lawDensity (∑ i, c i • κ i) z|
      ≤ ∑ z : Slot → X, ∑ i, c i * |lawDensity (κ i) z| := sum_le_sum fun z _ => hpt z
    _ = ∑ i, c i * ∑ z : Slot → X, |lawDensity (κ i) z| := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => (mul_sum _ _ _).symm
    _ = ∑ i, c i * mass (κ i) := by
        exact sum_congr rfl fun i _ => by rw [sum_abs_lawDensity_eq_mass _ (hκ i)]

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- A combination price: `‖∑ c κ‖ s ≤ ∑ c κ(1) σ` for `0 ≤ s ≤ σ`. -/
theorem comb_price_le {X : Type} [Fintype X] [DecidableEq X] {ι : Type} [Fintype ι]
    (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) (κ : ι → SlotMeasure X) (hκ : ∀ i, IsNonneg (κ i))
    {s σ : ℝ} (hs : 0 ≤ s) (hsσ : s ≤ σ) :
    (∑ z : Slot → X, |lawDensity (∑ i, c i • κ i) z|) * s ≤ ∑ i, c i * mass (κ i) * σ := by
  have h1 := sum_abs_lawDensity_comb_le c hc κ hκ
  have hm : 0 ≤ ∑ i, c i * mass (κ i) :=
    sum_nonneg fun i _ => mul_nonneg (hc i) (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg
      (hκ i))
  calc (∑ z : Slot → X, |lawDensity (∑ i, c i • κ i) z|) * s
      ≤ (∑ i, c i * mass (κ i)) * σ :=
        mul_le_mul h1 hsσ hs hm
    _ = ∑ i, c i * mass (κ i) * σ := sum_mul _ _ _

omit [DecidableEq P] in
/-- `‖Q_{L,𝔟}‖ sq(D_𝔟)^a ≤ u_{L,𝔟}`. -/
theorem envIncL_price_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {s : ℝ} (hs : 0 ≤ s)
    (hsel : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) :
    (∑ z, |lawDensity (TheoremCBlock.Structured.envIncL D L b) z|) * s ≤
      TheoremCBlock.Structured.envPriceL D L b :=
  comb_price_le _ (D.ME.cL_nonneg L b) _ (fun i => (D.ME.κL_pos L b i).1) hs hsel

omit [DecidableEq P] in
/-- `‖Q_{R,𝔟}‖ sq(D_𝔟)^a ≤ u_{R,𝔟}`. -/
theorem envIncR_price_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {s : ℝ} (hs : 0 ≤ s)
    (hsel : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) :
    (∑ z, |lawDensity (TheoremCBlock.Structured.envIncR D L b) z|) * s ≤
      TheoremCBlock.Structured.envPriceR D L b :=
  comb_price_le _ (D.ME.cR_nonneg L b) _ (fun i => (D.ME.κR_pos L b i).1) hs hsel

omit [DecidableEq P] in
/-- `‖Ñ_{0,𝔟} − μ_𝔟‖ sq(D_𝔟)^a ≤ u'_𝔟` (the reserved records). -/
theorem recLaw_price_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {s : ℝ} (hs : 0 ≤ s)
    (hsel : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) :
    (∑ z, |lawDensity (recLaw D L b) z|) * s ≤ D.GB.uprice L b := by
  have h := comb_price_le (fun _ => (1 : ℝ)) (fun _ => zero_le_one) (D.GB.κu L b)
    (fun i => (D.GB.κu_pos L b i).1) hs hsel
  simp only [one_smul, one_mul] at h
  exact h

omit [DecidableEq P] in
/-- **The selected norms and `sq(D_E)^a` against the prices**: for a valid term `g ⊥ f` and
increments `Q` with `‖Q_𝔟‖ sq(D_𝔟)^a ≤ u_𝔟` and the reserved records likewise,
`∏_{E} ‖Λ_𝔟‖ · sq(D_E)^a ≤ ∏_{f} u_𝔟 ∏_{g} u'_𝔟`, `E = f ∪ g`. -/
theorem termPrice_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) {c : ℝ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (uQ : BlockAtom Bk J L → ℝ)
    (f g : BlockAtom Bk J L → Bool) (hg : g ∈ validChoices f)
    (hQ : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ c ≤ uQ b)
    (hR : ∀ b, (∑ z, |lawDensity (recLaw D L b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ c ≤ D.GB.uprice L b) :
    (∏ b : {b // b ∈ termSet f g}, ∑ x : Slot → BlockLabel m₀ blk p L b.1,
        |lawDensity (termLaw D L Qb f g b.1) x|) *
      ((stepR (crtModuli m₀ blk p L) (termSet f g) 1 : ℕ) : ℝ) ^ c ≤
      (∏ b, if f b then uQ b else 1) * ∏ b, (if g b then D.GB.uprice L b else 1) := by
  unfold validChoices at hg
  simp only [mem_filter, mem_univ, true_and] at hg
  rw [stepR_rpow_eq_prod_coprime _ (crtModuli_pairwise blk hpair),
    ← prod_coe_sort (termSet f g), ← prod_mul_distrib]
  -- the price of an atom of the term
  set π : BlockAtom Bk J L → ℝ := fun b => if f b then uQ b else D.GB.uprice L b
  have hle : ∀ b : {b // b ∈ termSet f g},
      (∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (termLaw D L Qb f g b.1) x|) *
        ((leastSquare (crtModuli m₀ blk p L b.1) : ℕ) : ℝ) ^ c ≤ π b.1 := by
    intro b
    have hb := b.2
    unfold termSet at hb
    simp only [mem_filter, mem_univ, true_and] at hb
    unfold termLaw π
    cases hf : f b.1
    · have hgb : g b.1 = true := by
        rcases hb with h1 | h1
        · rw [hf] at h1; exact absurd h1 (by simp)
        · exact h1
      simp only [hgb, Bool.false_eq_true, ↓reduceIte]
      exact hR b.1
    · simp only [↓reduceIte]
      exact hQ b.1
  have hnn : ∀ b : {b // b ∈ termSet f g}, 0 ≤
      (∑ x : Slot → BlockLabel m₀ blk p L b.1, |lawDensity (termLaw D L Qb f g b.1) x|) *
        ((leastSquare (crtModuli m₀ blk p L b.1) : ℕ) : ℝ) ^ c :=
    fun b => mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  refine (Finset.prod_le_prod₀ (fun b _ => hnn b) (fun b _ => hle b)).trans (le_of_eq ?_)
  rw [prod_coe_sort (termSet f g) π, ← prod_mul_distrib]
  unfold termSet
  rw [prod_filter]
  apply prod_congr rfl
  intro b _
  unfold π
  cases hf : f b <;> cases hgb : g b <;> simp
  exact absurd (hg b hgb) (by simp [hf])

end Sarkozy.BracketEnergy

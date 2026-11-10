module

public import Sarkozy.DensityChain2.Factorization

@[expose] public section

/-!
# Per-atom inputs of the density chain: `hatom` and `_hselF`

* **`hatom_of_atoms`**: the per-term moment input `hatom` of DC1's `_hterms` (unit mixed
  `L^q` of `|Λ_𝔟|/‖Λ_𝔟‖` for every selected atom `𝔟 ∈ f ∪ g` of a term `(f, g)`) follows from the
  same bound for the two per-atom laws that a term can select: the increment `Q_𝔟` (on `f`) and the
  reserved records `Ñ_{0,𝔟} − μ_𝔟 = ∑_i κu_{𝔟,i}` (on `g`). So `hatom` is term-independent: it is
  `lem:density:packets` for these laws.
* `mixedLpBound_mono`: unit mixed `L^q` gives unit mixed `L^{q'}` for `q ≤ q'` ("a smaller `θ`
  follows by monotonicity of the norms", proof of `lem:density:packets`).
* `mixedLpBound_uniform`: the uniform law on `Slot → X` has unit mixed `L^q` for every `q ≥ 1`
  (a witness that the per-atom hypotheses at `q = 72/ϑ < 72` are satisfiable).
* **`hselF_of_parity`**: DC1's `_hselF`, `sq(D_𝔟)^a ≤ sel_𝔟`, from the parity condition and
  `blockSel ≤ selPre` (equality for the paper's `paperSel`, `paperSelAt`).
-/

namespace Sarkozy.DensityChain2

open Filter Finset Function
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.BlockAnchor

/-- The moment bound of a variation law depends only on the density. -/
theorem mixedLp_variationLaw_congr {X : Type} [Fintype X] [Nonempty X] {ρ ρ' : (Slot → X) → ℝ}
    (e : ρ = ρ') (hb : 0 < totalVariation ρ) (hb' : 0 < totalVariation ρ') {q C : ℝ} :
    MixedLpBound (variationLaw ρ hb) q C ↔ MixedLpBound (variationLaw ρ' hb') q C := by
  subst e
  rfl

/-- **Norm monotonicity** of the mixed moments: unit mixed `L^q` gives unit mixed `L^{q'}`,
`0 < q ≤ q'`. -/
theorem mixedLpBound_mono {V X : Type} [Fintype V] [DecidableEq V] [Fintype X] [Nonempty X]
    {μ : FiniteLaw (V → X)} {q q' C : ℝ} (hq : 0 < q) (hqq : q ≤ q') (hC : 0 ≤ C)
    (h : MixedLpBound μ q C) : MixedLpBound μ q' C := by
  intro f
  refine (h f).trans (mul_le_mul_of_nonneg_left ?_ hC)
  exact prod_le_prod₀ (fun v _ => FiniteLaw.lpNorm_nonneg _ _ _)
    (fun v _ => FiniteLaw.lpNorm_mono _ hq hqq (f v))

/-- The uniform law on `Slot → X` (independent uniform slots) has unit mixed `L^q`, `q ≥ 1`. -/
theorem mixedLpBound_uniform {X : Type} [Fintype X] [Nonempty X] {q : ℝ} (hq : 1 ≤ q) :
    MixedLpBound (FiniteLaw.uniform (Slot → X)) q 1 := by
  intro f
  rw [Functional.expect_uniform_pi_prod (Ωe := fun _ : Slot => X) f, one_mul, abs_prod]
  exact prod_le_prod₀ (fun v _ => abs_nonneg _)
    (fun v _ => FiniteLaw.abs_expect_le_lpNorm _ hq (f v))


variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`hatom` from per-atom bounds** (`lem:density:packets`): if the increments `Q_𝔟` and the
reserved records `Ñ_{0,𝔟} − μ_𝔟` have unit mixed `L^q` (normalized by their variation), then so
does the selected law of every atom of every term `(f, g)`. -/
theorem hatom_of_atoms (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) {q : ℝ}
    (hQ : ∀ b, ∀ hb : 0 < totalVariation (lawDensity (Qb b)),
      MixedLpBound (variationLaw _ hb) q 1)
    (hR : ∀ b, ∀ hb : 0 < totalVariation (lawDensity (recLaw D L b)),
      MixedLpBound (variationLaw _ hb) q 1)
    (f g : BlockAtom Bk J L → Bool) :
    ∀ b ∈ termSet f g,
      ∀ hb : 0 < totalVariation (lawDensity (BracketEnergy.termLaw D L Qb f g b)),
      MixedLpBound (variationLaw _ hb) q 1 := by
  intro b hb hb'
  by_cases hf : f b = true
  · have e : BracketEnergy.termLaw D L Qb f g b = Qb b := by
      simp [BracketEnergy.termLaw, hf]
    have hb2 : 0 < totalVariation (lawDensity (Qb b)) := e ▸ hb'
    exact (mixedLp_variationLaw_congr (congrArg lawDensity e) hb' hb2).mpr (hQ b hb2)
  · have hg : g b = true := by
      unfold termSet at hb
      rw [mem_filter] at hb
      rcases hb.2 with h1 | h1
      · exact absurd h1 hf
      · exact h1
    have e : BracketEnergy.termLaw D L Qb f g b = recLaw D L b := by
      simp [BracketEnergy.termLaw, hf, hg]
    have hb2 : 0 < totalVariation (lawDensity (recLaw D L b)) := e ▸ hb'
    exact (mixedLp_variationLaw_congr (congrArg lawDensity e) hb' hb2).mpr (hR b hb2)

omit [DecidableEq P] in
/-- **DC1's `_hselF` from the parity condition**: `sq(D_𝔟)^a ≤ sel_𝔟` at every atom, if
`e_p ∈ {1} ∪ 2ℕ` and the prefix selection factors are at least the paper's `def:price` values
`blockSel a pp ep blk β` (with equality for `BlockAnchor.paperSel`, `MainTarget.paperSelAt`).
At a tail prime it is the equality `sq(p)^a = p^{2a}`. -/
theorem hselF_of_parity (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (hpar : ParityCondition D.S.ep)
    (hsel : ∀ β, blockSel a D.S.pp D.S.ep blk β ≤ D.S.selPre β) (L : ℕ)
    (b : BlockAtom Bk J L) :
    ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b := by
  cases b with
  | inl β =>
    change ((leastSquare (blockModulus m₀ blk β) : ℕ) : ℝ) ^ a ≤ D.S.selPre β
    rw [leastSquare_rpow_eq_blockSel D.S.m₀_eq D.S.pp_prime hpar h0]
    exact hsel β
  | inr j =>
    change ((leastSquare (p L j) : ℕ) : ℝ) ^ a ≤ ((p L j : ℕ) : ℝ) ^ (2 * a)
    rw [leastSquare_prime (D.S.p_prime L j), Nat.cast_pow, ← Real.rpow_natCast,
      ← Real.rpow_mul (Nat.cast_nonneg _)]
    norm_num


omit [DecidableEq P] in
/-- **The wrapping price row of `fixC`**: `‖wrapInc_𝔟‖ s ≤ wrapPrice_𝔟` for `0 ≤ s ≤ sel_𝔟`
(`wrapInc = ∑_t (π̃^s D^s + π̃^a D^a)` with probability components, `wrapPrice = ∑_t (π^s + π^a)`,
`π = π̃ sel`). -/
theorem wrapInc_price_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (b : BlockAtom Bk J L) {s : ℝ} (hs : 0 ≤ s)
    (hsel : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) :
    (∑ z, |lawDensity (TheoremCBlock.Structured.wrapInc D L b) z|) * s ≤
      TheoremCBlock.Structured.wrapPrice D L b := by
  have hw : TheoremCBlock.Structured.wrapInc D L b =
      ∑ i : D.CL.T L b ⊕ D.CL.T L b,
        (Sum.elim (fun t => D.CL.πt L b t .sym) (fun t => D.CL.πt L b t .skew) i) •
          (Sum.elim (fun t => D.CL.D L b t .sym) (fun t => D.CL.D L b t .skew) i) := by
    unfold TheoremCBlock.Structured.wrapInc
    rw [Fintype.sum_sum_type, ← sum_add_distrib]
    rfl
  rw [hw]
  refine (comb_price_le _ (fun i => by cases i <;> exact D.CL.πt_nonneg _ _ _ _) _
    (fun i => by cases i <;> exact (D.CL.D_prob _ _ _ _).1) hs hsel).trans (le_of_eq ?_)
  rw [Fintype.sum_sum_type]
  unfold TheoremCBlock.Structured.wrapPrice TheoremCBlock.ComparisonLaw.π
  simp only [Sum.elim_inl, Sum.elim_inr, (D.CL.D_prob _ _ _ _).2, mul_one]
  rw [← sum_add_distrib]

omit [DecidableEq P] in
/-- **The wrapping price total**: `∑_𝔟 wrapPrice_𝔟 ≤ S + A` (`CL.S_total`, `CL.A_total`). -/
theorem wrapPrice_total (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    ∑ b, TheoremCBlock.Structured.wrapPrice D L b ≤ D.CL.S + D.CL.A := by
  unfold TheoremCBlock.Structured.wrapPrice
  simp only [sum_add_distrib]
  exact add_le_add (D.CL.S_total L) (D.CL.A_total L)

end Sarkozy.DensityChain2

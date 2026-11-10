module

public import Sarkozy.BracketEnergy.Expansion
public import Sarkozy.EnvelopeEnergiesPaper.CRTBundles

@[expose] public section

/-!
# The bracket of (CP3) on the cyclic coordinates, and `lem:bracket-energy` for one term

For comparison data `D` on the block atoms, the bracket of (CP3) is
`Ñ_𝔟 = D.GB.N L 𝔟 = Ñ_{0,𝔟} + δ_{E,𝔟}` with `Ñ_{0,𝔟} − μ_𝔟 = ∑_i κu_{𝔟,i}` (positive
reserved-diagonal records, `GramBracket.N₀_sub`). This file:
* names the three parts `muLaw` (`μ_𝔟 = D.R.law`), `recLaw` (`∑_i κu_{𝔟,i}`) and `delLaw`
  (`δ_{E,𝔟} = ∑_i (κ'_{𝔟,i} − κ_{𝔟,i})`), with `N_eq : Ñ = μ + rec + δ` and `N₀_eq`;
* carries the selected laws `⊗_𝔟 (f ? Q : Ñ)` and their expansion terms to the cyclic coordinates
  (`crtLaws_bracket`, `crtLaws_bracket0`, `crtLaws_term`);
* **`bracket_term_le`** (`lem:bracket-energy`, its proof, for one selected positive measure
  `κ = ⊗_{𝔟 ∈ f} Q_𝔟` and any inputs `G`): from
  - the first bound for every term `⊗_{f} Q ⊗ ⊗_{g} rec ⊗ μ_{−f−g}` (outside law `μ`),
    `|E| ≤ (1 + z) K ∏_{𝔟 ∈ g} u_𝔟 + r_g` (`prop:record:density-structured` with the structured
    slot data `G`), and
  - the difference bound `|E_Ñ − E_{Ñ₀}| ≤ (R_err + z) K + r₂` (`lem:sharp-first` with
    `ρ = Ñ₀` on the first-stage atoms outside `f`),

  it gives `|E_Ñ| ≤ (B + e^{U₀} z + z) K + ∑_{g ⊥ f} r_g + r₂`, with `B = e^{U₀} + R_err` the
  bracket constant of `D` and `u_𝔟 = GB.uprice` (whose sum is at most `U₀`, (CP3)).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.BlockFrame Sarkozy.TheoremCBlock
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The reference `μ_𝔟` of the atom. -/
noncomputable def muLaw (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    AtomMeasure m₀ blk p L b :=
  D.R.law p L b

/-- The reserved records `Ñ_{0,𝔟} − μ_𝔟 = ∑_i κu_{𝔟,i}` of (CP3). -/
noncomputable def recLaw (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    AtomMeasure m₀ blk p L b :=
  ∑ i, D.GB.κu L b i

/-- The first-stage differences `δ_{E,𝔟} = ∑_i (κ'_{𝔟,i} − κ_{𝔟,i})` of (CP2). -/
noncomputable def delLaw (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    AtomMeasure m₀ blk p L b :=
  ∑ i, (D.FS.κ' L b i - D.FS.κ L b i)

omit [DecidableEq P] in
/-- `Ñ_{0,𝔟} = μ_𝔟 + ∑_i κu_{𝔟,i}` (`def:cp3`). -/
theorem N₀_eq (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    D.GB.N₀ L b = muLaw D L b + recLaw D L b := by
  unfold muLaw recLaw
  rw [← D.GB.N₀_sub L b]
  abel

omit [DecidableEq P] in
/-- **The bracket expanded** (`lem:bracket-energy`, proof): `Ñ_𝔟 = μ_𝔟 + ∑_i κu_{𝔟,i} + δ_{E,𝔟}`. -/
theorem N_eq (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    D.GB.N L b = muLaw D L b + recLaw D L b + delLaw D L b := by
  unfold GramBracket.N delLaw
  rw [N₀_eq]

omit [DecidableEq P] in
/-- The price `u_𝔟` of the reserved records is nonnegative. -/
theorem uprice_nonneg (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) (b : BlockAtom Bk J L) :
    0 ≤ D.GB.uprice L b :=
  sum_nonneg fun i _ => mul_nonneg (ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
    (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
/-- `∑_𝔟 u_𝔟 ≤ U₀` (CP3). -/
theorem sum_uprice_le (D : ComparisonData a m₀ blk p pr h E) (L : ℕ) :
    ∑ b, D.GB.uprice L b ≤ D.GB.U₀ :=
  D.GB.U₀_total L

omit [DecidableEq P] in
/-- `0 ≤ R_err`. -/
theorem Rerr_nonneg (D : ComparisonData a m₀ blk p pr h E) : 0 ≤ D.GB.Rerr :=
  mul_nonneg (Real.exp_pos _).le (RecordExpansion.tagSeries_nonneg D.dT_nonneg D.vT_nonneg)

section CRT

variable (blk)

/-- The pull to the cyclic coordinates is additive. -/
theorem pullLaw_add {X X' : Type} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']
    (e : X' ≃ X) (M N : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) :
    pullLaw e (M + N) = pullLaw e M + pullLaw e N := by
  unfold pullLaw
  exact LinearMap.add_comp _ _ _

omit [DecidableEq P] in
/-- **The selected bracket on the cyclic coordinates**: `crtLaws (f ? Q : Ñ)` is
`f ? crt Q : crt μ + crt rec + crt δ`. -/
theorem crtLaws_bracket (D : ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (Qb : ∀ b, AtomMeasure m₀ blk p L b)
    (f : BlockAtom Bk J L → Bool) :
    crtLaws blk h0 L (fun b => if f b then Qb b else D.GB.N L b) =
      fun b => if f b then crtLaws blk h0 L Qb b else
        crtLaws blk h0 L (muLaw D L) b + crtLaws blk h0 L (recLaw D L) b +
          crtLaws blk h0 L (delLaw D L) b := by
  funext b
  unfold crtLaws
  cases hf : f b
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [N_eq, pullLaw_add, pullLaw_add]
  · simp only [hf, ↓reduceIte]

omit [DecidableEq P] in
/-- `crtLaws (f ? Q : Ñ₀) = f ? crt Q : crt μ + crt rec`. -/
theorem crtLaws_bracket0 (D : ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (Qb : ∀ b, AtomMeasure m₀ blk p L b)
    (f : BlockAtom Bk J L → Bool) :
    crtLaws blk h0 L (fun b => if f b then Qb b else D.GB.N₀ L b) =
      fun b => if f b then crtLaws blk h0 L Qb b else
        crtLaws blk h0 L (muLaw D L) b + crtLaws blk h0 L (recLaw D L) b := by
  funext b
  unfold crtLaws
  cases hf : f b
  · simp only [hf, Bool.false_eq_true, ↓reduceIte]
    rw [N₀_eq, pullLaw_add]
  · simp only [hf, ↓reduceIte]

omit [DecidableEq P] in
/-- The expansion terms on the cyclic coordinates. -/
theorem crtLaws_term (D : ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (Qb : ∀ b, AtomMeasure m₀ blk p L b)
    (f g : BlockAtom Bk J L → Bool) :
    crtLaws blk h0 L (fun b => if f b then Qb b else if g b then recLaw D L b else muLaw D L b) =
      fun b => if f b then crtLaws blk h0 L Qb b else
        if g b then crtLaws blk h0 L (recLaw D L) b else crtLaws blk h0 L (muLaw D L) b := by
  funext b
  unfold crtLaws
  cases hf : f b <;> cases hg : g b <;> simp only [hf, hg, Bool.false_eq_true, ↓reduceIte]

omit [DecidableEq P] in
/-- **`lem:bracket-energy` for one selected positive measure, with any inputs** (the proof of
the lemma, assembled): if every expansion term `⊗_{f} Q ⊗ ⊗_{g} rec ⊗ μ_{−f−g}` (`g ⊥ f`)
satisfies the first bound `|E| ≤ (1 + z) K ∏_{𝔟 ∈ g} u_𝔟 + r_g` and the difference satisfies
`|E_Ñ − E_{Ñ₀}| ≤ (R_err + z) K + r₂` (`lem:sharp-first`), then
`|E_Ñ| ≤ (B + (e^{U₀} z + z)) K + (∑_{g ⊥ f} r_g + r₂)`. -/
theorem bracket_term_le (D : ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (Qb : ∀ b, AtomMeasure m₀ blk p L b)
    (f : BlockAtom Bk J L → Bool) (G : Slot → ResidueSpace (crtModuli m₀ blk p L) → ℝ)
    {K z r₂ : ℝ} (hK : 0 ≤ K) (hz : 0 ≤ z) (r : (BlockAtom Bk J L → Bool) → ℝ)
    (hfirst : ∀ g ∈ validChoices f,
      |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else if g b then recLaw D L b else muLaw D L b)) G| ≤
        (1 + z) * K * ∏ b, (if g b then D.GB.uprice L b else 1) + r g)
    (hdiff : |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N L b)) G -
        multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
          if f b then Qb b else D.GB.N₀ L b)) G| ≤ (D.GB.Rerr + z) * K + r₂) :
    |multilinearIntegral (tensorLaw (crtLaws blk h0 L fun b =>
        if f b then Qb b else D.GB.N L b)) G| ≤
      (D.B + (Real.exp D.GB.U₀ * z + z)) * K + (∑ g ∈ validChoices f, r g + r₂) := by
  rw [crtLaws_bracket blk D L h0 Qb f, crtLaws_bracket0 blk D L h0 Qb f] at hdiff
  rw [crtLaws_bracket blk D L h0 Qb f]
  have hterm : ∀ g ∈ validChoices f,
      |multilinearIntegral (tensorLaw fun b => if f b then crtLaws blk h0 L Qb b else
          if g b then crtLaws blk h0 L (recLaw D L) b else crtLaws blk h0 L (muLaw D L) b) G| ≤
        (1 + z) * K * ∏ b, (if g b then D.GB.uprice L b else 1) + r g := by
    intro g hg
    rw [← crtLaws_term blk D L h0 Qb f g]
    exact hfirst g hg
  have h := abs_multilinear_bracket_le f (crtLaws blk h0 L Qb) (crtLaws blk h0 L (muLaw D L))
    (crtLaws blk h0 L (recLaw D L)) (crtLaws blk h0 L (delLaw D L)) G (D.GB.uprice L)
    (uprice_nonneg D L) (sum_uprice_le D L) (mul_nonneg (by linarith) hK) r hterm hdiff
  have hB : D.B = Real.exp D.GB.U₀ + D.GB.Rerr := rfl
  rw [hB]
  calc _ ≤ _ := h
    _ = _ := by ring

end CRT

end Sarkozy.BracketEnergy

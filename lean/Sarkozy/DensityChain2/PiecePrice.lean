module

public import Sarkozy.DensityChain2.Price

@[expose] public section

/-!
# The prices of DC2's folded pieces (`lem:record:folded-energy`(e), `def:price`)

For the per-piece main price of DC2's `hfold`, the selected norms of a folded piece must be
dominated by its piece price: `‖Λ_𝔟‖ sq(D_𝔟)^a ≤ bpieceG_𝔟 · (u_𝔟 if 𝔟 ∈ f)`.

* `mass_diagonalLaw_halfMarginalPlus/Minus`: the folded law `Diag(m_±(κ))` has the mass of `κ`;
* `mass_bpieceLp`, `mass_bpieceLm`: the masses of DC2's folded pieces (`κu`, the whole difference
  with its full folded law, the positive parts, `Q`);
* **`bpieceLp_price_le`**, `bpieceLm_price_le`: the per-atom price inequality at every admissible
  non-`μ` piece, from `sq(D_𝔟)^a ≤ sel_𝔟` (`hselF_of_parity`) and DC1/B9's increment prices.
-/

namespace Sarkozy.DensityChain2

open Finset
open scoped BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.BlockFrame Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.EnvelopeInputsBlock

section Mass

variable {X : Type} [Fintype X] [DecidableEq X]

/-- `∑_x m_+(κ)(x) = κ(1)`. -/
theorem sum_halfMarginalPlus (c : ReflectionCut Slot) (κ : SlotMeasure X) :
    ∑ x, halfMarginalPlus c κ x = mass κ := by
  unfold halfMarginalPlus mass
  rw [← map_sum]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp

/-- `∑_x m_-(κ)(x) = κ(1)`. -/
theorem sum_halfMarginalMinus (c : ReflectionCut Slot) (κ : SlotMeasure X) :
    ∑ x, halfMarginalMinus c κ x = mass κ := by
  unfold halfMarginalMinus mass
  rw [← map_sum]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp

omit [DecidableEq X] in
/-- The mass of a diagonal law is the mass of its half law. -/
theorem mass_diagonalLaw (c : ReflectionCut Slot) (m : (c.Half → X) → ℝ) :
    mass (c.diagonalLaw m) = ∑ x, m x := by
  change (∑ x, m x * 1) = _
  simp

end Mass

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **The price of a plus folded piece** (`lem:record:folded-energy`(e), `def:price`): at every
admissible non-`μ` piece `x` of an atom (`hpieceCoef ≠ 0`),
`‖bpieceLp_𝔟(x)‖ s ≤ bpieceG_𝔟(x) · (u_𝔟 if 𝔟 ∈ f, else 1)` for `s ≤ sel_𝔟`, given
`‖Q_𝔟‖ s ≤ u_𝔟`. -/
theorem bpieceLp_price_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) (x : DensityFibre.HPiece D L b)
    (hcoef : DensityFibre.hpieceCoef D L f σ j b x ≠ 0)
    (hx : DensityFibre.hpieceIsMu D L b x = false) {s : ℝ}
    (hsel : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) (uQ : ℝ)
    (hQp : (∑ z, |lawDensity (Qb b) z|) * s ≤ uQ) :
    (∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b x) z|) * s ≤
      DensityFibre.bpieceG D L b x * (if f b then uQ else 1) := by
  rw [sum_abs_lawDensity_eq_mass _ (DensityFibre.bpieceLp_positiveRecord D L Qb dec hQ j b x hx).1]
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [DensityFibre.hpieceIsMu] at hx
  · have hf : f b = false := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2
    simp only [DensityFibre.bpieceLp, DensityFibre.bpieceG, hf, Bool.false_eq_true, ↓reduceIte,
      mul_one, mass_diagonalLaw, sum_halfMarginalPlus]
    exact mul_le_mul_of_nonneg_left hsel
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1)
  · have hf : f b = false := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2.2
    have hm : mass (DensityFibre.bpieceLp D L Qb dec j b (.inr (.inl (i, none)))) =
        mass (D.FS.κ L b i) := by
      simp only [DensityFibre.bpieceLp]
      unfold mass
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
      have h1 : ∀ s', ((D.FS.cut j).diagonalLaw (halfMarginalPlus (D.FS.cut j) ((dec b i).κs s')))
          (fun _ => 1) = 1 := by
        intro s'
        have := mass_diagonalLaw (D.FS.cut j) (halfMarginalPlus (D.FS.cut j) ((dec b i).κs s'))
        unfold mass at this
        rw [this, sum_halfMarginalPlus]
        exact ((dec b i).prob s').2
      simp only [h1, mul_one, (dec b i).π.total]
    rw [hm]
    simp only [DensityFibre.bpieceG, hf, Bool.false_eq_true, ↓reduceIte, mul_one]
    exact mul_le_mul_of_nonneg_left hsel
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · have hf : f b = false := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2.2
    simp only [DensityFibre.bpieceLp, DensityFibre.bpieceG, hf, Bool.false_eq_true, ↓reduceIte,
      mul_one, mass_diagonalLaw, sum_halfMarginalPlus]
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hsel
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
    · simp only [↓reduceIte]
      exact mul_le_mul_of_nonneg_left hsel
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
  · have hf : f b = true := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2
    simp only [DensityFibre.bpieceLp, DensityFibre.bpieceG, hf, ↓reduceIte, one_mul,
      mass_diagonalLaw, sum_halfMarginalPlus]
    rw [← sum_abs_lawDensity_eq_mass _ (hQ b).1]
    exact hQp


omit [DecidableEq P] in
/-- **The price of a minus folded piece** (`lem:record:folded-energy`(e), `def:price`): at every
admissible non-`μ` piece `x` of an atom (`hpieceCoef ≠ 0`),
`‖bpieceLm_𝔟(x)‖ s ≤ bpieceG_𝔟(x) · (u_𝔟 if 𝔟 ∈ f, else 1)` for `s ≤ sel_𝔟`, given
`‖Q_𝔟‖ s ≤ u_𝔟`. -/
theorem bpieceLm_price_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b : BlockAtom Bk J L) (x : DensityFibre.HPiece D L b)
    (hcoef : DensityFibre.hpieceCoef D L f σ j b x ≠ 0)
    (hx : DensityFibre.hpieceIsMu D L b x = false) {s : ℝ}
    (hsel : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) (uQ : ℝ)
    (hQp : (∑ z, |lawDensity (Qb b) z|) * s ≤ uQ) :
    (∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b x) z|) * s ≤
      DensityFibre.bpieceG D L b x * (if f b then uQ else 1) := by
  rw [sum_abs_lawDensity_eq_mass _ (DensityFibre.bpieceLm_positiveRecord D L Qb dec hQ j b x hx).1]
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [DensityFibre.hpieceIsMu] at hx
  · have hf : f b = false := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2
    simp only [DensityFibre.bpieceLm, DensityFibre.bpieceG, hf, Bool.false_eq_true, ↓reduceIte,
      mul_one, mass_diagonalLaw, sum_halfMarginalMinus]
    exact mul_le_mul_of_nonneg_left hsel
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1)
  · have hf : f b = false := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2.2
    have hm : mass (DensityFibre.bpieceLm D L Qb dec j b (.inr (.inl (i, none)))) =
        mass (D.FS.κ L b i) := by
      simp only [DensityFibre.bpieceLm]
      unfold mass
      simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
      have h1 : ∀ s', ((D.FS.cut j).diagonalLaw (halfMarginalMinus (D.FS.cut j) ((dec b i).κs s')))
          (fun _ => 1) = 1 := by
        intro s'
        have := mass_diagonalLaw (D.FS.cut j) (halfMarginalMinus (D.FS.cut j) ((dec b i).κs s'))
        unfold mass at this
        rw [this, sum_halfMarginalMinus]
        exact ((dec b i).prob s').2
      simp only [h1, mul_one, (dec b i).π.total]
    rw [hm]
    simp only [DensityFibre.bpieceG, hf, Bool.false_eq_true, ↓reduceIte, mul_one]
    exact mul_le_mul_of_nonneg_left hsel
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
  · have hf : f b = false := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2.2
    simp only [DensityFibre.bpieceLm, DensityFibre.bpieceG, hf, Bool.false_eq_true, ↓reduceIte,
      mul_one, mass_diagonalLaw, sum_halfMarginalMinus]
    cases t
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact mul_le_mul_of_nonneg_left hsel
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
    · simp only [↓reduceIte]
      exact mul_le_mul_of_nonneg_left hsel
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
  · have hf : f b = true := by
      simp only [DensityFibre.hpieceCoef, ne_eq, ite_eq_right_iff, not_forall] at hcoef
      exact hcoef.1.2
    simp only [DensityFibre.bpieceLm, DensityFibre.bpieceG, hf, ↓reduceIte, one_mul,
      mass_diagonalLaw, sum_halfMarginalMinus]
    rw [← sum_abs_lawDensity_eq_mass _ (hQ b).1]
    exact hQp


omit [DecidableEq P] in
/-- **The selected price of a plus folded piece** (`lem:record:folded-energy`(e), `def:price`):
for an admissible piece `φ` (`hpieceCoef ≠ 0` at every atom) with selected atoms
`E = hTermAtoms φ`, `∏_E ‖Λ_𝔟‖ · sq(D_E)^a ≤ ∏_𝔟 bpieceG_𝔟(φ_𝔟) · ∏_{f} u_𝔟`. With
`mainPrice_split` this makes the per-piece chain bound of `env_foldPlus_piece_paper` of the form
`(∏ bpieceG) M₊ + r₊(φ)` that DC2's `hfold` asks, with `M₊` independent of the piece. -/
theorem piecePrice_plus_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hsel : ∀ b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQp : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b) :
    (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
        ∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b.1 (φ b.1)) z|) *
      ((leastSquare (∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) * ∏ b, (if f b then uQ b else 1) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hsq : ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a =
      ∏ b ∈ Es, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a := by
    rw [leastSquare_prod_coprime (crtModuli m₀ blk p L) (crtModuli_pairwise blk hpair) Es,
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  rw [hsq, prod_coe_sort Es (fun b => ∑ z, |lawDensity (DensityFibre.bpieceLp D L Qb dec j b
    (φ b)) z|), ← prod_mul_distrib, ← prod_mul_distrib]
  have hG0 : ∀ b, 0 ≤ DensityFibre.bpieceG D L b (φ b) * (if f b then uQ b else 1) := by
    intro b
    refine mul_nonneg (DensityFibre.bpieceG_nonneg D L b (φ b)) ?_
    split_ifs
    · exact le_trans (mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hQp b)
    · exact zero_le_one
  have hout : ∀ b ∉ Es, DensityFibre.bpieceG D L b (φ b) * (if f b then uQ b else 1) = 1 := by
    intro b hb
    rw [hEs] at hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    have hc := hφ b
    revert hb hc
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb hc <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceG, DensityFibre.hpieceCoef]
  rw [← prod_mul_prod_compl Es (fun b => DensityFibre.bpieceG D L b (φ b) *
    (if f b then uQ b else 1))]
  rw [prod_congr rfl (fun b hb => hout b (mem_compl.mp hb)), prod_const_one, mul_one]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun b hb => ?_
  exact bpieceLp_price_le D L Qb hQ dec j f σ b (φ b) (hφ b) (mem_filter.mp hb).2 (hsel b)
    (uQ b) (hQp b)

omit [DecidableEq P] in
/-- **The selected price of a minus folded piece** (`lem:record:folded-energy`(e), `def:price`):
for an admissible piece `φ` (`hpieceCoef ≠ 0` at every atom) with selected atoms
`E = hTermAtoms φ`, `∏_E ‖Λ_𝔟‖ · sq(D_E)^a ≤ ∏_𝔟 bpieceG_𝔟(φ_𝔟) · ∏_{f} u_𝔟`. With
`mainPrice_split` this makes the per-piece chain bound of `env_foldMinus_piece_paper` of the form
`(∏ bpieceG) M₋ + r₋(φ)` that DC2's `hfold` asks, with `M₋` independent of the piece. -/
theorem piecePrice_minus_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (dec : DecFamily D L) (j : D.FS.Tag) (f : BlockAtom Bk J L → Bool)
    (σ : ∀ b, Option (D.FS.Ib L b)) (φ : ∀ b, DensityFibre.HPiece D L b)
    (hφ : ∀ b, DensityFibre.hpieceCoef D L f σ j b (φ b) ≠ 0)
    (hsel : ∀ b, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      TheoremCBlock.selectionFactor a p D.S.selPre L b)
    (uQ : BlockAtom Bk J L → ℝ)
    (hQp : ∀ b, (∑ z, |lawDensity (Qb b) z|) *
      ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤ uQ b) :
    (∏ b : {b // b ∈ DensityFibre.hTermAtoms D L φ},
        ∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b.1 (φ b.1)) z|) *
      ((leastSquare (∏ b ∈ DensityFibre.hTermAtoms D L φ, crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a ≤
      (∏ b, DensityFibre.bpieceG D L b (φ b)) * ∏ b, (if f b then uQ b else 1) := by
  set Es := DensityFibre.hTermAtoms D L φ with hEs
  have hsq : ((leastSquare (∏ b ∈ Es, crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a =
      ∏ b ∈ Es, ((leastSquare (crtModuli m₀ blk p L b) : ℕ) : ℝ) ^ a := by
    rw [leastSquare_prod_coprime (crtModuli m₀ blk p L) (crtModuli_pairwise blk hpair) Es,
      Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun _ _ => Nat.cast_nonneg _)]
  rw [hsq, prod_coe_sort Es (fun b => ∑ z, |lawDensity (DensityFibre.bpieceLm D L Qb dec j b
    (φ b)) z|), ← prod_mul_distrib, ← prod_mul_distrib]
  have hG0 : ∀ b, 0 ≤ DensityFibre.bpieceG D L b (φ b) * (if f b then uQ b else 1) := by
    intro b
    refine mul_nonneg (DensityFibre.bpieceG_nonneg D L b (φ b)) ?_
    split_ifs
    · exact le_trans (mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)) (hQp b)
    · exact zero_le_one
  have hout : ∀ b ∉ Es, DensityFibre.bpieceG D L b (φ b) * (if f b then uQ b else 1) = 1 := by
    intro b hb
    rw [hEs] at hb
    unfold DensityFibre.hTermAtoms at hb
    simp only [mem_filter, mem_univ, true_and, Bool.not_eq_false] at hb
    have hc := hφ b
    revert hb hc
    rcases φ b with (_ | k) | (⟨i, _ | t⟩ | _) <;> intro hb hc <;>
      simp_all [DensityFibre.hpieceIsMu, DensityFibre.bpieceG, DensityFibre.hpieceCoef]
  rw [← prod_mul_prod_compl Es (fun b => DensityFibre.bpieceG D L b (φ b) *
    (if f b then uQ b else 1))]
  rw [prod_congr rfl (fun b hb => hout b (mem_compl.mp hb)), prod_const_one, mul_one]
  refine prod_le_prod₀ (fun b _ => mul_nonneg (sum_nonneg fun _ _ => abs_nonneg _)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)) fun b hb => ?_
  exact bpieceLm_price_le D L Qb hQ dec j f σ b (φ b) (hφ b) (mem_filter.mp hb).2 (hsel b)
    (uQ b) (hQp b)

end Sarkozy.DensityChain2

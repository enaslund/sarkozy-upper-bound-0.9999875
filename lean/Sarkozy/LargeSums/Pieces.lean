module

public import Sarkozy.LargeSums.Holder
public import Sarkozy.SharpSums.Split
public import Sarkozy.DensityChain2.Hfold
public import Sarkozy.DensityChain2.Factorization
public import Sarkozy.DensityChain.Moduli

@[expose] public section

/-!
# The folded pieces: masses, positivity, the per-atom sums and the large pieces

LP (8 November 2026). The pieces `HPiece` of the baseline route of `lem:sharp-first`
(`DensityFibre.FoldedChoice`) at one atom, and what Rankin's trick (`lem:record:density-lp`) needs
of them:

* `pieceMass`: the mass of a folded piece (`1` for `μ`; the mass of the record otherwise), and
  **`mass_bpieceLp`**, **`mass_bpieceLm`**: both folded laws of a piece have this mass
  (`lem:record:folded-energy`(b) at the constant function);
* `isPositiveRecord_bpieceLp/Lm`: every folded piece, `μ` included, is a positive record;
* `coefAt`, `hpieceCoef_eq`: the coefficient of a piece depends on `(f, σ)` only through
  `(f 𝔟, σ 𝔟)`; **`sum_abs_coefAt_le`**: for each piece, `∑_{y, o} |c_{y,o}| ≤ 1` (a piece is
  used by at most one local choice);
* `qf`: `q_𝔟` at a non-`μ` piece, `1` at `μ`; **`sum_atom_le`**: the per-atom Rankin sum
  `∑_x D_x m_x qf_x^{1/4} = 1 + q_𝔟^{1/4} Pr_𝔟`, with `Pr_𝔟` the masses of the records at `𝔟`;
* **`large_of_not_small`** (`def:record:structured-energy`(a), DC1's `moduli_dichotomy` with
  DC2's factorization `D_𝔟 = q_𝔟 c_𝔟`): a piece that is not small has `N^τ < ∏_𝔟 qf_𝔟(φ_𝔟)`;
* **`sum_choices_rankin_le`**: Rankin over the large pieces, then the sums over the choices
  `(f, σ)`: `∑_f ∑_{σ ∈ S} ∑_{¬small φ} w_φ m(φ) ≤ T^{-1/4} ∏_𝔟 (1 + q_𝔟^{1/4} Pr_𝔟)`.
-/

namespace Sarkozy.LargeSums

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.DensityChain Sarkozy.DensityFibre
  Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
  Sarkozy.EnvelopeEnergiesPaper Sarkozy.DensityChain2 Sarkozy.Comparison ReflectionCut

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Pieces

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)

/-- The mass of a folded piece: `1` for `μ`, the mass of the record otherwise (`κ(1)` for a
whole difference `κ' − κ`, whose full folded law is `κ(1) ∑_s π_s Diag(m_±(κ_s))`). -/
noncomputable def pieceMass (b : BlockAtom Bk J L) : HPiece D L b → ℝ
  | .inl none => 1
  | .inl (some k) => mass (D.GB.κu L b k)
  | .inr (.inl (i, none)) => mass (D.FS.κ L b i)
  | .inr (.inl (i, some t)) => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)
  | .inr (.inr _) => mass (Qb b)

omit [DecidableEq P] in
theorem pieceMass_nonneg (hQ : ∀ b, IsPositiveRecord (Qb b)) (b : BlockAtom Bk J L)
    (x : HPiece D L b) : 0 ≤ pieceMass D L Qb b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b k).1
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (hQ b).1

/-- A slot (`Slot` is nonempty). -/
def slot0 : Slot := (0, 0, 0)

omit [DecidableEq P] in
/-- The reference law of an atom has mass `1`. -/
theorem mass_refLaw (b : BlockAtom Bk J L) : mass (D.R.law p L b) = 1 := by
  unfold TheoremCBlock.Reference.law mass
  rcases b with β | j
  · change ∑ z, (D.R.μ₀ β).weight z * 1 = 1
    simp only [mul_one]
    exact (D.R.μ₀ β).total
  · change ∑ z, (D.R.μp (p L j)).weight z * 1 = 1
    simp only [mul_one]
    exact (D.R.μp (p L j)).total

section Folds

variable {X : Type} [Fintype X] [DecidableEq X] (c : ReflectionCut Slot)

theorem mass_diag_plus (K : SlotMeasure X) :
    mass (c.diagonalLaw (halfMarginalPlus c K)) = mass K :=
  diagonalLaw_halfMarginalPlus_slot c K (fun _ => (1 : ℝ)) slot0

theorem mass_diag_minus (K : SlotMeasure X) :
    mass (c.diagonalLaw (halfMarginalMinus c K)) = mass K :=
  diagonalLaw_halfMarginalMinus_slot c K (fun _ => (1 : ℝ)) slot0

theorem mass_fullFold_plus {S : Type} [Fintype S] (m : ℝ) (π : FiniteLaw S)
    (κs : S → SlotMeasure X) (hprob : ∀ s, IsProbability (κs s)) :
    mass (m • ∑ s, π.weight s • c.diagonalLaw (halfMarginalPlus c (κs s))) = m := by
  unfold mass
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  have h1 : ∀ s, c.diagonalLaw (halfMarginalPlus c (κs s)) (fun _ => 1) = 1 := fun s =>
    (mass_diag_plus c (κs s)).trans (hprob s).2
  simp only [h1, mul_one, π.total]

theorem mass_fullFold_minus {S : Type} [Fintype S] (m : ℝ) (π : FiniteLaw S)
    (κs : S → SlotMeasure X) (hprob : ∀ s, IsProbability (κs s)) :
    mass (m • ∑ s, π.weight s • c.diagonalLaw (halfMarginalMinus c (κs s))) = m := by
  unfold mass
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, smul_eq_mul]
  have h1 : ∀ s, c.diagonalLaw (halfMarginalMinus c (κs s)) (fun _ => 1) = 1 := fun s =>
    (mass_diag_minus c (κs s)).trans (hprob s).2
  simp only [h1, mul_one, π.total]

end Folds

variable (dec : DecFamily D L)

omit [DecidableEq P] in
/-- **The plus folded law of a piece has the mass of the piece.** -/
theorem mass_bpieceLp (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    mass (bpieceLp D L Qb dec j b x) = pieceMass D L Qb b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact mass_refLaw D L b
  · exact mass_diag_plus _ _
  · exact mass_fullFold_plus _ _ _ _ (dec b i).prob
  · cases t
    · exact mass_diag_plus _ _
    · exact mass_diag_plus _ _
  · exact mass_diag_plus _ _

omit [DecidableEq P] in
/-- **The minus folded law of a piece has the mass of the piece.** -/
theorem mass_bpieceLm (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    mass (bpieceLm D L Qb dec j b x) = pieceMass D L Qb b x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · exact mass_refLaw D L b
  · exact mass_diag_minus _ _
  · exact mass_fullFold_minus _ _ _ _ (dec b i).prob
  · cases t
    · exact mass_diag_minus _ _
    · exact mass_diag_minus _ _
  · exact mass_diag_minus _ _

omit [DecidableEq P] in
/-- Every plus folded piece, `μ` included, is a positive record (`μ` by (R3)). -/
theorem isPositiveRecord_bpieceLp (hp : ∀ j, (p L j).Prime) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    IsPositiveRecord (bpieceLp D L Qb dec j b x) := by
  cases hx : hpieceIsMu D L b x
  · exact bpieceLp_positiveRecord D L Qb dec hQ j b x hx
  · rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
    · exact isPositiveRecord_muLaw D L hp b
    all_goals simp [hpieceIsMu] at hx

omit [DecidableEq P] in
/-- Every minus folded piece, `μ` included, is a positive record. -/
theorem isPositiveRecord_bpieceLm (hp : ∀ j, (p L j).Prime) (hQ : ∀ b, IsPositiveRecord (Qb b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    IsPositiveRecord (bpieceLm D L Qb dec j b x) := by
  cases hx : hpieceIsMu D L b x
  · exact bpieceLm_positiveRecord D L Qb dec hQ j b x hx
  · rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
    · exact isPositiveRecord_muLaw D L hp b
    all_goals simp [hpieceIsMu] at hx

/-- The coefficient of a piece at the local choice `(y, o) = (f 𝔟, σ 𝔟)`. -/
noncomputable def coefAt (j : D.FS.Tag) (b : BlockAtom Bk J L) (y : Bool)
    (o : Option (D.FS.Ib L b)) : HPiece D L b → ℝ
  | .inl _ => if o = none ∧ y = false then 1 else 0
  | .inr (.inl (i, none)) => if o = some i ∧ D.FS.tag L b i = j ∧ y = false then 1 else 0
  | .inr (.inl (i, some t)) =>
      if o = some i ∧ D.FS.tag L b i ≠ j ∧ y = false then (if t then 1 else -1) else 0
  | .inr (.inr _) => if o = none ∧ y = true then 1 else 0

omit [DecidableEq P] in
theorem hpieceCoef_eq (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b))
    (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    hpieceCoef D L f σ j b x = coefAt D L j b (f b) (σ b) x := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _) <;> rfl

omit [DecidableEq P] in
/-- **A piece is used by at most one local choice**: `∑_{y, o} |c_{y,o}(x)| ≤ 1`. -/
theorem sum_abs_coefAt_le (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : HPiece D L b) :
    ∑ y : Bool, ∑ o : Option (D.FS.Ib L b), |coefAt D L j b y o x| ≤ 1 := by
  rcases x with (_ | k) | (⟨i, _ | t⟩ | _)
  · simp [coefAt, Fintype.sum_option]
  · simp [coefAt, Fintype.sum_option]
  · simp only [coefAt, Fintype.sum_bool, Fintype.sum_option, reduceCtorEq, false_and,
      ↓reduceIte, abs_zero, Option.some.injEq, Bool.true_eq_false, and_false, sum_const_zero,
      and_true, zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [hi']) (by simp)]
    split_ifs <;> simp
  · simp only [coefAt, Fintype.sum_bool, Fintype.sum_option, reduceCtorEq, false_and,
      ↓reduceIte, abs_zero, Option.some.injEq, Bool.true_eq_false, and_false, sum_const_zero,
      and_true, zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [hi']) (by simp)]
    split_ifs <;> simp
  · simp [coefAt, Fintype.sum_option]

/-- The Rankin weight of a piece: `q_𝔟` at a non-`μ` piece, `1` at `μ`. -/
noncomputable def qf (q : BlockAtom Bk J L → ℝ) (b : BlockAtom Bk J L) (x : HPiece D L b) : ℝ :=
  if hpieceIsMu D L b x = true then 1 else q b

omit [DecidableEq P] in
theorem qf_nonneg {q : BlockAtom Bk J L → ℝ} (hq : ∀ b, 0 ≤ q b) (b : BlockAtom Bk J L)
    (x : HPiece D L b) : 0 ≤ qf D L q b x := by
  unfold qf
  split_ifs
  · exact zero_le_one
  · exact hq b

/-- The masses of the records at an atom: `∑_k ‖κu_k‖ + ‖Q‖ + ∑_i (d_i ‖κ_i‖ + ‖κ'_i‖ + ‖κ_i‖)`. -/
noncomputable def atomPr (b : BlockAtom Bk J L) : ℝ :=
  ∑ k, mass (D.GB.κu L b k) + mass (Qb b) +
    ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) + (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)))

omit [DecidableEq P] in
/-- **The per-atom Rankin sum**: `∑_x D_x m_x qf_x^{1/4} = 1 + q_𝔟^{1/4} Pr_𝔟`. -/
theorem sum_atom_eq (q : BlockAtom Bk J L → ℝ) (b : BlockAtom Bk J L) :
    ∑ x, bpieceD D L b x * pieceMass D L Qb b x * qf D L q b x ^ ((1 : ℝ) / 4) =
      1 + q b ^ ((1 : ℝ) / 4) * atomPr D L Qb b := by
  rw [sum_hpiece]
  simp only [bpieceD, pieceMass, qf, hpieceIsMu, ↓reduceIte, Real.one_rpow, mul_one,
    Bool.false_eq_true, one_mul, atomPr]
  rw [mul_add, mul_add, mul_sum, mul_sum]
  simp only [mul_comm (mass (D.GB.κu L b _)) (q b ^ ((1 : ℝ) / 4))]
  have e : ∀ i, D.FS.dconst L b i * mass (D.FS.κ L b i) * q b ^ ((1 : ℝ) / 4) +
      (mass (D.FS.κ' L b i) * q b ^ ((1 : ℝ) / 4) + mass (D.FS.κ L b i) * q b ^ ((1 : ℝ) / 4)) =
      q b ^ ((1 : ℝ) / 4) * (D.FS.dconst L b i * mass (D.FS.κ L b i) +
        (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) := fun i => by ring
  simp only [e]
  ring

end Pieces

section Rankin

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
  (Qb : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)

/-- The weight of a piece at a local choice: `|c_{y,o}(x)| D_x m_x`. -/
noncomputable def rankinG (j : D.FS.Tag) (b : BlockAtom Bk J L) (y : Bool)
    (o : Option (D.FS.Ib L b)) (x : HPiece D L b) : ℝ :=
  |coefAt D L j b y o x| * bpieceD D L b x * pieceMass D L Qb b x

omit [DecidableEq P] in
theorem rankinG_nonneg (hQ : ∀ b, IsPositiveRecord (Qb b)) (j : D.FS.Tag) (b : BlockAtom Bk J L)
    (y : Bool) (o : Option (D.FS.Ib L b)) (x : HPiece D L b) : 0 ≤ rankinG D L Qb j b y o x :=
  mul_nonneg (mul_nonneg (abs_nonneg _) (bpieceD_nonneg D L b x)) (pieceMass_nonneg D L Qb hQ b x)

omit [DecidableEq P] in
/-- **Rankin over the large pieces, then the sums over the local choices** (`lem:record:density-lp`,
last display; the sums over `f` and `σ` as in `lem:sharp-first`): if every piece outside `small`
has `T < ∏_𝔟 qf_𝔟(φ_𝔟)`, then
`∑_f ∑_{σ ∈ S} ∑_{¬small φ} w_φ m(φ) ≤ T^{-1/4} ∏_𝔟 (1 + q_𝔟^{1/4} Pr_𝔟)`, with
`w_φ = ∏_𝔟 |c_𝔟(φ_𝔟)| D_𝔟(φ_𝔟)` and `m(φ) = ∏_𝔟 m_𝔟(φ_𝔟)`. -/
theorem sum_choices_rankin_le (hQ : ∀ b, IsPositiveRecord (Qb b)) (j : D.FS.Tag)
    (q : BlockAtom Bk J L → ℝ) (hq : ∀ b, 0 ≤ q b) {T : ℝ} (hT : 0 < T)
    (small : (∀ b, HPiece D L b) → Prop)
    (hlarge : ∀ φ, ¬ small φ → T < ∏ b, qf D L q b (φ b))
    (S : Finset (∀ b, Option (D.FS.Ib L b))) :
    ∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S, ∑ φ : (∀ b, HPiece D L b),
      choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
        (open Classical in if small φ then 0 else ∏ b, pieceMass D L Qb b (φ b)) ≤
      T ^ (-((1 : ℝ) / 4)) * ∏ b, (1 + q b ^ ((1 : ℝ) / 4) * atomPr D L Qb b) := by
  classical
  have hW : ∀ b x, 0 ≤ qf D L q b x ^ ((1 : ℝ) / 4) := fun b x =>
    Real.rpow_nonneg (qf_nonneg D L hq b x) _
  -- one choice
  have hone : ∀ (f : BlockAtom Bk J L → Bool) (σ : ∀ b, Option (D.FS.Ib L b)),
      ∑ φ : (∀ b, HPiece D L b),
        choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
          (if small φ then 0 else ∏ b, pieceMass D L Qb b (φ b)) ≤
      T ^ (-((1 : ℝ) / 4)) *
        ∏ b, ∑ x, rankinG D L Qb j b (f b) (σ b) x * qf D L q b x ^ ((1 : ℝ) / 4) := by
    intro f σ
    have e1 : ∀ φ : (∀ b, HPiece D L b), choiceWeight (hpieceCoef D L f σ j) (bpieceD D L) φ *
        (if small φ then 0 else ∏ b, pieceMass D L Qb b (φ b)) =
        if small φ then 0 else ∏ b, rankinG D L Qb j b (f b) (σ b) (φ b) := by
      intro φ
      split_ifs
      · rw [mul_zero]
      · unfold choiceWeight
        rw [← prod_mul_distrib]
        refine prod_congr rfl fun b _ => ?_
        rw [hpieceCoef_eq]
        rfl
    simp_rw [e1]
    rw [sum_ite, sum_const_zero, zero_add]
    refine le_trans ?_ (Sarkozy.SharpSums.sum_large_pieces_le
      (fun b x => rankinG D L Qb j b (f b) (σ b) x)
      (fun b x => qf D L q b x) (fun b x => rankinG_nonneg D L Qb hQ j b (f b) (σ b) x)
      (fun b x => qf_nonneg D L hq b x) hT)
    refine sum_le_sum_of_subset_of_nonneg ?_ fun φ _ _ =>
      prod_nonneg fun b _ => rankinG_nonneg D L Qb hQ j b _ _ _
    intro φ hφ
    rw [mem_filter] at hφ ⊢
    exact ⟨hφ.1, hlarge φ hφ.2⟩
  have hF0 : ∀ (b : BlockAtom Bk J L) (y : Bool) (o : Option (D.FS.Ib L b)),
      0 ≤ ∑ x, rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4) := fun b y o =>
    sum_nonneg fun x _ => mul_nonneg (rankinG_nonneg D L Qb hQ j b y o x) (hW b x)
  calc _ ≤ ∑ f : BlockAtom Bk J L → Bool, ∑ σ ∈ S, T ^ (-((1 : ℝ) / 4)) *
        ∏ b, ∑ x, rankinG D L Qb j b (f b) (σ b) x * qf D L q b x ^ ((1 : ℝ) / 4) :=
        sum_le_sum fun f _ => sum_le_sum fun σ _ => hone f σ
    _ ≤ ∑ f : BlockAtom Bk J L → Bool, ∑ σ : (∀ b, Option (D.FS.Ib L b)),
        T ^ (-((1 : ℝ) / 4)) *
          ∏ b, ∑ x, rankinG D L Qb j b (f b) (σ b) x * qf D L q b x ^ ((1 : ℝ) / 4) := by
        refine sum_le_sum fun f _ => sum_le_univ_sum_of_nonneg fun σ => ?_
        exact mul_nonneg (Real.rpow_nonneg hT.le _) (prod_nonneg fun b _ => hF0 b _ _)
    _ = T ^ (-((1 : ℝ) / 4)) * ∏ b, ∑ y : Bool, ∑ o : Option (D.FS.Ib L b), ∑ x,
          rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4) := by
        simp_rw [← mul_sum]
        congr 1
        rw [Fintype.prod_sum (fun b y => ∑ o : Option (D.FS.Ib L b), ∑ x,
          rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4))]
        refine sum_congr rfl fun f _ => ?_
        rw [Fintype.prod_sum (fun b o => ∑ x,
          rankinG D L Qb j b (f b) o x * qf D L q b x ^ ((1 : ℝ) / 4))]
    _ ≤ T ^ (-((1 : ℝ) / 4)) * ∏ b, (1 + q b ^ ((1 : ℝ) / 4) * atomPr D L Qb b) := by
        refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hT.le _)
        refine prod_le_prod₀ (fun b _ => sum_nonneg fun y _ => sum_nonneg fun o _ =>
          hF0 b y o) fun b _ => ?_
        rw [← sum_atom_eq D L Qb q b]
        have e3 : ∑ y : Bool, ∑ o : Option (D.FS.Ib L b), ∑ x,
            rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4) =
            ∑ x, (∑ y : Bool, ∑ o : Option (D.FS.Ib L b), |coefAt D L j b y o x|) *
              (bpieceD D L b x * pieceMass D L Qb b x * qf D L q b x ^ ((1 : ℝ) / 4)) := by
          simp_rw [sum_mul]
          calc ∑ y : Bool, ∑ o : Option (D.FS.Ib L b), ∑ x,
                rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4)
              = ∑ y : Bool, ∑ x, ∑ o : Option (D.FS.Ib L b),
                rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4) :=
                sum_congr rfl fun y _ => sum_comm
            _ = ∑ x, ∑ y : Bool, ∑ o : Option (D.FS.Ib L b),
                rankinG D L Qb j b y o x * qf D L q b x ^ ((1 : ℝ) / 4) := sum_comm
            _ = _ := sum_congr rfl fun x _ => sum_congr rfl fun y _ => sum_congr rfl fun o _ => by
                unfold rankinG
                ring
        rw [e3]
        refine sum_le_sum fun x _ => ?_
        have h0 : 0 ≤ bpieceD D L b x * pieceMass D L Qb b x * qf D L q b x ^ ((1 : ℝ) / 4) :=
          mul_nonneg (mul_nonneg (bpieceD_nonneg D L b x) (pieceMass_nonneg D L Qb hQ b x))
            (hW b x)
        calc _ ≤ 1 * (bpieceD D L b x * pieceMass D L Qb b x *
              qf D L q b x ^ ((1 : ℝ) / 4)) :=
              mul_le_mul_of_nonneg_right (sum_abs_coefAt_le D L j b x) h0
          _ = _ := one_mul _

end Rankin

end Sarkozy.LargeSums

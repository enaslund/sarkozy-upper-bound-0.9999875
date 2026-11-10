module

public import Sarkozy.LargeSums.Data
public import Sarkozy.ThetaOne.SharpFirstWhole

@[expose] public section

/-!
# The whole-difference pieces of `lem:sharp-first`: masses, positivity and the choice sums

SR (8 November 2026). TH's pieces `ThetaOne.WPiece` of the whole-difference expansion of
`lem:sharp-first` (`μ_𝔟`, the records `κa_h` of `ρ_𝔟 − μ_𝔟`, a whole difference `κ' − κ` with
its full folded law, and the two positive parts `κ'`, `κ`), and what the summation of
`lem:sharp-first` needs of them:

* `wIsMu`, `wAtoms`: the `μ`-piece and the selected atoms `E` of a choice of pieces;
* `wMass`, **`mass_wpieceLp`**, **`mass_wpieceLm`**: both folded laws of a piece have the mass of
  the piece (`lem:record:folded-energy`(b) at the constant function);
* **`isPositiveRecord_wpieceLp/Lm`**: every folded piece, `μ` included, is a positive record;
* **`wMass_mul_le_wpieceG`**: `‖piece‖ s ≤ g` for `s ≤ sel_𝔟` (the price of a piece is its mass
  times the selection factor);
* `wCmax`, `sum_abs_wpieceCoef_le`: a piece is used by at most one local choice `σ_𝔟`, with total
  coefficient at most `wCmax` (`|c_h|` at a record of `ρ_𝔟 − μ_𝔟`, `1` otherwise);
* **`sum_choices_le`**: `∑_σ ∑_f w_{σ,j}(f) m(f) Φ(f) ≤ ∑_f ∏_𝔟 (c_max d m)_𝔟(f_𝔟) Φ(f)` for
  every `Φ ≥ 0` (the sums over the choices of `lem:sharp-first`, "at most one difference of an
  atom enters a term");
* `wPr`, `sum_atom_eq`: the per-atom sum `∑_x c_max d m qf^{1/4} = 1 + q_𝔟^{1/4} Pr_𝔟`;
* **`prod_wPr_le_exp`** (`def:cp8`(c)): `∏_𝔟 (1 + q_𝔟^{1/4} Pr_𝔟) ≤ e^{D.SM.bound}`.
-/

namespace Sarkozy.SharpFirst

open Finset Function
open scoped BigOperators
open Sarkozy.TheoremC Sarkozy.Structured Sarkozy.DensityChain Sarkozy.DensityFibre
  Sarkozy.EnvelopeInputs Sarkozy.EnvelopeInputsBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
  Sarkozy.EnvelopeEnergiesPaper Sarkozy.DensityChain2 Sarkozy.Comparison Sarkozy.ThetaOne
  Sarkozy.LargeSums ReflectionCut

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

section Pieces

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- Whether a piece is `μ_𝔟`. -/
def wIsMu (b : BlockAtom Bk J L) : WPiece D L b → Bool
  | .inl none => true
  | _ => false

/-- The selected atoms of a choice of pieces: the atoms whose piece is not `μ_𝔟`. -/
def wAtoms (f : ∀ b, WPiece D L b) : Finset (BlockAtom Bk J L) :=
  univ.filter fun b => wIsMu D L b (f b) = false

/-- The mass of a piece: `1` for `μ`, the mass of the record otherwise (`κ(1)` for a whole
difference, whose full folded law is `κ(1) ∑_s π_s Diag(m_±(κ_s))`). -/
noncomputable def wMass (b : BlockAtom Bk J L) : WPiece D L b → ℝ
  | .inl none => 1
  | .inl (some hh) => mass (D.FS.κa L b hh)
  | .inr ⟨i, none⟩ => mass (D.FS.κ L b i)
  | .inr ⟨i, some t⟩ => if t then mass (D.FS.κ' L b i) else mass (D.FS.κ L b i)

omit [DecidableEq P] in
theorem wMass_nonneg (b : BlockAtom Bk J L) (x : WPiece D L b) : 0 ≤ wMass D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact zero_le_one
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b hh).1
  · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
  · cases t
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1
    · exact TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1

variable {D L} (dec : DecFamily D L)

omit [DecidableEq P] in
/-- **The plus folded law of a piece has the mass of the piece.** -/
theorem mass_wpieceLp (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b) :
    mass (wpieceLp dec j b x) = wMass D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact mass_refLaw D L b
  · exact mass_diag_plus _ _
  · exact mass_fullFold_plus _ _ _ _ (dec b i).prob
  · cases t
    · exact mass_diag_plus _ _
    · exact mass_diag_plus _ _

omit [DecidableEq P] in
/-- **The minus folded law of a piece has the mass of the piece.** -/
theorem mass_wpieceLm (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b) :
    mass (wpieceLm dec j b x) = wMass D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact mass_refLaw D L b
  · exact mass_diag_minus _ _
  · exact mass_fullFold_minus _ _ _ _ (dec b i).prob
  · cases t
    · exact mass_diag_minus _ _
    · exact mass_diag_minus _ _

omit [DecidableEq P] in
/-- Every plus folded piece, `μ` included (by (R3)), is a positive record. -/
theorem isPositiveRecord_wpieceLp (hp : ∀ j, (p L j).Prime) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) (x : WPiece D L b) : IsPositiveRecord (wpieceLp dec j b x) := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact isPositiveRecord_muLaw D L hp b
  · exact isPositiveRecord_diag_plus _ (D.FS.κa_pos L b hh)
  · exact isPositiveRecord_fullFold_plus _ (D.FS.κ_pos L b i) (dec b i).π (dec b i).κs
      (dec b i).prob (dec b i).hκ
  · cases t
    · exact isPositiveRecord_diag_plus _ (D.FS.κ_pos L b i)
    · exact isPositiveRecord_diag_plus _ (D.FS.κ'_pos L b i)

omit [DecidableEq P] in
/-- Every minus folded piece, `μ` included, is a positive record. -/
theorem isPositiveRecord_wpieceLm (hp : ∀ j, (p L j).Prime) (j : D.FS.Tag)
    (b : BlockAtom Bk J L) (x : WPiece D L b) : IsPositiveRecord (wpieceLm dec j b x) := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · exact isPositiveRecord_muLaw D L hp b
  · exact isPositiveRecord_diag_minus _ (D.FS.κa_pos L b hh)
  · exact isPositiveRecord_fullFold_minus _ (D.FS.κ_pos L b i) (dec b i).π (dec b i).κs
      (dec b i).prob (dec b i).hκ
  · cases t
    · exact isPositiveRecord_diag_minus _ (D.FS.κ_pos L b i)
    · exact isPositiveRecord_diag_minus _ (D.FS.κ'_pos L b i)

omit [DecidableEq P] in
/-- The folded laws of `μ_𝔟` are `μ_𝔟` (plus side). -/
theorem wpieceLp_of_mu (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b)
    (hx : wIsMu D L b x = true) : wpieceLp dec j b x = D.R.law p L b := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩ <;> simp_all [wIsMu, wpieceLp]

omit [DecidableEq P] in
/-- The folded laws of `μ_𝔟` are `μ_𝔟` (minus side). -/
theorem wpieceLm_of_mu (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b)
    (hx : wIsMu D L b x = true) : wpieceLm dec j b x = D.R.law p L b := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩ <;> simp_all [wIsMu, wpieceLm]

omit [DecidableEq P] in
theorem wMass_of_mu (b : BlockAtom Bk J L) (x : WPiece D L b) (hx : wIsMu D L b x = true) :
    wMass D L b x = 1 := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩ <;> simp_all [wIsMu, wMass]

omit [DecidableEq P] in
theorem wpieceG_of_mu (b : BlockAtom Bk J L) (x : WPiece D L b) (hx : wIsMu D L b x = true) :
    wpieceG D L b x = 1 := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩ <;> simp_all [wIsMu, wpieceG]

omit [DecidableEq P] in
/-- **The price of a piece dominates its mass times `s ≤ sel_𝔟`** (`def:price`: the price of a
piece is its mass times the selection factor). -/
theorem wMass_mul_le_wpieceG (b : BlockAtom Bk J L) (x : WPiece D L b)
    (hx : wIsMu D L b x = false) {s : ℝ}
    (hs : s ≤ TheoremCBlock.selectionFactor a p D.S.selPre L b) :
    wMass D L b x * s ≤ wpieceG D L b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · simp [wIsMu] at hx
  · exact mul_le_mul_of_nonneg_left hs (wMass_nonneg D L b _)
  · exact mul_le_mul_of_nonneg_left hs (wMass_nonneg D L b _)
  · cases t
    · exact mul_le_mul_of_nonneg_left hs (wMass_nonneg D L b (.inr ⟨i, some false⟩))
    · exact mul_le_mul_of_nonneg_left hs (wMass_nonneg D L b (.inr ⟨i, some true⟩))

omit [DecidableEq P] in
theorem wpieceG_nonneg (b : BlockAtom Bk J L) (x : WPiece D L b) :
    0 ≤ wpieceG D L b x := by
  by_cases hx : wIsMu D L b x = true
  · rw [wpieceG_of_mu b x hx]
    exact zero_le_one
  · have h := wMass_mul_le_wpieceG b x (Bool.eq_false_iff.mpr hx)
      (le_refl (TheoremCBlock.selectionFactor a p D.S.selPre L b))
    exact le_trans (mul_nonneg (wMass_nonneg D L b x) (D.selectionFactor_nonneg L b)) h

end Pieces

section Choices

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}

/-- The largest total coefficient of a piece over the local choices: `|c_h|` at a record of
`ρ_𝔟 − μ_𝔟`, `1` otherwise. -/
noncomputable def wCmax (b : BlockAtom Bk J L) : WPiece D L b → ℝ
  | .inl (some hh) => |D.FS.ca L b hh|
  | _ => 1

omit [DecidableEq P] in
theorem wCmax_nonneg (b : BlockAtom Bk J L) (x : WPiece D L b) : 0 ≤ wCmax b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩ <;> simp [wCmax]

/-- The coefficient of a piece at the local choice `o = σ_𝔟`. -/
noncomputable def wCoefAt (j : D.FS.Tag) (b : BlockAtom Bk J L) (o : Option (D.FS.Ib L b)) :
    WPiece D L b → ℝ
  | .inl o' => if o = none then o'.elim 1 (D.FS.ca L b) else 0
  | .inr ⟨i, none⟩ => if o = some i ∧ D.FS.tag L b i = j then 1 else 0
  | .inr ⟨i, some t⟩ => if o = some i ∧ D.FS.tag L b i ≠ j then (if t then 1 else -1) else 0

omit [DecidableEq P] in
theorem wpieceCoef_eq (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag) (b : BlockAtom Bk J L)
    (x : WPiece D L b) : wpieceCoef σ j b x = wCoefAt j b (σ b) x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩ <;> rfl

omit [DecidableEq P] in
/-- **A piece is used by at most one local choice**: `∑_o |c_o(x)| ≤ c_max(x)`. -/
theorem sum_abs_wCoefAt_le (j : D.FS.Tag) (b : BlockAtom Bk J L) (x : WPiece D L b) :
    ∑ o : Option (D.FS.Ib L b), |wCoefAt j b o x| ≤ wCmax b x := by
  rcases x with (_ | hh) | ⟨i, _ | t⟩
  · simp [wCoefAt, wCmax, Fintype.sum_option]
  · simp [wCoefAt, wCmax, Fintype.sum_option]
  · simp only [wCoefAt, wCmax, Fintype.sum_option, reduceCtorEq, false_and, ↓reduceIte,
      abs_zero, Option.some.injEq, zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [hi']) (by simp)]
    split_ifs <;> simp
  · simp only [wCoefAt, wCmax, Fintype.sum_option, reduceCtorEq, false_and, ↓reduceIte,
      abs_zero, Option.some.injEq, zero_add]
    rw [Finset.sum_eq_single i (fun i' _ hi' => by simp [hi']) (by simp)]
    split_ifs <;> simp

omit [DecidableEq P] in
theorem choiceWeight_w_nonneg (σ : ∀ b, Option (D.FS.Ib L b)) (j : D.FS.Tag)
    (f : ∀ b, WPiece D L b) : 0 ≤ choiceWeight (wpieceCoef σ j) (wpieceD D L) f :=
  prod_nonneg fun b _ => mul_nonneg (abs_nonneg _) (wpieceD_nonneg b (f b))

omit [DecidableEq P] in
/-- **The sums over the choices** (`lem:sharp-first`: "at most one difference of an atom enters
a term"): for every `Φ ≥ 0`,
`∑_σ ∑_f w_{σ,j}(f) m(f) Φ(f) ≤ ∑_f ∏_𝔟 (c_max d m)_𝔟(f_𝔟) Φ(f)`. -/
theorem sum_choices_le (j : D.FS.Tag) (Φ : (∀ b, WPiece D L b) → ℝ) (hΦ : ∀ f, 0 ≤ Φ f) :
    ∑ σ : (∀ b, Option (D.FS.Ib L b)), ∑ f : (∀ b, WPiece D L b),
      choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f ≤
      ∑ f : (∀ b, WPiece D L b),
        (∏ b, wCmax b (f b) * wpieceD D L b (f b) * wMass D L b (f b)) * Φ f := by
  rw [Finset.sum_comm]
  refine sum_le_sum fun f _ => ?_
  have hdm : ∀ b, 0 ≤ wpieceD D L b (f b) * wMass D L b (f b) := fun b =>
    mul_nonneg (wpieceD_nonneg b (f b)) (wMass_nonneg D L b (f b))
  have e1 : ∀ σ : (∀ b, Option (D.FS.Ib L b)),
      choiceWeight (wpieceCoef σ j) (wpieceD D L) f * (∏ b, wMass D L b (f b)) * Φ f =
      (∏ b, |wCoefAt j b (σ b) (f b)| * (wpieceD D L b (f b) * wMass D L b (f b))) * Φ f := by
    intro σ
    unfold choiceWeight
    rw [← prod_mul_distrib]
    congr 1
    refine prod_congr rfl fun b _ => ?_
    rw [wpieceCoef_eq]
    ring
  simp_rw [e1]
  rw [← Finset.sum_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hΦ f)
  rw [← Fintype.prod_sum (fun b o => |wCoefAt j b o (f b)| *
    (wpieceD D L b (f b) * wMass D L b (f b)))]
  refine prod_le_prod₀ (fun b _ => sum_nonneg fun o _ => mul_nonneg (abs_nonneg _) (hdm b))
    fun b _ => ?_
  rw [← Finset.sum_mul]
  calc (∑ o, |wCoefAt j b o (f b)|) * (wpieceD D L b (f b) * wMass D L b (f b))
      ≤ wCmax b (f b) * (wpieceD D L b (f b) * wMass D L b (f b)) :=
        mul_le_mul_of_nonneg_right (sum_abs_wCoefAt_le j b (f b)) (hdm b)
    _ = _ := by ring

end Choices

section Rankin

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)

/-- The Rankin weight of a piece: `q_𝔟` at a non-`μ` piece, `1` at `μ`. -/
noncomputable def wqf (q : BlockAtom Bk J L → ℝ) (b : BlockAtom Bk J L) (x : WPiece D L b) : ℝ :=
  if wIsMu D L b x = true then 1 else q b

omit [DecidableEq P] in
theorem wqf_nonneg {q : BlockAtom Bk J L → ℝ} (hq : ∀ b, 0 ≤ q b) (b : BlockAtom Bk J L)
    (x : WPiece D L b) : 0 ≤ wqf D L q b x := by
  unfold wqf
  split_ifs
  · exact zero_le_one
  · exact hq b

/-- The masses of the records at an atom:
`Pr_𝔟 = ∑_h |c_h| ‖κa_h‖ + ∑_i (d_i ‖κ_i‖ + ‖κ'_i‖ + ‖κ_i‖)`. -/
noncomputable def wPr (b : BlockAtom Bk J L) : ℝ :=
  ∑ hh, |D.FS.ca L b hh| * mass (D.FS.κa L b hh) +
    ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) + (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i)))

omit [DecidableEq P] in
theorem wPr_nonneg (b : BlockAtom Bk J L) : 0 ≤ wPr D L b := by
  unfold wPr
  refine add_nonneg (sum_nonneg fun hh _ => mul_nonneg (abs_nonneg _)
    (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κa_pos L b hh).1))
    (sum_nonneg fun i _ => add_nonneg (mul_nonneg (D.FS.dconst_nonneg L b i)
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1))
      (add_nonneg (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)
        (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)))

omit [DecidableEq P] in
/-- The sum over the pieces of an atom, written out. -/
theorem sum_wpiece {M : Type} [AddCommMonoid M] (b : BlockAtom Bk J L) (F : WPiece D L b → M) :
    ∑ x, F x = F (.inl none) + ∑ hh, F (.inl (some hh)) +
      ∑ i, (F (.inr ⟨i, none⟩) + (F (.inr ⟨i, some false⟩) + F (.inr ⟨i, some true⟩))) := by
  rw [Fintype.sum_sum_type, Fintype.sum_option, Fintype.sum_sigma]
  congr 1
  refine sum_congr rfl fun i _ => ?_
  rw [Fintype.sum_option, Fintype.sum_bool]
  abel

omit [DecidableEq P] in
/-- **The per-atom Rankin sum**: `∑_x c_max d m qf^{1/4} = 1 + q_𝔟^{1/4} Pr_𝔟`. -/
theorem sum_atom_eq (q : BlockAtom Bk J L → ℝ) (b : BlockAtom Bk J L) :
    ∑ x, wCmax b x * wpieceD D L b x * wMass D L b x * wqf D L q b x ^ ((1 : ℝ) / 4) =
      1 + q b ^ ((1 : ℝ) / 4) * wPr D L b := by
  rw [sum_wpiece]
  simp only [wCmax, wpieceD, wMass, wqf, wIsMu, ↓reduceIte, Real.one_rpow, mul_one,
    Bool.false_eq_true, one_mul, wPr]
  rw [mul_add, mul_sum, mul_sum, add_assoc]
  congr 1
  congr 1
  · refine sum_congr rfl fun hh _ => ?_
    ring
  · refine sum_congr rfl fun i _ => ?_
    ring

omit [DecidableEq P] in
/-- **`Pr_𝔟` is at most the prices of `def:cp8`(c)** (`sel_𝔟 ≥ 1`):
`Pr_𝔟 ≤ p_𝔟 + ∑ v + ∑ d`. -/
theorem wPr_le (ha : 0 ≤ a) (b : BlockAtom Bk J L) :
    wPr D L b ≤ D.FS.pvar L b + ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i := by
  have hs := D.one_le_selectionFactor ha L b
  set s := TheoremCBlock.selectionFactor a p D.S.selPre L b with hsdef
  have hm : ∀ {X : Type} [Fintype X] {κ : SlotMeasure X}, IsNonneg κ → mass κ ≤ mass κ * s :=
    fun hκ => le_mul_of_one_le_right
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg hκ) hs
  have hp : ∑ hh, |D.FS.ca L b hh| * mass (D.FS.κa L b hh) ≤ D.FS.pvar L b := by
    unfold TheoremCBlock.FirstStage.pvar
    refine sum_le_sum fun hh _ => ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (hm (D.FS.κa_pos L b hh).1) (abs_nonneg _)
  have hdv : ∑ i, (D.FS.dconst L b i * mass (D.FS.κ L b i) +
      (mass (D.FS.κ' L b i) + mass (D.FS.κ L b i))) ≤
      ∑ i, D.FS.vprice L b i + ∑ i, D.FS.dprice L b i := by
    rw [← sum_add_distrib]
    refine sum_le_sum fun i _ => ?_
    have h1 : D.FS.dconst L b i * mass (D.FS.κ L b i) ≤ D.FS.dprice L b i := by
      unfold TheoremCBlock.FirstStage.dprice sharpPrice
      have := mul_le_mul_of_nonneg_left (hm (D.FS.κ_pos L b i).1) (D.FS.dconst_nonneg L b i)
      nlinarith
    have h2 : mass (D.FS.κ' L b i) + mass (D.FS.κ L b i) ≤ D.FS.vprice L b i := by
      unfold TheoremCBlock.FirstStage.vprice
      have := hm (D.FS.κ_pos L b i).1
      have := hm (D.FS.κ'_pos L b i).1
      nlinarith
    linarith
  unfold wPr
  linarith

omit [DecidableEq P] in
/-- **`Π_H ≤ exp(D.SM.bound)`** (`def:cp8`(c), the summability, as the paper uses it after
`lem:record:density-lp`). -/
theorem prod_wPr_le_exp (ha : 0 ≤ a) :
    ∏ b, (1 + atomQR D L b ^ ((1 : ℝ) / 4) * wPr D L b) ≤ Real.exp D.SM.bound := by
  have hq4 : ∀ b, 0 ≤ atomQR D L b ^ ((1 : ℝ) / 4) := fun b =>
    Real.rpow_nonneg (atomQR_nonneg D L b) _
  refine (prod_one_add_le_exp _ _ fun b _ => mul_nonneg (hq4 b) (wPr_nonneg D L b)).trans ?_
  refine Real.exp_le_exp.mpr ((sum_le_sum fun b _ => ?_).trans (D.SM.summable L))
  rw [oneWeight_eq_atomQ]
  refine mul_le_mul_of_nonneg_left ((wPr_le D L ha b).trans ?_) (hq4 b)
  have h1 := TheoremCBlock.Structured.uprice_nonneg D L b
  have h2 : 0 ≤ symTotal (D.CL.π L) b + skewTotal (D.CL.π L) b := by
    have := TheoremCBlock.Structured.wrapPrice_nonneg D L b
    unfold TheoremCBlock.Structured.wrapPrice at this
    unfold symTotal skewTotal
    rw [← sum_add_distrib]
    exact this
  have h3 := TheoremCBlock.Structured.envPriceL_nonneg D L b
  have h4 := TheoremCBlock.Structured.envPriceR_nonneg D L b
  unfold TheoremCBlock.Structured.envPriceL at h3
  unfold TheoremCBlock.Structured.envPriceR at h4
  linarith

end Rankin

end Sarkozy.SharpFirst

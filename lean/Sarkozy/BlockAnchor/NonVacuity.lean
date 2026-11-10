module

public import Sarkozy.BlockAnchor.Paper

@[expose] public section

/-!
# Non-vacuity of the first-stage cost at the paper's block prices (`def:cp2`, `def:price`)

D1 found that with the merged prefix atom of `Sarkozy.PaperFrame` the field `hL₀ : L₀ ≤ 4.8·10⁻⁴`
of the obligations cannot hold for the paper's first stage: every record at the prefix is charged
the factor of the whole prefix, which is at least `6·10⁹` at `a₀`
(`six_billion_le_paperMergedSel`). This file checks that the block atoms remove that obstruction.

* `toyFirstStage`: a first stage (`def:cp2`) on the block atoms with one sharp difference at one
  block `β₀`: a pair of positive records `w μ_{β₀}` (mass `w`) with sharp constant `d`, no variation
  records. Every field of `TheoremCBlock.FirstStage` is proved, the totals are computed at the block
  price `selPre β₀` (`toyFirstStage_dT`, `toyFirstStage_vT`), and
  `L₀ = 𝔗(d, v) ≤ e^{w selPre(β₀) max(d, 2)} − 1` (`toyFirstStage_L₀_le`).
* **`toy_paper_L₀_le`**: at the paper's prices, for a block of class-three primes of logarithmic
  length `≤ 886` (the upper band budget, `def:record:upper-bands`), with `w = 10⁻⁶` and `d = 1`:
  `L₀ ≤ anchorLedger.L₀`. So `hL₀` is satisfiable together with the paper's selection factors and a
  nonzero sharp first-stage record at a block.
* **`merged_L₀_ge`**: in the merged frame (`TheoremCParam.FirstStage`), a sharp difference of
  mass `w` and constant `d` at the prefix atom forces `L₀ ≥ w d selPre`; with the paper's value of
  the merged factor, `w = 10⁻⁶`, `d = 1`, this is `≥ 6000` (`merged_paper_L₀_ge`), far above the
  ledger's `4.8·10⁻⁴`.

The records of the toy are not the paper's (Part V's first stage is not formalized); the toy shows
that the obstruction found by D1 is gone, not that the paper's first stage satisfies `hL₀`.
-/

open Finset

namespace Sarkozy.BlockAnchor

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.BlockFrame Sarkozy.PaperFrame
  Sarkozy.Comparison Sarkozy.FourierArithmetic

section Toy

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
theorem isNonneg_law (R : TheoremCBlock.Reference m₀ blk) (L : ℕ) (b : BlockAtom Bk J L) :
    IsNonneg (R.law p L b) := by
  intro f hf
  cases b with
  | inl β => exact signedIntegral_nonneg (R.μ₀ β).nonneg hf
  | inr j => exact signedIntegral_nonneg (R.μp (p L j)).nonneg hf

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
theorem mass_law (R : TheoremCBlock.Reference m₀ blk) (L : ℕ) (b : BlockAtom Bk J L) :
    mass (R.law p L b) = 1 := by
  cases b with
  | inl β => exact mass_signedIntegral (R.μ₀ β)
  | inr j => exact mass_signedIntegral (R.μp (p L j))

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
theorem mass_smul_law (R : TheoremCBlock.Reference m₀ blk) (L : ℕ) (b : BlockAtom Bk J L) (w : ℝ) :
    mass (w • R.law p L b) = w := by
  unfold mass
  rw [LinearMap.smul_apply, smul_eq_mul]
  have h := mass_law (p := p) R L b
  unfold mass at h
  rw [h, mul_one]

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- A multiple `w μ_β ≥ 0` of a block reference law is a positive record (`def:cp:records`). -/
theorem isPositiveRecord_smul_law (R : TheoremCBlock.Reference m₀ blk) (L : ℕ) (β : Bk) {w : ℝ}
    (hw : 0 ≤ w) : IsPositiveRecord (w • R.law p L (Sum.inl β)) := by
  refine ⟨fun f hf => ?_, fun v g => ?_⟩
  · rw [LinearMap.smul_apply, smul_eq_mul]
    exact mul_nonneg hw (isNonneg_law R L _ f hf)
  · rw [mass_smul_law, LinearMap.smul_apply, smul_eq_mul]
    have h := R.unif₀ β v g
    rw [FiniteLaw.expect_uniform] at h
    change w * (R.μ₀ β).expect (fun z => g (z v)) = _
    rw [h]

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] in
/-- A zero difference has every sharp bound `d ≥ 0` relative to a multiple of a reference law. -/
theorem hasSharpBound_zero (R : TheoremCBlock.Reference m₀ blk) (L : ℕ) (b : BlockAtom Bk J L)
    (c : ReflectionCut Slot) (w : ℝ) {d : ℝ} (hd : 0 ≤ d) :
    HasSharpBound c (w • R.law p L b) (w • R.law p L b - w • R.law p L b) d := by
  refine ⟨Unit, inferInstance, FiniteLaw.uniform Unit, fun _ => R.law p L b, fun _ => 0,
    fun _ => ⟨isNonneg_law R L b, mass_law R L b⟩, ?_, ?_, fun _ => ?_⟩
  · rw [mass_smul_law, Fintype.sum_unique]
    have hw1 : (FiniteLaw.uniform Unit).weight default = 1 := by
      simp [FiniteLaw.uniform]
    rw [hw1, one_smul]
  · simp
  · intro F G
    have h0 : c.form (0 : SlotMeasure (BlockLabel m₀ blk p L b)) F G = 0 := rfl
    rw [h0, abs_zero]
    exact mul_nonneg (mul_nonneg hd (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)

/-- **A toy first stage on the block atoms** (`def:cp2`): one sharp difference at the block `β₀`,
between the positive records `κ = κ' = w μ_{β₀}` of mass `w`, with sharp constant `d` (an upper
bound: the difference is zero), and no variation records (`ρ = μ`). The totals are the block
prices: `P = 0`, `d_tag = w d selPre(β₀)`, `v_tag = 2 w selPre(β₀)`. -/
noncomputable def toyFirstStage (a : ℝ) (selPre : Bk → ℝ) (R : TheoremCBlock.Reference m₀ blk)
    (β₀ : Bk) (w d : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) :
    TheoremCBlock.FirstStage a m₀ blk p selPre R where
  fs _ := {Sum.inl β₀}
  Tag := Unit
  cut _ := reservedCut
  cut_family _ := Or.inr (Or.inr rfl)
  ϑ₀ := reservedCut
  ϑ₀_family := Or.inr (Or.inr rfl)
  ρ L b := R.law p L b
  Ia _ _ := Empty
  ca _ _ i := i.elim
  κa _ _ i := i.elim
  κa_pos _ _ i := i.elim
  ρ_sub L b := by simp
  ρ_ge L b _ := below_refl _ _
  ρ_off _ _ _ := rfl
  Ib L b := {_u : Unit // b = Sum.inl β₀}
  κ L b _ := w • R.law p L b
  κ' L b _ := w • R.law p L b
  κ_pos L b i := by
    obtain ⟨_, rfl⟩ := i
    exact isPositiveRecord_smul_law R L β₀ hw
  κ'_pos L b i := by
    obtain ⟨_, rfl⟩ := i
    exact isPositiveRecord_smul_law R L β₀ hw
  mass_eq _ _ _ := rfl
  tag _ _ _ := ()
  dconst _ _ _ := d
  dconst_nonneg _ _ _ := hd
  sharp L b _ := hasSharpBound_zero R L b reservedCut w hd
  off L b hb := ⟨fun i => hb (by rw [i.2]; exact Finset.mem_singleton_self _)⟩
  P := 0
  dT _ := w * d * selPre β₀
  vT _ := 2 * w * selPre β₀
  P_total L := by simp
  dT_total L j := by
    apply le_of_eq
    rw [Finset.sum_eq_single (Sum.inl β₀)]
    · rw [Fintype.sum_subsingleton _ ⟨(), rfl⟩]
      simp only [Subsingleton.elim () j, ↓reduceIte]
      unfold sharpPrice
      rw [mass_smul_law]
      rfl
    · intro b _ hb
      have : IsEmpty {_u : Unit // b = Sum.inl β₀} := ⟨fun i => hb i.2⟩
      exact Finset.sum_of_isEmpty _
    · intro h
      exact absurd (mem_univ _) h
  vT_total L j := by
    apply le_of_eq
    rw [Finset.sum_eq_single (Sum.inl β₀)]
    · rw [Fintype.sum_subsingleton _ ⟨(), rfl⟩]
      simp only [Subsingleton.elim () j, ↓reduceIte]
      rw [mass_smul_law]
      change (w + w) * selPre β₀ = 2 * w * selPre β₀
      ring
    · intro b _ hb
      have : IsEmpty {_u : Unit // b = Sum.inl β₀} := ⟨fun i => hb i.2⟩
      exact Finset.sum_of_isEmpty _
    · intro h
      exact absurd (mem_univ _) h

/-- **The first-stage cost of the toy** (`L₀ = e^P 𝔗(d, v)`, `def:cp2`):
`L₀ ≤ e^{w selPre(β₀) max(d, 2)} − 1`. -/
theorem toyFirstStage_L₀_le (a : ℝ) (selPre : Bk → ℝ) (R : TheoremCBlock.Reference m₀ blk)
    (β₀ : Bk) {w d : ℝ} (hw : 0 ≤ w) (hd : 0 ≤ d) (hs : 0 ≤ selPre β₀) :
    (toyFirstStage (p := p) a selPre R β₀ w d hw hd).L₀ ≤
      Real.exp (w * selPre β₀ * max d 2) - 1 := by
  unfold TheoremCBlock.FirstStage.L₀ firstStageCost
  change Real.exp 0 * tagSeries (fun _ : Unit => w * d * selPre β₀)
      (fun _ : Unit => 2 * w * selPre β₀) ≤ _
  rw [Real.exp_zero, one_mul]
  have hws : 0 ≤ w * selPre β₀ := mul_nonneg hw hs
  have h := tagSeries_le_exp (d := fun _ : Unit => w * d * selPre β₀)
    (v := fun _ : Unit => 2 * w * selPre β₀) (m := fun _ : Unit => w * selPre β₀ * max d 2)
    (fun _ => by positivity) (fun _ => by positivity)
    (fun _ => by nlinarith [le_max_left d 2]) (fun _ => by nlinarith [le_max_right d 2])
  simpa only [Fintype.sum_unique] using h

end Toy

/-! ## At the paper's prices -/

section Paper

open CancellationSteps

/-- `e^{2 a₀ · 886} ≤ e² ≤ 15/2`. -/
theorem exp_anchor_budget_le : Real.exp (2 * Param.Params.anchorDecay * 886) ≤ 15 / 2 := by
  have h1 : 2 * Param.Params.anchorDecay * 886 ≤ 1 + 1 := by norm_num [Param.Params.anchorDecay]
  have h3 := Real.exp_one_lt_d9
  have h4 : 0 < Real.exp 1 := Real.exp_pos 1
  calc Real.exp (2 * Param.Params.anchorDecay * 886) ≤ Real.exp (1 + 1) := Real.exp_le_exp.mpr h1
    _ = Real.exp 1 * Real.exp 1 := Real.exp_add 1 1
    _ ≤ 15 / 2 := by nlinarith

/-- **`hL₀` is satisfiable at the paper's block prices with a sharp record at a block.** For the
paper's data, any block reference and a block `β₀` of class-three primes (`e_p = 1`) of
logarithmic length `≤ 886` (`def:record:upper-bands`(b): the band budget `L_band ≤ 886`), the toy
first stage with record mass `w = 10⁻⁶` and sharp constant `d = 1` at `β₀`, priced by
`paperSel blk β₀ = q_{β₀}^{2a₀} ≤ e^{2a₀·886}`, has `L₀ ≤ anchorLedger.L₀`. -/
theorem toy_paper_L₀_le {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : PaperJ0 → Bk)
    (R : TheoremCBlock.Reference paperM0 blk) (β₀ : Bk)
    (h1 : ∀ i : BlockIdx blk β₀, paperEP i.1 = 1)
    (hL : ∑ i : BlockIdx blk β₀, Real.log (paperPP i.1) ≤ 886) :
    (toyFirstStage (p := paperTail) Param.Params.anchorDecay (paperSel blk) R β₀ (1 / 1000000) 1
      (by norm_num) zero_le_one).L₀ ≤ LedgerAnchor.anchorLedger.L₀ := by
  have hs1 := one_le_paperSel blk β₀
  have hs : paperSel blk β₀ ≤ 15 / 2 := by
    rw [paperSel_eq]
    exact (blockSel_le_exp anchorDecay_nonneg one_le_paperPP blk β₀ h1 hL).trans
      exp_anchor_budget_le
  have h := toyFirstStage_L₀_le (p := paperTail) Param.Params.anchorDecay (paperSel blk) R β₀
    (w := 1 / 1000000) (d := 1) (by norm_num) zero_le_one (by linarith)
  have hmax : max (1 : ℝ) 2 = 2 := by norm_num
  rw [hmax] at h
  have hx0 : 0 ≤ 1 / 1000000 * paperSel blk β₀ * 2 := by positivity
  have hx1 : 1 / 1000000 * paperSel blk β₀ * 2 ≤ 1 := by nlinarith
  have hexp := Real.abs_exp_sub_one_le (x := 1 / 1000000 * paperSel blk β₀ * 2)
    (by rw [abs_of_nonneg hx0]; exact hx1)
  rw [abs_of_nonneg hx0] at hexp
  have hL0 : LedgerAnchor.anchorLedger.L₀ = 0.00047996208 := rfl
  rw [hL0]
  have := (le_abs_self _).trans hexp
  nlinarith

end Paper

/-! ## The merged prefix atom -/

section Merged

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

/-- The tag series is at least its first-order term at any tag: `𝔗(d, v) ≥ d_j`
(the count vector `k = e_j`). -/
theorem le_tagSeries_single {Tag : Type} [Fintype Tag] [DecidableEq Tag] {d v : Tag → ℝ}
    (hd : ∀ j, 0 ≤ d j) (hv : ∀ j, 0 ≤ v j) (j : Tag) : d j ≤ tagSeries d v := by
  have h := sum_tagMin_le_tagSeries hd hv {Pi.single j 1}
  rw [Finset.sum_singleton] at h
  refine le_trans ?_ h
  have htags : tagsOf (Pi.single j 1 : Tag → ℕ) = {j} := by
    ext j'
    simp only [tagsOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    by_cases h' : j' = j
    · subst h'
      simp
    · simp [h']
  have hne : (tagsOf (Pi.single j 1 : Tag → ℕ)).Nonempty := by
    rw [htags]
    exact Finset.singleton_nonempty j
  unfold tagMin
  simp only [hne, ↓reduceDIte]
  apply Finset.le_inf'
  intro b hb
  rw [htags, Finset.mem_singleton] at hb
  subst hb
  apply le_of_eq
  unfold tagTerm
  rw [Finset.prod_eq_single b, Finset.prod_eq_single b]
  · simp
  · intro j' _ hj'
    simp [Pi.single_eq_of_ne hj']
  · simp
  · intro j' _ hj'
    simp [hj']
  · simp

omit [∀ L, DecidableEq (J L)] in
/-- **In the merged frame a sharp record at the prefix atom costs its sharp price in `L₀`.** For
first-stage data of `Sarkozy.TheoremCParam` (the merged prefix atom `none` with selection factor
`selPre`), a difference at the prefix of mass `w` and sharp constant `d` forces
`L₀ = e^P 𝔗(d, v) ≥ w d selPre`. -/
theorem merged_L₀_ge {a : ℝ} {selPre : ℝ} (hsel : 0 ≤ selPre) {R : TheoremC.Reference m₀}
    (FS : TheoremCParam.FirstStage a m₀ p selPre R) (L : ℕ) (i : FS.Ib L none) :
    mass (FS.κ L none i) * FS.dconst L none i * selPre ≤ FS.L₀ := by
  have hselF : ∀ L b, 0 ≤ TheoremCParam.selectionFactor a p selPre L b := by
    intro L b
    cases b with
    | none => exact hsel
    | some j => exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hmass : ∀ {X : Type} [Fintype X] {κ : SlotMeasure X}, IsNonneg κ → 0 ≤ mass κ :=
    fun h => h _ fun _ => zero_le_one
  have hdp : ∀ L b i, 0 ≤ sharpPrice (TheoremCParam.selectionFactor a p selPre L b) (FS.κ L b i)
      (FS.dconst L b i) := fun L b i =>
    mul_nonneg (mul_nonneg (hmass (FS.κ_pos L b i).1) (FS.dconst_nonneg L b i)) (hselF L b)
  have hvp : ∀ L b i, 0 ≤ (mass (FS.κ L b i) + mass (FS.κ' L b i)) *
      TheoremCParam.selectionFactor a p selPre L b := fun L b i =>
    mul_nonneg (add_nonneg (hmass (FS.κ_pos L b i).1) (hmass (FS.κ'_pos L b i).1)) (hselF L b)
  have hdT : ∀ j, 0 ≤ FS.dT j := fun j =>
    le_trans (sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact hdp 0 b i
      · exact le_refl 0) (FS.dT_total 0 j)
  have hvT : ∀ j, 0 ≤ FS.vT j := fun j =>
    le_trans (sum_nonneg fun b _ => sum_nonneg fun i _ => by
      split_ifs
      · exact hvp 0 b i
      · exact le_refl 0) (FS.vT_total 0 j)
  have hP : 0 ≤ FS.P :=
    le_trans (sum_nonneg fun b _ => sum_nonneg fun i _ => mul_nonneg (mul_nonneg (abs_nonneg _)
      (hmass (FS.κa_pos 0 b i).1)) (hselF 0 b)) (FS.P_total 0)
  have hrec : sharpPrice selPre (FS.κ L none i) (FS.dconst L none i) ≤
      FS.dT (FS.tag L none i) := by
    refine le_trans ?_ (FS.dT_total L (FS.tag L none i))
    refine le_trans ?_ (Finset.single_le_sum (f := fun b => ∑ i', if FS.tag L b i' = FS.tag L none i
      then sharpPrice (TheoremCParam.selectionFactor a p selPre L b) (FS.κ L b i')
        (FS.dconst L b i') else 0)
      (fun b _ => sum_nonneg fun i' _ => by
        split_ifs
        · exact hdp L b i'
        · exact le_refl 0) (mem_univ none))
    refine le_trans ?_ (Finset.single_le_sum (f := fun i' => if FS.tag L none i' = FS.tag L none i
      then sharpPrice (TheoremCParam.selectionFactor a p selPre L none) (FS.κ L none i')
        (FS.dconst L none i') else 0)
      (fun i' _ => by
        split_ifs
        · exact hdp L none i'
        · exact le_refl 0) (mem_univ i))
    simp only [↓reduceIte]
    rfl
  unfold TheoremCParam.FirstStage.L₀ firstStageCost
  calc mass (FS.κ L none i) * FS.dconst L none i * selPre =
        sharpPrice selPre (FS.κ L none i) (FS.dconst L none i) := rfl
    _ ≤ FS.dT (FS.tag L none i) := hrec
    _ ≤ tagSeries FS.dT FS.vT := le_tagSeries_single hdT hvT _
    _ ≤ Real.exp FS.P * tagSeries FS.dT FS.vT :=
        le_mul_of_one_le_left (tagSeries_nonneg hdT hvT) (Real.one_le_exp hP)

/-- **In the merged frame, at the paper's `def:price` value of the merged atom, `hL₀` fails** as
soon as one sharp record at the prefix has `w d ≥ 10⁻⁶`: then `L₀ ≥ 6000 > anchorLedger.L₀`
(`six_billion_le_paperMergedSel`). This is D1's obstruction, which the block atoms remove
(`toy_paper_L₀_le`). -/
theorem merged_paper_L₀_ge {R : TheoremC.Reference CancellationSteps.paperM0}
    (FS : TheoremCParam.FirstStage Param.Params.anchorDecay CancellationSteps.paperM0
      CancellationSteps.paperTail paperMergedSel R) (L : ℕ) (i : FS.Ib L none)
    (hw : (1 : ℝ) / 1000000 ≤ mass (FS.κ L none i) * FS.dconst L none i) :
    6000 ≤ FS.L₀ ∧ LedgerAnchor.anchorLedger.L₀ < FS.L₀ := by
  have hS := six_billion_le_paperMergedSel
  have h := merged_L₀_ge (by linarith) FS L i
  have hL0 : LedgerAnchor.anchorLedger.L₀ = 0.00047996208 := rfl
  rw [hL0]
  constructor <;> nlinarith

end Merged

end Sarkozy.BlockAnchor

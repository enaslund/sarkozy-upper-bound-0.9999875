module

public import Sarkozy.CliqueDeletion.Paper

@[expose] public section

/-!
# The total price of the square-clique deletions (`lem:frontier:iidenergy`(iii),(iv))

`paper/sections/19_prefix.tex`, `lem:frontier:iidenergy`(i),(iii),(iv).

The price of the square-clique atom `{p}` is `s_p + a_p = ω_p · q_p^{2a}` with the selection factor
`q_p^{2a} = p^{e_p a} = p^{2𝔪 a}` (B2's `ComparisonInputs.cliquePrice`, `paperSelAt`). With the
deletions of `paperCliqueDeletion` (`ω_p ≤ 12 · 2^{-𝔪}`) and at `a = a_T`:

* `prefixSel_le`: `q_p^{2a_T} ≤ 2^{7146}` (`p < P₄ = 2^{512}`, `512 · 2𝔪 · a_T < 7146`);
* `card_prefixCoord_le`: there are at most `2^{512}` prefix coordinates;
* **`cliquePrice_sum_le`**: `∑_p ω_p q_p^{2a_T} ≤ 12 · 2^{-534}` for every family of deletions with
  `ω_p ≤ 12 · 2^{-𝔪}`, in particular (`ComparisonInputs.cliquePrice_sum_le`) for B2's
  `ComparisonInputs` whose clique field is `paperCliqueDeletion` (K2's `SAParts.hq` with
  `H = 12/2^{534}`).

The paper's `H_iid < 2^{513 - 𝔪 + 1024𝔪a}` (iv) uses `ω_p ≤ η_𝔪 < 2^{1-𝔪}`; here `ω_p ≤ 12·2^{-𝔪}`
gives `12 · 2^{512 - 𝔪 + 1024𝔪 a}` with the same exponent, well inside the allowance `10^{-12}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.CliqueDeletion

open Sarkozy.PartV Sarkozy.PartVLaws Sarkozy.TheoremC Sarkozy.ComparisonLawPaper
  Sarkozy.CancellationSteps Sarkozy.BlockAnchor
open Sarkozy.TargetLedger (targetDecay)

variable {B : Type} [DecidableEq B] (blockOf : PaperJ0 → B)

/-- There are at most `P₄ = 2^{512}` prefix coordinates. -/
theorem card_prefixCoord_le : (Fintype.card PrefixCoord : ℝ) ≤ 2 ^ 512 := by
  have h1 : Fintype.card PrefixCoord ≤ Fintype.card PaperJ0 := Fintype.card_subtype_le _
  have h2 : Fintype.card PaperJ0 ≤ PartV.P4 := by
    rw [Fintype.card_coe]
    calc paperFixedPrimes.card ≤ (range PartV.P4).card :=
          card_le_card fun x hx => mem_range.mpr (paperJ0_lt_P4 ⟨x, hx⟩)
      _ = PartV.P4 := card_range _
  have h3 : (PartV.P4 : ℝ) = 2 ^ 512 := by
    simp only [PartV.P4, Nat.cast_pow, Nat.cast_ofNat]
  calc (Fintype.card PrefixCoord : ℝ) ≤ (PartV.P4 : ℝ) := by exact_mod_cast h1.trans h2
    _ = 2 ^ 512 := h3

/-- **The selection factor of a prefix atom at `a_T`**: `q_p^{2a_T} = p^{2𝔪 a_T} ≤ 2^{7146}`
(`lem:frontier:iidenergy`(i)). -/
theorem prefixSel_le (q : PrefixCoord) :
    MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q) ≤ 2 ^ (7146 : ℕ) := by
  rw [MainTarget.paperSelAt_eq]
  unfold blockSel
  rw [Fintype.prod_eq_single (prefixPoint blockOf q)
    (fun j hj => absurd (prefixPoint_unique blockOf q j) hj)]
  have hq : (prefixPoint blockOf q).1 = q.1 := rfl
  unfold coordSel
  rw [hq]
  have hep : paperEP q.1 = 2 * digitPairs := by
    unfold paperEP
    simp only [q.2, ↓reduceIte, prefixExponent]
  have hne : paperEP q.1 ≠ 1 := by
    rw [hep]
    unfold digitPairs
    norm_num
  simp only [hne, ↓reduceIte]
  rw [hep]
  have hp : (paperPP q.1 : ℝ) ≤ 2 ^ 512 := by
    have h := paperJ0_lt_P4 q.1
    have h' : (paperPP q.1 : ℝ) ≤ (PartV.P4 : ℝ) := by
      unfold paperPP
      exact_mod_cast h.le
    calc (paperPP q.1 : ℝ) ≤ (PartV.P4 : ℝ) := h'
      _ = 2 ^ 512 := by simp only [PartV.P4, Nat.cast_pow, Nat.cast_ofNat]
  have ha : 0 ≤ ((2 * digitPairs : ℕ) : ℝ) * targetDecay := by
    have := TargetLedger.targetDecay_nonneg
    positivity
  calc (paperPP q.1 : ℝ) ^ (((2 * digitPairs : ℕ) : ℝ) * targetDecay)
      ≤ ((2 : ℝ) ^ 512) ^ (((2 * digitPairs : ℕ) : ℝ) * targetDecay) :=
        Real.rpow_le_rpow (Nat.cast_nonneg _) hp ha
    _ = (2 : ℝ) ^ ((512 : ℝ) * (((2 * digitPairs : ℕ) : ℝ) * targetDecay)) := by
        rw [← Real.rpow_natCast 2 512, ← Real.rpow_mul (by norm_num)]
        norm_num
    _ ≤ (2 : ℝ) ^ ((7146 : ℕ) : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
        unfold digitPairs targetDecay
        norm_num
    _ = 2 ^ (7146 : ℕ) := Real.rpow_natCast 2 7146

/-- **The total price of the square-clique deletions** (`lem:frontier:iidenergy`(iii),(iv)), for
every family of deletions with `ω_p ≤ 12 · 2^{-𝔪}`: `∑_p ω_p q_p^{2a_T} ≤ 12 · 2^{-534}`. -/
theorem cliquePrice_sum_le (ω : PrefixCoord → ℝ)
    (hω : ∀ q, ω q ≤ 12 / 2 ^ digitPairs) :
    ∑ q, ω q * MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q) ≤
      12 / 2 ^ 534 := by
  have hterm : ∀ q, ω q * MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q) ≤
      12 / 2 ^ digitPairs * 2 ^ (7146 : ℕ) := by
    intro q
    have hs0 : 0 ≤ MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q) :=
      le_trans zero_le_one (MainTarget.one_le_paperSelAt _ TargetLedger.targetDecay_nonneg _)
    exact mul_le_mul (hω q) (prefixSel_le blockOf q) hs0 (by positivity)
  calc ∑ q, ω q * MainTarget.paperSelAt (paperAtomMap blockOf) targetDecay (.inl q)
      ≤ ∑ _q : PrefixCoord, 12 / 2 ^ digitPairs * (2 : ℝ) ^ (7146 : ℕ) :=
        sum_le_sum fun q _ => hterm q
    _ = (Fintype.card PrefixCoord : ℝ) * (12 / 2 ^ digitPairs * 2 ^ (7146 : ℕ)) := by
        rw [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ 2 ^ 512 * (12 / 2 ^ digitPairs * 2 ^ (7146 : ℕ)) :=
        mul_le_mul_of_nonneg_right card_prefixCoord_le (by positivity)
    _ = 12 / 2 ^ 534 := by
        have h : (2 : ℝ) ^ (534 + (512 + 7146)) = 2 ^ 534 * (2 ^ 512 * 2 ^ 7146) := by
          rw [pow_add, pow_add]
        simp only [Nat.reduceAdd] at h
        unfold digitPairs
        rw [h]
        field_simp

/-- **The square-clique price of B2's `ComparisonInputs`** whose deletions have `ω_p ≤ 12·2^{-𝔪}`
(e.g. `paperCliqueDeletion`, `paperCliqueDeletion_ω_le`): `∑_p (s_p + a_p) ≤ 12 · 2^{-534}`. -/
theorem ComparisonInputs.cliquePrice_sum_le [Fintype B] {hW : Target.Weil}
    {spec : ∀ b, PaperBlockSpec blockOf b} {hC : TailInputsCorr PartV.P4}
    {In : FirstStagePaper.FirstStageInputs blockOf} (I : ComparisonInputs blockOf hW spec hC In)
    (hI : ∀ q, (I.clique q).ω ≤ 12 / 2 ^ digitPairs) :
    ∑ q, I.cliquePrice q ≤ 12 / 2 ^ 534 :=
  CliqueDeletion.cliquePrice_sum_le blockOf (fun q => (I.clique q).ω) hI

end Sarkozy.CliqueDeletion

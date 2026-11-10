module

public import Sarkozy.SignedEstimates.Col
public import Sarkozy.SignedEstimates.G0
public import Sarkozy.MainFinal2.Structure

@[expose] public section

/-!
# `SignedEstimates` at every prime of every middle block (E1)

`paper/sections/21_middle_records.tex`, `lem:signed-components`(b), `lem:old-f-law`(a);
`thm:weil`(a) (H1, `Target.Weil`).

* **`signedEstimates_of`**: over any finite field with `q ≡ 3 (4)`, `q ≥ 2²⁴`, given the Weil bound
  `|W(a, b, d)| ≤ 2√q` for distinct labels, B8's `SignedEstimates hF t c η e` holds with the
  paper's `η = η_c = 10q` (`q = 1/p`) and `e = e₀ = 2q/((1-3q)(1-4q))`, for every `0 ≤ t ≤ 1`
  and every component `c`;
* `weil_three`: H1 gives the Weil bound at `ZMod p` (`S = {a, b, d}`, `|S| - 1 = 2`);
* **`signedEstimates_zmod`**: the same at `ZMod p` from H1;
* **`paperMiddleEstimates hW b hne`**: K2's `MiddleEstimates b hne` on every middle block of the
  paper's partition, with `η_p = 10/p` and `e_p = e₀(p)` exactly (field 11 of
  `MainFinalObligations2`, closed from H1). Every middle prime is at least `Q₃ = 19951586 > 2²⁴`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedEstimates

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing Sarkozy.SignedComponents

section Field

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

theorem compU_real (c : Fin 3) : ((compU c : ℤ) : ℝ) = 1 ∨ ((compU c : ℤ) : ℝ) = -1 := by
  rcases compU_cases c with h | h <;> simp [h]

theorem compV_real (c : Fin 3) : ((compV c : ℤ) : ℝ) = 1 ∨ ((compV c : ℤ) : ℝ) = -1 := by
  rcases compV_cases c with h | h <;> simp [h]

/-- **The estimates of `lem:signed-components`(b) and `lem:old-f-law`(a)** at one prime, with the
paper's constants `η = 10/p` and `e = e₀(p)`, for `p ≡ 3 (4)`, `p ≥ 2²⁴`, `0 ≤ t ≤ 1`, given the
Weil bound for the cubic character sums at distinct labels (`thm:weil`(a)). -/
theorem signedEstimates_of (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (hn : 16777216 ≤ Fintype.card F) (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (hW : ∀ a b d : F, a ≠ b → a ≠ d → b ≠ d → |Wsum a b d| ≤ 2 * Real.sqrt (Fintype.card F))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : Fin 3) :
    SignedEstimates hF t c (10 / (Fintype.card F : ℝ)) (e0 (Fintype.card F)) := by
  have hn' : (16777216 : ℝ) ≤ Fintype.card F := by exact_mod_cast hn
  have hrow : ∀ x : Fin 3 → F, HF x →
      |rowMean t (compU c) (compV c) x - 1| ≤ 10 / (Fintype.card F : ℝ) := fun x hx => by
    obtain ⟨h01, h02, h12⟩ := HF_ne hx
    exact rowMean_bound hR h3 hn' ht0 ht1 (compU_real c) (compV_real c) hx (hW _ _ _ h01 h02 h12)
  refine ⟨hrow, fun y hy => ?_, zMean_bound_of_row hR (by omega) hrow, fun x hx =>
    g0_bound hR h3 (by omega) hF hx⟩
  obtain ⟨h01, h02, h12⟩ := HF_ne hy
  exact colMean_bound hR h3 hn' ht0 ht1 (compU_real c) (compV_real c) hy (hW _ _ _ h01 h02 h12)

end Field

/-- **H1 gives the Weil bound for three distinct labels** (`thm:weil`(a) with `S = {a, b, d}`):
`|∑_c χ(c - a) χ(c - b) χ(c - d)| ≤ 2√p`. -/
theorem weil_three (hW : Target.Weil) (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (a b d : ZMod p)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d) : |Wsum a b d| ≤ 2 * Real.sqrt p := by
  have hS : ({a, b, d} : Finset (ZMod p)).Nonempty := ⟨a, by simp⟩
  have h := hW p hp {a, b, d} hS
  have ha : a ∉ ({b, d} : Finset (ZMod p)) := by simp [hab, had]
  have hb : b ∉ ({d} : Finset (ZMod p)) := by simp [hbd]
  have hcard : (({a, b, d} : Finset (ZMod p)).card : ℝ) = 3 := by
    rw [card_insert_of_notMem ha, card_pair hbd]; norm_num
  rw [hcard] at h
  have e : Wsum a b d =
      ((∑ x, quadraticChar (ZMod p) (∏ e ∈ ({a, b, d} : Finset (ZMod p)), (x - e)) : ℤ) : ℝ) := by
    unfold Wsum
    push_cast
    refine sum_congr rfl fun x _ => ?_
    rw [prod_insert ha, prod_insert hb, prod_singleton, map_mul, map_mul]
    push_cast
    ring
  rw [e]
  linarith

/-- **`SignedEstimates` at `ZMod p` from H1** (`lem:signed-components`(b), `lem:old-f-law`(a)),
with `η = 10/p`, `e = e₀(p)`, for `p ≡ 3 (4)`, `p ≥ 2²⁴`. -/
theorem signedEstimates_zmod (hW : Target.Weil) (p : ℕ) [Fact p.Prime] (h3 : p % 4 = 3)
    (hn : 16777216 ≤ p) (hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : Fin 3) :
    SignedEstimates hF t c (10 / (p : ℝ)) (e0 p) := by
  have hp2 : p ≠ 2 := by omega
  have hR : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hc : Fintype.card (ZMod p) = p := ZMod.card p
  have h := signedEstimates_of hR (by rw [hc]; exact h3) (by rw [hc]; exact hn) hF
    (fun a b d hab had hbd => by rw [hc]; exact weil_three hW p hp2 a b d hab had hbd) ht0 ht1 c
  rw [hc] at h
  exact h

theorem e0_nonneg {n : ℝ} (hn : 5 ≤ n) : 0 ≤ e0 n := by
  unfold e0
  have : 0 < n - 3 := by linarith
  have : 0 < n - 4 := by linarith
  have : 0 < n := by linarith
  positivity

theorem e0_lt_one {n : ℝ} (hn : 10 ≤ n) : e0 n < 1 := by
  unfold e0
  have h : 0 < (n - 3) * (n - 4) := by
    have : 0 < n - 3 := by linarith
    have : 0 < n - 4 := by linarith
    positivity
  rw [div_lt_one h]
  nlinarith

/-! ## The paper's middle blocks -/

section Paper

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartVRecords
open Sarkozy.CancellationSteps Sarkozy.MainAnchor Sarkozy.MainTarget Sarkozy.FirstStagePaper
  Sarkozy.GramBracketPaper Sarkozy.JointClosing Sarkozy.BlockSpecPaper
open Sarkozy.PartVLaws (paperAtomMap blockPrimes)
open Sarkozy.MainFinal Sarkozy.MainFinal2

theorem blockPrime_ge (b : Blk) (i : {j : PaperJ0 // paperAtomMap bOf j = .inr b}) :
    16777216 ≤ blockPrimes bOf b i :=
  le_trans (by norm_num [PartV.Q3]) (blockPrimes_mod_ge b i).2

/-- **The signed estimates of every middle block of the paper** (field 11 of
`MainFinalObligations2`, `lem:signed-components`(b) and `lem:old-f-law`(a)), **proved from H1**,
with the paper's constants `η_p = 10/p` and `e_p = e₀(p) = 2q/((1-3q)(1-4q))` at every prime `p`
of the block, at the paper's `t = 127/500`. -/
noncomputable def paperMiddleEstimates (hW : Target.Weil) (b : Blk)
    (hne : MiddleNonempty (blockPrimes bOf b)) : MiddleEstimates b hne where
  η i := 10 / (blockPrimes bOf b i : ℝ)
  e i := e0 (blockPrimes bOf b i)
  hη i := by positivity
  hη1 i := by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    rw [div_lt_one (by linarith)]
    linarith
  he i := e0_nonneg (by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    linarith)
  he1 i := e0_lt_one (by
    have h : (16777216 : ℝ) ≤ blockPrimes bOf b i := by exact_mod_cast blockPrime_ge b i
    linarith)
  E i c := signedEstimates_zmod hW _ (blockPrimes_mod_ge b i).1 (blockPrime_ge b i) (hne.F2 i)
    tPaper_nonneg tPaper_le_one c

end Paper

end Sarkozy.SignedEstimates

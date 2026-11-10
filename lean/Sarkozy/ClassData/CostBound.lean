module

public import Sarkozy.ClassData.CostData
public import Sarkozy.ClassInputsPaper.Energy

@[expose] public section

/-!
# `classCost ≤ C_n` at `a_T` for the 49 degree vectors (kernel-checked)

`paper/sections/28_closing.tex`, `def:closing-quantities`(7); `paper/sections/23_envelopes.tex`,
`thm:envelopes`(i), `cor:envelope-costs`, `lem:orbit-coupon`(iv).

B10's `consistent_inl` reduces the consistency of a degree class (K2's field 41,
`Cls.ES.consistent`, on the degree classes) to analytic inputs (the background gate `hbg`, the
remainder bound `hρ`, the price identities `harm`, `hυ0`, `hυ`), the energy factor `B ≤ B'`, and
the numerical gate **`classCost κ_H κ_b M M^inv U₀ tU tδ ≤ C_n`**. Here the numerical gate is
proved at the parameters of `CostData.lean` for every `n ∈ paperN`, with `C_n = paperC n`, B4's
rounded costs (the costs B4's `savings_cert` uses):

* `exp_U0_le`, `le_exp_tU`, `exp_tU_le`: the exponentials, by `Real.exp_bound` with 50 terms;
* `bound_le_cQ` (`decide +kernel`): the class costs with the exponentials replaced by their
  enclosures are at most `cQ` on all 49 triples;
* **`paper_classCost_le`**: `classCost (paperκH n) … ≤ paperC n` for `n ∈ paperN`;
* **`paper_classCost_gates`**: W2's side conditions `0 ≤ κ_b ≤ κ_H`, `tU ≤ U₀` and
  `M^inv e^{tU} tδ ≤ M R_err` (`classCost_ge`, `lem:orbit-coupon`(iv)) at the same parameters;
* **`consistent_inl_paper`**: B10's `consistent_inl` at these parameters, with `B = B^{ledger}`,
  for any class data with `N ⊆ paperN`, `C ≥ paperC` on `N` and `B' ≥ B^{ledger}` (in particular
  B10's `ClassData.paper` with `C = paperC`). Only the analytic inputs remain.
-/

open Finset

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper
open Sarkozy.Envelopes (classCost)
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ### The exponentials -/

theorem exp_U0_le : Real.exp (U0 : ℝ) ≤ (eUhi : ℝ) :=
  exp_le_of_ps (n := 50) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel)

theorem le_exp_tU : (eTlo : ℝ) ≤ Real.exp (tU : ℝ) :=
  le_exp_of_ps (n := 50) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel)

theorem exp_tU_le : Real.exp (tU : ℝ) ≤ (eThi : ℝ) :=
  exp_le_of_ps (n := 50) (by decide +kernel) (by decide +kernel) (by norm_num)
    (by decide +kernel)

/-! ### The class of a degree vector -/

/-- The index (`0 … 15`, as in `CostData.lean`) of the general class `(n, m)`, `n ≥ 1`. -/
def genIdx : ℕ → ℕ → ℕ
  | 1, 3 => 0
  | 2, 2 => 1
  | 3, 1 => 2
  | 4, 0 => 3
  | 1, 5 => 4
  | 2, 4 => 5
  | 3, 3 => 6
  | 4, 2 => 7
  | 5, 1 => 8
  | 6, 0 => 9
  | 2, 0 => 10
  | 1, 1 => 11
  | _, _ => 0

/-- The class index of the degree vector `(n, m₀, m₁)`, with the branching of B4's `cQ`. -/
def clsOf (n m₀ m₁ : ℕ) : ℕ :=
  if n = 0 then
    (if m₀ + m₁ = 2 then (if m₀ = 1 then 13 else 12)
      else if m₀ + m₁ = 4 then 14 else 15)
  else genIdx n (m₀ + m₁)

/-- The class index of a degree vector. -/
def idxOf (n : Fin 3 → ℕ) : ℕ := clsOf (n 0) (n 1) (n 2)

/-- The class cost of class `i` with `e^{U₀} ≤ eUhi` and `eTlo ≤ e^{tU}` substituted. -/
def boundQ (i : ℕ) : ℚ :=
  κHQ i * eUhi - (κHQ i - κbQ i) * eTlo + MQ i * Rerr - MinvQ i * eTlo * tδ

/-- **The numerical gate on all 49 triples** (`decide +kernel`): the signs, and the class cost
with the exponential enclosures is at most B4's `cQ`. -/
theorem bound_le_cQ : ∀ t ∈ triples,
    (0 ≤ κbQ (clsOf t.1 t.2.1 t.2.2) ∧ κbQ (clsOf t.1 t.2.1 t.2.2) ≤ κHQ (clsOf t.1 t.2.1 t.2.2) ∧
      0 ≤ MinvQ (clsOf t.1 t.2.1 t.2.2) ∧
      MinvQ (clsOf t.1 t.2.1 t.2.2) * eThi * tδ ≤ MQ (clsOf t.1 t.2.1 t.2.2) * Rerr) ∧
    boundQ (clsOf t.1 t.2.1 t.2.2) ≤ cQ t.1 t.2.1 t.2.2 := by
  decide +kernel

theorem tU_le_U0 : tU ≤ U0 := by decide +kernel

theorem tδ_nonneg : 0 ≤ tδ := by decide +kernel

theorem Rerr_nonneg : 0 ≤ Rerr := by decide +kernel

/-! ### The parameters over the reals -/

/-- `κ_H` of the class of `n`. -/
noncomputable def paperκH (n : Fin 3 → ℕ) : ℝ := (κHQ (idxOf n) : ℝ)
/-- `κ_b` of the class of `n`. -/
noncomputable def paperκb (n : Fin 3 → ℕ) : ℝ := (κbQ (idxOf n) : ℝ)
/-- `M` of the class of `n`. -/
noncomputable def paperM (n : Fin 3 → ℕ) : ℝ := (MQ (idxOf n) : ℝ)
/-- `M^inv` of the class of `n`. -/
noncomputable def paperMinv (n : Fin 3 → ℕ) : ℝ := (MinvQ (idxOf n) : ℝ)
/-- `U₀` at `a_T`. -/
noncomputable def paperU0 : ℝ := (U0 : ℝ)
/-- `tU_inv` at `a_T`. -/
noncomputable def paperTU : ℝ := (tU : ℝ)
/-- `R_err` at `a_T`. -/
noncomputable def paperRerr : ℝ := (Rerr : ℝ)
/-- `tδ_s` at `a_T`. -/
noncomputable def paperTδ : ℝ := (tδ : ℝ)

/-- From `n ∈ paperN` to its triple. -/
theorem exists_triple {n : Fin 3 → ℕ} (hn : n ∈ paperN) :
    ∃ t ∈ triples, n = toVec t := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hn
  exact ⟨t, List.mem_toFinset.mp ht, rfl⟩

/-- The real class cost is at most the rational bound `boundQ`, given the signs. -/
theorem classCost_le_boundQ (i : ℕ) (hb0 : 0 ≤ κbQ i) (hb : κbQ i ≤ κHQ i)
    (hm : 0 ≤ MinvQ i) :
    classCost (κHQ i : ℝ) (κbQ i) (MQ i) (MinvQ i) U0 tU Rerr tδ ≤ (boundQ i : ℝ) := by
  have e1 := exp_U0_le
  have e2 := le_exp_tU
  have hH : (0 : ℝ) ≤ κHQ i := by exact_mod_cast hb0.trans hb
  have hHb : (0 : ℝ) ≤ (κHQ i : ℝ) - κbQ i := by
    have : ((κbQ i : ℚ) : ℝ) ≤ κHQ i := by exact_mod_cast hb
    linarith
  have hmd : (0 : ℝ) ≤ (MinvQ i : ℝ) * tδ := by
    have h1 : (0 : ℝ) ≤ MinvQ i := by exact_mod_cast hm
    have h2 : (0 : ℝ) ≤ tδ := by exact_mod_cast tδ_nonneg
    positivity
  have a1 := mul_le_mul_of_nonneg_left e1 hH
  have a2 := mul_le_mul_of_nonneg_left e2 hHb
  have a3 := mul_le_mul_of_nonneg_left e2 hmd
  unfold classCost boundQ
  push_cast
  nlinarith

/-- **`classCost ≤ C_n` at `a_T`** (`def:closing-quantities`(7), `cor:envelope-costs`): for every
degree vector `n` of the sixteen envelope classes, the class cost at the paper's parameters
(`CostData.lean`) is at most B4's `paperC n`. This is the numerical gate `hC` of B10's
`consistent_inl`. -/
theorem paper_classCost_le {n : Fin 3 → ℕ} (hn : n ∈ paperN) :
    classCost (paperκH n) (paperκb n) (paperM n) (paperMinv n) paperU0 paperTU paperRerr paperTδ ≤
      paperC n := by
  obtain ⟨t, ht, rfl⟩ := exists_triple hn
  obtain ⟨⟨hb0, hb, hm, -⟩, hle⟩ := bound_le_cQ t ht
  have e : idxOf (toVec t) = clsOf t.1 t.2.1 t.2.2 := rfl
  have ec : paperC (toVec t) = (cQ t.1 t.2.1 t.2.2 : ℝ) := rfl
  unfold paperκH paperκb paperM paperMinv paperU0 paperTU paperRerr paperTδ
  rw [e, ec]
  exact (classCost_le_boundQ _ hb0 hb hm).trans (by exact_mod_cast hle)

/-- **W2's side conditions at the paper's parameters** (`classCost_ge`, `lem:orbit-coupon`(iv)):
`0 ≤ κ_b ≤ κ_H`, `tU_inv ≤ U₀` and `M^inv e^{tU_inv} tδ_s ≤ M R_err`. -/
theorem paper_classCost_gates {n : Fin 3 → ℕ} (hn : n ∈ paperN) :
    0 ≤ paperκb n ∧ paperκb n ≤ paperκH n ∧ paperTU ≤ paperU0 ∧
      paperMinv n * Real.exp paperTU * paperTδ ≤ paperM n * paperRerr := by
  obtain ⟨t, ht, rfl⟩ := exists_triple hn
  obtain ⟨⟨hb0, hb, hm, hc⟩, -⟩ := bound_le_cQ t ht
  have e : idxOf (toVec t) = clsOf t.1 t.2.1 t.2.2 := rfl
  unfold paperκH paperκb paperM paperMinv paperU0 paperTU paperRerr paperTδ
  rw [e]
  refine ⟨by exact_mod_cast hb0, by exact_mod_cast hb, by exact_mod_cast tU_le_U0, ?_⟩
  have h1 : (0 : ℝ) ≤ MinvQ (clsOf t.1 t.2.1 t.2.2) := by exact_mod_cast hm
  have h2 : (0 : ℝ) ≤ tδ := by exact_mod_cast tδ_nonneg
  have h3 := mul_le_mul_of_nonneg_left exp_tU_le h1
  have h4 := mul_le_mul_of_nonneg_right h3 h2
  have hc' : ((MinvQ (clsOf t.1 t.2.1 t.2.2) * eThi * tδ : ℚ) : ℝ) ≤
      ((MQ (clsOf t.1 t.2.1 t.2.2) * Rerr : ℚ) : ℝ) := by exact_mod_cast hc
  push_cast at hc'
  linarith

/-! ### B10's `consistent_inl` at the paper's parameters -/

section Consistent

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The consistency of a degree class at `a_T`** (K2's field 41 on a degree class;
`thm:envelopes`(i), `cor:envelope-costs`, `lem:oct24:invariant-background`(v)): B10's
`consistent_inl` with the class-cost parameters of `CostData.lean`, `B = B^{ledger}`, and the
numerical gate `classCost ≤ C_n` proved (`paper_classCost_le`). It applies to any class data with
`N ⊆ paperN`, `C_n ≥ paperC n` on `N` and `B' ≥ B^{ledger}`; B10's `ClassData.paper` with
`C = paperC` has all three by `rfl`. *Hypotheses* (analytic): the background gate `hbg`, the
remainder bound `hρ`, and the price identities `harm`, `hυ0`, `hυ`. -/
theorem consistent_inl_paper {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (cd : ClassInputsPaper.ClassData D.CL) (hN : ∀ n ∈ cd.N, n ∈ paperN)
    (hC : ∀ n ∈ cd.N, paperC n ≤ cd.C n) (hBp : targetLedger.B ≤ cd.Bp)
    {Θ : Type} [Fintype Θ] (L : ℕ) (n : {n // n ∈ cd.N}) (wc u : Θ → ℝ)
    (ρ wt CX υ : Choice (D.CL.T L) → ℝ)
    (hbg : ∑ j, wc j * u j ≤ (paperκH n.1 * Real.exp paperU0 -
        (paperκH n.1 - paperκb n.1) * Real.exp paperTU) *
      ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω))
    (hρ : ∑ ω ∈ cd.clsSel L (.inl n), ρ ω ≤
      (paperM n.1 * paperRerr - paperMinv n.1 * Real.exp paperTU * paperTδ) *
          (∑ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω) +
        targetLedger.B * (∑ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω))
    (harm : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * CX ω = mono (cd.yarm L) (selMono ω))
    (hυ0 : ∀ ω ∈ cd.clsSel L (.inl n), 0 ≤ wt ω * υ ω * CX ω)
    (hυ : ∀ ω ∈ cd.clsSel L (.inl n), wt ω * υ ω * CX ω ≤
      mono (fun v => cd.ylead L v + cd.yrem L v) (selMono ω) - mono (cd.ylead L) (selMono ω)) :
    ∑ j, wc j * u j + ∑ ω ∈ cd.clsSel L (.inl n), ρ ω ≤
      ∑ ω ∈ cd.clsSel L (.inl n), cd.φ L ω :=
  consistent_inl cd L n wc u ρ wt CX υ hbg hρ harm hυ0 hυ hBp
    TargetLedger.targetLedger_bounds.B_nonneg
    ((paper_classCost_le (hN n.1 n.2)).trans (hC n.1 n.2))

end Consistent

end Sarkozy.ClassData

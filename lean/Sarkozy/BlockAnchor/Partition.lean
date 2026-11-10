module

public import Sarkozy.BlockAnchor.NonVacuity
public import Sarkozy.PartV.Construction

@[expose] public section

/-!
# The paper's partition of the fixed primes into prefix atoms

`paper/sections/18_design.tex`, `def:construction`(b); `def:record:exact-blocks` and
`def:record:upper-bands`(b) (V1's `PartV.MiddleBlock` and `PartV.UpperBlock`, whose partitions are
parameters in V1).

`IsPaperPartition blk` says that the block assignment `blk` of the fixed primes `𝒫₁ ∪ 𝒫₃` has the
paper's atoms:
- every square-clique prime `p ≡ 1 (4)` is an atom `{p}` of its own;
- every block containing a class-three prime consists exactly of the primes of one V1 middle block
  (budget `∑ log p ≤ 570`) or one V1 upper block (band budget `≤ 886`).

The partition itself (V1's greedy blocks and bands) is not constructed here; this is the property
every such partition has.

* `paperSel_prefix_atom`: the factor of `{p}` is `p^{2𝔪 a₀}` (`def:price`, the reading for `e_p`
  even);
* **`paperSel_class3_le`**: the factor of every block of class-three primes is
  `≤ e^{2a₀·886} ≤ 15/2`;
* **`toy_partition_L₀_le`**: the toy first stage of `NonVacuity.lean` at any such block has
  `L₀ ≤ anchorLedger.L₀`.
-/

open Finset

namespace Sarkozy.BlockAnchor

open Sarkozy.BlockFrame CancellationSteps

variable {Bk : Type} [Fintype Bk] [DecidableEq Bk]

/-- **The paper's prefix atoms** (`def:construction`(b)): square-clique singletons `{p}` for
`p ≡ 1 (4)`, and V1's middle and upper blocks for the class-three primes. -/
structure IsPaperPartition (blk : PaperJ0 → Bk) : Prop where
  prefix_singleton : ∀ i j : PaperJ0, i.1 % 4 = 1 → blk j = blk i → j = i
  class3_block : ∀ β : Bk, (∃ i : PaperJ0, blk i = β ∧ i.1 % 4 = 3) →
    (∃ M : PartV.MiddleBlock, ∀ i : PaperJ0, blk i = β ↔ i.1 ∈ M.primes) ∨
      (∃ U : PartV.UpperBlock, ∀ i : PaperJ0, blk i = β ↔ i.1 ∈ U.primes)

omit [Fintype Bk] in
/-- The coordinates of a block given by a finite set of primes: the factor is `e^{2a₀ ∑ log p}`
at most, if the primes are class three. -/
theorem blockLog_le_of_primes (blk : PaperJ0 → Bk) (β : Bk) (S : Finset ℕ)
    (hS : ∀ i : PaperJ0, blk i = β ↔ i.1 ∈ S) :
    ∑ i : BlockIdx blk β, Real.log (paperPP i.1) ≤ ∑ p ∈ S, Real.log p := by
  classical
  let g : BlockIdx blk β → ℕ := fun i => i.1.1
  have hinj : ∀ x ∈ (univ : Finset (BlockIdx blk β)), ∀ y ∈ (univ : Finset (BlockIdx blk β)),
      g x = g y → x = y := fun x _ y _ h => Subtype.ext (Subtype.ext h)
  have himg : (univ : Finset (BlockIdx blk β)).image g ⊆ S := by
    intro x hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact (hS i.1).mp i.2
  have h1 : ∑ i : BlockIdx blk β, Real.log (paperPP i.1) =
      ∑ x ∈ (univ : Finset (BlockIdx blk β)).image g, Real.log (x : ℝ) :=
    (Finset.sum_image (f := fun x : ℕ => Real.log (x : ℝ)) hinj).symm
  rw [h1]
  exact Finset.sum_le_sum_of_subset_of_nonneg himg (fun x _ _ => Real.log_natCast_nonneg x)

theorem paperEP_of_class3 (i : PaperJ0) (h3 : i.1 % 4 = 3) : paperEP i = 1 := by
  unfold paperEP
  have : i.1 % 4 ≠ 1 := by omega
  simp only [this, ↓reduceIte]

omit [Fintype Bk] in
/-- **Every block of class-three primes of a paper partition has factor `≤ 15/2`**: its primes have
`e_p = 1` and logarithmic length `≤ 570` (middle) or `≤ 886` (upper), so
`q_𝔟^{2a₀} ≤ e^{2a₀·886} ≤ 15/2` (`blockSel_le_exp`, `lem:record:local-domain`(ii)). -/
theorem paperSel_class3_le {blk : PaperJ0 → Bk} (hP : IsPaperPartition blk) (β : Bk)
    (hβ : ∃ i : PaperJ0, blk i = β ∧ i.1 % 4 = 3) : paperSel blk β ≤ 15 / 2 := by
  obtain ⟨S, hS, hcl, hbud⟩ : ∃ S : Finset ℕ, (∀ i : PaperJ0, blk i = β ↔ i.1 ∈ S) ∧
      (∀ p ∈ S, p % 4 = 3) ∧ ∑ p ∈ S, Real.log p ≤ 886 := by
    rcases hP.class3_block β hβ with ⟨M, hM⟩ | ⟨U, hU⟩
    · refine ⟨M.primes, hM, M.class3, M.budget.trans ?_⟩
      unfold PartV.middleBudget
      norm_num
    · refine ⟨U.primes, hU, U.class3, U.budget.trans ?_⟩
      exact_mod_cast U.bandBudget_le
  have h1 : ∀ i : BlockIdx blk β, paperEP i.1 = 1 := fun i =>
    paperEP_of_class3 i.1 (hcl _ ((hS i.1).mp i.2))
  rw [paperSel_eq]
  exact (blockSel_le_exp anchorDecay_nonneg one_le_paperPP blk β h1
    ((blockLog_le_of_primes blk β S hS).trans hbud)).trans exp_anchor_budget_le

omit [Fintype Bk] in
/-- The factor of a square-clique atom `{p}` of a paper partition is `p^{2𝔪 a₀}` (`def:price`,
read as `p^{e_p a}` for `e_p = 2𝔪` even). -/
theorem paperSel_prefix_atom {blk : PaperJ0 → Bk} (hP : IsPaperPartition blk) (i : PaperJ0)
    (h1 : i.1 % 4 = 1) :
    paperSel blk (blk i) =
      (i.1 : ℝ) ^ ((PartV.prefixExponent : ℝ) * Param.Params.anchorDecay) := by
  have : Subsingleton (BlockIdx blk (blk i)) :=
    ⟨fun x y => Subtype.ext ((hP.prefix_singleton i x.1 h1 x.2).trans
      (hP.prefix_singleton i y.1 h1 y.2).symm)⟩
  rw [paperSel_eq]
  unfold blockSel
  rw [Fintype.prod_subsingleton _ ⟨i, rfl⟩]
  have hep : paperEP i = PartV.prefixExponent := by
    unfold paperEP
    simp only [h1, ↓reduceIte]
  have hne : paperEP i ≠ 1 := by
    rw [hep]
    unfold PartV.prefixExponent PartV.digitPairs
    norm_num
  unfold coordSel
  simp only [hne, ↓reduceIte]
  rw [hep]
  rfl

/-- **`hL₀` is satisfiable at every block of class-three primes of a paper partition**: the toy
first stage with record mass `10⁻⁶` and sharp constant `1` there has `L₀ ≤ anchorLedger.L₀`. -/
theorem toy_partition_L₀_le {blk : PaperJ0 → Bk} (hP : IsPaperPartition blk)
    (R : TheoremCBlock.Reference paperM0 blk) (β₀ : Bk)
    (hβ : ∃ i : PaperJ0, blk i = β₀ ∧ i.1 % 4 = 3) :
    (toyFirstStage (p := paperTail) Param.Params.anchorDecay (paperSel blk) R β₀ (1 / 1000000) 1
      (by norm_num) zero_le_one).L₀ ≤ LedgerAnchor.anchorLedger.L₀ := by
  have hs1 := one_le_paperSel blk β₀
  have hs := paperSel_class3_le hP β₀ hβ
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

end Sarkozy.BlockAnchor

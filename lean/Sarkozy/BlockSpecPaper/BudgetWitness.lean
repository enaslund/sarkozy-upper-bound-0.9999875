module

public import Sarkozy.BlockSpecPaper.Main
public import Mathlib.Analysis.Complex.ExponentialBounds

@[expose] public section

/-!
# Non-vacuity of `PaperBudget`: a within-site rule with the budget

`PaperBudget cell` is a hypothesis on the within-site block rule. To show that it can be met, this
file gives an explicit rule, **not the paper's**: in each site, the class-three primes in
increasing order are grouped into consecutive blocks of `n_s = ⌊L_s / log Y_s⌋` primes, with
`L_s = 570` on a middle piece and `L_s = L_band(k)` on band `k`, and `Y_s` the end of the site
(the cells of `def:record:exact-blocks`(d) with a single cell per site). Every block then has
at most `n_s` primes, all `< Y_s`, so `∑ log p ≤ n_s log Y_s ≤ L_s` (`fixedCell_budget`).

The paper's rule (greedy blocks below `X_Ch`, `128 log₂(Y/x)` cells per piece, the recorded band
cardinalities) has finer cells and hence fewer blocks; its budget is V1's `greedy_log_budget` and
`cellBlock_log_budget`, given the recorded data.
-/

open Finset

namespace Sarkozy.BlockSpecPaper

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper

/-- The budget `L_s` of a site: `570` on a middle piece, the record's `L_band(k)` on band `k`. -/
def siteBudget : Site → ℕ
  | .inl _ => middleBudget
  | .inr k => (UpperRecords.CompletionData.record k).budget

/-- The block cardinality `n_s = ⌊L_s / log Y_s⌋` of a site. -/
noncomputable def siteCard (s : Site) : ℕ := ⌊(siteBudget s : ℝ) / Real.log (siteStop s)⌋₊

/-- The rank of `p` among the class-three primes of the site `s` below it. -/
noncomputable def siteRank (s : Site) (p : ℕ) : ℕ :=
  ((range p).filter fun q => q.Prime ∧ q % 4 = 3 ∧ siteStart s ≤ q).card

/-- **The explicit within-site rule**: the block index of `p` is `⌊rank / n_s⌋`. -/
noncomputable def fixedCell (p : ℕ) : ℕ := siteRank (siteOf p) p / siteCard (siteOf p)

theorem siteRank_lt {s : Site} {p p' : ℕ} (hp : p.Prime ∧ p % 4 = 3 ∧ siteStart s ≤ p)
    (hlt : p < p') : siteRank s p < siteRank s p' := by
  unfold siteRank
  apply card_lt_card
  refine ⟨fun q hq => ?_, fun h => ?_⟩
  · rw [mem_filter, mem_range] at hq ⊢
    exact ⟨hq.1.trans hlt, hq.2⟩
  · have hmem : p ∈ (range p').filter fun q => q.Prime ∧ q % 4 = 3 ∧ siteStart s ≤ q :=
      mem_filter.mpr ⟨mem_range.mpr hlt, hp⟩
    have := h hmem
    rw [mem_filter, mem_range] at this
    exact lt_irrefl _ this.1

/-- The rank is injective on the class-three primes of a site. -/
theorem siteRank_injOn {s : Site} {p p' : ℕ} (hp : p.Prime ∧ p % 4 = 3 ∧ siteStart s ≤ p)
    (hp' : p'.Prime ∧ p' % 4 = 3 ∧ siteStart s ≤ p') (h : siteRank s p = siteRank s p') :
    p = p' := by
  rcases lt_trichotomy p p' with hlt | heq | hgt
  · exact absurd h (siteRank_lt hp hlt).ne
  · exact heq
  · exact absurd h (siteRank_lt hp' hgt).ne'

/-- Every site ends at `P₄ = 2⁵¹²` or earlier. -/
theorem siteStop_le_P4 : ∀ s : Site, siteStop s ≤ P4
  | .inl i => by
      have h : pieceStop i ≤ P3 := by
        revert i
        unfold pieceStop pieceEnds P3
        decide +kernel
      exact h.trans P3_lt_P4.le
  | .inr k => by
      have h : ∀ k : Fin 310, (bandOf k).2 ≤ P4 := by decide +kernel
      exact h k

theorem two_le_siteStop (s : Site) : 2 ≤ siteStop s := by
  rcases s with i | k
  · have := (pieceStart_ge_Q3 i).trans (pieceStart_lt_pieceStop i).le
    unfold Q3 at this
    exact le_trans (by norm_num) this
  · have := (P3_le_bandStart k).trans (exists_band_lt k).le
    unfold P3 at this
    exact le_trans (by norm_num) this
where
  exists_band_lt (k : Fin 310) : (bandOf k).1 < (bandOf k).2 := by
    have h : ∀ k : Fin 310, (bandOf k).1 < (bandOf k).2 := by decide +kernel
    exact h k

/-- `log Y_s ≤ 512 log 2 < 355`. -/
theorem log_siteStop_lt (s : Site) : Real.log (siteStop s) < 355 := by
  have h1 : (siteStop s : ℝ) ≤ 2 ^ 512 := by
    have := siteStop_le_P4 s
    unfold P4 at this
    exact_mod_cast this
  have h0 : (0 : ℝ) < siteStop s := by
    have := two_le_siteStop s
    have h' : (0 : ℕ) < siteStop s := by omega
    exact_mod_cast h'
  have h2 : Real.log (siteStop s) ≤ 512 * Real.log 2 := by
    have h5 : Real.log ((2 : ℝ) ^ 512) = 512 * Real.log 2 := by
      rw [Real.log_pow]
      norm_num
    rw [← h5]
    exact Real.log_le_log h0 h1
  have h3 := Real.log_two_lt_d9
  norm_num at h3
  linarith

theorem log_siteStop_pos (s : Site) : 0 < Real.log (siteStop s) := by
  apply Real.log_pos
  have := two_le_siteStop s
  have h' : (1 : ℕ) < siteStop s := by omega
  exact_mod_cast h'

theorem budget_ge_550 : ∀ s : Site, (550 : ℝ) ≤ siteBudget s
  | .inl _ => by norm_num [siteBudget, middleBudget]
  | .inr k => by
      have := (UpperRecords.band_budget k).1
      unfold siteBudget
      exact_mod_cast this

/-- `n_s ≥ 1` on every site. -/
theorem one_le_siteCard (s : Site) : 1 ≤ siteCard s := by
  unfold siteCard
  rw [Nat.one_le_floor_iff, one_le_div (log_siteStop_pos s)]
  linarith [budget_ge_550 s, log_siteStop_lt s]

/-- `n_s log Y_s ≤ L_s`. -/
theorem siteCard_mul_log_le (s : Site) :
    (siteCard s : ℝ) * Real.log (siteStop s) ≤ siteBudget s := by
  have hl := log_siteStop_pos s
  have h := Nat.floor_le (div_nonneg (Nat.cast_nonneg (siteBudget s)) hl.le)
  calc (siteCard s : ℝ) * Real.log (siteStop s) ≤
        (siteBudget s : ℝ) / Real.log (siteStop s) * Real.log (siteStop s) :=
        mul_le_mul_of_nonneg_right h hl.le
    _ = siteBudget s := div_mul_cancel₀ _ hl.ne'

/-- **Every block of the explicit rule has at most `n_s` primes.** -/
theorem fixedCell_card_le (b : PaperBlock fixedCell) :
    Fintype.card {j : PaperJ0 // paperAtomMap (paperBlockOf fixedCell) j = .inr b} ≤
      siteCard (blockSite b) := by
  set s := blockSite b
  set n := siteCard s
  have hn : 0 < n := one_le_siteCard s
  -- every coordinate of the block has rank in `[m n, m n + n)`, `m = b.val.2`
  have hcoord : ∀ j : {j : PaperJ0 // paperAtomMap (paperBlockOf fixedCell) j = .inr b},
      siteOf j.1.1 = s ∧ siteRank s j.1.1 / n = b.val.2 := by
    intro j
    obtain ⟨_, hb⟩ := blockOf_of_coord j
    have h1 : b.val.1 = siteOf j.1.1 := by rw [hb]; rfl
    have h2 : b.val.2 = fixedCell j.1.1 := by rw [hb]; rfl
    refine ⟨h1.symm, ?_⟩
    rw [h2]
    unfold fixedCell
    rw [← h1]
    rfl
  have hcls : ∀ j : {j : PaperJ0 // paperAtomMap (paperBlockOf fixedCell) j = .inr b},
      j.1.1.Prime ∧ j.1.1 % 4 = 3 ∧ siteStart s ≤ j.1.1 := by
    intro j
    have hm : blockPrimes (paperBlockOf fixedCell) b j = j.1.1 :=
      paperM0_cls3 (blockOf_of_coord j).1
    have h3 := (blockPrimes_mod_ge b j).1
    have h4 := (mem_site j).1
    rw [hm] at h3 h4
    exact ⟨paperJ0_prime j.1, h3, h4⟩
  let f : {j : PaperJ0 // paperAtomMap (paperBlockOf fixedCell) j = .inr b} → Fin n :=
    fun j => ⟨siteRank s j.1.1 % n, Nat.mod_lt _ hn⟩
  have hf : Function.Injective f := by
    intro x y hxy
    have hmod : siteRank s x.1.1 % n = siteRank s y.1.1 % n := congrArg Fin.val hxy
    have hdiv : siteRank s x.1.1 / n = siteRank s y.1.1 / n := by
      rw [(hcoord x).2, (hcoord y).2]
    have hr : siteRank s x.1.1 = siteRank s y.1.1 := by
      rw [← Nat.div_add_mod (siteRank s x.1.1) n, ← Nat.div_add_mod (siteRank s y.1.1) n, hdiv,
        hmod]
    exact Subtype.ext (Subtype.ext (siteRank_injOn (hcls x) (hcls y) hr))
  simpa using Fintype.card_le_of_injective f hf

/-- **The explicit within-site rule satisfies the budget** (non-vacuity of `PaperBudget`). -/
theorem fixedCell_budget : PaperBudget fixedCell := by
  intro b
  have hsum : ∑ j, Real.log (blockPrimes (paperBlockOf fixedCell) b j) ≤
      siteBudget (blockSite b) := by
    have h1 : ∀ j, Real.log (blockPrimes (paperBlockOf fixedCell) b j) ≤
        Real.log (siteStop (blockSite b)) := by
      intro j
      have hlt := (mem_site j).2
      have hpos : (0 : ℝ) < blockPrimes (paperBlockOf fixedCell) b j := by
        have := (paperM0_block_prime (paperBlockOf fixedCell) j).pos
        exact_mod_cast this
      exact Real.log_le_log hpos (by exact_mod_cast hlt.le)
    calc ∑ j, Real.log (blockPrimes (paperBlockOf fixedCell) b j) ≤
          ∑ _j : {j : PaperJ0 // paperAtomMap (paperBlockOf fixedCell) j = .inr b},
            Real.log (siteStop (blockSite b)) := sum_le_sum fun j _ => h1 j
      _ = (Fintype.card {j : PaperJ0 // paperAtomMap (paperBlockOf fixedCell) j = .inr b} : ℝ) *
            Real.log (siteStop (blockSite b)) := by
          rw [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ (siteCard (blockSite b) : ℝ) * Real.log (siteStop (blockSite b)) :=
          mul_le_mul_of_nonneg_right (by exact_mod_cast fixedCell_card_le b)
            (log_siteStop_pos _).le
      _ ≤ siteBudget (blockSite b) := siteCard_mul_log_le _
  refine ⟨fun i hs => ?_, fun k hs => ?_⟩
  · have h := hsum
    rw [hs] at h
    exact h
  · have h := hsum
    rw [hs] at h
    exact h

/-- **The main statement with the explicit within-site rule** (`main_target_paper_block_B1_lemmas`
at `cell := fixedCell`, the budget discharged by `fixedCell_budget`): no partition data and no
combinatorial hypothesis remain, only the lemma forms of the analytic inputs and the sixteen Part V
obligations. `fixedCell` is **not** the paper's rule (it has single cells per site, hence more
blocks); whether the ledger obligations close for it is not checked. -/
theorem main_target_fixedCell (hWeil : Target.Weil)
    (hMovingRoot : Target.MovingRoot) (hFourCycle : Target.FourCycle)
    (hThetaSmallRR : Target.ThetaSmallRR) (hU : ∀ k, UpperBandLemma k)
    (hM : ∀ i, allpIndividual i = none → MiddleUniformLemma i)
    (hI : ∀ i u, allpIndividual i = some u → MiddleIndividualLemma i u)
    (O : B1FinalObligationsTarget fixedCell hWeil hMovingRoot hFourCycle
      (paperAnalyticInputs_of_lemmas fixedCell_budget hU hM hI)) :
    Target.SarkozyBound TargetLedger.targetSaving :=
  main_target_paper_block_B1_lemmas hWeil hMovingRoot hFourCycle hThetaSmallRR
    fixedCell fixedCell_budget hU hM hI O

end Sarkozy.BlockSpecPaper

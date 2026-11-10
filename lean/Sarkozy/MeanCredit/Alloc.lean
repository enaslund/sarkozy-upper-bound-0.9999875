module

public import Sarkozy.MeanCredit.Aggregate
public import Sarkozy.MainFinalF1b.ClassesB
public import Sarkozy.ClassData.AllocRoom

@[expose] public section

/-!
# The combined gate `AllocJ` from the completed residual series

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (the completion paragraph),
`prop:joint-upper-mean`; `paper/sections/11_comparison_proof.tex`, `cor:joint-closing`;
`paper/sections/32_four_routes_closing.tex`, `eq:final-joint-closing`, `cert:four-routes-closing`.

`AllocJB ED b` (field 33 of the class group of `main_goal_theta1k`) asks, at every scale `L`,
`63 (κ_L + ∑_j w_j u_j) − ∑_j b_j u_j ≤ 63 𝓔 − 64 Δ` with the ledger's `𝓔`, `Δ`. The paper proves it
in three steps, which are separated here:

1. **Booking** (`Booking`): the left side is a sum, over the terms of the record expansion at scale
   `L` (each counted once), of a residual coefficient `R(deg ω) ≥ 0` of the letter degree times the
   monomial. This is where the formal data must be the paper's comparison and mean coefficients,
   with the variance credit counted once. **`hbook_of_form`** proves it from the per-selection form
   of the formal data, at the formal objects (`Choice (D.CL.T L)`, `D.CL.π L`, `ED.κ`).
2. **Completion** (proved, `MeanCredit.completion_le`): repeated block labels enlarge the sum,
   giving the exponential series `∑_d R(d) ∏_l X_l^{d_l}/d_l!` in the letter totals. Monotone in
   the totals (`completedMono_le_of_totals`).
3. **Evaluation** (`SeriesBound R X M`): the completed series at the totals `X` is at most `M`.
   This is the paper's closed-form evaluation (`eq:final-joint-closing`), done by the harness; it
   is a statement about numbers only.

**`allocJB_of_booking`**: 1–3 with `M ≤ 63 𝓔^{ledger} − 64 Δ^{ledger}` give `AllocJB`.

**The upper allocation cannot be booked** (FA2 P3): a selection with nonempty upper support lies in
no class, so its booked coefficient is `63 B` with no mean subtraction (`hbook_of_form`'s `hR`), and
the completed series is the paper's *without* `Δ_u − R_u`. **`upperFree_room`** (kernel):
`63 𝓔_h − 64 Δ_mid^{ledger} + 12/5 ≤ 63 𝓔^{ledger} − 64 Δ^{ledger}`, where `𝓔_h` is the harness's
`𝓔` (upper end) and `Δ_mid^{ledger}` the ledger's middle allocations (below the harness's). So the
upper-free evaluation fits with spare `12/5` (`allocJB_of_booking_upperFree`). (RG, 7 November 2026:
at RB's package R the spare is about `2.51`, almost all from the ledger's slack on `A`; at E3's v2
ledger it was `0.1289`, and the price of not booking `Δ_u` was `64(Δ_u − R_u) = 0.19406` of the
room `0.32302`.)
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MeanCredit

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData
open Sarkozy.MainFinalF1b
open Sarkozy.TargetLedger (targetLedger)

/-! ## The evaluation of the completed series -/

/-- **The completed series is at most `M`** (the evaluation of `eq:final-joint-closing` at the
letter totals `X`): every partial sum of `∑_d R(d) ∏_l X_l^{d_l}/d_l!` is at most `M`. For
`R ≥ 0` this is the bound on the whole series. A statement about numbers only. -/
def SeriesBound {Λ : Type*} [Fintype Λ] (R : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (M : ℝ) : Prop :=
  ∀ Ds : Finset (Λ → ℕ), ∑ d ∈ Ds, R d * ∏ l, X l ^ d l / (d l).factorial ≤ M

section Totals

variable {J : Type*} [Fintype J] {T : J → Type*} [∀ b, Fintype (T b)]
  {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The completed monomial is monotone in the letter totals.** -/
theorem completedMono_le_of_totals (ℓ : Entry T → Λ) {π : ∀ b, T b → ChangeType → ℝ}
    (hπ : ∀ b t e, 0 ≤ π b t e) (X : Λ → ℝ) (hX : ∀ l, letterTotal ℓ π l ≤ X l)
    (d : Λ → ℕ) : completedMono ℓ π d ≤ ∏ l, X l ^ d l / (d l).factorial := by
  unfold completedMono
  refine prod_le_prod₀ (fun l _ => ?_) fun l _ => ?_
  · exact div_nonneg (pow_nonneg (sum_nonneg fun _ _ => hπ _ _ _) _) (Nat.cast_nonneg _)
  · have h0 : 0 ≤ letterTotal ℓ π l := sum_nonneg fun _ _ => hπ _ _ _
    exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 (hX l) _) (Nat.cast_nonneg _)

end Totals

/-! ## The booking and the gate -/

section Gate

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The booking at scale `L`** (`prop:joint-middle-mean`, `prop:joint-upper-mean`, "combine its
comparison coefficient `c` and retained mean coefficient `b` as `(63c − b)Z` first"): terms of a
record expansion (any atoms `J'`, records `T'`, nonnegative prices `π'`, letters `ℓ`, a finite set
`S` of choices), whose letter totals are at most `X`, such that the left side of the gate is at most
`∑_{ω ∈ S} R(deg ω) π'_ω`. The refined atoms allow e.g. the split of a skew price into raw arm and
remainder. *Hypothesis* (the identification of the formal data with the paper's coefficients). -/
structure Booking {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
    (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ) (Λ : Type) [Fintype Λ] [DecidableEq Λ]
    (R : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (L : ℕ) where
  J' : Type
  [J'Fintype : Fintype J']
  [J'DecEq : DecidableEq J']
  T' : J' → Type
  [T'Fintype : ∀ b, Fintype (T' b)]
  [T'DecEq : ∀ b, DecidableEq (T' b)]
  π' : ∀ b, T' b → ChangeType → ℝ
  π'_nonneg : ∀ b t e, 0 ≤ π' b t e
  ℓ : Entry T' → Λ
  S : Finset (Choice T')
  /-- The letter totals are at most `X` (the price bounds). -/
  hX : ∀ l, letterTotal ℓ π' l ≤ X l
  /-- The left side of the gate is the residual series over the terms, each booked once. -/
  hbook : 63 * (ED.κ L + ∑ j, ED.w L j * ED.u L j) - ∑ j, b L j * ED.u L j ≤
    ∑ ω ∈ S, R (deg ℓ ω) * monomial π' ω

attribute [instance] Booking.J'Fintype Booking.J'DecEq Booking.T'Fintype Booking.T'DecEq

/-- **The completed bound at one scale**: booking, completion (`completion_le`), monotonicity in the
totals and the evaluation give `63 (κ_L + ∑ w u) − ∑ b u ≤ M`. -/
theorem completed_le_of_booking {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassData D.CL} {ED : ClassEnergyDataB D cd} {b : ∀ L, ED.Θ L → ℝ}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {R : (Λ → ℕ) → ℝ} {X : Λ → ℝ} {M : ℝ}
    (hR : ∀ d, 0 ≤ R d) (hser : SeriesBound R X M) {L : ℕ} (Bo : Booking ED b Λ R X L) :
    63 * (ED.κ L + ∑ j, ED.w L j * ED.u L j) - ∑ j, b L j * ED.u L j ≤ M := by
  have h1 := Bo.hbook
  have h2 := completion_le Bo.ℓ Bo.π'_nonneg Bo.S (Bo.S.image (deg Bo.ℓ))
    (fun ω hω => mem_image_of_mem _ hω) R (fun d _ => hR d)
  have h3 : ∑ d ∈ Bo.S.image (deg Bo.ℓ), R d * completedMono Bo.ℓ Bo.π' d ≤
      ∑ d ∈ Bo.S.image (deg Bo.ℓ), R d * ∏ l, X l ^ d l / (d l).factorial :=
    sum_le_sum fun d _ => mul_le_mul_of_nonneg_left
      (completedMono_le_of_totals Bo.ℓ Bo.π'_nonneg X Bo.hX d) (hR d)
  have h4 := hser (Bo.S.image (deg Bo.ℓ))
  linarith

/-- **`AllocJB` from the booking and the evaluation** (`cor:joint-closing`,
`prop:joint-middle-mean`, `prop:joint-upper-mean`, `eq:final-joint-closing`). *Hypotheses*: the
booking at every scale, `R ≥ 0` (the residual gates), the evaluation `SeriesBound R X M`, and
`M ≤ 63 𝓔^{ledger} − 64 Δ^{ledger}`. -/
theorem allocJB_of_booking {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassData D.CL} (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ)
    (Λ : Type) [Fintype Λ] [DecidableEq Λ] (R : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (M : ℝ)
    (hR : ∀ d, 0 ≤ R d) (hser : SeriesBound R X M)
    (hM : M ≤ 63 * targetLedger.E - ledgerDelta targetLedger)
    (Bo : ∀ L, Booking ED b Λ R X L) : AllocJB ED b := fun L => by
  have h := completed_le_of_booking hR hser (Bo L)
  linarith

/-- **The booking from the per-selection form of the formal data**, at the formal objects
(`Choice (D.CL.T L)`, `D.CL.π L`, `ED.κ`). Each selection `ω` carries at most one labelled
diagonal `labS ω` with weight `wt`; the upper prices are the aggregated monomials (`hu`); the
residual of a class selection is a coefficient times its monomial (`hρ`); and the per-selection
residual coefficient (`63 B` off the classes, `63 r_ω` on them, plus `(63 w_j − b_j) wt_j` on its
label) is at most `R(deg ω)` (`hR`). -/
theorem hbook_of_form {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
    (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ) (L : ℕ)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (ℓ : Entry (D.CL.T L) → Λ) (R : (Λ → ℕ) → ℝ)
    [DecidableEq (ED.Θ L)]
    (labS : Choice (D.CL.T L) → Option (ED.Θ L)) (wt : ED.Θ L → ℝ)
    (r : Choice (D.CL.T L) → ℝ)
    (hres : ∀ j, 0 ≤ 63 * ED.w L j - b L j)
    (hu : ∀ j, ED.u L j ≤ agg (cd.sel L) labS wt (monomial (D.CL.π L)) j)
    (hρ : ∀ ω ∈ cd.sel L, cd.cls L ω ≠ none → ED.ρ L ω ≤ r ω * monomial (D.CL.π L) ω)
    (hR : ∀ ω ∈ cd.sel L, (if cd.cls L ω = none then 63 * D.B else 63 * r ω) +
      coefOf (fun j => 63 * ED.w L j - b L j) wt (labS ω) ≤ R (deg ℓ ω)) :
    63 * (ED.κ L + ∑ j, ED.w L j * ED.u L j) - ∑ j, b L j * ED.u L j ≤
      ∑ ω ∈ cd.sel L, R (deg ℓ ω) * monomial (D.CL.π L) ω := by
  have hπ : ∀ b t e, 0 ≤ D.CL.π L b t e := cd.π_nonneg L
  have hm : ∀ ω, 0 ≤ monomial (D.CL.π L) ω := monomial_nonneg hπ
  -- the diagonal part
  have e1 : 63 * ∑ j, ED.w L j * ED.u L j - ∑ j, b L j * ED.u L j =
      ∑ j, (63 * ED.w L j - b L j) * ED.u L j := by
    rw [mul_sum, ← sum_sub_distrib]
    exact sum_congr rfl fun j _ => by ring
  have h1 : ∑ j, (63 * ED.w L j - b L j) * ED.u L j ≤
      ∑ j, (63 * ED.w L j - b L j) * agg (cd.sel L) labS wt (monomial (D.CL.π L)) j :=
    sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hu j) (hres j)
  rw [sum_mul_agg] at h1
  -- the comparison constant
  have h2 : 63 * ED.κ L ≤ ∑ ω ∈ cd.sel L,
      (if cd.cls L ω = none then 63 * D.B else 63 * r ω) * monomial (D.CL.π L) ω := by
    unfold ClassEnergyDataB.κ
    rw [mul_sum]
    refine sum_le_sum fun ω hω => ?_
    by_cases hc : cd.cls L ω = none
    · simp only [hc, ↓reduceIte]
      ring_nf
      exact le_rfl
    · simp only [hc, ↓reduceIte]
      have := hρ ω hω hc
      nlinarith
  have h3 : ∑ ω ∈ cd.sel L, ((if cd.cls L ω = none then 63 * D.B else 63 * r ω) *
        monomial (D.CL.π L) ω +
      coefOf (fun j => 63 * ED.w L j - b L j) wt (labS ω) * monomial (D.CL.π L) ω) ≤
      ∑ ω ∈ cd.sel L, R (deg ℓ ω) * monomial (D.CL.π L) ω := by
    refine sum_le_sum fun ω hω => ?_
    rw [← add_mul]
    exact mul_le_mul_of_nonneg_right (hR ω hω) (hm ω)
  rw [sum_add_distrib] at h3
  linarith

/-! ## The ledger's room without the upper allocation -/

/-- The ledger's middle allocations `Δ_α + Δ_M + Δ_O + Δ_K` (each rounded down from the harness's
values at RB's point at the ledger's exponent `a_G = 71/10⁵`; RG). -/
def ledgerMid : ℚ := 4914747146 / 10 ^ 12 + 7740956387 / 10 ^ 12 + 3927490486 / 10 ^ 12 +
  405557461 / 10 ^ 12

/-- **The room of the upper-free evaluation** (kernel-checked): with the harness's `𝓔_h` (upper end)
and the ledger's middle allocations,
`63 𝓔_h − 64 Δ_mid + 12/5 ≤ 63 𝓔^{ledger} − 64 (Δ_mid + Δ_u − R_u)^{ledger}`. At RB's
package R (`a_G`, RG) the untrusted value of the spare is about `2.511`; RG states `12/5` (it was
`0.1289`, the spare `0.128960` at E3's v2 ledger). -/
theorem upperFree_room :
    63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + 12 / 5 ≤
      63 * targetLedger.E - ledgerDelta targetLedger := by
  have h := targetLedger_E_ge
  have hd : ledgerDelta targetLedger = 64 * ((0.004914747146 + 0.007740956387 + 0.003927490486 +
      0.000405557461) + 0.002446945672 - 0.000000186538) := rfl
  rw [hd]
  norm_num [TargetLedger.targetExpSplusInterval, TargetLedger.targetExpSminusInterval, harnessE,
    ledgerMid] at h ⊢
  linarith

/-- **`AllocJB` from the booking and the upper-free evaluation**: `allocJB_of_booking` at
`M = 63 𝓔_h − 64 Δ_mid^{ledger} + δ` with `δ ≤ 12/5` (`upperFree_room`; `0.1289` before RG). The
tolerance `δ` absorbs the excess of the formal totals over the harness's (about
`161.3 δ_A + 218.9 δ_S`, untrusted derivatives of `63 𝓔` at the harness point). -/
theorem allocJB_of_booking_upperFree {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassData D.CL} (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ)
    (Λ : Type) [Fintype Λ] [DecidableEq Λ] (R : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (δ : ℝ)
    (hδ : δ ≤ 12 / 5) (hR : ∀ d, 0 ≤ R d)
    (hser : SeriesBound R X (63 * (harnessE : ℝ) - 64 * (ledgerMid : ℝ) + δ))
    (Bo : ∀ L, Booking ED b Λ R X L) : AllocJB ED b :=
  allocJB_of_booking ED b Λ R X _ hR hser (by linarith [upperFree_room]) Bo

/-! ## The reduction loses nothing (non-vacuity) -/

/-- The atoms of the one-term expansion (none). -/
abbrev NoAtom : Empty → Type := fun _ => Empty

/-- The only choice on no atoms. -/
def noChoice : Choice NoAtom := fun b => Empty.elim b

theorem sum_choice_noAtom (f : Choice NoAtom → ℝ) :
    ∑ ω : Choice NoAtom, f ω = f noChoice := by
  refine sum_eq_single noChoice (fun ω _ hω => ?_) (fun h => (h (mem_univ _)).elim)
  exact (hω (funext fun b => Empty.elim b)).elim

/-- **The trivial booking**: one term (the empty choice on no atoms), letter `Unit`, coefficient
`M`, totals `0`. It books any left side at most `M`. -/
def bookingTrivial {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
    (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ) (M : ℝ) (L : ℕ)
    (hL : 63 * (ED.κ L + ∑ j, ED.w L j * ED.u L j) - ∑ j, b L j * ED.u L j ≤ M) :
    Booking ED b Unit (fun _ => M) (fun _ => 0) L where
  J' := Empty
  T' := NoAtom
  π' b := b.elim
  π'_nonneg b := b.elim
  ℓ _ := ()
  S := univ
  hX _ := by
    unfold letterTotal
    rw [univ_eq_empty, filter_empty, sum_empty]
  hbook := by
    rw [sum_choice_noAtom]
    have hm : monomial (fun b : Empty => b.elim) noChoice = 1 := by
      unfold monomial
      rw [univ_eq_empty, prod_empty]
    rw [hm, mul_one]
    exact hL

/-- The completed series of the trivial booking is `M` (only the degree `0` survives). -/
theorem seriesBound_trivial {M : ℝ} (hM : 0 ≤ M) :
    SeriesBound (fun _ : Unit → ℕ => M) (fun _ => 0) M := by
  intro Ds
  have e : ∀ d : Unit → ℕ, M * ∏ l, (0 : ℝ) ^ d l / (d l).factorial =
      if d = 0 then M else 0 := by
    intro d
    rw [Fintype.prod_unique]
    by_cases hd : d = 0
    · simp [hd]
    · have h1 : d () ≠ 0 := fun h0 => hd (funext fun u => by cases u; exact h0)
      simp [hd, zero_pow h1]
  rw [sum_congr rfl fun d _ => e d, sum_ite_eq']
  split_ifs
  · exact le_rfl
  · exact hM

/-- **`AllocJB` gives the booking and the evaluation back** (the trivial booking at
`M = 63 𝓔^{ledger} − 64 Δ^{ledger}`): the reduction `allocJB_of_booking` is as strong as `AllocJB`,
so it adds no hypothesis that `AllocJB` does not already contain. Its content is in discharging the
booking by the paper's coefficients (`hbook_of_form`) and the evaluation by the paper's series. -/
theorem booking_of_allocJB {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassData D.CL} (ED : ClassEnergyDataB D cd) (b : ∀ L, ED.Θ L → ℝ)
    (hA : AllocJB ED b) :
    Nonempty (∀ L, Booking ED b Unit (fun _ => 63 * targetLedger.E - ledgerDelta targetLedger)
      (fun _ => 0) L) ∧
    SeriesBound (fun _ : Unit → ℕ => 63 * targetLedger.E - ledgerDelta targetLedger)
      (fun _ => 0) (63 * targetLedger.E - ledgerDelta targetLedger) := by
  have hM : 0 ≤ 63 * targetLedger.E - ledgerDelta targetLedger := by
    have h := upperFree_room
    norm_num [harnessE, ledgerMid] at h
    linarith
  refine ⟨⟨fun L => bookingTrivial ED b _ L ?_⟩, seriesBound_trivial hM⟩
  have h := hA L
  linarith

end Gate

end Sarkozy.MeanCredit

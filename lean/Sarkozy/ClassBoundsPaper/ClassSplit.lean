module

public import Sarkozy.ClassBoundsPaper.Algebra

@[expose] public section

/-!
# Splitting the selection terms by classes, at energy level

The scalar step of `lem:record:record-expansion`(ii) with class bounds at **energy level**: the
terms of the selections in no class are bounded through (E1) by `(B + ε_E) π_ω Y + q_ω`, those of a
class `𝒞_i` by energies `Z_j` of labelled positive diagonals with weights `w_{ij}` plus an evaluated
residual `ρ_ω` (`thm:envelopes`(i), the envelope energies kept as energies, for the joint closing
`cor:joint-closing`). Then
`∑_ω |I_ω| ≤ ∑_j (∑_i w_{ij}) Z_j + κ Y + (ε_E + |ε|)(∑_ω π_ω) Y + ∑_ω (q_ω + r_ω)` with
`κ = ∑_{ω in no class} B π_ω + ∑_{ω in a class} ρ_ω` (`sum_abs_le_split`). All proved.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ClassBoundsPaper

variable {X ι Θ : Type*} [Fintype ι] [DecidableEq ι] [Fintype Θ]

/-- The sum over a finite set split into the selections in no class and the classes. -/
theorem sum_split_classes (sel : Finset X) (cls : X → Option ι) (g : X → ℝ) :
    ∑ ω ∈ sel, g ω = ∑ ω ∈ sel.filter (fun ω => cls ω = none), g ω +
      ∑ i, ∑ ω ∈ sel.filter (fun ω => cls ω = some i), g ω := by
  rw [← Finset.sum_fiberwise sel cls g, Fintype.sum_option]

/-- **The terms split by classes at energy level** (see the module docstring). -/
theorem sum_abs_le_split (sel : Finset X) (cls : X → Option ι) (I π ρ q r : X → ℝ)
    (wc : ι → Θ → ℝ) (Z : Θ → ℝ) {B εE ε Y : ℝ} (hπ : ∀ ω, 0 ≤ π ω) (hq : ∀ ω, 0 ≤ q ω)
    (hr : ∀ ω, 0 ≤ r ω) (hY : 0 ≤ Y) (hεE : 0 ≤ εE)
    (hnone : ∀ ω ∈ sel, cls ω = none → I ω ≤ (B + εE) * π ω * Y + q ω)
    (hcls : ∀ i, ∑ ω ∈ sel.filter (fun ω => cls ω = some i), I ω ≤
      ∑ j, wc i j * Z j + ∑ ω ∈ sel.filter (fun ω => cls ω = some i),
        ((ρ ω + ε * π ω) * Y + r ω)) :
    ∑ ω ∈ sel, I ω ≤ ∑ j, (∑ i, wc i j) * Z j +
      (∑ ω ∈ sel, (if cls ω = none then B * π ω else ρ ω)) * Y +
      (εE + |ε|) * (∑ ω ∈ sel, π ω) * Y + ∑ ω ∈ sel, (q ω + r ω) := by
  set S0 := sel.filter (fun ω => cls ω = none)
  set Si := fun i => sel.filter (fun ω => cls ω = some i)
  -- the no-class part
  have h0 : ∑ ω ∈ S0, I ω ≤ (∑ ω ∈ S0, B * π ω) * Y + εE * (∑ ω ∈ S0, π ω) * Y +
      ∑ ω ∈ S0, q ω := by
    calc ∑ ω ∈ S0, I ω ≤ ∑ ω ∈ S0, ((B + εE) * π ω * Y + q ω) :=
          sum_le_sum fun ω hω => hnone ω (mem_filter.mp hω).1 (mem_filter.mp hω).2
      _ = _ := by
          rw [sum_add_distrib, sum_mul, mul_sum, sum_mul]
          congr 1
          rw [← sum_add_distrib]
          exact sum_congr rfl fun ω _ => by ring
  -- the classes
  have hi : ∀ i, ∑ ω ∈ Si i, I ω ≤ ∑ j, wc i j * Z j + (∑ ω ∈ Si i, ρ ω) * Y +
      |ε| * (∑ ω ∈ Si i, π ω) * Y + ∑ ω ∈ Si i, r ω := by
    intro i
    refine (hcls i).trans ?_
    have e : ∑ ω ∈ Si i, ((ρ ω + ε * π ω) * Y + r ω) =
        (∑ ω ∈ Si i, ρ ω) * Y + ε * (∑ ω ∈ Si i, π ω) * Y + ∑ ω ∈ Si i, r ω := by
      simp only [add_mul, sum_add_distrib, Finset.mul_sum, Finset.sum_mul, mul_assoc]
    rw [e]
    have hπs : 0 ≤ (∑ ω ∈ Si i, π ω) * Y := mul_nonneg (sum_nonneg fun ω _ => hπ ω) hY
    have : ε * (∑ ω ∈ Si i, π ω) * Y ≤ |ε| * (∑ ω ∈ Si i, π ω) * Y := by
      rw [mul_assoc, mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self ε) hπs
    linarith
  have hI := sum_split_classes sel cls I
  have hκ := sum_split_classes sel cls (fun ω => if cls ω = none then B * π ω else ρ ω)
  have hκ0 : ∑ ω ∈ S0, (if cls ω = none then B * π ω else ρ ω) = ∑ ω ∈ S0, B * π ω :=
    sum_congr rfl fun ω hω => by rw [ite_eq_left (mem_filter.mp hω).2]
  have hκi : ∀ i, ∑ ω ∈ Si i, (if cls ω = none then B * π ω else ρ ω) = ∑ ω ∈ Si i, ρ ω :=
    fun i => sum_congr rfl fun ω hω => by
      rw [ite_eq_right (by rw [(mem_filter.mp hω).2]; exact Option.some_ne_none i)]
  have hπsplit := sum_split_classes sel cls π
  have hqr := sum_split_classes sel cls (fun ω => q ω + r ω)
  have hqr0 : ∑ ω ∈ S0, q ω ≤ ∑ ω ∈ S0, (q ω + r ω) :=
    sum_le_sum fun ω _ => by linarith [hr ω]
  have hqri : ∀ i, ∑ ω ∈ Si i, r ω ≤ ∑ ω ∈ Si i, (q ω + r ω) :=
    fun i => sum_le_sum fun ω _ => by linarith [hq ω]
  have hW : ∑ i, ∑ j, wc i j * Z j = ∑ j, (∑ i, wc i j) * Z j := by
    rw [sum_comm]
    exact sum_congr rfl fun j _ => by rw [sum_mul]
  have hsum_i : ∑ i, ∑ ω ∈ Si i, I ω ≤ ∑ i, (∑ j, wc i j * Z j + (∑ ω ∈ Si i, ρ ω) * Y +
      |ε| * (∑ ω ∈ Si i, π ω) * Y + ∑ ω ∈ Si i, r ω) := sum_le_sum fun i _ => hi i
  have e1 : ∑ i, (∑ j, wc i j * Z j + (∑ ω ∈ Si i, ρ ω) * Y +
      |ε| * (∑ ω ∈ Si i, π ω) * Y + ∑ ω ∈ Si i, r ω) =
      ∑ j, (∑ i, wc i j) * Z j + (∑ i, ∑ ω ∈ Si i, ρ ω) * Y +
        |ε| * (∑ i, ∑ ω ∈ Si i, π ω) * Y + ∑ i, ∑ ω ∈ Si i, r ω := by
    rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, hW]
    simp only [Finset.mul_sum, Finset.sum_mul]
  rw [e1] at hsum_i
  have hS0π : 0 ≤ ∑ ω ∈ S0, π ω := sum_nonneg fun ω _ => hπ ω
  have hSiπ : 0 ≤ ∑ i, ∑ ω ∈ Si i, π ω := sum_nonneg fun i _ => sum_nonneg fun ω _ => hπ ω
  have hab := abs_nonneg ε
  have hqrsum : ∑ ω ∈ S0, q ω + ∑ i, ∑ ω ∈ Si i, r ω ≤ ∑ ω ∈ sel, (q ω + r ω) := by
    rw [hqr]
    exact add_le_add hqr0 (sum_le_sum fun i _ => hqri i)
  rw [hI, hκ, hκ0, hπsplit, Finset.sum_congr rfl fun i _ => hκi i]
  nlinarith [mul_nonneg (mul_nonneg hεE hSiπ) hY, mul_nonneg (mul_nonneg hab hS0π) hY]

end Sarkozy.ClassBoundsPaper

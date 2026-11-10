module

public import Sarkozy.Allocation.Finite
public import Mathlib.Tactic.FinCases

/-!
# The selected finite allocation coefficients

The paper's resource ratio is 2.004317. In the required degree ranges, the
minimizing vertex has either all lower or all upper coordinates. The formulas
below choose that endpoint and check every competing vertex with exact
rational arithmetic. Their validity then extends to the full box by the
multiaffine theorem.
-/

@[expose] public section

namespace Sarkozy.Allocation

def resourceRatio : ℚ := 2004317 / 1000000
def resourceLower : ℚ := 1 / resourceRatio
def resourceUpper : ℚ := 1 / 2

def vertexProductQ (n k : ℕ) : ℚ :=
  (1 + resourceLower) ^ k * (1 + resourceUpper) ^ (n - k)

def vertexFirstQ (n k : ℕ) : ℚ :=
  (k : ℚ) * resourceLower + ((n : ℚ) - k) * resourceUpper

def vertexSecondQ (n k : ℕ) : ℚ :=
  ((vertexFirstQ n k) ^ 2 -
    ((k : ℚ) * resourceLower ^ 2 + ((n : ℚ) - k) * resourceUpper ^ 2)) / 2

def etaIndex (n : ℕ) : ℕ := if n ≤ 5 then 0 else n
def zetaIndex (n : ℕ) : ℕ := if n ≤ 3 then 0 else n

def etaCoefficient (n : ℕ) : ℚ :=
  (vertexProductQ n (etaIndex n) - 1) / vertexSecondQ n (etaIndex n)

def zetaCoefficient (n : ℕ) : ℚ :=
  vertexProductQ n (zetaIndex n) / vertexFirstQ n (zetaIndex n)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem eta_vertex_certificate : ∀ n : Fin 11, 2 ≤ n.val → ∀ k : Fin (n.val + 1),
    etaCoefficient n.val * vertexSecondQ n.val k.val ≤ vertexProductQ n.val k.val - 1 := by
  intro n hn k
  fin_cases n <;> fin_cases k <;> first
    | omega
    | norm_num [etaCoefficient, etaIndex, vertexProductQ, vertexFirstQ, vertexSecondQ,
        resourceLower, resourceUpper, resourceRatio]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
theorem zeta_vertex_certificate : ∀ n : Fin 10, 1 ≤ n.val → ∀ k : Fin (n.val + 1),
    zetaCoefficient n.val * vertexFirstQ n.val k.val ≤ vertexProductQ n.val k.val := by
  intro n hn k
  fin_cases n <;> fin_cases k <;> first
    | omega
    | norm_num [zetaCoefficient, zetaIndex, vertexProductQ, vertexFirstQ,
        resourceLower, resourceUpper, resourceRatio]

theorem cast_vertexProduct (n k : ℕ) :
    (vertexProductQ n k : ℝ) = vertexProduct n k resourceLower resourceUpper := by
  simp [vertexProductQ, vertexProduct]

theorem cast_vertexFirst (n k : ℕ) :
    (vertexFirstQ n k : ℝ) = vertexFirst n k resourceLower resourceUpper := by
  simp [vertexFirstQ, vertexFirst]

theorem cast_vertexSecond (n k : ℕ) :
    (vertexSecondQ n k : ℝ) = vertexSecond n k resourceLower resourceUpper := by
  simp [vertexSecondQ, vertexSecond, cast_vertexFirst]

/-- The sharper finite second-degree coefficients used by the joint mean. -/
theorem eta_selected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 2 ≤ Fintype.card ι) (hn' : Fintype.card ι ≤ 10)
    {z : ι → ℝ} (hz : ∀ i, (resourceLower : ℝ) ≤ z i ∧ z i ≤ resourceUpper) :
    (etaCoefficient (Fintype.card ι) : ℝ) * secondSum z ≤ onePlusProduct z - 1 := by
  apply second_allocation_of_vertices
    (by norm_num [resourceLower, resourceUpper, resourceRatio]) ?_ hz
  intro k hk
  have h := eta_vertex_certificate ⟨Fintype.card ι, by omega⟩ hn
    ⟨k, by change k < Fintype.card ι + 1; omega⟩
  have hc : (etaCoefficient (Fintype.card ι) : ℝ) * (vertexSecondQ (Fintype.card ι) k : ℝ) ≤
      (vertexProductQ (Fintype.card ι) k : ℝ) - 1 := by exact_mod_cast h
  simpa only [cast_vertexProduct, cast_vertexSecond] using hc

/-- The sharper finite first-degree coefficients used by the joint mean. -/
theorem zeta_selected {ι : Type*} [Fintype ι] [DecidableEq ι]
    (hn : 1 ≤ Fintype.card ι) (hn' : Fintype.card ι ≤ 9)
    {z : ι → ℝ} (hz : ∀ i, (resourceLower : ℝ) ≤ z i ∧ z i ≤ resourceUpper) :
    (zetaCoefficient (Fintype.card ι) : ℝ) * firstSum z ≤ onePlusProduct z := by
  apply first_allocation_of_vertices
    (by norm_num [resourceLower, resourceUpper, resourceRatio]) ?_ hz
  intro k hk
  have h := zeta_vertex_certificate ⟨Fintype.card ι, by omega⟩ hn
    ⟨k, by change k < Fintype.card ι + 1; omega⟩
  have hc : (zetaCoefficient (Fintype.card ι) : ℝ) * (vertexFirstQ (Fintype.card ι) k : ℝ) ≤
      (vertexProductQ (Fintype.card ι) k : ℝ) := by exact_mod_cast h
  simpa only [cast_vertexProduct, cast_vertexFirst] using hc

end Sarkozy.Allocation

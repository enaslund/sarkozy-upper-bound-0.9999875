module

public import Sarkozy.Kernel.FiniteKernel

@[expose] public section

/-!
# Kernel library: `UniformRates` (adapted from OpenAI)

This module is adapted, with minimal changes, from
`lean/OAI/Combinatorics/SquareDifference/UniformRates.lean` of OpenAI's math
repository (revision `1581d4cbdd69a0faf34b2089614fe2a814316a6a`, Apache
License 2.0; see `LICENSE.openai` and `NOTICES.md`). It belongs to the
dependency chain of the actual-square kernel estimate (paper,
`prop:record:kernel20`, Appendix C).

Changes: the namespace `OAI.SquareDifference` is renamed `Sarkozy.Kernel` and
the explicit module header is added; no proof needed changes for the pinned
Lean/mathlib versions. Declarations of the upstream file outside the dependency
closure of this project's kernel theorems were removed (the closure was computed
from the compiled proof terms); the remaining declarations are verbatim. The
import chain is the upstream linear chain restricted to the kernel files
(upstream `PrimeGauss.lean` imported `ScaleTransfer.lean`; here it imports
mathlib only, which suffices).
-/

namespace Sarkozy

section
open Finset
open scoped ComplexConjugate BigOperators

namespace Kernel

open Finset

section GridModel

variable {I : Type*} [Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [∀i, Fact (p i).Prime] (hinj : Function.Injective p)

include hinj

omit [DecidableEq I] [∀i, Fact (p i).Prime] in
lemma primary_cover_of_prime_support (q : ℕ) (hq : q≠0)
    (hs : ∀r, r.Prime → r∣q → ∃i,p i=r) : q∣∏i,primaryModulus q (p i) := by
  classical
  have h := dvd_primaryModulus_product q hq (univ.image p) (by
    intro r hr
    obtain ⟨i,hi⟩ := hs r (Nat.mem_primeFactors.mp hr).1 (Nat.mem_primeFactors.mp hr).2.1
    exact mem_image.mpr ⟨i,mem_univ _,hi⟩)
  rwa [prod_image (fun _ _ _ _ h => hinj h)] at h

variable (R : Finset I) (c : ∀i,ZMod (p i))

end GridModel

end Kernel

open Filter

open scoped Topology

namespace Kernel

lemma kernel_rate_log (n T : ℝ) (hn : 1≤n) (hT : 0<T)
    (hTn : T≤2*n^((7:ℝ)/8)) :
    1+Real.log T ≤18*n^((1:ℝ)/16) := by
  have hn0 : 0<n := by linarith
  have hn1 : 1≤n^((1:ℝ)/16) := Real.one_le_rpow hn (by norm_num)
  have hlog : Real.log n≤16*n^((1:ℝ)/16) := by
    simpa [div_eq_mul_inv,mul_comm] using Real.log_le_rpow_div hn0.le (show 0<(1:ℝ)/16 by norm_num)
  have hl2 : Real.log 2≤1 := by
    simpa only [show (2:ℝ)-1=1 by norm_num] using Real.log_le_sub_one_of_pos (show 0<(2:ℝ) by norm_num)
  have hh := Real.log_le_log hT hTn
  rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hn0 _).ne', Real.log_rpow hn0] at hh
  nlinarith [Real.log_nonneg hn]

lemma natural_sqrt_bounds (N : ℕ) (hN : 1≤N) :
    1≤N.sqrt ∧ N.sqrt^2≤N ∧ N<(N.sqrt+1)^2 ∧ (N.sqrt:ℝ)≤(N:ℝ)^((1:ℝ)/2) := by
  refine ⟨Nat.sqrt_pos.mpr (by omega),Nat.sqrt_le' N,Nat.lt_succ_sqrt' N,?_⟩
  rw [← Real.sqrt_eq_rpow]
  apply (Real.le_sqrt (Nat.cast_nonneg _) (Nat.cast_nonneg _)).mpr
  exact_mod_cast Nat.sqrt_le' N

end Kernel

namespace Kernel

open Finset

section UniformFinal

variable {I : Type*} [instFintypeI : Fintype I] [instDecidableEqI : DecidableEq I]
  (p : I → ℕ) [instFactNatPrimepi : ∀i, Fact (p i).Prime]
  (R : Finset I) (c : ∀i,ZMod (p i))

lemma rootProduct_le_squareModulus {I : Type*}
    [Fintype I]
    [DecidableEq I]
    (p : I → ℕ)
    [∀ (i : I), Fact (Nat.Prime (p i))]
    (R : Finset I) : (∏i∈R,p i)≤rootSquareModulus p R := by
  apply Finset.prod_le_prod
  intro i _
  split_ifs with h
  · omega
  · exact le_rfl

end UniformFinal

end Kernel

open Finset Complex

open scoped BigOperators ComplexConjugate

end

end Sarkozy

module

public import Sarkozy.DLK.Basic
public import Sarkozy.Spectral.GlueMatching

/-!
# The consumers of the four-cycle bound, with `thm:dl:K` as the hypothesis

`Extraction.FourCycleBound p` (`cor:dl:normalized`(a), `a = b = 2`) was a hypothesis of WP-FI's
`lem:matching:kernel`(b) (`Extraction/KernelTwoCycles.lean`) and of WP-A's matching bound
`lem:push:localvariance`(b)(i) (`Spectral/GlueMatching.lean`). Here it is discharged by
`DLK.fourCycleBound` from the literature input `Target.FourCycle` (`thm:dl:K`, H6), for every odd
prime `p`; the statements are otherwise those of the original theorems.

* `witnessKernel_rectangle_opBound_of_fourCycle`: the complete rectangle (`rem:extraction-kernels`).
* `blockWitnessKernel_opBound_of_fourCycle`: `lem:matching:kernel`(b), sorted-block form.
* `witnessKernel_opBound_twoCycles_of_fourCycle`, `..._injective_of_fourCycle`:
  `lem:matching:kernel`(b), general form (strongly connected components of at most two vertices).
* `glue_matching_twoCycles_of_fourCycle`: `lem:push:localvariance`(b)(i), any number of two-vertex
  components.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DLK

open Sarkozy Sarkozy.Influence Sarkozy.Extraction

variable {p : ℕ} [Fact p.Prime]

/-- **The complete rectangle** (`rem:extraction-kernels`; `cor:dl:normalized`(a), `a = b = 2`),
from `thm:dl:K`: on the pairs with distinct coordinates the kernel `∏_{a,b ≤ 2} χ(ς_{ab}(y_b - x_a))`
has `ℓ²` norm at most `2 √p²`, i.e. `2r²` for uniform probability. -/
theorem witnessKernel_rectangle_opBound_of_fourCycle (hDLK : Target.FourCycle) (hp2 : p ≠ 2)
    {ς : Fin 2 → Fin 2 → ZMod p} (hς : ∀ a b, ς a b = 1 ∨ ς a b = -1) :
    OpBound (univ.filter (fun x : Fin 2 → ZMod p => x 0 ≠ x 1))
      (univ.filter (fun x : Fin 2 → ZMod p => x 0 ≠ x 1)) (witnessKernel univ ς)
      (2 * Real.sqrt p ^ 2) :=
  witnessKernel_rectangle_opBound hp2 (fourCycleBound hDLK hp2) hς

/-- **`lem:matching:kernel`(b), sorted-block form**, from `thm:dl:K` (`Target.FourCycle`) in
place of the hypothesis `FourCycleBound p`: the block `R × C` of the witness kernel has `ℓ²`
operator norm at most `2^β √p^k` (`2^β r^k` for uniform probability). -/
theorem blockWitnessKernel_opBound_of_fourCycle (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {k : ℕ}
    (D : BlockWitness (p := p) k) {R C : Finset (Fin k → ZMod p)}
    (hR : ∀ x ∈ R, ∀ i l, i ≠ l → D.blk i = D.blk l → x i ≠ x l)
    (hC : ∀ y ∈ C, ∀ i l, i ≠ l → D.blk i = D.blk l → y i ≠ y l) :
    OpBound R C (witnessKernel D.pairs D.sign) (2 ^ D.numTwo * Real.sqrt p ^ k) :=
  blockWitnessKernel_opBound hp2 (fourCycleBound hDLK hp2) D hR hC

/-- **`lem:matching:kernel`(b)**, from `thm:dl:K` (`Target.FourCycle`) in place of the hypothesis
`FourCycleBound p`. Let `𝒦 ⊆ {1, …, k}²` contain the diagonal, let `ς = ±1` on `𝒦`, and suppose
that every strongly connected component of `D_𝒦` has at most two vertices, `β` of them two. For
sets `R`, `C` of tuples injective on the two-vertex components, the block `R × C` of the witness
kernel has `ℓ²` operator norm at most `2^β √p^k`, i.e. `‖P_out T_𝒦 P_in‖ ≤ 2^β r^k` for uniform
probability. -/
theorem witnessKernel_opBound_twoCycles_of_fourCycle (hDLK : Target.FourCycle) (hp2 : p ≠ 2)
    {k : ℕ} {𝒦 : Finset (Fin k × Fin k)} {ς : Fin k → Fin k → ZMod p} (h𝒦 : ∀ i, (i, i) ∈ 𝒦)
    (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) {R C : Finset (Fin k → ZMod p)}
    (hR : ∀ x ∈ R, ∀ i l, i ≠ l → twoCycleMutual 𝒦 i l → x i ≠ x l)
    (hC : ∀ y ∈ C, ∀ i l, i ≠ l → twoCycleMutual 𝒦 i l → y i ≠ y l) :
    OpBound R C (witnessKernel 𝒦 ς) (2 ^ twoCycleCount 𝒦 * Real.sqrt p ^ k) :=
  witnessKernel_opBound_twoCycles hp2 (fourCycleBound hDLK hp2) h𝒦 hς hcard hR hC

/-- **`lem:matching:kernel`(b) for the injective tuples**, from `thm:dl:K` (`Target.FourCycle`):
`‖P_out T_𝒦 P_in‖_{ℓ²} ≤ 2^β √p^k`, i.e. `≤ 2^β r^k` for uniform probability. -/
theorem witnessKernel_opBound_twoCycles_injective_of_fourCycle (hDLK : Target.FourCycle)
    (hp2 : p ≠ 2) {k : ℕ} {𝒦 : Finset (Fin k × Fin k)} {ς : Fin k → Fin k → ZMod p}
    (h𝒦 : ∀ i, (i, i) ∈ 𝒦) (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcard : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2) :
    OpBound (univ.filter (fun x : Fin k → ZMod p => Function.Injective x))
      (univ.filter (fun x : Fin k → ZMod p => Function.Injective x))
      (witnessKernel 𝒦 ς) (2 ^ twoCycleCount 𝒦 * Real.sqrt p ^ k) :=
  witnessKernel_opBound_twoCycles_injective hp2 (fourCycleBound hDLK hp2) h𝒦 hς hcard

/-- **The matching bound with two-vertex components** (`lem:push:localvariance`(b)(i), any `b`),
from `thm:dl:K` (`Target.FourCycle`) in place of the hypothesis `FourCycleBound p`:
`|∑_{x ∈ R, y ∈ C} (∏_i ρ_i(x_i)) a(x) K(x, y) b(y) ∏_l σ_l(y_l)| ≤
2^β √p^k (∏_i ‖ρ_i‖²)^{1/2} (∏_l ‖σ_l‖²)^{1/2}` (counting norms), i.e. `2^β r^k ∏ ‖ρ_i‖_{L²}`. -/
theorem glue_matching_twoCycles_of_fourCycle (hDLK : Target.FourCycle) (hp2 : p ≠ 2) {k : ℕ}
    {𝒦 : Finset (Fin k × Fin k)} {ς : Fin k → Fin k → ZMod p} (hdiag : ∀ i, (i, i) ∈ 𝒦)
    (hς : ∀ e ∈ 𝒦, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcomp : ∀ i, (twoCycleComponent 𝒦 i).card ≤ 2)
    {R C : Finset (Fin k → ZMod p)}
    (hR : ∀ x ∈ R, ∀ i l, i ≠ l → twoCycleMutual 𝒦 i l → x i ≠ x l)
    (hC : ∀ y ∈ C, ∀ i l, i ≠ l → twoCycleMutual 𝒦 i l → y i ≠ y l)
    (ρ σ : Fin k → ZMod p → ℝ) (a b : (Fin k → ZMod p) → ℝ) (ha : ∀ x, |a x| ≤ 1)
    (hb : ∀ y, |b y| ≤ 1) :
    |∑ x ∈ R, ∑ y ∈ C, ((∏ i, ρ i (x i)) * a x) * witnessKernel 𝒦 ς x y *
        (b y * ∏ l, σ l (y l))| ≤
      2 ^ twoCycleCount 𝒦 * Real.sqrt p ^ k * Real.sqrt (∏ i, ∑ t, ρ i t ^ 2) *
        Real.sqrt (∏ l, ∑ t, σ l t ^ 2) :=
  Spectral.glue_matching_twoCycles hp2 (fourCycleBound hDLK hp2) hdiag hς hcomp hR hC ρ σ a b
    ha hb

end Sarkozy.DLK

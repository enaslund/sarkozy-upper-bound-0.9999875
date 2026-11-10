module

public import Sarkozy.Extraction.CoverRows
public import Sarkozy.Extraction.CompressedPartition
public import Sarkozy.Influence.OpBound

@[expose] public section

/-!
# Grouped extraction: the data (`lem:matching:extractionk`, `def:extraction:records`)

`paper/sections/16_extraction.tex`, `subsec:extraction:extraction`. The objects shared by the
files of `ExtractionK/`, in the formal setting of `Extraction/CoverRows.lean`: a finite field `F`
(`F = 𝔽_p` in the paper) with `q = |F|` elements, `χ = quadraticChar F`, `r = q^{-1/2}`, the half
graph `G⁺` an oriented graph `G` on a finite type `U` (`U⁺`), cross signs `ς : U → U → ℤ`.
The two labellings `x, x'` of a pair live on two copies `X`, `Z` of `U⁺`; a cross pair
`e = (a, b)` has its `x`-endpoint `a` and its `x'`-endpoint `b`.

* `chiPair ς e x x'` is `χ_e(x, x') = χ(ς_{ab}(x'_b - x_a))`.
* `classKer ς P Fr x x' = ∏_{e ∈ P} χ_e ∏_{e ∈ Fr} (1 + χ_e)`, the kernel `∑_{S ∈ 𝒞} χ_S` of a
  class `𝒞 = 𝒞(P, A)` with free pairs `Fr` (Step 1 of the proof, `sum_cls_eq_classKer` in
  `Grouped.lean`).
* `restr S x` is the labelling `x` restricted to `S` (extended by `0`); `partLab G S` is the set of
  labellings of `S` (zero outside `S`, injective with the edge conditions inside `S`), i.e.
  `Inj_p(G⁺[S])`; `injTuples V` is the set of injective tuples on `V` (zero outside `V`).
* `rectKer ς P V W v w = ∏_{(a,b) ∈ P ∩ (V × W)} χ(ς_{ab}(w_b - v_a))`, the kernel `𝖶` of the
  present rectangle pairs.
* Integrated vertices (`def:extraction:records`, `u ∈ U_x`): with a global order `ord` of the
  `x`-copy in which `U_x` comes last, `ordT G ord u = t_u` (the `G⁺`-neighbours of `u` earlier in
  the order), `intH Fr u = H_u = {b : (u, b) ∈ Fr}`, `intS = s_u = t_u + h_u`, `intExp` the
  exponent `c^U(u, b) - [b ∈ H_u]`, `intNum` the numerator of `F_u`,
  `1 + e_{s_u}(q, n) + r² 2^{s_u} ∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]}`, and `intF = F_u`.
* `kappaFixed`: `κ^f`, the number of merges `(i, b)` at the vertices `u ∈ U_x` with `i ∉ U_x` a
  `G⁺`-neighbour of `u`, `b ∈ H_u` and `x_i = c'_b` (Step 6).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

section Defs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `χ_e(x, x') = χ(ς_{ab}(x'_b - x_a))` for `e = (a, b)`. -/
noncomputable def chiPair (ς : U → U → ℤ) (e : U × U) (x x' : U → F) : ℝ :=
  (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ)

/-- The kernel of a class `𝒞(P, A)` with free pairs `Fr`:
`∑_{S ∈ 𝒞} χ_S = ∏_{e ∈ P} χ_e ∏_{e ∈ Fr} (1 + χ_e)`. -/
noncomputable def classKer (ς : U → U → ℤ) (P Fr : Finset (U × U)) (x x' : U → F) : ℝ :=
  (∏ e ∈ P, chiPair ς e x x') * ∏ e ∈ Fr, (1 + chiPair ς e x x')

/-- The restriction of `x` to `S`, extended by `0`. -/
def restr (S : Finset U) (x : U → F) : U → F := fun u => if u ∈ S then x u else 0

variable (F) in
/-- The labellings of `S` (`Inj_p(G⁺[S])`), extended by `0`: zero outside `S`, injective on `S`
and satisfying the edge conditions inside `S`. -/
noncomputable def partLab (G : OrientedGraph U) (S : Finset U) : Finset (U → F) := by
  classical exact univ.filter fun c => (∀ u, u ∉ S → c u = 0) ∧ Feasible F G S c

variable (F) in
/-- The injective tuples on `V`, extended by `0`. -/
noncomputable def injTuples (V : Finset U) : Finset (U → F) := by
  classical exact univ.filter fun v => (∀ u, u ∉ V → v u = 0) ∧
    ∀ a ∈ V, ∀ b ∈ V, v a = v b → a = b

/-- The kernel `𝖶(v, w) = ∏_{(a,b) ∈ P ∩ (V × W)} χ(ς_{ab}(w_b - v_a))` of the present
rectangle pairs. -/
noncomputable def rectKer (ς : U → U → ℤ) (P : Finset (U × U)) (V W : Finset U)
    (v w : U → F) : ℝ :=
  ∏ e ∈ P.filter (fun e => e.1 ∈ V ∧ e.2 ∈ W), chiPair ς e v w

/-- `t_u`: the number of `G⁺`-neighbours of `u` earlier in the order `ord`. -/
noncomputable def ordT (G : OrientedGraph U) (ord : U → ℕ) (u : U) : ℕ :=
  coverRowT G univ ord u

/-- The free partners `H_u = {b : (u, b) ∈ Fr}` of an integrated vertex `u ∈ U_x`. -/
def intH (Fr : Finset (U × U)) (u : U) : Finset U := univ.filter fun b => (u, b) ∈ Fr

/-- `s_u = t_u + h_u`. -/
noncomputable def intS (G : OrientedGraph U) (ord : U → ℕ) (Fr : Finset (U × U)) (u : U) : ℕ :=
  ordT G ord u + (intH Fr u).card

/-- The exponent `c^U(u, b) - [b ∈ H_u]` (an integer). -/
def intExp (G : OrientedGraph U) (ς : U → U → ℤ) (Fr : Finset (U × U)) (u b : U) : ℤ :=
  (rowsCU G ς u b : ℤ) - if b ∈ intH Fr u then 1 else 0

/-- The numerator of the vertex factor `F_u` of an integrated vertex `u ∈ U_x`
(`def:extraction:records`):
`1 + e_{s_u}(q, n) + r² 2^{s_u} ∑_{b ∈ C_z} 2^{c^U(u,b) - [b ∈ H_u]}`, `r = q^{-1/2}`. -/
noncomputable def intNum (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : ℝ :=
  1 + coarseError (intS G ord Fr u) q n +
    (Real.sqrt q)⁻¹ ^ 2 * 2 ^ intS G ord Fr u * ∑ b ∈ Cz, (2 : ℝ) ^ intExp G ς Fr u b

/-- The vertex factor `F_u` of an integrated vertex `u ∈ U_x` (`def:extraction:records`). -/
noncomputable def intF (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) (ord : U → ℕ)
    (Fr : Finset (U × U)) (Cz : Finset U) (u : U) : ℝ :=
  intNum G ς q n ord Fr Cz u / (1 - coarseError (ordT G ord u) q n)

/-- `κ^f`: the merges `(i, b)` at the integrated vertices `u ∈ U_x` with a fixed label, i.e.
`i ∉ U_x` a `G⁺`-neighbour of `u`, `b ∈ H_u` and `x_i = c'_b` (Step 6). -/
def kappaFixed (G : OrientedGraph U) (Fr : Finset (U × U)) (Ux : Finset U) (x c' : U → F) :
    ℕ :=
  ∑ u ∈ Ux, ∑ i ∈ univ.filter (fun i => i ∉ Ux ∧ ((i, u) ∈ G.E ∨ (u, i) ∈ G.E)),
    ∑ b ∈ intH Fr u, if x i = c' b then 1 else 0

end Defs

end Sarkozy.ExtractionK

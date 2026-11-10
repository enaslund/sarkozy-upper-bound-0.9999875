module

public import Sarkozy.ExtractionK.Defs
public import Sarkozy.Extraction.KernelTwoCycles

@[expose] public section

/-!
# The kernel hypothesis of the grouped extraction (`lem:matching:kernel` for `𝖶`)

`paper/sections/16_extraction.tex`, `lem:matching:extractionk`. The theorem assumes that the
kernel `𝖶(v, w) = ∏_{(a,b) ∈ P ∩ (V × W)} χ(ς_{ab}(w_b - v_a))` of the present rectangle pairs
(`rectKer`), compressed to injective tuples, has norm at most `c_ker r^k` for uniform
probability, and notes that `lem:matching:kernel` gives `c_ker = 2^{β(𝒞)}` when every strongly
connected component of the witness digraph `D_𝒞` has at most two vertices. This file proves
that remark, over `F = 𝔽_p` (`ZMod p`), in the `ℓ²` (counting) normalization of `OpBound`:
the block `injTuples V × injTuples W` of `rectKer` has norm at most `2^β √p^k`, which is
`2^β r^k` for uniform probability.

* `witnessIdx P w = 𝒦 = {(i, l) : (j_i, k_l) ∈ P}` for a witness `w = ((j_1, k_1), …, (j_k, k_k))`;
  its digraph `D_𝒦` is the witness digraph `D_𝒞` of `def:extraction:witness`(b)
  (`witnessIdx_arc_iff`), so `twoCycleCount (witnessIdx P w)` is `β(𝒞)`, and it contains the
  diagonal (`witnessIdx_diag`).
* `rectKer_eq_witnessKernel`: `𝖶(v, w') = T_𝒦(v ∘ j, w' ∘ k)`, the witness kernel of
  `lem:matching:kernel` with the signs `ς_{il} = ς_{j_i k_l}`.
* `rectKer_opBound_twoCycles` (`lem:matching:kernel`(b); `cor:dl:normalized`(a) enters as the
  hypothesis `FourCycleBound p`): `c_ker = 2^{β(𝒞)}` when every strongly connected component of
  `D_𝒞` has at most two vertices.
* `rectKer_opBound_acyclic` (`lem:matching:kernel`(a)): `c_ker = 1` when `D_𝒞` is acyclic.
* `IsWitness.rectKer_opBound_twoCycles`, `IsWitness.rectKer_opBound_acyclic`: the same for a
  witness in the sense of `def:extraction:witness` (`IsWitness`).

The proof transports the bounds of `Extraction/KernelAcyclic.lean` and
`Extraction/KernelTwoCycles.lean` along the bijection `injTuples V ≃ {x : Fin k → 𝔽_p injective}`,
`v ↦ (i ↦ v (j_i))` (inverse: extension by `0`, `Function.extend`), and the bijection
`𝒦 → P ∩ (V × W)`, `(i, l) ↦ (j_i, k_l)` (`opBound_transport`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction Sarkozy.Influence

section Transport

variable {α β α' β' : Type*}

/-- An operator bound passes along bijections `R ≃ R'`, `C ≃ C'` of the row and column blocks
(given with their inverses). -/
theorem opBound_transport {R : Finset α} {C : Finset β} {R' : Finset α'} {C' : Finset β'}
    {K : α' → β' → ℝ} {Λ : ℝ} (h : OpBound R' C' K Λ)
    (φ : α → α') (φi : α' → α) (hφ : ∀ a ∈ R, φ a ∈ R') (hφi : ∀ a ∈ R', φi a ∈ R)
    (hφl : ∀ a ∈ R, φi (φ a) = a) (hφr : ∀ a ∈ R', φ (φi a) = a)
    (ψ : β → β') (ψi : β' → β) (hψ : ∀ b ∈ C, ψ b ∈ C') (hψi : ∀ b ∈ C', ψi b ∈ C)
    (hψl : ∀ b ∈ C, ψi (ψ b) = b) (hψr : ∀ b ∈ C', ψ (ψi b) = b) :
    OpBound R C (fun a b => K (φ a) (ψ b)) Λ := by
  intro x
  have hcol : ∀ a' : α', ∑ b ∈ C, K a' (ψ b) * x b = ∑ b' ∈ C', K a' b' * x (ψi b') :=
    fun a' => sum_nbij' ψ ψi hψ hψi hψl hψr (fun b hb => by simp only [hψl b hb])
  have hrow : ∑ a ∈ R, (∑ b ∈ C, K (φ a) (ψ b) * x b) ^ 2 =
      ∑ a' ∈ R', (∑ b' ∈ C', K a' b' * x (ψi b')) ^ 2 :=
    sum_nbij' φ φi hφ hφi hφl hφr (fun a _ => by simp only [hcol])
  have hnorm : ∑ b ∈ C, x b ^ 2 = ∑ b' ∈ C', x (ψi b') ^ 2 :=
    sum_nbij' ψ ψi hψ hψi hψl hψr (fun b hb => by simp only [hψl b hb])
  rw [hrow, hnorm]
  exact h (fun b' => x (ψi b'))

end Transport

section Coordinates

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U] {k : ℕ}

theorem mem_injTuples_coords {V : Finset U} {v : U → F} :
    v ∈ injTuples F V ↔ (∀ u, u ∉ V → v u = 0) ∧ ∀ a ∈ V, ∀ b ∈ V, v a = v b → a = b := by
  unfold injTuples
  rw [mem_filter]
  exact and_iff_right (mem_univ v)

/-- The coordinates `(v_{j_1}, …, v_{j_k})` of an injective tuple on `V = {j_1, …, j_k}` are
distinct. -/
theorem coords_injective {j : Fin k → U} (hj : Function.Injective j) {v : U → F}
    (hv : v ∈ injTuples F (univ.image j)) : Function.Injective fun i => v (j i) := by
  intro i i' h
  exact hj ((mem_injTuples_coords.mp hv).2 (j i) (mem_image_of_mem j (mem_univ i)) (j i')
    (mem_image_of_mem j (mem_univ i')) h)

/-- The extension by `0` of distinct values at `j_1, …, j_k` is an injective tuple on `V`. -/
theorem extend_mem_injTuples {j : Fin k → U} (hj : Function.Injective j) {x : Fin k → F}
    (hx : Function.Injective x) : Function.extend j x (0 : U → F) ∈ injTuples F (univ.image j) := by
  rw [mem_injTuples_coords]
  refine ⟨fun u hu => ?_, fun a ha b hb hab => ?_⟩
  · rw [Function.extend_apply' x (0 : U → F) u
      fun ⟨i, hi⟩ => hu (hi ▸ mem_image_of_mem j (mem_univ i))]
    rfl
  · obtain ⟨i, -, rfl⟩ := mem_image.mp ha
    obtain ⟨i', -, rfl⟩ := mem_image.mp hb
    rw [hj.extend_apply, hj.extend_apply] at hab
    rw [hx hab]

theorem extend_coords {j : Fin k → U} (hj : Function.Injective j) {v : U → F}
    (hv : v ∈ injTuples F (univ.image j)) :
    Function.extend j (fun i => v (j i)) (0 : U → F) = v := by
  funext u
  by_cases hu : u ∈ univ.image j
  · obtain ⟨i, -, rfl⟩ := mem_image.mp hu
    exact hj.extend_apply _ (0 : U → F) i
  · rw [Function.extend_apply' _ (0 : U → F) u
      fun ⟨i, hi⟩ => hu (hi ▸ mem_image_of_mem j (mem_univ i)), (mem_injTuples_coords.mp hv).1 u hu]
    rfl

omit [Fintype F] [DecidableEq F] [Fintype U] [DecidableEq U] in
theorem coords_extend {j : Fin k → U} (hj : Function.Injective j) (x : Fin k → F) :
    (fun i => Function.extend j x (0 : U → F) (j i)) = x :=
  funext fun i => hj.extend_apply x (0 : U → F) i

end Coordinates

section WitnessIndex

variable {U : Type*} [DecidableEq U] {k : ℕ}

/-- The index set `𝒦 = {(i, l) : (j_i, k_l) ∈ P}` of the witness digraph `D_𝒞` of a witness
`w = ((j_1, k_1), …, (j_k, k_k))` (`def:extraction:witness`(b)): `D_𝒦` has an arc `i → l`
(`i ≠ l`) exactly when `(j_i, k_l) ∈ P` (`witnessIdx_arc_iff`). -/
def witnessIdx (P : Finset (U × U)) (w : Fin k → U × U) : Finset (Fin k × Fin k) :=
  univ.filter fun il => ((w il.1).1, (w il.2).2) ∈ P

theorem mem_witnessIdx {P : Finset (U × U)} {w : Fin k → U × U} {i l : Fin k} :
    (i, l) ∈ witnessIdx P w ↔ ((w i).1, (w l).2) ∈ P := by
  unfold witnessIdx
  rw [mem_filter]
  exact and_iff_right (mem_univ _)

/-- `𝒦` contains the diagonal pairs `(i, i)`: the witness pairs are present. -/
theorem witnessIdx_diag {P : Finset (U × U)} {w : Fin k → U × U} (hP : ∀ i, w i ∈ P)
    (i : Fin k) : (i, i) ∈ witnessIdx P w := by
  rw [mem_witnessIdx]
  exact hP i

/-- The digraph `D_𝒦` of `lem:matching:kernel` for `𝒦 = witnessIdx P w` is the witness digraph
`D_𝒞` of `def:extraction:witness`(b) (`ClassWitnessArc`); so `twoCycleCount (witnessIdx P w)`
is `β(𝒞)`. -/
theorem witnessIdx_arc_iff {P : Finset (U × U)} {w : Fin k → U × U} {i l : Fin k} :
    WitnessArc (witnessIdx P w) i l ↔ ClassWitnessArc P w i l := by
  unfold WitnessArc ClassWitnessArc
  rw [mem_witnessIdx]
  exact and_comm

omit [DecidableEq U] in
/-- Signs `ς ∈ {0, ±1}` that do not vanish on `P` are `±1` on `P`. -/
theorem sign_pm_of_ne_zero {ς : U → U → ℤ} (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    {P : Finset (U × U)} (hP : ∀ e ∈ P, ς e.1 e.2 ≠ 0) :
    ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 := fun e he =>
  (hς e.1 e.2).resolve_left (hP e he)

end WitnessIndex

section Bridge

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U] {k : ℕ}

/-- The signs `ς_{il} = ς_{j_i k_l}` of the witness kernel, in `𝔽_p`. -/
def witnessSign (ς : U → U → ℤ) (w : Fin k → U × U) (i l : Fin k) : ZMod p :=
  ((ς (w i).1 (w l).2 : ℤ) : ZMod p)

omit [Fintype U] in
theorem witnessSign_pm {ς : U → U → ℤ} {P : Finset (U × U)} {w : Fin k → U × U}
    (hς : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1) :
    ∀ e ∈ witnessIdx P w, witnessSign (p := p) ς w e.1 e.2 = 1 ∨
      witnessSign (p := p) ς w e.1 e.2 = -1 := by
  intro e he
  have hmem : ((w e.1).1, (w e.2).2) ∈ P := mem_witnessIdx.mp he
  rcases hς _ hmem with h | h
  · left
    simp only [witnessSign, h, Int.cast_one]
  · right
    simp only [witnessSign, h, Int.cast_neg, Int.cast_one]

omit [Fintype U] in
/-- **The kernel identity**: `𝖶(v, w') = ∏_{(i,l) ∈ 𝒦} χ(ς_{j_i k_l}(w'_{k_l} - v_{j_i}))`,
the witness kernel `T_𝒦` of `lem:matching:kernel` at the coordinates `(v_{j_i})_i`,
`(w'_{k_l})_l`; the product is reindexed along the bijection `(i, l) ↦ (j_i, k_l)` from `𝒦` to
`P ∩ (V × W)`. -/
theorem rectKer_eq_witnessKernel (ς : U → U → ℤ) (P : Finset (U × U)) (w : Fin k → U × U)
    (h1 : Function.Injective fun i => (w i).1) (h2 : Function.Injective fun i => (w i).2)
    (v w' : U → ZMod p) :
    rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2) v w' =
      witnessKernel (witnessIdx P w) (witnessSign ς w) (fun i => v (w i).1)
        (fun l => w' (w l).2) := by
  unfold rectKer witnessKernel
  symm
  refine prod_nbij (fun il => ((w il.1).1, (w il.2).2)) ?_ ?_ ?_ ?_
  · intro il hil
    rw [mem_filter]
    exact ⟨mem_witnessIdx.mp hil, mem_image_of_mem _ (mem_univ _),
      mem_image_of_mem _ (mem_univ _)⟩
  · intro a _ b _ hab
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext (h1 hab.1) (h2 hab.2)
  · intro e he
    rw [mem_coe, mem_filter] at he
    obtain ⟨heP, he1, he2⟩ := he
    obtain ⟨i, -, hi⟩ := mem_image.mp he1
    obtain ⟨l, -, hl⟩ := mem_image.mp he2
    have he' : ((w i).1, (w l).2) = e := Prod.ext hi hl
    refine ⟨(i, l), ?_, he'⟩
    rw [mem_coe, mem_witnessIdx, he']
    exact heP
  · intro il _
    rfl

/-- The `𝒦`-kernel bound transported to `rectKer` on `injTuples V × injTuples W`. -/
theorem rectKer_opBound_of_witnessKernel (ς : U → U → ℤ) (P : Finset (U × U))
    (w : Fin k → U × U) (h1 : Function.Injective fun i => (w i).1)
    (h2 : Function.Injective fun i => (w i).2) {Λ : ℝ} {R' C' : Finset (Fin k → ZMod p)}
    (hR' : ∀ x, x ∈ R' ↔ Function.Injective x) (hC' : ∀ x, x ∈ C' ↔ Function.Injective x)
    (hK : OpBound R' C' (witnessKernel (witnessIdx P w) (witnessSign ς w)) Λ) :
    OpBound (injTuples (ZMod p) (univ.image fun i => (w i).1))
      (injTuples (ZMod p) (univ.image fun i => (w i).2))
      (rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2)) Λ := by
  have hfun : rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2) =
      fun (v w' : U → ZMod p) => witnessKernel (witnessIdx P w) (witnessSign ς w)
        (fun i => v (w i).1) (fun l => w' (w l).2) :=
    funext fun v => funext fun w' => rectKer_eq_witnessKernel ς P w h1 h2 v w'
  rw [hfun]
  set j₁ : Fin k → U := fun i => (w i).1
  set j₂ : Fin k → U := fun i => (w i).2
  have key := opBound_transport (R := injTuples (ZMod p) (univ.image j₁))
    (C := injTuples (ZMod p) (univ.image j₂)) hK (fun v i => v (j₁ i))
    (fun x => Function.extend j₁ x (0 : U → ZMod p))
    (fun v hv => (hR' _).mpr (coords_injective h1 hv))
    (fun x hx => extend_mem_injTuples h1 ((hR' x).mp hx))
    (fun v hv => extend_coords h1 hv) (fun x _ => coords_extend h1 x)
    (fun v i => v (j₂ i)) (fun x => Function.extend j₂ x (0 : U → ZMod p))
    (fun v hv => (hC' _).mpr (coords_injective h2 hv))
    (fun x hx => extend_mem_injTuples h2 ((hC' x).mp hx))
    (fun v hv => extend_coords h2 hv) (fun x _ => coords_extend h2 x)
  exact key

/-- **The kernel hypothesis of `lem:matching:extractionk` from `lem:matching:kernel`(b).** Let
`w = ((j_1, k_1), …, (j_k, k_k))` be pairs of `P` with distinct `j_i` and distinct `k_i`,
`V = {j_i}`, `W = {k_i}`, with signs `ς = ±1` on `P`. If every strongly connected component of
the witness digraph `D_𝒞` (`witnessIdx_arc_iff`) has at most two vertices, the kernel `𝖶` of
the present rectangle pairs, compressed to injective tuples, has `ℓ²` norm at most
`2^{β(𝒞)} √p^k`, i.e. `c_ker = 2^{β(𝒞)}` (`2^β r^k` for uniform probability). The four-cycle
bound `cor:dl:normalized`(a) (`FourCycleBound p`) is a hypothesis. -/
theorem rectKer_opBound_twoCycles (hp2 : p ≠ 2) (h4 : FourCycleBound p) (ς : U → U → ℤ)
    (P : Finset (U × U)) (w : Fin k → U × U) (hP : ∀ i, w i ∈ P)
    (h1 : Function.Injective fun i => (w i).1) (h2 : Function.Injective fun i => (w i).2)
    (hς : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcard : ∀ i, (twoCycleComponent (witnessIdx P w) i).card ≤ 2) :
    OpBound (injTuples (ZMod p) (univ.image fun i => (w i).1))
      (injTuples (ZMod p) (univ.image fun i => (w i).2))
      (rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt p ^ k) :=
  rectKer_opBound_of_witnessKernel ς P w h1 h2 (fun _ => mem_filter.trans (and_iff_right (mem_univ _)))
    (fun _ => mem_filter.trans (and_iff_right (mem_univ _)))
    (witnessKernel_opBound_twoCycles_injective hp2 h4 (witnessIdx_diag hP) (witnessSign_pm hς)
      hcard)

/-- **The kernel hypothesis of `lem:matching:extractionk` from `lem:matching:kernel`(a)**: if
the witness digraph `D_𝒞` is acyclic, `c_ker = 1`, i.e. the kernel `𝖶` of the present
rectangle pairs, compressed to injective tuples, has `ℓ²` norm at most `√p^k` (`r^k` for uniform
probability). -/
theorem rectKer_opBound_acyclic (hp2 : p ≠ 2) (ς : U → U → ℤ) (P : Finset (U × U))
    (w : Fin k → U × U) (hP : ∀ i, w i ∈ P) (h1 : Function.Injective fun i => (w i).1)
    (h2 : Function.Injective fun i => (w i).2) (hς : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hac : IsAcyclicWitness (witnessIdx P w)) :
    OpBound (injTuples (ZMod p) (univ.image fun i => (w i).1))
      (injTuples (ZMod p) (univ.image fun i => (w i).2))
      (rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2))
      (Real.sqrt p ^ k) :=
  rectKer_opBound_of_witnessKernel ς P w h1 h2 (R' := univ.filter fun x => Function.Injective x)
    (C' := univ.filter fun x => Function.Injective x)
    (fun _ => mem_filter.trans (and_iff_right (mem_univ _)))
    (fun _ => mem_filter.trans (and_iff_right (mem_univ _)))
    ((witnessKernel_opBound_of_mem hp2 (witnessIdx_diag hP) (witnessSign_pm hς) hac).subset
      (subset_univ _) (subset_univ _))

/-- `rectKer_opBound_twoCycles` for a witness of `def:extraction:witness` (`IsWitness`):
`c_ker = 2^{β(𝒞)}`, with `FourCycleBound p` (`cor:dl:normalized`(a)) as a hypothesis. -/
theorem IsWitness.rectKer_opBound_twoCycles {Ex P A : Finset (U × U)} {w : Fin k → U × U}
    (hw : IsWitness Ex P A w) (hp2 : p ≠ 2) (h4 : FourCycleBound p) (ς : U → U → ℤ)
    (hς : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1)
    (hcard : ∀ i, (twoCycleComponent (witnessIdx P w) i).card ≤ 2) :
    OpBound (injTuples (ZMod p) (univ.image fun i => (w i).1))
      (injTuples (ZMod p) (univ.image fun i => (w i).2))
      (rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2))
      (2 ^ twoCycleCount (witnessIdx P w) * Real.sqrt p ^ k) :=
  ExtractionK.rectKer_opBound_twoCycles hp2 h4 ς P w hw.mem hw.injective_fst hw.injective_snd
    hς hcard

/-- `rectKer_opBound_acyclic` for a witness of `def:extraction:witness` (`IsWitness`):
`c_ker = 1` when the witness digraph is acyclic. -/
theorem IsWitness.rectKer_opBound_acyclic {Ex P A : Finset (U × U)} {w : Fin k → U × U}
    (hw : IsWitness Ex P A w) (hp2 : p ≠ 2) (ς : U → U → ℤ)
    (hς : ∀ e ∈ P, ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1) (hac : IsAcyclicWitness (witnessIdx P w)) :
    OpBound (injTuples (ZMod p) (univ.image fun i => (w i).1))
      (injTuples (ZMod p) (univ.image fun i => (w i).2))
      (rectKer ς P (univ.image fun i => (w i).1) (univ.image fun i => (w i).2))
      (Real.sqrt p ^ k) :=
  ExtractionK.rectKer_opBound_acyclic hp2 ς P w hw.mem hw.injective_fst hw.injective_snd hς hac

end Bridge

end Sarkozy.ExtractionK

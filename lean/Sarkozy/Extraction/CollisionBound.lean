module

public import Sarkozy.Extraction.CoverRows
public import Sarkozy.Influence.OpBound

@[expose] public section

/-!
# Ordered coincidences, I: one coincidence (`lem:oct24-collision`(a), (c))

`paper/sections/16_extraction.tex`, `subsec:extraction:coincidences`, `lem:oct24-collision`:
the definitions, part (a) (exactly one coincidence) and part (c) (the series tail). Parts (b),
(d), (e) are in `Sarkozy.Extraction.CollisionStrata`. The collision kernel `K_coll` and the
operators `T_S` are those of `subsec:spec:perp` / `lem:spec:expansion`. Inputs:
`lem:extraction-merged-count` (`merged_count_le_fintype`), `lem:extension`(b), (c)
(`card_vertexAdmissible`), `lem:graphs:sequential`(a) (through `coverRow_seq_upper`,
`coverRow_seq_lower` of `Sarkozy.Extraction.CoverRows`), `it:et:compare`, `it:et:poly`, and
Schur's test (`Sarkozy.Influence.opBound_schur`).

## Formal setting

As in `Sarkozy.Extraction.CoverRows`: `F` a finite field with `q` elements (`F = 𝔽_p`),
`χ = quadraticChar F`, `WeilBound F` Weil's theorem (`thm:weil`(a), the literature input of
`lem:extension`, the only hypothesis from outside the paper); the half graph `G⁺` an oriented
graph `G` on a finite type `U` (`= U⁺`), `n ≥ |U|`; cross signs `ς : U → U → ℤ` with values in
`{0, ±1}` and, for the operator bounds, `ς_{kj} = -ς_{jk}` (`lem:spec:elementary`), so that
`K_coll` is symmetric. `μ = λ_p(G⁺)` is the uniform law on `𝓘⁺ = Inj_p(G⁺)`.
`collision_opBound_specData` is (a) for spectral data (`G⁺ = D.halfGraph`, `ς = D.sgn`,
`n = |U⁺|`).

Definitions: `collisionCross` (`E_×`), `collisionKernel` (`∏_{e ∈ E_×} (1 + χ_e)`),
`collisionCommon` (`|x(U⁺) ∩ x'(U⁺)|`), `collisionKernel1` (`K_coll` on the pairs with exactly
one common label), `collisionR` (`r_i`), `collisionA` (`a_{ij}`), `collisionLint` (`L_int`),
`collisionBefore`, `collisionT` (`t^{ij}_ℓ`), `collisionD1` (`D_1`), `collisionUps` (`Υ`),
`collisionDeltaPlus` (`Δ⁺`), `collisionB` (`b_i(π)`), `collisionTk` (`t^{(k)}_i`),
`collisionUpsK` (`Υ_k`). The orders: `ord i j` is an order of `U⁺ \ {i}` for each `(i, j)` (a
ranking injective on `U⁺ \ {i}`), and `π k` an order of `U⁺` for each `k`.

## Results and normalization

An operator `T` on `L²(μ)` with kernel `K` relative to `μ ⊗ μ`, `(T f)(x) = E_{x' ∼ μ} K(x, x') f(x')`,
is represented by its matrix `K(x, x')/|𝓘⁺|` on `𝓘⁺ × 𝓘⁺`: `OpBound 𝓘⁺ 𝓘⁺ (K/|𝓘⁺|) D`
(`Sarkozy.Influence.OpBound`) says `∑_x (∑_{x'} K(x,x') f(x')/|𝓘⁺|)² ≤ D² ∑_{x'} f(x')²`, which
is `‖T f‖_μ ≤ D ‖f‖_μ` for all `f` (both sides carry the weight `1/|𝓘⁺|` of `μ`), i.e.
`‖T‖ ≤ D`.

* (a) `collision_rowSum_le`: `E_{x' ∼ μ}[K_coll,1(x, x')] ≤ D_1` for every injective `x`;
  `collision_opBound`: `‖T_coll,1‖ ≤ D_1` (Schur's test for the symmetric kernel).
* (c) `collisionUpsK_eq` (`Υ_k = Υ` for `k ≥ Δ⁺`) and `collision_tail_le` (the geometric
  tail bound, for the partial sums `∑_{k₀ ≤ k < m}`, any `k₀ ≥ Δ⁺` and any `0 ≤ Ξ < k₀ + 1`).
* `collision_oneStep_gen` and `collision_card_lower_gen`, the one-step sum with several
  coincident vertices and the lower count along any order, are used for (b).

## Proofs

As in the paper. A stratum `(i, j)` is labelled by `coverRow_seq_upper` (Step 5 of
`lem:extraction-rows`), with weights that vanish outside the stratum, in the order "coincident
vertex first" (`collisionOrd`); the one-step sums are bounded by `lem:extraction-merged-count`
(`collision_oneStep`) and at the coincident vertex by `w_i(x_j) ≤ 2^{r_i - [j ∈ N(i)]}`
(`collisionW_at_le`). The count `|𝓘⁺|` is bounded below along the same order
(`collision_card_lower`), so that the factors `2^{-t}` cancel; this replaces the paper's
`|𝓘⁺| ≥ p^n 2^{-|E(G⁺)|} L_int` and its identity `∑ t⁰ = |E(G⁺)|`.

## Deviations

* Only the coarse error `e_t(p, n')` is used; of the hypothesis `e_Δ(p, 2n) < 1` only
  `e_{d⁰_i}(p, n) < 1` is used (`collision_opBound_specData` assumes `e_Δ(p, 2n) < 1`).
* `x` is only assumed injective in the row-sum bounds; `n` may be any `n ≥ |U⁺|`;
  `Inj_p(G⁺) ≠ ∅` is a hypothesis (`hne`).
* In (c) `Ξ` is any real `0 ≤ Ξ < k₀ + 1` and `k₀` any integer `≥ Δ⁺` (the paper:
  `k₀ = max(2, Δ⁺)` and `Ξ` of (b)); the tail is stated for the finite partial sums.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Labellings

/-! ## The data -/

section Defs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The cross pairs `E_× = {(j, k) : ς_{jk} ≠ 0}`. -/
def collisionCross (ς : U → U → ℤ) : Finset (U × U) := univ.filter fun e => ς e.1 e.2 ≠ 0

/-- `∏_{e ∈ E_×} (1 + χ_e(x, x'))`, `χ_e(x, x') = χ(ς_{jk}(x'_k - x_j))` for `e = (j, k)`. -/
noncomputable def collisionKernel (ς : U → U → ℤ) (x x' : U → F) : ℝ :=
  ∏ e ∈ collisionCross ς, (1 + (quadraticChar F ((ς e.1 e.2 : F) * (x' e.2 - x e.1)) : ℝ))

/-- The number `|x(U⁺) ∩ x'(U⁺)|` of common labels. -/
def collisionCommon (x x' : U → F) : ℕ := (univ.image x ∩ univ.image x').card

/-- The kernel of `T_coll,1`: `K_coll` on the pairs with exactly one common label, `0`
elsewhere. -/
noncomputable def collisionKernel1 (ς : U → U → ℤ) (x x' : U → F) : ℝ :=
  if collisionCommon x x' = 1 then collisionKernel ς x x' else 0

/-- `r_i = |N(i)|`. -/
def collisionR (ς : U → U → ℤ) (i : U) : ℕ := (rowsN ς i).card

/-- `a_{ij} = 2^{r_i - [j ∈ N(i)] + mg(j, i)}`. -/
noncomputable def collisionA (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) : ℝ :=
  2 ^ (collisionR ς i - (if j ∈ rowsN ς i then 1 else 0) + rowsMg G ς j i)

/-- `L_int = ∏_{i ∈ U⁺} (1 - e_{d⁰_i}(q, n))`. -/
noncomputable def collisionLint (G : OrientedGraph U) (q : ℝ) (n : ℕ) : ℝ :=
  ∏ i, (1 - coarseError (rowsDeg0 G i) q n)

/-- The vertices of `U⁺ \ {i}` before `ℓ` in the order `ord i j` chosen for `(i, j)`. -/
def collisionBefore (ord : U → U → U → ℕ) (i j ℓ : U) : Finset U :=
  univ.filter fun u => u ≠ i ∧ ord i j u < ord i j ℓ

/-- `t^{ij}_ℓ = r_ℓ + [ℓ ∼ i] - [ℓ ∼ i and j ∈ N(ℓ)] + |Adj(ℓ) ∩ {vertices before ℓ}|`. -/
def collisionT (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ) (i j ℓ : U) : ℕ :=
  collisionR ς ℓ + (if i ∈ rowsAdj G ℓ then 1 else 0) -
      (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0) +
    (rowsAdj G ℓ ∩ collisionBefore ord i j ℓ).card

/-- `D_1 = (q L_int)⁻¹ ∑_{i,j} a_{ij} ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n))`. -/
noncomputable def collisionD1 (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    (q : ℝ) (n : ℕ) : ℝ :=
  (q * collisionLint G q n)⁻¹ * ∑ i, ∑ j, collisionA G ς i j *
    ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))

end Defs

/-! ## The cross factors of one vertex -/

section Factors

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `w_k(y) = ∏_{j ∈ N(k)} (1 + χ(ς_{jk}(y - x_j)))`, the cross factors at the `x'`-vertex `k`. -/
noncomputable def collisionW (ς : U → U → ℤ) (x : U → F) (k : U) (y : F) : ℝ :=
  ∏ j ∈ rowsN ς k, (1 + (quadraticChar F ((ς j k : F) * (y - x j)) : ℝ))

omit [DecidableEq U] in
theorem collisionW_nonneg (ς : U → U → ℤ) (x : U → F) (k : U) (y : F) :
    0 ≤ collisionW ς x k y :=
  prod_nonneg fun _ _ => (coverRow_one_add_chi _).1

omit [DecidableEq U] in
/-- `K_coll(x, x') = ∏_k w_k(x'_k)`. -/
theorem collisionKernel_eq_prod (ς : U → U → ℤ) (x x' : U → F) :
    collisionKernel ς x x' = ∏ k, collisionW ς x k (x' k) := by
  unfold collisionKernel collisionW
  apply prod_finset_product_right (collisionCross ς) univ (fun k => rowsN ς k)
  intro p
  simp only [collisionCross, rowsN, mem_filter, mem_univ, true_and]

omit [DecidableEq U] in
theorem collisionKernel_nonneg (ς : U → U → ℤ) (x x' : U → F) : 0 ≤ collisionKernel ς x x' :=
  prod_nonneg fun _ _ => (coverRow_one_add_chi _).1

omit [DecidableEq U] in
theorem collisionKernel1_nonneg (ς : U → U → ℤ) (x x' : U → F) :
    0 ≤ collisionKernel1 ς x x' := by
  unfold collisionKernel1
  split_ifs
  · exact collisionKernel_nonneg ς x x'
  · exact le_rfl

/-- At a coincident vertex, `x'_i = x_j`: the factor of `j`, if `j ∈ N(i)`, is `1 + χ(0) = 1`,
so `w_i(x_j) ≤ 2^{r_i - [j ∈ N(i)]}`. -/
theorem collisionW_at_le (ς : U → U → ℤ) (x : U → F) (i j : U) :
    collisionW ς x i (x j) ≤ 2 ^ (collisionR ς i - if j ∈ rowsN ς i then 1 else 0) := by
  unfold collisionW collisionR
  have hg0 : ∀ a ∈ rowsN ς i, 0 ≤ 1 + (quadraticChar F ((ς a i : F) * (x j - x a)) : ℝ) :=
    fun a _ => (coverRow_one_add_chi _).1
  have hg2 : ∀ a ∈ rowsN ς i, 1 + (quadraticChar F ((ς a i : F) * (x j - x a)) : ℝ) ≤ 2 :=
    fun a _ => (coverRow_one_add_chi _).2
  split_ifs with hj
  · rw [← mul_prod_erase _ _ hj]
    simp only [sub_self, mul_zero, quadraticChar_zero, Int.cast_zero, add_zero, one_mul]
    rw [← card_erase_of_mem hj]
    calc ∏ a ∈ (rowsN ς i).erase j, (1 + (quadraticChar F ((ς a i : F) * (x j - x a)) : ℝ))
        ≤ ∏ _a ∈ (rowsN ς i).erase j, (2 : ℝ) :=
          prod_le_prod₀ (fun a ha => hg0 a (mem_of_mem_erase ha))
            (fun a ha => hg2 a (mem_of_mem_erase ha))
      _ = 2 ^ ((rowsN ς i).erase j).card := prod_const 2
  · rw [Nat.sub_zero]
    calc ∏ a ∈ rowsN ς i, (1 + (quadraticChar F ((ς a i : F) * (x j - x a)) : ℝ))
        ≤ ∏ _a ∈ rowsN ς i, (2 : ℝ) := prod_le_prod₀ hg0 hg2
      _ = 2 ^ (rowsN ς i).card := prod_const 2

/-- **The one-step sum at a non-coincident vertex** (proof of `lem:oct24-collision`(a)). Let
`x'` be feasible on the labelled set `A`, with one coincident vertex `i ∈ A`, `x'_i = x_j`, all
other labels of `A` outside `x(U⁺)`. For a new vertex `ℓ` with `t` labelled neighbours, the sum of
`w_ℓ` over its admissible labels outside `x(U⁺)` is at most
`q 2^{-t} 2^{μ} (1 + e_{t + r_ℓ - μ}(q, n'))`, `μ = [ℓ ∼ i and j ∈ N(ℓ)]`, by
`lem:extraction-merged-count`: the only merged root is `x'_i = x_j`. -/
theorem collision_oneStep (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (x : U → F) (hx : Function.Injective x)
    (A : Finset U) (ℓ : U) (x' : U → F) (hx' : Feasible F G A x') (i j : U) (hiA : i ∈ A)
    (hxi : x' i = x j) (hother : ∀ u ∈ A, u ≠ i → x' u ∉ univ.image x) {n' : ℝ}
    (hn' : 0 ≤ n') :
    ∑ c ∈ (vertexAdmissible G A x' ℓ).filter (fun c => c ∉ univ.image x),
        collisionW ς x ℓ c ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ nbrCount G A ℓ *
        2 ^ (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0) *
        (1 + coarseError (nbrCount G A ℓ + collisionR ς ℓ -
          (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0)) (Fintype.card F) n') := by
  set X : Finset F := univ.image x with hX
  set NA := A.filter (fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E) with hNA
  set Nl := rowsN ς ℓ with hNl
  let β : NA → F := fun u => x' u
  have hβ : Function.Injective β := fun u w h =>
    Subtype.ext (hx'.1 u (mem_filter.mp u.2).1 w (mem_filter.mp w.2).1 h)
  let γ : Nl → F := fun a => x a
  have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hx h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun u => if (u.1, ℓ) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Nl → ℤ := fun a => quadraticChar F (ς a.1 ℓ : F)
  have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
    have ha : ς a.1 ℓ ≠ 0 := by simpa [hNl, rowsN] using a.2
    rcases hς a.1 ℓ with h | h | h
    · exact absurd h ha
    · left
      simp [s', h]
    · simp only [s', h, Int.cast_neg, Int.cast_one]
      exact hm1
  set 𝒳 : Finset F := A.image x' ∪ X with h𝒳
  have hβX : ∀ u, β u ∈ 𝒳 := fun u =>
    mem_union_left _ (mem_image_of_mem x' (mem_filter.mp u.2).1)
  have hγX : ∀ a, γ a ∈ 𝒳 := fun a => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn'
  have hset : (vertexAdmissible G A x' ℓ).filter (fun y => y ∉ X) =
      univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun u => ?_⟩
      have hu := (mem_filter.mp u.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin u (mem_filter.mp u.2).1 h
      · have hvu : (ℓ, u.1) ∈ G.E := hu.resolve_left h
        have h1 := hout u (mem_filter.mp u.2).1 hvu
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun u hu he => ?_, fun u hu he => ?_⟩, hcX⟩
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inl he⟩
        have := hall ⟨u, hmem⟩
        simpa [s, β, he] using this
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inr he⟩
        have hnot : (u, ℓ) ∉ G.E := G.oriented ℓ u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      collisionW ς x ℓ y = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) := by
    intro y _
    unfold collisionW
    rw [← prod_coe_sort Nl]
    refine prod_congr rfl fun a _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = nbrCount G A ℓ := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Nl = collisionR ς ℓ := Fintype.card_coe _
  have hmerge : mergedCount β γ = if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0 := by
    unfold mergedCount
    calc (univ.filter fun il : NA × Nl => β il.1 = γ il.2).card
        = ∑ il : NA × Nl, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ u : NA, ∑ a : Nl, if β u = γ a then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ u : NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_congr rfl fun u _ => sum_coe_sort Nl (fun a => if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_coe_sort NA (fun u => ∑ a ∈ Nl, if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, if u = i then (if j ∈ Nl then 1 else 0) else 0 := by
          refine sum_congr rfl fun u hu => ?_
          by_cases hui : u = i
          · subst hui
            simp only [hxi, hx.eq_iff, ↓reduceIte]
            rw [sum_ite_eq]
          · simp only [hui, ↓reduceIte]
            refine sum_eq_zero fun a _ => ?_
            have hno := hother u (mem_filter.mp hu).1 hui
            have : x' u ≠ x a := fun h => hno (h ▸ mem_image_of_mem x (mem_univ a))
            simp only [this, ↓reduceIte]
      _ = if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0 := by
          rw [sum_ite_eq']
          have hiff : i ∈ NA ↔ i ∈ rowsAdj G ℓ := by
            simp only [hNA, rowsAdj, mem_filter, mem_univ, true_and, hiA]
          by_cases h1 : i ∈ rowsAdj G ℓ <;> by_cases h2 : j ∈ rowsN ς ℓ <;>
            simp [h1, h2, hiff, hNl]
  rw [hset, sum_congr rfl hsummand]
  rw [hcardι, hcardκ, hmerge] at hmc
  exact hmc

end Factors

/-! ## One coincidence: the strata `(i, j)` -/

section Strata

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The order used for the stratum `(i, j)`: `i` first, then `U⁺ \ {i}` in the order `ord i j`. -/
def collisionOrd (ord : U → U → U → ℕ) (i j : U) : U → ℕ :=
  fun ℓ => if ℓ = i then 0 else ord i j ℓ + 1

omit [Fintype U] in
theorem collisionOrd_injOn (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ') (i j : U)
    (C : Finset U) : Set.InjOn (collisionOrd ord i j) C := by
  intro a _ b _ h
  unfold collisionOrd at h
  by_cases ha : a = i <;> by_cases hb : b = i
  · rw [ha, hb]
  · simp only [ha, hb, ↓reduceIte] at h
    omega
  · simp only [ha, hb, ↓reduceIte] at h
    omega
  · simp only [ha, hb, ↓reduceIte, add_left_inj] at h
    exact hord i j a b ha hb h

theorem collision_earlier_self (ord : U → U → U → ℕ) (i j : U) :
    coverRowEarlier univ (collisionOrd ord i j) i = ∅ := by
  unfold coverRowEarlier collisionOrd
  ext u
  simp

theorem collision_mem_earlier (ord : U → U → U → ℕ) {i j ℓ : U} (hℓ : ℓ ≠ i) (u : U) :
    u ∈ coverRowEarlier univ (collisionOrd ord i j) ℓ ↔
      u = i ∨ (u ≠ i ∧ ord i j u < ord i j ℓ) := by
  unfold coverRowEarlier collisionOrd
  simp only [mem_filter, mem_univ, true_and, hℓ, ↓reduceIte]
  by_cases hu : u = i
  · simp [hu]
  · simp [hu]

/-- The number of labelled neighbours of `ℓ ≠ i`: `[ℓ ∼ i] + |Adj(ℓ) ∩ {vertices before ℓ}|`. -/
theorem collision_t0 (G : OrientedGraph U) (ord : U → U → U → ℕ) {i j ℓ : U} (hℓ : ℓ ≠ i) :
    nbrCount G (coverRowEarlier univ (collisionOrd ord i j) ℓ) ℓ =
      (if i ∈ rowsAdj G ℓ then 1 else 0) + (rowsAdj G ℓ ∩ collisionBefore ord i j ℓ).card := by
  have hA : coverRowEarlier univ (collisionOrd ord i j) ℓ =
      insert i (collisionBefore ord i j ℓ) := by
    ext u
    rw [collision_mem_earlier ord hℓ, mem_insert]
    simp only [collisionBefore, mem_filter, mem_univ, true_and]
  have hiB : i ∉ collisionBefore ord i j ℓ := by simp [collisionBefore]
  have hB : ((collisionBefore ord i j ℓ).filter fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E) =
      rowsAdj G ℓ ∩ collisionBefore ord i j ℓ := by
    ext u
    simp only [collisionBefore, rowsAdj, mem_filter, mem_univ, true_and, mem_inter]
    tauto
  have hiadj : i ∈ rowsAdj G ℓ ↔ (i, ℓ) ∈ G.E ∨ (ℓ, i) ∈ G.E := by
    simp only [rowsAdj, mem_filter, mem_univ, true_and]
  unfold nbrCount
  rw [hA, filter_insert]
  split_ifs with h1 h2 h2
  · rw [card_insert_of_notMem (fun h => hiB (mem_filter.mp h).1), hB]
    ring
  · exact absurd (hiadj.mpr h1) h2
  · exact absurd (hiadj.mp h2) h1
  · rw [hB, zero_add]

/-- `t^{ij}_ℓ = t⁰_ℓ + r_ℓ - μ_ℓ`, the number of distinct roots at `ℓ`. -/
theorem collision_t_eq (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    {i j ℓ : U} (hℓ : ℓ ≠ i) :
    nbrCount G (coverRowEarlier univ (collisionOrd ord i j) ℓ) ℓ + collisionR ς ℓ -
        (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0) = collisionT G ς ord i j ℓ := by
  rw [collision_t0 G ord hℓ]
  unfold collisionT
  by_cases h1 : i ∈ rowsAdj G ℓ <;> by_cases h2 : j ∈ rowsN ς ℓ <;> simp only [h1, h2, and_true,
    and_false, ↓reduceIte] <;> omega

/-- The weight of a vertex `ℓ ≠ i` in the stratum `(i, j)`: `w_ℓ(y_ℓ)` if `y_i = x_j` and the
labels of `ℓ` and of the vertices `≠ i` labelled before `ℓ` lie outside `x(U⁺)`, else `0`. -/
noncomputable def collisionPhi (ς : U → U → ℤ) (ord : U → U → U → ℕ) (x : U → F) (i j ℓ : U)
    (y : U → F) : ℝ :=
  if ℓ ≠ i ∧ y i = x j ∧ (∀ u ∈ coverRowEarlier univ (collisionOrd ord i j) ℓ, u ≠ i →
      y u ∉ univ.image x) ∧ y ℓ ∉ univ.image x
  then collisionW ς x ℓ (y ℓ) else 0

/-- The one-step bound `q 2^{-t⁰_ℓ} 2^{μ_ℓ} (1 + e_{t^{ij}_ℓ}(q, 2n))` of `ℓ ≠ i`. -/
noncomputable def collisionM (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    (q : ℝ) (n : ℕ) (i j ℓ : U) : ℝ :=
  if ℓ = i then 0 else
    q * (2 : ℝ)⁻¹ ^ nbrCount G (coverRowEarlier univ (collisionOrd ord i j) ℓ) ℓ *
      2 ^ (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0) *
      (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))

theorem collisionM_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    {q : ℝ} (hq : 0 ≤ q) (n : ℕ) (i j ℓ : U) : 0 ≤ collisionM G ς ord q n i j ℓ := by
  unfold collisionM
  have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
    (collisionT G ς ord i j ℓ)
  split_ifs
  · exact le_rfl
  all_goals exact mul_nonneg (by positivity) (by linarith)

/-- **The stratum `(i, j)`** (proof of `lem:oct24-collision`(a)): labelling `i` first and the
other vertices in the order `ord i j`,
`∑_{x' ∈ 𝓘⁺, x'_i = x_j, x'_ℓ ∉ x(U⁺) (ℓ ≠ i)} K_coll(x, x') ≤ w_i(x_j) ∏_{ℓ ≠ i} M_ℓ`. -/
theorem collision_stratum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) (n : ℕ) (i j : U) :
    ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
      collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord (Fintype.card F) n i j ℓ := by
  set X : Finset F := univ.image x with hX
  set ord' := collisionOrd ord i j with hord'
  have hinj := collisionOrd_injOn ord hord i j univ
  have hq0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  -- locality of the weights
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord' a ≤ ord' b → y a = y' a) →
        collisionPhi ς ord x i j b y = collisionPhi ς ord x i j b y' := by
    intro b _ y y' h
    have e1 : y i = y' i := h i (mem_univ _) (by simp [hord', collisionOrd])
    have e2 : ∀ u ∈ coverRowEarlier univ ord' b, y u = y' u :=
      fun u hu => h u (mem_univ _) (mem_filter.mp hu).2.le
    have e3 : y b = y' b := h b (mem_univ _) le_rfl
    unfold collisionPhi
    refine if_congr ?_ (by rw [e3]) rfl
    rw [e1, e3]
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun u hu hui => (e2 u hu) ▸ h3 u hu hui, h4⟩
    · rintro ⟨h1, h2, h3, h4⟩
      exact ⟨h1, h2, fun u hu hui => (e2 u hu).symm ▸ h3 u hu hui, h4⟩
  -- the one-step bounds
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord' b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          collisionPhi ς ord x i j b (Function.update x' b c) ≤
            collisionM G ς ord (Fintype.card F) n i j b := by
    intro b _ x' hx'
    by_cases hbi : b = i
    · subst hbi
      simp [collisionPhi, collisionM]
    have hupd : ∀ c, collisionPhi ς ord x i j b (Function.update x' b c) =
        if (x' i = x j ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ≠ i → x' u ∉ X) ∧ c ∉ X then
          collisionW ς x b c else 0 := by
      intro c
      unfold collisionPhi
      have hui : Function.update x' b c i = x' i := Function.update_of_ne (Ne.symm hbi) _ _
      have hu : ∀ u ∈ coverRowEarlier univ ord' b, Function.update x' b c u = x' u := by
        intro u hu
        have hub : u ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp hu).2
        exact Function.update_of_ne hub _ _
      refine if_congr ?_ (by rw [Function.update_self]) rfl
      rw [hui, Function.update_self]
      constructor
      · rintro ⟨_, h2, h3, h4⟩
        exact ⟨⟨h2, fun u huE hui' => (hu u huE) ▸ h3 u huE hui'⟩, h4⟩
      · rintro ⟨⟨h2, h3⟩, h4⟩
        exact ⟨hbi, h2, fun u huE hui' => (hu u huE).symm ▸ h3 u huE hui', h4⟩
    rw [sum_congr rfl fun c _ => hupd c]
    by_cases hcond : x' i = x j ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ≠ i → x' u ∉ X
    · have hc' : ∀ c, (if (x' i = x j ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ≠ i → x' u ∉ X) ∧
          c ∉ X then collisionW ς x b c else 0) = if c ∉ X then collisionW ς x b c else 0 := by
        intro c
        by_cases hcX : c ∈ X
        · rw [ite_eq_right (fun h => h.2 hcX), ite_eq_right (fun h => h hcX)]
        · rw [ite_eq_left ⟨hcond, hcX⟩, ite_eq_left hcX]
      rw [sum_congr rfl fun c _ => hc' c, ← sum_filter]
      have hiA : i ∈ coverRowEarlier univ ord' b := (collision_mem_earlier ord hbi i).mpr (Or.inl rfl)
      have h := collision_oneStep hW G ς hς x hx (coverRowEarlier univ ord' b) b x' hx' i j hiA
        hcond.1 hcond.2 (n' := 2 * (n : ℝ)) (by positivity)
      rw [collision_t_eq G ς ord hbi] at h
      unfold collisionM
      rw [ite_eq_right hbi]
      exact h
    · simp only [hcond, false_and, ↓reduceIte, sum_const_zero]
      exact collisionM_nonneg G ς ord hq0 n i j b
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hseg : ∀ b ∈ univ.erase i, ∀ b' ∈ (univ : Finset U), b' ∉ univ.erase i →
      ord' b' < ord' b := by
    intro b hb b' _ hb'
    have hb'i : b' = i := by
      by_contra h
      exact hb' (mem_erase.mpr ⟨h, mem_univ _⟩)
    have hbi : b ≠ i := (mem_erase.mp hb).1
    simp [hord', collisionOrd, hb'i, hbi]
  set y0 : U → F := fun _ => x j with hy0
  have hfe : Feasible F G (univ \ univ.erase i) y0 := by
    rw [sdiff_erase_self (mem_univ i)]
    refine ⟨fun a ha b hb _ => by rw [mem_singleton.mp ha, mem_singleton.mp hb], ?_⟩
    intro e he h1 h2
    have h1' := mem_singleton.mp h1
    have h2' := mem_singleton.mp h2
    have : e = (i, i) := Prod.ext h1' h2'
    exact absurd (this ▸ he) (G.loopless i)
  have hseq := coverRow_seq_upper G hinj (collisionPhi ς ord x i j)
    (collisionM G ς ord (Fintype.card F) n i j) 1
    (fun b y => by unfold collisionPhi; split_ifs
                   · exact collisionW_nonneg ς x b _
                   · exact le_rfl)
    (fun b => collisionM_nonneg G ς ord hq0 n i j b) zero_le_one hloc hstep hK
    (univ.erase i).card (univ.erase i) rfl (subset_univ _) hseg y0 hfe
  rw [one_mul, sdiff_erase_self (mem_univ i)] at hseq
  unfold coverRowExtSum at hseq
  rw [sum_filter] at hseq
  calc ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ X then collisionKernel ς x y else 0)
      ≤ ∑ y ∈ injLabellings F G, collisionW ς x i (x j) *
          (if ∀ a ∈ ({i} : Finset U), y a = y0 a then
            ∏ ℓ ∈ univ.erase i, collisionPhi ς ord x i j ℓ y else 0) := by
        refine sum_le_sum fun y _ => ?_
        split_ifs with h1 h2
        · rw [collisionKernel_eq_prod, ← mul_prod_erase univ _ (mem_univ i), h1.1]
          refine mul_le_mul_of_nonneg_left (le_of_eq (prod_congr rfl fun ℓ hℓ => ?_))
            (collisionW_nonneg ς x i _)
          have hℓi : ℓ ≠ i := (mem_erase.mp hℓ).1
          unfold collisionPhi
          rw [ite_eq_left ⟨hℓi, h1.1, fun u _ hui => h1.2 u hui, h1.2 ℓ hℓi⟩]
        · exact absurd (fun a ha => by rw [mem_singleton.mp ha]; exact h1.1) h2
        · exact mul_nonneg (collisionW_nonneg ς x i _) (prod_nonneg fun ℓ _ => by
            unfold collisionPhi; split_ifs
            · exact collisionW_nonneg ς x ℓ _
            · exact le_rfl)
        · simp
    _ = collisionW ς x i (x j) * ∑ y ∈ injLabellings F G,
          (if ∀ a ∈ ({i} : Finset U), y a = y0 a then
            ∏ ℓ ∈ univ.erase i, collisionPhi ς ord x i j ℓ y else 0) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hseq (collisionW_nonneg ς x i _)

end Strata

/-! ## The single-coincidence bound (`lem:oct24-collision`(a)) -/

section SingleCoincidence

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The lower count `|𝓘⁺| ≥ ∏_v q 2^{-t'_v}(1 - e_{t'_v}(q, n))` along the order of the
stratum `(i, j)` (`lem:graphs:sequential`(a); `t'_v` the number of earlier neighbours). -/
theorem collision_card_lower (hW : WeilBound F) (G : OrientedGraph U) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ') {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (i j : U) :
    ∏ v, ((Fintype.card F : ℝ) / 2 ^ nbrCount G (coverRowEarlier univ (collisionOrd ord i j) v) v *
        (1 - coarseError (nbrCount G (coverRowEarlier univ (collisionOrd ord i j) v) v)
          (Fintype.card F) n)) ≤ (injLabellings F G).card := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set ord' := collisionOrd ord i j with hord'
  have hinj := collisionOrd_injOn ord hord i j univ
  have het : ∀ v, coarseError (nbrCount G (coverRowEarlier univ ord' v) v) (Fintype.card F) n < 1 :=
    fun v => lt_of_le_of_lt (coarseError_mono hn0 (coverRow_nbrCount_le G _ v)) (hS1 v)
  have hℓ0 : ∀ v, 0 ≤ (Fintype.card F : ℝ) / 2 ^ nbrCount G (coverRowEarlier univ ord' v) v *
      (1 - coarseError (nbrCount G (coverRowEarlier univ ord' v) v) (Fintype.card F) n) :=
    fun v => mul_nonneg (by positivity) (by linarith [het v])
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord' b) x' →
        (Fintype.card F : ℝ) / 2 ^ nbrCount G (coverRowEarlier univ ord' b) b *
          (1 - coarseError (nbrCount G (coverRowEarlier univ ord' b) b) (Fintype.card F) n) ≤
        (vertexAdmissible G (coverRowEarlier univ ord' b) x' b).card := by
    intro b _ x' hx'
    obtain ⟨-, hlo⟩ := card_vertexAdmissible hW G hx' b
    have hsoft := coverRow_softError_le hq1 n (nbrCount G (coverRowEarlier univ ord' b) b)
    have hA : ((coverRowEarlier univ ord' b).card : ℝ) ≤ n := by
      have := (card_le_univ (coverRowEarlier univ ord' b)).trans hn
      exact_mod_cast this
    have hpos : (0 : ℝ) < 2 ^ nbrCount G (coverRowEarlier univ ord' b) b := by positivity
    have h2A := mul_le_mul_of_nonneg_left hA hpos.le
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  have hL : ∀ y : U → F, Feasible F G univ y → (1 : ℝ) ≤ extCount G univ y := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hfe : Feasible F G (univ \ univ) (fun _ => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have h := coverRow_seq_lower G hinj _ 1 hℓ0 zero_le_one hstep hL (univ : Finset U).card univ
    rfl subset_rfl (fun _ _ b' _ hb' => absurd (mem_univ b') hb') (fun _ => (0 : F)) hfe
  rw [one_mul, Finset.sdiff_self] at h
  have he : extCount G ∅ (fun _ => (0 : F)) = (injLabellings F G).card := by
    unfold extCount
    congr 1
    exact filter_true_of_mem fun _ _ => by simp
  rwa [he] at h

omit [DecidableEq U] in
/-- `∑_{ℓ ≠ i} [ℓ ∼ i and j ∈ N(ℓ)] = mg(j, i)`. -/
theorem collision_sum_merges (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) [DecidableEq U] :
    ∑ ℓ ∈ univ.erase i, (if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0) = rowsMg G ς j i := by
  rw [← card_filter]
  unfold rowsMg
  congr 1
  ext ℓ
  simp only [rowsAdj, mem_filter, mem_erase, mem_univ, true_and, and_true]
  constructor
  · rintro ⟨_, h1, h2⟩
    exact ⟨h1.symm, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h1.symm, h2⟩
    rintro rfl
    rcases h1 with h | h <;> exact G.loopless _ h

/-- **One stratum, normalized**: the sum of `K_coll(x, ·)` over the stratum `(i, j)` is at most
`(q L_int)⁻¹ a_{ij} ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n)) · |𝓘⁺|`. -/
theorem collision_stratum_ratio (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (i j : U) :
    ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
      ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
        (collisionA G ς i j * ∏ ℓ ∈ univ.erase i,
          (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
        (injLabellings F G).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set t' : U → ℕ := fun v => nbrCount G (coverRowEarlier univ (collisionOrd ord i j) v) v with ht'
  set μ : U → ℕ := fun ℓ => if i ∈ rowsAdj G ℓ ∧ j ∈ rowsN ς ℓ then 1 else 0 with hμ
  set eT : U → ℝ := fun ℓ => coarseError (collisionT G ς ord i j ℓ) q (2 * n) with heT
  set ℓf : U → ℝ := fun v => q / 2 ^ t' v * (1 - coarseError (t' v) q n) with hℓf
  have het : ∀ v, coarseError (t' v) q n ≤ coarseError (rowsDeg0 G v) q n :=
    fun v => coarseError_mono hn0 (coverRow_nbrCount_le G _ v)
  have het1 : ∀ v, 0 < 1 - coarseError (t' v) q n := fun v => by linarith [het v, hS1 v]
  have heT0 : ∀ ℓ, 0 ≤ eT ℓ := fun ℓ =>
    coarseError_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) _
  have hstr := collision_stratum_le hW G ς hς ord hord x hx n i j
  have hlow := collision_card_lower hW G ord hord hn hS1 i j
  -- `M_ℓ = c_ℓ ℓ_ℓ` with `c_ℓ = 2^{μ_ℓ}(1 + e_{t^{ij}_ℓ})/(1 - e_{t'_ℓ})`
  have hM : ∀ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ =
      (2 ^ μ ℓ * (1 + eT ℓ) / (1 - coarseError (t' ℓ) q n)) * ℓf ℓ := by
    intro ℓ hℓ
    have hℓi : ℓ ≠ i := (mem_erase.mp hℓ).1
    unfold collisionM
    rw [ite_eq_right hℓi]
    have h1 : 1 - coarseError (nbrCount G (coverRowEarlier univ (collisionOrd ord i j) ℓ) ℓ) q n
        ≠ 0 := (het1 ℓ).ne'
    simp only [hℓf, heT, hμ, ht', inv_pow]
    field_simp
  have hprodM : ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ =
      (2 ^ rowsMg G ς j i * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) /
        (∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n)) * ∏ ℓ ∈ univ.erase i, ℓf ℓ := by
    rw [prod_congr rfl hM, prod_mul_distrib, prod_div_distrib, prod_mul_distrib,
      prod_pow_eq_pow_sum, collision_sum_merges G ς i j]
  have hti : t' i = 0 := by
    simp only [ht', collision_earlier_self, nbrCount, filter_empty, card_empty]
  have hℓi : ℓf i = q * (1 - coarseError 0 q n) := by
    simp only [hℓf, hti, pow_zero, div_one]
  have hprodℓ : ∏ v, ℓf v = q * (1 - coarseError 0 q n) * ∏ ℓ ∈ univ.erase i, ℓf ℓ := by
    rw [← mul_prod_erase univ ℓf (mem_univ i), hℓi]
  -- `L_int ≤ (1 - e_0) ∏_{ℓ ≠ i} (1 - e_{t'_ℓ})`
  have hLle : collisionLint G q n ≤
      (1 - coarseError 0 q n) * ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n) := by
    unfold collisionLint
    rw [← mul_prod_erase univ _ (mem_univ i)]
    refine mul_le_mul ?_ ?_ (prod_nonneg fun v _ => by linarith [hS1 v]) ?_
    · linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i))]
    · exact prod_le_prod₀ (fun v _ => by linarith [hS1 v]) (fun v _ => by linarith [het v])
    · linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i)), hS1 i]
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hQpos : 0 < ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n) :=
    prod_pos fun v _ => het1 v
  have hP0 : 0 ≤ ∏ ℓ ∈ univ.erase i, (1 + eT ℓ) := prod_nonneg fun ℓ _ => by linarith [heT0 ℓ]
  have hℓ'0 : 0 ≤ ∏ ℓ ∈ univ.erase i, ℓf ℓ :=
    prod_nonneg fun v _ => mul_nonneg (by positivity) (het1 v).le
  have hw := collisionW_at_le ς x i j
  have hw0 := collisionW_nonneg ς x i (x j)
  have ha : collisionA G ς i j = 2 ^ (collisionR ς i - if j ∈ rowsN ς i then 1 else 0) *
      2 ^ rowsMg G ς j i := by
    unfold collisionA
    rw [pow_add]
  have he00 : 0 < 1 - coarseError 0 q n := by
    linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i)), hS1 i]
  -- the key inequality: `w_i(x_j) ∏ M ≤ (q L)⁻¹ a ∏(1 + e) ∏ ℓ`
  have hkey : collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ ≤
      (q * collisionLint G q n)⁻¹ * (collisionA G ς i j * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) *
        ∏ v, ℓf v := by
    rw [hprodM, hprodℓ]
    set P := ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)
    set Q := ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n)
    set ℓ' := ∏ ℓ ∈ univ.erase i, ℓf ℓ
    set L := collisionLint G q n
    set w := collisionW ς x i (x j)
    set A := collisionA G ς i j
    -- `w 2^{mg} L ≤ A (1 - e_0) Q`
    have h1 : w * 2 ^ rowsMg G ς j i * L ≤ A * ((1 - coarseError 0 q n) * Q) := by
      have hA' : w * 2 ^ rowsMg G ς j i ≤ A := by
        rw [ha]
        exact mul_le_mul_of_nonneg_right hw (by positivity)
      have hA0 : 0 ≤ A := by unfold A collisionA; positivity
      calc w * 2 ^ rowsMg G ς j i * L ≤ A * L := mul_le_mul_of_nonneg_right hA' hLpos.le
        _ ≤ A * ((1 - coarseError 0 q n) * Q) := mul_le_mul_of_nonneg_left hLle hA0
    have hlhs : w * ((2 ^ rowsMg G ς j i * P) / Q * ℓ') =
        (w * 2 ^ rowsMg G ς j i * L) * (P * ℓ' / (L * Q)) := by
      field_simp
    have hrhs : (q * L)⁻¹ * (A * P) * (q * (1 - coarseError 0 q n) * ℓ') =
        (A * ((1 - coarseError 0 q n) * Q)) * (P * ℓ' / (L * Q)) := by
      field_simp
    rw [hlhs, hrhs]
    exact mul_le_mul_of_nonneg_right h1 (div_nonneg (mul_nonneg hP0 hℓ'0)
      (mul_pos hLpos hQpos).le)
  have hcoef : 0 ≤ (q * collisionLint G q n)⁻¹ *
      (collisionA G ς i j * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) := by
    refine mul_nonneg (inv_nonneg.mpr (mul_pos hq0 hLpos).le) (mul_nonneg ?_ hP0)
    unfold collisionA
    positivity
  calc _ ≤ collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ := hstr
    _ ≤ _ := hkey
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hcoef

/-- A pair with exactly one common label lies in a stratum `(i, j)`: `x'_i = x_j` and
`x'_ℓ ∉ x(U⁺)` for `ℓ ≠ i`. -/
theorem collisionKernel1_le_sum (ς : U → U → ℤ) (x y : U → F) (hy : Function.Injective y) :
    collisionKernel1 ς x y ≤ ∑ i, ∑ j,
      (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
  have hterm : ∀ i j, 0 ≤
      (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) :=
    fun i j => by split_ifs; exacts [collisionKernel_nonneg ς x y, le_rfl]
  unfold collisionKernel1
  split_ifs with h1
  · obtain ⟨z, hz⟩ := card_eq_one.mp h1
    have hzx : z ∈ univ.image x := (mem_inter.mp (hz ▸ mem_singleton_self z)).1
    have hzy : z ∈ univ.image y := (mem_inter.mp (hz ▸ mem_singleton_self z)).2
    obtain ⟨i₀, -, hi₀⟩ := mem_image.mp hzy
    obtain ⟨j₀, -, hj₀⟩ := mem_image.mp hzx
    have hcond : y i₀ = x j₀ ∧ ∀ ℓ, ℓ ≠ i₀ → y ℓ ∉ univ.image x := by
      refine ⟨hi₀.trans hj₀.symm, fun ℓ hℓ hmem => hℓ ?_⟩
      have : y ℓ ∈ univ.image x ∩ univ.image y := mem_inter.mpr ⟨hmem, mem_image_of_mem y (mem_univ ℓ)⟩
      rw [hz, mem_singleton] at this
      exact hy (this.trans hi₀.symm)
    calc collisionKernel ς x y
        = (if y i₀ = x j₀ ∧ ∀ ℓ, ℓ ≠ i₀ → y ℓ ∉ univ.image x then collisionKernel ς x y
            else 0) := (ite_eq_left hcond).symm
      _ ≤ ∑ j, (if y i₀ = x j ∧ ∀ ℓ, ℓ ≠ i₀ → y ℓ ∉ univ.image x then collisionKernel ς x y
            else 0) := single_le_sum (fun j _ => hterm i₀ j) (mem_univ j₀)
      _ ≤ _ := single_le_sum (f := fun i => ∑ j,
            (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0))
            (fun i _ => sum_nonneg fun j _ => hterm i j) (mem_univ i₀)
  · exact sum_nonneg fun i _ => sum_nonneg fun j _ => hterm i j

/-- **`lem:oct24-collision`(a), row sums**: for every injective `x` (e.g. `x ∈ 𝓘⁺`),
`E_{x' ∼ μ}[K_coll,1(x, x')] ≤ D_1`. -/
theorem collision_rowSum_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) :
    (graphLaw G hne).expect (collisionKernel1 ς x) ≤ collisionD1 G ς ord (Fintype.card F) n := by
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  calc ∑ y ∈ injLabellings F G, collisionKernel1 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ i, ∑ j,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel1_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ i, ∑ j, ∑ y ∈ injLabellings F G,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) := by
        rw [sum_comm]
        exact sum_congr rfl fun i _ => sum_comm
    _ ≤ ∑ i, ∑ j, ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
          (collisionA G ς i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          collision_stratum_ratio hW G ς hς ord hord x hx hn hS1 i j
    _ = collisionD1 G ς ord (Fintype.card F) n * (injLabellings F G).card := by
        unfold collisionD1
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, sum_mul]

end SingleCoincidence

/-! ## Schur's test: the operator bound -/

section Schur

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [DecidableEq U] in
/-- `K_coll` is symmetric, since `ς_{kj} = -ς_{jk}` (`lem:spec:elementary`). -/
theorem collisionKernel_symm (ς : U → U → ℤ) (hanti : ∀ j k, ς k j = -ς j k) (x x' : U → F) :
    collisionKernel ς x x' = collisionKernel ς x' x := by
  unfold collisionKernel
  refine prod_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
  · intro e he
    simp only [collisionCross, mem_filter, mem_univ, true_and, Prod.fst_swap,
      Prod.snd_swap] at he ⊢
    rw [hanti]
    exact neg_ne_zero.mpr he
  · intro e he
    simp only [collisionCross, mem_filter, mem_univ, true_and, Prod.fst_swap,
      Prod.snd_swap] at he ⊢
    rw [hanti]
    exact neg_ne_zero.mpr he
  · intro e _
    exact Prod.swap_swap e
  · intro e _
    exact Prod.swap_swap e
  · intro e _
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hanti e.1 e.2]
    congr 3
    push_cast
    ring

omit [Field F] [Fintype F] [DecidableEq U] in
theorem collisionCommon_symm (x x' : U → F) :
    collisionCommon x x' = collisionCommon x' x := by
  unfold collisionCommon
  rw [inter_comm]

omit [DecidableEq U] in
theorem collisionKernel1_symm (ς : U → U → ℤ) (hanti : ∀ j k, ς k j = -ς j k) (x x' : U → F) :
    collisionKernel1 ς x x' = collisionKernel1 ς x' x := by
  unfold collisionKernel1
  rw [collisionCommon_symm, collisionKernel_symm ς hanti]

/-- **`lem:oct24-collision`(a)**: `‖T_coll,1‖ ≤ D_1` on `L²(μ)`, `μ = λ_p(G⁺)` uniform on `𝓘⁺`.
The operator `(T_coll,1 f)(x) = E_{x' ∼ μ}[K_coll,1(x, x') f(x')]` has matrix
`K_coll,1(x, x')/|𝓘⁺|` on `𝓘⁺ × 𝓘⁺`, and `OpBound 𝓘⁺ 𝓘⁺ (K_coll,1/|𝓘⁺|) D_1` says
`∑_x (∑_{x'} K_coll,1(x,x') f(x')/|𝓘⁺|)² ≤ D_1² ∑_{x'} f(x')²`, which is `‖T f‖_μ ≤ D_1 ‖f‖_μ`
(both sides carry the factor `1/|𝓘⁺|` of `μ`). By Schur's test (`opBound_schur`) for the
nonnegative symmetric kernel, the norm is at most the largest row sum `E_{x' ∼ μ}[K_coll,1(x, x')]`
(`collision_rowSum_le`). -/
theorem collision_opBound (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ') :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel1 ς x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel1 ς x x' / (injLabellings F G).card ≤
        collisionD1 G ς ord (Fintype.card F) n := by
    intro x hx
    have hxinj : Function.Injective x := fun a b h => by
      simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
      exact hx.1 a (mem_univ _) b (mem_univ _) h
    have h := collision_rowSum_le hW G ς hς hne hn hS1 ord hord x hxinj
    rw [coverRow_expect_graphLaw] at h
    rwa [← sum_div]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel1 ς x x' / (injLabellings F G).card ≤
        collisionD1 G ς ord (Fintype.card F) n := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel1 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel1 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [collisionKernel1_symm ς hanti]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ collisionD1 G ς ord (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel1_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel1_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

end Schur

/-! ## The series tail and the coarse form of `D_1` (`lem:oct24-collision`(c), (d)) -/

section Coarse

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `Υ = ∏_{i ∈ U⁺} (1 + e_{d_i}(q, 2n))`, `d_i = d⁰_i + r_i`. -/
noncomputable def collisionUps (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  ∏ i, (1 + coarseError (rowsDeg0 G i + collisionR ς i) q (2 * n))

/-- `Δ⁺ = max_i d⁰_i`. -/
def collisionDeltaPlus (G : OrientedGraph U) : ℕ := univ.sup (rowsDeg0 G)

/-- `b_i(π)`, the number of `G⁺`-neighbours of `i` preceding `i` in the order `π`. -/
def collisionB (G : OrientedGraph U) (π : U → ℕ) (i : U) : ℕ :=
  (rowsAdj G i ∩ univ.filter fun u => π u < π i).card

/-- `t^{(k)}_i = min(r_i + d⁰_i, r_i + b_i(π_k) + k)`, for orders `π_k` (`k ≥ 2`). -/
def collisionTk (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ) (k : ℕ) (i : U) : ℕ :=
  min (collisionR ς i + rowsDeg0 G i) (collisionR ς i + collisionB G (π k) i + k)

/-- `Υ_k = ∏_i (1 + e_{t^{(k)}_i}(q, 2n))`. -/
noncomputable def collisionUpsK (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ)
    (q : ℝ) (n : ℕ) (k : ℕ) : ℝ :=
  ∏ i, (1 + coarseError (collisionTk G ς π k i) q (2 * n))

/-- **`lem:oct24-collision`(c)**, first claim: `Υ_k = Υ` for `k ≥ Δ⁺`. -/
theorem collisionUpsK_eq (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ) (q : ℝ)
    (n : ℕ) {k : ℕ} (hk : collisionDeltaPlus G ≤ k) :
    collisionUpsK G ς π q n k = collisionUps G ς q n := by
  unfold collisionUpsK collisionUps
  refine prod_congr rfl fun i _ => ?_
  have hd : rowsDeg0 G i ≤ k := (le_sup (f := rowsDeg0 G) (mem_univ i)).trans hk
  have h : collisionTk G ς π k i = rowsDeg0 G i + collisionR ς i := by
    unfold collisionTk
    rw [min_eq_left (by omega)]
    omega
  rw [h]

/-- `Ξ^{k₀+m}/(k₀+m)! ≤ (Ξ^{k₀}/k₀!) (Ξ/(k₀+1))^m` for `Ξ ≥ 0`. -/
theorem collision_term_le {Ξ : ℝ} (hΞ : 0 ≤ Ξ) (k₀ : ℕ) :
    ∀ m : ℕ, Ξ ^ (k₀ + m) / ((k₀ + m).factorial : ℝ) ≤
      Ξ ^ k₀ / (k₀.factorial : ℝ) * (Ξ / (k₀ + 1)) ^ m
  | 0 => by simp
  | m + 1 => by
      have ih := collision_term_le hΞ k₀ m
      have hf : ((k₀ + (m + 1)).factorial : ℝ) = (k₀ + m + 1) * (k₀ + m).factorial := by
        rw [show k₀ + (m + 1) = (k₀ + m) + 1 by ring, Nat.factorial_succ]
        push_cast
        ring
      have hfpos : (0 : ℝ) < (k₀ + m).factorial := by exact_mod_cast Nat.factorial_pos _
      have hρ : Ξ / ((k₀ : ℝ) + m + 1) ≤ Ξ / ((k₀ : ℝ) + 1) :=
        div_le_div_of_nonneg_left hΞ (by positivity) (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
      have hsplit : Ξ ^ (k₀ + (m + 1)) / ((k₀ + (m + 1)).factorial : ℝ) =
          Ξ ^ (k₀ + m) / ((k₀ + m).factorial : ℝ) * (Ξ / ((k₀ : ℝ) + m + 1)) := by
        rw [hf, show k₀ + (m + 1) = (k₀ + m) + 1 by ring, pow_succ]
        field_simp
      rw [hsplit, pow_succ, ← mul_assoc]
      exact mul_le_mul ih hρ (div_nonneg hΞ (by positivity))
        (mul_nonneg (div_nonneg (pow_nonneg hΞ _) (by positivity)) (pow_nonneg (by positivity) _))

/-- **`lem:oct24-collision`(c)**, the series tail: for `k₀ ≥ Δ⁺`, `0 ≤ Ξ < k₀ + 1` and every
`m`, `L⁻¹ ∑_{k₀ ≤ k < m} Υ_k Ξ^k/k! ≤ (Υ/L) (Ξ^{k₀}/k₀!) (1 - Ξ/(k₀ + 1))⁻¹` (the partial sums
of `∑_{k ≥ k₀}`; in the paper `k₀ = max(2, Δ⁺)` and `Ξ` is the constant of (b)). -/
theorem collision_tail_le (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ) {q : ℝ}
    (n : ℕ) {L Ξ : ℝ} (hL : 0 < L) (hΞ : 0 ≤ Ξ) {k₀ : ℕ} (hk₀ : collisionDeltaPlus G ≤ k₀)
    (hΞk : Ξ < k₀ + 1) (m : ℕ) :
    L⁻¹ * ∑ k ∈ Ico k₀ m, collisionUpsK G ς π q n k * (Ξ ^ k / (k.factorial : ℝ)) ≤
      collisionUps G ς q n / L * (Ξ ^ k₀ / (k₀.factorial : ℝ)) * (1 - Ξ / (k₀ + 1))⁻¹ := by
  have hUps0 : 0 ≤ collisionUps G ς q n := by
    unfold collisionUps
    refine prod_nonneg fun i _ => ?_
    have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
      (rowsDeg0 G i + collisionR ς i)
    linarith
  have hρ0 : 0 ≤ Ξ / (k₀ + 1) := div_nonneg hΞ (by positivity)
  have hρ1 : Ξ / (k₀ + 1) < 1 := (div_lt_one (by positivity)).mpr hΞk
  have hEq : ∑ k ∈ Ico k₀ m, collisionUpsK G ς π q n k * (Ξ ^ k / (k.factorial : ℝ)) =
      collisionUps G ς q n * ∑ k ∈ Ico k₀ m, Ξ ^ k / (k.factorial : ℝ) := by
    rw [mul_sum]
    refine sum_congr rfl fun k hk => ?_
    rw [collisionUpsK_eq G ς π q n (hk₀.trans (mem_Ico.mp hk).1)]
  have hgeom : ∑ k ∈ Ico k₀ m, Ξ ^ k / (k.factorial : ℝ) ≤
      Ξ ^ k₀ / (k₀.factorial : ℝ) * (1 - Ξ / (k₀ + 1))⁻¹ := by
    rw [sum_Ico_eq_sum_range]
    have hgs : ∑ t ∈ range (m - k₀), (Ξ / (k₀ + 1)) ^ t ≤ (1 - Ξ / (k₀ + 1))⁻¹ := by
      have h1 := geom_sum_mul_neg (Ξ / (k₀ + 1)) (m - k₀)
      have hpos : 0 < 1 - Ξ / (k₀ + 1) := by linarith
      rw [← one_div, le_div_iff₀ hpos, h1]
      linarith [pow_nonneg hρ0 (m - k₀)]
    calc ∑ t ∈ range (m - k₀), Ξ ^ (k₀ + t) / ((k₀ + t).factorial : ℝ)
        ≤ ∑ t ∈ range (m - k₀), Ξ ^ k₀ / (k₀.factorial : ℝ) * (Ξ / (k₀ + 1)) ^ t :=
          sum_le_sum fun t _ => collision_term_le hΞ k₀ t
      _ = Ξ ^ k₀ / (k₀.factorial : ℝ) * ∑ t ∈ range (m - k₀), (Ξ / (k₀ + 1)) ^ t := by
          rw [mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hgs (div_nonneg (pow_nonneg hΞ _) (by positivity))
  rw [hEq]
  calc L⁻¹ * (collisionUps G ς q n * ∑ k ∈ Ico k₀ m, Ξ ^ k / (k.factorial : ℝ))
      ≤ L⁻¹ * (collisionUps G ς q n * (Ξ ^ k₀ / (k₀.factorial : ℝ) * (1 - Ξ / (k₀ + 1))⁻¹)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hgeom hUps0)
          (inv_nonneg.mpr hL.le)
    _ = _ := by ring

end Coarse

/-! ## General one-step sums and lower counts (used in `lem:oct24-collision`(b)) -/

section General

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **The one-step sum with several coincident vertices**: `x'` feasible on `A`, the vertices
`u ∈ A ∩ I` coincident (`x'_u = x_{ψ(u)}`), the others outside `x(U⁺)`. For a new vertex `ℓ`, the
sum of `w_ℓ` over its admissible labels outside `x(U⁺)` is at most
`q 2^{-t} 2^{μ} (1 + e_{t + r_ℓ - μ}(q, n'))`, with `μ` the number of labelled coincident
neighbours `u` of `ℓ` with `ψ(u) ∈ N(ℓ)` (`lem:extraction-merged-count`). -/
theorem collision_oneStep_gen (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (x : U → F) (hx : Function.Injective x)
    (A : Finset U) (ℓ : U) (x' : U → F) (hx' : Feasible F G A x') (I : Finset U) (ψ : U → U)
    (hcoinc : ∀ u ∈ A, u ∈ I → x' u = x (ψ u)) (hother : ∀ u ∈ A, u ∉ I → x' u ∉ univ.image x)
    {n' : ℝ} (hn' : 0 ≤ n') :
    ∑ c ∈ (vertexAdmissible G A x' ℓ).filter (fun c => c ∉ univ.image x),
        collisionW ς x ℓ c ≤
      Fintype.card F * (2 : ℝ)⁻¹ ^ nbrCount G A ℓ *
        2 ^ ((A.filter fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E).filter
          fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ).card *
        (1 + coarseError (nbrCount G A ℓ + collisionR ς ℓ -
          ((A.filter fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E).filter
            fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ).card) (Fintype.card F) n') := by
  set X : Finset F := univ.image x with hX
  set NA := A.filter (fun u => (u, ℓ) ∈ G.E ∨ (ℓ, u) ∈ G.E) with hNA
  set Nl := rowsN ς ℓ with hNl
  let β : NA → F := fun u => x' u
  have hβ : Function.Injective β := fun u w h =>
    Subtype.ext (hx'.1 u (mem_filter.mp u.2).1 w (mem_filter.mp w.2).1 h)
  let γ : Nl → F := fun a => x a
  have hγ : Function.Injective γ := fun a a' h => Subtype.ext (hx h)
  have hm1 : quadraticChar F (-1) = 1 ∨ quadraticChar F (-1) = -1 :=
    quadraticChar_dichotomy (neg_ne_zero.mpr one_ne_zero)
  let s : NA → ℤ := fun u => if (u.1, ℓ) ∈ G.E then 1 else quadraticChar F (-1)
  have hs : ∀ u, s u = 1 ∨ s u = -1 := fun u => by
    simp only [s]
    split_ifs
    · exact Or.inl rfl
    · exact hm1
  let s' : Nl → ℤ := fun a => quadraticChar F (ς a.1 ℓ : F)
  have hs' : ∀ a, s' a = 1 ∨ s' a = -1 := fun a => by
    have ha : ς a.1 ℓ ≠ 0 := by simpa [hNl, rowsN] using a.2
    rcases hς a.1 ℓ with h | h | h
    · exact absurd h ha
    · left
      simp [s', h]
    · simp only [s', h, Int.cast_neg, Int.cast_one]
      exact hm1
  set 𝒳 : Finset F := A.image x' ∪ X with h𝒳
  have hβX : ∀ u, β u ∈ 𝒳 := fun u =>
    mem_union_left _ (mem_image_of_mem x' (mem_filter.mp u.2).1)
  have hγX : ∀ a, γ a ∈ 𝒳 := fun a => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX hn'
  have hset : (vertexAdmissible G A x' ℓ).filter (fun y => y ∉ X) =
      univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i) := by
    ext c
    simp only [vertexAdmissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨hc, hin, hout⟩, hcX⟩
      refine ⟨⟨hc, hcX⟩, fun u => ?_⟩
      have hu := (mem_filter.mp u.2).2
      simp only [s, β]
      split_ifs with h
      · exact hin u (mem_filter.mp u.2).1 h
      · have hvu : (ℓ, u.1) ∈ G.E := hu.resolve_left h
        have h1 := hout u (mem_filter.mp u.2).1 hvu
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul] at h1
        rcases hm1 with h' | h' <;> rw [h'] at h1 ⊢ <;> linarith
    · rintro ⟨⟨hc, hcX⟩, hall⟩
      refine ⟨⟨hc, fun u hu he => ?_, fun u hu he => ?_⟩, hcX⟩
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inl he⟩
        have := hall ⟨u, hmem⟩
        simpa [s, β, he] using this
      · have hmem : u ∈ NA := mem_filter.mpr ⟨hu, Or.inr he⟩
        have hnot : (u, ℓ) ∉ G.E := G.oriented ℓ u he
        have h1 := hall ⟨u, hmem⟩
        simp only [s, β, hnot, ↓reduceIte] at h1
        have : x' u - c = -1 * (c - x' u) := by ring
        rw [this, map_mul, h1]
        rcases hm1 with h' | h' <;> rw [h'] <;> norm_num
  have hsummand : ∀ y ∈ univ.filter (fun y => y ∉ 𝒳 ∧ ∀ i, quadraticChar F (y - β i) = s i),
      collisionW ς x ℓ y = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (y - γ l)) := by
    intro y _
    unfold collisionW
    rw [← prod_coe_sort Nl]
    refine prod_congr rfl fun a _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  have hcardι : Fintype.card NA = nbrCount G A ℓ := by
    rw [Fintype.card_coe]
    rfl
  have hcardκ : Fintype.card Nl = collisionR ς ℓ := Fintype.card_coe _
  have hmerge : mergedCount β γ = (NA.filter fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ).card := by
    unfold mergedCount
    rw [card_filter (fun u => u ∈ I ∧ ψ u ∈ rowsN ς ℓ) NA]
    calc (univ.filter fun il : NA × Nl => β il.1 = γ il.2).card
        = ∑ il : NA × Nl, if β il.1 = γ il.2 then 1 else 0 := card_filter _ _
      _ = ∑ u : NA, ∑ a : Nl, if β u = γ a then 1 else 0 := Fintype.sum_prod_type _
      _ = ∑ u : NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_congr rfl fun u _ => sum_coe_sort Nl (fun a => if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, ∑ a ∈ Nl, if x' u = x a then 1 else 0 :=
          sum_coe_sort NA (fun u => ∑ a ∈ Nl, if x' u = x a then 1 else 0)
      _ = ∑ u ∈ NA, if u ∈ I ∧ ψ u ∈ rowsN ς ℓ then 1 else 0 := by
          refine sum_congr rfl fun u hu => ?_
          have huA := (mem_filter.mp hu).1
          by_cases huI : u ∈ I
          · rw [hcoinc u huA huI]
            simp only [hx.eq_iff]
            rw [sum_ite_eq]
            by_cases hψ : ψ u ∈ rowsN ς ℓ <;> simp [hψ, huI, hNl]
          · simp only [huI, false_and, ↓reduceIte]
            refine sum_eq_zero fun a _ => ?_
            have hno := hother u huA huI
            have : x' u ≠ x a := fun h => hno (h ▸ mem_image_of_mem x (mem_univ a))
            simp only [this, ↓reduceIte]
  rw [hset, sum_congr rfl hsummand]
  rw [hcardι, hcardκ, hmerge] at hmc
  exact hmc

/-- The lower count `|𝓘⁺| ≥ ∏_v q 2^{-t'_v}(1 - e_{t'_v}(q, n))` along any order `o`
(`lem:graphs:sequential`(a)). -/
theorem collision_card_lower_gen (hW : WeilBound F) (G : OrientedGraph U) (o : U → ℕ)
    (ho : Set.InjOn o (univ : Finset U)) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) :
    ∏ v, ((Fintype.card F : ℝ) / 2 ^ nbrCount G (coverRowEarlier univ o v) v *
        (1 - coarseError (nbrCount G (coverRowEarlier univ o v) v) (Fintype.card F) n)) ≤
      (injLabellings F G).card := by
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have het : ∀ v, coarseError (nbrCount G (coverRowEarlier univ o v) v) (Fintype.card F) n < 1 :=
    fun v => lt_of_le_of_lt (coarseError_mono hn0 (coverRow_nbrCount_le G _ v)) (hS1 v)
  have hℓ0 : ∀ v, 0 ≤ (Fintype.card F : ℝ) / 2 ^ nbrCount G (coverRowEarlier univ o v) v *
      (1 - coarseError (nbrCount G (coverRowEarlier univ o v) v) (Fintype.card F) n) :=
    fun v => mul_nonneg (by positivity) (by linarith [het v])
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ o b) x' →
        (Fintype.card F : ℝ) / 2 ^ nbrCount G (coverRowEarlier univ o b) b *
          (1 - coarseError (nbrCount G (coverRowEarlier univ o b) b) (Fintype.card F) n) ≤
        (vertexAdmissible G (coverRowEarlier univ o b) x' b).card := by
    intro b _ x' hx'
    obtain ⟨-, hlo⟩ := card_vertexAdmissible hW G hx' b
    have hsoft := coverRow_softError_le hq1 n (nbrCount G (coverRowEarlier univ o b) b)
    have hA : ((coverRowEarlier univ o b).card : ℝ) ≤ n := by
      have := (card_le_univ (coverRowEarlier univ o b)).trans hn
      exact_mod_cast this
    have hpos : (0 : ℝ) < 2 ^ nbrCount G (coverRowEarlier univ o b) b := by positivity
    have h2A := mul_le_mul_of_nonneg_left hA hpos.le
    rw [div_mul_eq_mul_div, div_le_iff₀ hpos]
    linarith
  have hL : ∀ y : U → F, Feasible F G univ y → (1 : ℝ) ≤ extCount G univ y := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hfe : Feasible F G (univ \ univ) (fun _ => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have h := coverRow_seq_lower G ho _ 1 hℓ0 zero_le_one hstep hL (univ : Finset U).card univ
    rfl subset_rfl (fun _ _ b' _ hb' => absurd (mem_univ b') hb') (fun _ => (0 : F)) hfe
  rw [one_mul, Finset.sdiff_self] at h
  have he : extCount G ∅ (fun _ => (0 : F)) = (injLabellings F G).card := by
    unfold extCount
    congr 1
    exact filter_true_of_mem fun _ _ => by simp
  rwa [he] at h

end General

/-! ## Spectral data -/

section SpecDataForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`lem:oct24-collision`(a) for spectral data** (`def:spec:data`): `G⁺ = D.halfGraph`,
`ς = D.sgn`, `n = |U⁺|`, under `e_Δ(p, 2n) < 1`: `‖T_coll,1‖ ≤ D_1` on `L²(μ)` (in the matrix
normalization of `collision_opBound`). -/
theorem collision_opBound_specData (hW : WeilBound F) (D : Cuts.SpecData V)
    (hne : (injLabellings F D.halfGraph).Nonempty)
    (hS1 : coarseError D.Delta (Fintype.card F) (2 * D.n) < 1)
    (ord : D.cut.Half → D.cut.Half → D.cut.Half → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ') :
    Sarkozy.Influence.OpBound (injLabellings F D.halfGraph) (injLabellings F D.halfGraph)
      (fun x x' => collisionKernel1 D.sgn x x' / (injLabellings F D.halfGraph).card)
      (collisionD1 D.halfGraph D.sgn ord (Fintype.card F) D.n) := by
  refine collision_opBound hW D.halfGraph D.sgn ?_ (fun j k => D.sgn_antisymm j k) hne ?_ ?_ ord
    hord
  · intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp
  · exact le_of_eq (Fintype.card_coe _)
  · intro i
    have hdeg : rowsDeg0 D.halfGraph i ≤ D.Delta := by
      rw [coverRow_rowsDeg0_halfGraph]
      exact (Nat.le_add_right _ _).trans (Finset.le_sup (f := D.dk) (mem_univ i))
    have hn0 : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
    calc coarseError (rowsDeg0 D.halfGraph i) (Fintype.card F) D.n
        ≤ coarseError D.Delta (Fintype.card F) D.n := coarseError_mono hn0 hdeg
      _ ≤ coarseError D.Delta (Fintype.card F) (2 * D.n) :=
          coverRow_coarseError_mono_n _ (by linarith)
      _ < 1 := hS1

end SpecDataForm

end Sarkozy.Extraction

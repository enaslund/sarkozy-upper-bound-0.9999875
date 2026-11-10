module

public import Sarkozy.Extraction.CollisionStrata

@[expose] public section

/-!
# Corollaries of the ordered coincidence bound (`lem:signed-collisions`, `cor:incident-weights`)

`paper/sections/16_extraction.tex`, `lem:signed-collisions` and `cor:incident-weights`, in the
setting and normalization of `Sarkozy.Extraction.CollisionBound` (an operator `T` on `L²(μ)` with
kernel `K` is represented by its matrix `K(x, x')/|𝓘⁺|`, and `OpBound 𝓘⁺ 𝓘⁺ (K/|𝓘⁺|) D` is
`‖T‖ ≤ D`). `WeilBound F` is Weil's theorem (`thm:weil`(a)), the only hypothesis from outside
the paper. `cor:soft-kernels` is not formalized.

## `lem:signed-collisions`

The hypothesis `p ≡ 3 (mod 4)` is `χ(-1) = -1` (`collision_chi_neg_one` derives it from
`|F| ≡ 3 (mod 4)`). Both half labellings are labellings of the same half graph `G⁺`, so they
have the same signed adjacency `A_{ij} = 1[i → j] - 1[j → i]` (`collisionSignedAdj`). The hard
cross kernel is `∏_{(k,i) ∈ E_×} (1 + D_{ki} χ(y_i - x_k))` with `D_{ki} = ς_{ki}`
(`collisionKernel_eq_D`), and `γ_{ij}` is `collisionGamma`.

* `collision_signed_vanish`: `K_coll(x, y) = 0` for `x, y ∈ 𝓘⁺` with `y_i = x_j` and
  `γ_{ij} = 0` (every collision stratum containing `y_i = x_j` vanishes).
* `collision_rowSum_signed_le`, `collision_opBound_signed`: the single-collision row sums and
  `‖T_coll,1‖` are at most `D_1^#` (`collisionD1Sharp`), with `ã_{ij} = γ_{ij} a_{ij}`
  (`collisionAtilde`).
* `collision_rowSum2_signed_edges_le`, `collision_opBound2_signed_edges`: the same for
  `T_coll,≥2` and `D_{≥2}^# = L_int⁻¹ ∑_k q^{-k} Υ_k ∑_{|I|=k} 2^{e(I)} ∏_{i ∈ I} s_i`
  (`collisionD2SharpEdges`, `s_i = collisionSTilde`, `e(I) = collisionEdgesIn`), from
  `collision_stratumI_ratio_edges` (the stratum bound with `2^{e(I)}`, via
  `collision_sum_t_le_edges`). `collision_rowSum2_signed_le` and `collision_opBound2_signed` are
  the weaker forms with `2^{e(I)} ≤ 2^{kΔ⁺/2}` (`collisionD2Sharp`).
* The column bounds ("the transposed argument") are the row bounds: the kernel is symmetric
  (`ς_{kj} = -ς_{jk}`).

## `cor:incident-weights` (hard cross factors)

`collisionAlpha` is `α_{ij}(x) = w_i(x_j) 2^{mg(j,i)}` and `collisionRho` is
`ρ_i(x) = r² ∑_j α_{ij}(x)`.

* `collisionAlpha_le`: `α_{ij}(x) ≤ a_{ij}`.
* `collision_rowSum_incident_le`, `collision_rowSum2_incident_le`: the row sums at `x` of
  `T_coll,1` and `T_coll,≥2` are at most `collisionIncident1`
  (`L_int⁻¹ ∑_{i,j} r² α_{ij}(x) ∏_{ℓ ≠ i}(1 + e_{t^{ij}_ℓ}(p, 2n))`) and `collisionIncident2`
  (`L_int⁻¹ ∑_k Υ_k ∑_{|I|=k} 2^{e(I)} ∏_{i ∈ I} ρ_i(x)`).
* `collision_opBound_incident`, `collision_opBound2_incident`: for the symmetric kernel, the
  norms are at most any common bound `Λ` of these row bounds over `x ∈ 𝓘⁺` (e.g. their suprema).

The proofs keep, at a coincident vertex, its cross factor `w_i(x_{ψ(i)})` instead of its bound
(`collision_stratum_ratio_incident`, `collision_stratumI_le_incident`,
`collision_stratumI_ratio_incident`, copies of the proofs of `lem:oct24-collision`).

## Deviations

* `cor:incident-weights` is formalized for the hard cross factors only (the soft factors of
  `cor:soft-kernels` are not formalized), and only the symmetric case of the operator bounds
  (the hard kernel is symmetric).
* As in `Sarkozy.Extraction.CollisionBound`: coarse errors; only `e_{d⁰_i}(p, n) < 1` is
  used; any `n ≥ |U⁺|`; `Inj_p(G⁺) ≠ ∅` a hypothesis.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Labellings

section Signed

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Fintype U] [DecidableEq U] in
/-- `p ≡ 3 (mod 4)` gives `χ(-1) = -1` (`FiniteField.isSquare_neg_one_iff`). -/
theorem collision_chi_neg_one (hF : Fintype.card F % 4 = 3) : quadraticChar F (-1) = -1 := by
  have hns : ¬ IsSquare (-1 : F) := by
    rw [FiniteField.isSquare_neg_one_iff]
    omega
  exact quadraticChar_neg_one_iff_not_isSquare.mpr hns

/-- The signed adjacency `A_{ij} = 1[i → j] - 1[j → i]` of the half graph `G⁺`. -/
def collisionSignedAdj (G : OrientedGraph U) (i j : U) : ℤ :=
  (if (i, j) ∈ G.E then 1 else 0) - (if (j, i) ∈ G.E then 1 else 0)

/-- The sign test `γ_{ij}`: `A_{kj} D_{ki} ≠ -1` for all `k` and `A_{iℓ} D_{jℓ} ≠ -1` for all
`ℓ`, with the coefficients `D = ς` of the hard cross kernel (`collisionKernel_eq_D`). -/
def collisionGamma (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) : Prop :=
  (∀ k, collisionSignedAdj G k j * ς k i ≠ -1) ∧ (∀ ℓ, collisionSignedAdj G i ℓ * ς j ℓ ≠ -1)

instance (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) : Decidable (collisionGamma G ς i j) := by
  unfold collisionGamma
  exact inferInstance

/-- The new pin weights `ã_{ij} = γ_{ij} 2^{r_i - [j ∈ N(i)] + mg(j, i)} = γ_{ij} a_{ij}`. -/
noncomputable def collisionAtilde (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) : ℝ :=
  if collisionGamma G ς i j then collisionA G ς i j else 0

/-- `s_i = ∑_j ã_{ij}`. -/
noncomputable def collisionSTilde (G : OrientedGraph U) (ς : U → U → ℤ) (i : U) : ℝ :=
  ∑ j, collisionAtilde G ς i j

/-- `D_1^# = (q L_int)⁻¹ ∑_{i,j} ã_{ij} ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n))` (the paper writes
`q = 1/p` for the prefactor). -/
noncomputable def collisionD1Sharp (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    (q : ℝ) (n : ℕ) : ℝ :=
  (q * collisionLint G q n)⁻¹ * ∑ i, ∑ j, collisionAtilde G ς i j *
    ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))

/-- The multiple-collision bound with the new weights,
`L_int⁻¹ ∑_{k=2}^{|U⁺|} Υ_k q^{-k} 2^{kΔ⁺/2} ∑_{|I| = k} ∏_{i ∈ I} s_i`. -/
noncomputable def collisionD2Sharp (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ)
    (q : ℝ) (n : ℕ) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U), collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G)) *
      ∑ I ∈ (univ : Finset U).powersetCard k, ∏ i ∈ I, collisionSTilde G ς i

theorem collisionAtilde_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (i j : U) :
    0 ≤ collisionAtilde G ς i j := by
  unfold collisionAtilde collisionA
  split_ifs <;> positivity

/-- On a feasible labelling `z`, the strict-square constraint of an edge between `u` and `v`
reads `χ(z_v - z_u) = A_{uv}` when `χ(-1) = -1`. -/
theorem collision_edge_sign (G : OrientedGraph U)
    (hm1 : quadraticChar F (-1) = -1) (z : U → F)
    (hz : Feasible F G univ z) {u v : U} (huv : collisionSignedAdj G u v ≠ 0) :
    quadraticChar F (z v - z u) = collisionSignedAdj G u v := by
  unfold collisionSignedAdj at huv ⊢
  by_cases h1 : (u, v) ∈ G.E
  · have h2 : (v, u) ∉ G.E := G.oriented u v h1
    simp only [h1, h2, ↓reduceIte, sub_zero]
    exact hz.2 (u, v) h1 (mem_univ _) (mem_univ _)
  · by_cases h2 : (v, u) ∈ G.E
    · simp only [h1, h2, ↓reduceIte, zero_sub]
      have h := hz.2 (v, u) h2 (mem_univ _) (mem_univ _)
      have : z v - z u = -1 * (z u - z v) := by ring
      rw [this, map_mul, hm1]
      simp only at h
      rw [h]
      norm_num
    · simp [h1, h2] at huv

/-- `χ(ς) = ς` for `ς = ±1` when `χ(-1) = -1`: the hard cross factor is `1 + ς_{ki} χ(y_i - x_k)`,
so the coefficients of `lem:signed-collisions` are `D_{ki} = ς_{ki}`. -/
theorem collision_chi_sign (hm1 : quadraticChar F (-1) = -1)
    {s : ℤ} (hs : s = 1 ∨ s = -1) : quadraticChar F (s : F) = s := by
  rcases hs with rfl | rfl
  · simp
  · simpa using hm1

omit [DecidableEq U] in
/-- The hard cross kernel as `∏_{(k,i) ∈ E_×} (1 + D_{ki} χ(y_i - x_k))` with `D = ς`. -/
theorem collisionKernel_eq_D (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hm1 : quadraticChar F (-1) = -1) (x y : U → F) :
    collisionKernel ς x y =
      ∏ e ∈ collisionCross ς, (1 + (ς e.1 e.2 : ℝ) * (quadraticChar F (y e.2 - x e.1) : ℝ)) := by
  unfold collisionKernel
  refine prod_congr rfl fun e he => ?_
  have hne : ς e.1 e.2 ≠ 0 := (mem_filter.mp he).2
  have hs : ς e.1 e.2 = 1 ∨ ς e.1 e.2 = -1 := (hς e.1 e.2).resolve_left hne
  rw [map_mul, collision_chi_sign hm1 hs]
  push_cast
  ring

/-- **`lem:signed-collisions`, vanishing**: if `χ(-1) = -1` (`p ≡ 3 mod 4`), every collision
stratum containing `y_i = x_j` vanishes when `γ_{ij} = 0`: `K_coll(x, y) = 0` for all
`x, y ∈ 𝓘⁺` with `y_i = x_j`. -/
theorem collision_signed_vanish (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hm1 : quadraticChar F (-1) = -1)
    {x y : U → F} (hx : x ∈ injLabellings F G) (hy : y ∈ injLabellings F G) {i j : U}
    (hij : y i = x j) (hγ : ¬ collisionGamma G ς i j) : collisionKernel ς x y = 0 := by
  have hxF : Feasible F G univ x := by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx
  have hyF : Feasible F G univ y := by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
    exact hy
  unfold collisionGamma at hγ
  rw [not_and_or] at hγ
  simp only [not_forall, not_not] at hγ
  unfold collisionKernel
  rcases hγ with ⟨k, hk⟩ | ⟨ℓ, hℓ⟩
  · have hA : collisionSignedAdj G k j ≠ 0 := fun h => by rw [h, zero_mul] at hk; omega
    have hs0 : ς k i ≠ 0 := fun h => by rw [h, mul_zero] at hk; omega
    have hs : ς k i = 1 ∨ ς k i = -1 := (hς k i).resolve_left hs0
    refine prod_eq_zero (i := (k, i)) (mem_filter.mpr ⟨mem_univ _, hs0⟩) ?_
    simp only
    rw [hij, map_mul, collision_edge_sign G hm1 x hxF hA, collision_chi_sign hm1 hs]
    have : ((ς k i * collisionSignedAdj G k j : ℤ) : ℝ) = -1 := by
      rw [mul_comm, hk]
      norm_num
    push_cast at this ⊢
    linarith
  · have hA : collisionSignedAdj G i ℓ ≠ 0 := fun h => by rw [h, zero_mul] at hℓ; omega
    have hs0 : ς j ℓ ≠ 0 := fun h => by rw [h, mul_zero] at hℓ; omega
    have hs : ς j ℓ = 1 ∨ ς j ℓ = -1 := (hς j ℓ).resolve_left hs0
    refine prod_eq_zero (i := (j, ℓ)) (mem_filter.mpr ⟨mem_univ _, hs0⟩) ?_
    simp only
    rw [← hij, map_mul, collision_edge_sign G hm1 y hyF hA, collision_chi_sign hm1 hs]
    have : ((ς j ℓ * collisionSignedAdj G i ℓ : ℤ) : ℝ) = -1 := by
      rw [mul_comm, hℓ]
      norm_num
    push_cast at this ⊢
    linarith

/-- **`lem:signed-collisions`, single collisions**: if `χ(-1) = -1`, the row sums of
`T_coll,1` at every `x ∈ 𝓘⁺` are at most `D_1^#`, the bound `D_1` of `lem:oct24-collision`(a)
with the pin weights `ã_{ij} = γ_{ij} a_{ij}`: the strata `(i, j)` with `γ_{ij} = 0` vanish. -/
theorem collision_rowSum_signed_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hm1 : quadraticChar F (-1) = -1)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : x ∈ injLabellings F G) :
    (graphLaw G hne).expect (collisionKernel1 ς x) ≤
      collisionD1Sharp G ς ord (Fintype.card F) n := by
  have hxinj : Function.Injective x := fun a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  have hstr : ∀ i j, ∑ y ∈ injLabellings F G,
      (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
        ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
          (collisionAtilde G ς i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card := by
    intro i j
    by_cases hγ : collisionGamma G ς i j
    · have h := collision_stratum_ratio hW G ς hς ord hord x hxinj hn hS1 i j
      unfold collisionAtilde
      rw [ite_eq_left hγ]
      exact h
    · have h0 : ∑ y ∈ injLabellings F G,
          (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) =
            0 := sum_eq_zero fun y hy => by
        split_ifs with hc
        · exact collision_signed_vanish G ς hς hm1 hx hy hc.1 hγ
        · rfl
      rw [h0]
      unfold collisionAtilde
      rw [ite_eq_right hγ]
      simp
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
          (collisionAtilde G ς i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hstr i j
    _ = collisionD1Sharp G ς ord (Fintype.card F) n * (injLabellings F G).card := by
        unfold collisionD1Sharp
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, sum_mul]

omit [Field F] [Fintype F] [DecidableEq F] in
/-- `∑_{ψ : I → U⁺} ∏_{l ∈ I} ã_{l, ψ(l)} = ∏_{l ∈ I} s_l`. -/
theorem collision_sum_maps_atilde (G : OrientedGraph U) (ς : U → U → ℤ) (I : Finset U) :
    ∑ ψ : (I → U), ∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l) =
      ∏ l ∈ I, collisionSTilde G ς l := by
  unfold collisionSTilde
  rw [← prod_coe_sort I (fun l => ∑ j, collisionAtilde G ς l j), Fintype.prod_sum]
  refine sum_congr rfl fun ψ _ => ?_
  rw [← prod_coe_sort I]
  refine prod_congr rfl fun l _ => ?_
  rw [collisionExt_coe]

/-- **`lem:signed-collisions`, multiple collisions**: if `χ(-1) = -1`, the row sums of
`T_coll,≥2` at every `x ∈ 𝓘⁺` are at most
`L_int⁻¹ ∑_{k=2}^{|U⁺|} Υ_k q^{-k} 2^{kΔ⁺/2} ∑_{|I| = k} ∏_{i ∈ I} s_i`: the strata `(I, ψ)`
with `γ_{l, ψ(l)} = 0` for some `l ∈ I` vanish, and the sum over all maps `ψ` of
`∏_{l ∈ I} ã_{l, ψ(l)}` factors as `∏_{l ∈ I} s_l`. -/
theorem collision_rowSum2_signed_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hm1 : quadraticChar F (-1) = -1)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : x ∈ injLabellings F G) :
    (graphLaw G hne).expect (collisionKernel2 ς x) ≤
      collisionD2Sharp G ς π (Fintype.card F) n := by
  have hxinj : Function.Injective x := fun a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set N : ℝ := ((injLabellings F G).card : ℝ) with hNdef
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  set c : ℕ → ℝ := fun k => (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G)) with hc
  have hstr : ∀ k ∈ Icc 2 (Fintype.card U), ∀ I ∈ (univ : Finset U).powersetCard k,
      ∀ ψ : (I → U), ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
        c k * (∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l)) * N := by
    intro k _ I hI ψ
    have hIk : I.card = k := (mem_powersetCard.mp hI).2
    by_cases hall : ∀ l ∈ I, collisionGamma G ς l (collisionExt I ψ l)
    · have hprod : ∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l) =
          ∏ l ∈ I, collisionA G ς l (collisionExt I ψ l) :=
        prod_congr rfl fun l hl => by
          unfold collisionAtilde
          rw [ite_eq_left (hall l hl)]
      have h := collision_stratumI_ratio hW G ς hς π hπ x hxinj hn hS1 I (collisionExt I ψ)
      rw [hIk] at h
      rw [hprod]
      refine h.trans (le_of_eq ?_)
      simp only [hc]
      ring
    · push Not at hall
      obtain ⟨l, hl, hγl⟩ := hall
      have h0 : ∑ y ∈ injLabellings F G,
          (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
            collisionKernel ς x y else 0) = 0 := sum_eq_zero fun y hy => by
        split_ifs with hcond
        · exact collision_signed_vanish G ς hς hm1 hx hy (hcond.1 l hl) hγl
        · rfl
      have hp0 : ∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l) = 0 :=
        prod_eq_zero hl (by unfold collisionAtilde; rw [ite_eq_right hγl])
      rw [h0, hp0]
      simp
  calc ∑ y ∈ injLabellings F G, collisionKernel2 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ k ∈ Icc 2 (Fintype.card U),
          ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel2_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          ∑ y ∈ injLabellings F G,
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        rw [sum_comm]
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          c k * (∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l)) * N :=
        sum_le_sum fun k hk => sum_le_sum fun I hI => sum_le_sum fun ψ _ => hstr k hk I hI ψ
    _ = ∑ k ∈ Icc 2 (Fintype.card U), c k * N *
          ∑ I ∈ (univ : Finset U).powersetCard k, ∏ i ∈ I, collisionSTilde G ς i := by
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun I _ => ?_
        rw [← collision_sum_maps_atilde G ς I, mul_sum]
        refine sum_congr rfl fun ψ _ => ?_
        ring
    _ = collisionD2Sharp G ς π q n * N := by
        unfold collisionD2Sharp
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        simp only [hc]
        ring

/-- **`lem:signed-collisions`, operator bound (single collisions)**: `‖T_coll,1‖ ≤ D_1^#` on
`L²(μ)` (matrix normalization of `collision_opBound`). The kernel is symmetric
(`ς_{kj} = -ς_{jk}`), so the column sums are row sums, and Schur's test applies. -/
theorem collision_opBound_signed (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hm1 : quadraticChar F (-1) = -1) (hne : (injLabellings F G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ') :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel1 ς x x' / (injLabellings F G).card)
      (collisionD1Sharp G ς ord (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel1 ς x x' / (injLabellings F G).card ≤
        collisionD1Sharp G ς ord (Fintype.card F) n := by
    intro x hx
    have h := collision_rowSum_signed_le hW G ς hς hm1 hne hn hS1 ord hord x hx
    rw [coverRow_expect_graphLaw] at h
    rwa [← sum_div]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel1 ς x x' / (injLabellings F G).card ≤
        collisionD1Sharp G ς ord (Fintype.card F) n := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel1 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel1 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [collisionKernel1_symm ς hanti]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ collisionD1Sharp G ς ord (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel1_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel1_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

/-- **`lem:signed-collisions`, operator bound (multiple collisions)**: `‖T_coll,≥2‖` is at most
the bound of `collision_rowSum2_signed_le` (symmetric kernel, Schur's test). -/
theorem collision_opBound2_signed (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hm1 : quadraticChar F (-1) = -1) (hne : (injLabellings F G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel2 ς x x' / (injLabellings F G).card)
      (collisionD2Sharp G ς π (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hsymm : ∀ x x' : U → F, collisionKernel2 ς x x' = collisionKernel2 ς x' x := by
    intro x x'
    unfold collisionKernel2
    rw [collisionCommon_symm, collisionKernel_symm ς hanti]
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤
        collisionD2Sharp G ς π (Fintype.card F) n := by
    intro x hx
    have h := collision_rowSum2_signed_le hW G ς hς hm1 hne hn hS1 π hπ x hx
    rw [coverRow_expect_graphLaw] at h
    rwa [← sum_div]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤
        collisionD2Sharp G ς π (Fintype.card F) n := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel2 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel2 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [hsymm]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ collisionD2Sharp G ς π (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel2_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel2_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

/-- `e(I)`, the number of edges of `G⁺` inside `I`. -/
def collisionEdgesIn (G : OrientedGraph U) (I : Finset U) : ℕ :=
  (G.E.filter fun e => e.1 ∈ I ∧ e.2 ∈ I).card

omit [Field F] [Fintype F] [DecidableEq F] in
/-- With `I` labelled first, the earlier neighbours of the vertices of `I` number at most `e(I)`:
each edge inside `I` is counted at its later endpoint. -/
theorem collision_sum_t_le_edges (G : OrientedGraph U) (p : U → ℕ) (I : Finset U) :
    ∑ v ∈ I, nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v ≤ collisionEdgesIn G I := by
  set S := (I ×ˢ I).filter fun uv : U × U => p uv.1 < p uv.2 ∧
    ((uv.1, uv.2) ∈ G.E ∨ (uv.2, uv.1) ∈ G.E) with hS
  have h1 : ∀ v ∈ I, nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v ≤
      (I.filter fun u => p u < p v ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E)).card := by
    intro v hv
    unfold nbrCount
    refine card_le_card fun u hu => ?_
    have hu1 := (mem_filter.mp hu).1
    have hu2 := (mem_filter.mp hu).2
    obtain ⟨huI, hlt⟩ := collision_earlierI_of_mem p I hv hu1
    exact mem_filter.mpr ⟨huI, hlt, hu2⟩
  have h2 : ∑ v ∈ I, (I.filter fun u => p u < p v ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E)).card =
      S.card := by
    rw [hS, card_filter, sum_product_right]
    refine sum_congr rfl fun v _ => ?_
    rw [card_filter]
  -- pairs `(u, v)` with `p u < p v` and an edge between them inject into the edges inside `I`
  have h3 : S.card ≤ collisionEdgesIn G I := by
    unfold collisionEdgesIn
    refine card_le_card_of_injOn (fun uv => if (uv.1, uv.2) ∈ G.E then (uv.1, uv.2) else
      (uv.2, uv.1)) ?_ ?_
    · intro uv huv
      have huv' := mem_filter.mp huv
      obtain ⟨h1', h2'⟩ := mem_product.mp huv'.1
      simp only [coe_filter, Set.mem_ofPred_eq]
      split_ifs with he
      · exact ⟨he, h1', h2'⟩
      · exact ⟨huv'.2.2.resolve_left he, h2', h1'⟩
    · intro uv huv uv' huv' heq
      have hlt := (mem_filter.mp huv).2.1
      have hlt' := (mem_filter.mp huv').2.1
      simp only at heq
      split_ifs at heq with ha hb hb
      · exact heq
      · have e1 : uv.1 = uv'.2 := (Prod.ext_iff.mp heq).1
        have e2 : uv.2 = uv'.1 := (Prod.ext_iff.mp heq).2
        rw [e1, e2] at hlt
        omega
      · have e1 : uv.2 = uv'.1 := (Prod.ext_iff.mp heq).1
        have e2 : uv.1 = uv'.2 := (Prod.ext_iff.mp heq).2
        rw [e1, e2] at hlt
        omega
      · have e1 : uv.2 = uv'.2 := (Prod.ext_iff.mp heq).1
        have e2 : uv.1 = uv'.1 := (Prod.ext_iff.mp heq).2
        exact Prod.ext e2 e1
  calc ∑ v ∈ I, nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v
      ≤ ∑ v ∈ I, (I.filter fun u => p u < p v ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E)).card :=
        sum_le_sum h1
    _ = S.card := h2
    _ ≤ collisionEdgesIn G I := h3

/-- **One stratum `(I, ψ)`, normalized, with `2^{e(I)}`**: with `k = |I|` and the order `π_k`,
the stratum sum of `K_coll(x, ·)` is at most
`L_int⁻¹ Υ_k q^{-k} 2^{e(I)} ∏_{l ∈ I} a_{l, ψ(l)} · |𝓘⁺|` (`collision_stratumI_ratio` before the
bound `2^{e(I)} ≤ 2^{kΔ⁺/2}`). -/
theorem collision_stratumI_ratio_edges (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (I : Finset U) (ψ : U → U) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      (collisionLint G (Fintype.card F) n)⁻¹ * collisionUpsK G ς π (Fintype.card F) n I.card *
        ((Fintype.card F : ℝ)⁻¹ ^ I.card * (2 : ℝ) ^ collisionEdgesIn G I *
          ∏ l ∈ I, collisionA G ς l (ψ l)) * (injLabellings F G).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set k := I.card with hk
  set p := π k with hp
  set o := collisionOrdI p I with ho
  set t' : U → ℕ := fun v => nbrCount G (coverRowEarlier univ o v) v with ht'
  set eK : U → ℝ := fun v => coarseError (collisionTk G ς π k v) q (2 * n) with heK
  have het : ∀ v, coarseError (t' v) q n ≤ coarseError (rowsDeg0 G v) q n :=
    fun v => coarseError_mono hn0 (coverRow_nbrCount_le G _ v)
  have het1 : ∀ v, 0 < 1 - coarseError (t' v) q n := fun v => by linarith [het v, hS1 v]
  have heK0 : ∀ v, 0 ≤ eK v := fun v => coarseError_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) _
  have hstr := collision_stratumI_le hW G ς hς p (hπ k) x hx n I ψ (le_refl k)
  have hlow := collision_card_lower_gen hW G o (collisionOrdI_injOn p (hπ k) I univ) hn hS1
  set ℓf : U → ℝ := fun v => q / 2 ^ t' v * (1 - coarseError (t' v) q n) with hℓf
  set num : U → ℝ := fun v => if v ∈ I then
      2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) * 2 ^ t' v * q⁻¹
    else 2 ^ collisionMuI G ς p I ψ v * (1 + eK v) with hnum
  -- `M_v = (num_v / (1 - e_{t'_v})) ℓ_v`
  have hM : ∀ v, collisionMI G ς p I ψ q n k v = num v / (1 - coarseError (t' v) q n) * ℓf v := by
    intro v
    have h1 := (het1 v).ne'
    unfold collisionMI
    by_cases hv : v ∈ I
    · rw [ite_eq_left hv]
      simp only [hnum, hℓf, hv, ↓reduceIte]
      field_simp
    · rw [ite_eq_right hv]
      simp only [hnum, hℓf, hv, ↓reduceIte, heK, collisionTk, inv_pow]
      field_simp
      simp only [ht', hp, ho]
      ring
  have hprodM : ∏ v, collisionMI G ς p I ψ q n k v =
      (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := by
    rw [prod_congr rfl fun v _ => hM v, prod_mul_distrib, prod_div_distrib]
  have hLle : collisionLint G q n ≤ ∏ v, (1 - coarseError (t' v) q n) :=
    prod_le_prod₀ (fun v _ => by linarith [hS1 v]) (fun v _ => by linarith [het v])
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hfilt : univ.filter (fun v => v ∈ I) = I := by
    ext v
    simp
  -- the numerator
  have hnum_le : ∏ v, num v ≤ collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I * ∏ l ∈ I, collisionA G ς l (ψ l)) := by
    have hsplit : ∏ v, num v = (∏ v ∈ I, (2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) *
        2 ^ t' v * q⁻¹)) * ∏ v ∈ univ.filter (fun v => v ∉ I),
          (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) := by
      simp only [hnum]
      rw [prod_ite, hfilt]
    have hI : ∏ v ∈ I, (2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) * 2 ^ t' v * q⁻¹) =
        (∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
          (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, ← prod_pow_eq_pow_sum]
    have hJ : ∏ v ∈ univ.filter (fun v => v ∉ I), (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) =
        (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
          ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    -- the pieces
    have hP1 : (2 : ℝ) ^ (∑ v ∈ I, t' v) ≤ (2 : ℝ) ^ collisionEdgesIn G I :=
      pow_le_pow_right₀ (by norm_num) (collision_sum_t_le_edges G p I)
    have hP2 : (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) ≤
        ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [prod_pow_eq_pow_sum]
      exact pow_le_pow_right₀ (by norm_num) (collision_sum_muI_le G ς p I ψ)
    have hP3 : ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) ≤ collisionUpsK G ς π q n k := by
      unfold collisionUpsK
      rw [← prod_filter_mul_prod_filter_not univ (fun v => v ∈ I)]
      refine le_mul_of_one_le_left (prod_nonneg fun v _ => by linarith [heK0 v]) ?_
      exact one_le_prod₀ fun v _ => by linarith [heK0 v]
    have hP4 : ∏ l ∈ I, collisionA G ς l (ψ l) =
        (∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
          ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun l _ => ?_
      unfold collisionA
      rw [pow_add]
    have hA0 : 0 ≤ ∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0) := by
      positivity
    have hU0 : 0 ≤ ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hq0' : 0 ≤ q⁻¹ ^ k := by positivity
    calc ∏ v, num v
        = ((∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
            (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k) *
          ((2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
            ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v)) := by
          rw [hsplit, hI, hJ]
      _ ≤ ((∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
            (2 : ℝ) ^ collisionEdgesIn G I * q⁻¹ ^ k) *
          ((∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l) * collisionUpsK G ς π q n k) := by
          refine mul_le_mul ?_ ?_ (mul_nonneg (by positivity) hU0) (by positivity)
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hA0) hq0'
          · exact mul_le_mul hP2 hP3 hU0 (by positivity)
      _ = _ := by rw [hP4]; ring
  have hnum0 : 0 ≤ ∏ v, num v := prod_nonneg fun v _ => by
    by_cases hv : v ∈ I
    · simp only [hnum, hv, ↓reduceIte]
      positivity
    · simp only [hnum, hv, ↓reduceIte]
      exact mul_nonneg (by positivity) (by linarith [heK0 v])
  have hQpos : 0 < ∏ v, (1 - coarseError (t' v) q n) := prod_pos fun v _ => het1 v
  have hℓ0 : 0 ≤ ∏ v, ℓf v := prod_nonneg fun v _ => mul_nonneg (by positivity) (het1 v).le
  have hC0 : 0 ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I * ∏ l ∈ I, collisionA G ς l (ψ l)) := by
    have hU : 0 ≤ collisionUpsK G ς π q n k :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hA : 0 ≤ ∏ l ∈ I, collisionA G ς l (ψ l) :=
      prod_nonneg fun l _ => by unfold collisionA; positivity
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hU) (by positivity)
  calc _ ≤ ∏ v, collisionMI G ς p I ψ q n k v := hstr
    _ = (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := hprodM
    _ ≤ (∏ v, num v) / collisionLint G q n * ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        exact div_le_div_of_nonneg_left hnum0 hLpos hLle
    _ ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
          (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I * ∏ l ∈ I, collisionA G ς l (ψ l)) *
          ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        rw [div_eq_inv_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left hnum_le (inv_nonneg.mpr hLpos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hC0

/-- `D_{≥2}^# = L_int⁻¹ ∑_{k=2}^{|U⁺|} q^{-k} Υ_k ∑_{|I| = k} 2^{e(I)} ∏_{i ∈ I} s_i`
(the paper writes `q = 1/p`). -/
noncomputable def collisionD2SharpEdges (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ)
    (q : ℝ) (n : ℕ) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U), q⁻¹ ^ k * collisionUpsK G ς π q n k *
    ∑ I ∈ (univ : Finset U).powersetCard k,
      (2 : ℝ) ^ collisionEdgesIn G I * ∏ i ∈ I, collisionSTilde G ς i

/-- **`lem:signed-collisions`, multiple collisions** (the paper's `D_{≥2}^#`): if `χ(-1) = -1`,
the row sums of `T_coll,≥2` at every `x ∈ 𝓘⁺` are at most
`L_int⁻¹ ∑_{k=2}^{|U⁺|} q^{-k} Υ_k ∑_{|I| = k} 2^{e(I)} ∏_{i ∈ I} s_i`. -/
theorem collision_rowSum2_signed_edges_le (hW : WeilBound F) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hm1 : quadraticChar F (-1) = -1) (hne : (injLabellings F G).Nonempty) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k)) (x : U → F)
    (hx : x ∈ injLabellings F G) :
    (graphLaw G hne).expect (collisionKernel2 ς x) ≤
      collisionD2SharpEdges G ς π (Fintype.card F) n := by
  have hxinj : Function.Injective x := fun a b h => by
    simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
    exact hx.1 a (mem_univ _) b (mem_univ _) h
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set N : ℝ := ((injLabellings F G).card : ℝ) with hNdef
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  set c : ℕ → Finset U → ℝ := fun k I => (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I) with hc
  have hstr : ∀ k ∈ Icc 2 (Fintype.card U), ∀ I ∈ (univ : Finset U).powersetCard k,
      ∀ ψ : (I → U), ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
        c k I * (∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l)) * N := by
    intro k _ I hI ψ
    have hIk : I.card = k := (mem_powersetCard.mp hI).2
    by_cases hall : ∀ l ∈ I, collisionGamma G ς l (collisionExt I ψ l)
    · have hprod : ∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l) =
          ∏ l ∈ I, collisionA G ς l (collisionExt I ψ l) :=
        prod_congr rfl fun l hl => by
          unfold collisionAtilde
          rw [ite_eq_left (hall l hl)]
      have h := collision_stratumI_ratio_edges hW G ς hς π hπ x hxinj hn hS1 I (collisionExt I ψ)
      rw [hIk] at h
      rw [hprod]
      refine h.trans (le_of_eq ?_)
      simp only [hc]
      ring
    · push Not at hall
      obtain ⟨l, hl, hγl⟩ := hall
      have h0 : ∑ y ∈ injLabellings F G,
          (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
            collisionKernel ς x y else 0) = 0 := sum_eq_zero fun y hy => by
        split_ifs with hcond
        · exact collision_signed_vanish G ς hς hm1 hx hy (hcond.1 l hl) hγl
        · rfl
      have hp0 : ∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l) = 0 :=
        prod_eq_zero hl (by unfold collisionAtilde; rw [ite_eq_right hγl])
      rw [h0, hp0]
      simp
  calc ∑ y ∈ injLabellings F G, collisionKernel2 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ k ∈ Icc 2 (Fintype.card U),
          ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel2_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          ∑ y ∈ injLabellings F G,
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        rw [sum_comm]
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          c k I * (∏ l ∈ I, collisionAtilde G ς l (collisionExt I ψ l)) * N :=
        sum_le_sum fun k hk => sum_le_sum fun I hI => sum_le_sum fun ψ _ => hstr k hk I hI ψ
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k,
          c k I * N * ∏ i ∈ I, collisionSTilde G ς i := by
        refine sum_congr rfl fun k _ => sum_congr rfl fun I _ => ?_
        rw [← collision_sum_maps_atilde G ς I, mul_sum]
        refine sum_congr rfl fun ψ _ => ?_
        ring
    _ = collisionD2SharpEdges G ς π q n * N := by
        unfold collisionD2SharpEdges
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        refine sum_congr rfl fun I _ => ?_
        simp only [hc]
        ring

/-- **`lem:signed-collisions`, operator bound with `D_{≥2}^#`**: `‖T_coll,≥2‖ ≤ D_{≥2}^#` on
`L²(μ)` (symmetric kernel, Schur's test). -/
theorem collision_opBound2_signed_edges (hW : WeilBound F) (G : OrientedGraph U)
    (ς : U → U → ℤ) (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1)
    (hanti : ∀ j k, ς k j = -ς j k) (hm1 : quadraticChar F (-1) = -1)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel2 ς x x' / (injLabellings F G).card)
      (collisionD2SharpEdges G ς π (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hsymm : ∀ x x' : U → F, collisionKernel2 ς x x' = collisionKernel2 ς x' x := by
    intro x x'
    unfold collisionKernel2
    rw [collisionCommon_symm, collisionKernel_symm ς hanti]
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤
        collisionD2SharpEdges G ς π (Fintype.card F) n := by
    intro x hx
    have h := collision_rowSum2_signed_edges_le hW G ς hς hm1 hne hn hS1 π hπ x hx
    rw [coverRow_expect_graphLaw] at h
    rwa [← sum_div]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤
        collisionD2SharpEdges G ς π (Fintype.card F) n := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel2 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel2 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [hsymm]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ collisionD2SharpEdges G ς π (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel2_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel2_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

end Signed

/-! ## Incident weights at coincident vertices (`cor:incident-weights`, hard cross factors) -/

section Incident

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The incident weight `α_{ij}(x) = w_i(x_j) 2^{mg(j, i)}`, `w_i(y) = ∏_{l ∈ N(i)}
(1 + χ(ς_{li}(y - x_l)))` the cross factor of the `x'`-vertex `i` at the label `y`. -/
noncomputable def collisionAlpha (G : OrientedGraph U) (ς : U → U → ℤ) (x : U → F) (i j : U) :
    ℝ :=
  collisionW ς x i (x j) * 2 ^ rowsMg G ς j i

/-- `ρ_i(x) = r² ∑_{j ∈ U⁺} α_{ij}(x)`, `r² = q⁻¹`. -/
noncomputable def collisionRho (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (x : U → F) (i : U) :
    ℝ :=
  (Real.sqrt q)⁻¹ ^ 2 * ∑ j, collisionAlpha G ς x i j

/-- The single-collision row bound with incident weights,
`L_int⁻¹ ∑_{i,j} r² α_{ij}(x) ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n))`. -/
noncomputable def collisionIncident1 (G : OrientedGraph U) (ς : U → U → ℤ)
    (ord : U → U → U → ℕ) (q : ℝ) (n : ℕ) (x : U → F) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ i, ∑ j, (Real.sqrt q)⁻¹ ^ 2 * collisionAlpha G ς x i j *
    ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))

omit [Fintype U] in
/-- **`cor:incident-weights`**, `α_{ij}(x) ≤ a_{ij}`: the factor of `l = j` is `1 + χ(0) = 1`
and every other factor is at most `2`. -/
theorem collisionAlpha_le (G : OrientedGraph U) (ς : U → U → ℤ) (x : U → F) (i j : U)
    [Fintype U] : collisionAlpha G ς x i j ≤ collisionA G ς i j := by
  unfold collisionAlpha collisionA
  rw [pow_add]
  exact mul_le_mul_of_nonneg_right (collisionW_at_le ς x i j) (by positivity)

/-- **One stratum, normalized, with the incident weight**: the sum of `K_coll(x, ·)` over the
stratum `(i, j)` is at most `(q L_int)⁻¹ α_{ij}(x) ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n)) · |𝓘⁺|`. -/
theorem collision_stratum_ratio_incident (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (i j : U) :
    ∑ y ∈ injLabellings F G,
        (if y i = x j ∧ ∀ ℓ, ℓ ≠ i → y ℓ ∉ univ.image x then collisionKernel ς x y else 0) ≤
      ((Fintype.card F : ℝ) * collisionLint G (Fintype.card F) n)⁻¹ *
        (collisionAlpha G ς x i j * ∏ ℓ ∈ univ.erase i,
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
  have hw0 := collisionW_nonneg ς x i (x j)
  have he00 : 0 < 1 - coarseError 0 q n := by
    linarith [coarseError_mono (q := q) hn0 (Nat.zero_le (rowsDeg0 G i)), hS1 i]
  -- the key inequality: `w_i(x_j) ∏ M ≤ (q L)⁻¹ a ∏(1 + e) ∏ ℓ`
  have hkey : collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ ≤
      (q * collisionLint G q n)⁻¹ * (collisionAlpha G ς x i j * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) *
        ∏ v, ℓf v := by
    rw [hprodM, hprodℓ]
    set P := ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)
    set Q := ∏ ℓ ∈ univ.erase i, (1 - coarseError (t' ℓ) q n)
    set ℓ' := ∏ ℓ ∈ univ.erase i, ℓf ℓ
    set L := collisionLint G q n
    set w := collisionW ς x i (x j)
    set A := collisionAlpha G ς x i j
    -- `w 2^{mg} L ≤ A (1 - e_0) Q`
    have h1 : w * 2 ^ rowsMg G ς j i * L ≤ A * ((1 - coarseError 0 q n) * Q) := by
      have hA' : w * 2 ^ rowsMg G ς j i ≤ A := le_rfl
      have hA0 : 0 ≤ A := mul_nonneg hw0 (by positivity)
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
      (collisionAlpha G ς x i j * ∏ ℓ ∈ univ.erase i, (1 + eT ℓ)) := by
    refine mul_nonneg (inv_nonneg.mpr (mul_pos hq0 hLpos).le) (mul_nonneg ?_ hP0)
    exact mul_nonneg hw0 (by positivity)
  calc _ ≤ collisionW ς x i (x j) * ∏ ℓ ∈ univ.erase i, collisionM G ς ord q n i j ℓ := hstr
    _ ≤ _ := hkey
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hcoef

/-- **`cor:incident-weights`, single collisions**: the row sum of `T_coll,1` at `x ∈ 𝓘⁺` is at
most `L_int⁻¹ ∑_{i,j} r² α_{ij}(x) ∏_{ℓ ≠ i} (1 + e_{t^{ij}_ℓ}(q, 2n))` (hard cross factors,
the orders of `lem:oct24-collision`(a)). -/
theorem collision_rowSum_incident_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (x : U → F) (hx : Function.Injective x) :
    (graphLaw G hne).expect (collisionKernel1 ς x) ≤
      collisionIncident1 G ς ord (Fintype.card F) n x := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
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
          (collisionAlpha G ς x i j * ∏ ℓ ∈ univ.erase i,
            (1 + coarseError (collisionT G ς ord i j ℓ) (Fintype.card F) (2 * n))) *
          (injLabellings F G).card :=
        sum_le_sum fun i _ => sum_le_sum fun j _ =>
          collision_stratum_ratio_incident hW G ς hς ord hord x hx hn hS1 i j
    _ = collisionIncident1 G ς ord (Fintype.card F) n x * (injLabellings F G).card := by
        unfold collisionIncident1
        rw [coverRow_r_sq hq0, mul_sum, sum_mul]
        refine sum_congr rfl fun i _ => ?_
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun j _ => ?_
        rw [mul_inv]
        ring


/-- The one-step bounds of the stratum `(I, ψ)` with incident weights: `w_v(x_{ψ(v)})` at
`v ∈ I`, as `collisionMI` at `v ∉ I`. -/
noncomputable def collisionMIw (G : OrientedGraph U) (ς : U → U → ℤ) (p : U → ℕ) (I : Finset U)
    (ψ : U → U) (x : U → F) (q : ℝ) (n k : ℕ) (v : U) : ℝ :=
  if v ∈ I then collisionW ς x v (x (ψ v))
  else q * (2 : ℝ)⁻¹ ^ nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v *
    2 ^ collisionMuI G ς p I ψ v *
    (1 + coarseError (min (collisionR ς v + rowsDeg0 G v) (collisionR ς v + collisionB G p v + k))
      q (2 * n))

theorem collisionMIw_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (p : U → ℕ) (I : Finset U)
    (ψ : U → U) (x : U → F) {q : ℝ} (hq : 0 ≤ q) (n k : ℕ) (v : U) :
    0 ≤ collisionMIw G ς p I ψ x q n k v := by
  unfold collisionMIw
  have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
    (min (collisionR ς v + rowsDeg0 G v) (collisionR ς v + collisionB G p v + k))
  by_cases hv : v ∈ I
  · rw [ite_eq_left hv]
    exact collisionW_nonneg ς x v _
  · rw [ite_eq_right hv]
    exact mul_nonneg (by positivity) (by linarith)

/-- **The stratum `(I, ψ)` with incident weights**: as `collision_stratumI_le`, keeping at a
coincident vertex `v ∈ I` its cross factor `w_v(x_{ψ(v)})`. -/
theorem collision_stratumI_le_incident (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (p : U → ℕ) (hp : Function.Injective p)
    (x : U → F) (hx : Function.Injective x) (n : ℕ) (I : Finset U) (ψ : U → U) {k : ℕ}
    (hk : I.card ≤ k) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      ∏ v, collisionMIw G ς p I ψ x (Fintype.card F) n k v := by
  set X : Finset F := univ.image x with hX
  set ord' := collisionOrdI p I with hord'
  have hinj := collisionOrdI_injOn p hp I univ
  have hq0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord' a ≤ ord' b → y a = y' a) →
        collisionPhiI ς p x I ψ b y = collisionPhiI ς p x I ψ b y' := by
    intro b _ y y' h
    have e3 : y b = y' b := h b (mem_univ _) le_rfl
    unfold collisionPhiI
    by_cases hbI : b ∈ I
    · simp only [hbI, ↓reduceIte, e3]
    · have e1 : ∀ l ∈ I, y l = y' l := fun l hl => h l (mem_univ _)
        (mem_filter.mp (collision_I_sub_earlier p I hbI hl)).2.le
      have e2 : ∀ u ∈ coverRowEarlier univ ord' b, y u = y' u :=
        fun u hu => h u (mem_univ _) (mem_filter.mp hu).2.le
      simp only [hbI, ↓reduceIte]
      refine if_congr ?_ (by rw [e3]) rfl
      rw [e3]
      constructor
      · rintro ⟨h1, h2, h4⟩
        exact ⟨fun l hl => (e1 l hl) ▸ h1 l hl, fun u hu huI => (e2 u hu) ▸ h2 u hu huI, h4⟩
      · rintro ⟨h1, h2, h4⟩
        exact ⟨fun l hl => (e1 l hl).symm ▸ h1 l hl,
          fun u hu huI => (e2 u hu).symm ▸ h2 u hu huI, h4⟩
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord' b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          collisionPhiI ς p x I ψ b (Function.update x' b c) ≤
            collisionMIw G ς p I ψ x (Fintype.card F) n k b := by
    intro b _ x' hx'
    by_cases hbI : b ∈ I
    · have hupd : ∀ c, collisionPhiI ς p x I ψ b (Function.update x' b c) =
          if c = x (ψ b) then collisionW ς x b c else 0 := by
        intro c
        unfold collisionPhiI
        simp only [hbI, ↓reduceIte, Function.update_self]
      rw [sum_congr rfl fun c _ => hupd c]
      have hle : ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          (if c = x (ψ b) then collisionW ς x b c else 0) ≤ collisionW ς x b (x (ψ b)) := by
        rw [sum_ite_eq']
        split_ifs
        · exact le_rfl
        · exact collisionW_nonneg ς x b _
      unfold collisionMIw
      rw [ite_eq_left hbI]
      exact hle
    · have hu : ∀ c, ∀ u ∈ coverRowEarlier univ ord' b, Function.update x' b c u = x' u := by
        intro c u hu
        have hub : u ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp hu).2
        exact Function.update_of_ne hub _ _
      have hl : ∀ c, ∀ l ∈ I, Function.update x' b c l = x' l := by
        intro c l hlI
        have hlb : l ≠ b := by
          rintro rfl
          exact hbI hlI
        exact Function.update_of_ne hlb _ _
      have hupd : ∀ c, collisionPhiI ς p x I ψ b (Function.update x' b c) =
          if ((∀ l ∈ I, x' l = x (ψ l)) ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ∉ I →
            x' u ∉ X) ∧ c ∉ X then collisionW ς x b c else 0 := by
        intro c
        unfold collisionPhiI
        simp only [hbI, ↓reduceIte]
        refine if_congr ?_ (by rw [Function.update_self]) rfl
        rw [Function.update_self]
        constructor
        · rintro ⟨h1, h2, h4⟩
          exact ⟨⟨fun l hlI => (hl c l hlI) ▸ h1 l hlI,
            fun u huE huI => (hu c u huE) ▸ h2 u huE huI⟩, h4⟩
        · rintro ⟨⟨h1, h2⟩, h4⟩
          exact ⟨fun l hlI => (hl c l hlI).symm ▸ h1 l hlI,
            fun u huE huI => (hu c u huE).symm ▸ h2 u huE huI, h4⟩
      rw [sum_congr rfl fun c _ => hupd c]
      by_cases hcond : (∀ l ∈ I, x' l = x (ψ l)) ∧
          ∀ u ∈ coverRowEarlier univ ord' b, u ∉ I → x' u ∉ X
      · have hc' : ∀ c, (if ((∀ l ∈ I, x' l = x (ψ l)) ∧ ∀ u ∈ coverRowEarlier univ ord' b,
            u ∉ I → x' u ∉ X) ∧ c ∉ X then collisionW ς x b c else 0) =
              if c ∉ X then collisionW ς x b c else 0 := by
          intro c
          by_cases hcX : c ∈ X
          · rw [ite_eq_right (fun h => h.2 hcX), ite_eq_right (fun h => h hcX)]
          · rw [ite_eq_left ⟨hcond, hcX⟩, ite_eq_left hcX]
        rw [sum_congr rfl fun c _ => hc' c, ← sum_filter]
        have h := collision_oneStep_gen hW G ς hς x hx (coverRowEarlier univ ord' b) b x' hx' I ψ
          (fun u _ huI => hcond.1 u huI) hcond.2 (n' := 2 * (n : ℝ)) (by positivity)
        refine h.trans ?_
        unfold collisionMIw
        rw [ite_eq_right hbI]
        -- the number of distinct roots is at most `t^{(k)}_b`
        have ht0 : nbrCount G (coverRowEarlier univ ord' b) b ≤
            min (rowsDeg0 G b) (collisionB G p b + k) := by
          refine le_min (coverRow_nbrCount_le G _ b) ?_
          unfold nbrCount collisionB
          calc ((coverRowEarlier univ ord' b).filter
                fun u => (u, b) ∈ G.E ∨ (b, u) ∈ G.E).card
              ≤ (I ∪ (rowsAdj G b ∩ univ.filter fun u => p u < p b)).card := by
                refine card_le_card fun u hu => ?_
                have hu1 := (mem_filter.mp hu).1
                have hu2 := (mem_filter.mp hu).2
                rcases mem_union.mp (collision_earlierI_sub p I b hu1) with h | h
                · exact mem_union_left _ h
                · refine mem_union_right _ (mem_inter.mpr ⟨?_, h⟩)
                  simp only [rowsAdj, mem_filter, mem_univ, true_and]
                  exact hu2
            _ ≤ I.card + (rowsAdj G b ∩ univ.filter fun u => p u < p b).card := card_union_le _ _
            _ ≤ (rowsAdj G b ∩ univ.filter fun u => p u < p b).card + k := by omega
        have hroots : nbrCount G (coverRowEarlier univ ord' b) b + collisionR ς b -
            collisionMuI G ς p I ψ b ≤
              min (collisionR ς b + rowsDeg0 G b) (collisionR ς b + collisionB G p b + k) := by
          have := le_min_iff.mp ht0
          refine le_min ?_ ?_ <;> omega
        have hmono := coarseError_mono (q := (Fintype.card F : ℝ))
          (by positivity : (0 : ℝ) ≤ 2 * n) hroots
        have hpos : (0 : ℝ) ≤ Fintype.card F * (2 : ℝ)⁻¹ ^
            nbrCount G (coverRowEarlier univ ord' b) b * 2 ^ collisionMuI G ς p I ψ b := by
          positivity
        unfold collisionMuI at hmono hpos ⊢
        exact mul_le_mul_of_nonneg_left (by linarith) hpos
      · simp only [hcond, false_and, ↓reduceIte, sum_const_zero]
        exact collisionMIw_nonneg G ς p I ψ x hq0 n k b
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hfe : Feasible F G (univ \ univ) (fun _ => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have hseq := coverRow_seq_upper G hinj (collisionPhiI ς p x I ψ)
    (collisionMIw G ς p I ψ x (Fintype.card F) n k) 1
    (fun b y => collisionPhiI_nonneg ς p x I ψ b y)
    (fun b => collisionMIw_nonneg G ς p I ψ x hq0 n k b) zero_le_one hloc hstep hK
    (univ : Finset U).card univ rfl subset_rfl (fun _ _ b' _ hb' => absurd (mem_univ b') hb')
    (fun _ => (0 : F)) hfe
  rw [one_mul, Finset.sdiff_self, coverRowExtSum_empty] at hseq
  refine le_trans (sum_le_sum fun y _ => ?_) hseq
  split_ifs with h1
  · rw [collisionKernel_eq_prod]
    refine le_of_eq (prod_congr rfl fun v _ => ?_)
    unfold collisionPhiI
    by_cases hvI : v ∈ I
    · rw [ite_eq_left hvI, ite_eq_left (h1.1 v hvI)]
    · rw [ite_eq_right hvI, ite_eq_left ⟨h1.1, fun u _ huI => h1.2 u huI, h1.2 v hvI⟩]
  · exact prod_nonneg fun v _ => collisionPhiI_nonneg ς p x I ψ v y

/-- **One stratum `(I, ψ)`, normalized, with incident weights**: with `k = |I|` and the order
`π_k`, the stratum sum of `K_coll(x, ·)` is at most
`L_int⁻¹ Υ_k q^{-k} 2^{e(I)} ∏_{l ∈ I} α_{l, ψ(l)}(x) · |𝓘⁺|`. -/
theorem collision_stratumI_ratio_incident (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (I : Finset U) (ψ : U → U) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      (collisionLint G (Fintype.card F) n)⁻¹ * collisionUpsK G ς π (Fintype.card F) n I.card *
        ((Fintype.card F : ℝ)⁻¹ ^ I.card * (2 : ℝ) ^ collisionEdgesIn G I *
          ∏ l ∈ I, collisionAlpha G ς x l (ψ l)) * (injLabellings F G).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set k := I.card with hk
  set p := π k with hp
  set o := collisionOrdI p I with ho
  set t' : U → ℕ := fun v => nbrCount G (coverRowEarlier univ o v) v with ht'
  set eK : U → ℝ := fun v => coarseError (collisionTk G ς π k v) q (2 * n) with heK
  have het : ∀ v, coarseError (t' v) q n ≤ coarseError (rowsDeg0 G v) q n :=
    fun v => coarseError_mono hn0 (coverRow_nbrCount_le G _ v)
  have het1 : ∀ v, 0 < 1 - coarseError (t' v) q n := fun v => by linarith [het v, hS1 v]
  have heK0 : ∀ v, 0 ≤ eK v := fun v => coarseError_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) _
  have hstr := collision_stratumI_le_incident hW G ς hς p (hπ k) x hx n I ψ (le_refl k)
  have hlow := collision_card_lower_gen hW G o (collisionOrdI_injOn p (hπ k) I univ) hn hS1
  set ℓf : U → ℝ := fun v => q / 2 ^ t' v * (1 - coarseError (t' v) q n) with hℓf
  set num : U → ℝ := fun v => if v ∈ I then
      collisionW ς x v (x (ψ v)) * 2 ^ t' v * q⁻¹
    else 2 ^ collisionMuI G ς p I ψ v * (1 + eK v) with hnum
  -- `M_v = (num_v / (1 - e_{t'_v})) ℓ_v`
  have hM : ∀ v, collisionMIw G ς p I ψ x q n k v = num v / (1 - coarseError (t' v) q n) * ℓf v := by
    intro v
    have h1 := (het1 v).ne'
    unfold collisionMIw
    by_cases hv : v ∈ I
    · rw [ite_eq_left hv]
      simp only [hnum, hℓf, hv, ↓reduceIte]
      field_simp
    · rw [ite_eq_right hv]
      simp only [hnum, hℓf, hv, ↓reduceIte, heK, collisionTk, inv_pow]
      field_simp
      simp only [ht', hp, ho]
      ring
  have hprodM : ∏ v, collisionMIw G ς p I ψ x q n k v =
      (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := by
    rw [prod_congr rfl fun v _ => hM v, prod_mul_distrib, prod_div_distrib]
  have hLle : collisionLint G q n ≤ ∏ v, (1 - coarseError (t' v) q n) :=
    prod_le_prod₀ (fun v _ => by linarith [hS1 v]) (fun v _ => by linarith [het v])
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hfilt : univ.filter (fun v => v ∈ I) = I := by
    ext v
    simp
  -- the numerator
  have hnum_le : ∏ v, num v ≤ collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I * ∏ l ∈ I, collisionAlpha G ς x l (ψ l)) := by
    have hsplit : ∏ v, num v = (∏ v ∈ I, (collisionW ς x v (x (ψ v)) *
        2 ^ t' v * q⁻¹)) * ∏ v ∈ univ.filter (fun v => v ∉ I),
          (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) := by
      simp only [hnum]
      rw [prod_ite, hfilt]
    have hI : ∏ v ∈ I, (collisionW ς x v (x (ψ v)) * 2 ^ t' v * q⁻¹) =
        (∏ l ∈ I, collisionW ς x l (x (ψ l))) *
          (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, ← prod_pow_eq_pow_sum]
    have hJ : ∏ v ∈ univ.filter (fun v => v ∉ I), (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) =
        (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
          ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    -- the pieces
    have hP1 : (2 : ℝ) ^ (∑ v ∈ I, t' v) ≤ (2 : ℝ) ^ collisionEdgesIn G I :=
      pow_le_pow_right₀ (by norm_num) (collision_sum_t_le_edges G p I)
    have hP2 : (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) ≤
        ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [prod_pow_eq_pow_sum]
      exact pow_le_pow_right₀ (by norm_num) (collision_sum_muI_le G ς p I ψ)
    have hP3 : ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) ≤ collisionUpsK G ς π q n k := by
      unfold collisionUpsK
      rw [← prod_filter_mul_prod_filter_not univ (fun v => v ∈ I)]
      refine le_mul_of_one_le_left (prod_nonneg fun v _ => by linarith [heK0 v]) ?_
      exact one_le_prod₀ fun v _ => by linarith [heK0 v]
    have hP4 : ∏ l ∈ I, collisionAlpha G ς x l (ψ l) =
        (∏ l ∈ I, collisionW ς x l (x (ψ l))) *
          ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [← prod_mul_distrib]
      rfl
    have hA0 : 0 ≤ ∏ l ∈ I, collisionW ς x l (x (ψ l)) :=
      prod_nonneg fun l _ => collisionW_nonneg ς x l _
    have hU0 : 0 ≤ ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hq0' : 0 ≤ q⁻¹ ^ k := by positivity
    calc ∏ v, num v
        = ((∏ l ∈ I, collisionW ς x l (x (ψ l))) *
            (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k) *
          ((2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
            ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v)) := by
          rw [hsplit, hI, hJ]
      _ ≤ ((∏ l ∈ I, collisionW ς x l (x (ψ l))) *
            (2 : ℝ) ^ collisionEdgesIn G I * q⁻¹ ^ k) *
          ((∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l) * collisionUpsK G ς π q n k) := by
          refine mul_le_mul ?_ ?_ (mul_nonneg (by positivity) hU0)
            (mul_nonneg (mul_nonneg hA0 (by positivity)) hq0')
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hA0) hq0'
          · exact mul_le_mul hP2 hP3 hU0 (by positivity)
      _ = _ := by rw [hP4]; ring
  have hnum0 : 0 ≤ ∏ v, num v := prod_nonneg fun v _ => by
    by_cases hv : v ∈ I
    · simp only [hnum, hv, ↓reduceIte]
      exact mul_nonneg (mul_nonneg (collisionW_nonneg ς x v _) (by positivity)) (by positivity)
    · simp only [hnum, hv, ↓reduceIte]
      exact mul_nonneg (by positivity) (by linarith [heK0 v])
  have hQpos : 0 < ∏ v, (1 - coarseError (t' v) q n) := prod_pos fun v _ => het1 v
  have hℓ0 : 0 ≤ ∏ v, ℓf v := prod_nonneg fun v _ => mul_nonneg (by positivity) (het1 v).le
  have hC0 : 0 ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I * ∏ l ∈ I, collisionAlpha G ς x l (ψ l)) := by
    have hU : 0 ≤ collisionUpsK G ς π q n k :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hA : 0 ≤ ∏ l ∈ I, collisionAlpha G ς x l (ψ l) :=
      prod_nonneg fun l _ => mul_nonneg (collisionW_nonneg ς x l _) (by positivity)
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hU)
      (mul_nonneg (by positivity) hA)
  calc _ ≤ ∏ v, collisionMIw G ς p I ψ x q n k v := hstr
    _ = (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := hprodM
    _ ≤ (∏ v, num v) / collisionLint G q n * ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        exact div_le_div_of_nonneg_left hnum0 hLpos hLle
    _ ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
          (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I * ∏ l ∈ I, collisionAlpha G ς x l (ψ l)) *
          ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        rw [div_eq_inv_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left hnum_le (inv_nonneg.mpr hLpos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hC0


/-- The multiple-collision row bound with incident weights,
`L_int⁻¹ ∑_{k=2}^{|U⁺|} Υ_k ∑_{|I| = k} 2^{e(I)} ∏_{i ∈ I} ρ_i(x)`. -/
noncomputable def collisionIncident2 (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ)
    (q : ℝ) (n : ℕ) (x : U → F) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U), collisionUpsK G ς π q n k *
    ∑ I ∈ (univ : Finset U).powersetCard k,
      (2 : ℝ) ^ collisionEdgesIn G I * ∏ i ∈ I, collisionRho G ς q x i

omit [Field F] [Fintype F] in
/-- `∑_{ψ : I → U⁺} ∏_{l ∈ I} α_{l, ψ(l)}(x) = ∏_{l ∈ I} ∑_j α_{lj}(x)`. -/
theorem collision_sum_maps_alpha [Field F] [Fintype F] (G : OrientedGraph U) (ς : U → U → ℤ)
    (x : U → F) (I : Finset U) :
    ∑ ψ : (I → U), ∏ l ∈ I, collisionAlpha G ς x l (collisionExt I ψ l) =
      ∏ l ∈ I, ∑ j, collisionAlpha G ς x l j := by
  rw [← prod_coe_sort I (fun l => ∑ j, collisionAlpha G ς x l j), Fintype.prod_sum]
  refine sum_congr rfl fun ψ _ => ?_
  rw [← prod_coe_sort I]
  refine prod_congr rfl fun l _ => ?_
  rw [collisionExt_coe]

theorem collision_prod_rho (G : OrientedGraph U) (ς : U → U → ℤ) {q : ℝ} (hq : 0 < q)
    (x : U → F) (I : Finset U) :
    q⁻¹ ^ I.card * ∏ l ∈ I, ∑ j, collisionAlpha G ς x l j = ∏ l ∈ I, collisionRho G ς q x l := by
  unfold collisionRho
  rw [coverRow_r_sq hq, prod_mul_distrib, prod_const]

/-- **`cor:incident-weights`, multiple collisions**: the row sum of `T_coll,≥2` at `x ∈ 𝓘⁺` is
at most `L_int⁻¹ ∑_{k=2}^{|U⁺|} Υ_k ∑_{|I| = k} 2^{e(I)} ∏_{i ∈ I} ρ_i(x)` (hard cross factors,
the orders of `lem:oct24-collision`(b)). -/
theorem collision_rowSum2_incident_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) :
    (graphLaw G hne).expect (collisionKernel2 ς x) ≤
      collisionIncident2 G ς π (Fintype.card F) n x := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : (0 : ℝ) < q := by
    rw [hq]
    exact_mod_cast Fintype.card_pos
  set N : ℝ := ((injLabellings F G).card : ℝ) with hNdef
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast card_pos.mpr hne
  rw [div_le_iff₀ hN]
  set c : ℕ → Finset U → ℝ := fun k I => (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * (2 : ℝ) ^ collisionEdgesIn G I) with hc
  have hstr : ∀ k ∈ Icc 2 (Fintype.card U), ∀ I ∈ (univ : Finset U).powersetCard k,
      ∀ ψ : (I → U), ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
        c k I * (∏ l ∈ I, collisionAlpha G ς x l (collisionExt I ψ l)) * N := by
    intro k _ I hI ψ
    have hIk : I.card = k := (mem_powersetCard.mp hI).2
    have h := collision_stratumI_ratio_incident hW G ς hς π hπ x hx hn hS1 I (collisionExt I ψ)
    rw [hIk] at h
    refine h.trans (le_of_eq ?_)
    simp only [hc]
    ring
  calc ∑ y ∈ injLabellings F G, collisionKernel2 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ k ∈ Icc 2 (Fintype.card U),
          ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel2_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          ∑ y ∈ injLabellings F G,
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        rw [sum_comm]
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          c k I * (∏ l ∈ I, collisionAlpha G ς x l (collisionExt I ψ l)) * N :=
        sum_le_sum fun k hk => sum_le_sum fun I hI => sum_le_sum fun ψ _ => hstr k hk I hI ψ
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k,
          (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k * (2 : ℝ) ^ collisionEdgesIn G I *
            (∏ i ∈ I, collisionRho G ς q x i) * N := by
        refine sum_congr rfl fun k _ => sum_congr rfl fun I hI => ?_
        have hIk : I.card = k := (mem_powersetCard.mp hI).2
        rw [← sum_mul, ← mul_sum, collision_sum_maps_alpha, ← collision_prod_rho G ς hq0 x I, hIk]
        simp only [hc]
        ring
    _ = collisionIncident2 G ς π q n x * N := by
        unfold collisionIncident2
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum, mul_sum, sum_mul]
        refine sum_congr rfl fun I _ => ?_
        ring

/-- **`cor:incident-weights`, operator bounds** (symmetric kernel): if `Λ` bounds the
single-collision row bound `collisionIncident1` at every `x ∈ 𝓘⁺` (e.g. its supremum), then
`‖T_coll,1‖ ≤ Λ` on `L²(μ)` (matrix normalization of `collision_opBound`). -/
theorem collision_opBound_incident (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ') {Λ : ℝ}
    (hΛ : ∀ x ∈ injLabellings F G, collisionIncident1 G ς ord (Fintype.card F) n x ≤ Λ) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel1 ς x x' / (injLabellings F G).card) Λ := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel1 ς x x' / (injLabellings F G).card ≤ Λ := by
    intro x hx
    have hxinj : Function.Injective x := fun a b h => by
      simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
      exact hx.1 a (mem_univ _) b (mem_univ _) h
    have h := collision_rowSum_incident_le hW G ς hς hne hn hS1 ord hord x hxinj
    rw [coverRow_expect_graphLaw] at h
    rw [← sum_div]
    exact h.trans (hΛ x hx)
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel1 ς x x' / (injLabellings F G).card ≤ Λ := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel1 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel1 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [collisionKernel1_symm ς hanti]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ Λ :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel1_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel1_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

/-- **`cor:incident-weights`, operator bounds** (symmetric kernel): if `Λ` bounds
`collisionIncident2` at every `x ∈ 𝓘⁺`, then `‖T_coll,≥2‖ ≤ Λ`. -/
theorem collision_opBound2_incident (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) {Λ : ℝ}
    (hΛ : ∀ x ∈ injLabellings F G, collisionIncident2 G ς π (Fintype.card F) n x ≤ Λ) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel2 ς x x' / (injLabellings F G).card) Λ := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hsymm : ∀ x x' : U → F, collisionKernel2 ς x x' = collisionKernel2 ς x' x := by
    intro x x'
    unfold collisionKernel2
    rw [collisionCommon_symm, collisionKernel_symm ς hanti]
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤ Λ := by
    intro x hx
    have hxinj : Function.Injective x := fun a b h => by
      simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
      exact hx.1 a (mem_univ _) b (mem_univ _) h
    have h := collision_rowSum2_incident_le hW G ς hς hne hn hS1 π hπ x hxinj
    rw [coverRow_expect_graphLaw] at h
    rw [← sum_div]
    exact h.trans (hΛ x hx)
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤ Λ := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel2 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel2 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [hsymm]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ Λ :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel2_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel2_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

end Incident

end Sarkozy.Extraction

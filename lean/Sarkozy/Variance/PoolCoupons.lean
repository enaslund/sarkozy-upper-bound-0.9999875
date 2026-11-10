module

public import Sarkozy.Certificates.DistinctChoice

/-!
# Terms pooled over the pieces from `2^31` (`lem:pool-coupons`)

`paper/sections/22_variance.tex`, Section 22.6, `lem:pool-coupons`, and the products of the
paragraph "Piece data" before `lem:distinct-choice`.

* `prod_union_le_pool`: **the first assertion** (the four products over `X ∪ Z` and the cap):
  for a set `X` of pattern `m` and a set `Z` of `k` pool blocks disjoint from it, a product over
  `X ∪ Z` of nonnegative block data bounded by the piece data on `X` and by the pool data on `Z`
  is at most `∏_{𝔅∈X} g_{i(𝔅)} · g_𝒫^k`. With `f = 1 + h_𝔅, M_𝔅, 1 + χ_𝔅, 1 + ε_𝔅, q_𝔅^{2a}`
  these are the products of `1 + h_{m+𝒫^k}`, `M_{m+𝒫^k}`, `1 + χ_{m+𝒫^k}`, `1 + η_{m+𝒫^k}` and
  `C_m C_𝒫^k`. With `Z = ∅` it is the piece-data bound for a set of pattern `m`.
* `esym_le_pow_mul`: `0 ≤ u ≤ ρ v` on `S` gives `e_k(u) ≤ ρ^k e_k(v)` (the pointwise step of (b)).
* `pool_coupons_mean_first`, `pool_coupons_mean_second`: **(b)**, both bounds:
  `∑_Z ∏_{𝔅∈Z} d_{i(𝔅)} b_𝔅^{-1} ≥ 𝔴_k(d^𝒫; ∅)` and
  `∑_Z [∏ d'_{i(𝔅)} b_𝔅^{-1} - ∏ d_{i(𝔅)} b_𝔅^{-1}] ≥ (1 - ρ^k) 𝔴_k(d'^𝒫; ∅)` for
  `0 ≤ d_i ≤ ρ d'_i`, `ρ ∈ [0, 1]`, where `𝔴_k(c; ∅) = (1/k!) ∏_{j<k} [𝔪(c) - j 𝔲(c)]_+` is
  `fallingPos (∑ c_i Σ_i) 𝔲 k / k!` and the sums over `Z` are the elementary symmetric sums
  `esym` of `Certificates/DistinctChoice.lean` (`lem:distinct-choice`(b), whose
  `distinct_choice_mixed` is used with `X = ∅`).

The use of these bounds in the mean coupons `m^pool_F`, `m^pool_Q` (`prop:record:mean-credit`,
`lem:record:companion-energy`) and the variance term `P_E(m)` of (a) belong to the assembly and
are not formalized here.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.DistinctChoice

namespace Sarkozy.Variance

section Products

variable {β : Type*} [DecidableEq β]

/-- **`lem:pool-coupons`, the first assertion**: for disjoint `X` and `Z`, nonnegative block data
`f` with `f ≤ g` on `X` (piece data) and `f ≤ g_𝒫` on `Z` (pool data),
`∏_{X ∪ Z} f ≤ (∏_X g) g_𝒫^{|Z|}`. -/
theorem prod_union_le_pool (X Z : Finset β) (hdisj : Disjoint X Z) (f g : β → ℝ) (gP : ℝ)
    (hf : ∀ B ∈ X ∪ Z, 0 ≤ f B) (hX : ∀ B ∈ X, f B ≤ g B) (hZ : ∀ B ∈ Z, f B ≤ gP) :
    ∏ B ∈ X ∪ Z, f B ≤ (∏ B ∈ X, g B) * gP ^ Z.card := by
  rw [prod_union hdisj]
  apply mul_le_mul
  · exact prod_le_prod₀ (fun B hB => hf B (mem_union_left Z hB)) hX
  · calc ∏ B ∈ Z, f B ≤ ∏ _B ∈ Z, gP := prod_le_prod₀ (fun B hB => hf B (mem_union_right X hB)) hZ
      _ = gP ^ Z.card := prod_const gP
  · exact prod_nonneg fun B hB => hf B (mem_union_right X hB)
  · exact prod_nonneg fun B hB => (hf B (mem_union_left Z hB)).trans (hX B hB)

end Products

section Mean

variable {β : Type*} [DecidableEq β]

omit [DecidableEq β] in
/-- The pointwise step of `lem:pool-coupons`(b): `0 ≤ u ≤ ρ v` on `S` gives
`e_k(u) ≤ ρ^k e_k(v)`. -/
theorem esym_le_pow_mul (S : Finset β) (u v : β → ℝ) {ρ : ℝ}
    (hu : ∀ B ∈ S, 0 ≤ u B) (huv : ∀ B ∈ S, u B ≤ ρ * v B) (k : ℕ) :
    esym S u k ≤ ρ ^ k * esym S v k := by
  unfold esym
  rw [mul_sum]
  apply sum_le_sum
  intro Z hZ
  obtain ⟨hZS, hZc⟩ := mem_powersetCard.mp hZ
  calc ∏ B ∈ Z, u B ≤ ∏ B ∈ Z, (ρ * v B) :=
        prod_le_prod₀ (fun B hB => hu B (hZS hB)) (fun B hB => huv B (hZS hB))
    _ = ρ ^ k * ∏ B ∈ Z, v B := by rw [prod_mul_distrib, prod_const, hZc]

omit [DecidableEq β] in
/-- The difference form of the pointwise step: `e_k(v) - e_k(u) ≥ (1 - ρ^k) e_k(v)`. -/
theorem esym_sub_ge (S : Finset β) (u v : β → ℝ) {ρ : ℝ}
    (hu : ∀ B ∈ S, 0 ≤ u B) (huv : ∀ B ∈ S, u B ≤ ρ * v B) (k : ℕ) :
    (1 - ρ ^ k) * esym S v k ≤ esym S v k - esym S u k := by
  have := esym_le_pow_mul S u v hu huv k
  linarith

/-- **`lem:pool-coupons`(b), the first bound**: for nonnegative coefficients `d` on the pool
`𝒫`, the `k`-sets `Z` of distinct pool blocks satisfy
`∑_Z ∏_{𝔅∈Z} d_{i(𝔅)} b_𝔅^{-1} ≥ 𝔴_k(d^𝒫; ∅) = fallingPos (∑_i d_i Σ_i) 𝔲(d) k / k!`
(`lem:distinct-choice`(b) with `m = ∅`). -/
theorem pool_coupons_mean_first {I : Type*} [DecidableEq I] (piece : β → I) (Ps : Finset I)
    (blocks : Finset β) (w : β → ℝ) (d Sig Xi : I → ℝ) (u : ℝ) (hd : ∀ i ∈ Ps, 0 ≤ d i)
    (hw : ∀ B ∈ blocks, 0 ≤ w B ∧ w B ≤ 1 / Xi (piece B))
    (hSig : ∀ i ∈ Ps, Sig i ≤ ∑ B ∈ blocks.filter (fun B => piece B = i), w B)
    (hu : ∀ i ∈ Ps, d i / Xi i ≤ u) (k : ℕ) :
    fallingPos (∑ i ∈ Ps, d i * Sig i) u k / k.factorial ≤
      esym (blocks.filter (fun B => piece B ∈ Ps)) (fun B => d (piece B) * w B) k := by
  have h := distinct_choice_mixed piece Ps blocks ∅ w d Sig Xi u hd hw hSig hu k
  simpa using h

/-- **`lem:pool-coupons`(b), the second bound**: for coefficient vectors with
`0 ≤ d_i ≤ ρ d'_i` and `d'_i ≥ 0` on the pool, `ρ ∈ [0, 1]`,
`∑_Z [∏_{𝔅∈Z} d'_{i(𝔅)} b_𝔅^{-1} - ∏_{𝔅∈Z} d_{i(𝔅)} b_𝔅^{-1}] ≥ (1 - ρ^k) 𝔴_k(d'^𝒫; ∅)`. -/
theorem pool_coupons_mean_second {I : Type*} [DecidableEq I] (piece : β → I) (Ps : Finset I)
    (blocks : Finset β) (w : β → ℝ) (d d' Sig Xi : I → ℝ) (u ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1)
    (hd : ∀ i ∈ Ps, 0 ≤ d i ∧ d i ≤ ρ * d' i) (hd' : ∀ i ∈ Ps, 0 ≤ d' i)
    (hw : ∀ B ∈ blocks, 0 ≤ w B ∧ w B ≤ 1 / Xi (piece B))
    (hSig : ∀ i ∈ Ps, Sig i ≤ ∑ B ∈ blocks.filter (fun B => piece B = i), w B)
    (hu : ∀ i ∈ Ps, d' i / Xi i ≤ u) (k : ℕ) :
    (1 - ρ ^ k) * (fallingPos (∑ i ∈ Ps, d' i * Sig i) u k / k.factorial) ≤
      esym (blocks.filter (fun B => piece B ∈ Ps)) (fun B => d' (piece B) * w B) k -
        esym (blocks.filter (fun B => piece B ∈ Ps)) (fun B => d (piece B) * w B) k := by
  set S := blocks.filter (fun B => piece B ∈ Ps)
  have hlow := pool_coupons_mean_first piece Ps blocks w d' Sig Xi u hd' hw hSig hu k
  have hpt : ∀ B ∈ S, (0 ≤ d (piece B) * w B) ∧ d (piece B) * w B ≤ ρ * (d' (piece B) * w B) := by
    intro B hB
    have hP := (mem_filter.mp hB).2
    have hB' := (mem_filter.mp hB).1
    obtain ⟨h0, h1⟩ := hd (piece B) hP
    have hw0 := (hw B hB').1
    exact ⟨mul_nonneg h0 hw0, by nlinarith⟩
  have hdiff := esym_sub_ge S (fun B => d (piece B) * w B) (fun B => d' (piece B) * w B)
    (fun B hB => (hpt B hB).1) (fun B hB => (hpt B hB).2) k
  have hρk : 0 ≤ 1 - ρ ^ k := by
    have := pow_le_one₀ hρ0 hρ1 (n := k)
    linarith
  calc (1 - ρ ^ k) * (fallingPos (∑ i ∈ Ps, d' i * Sig i) u k / k.factorial)
      ≤ (1 - ρ ^ k) * esym S (fun B => d' (piece B) * w B) k :=
        mul_le_mul_of_nonneg_left hlow hρk
    _ ≤ _ := hdiff

end Mean

end Sarkozy.Variance

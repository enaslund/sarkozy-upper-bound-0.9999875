module

public import Sarkozy.Extraction.CoverRows
public import Sarkozy.Influence.OpBound

@[expose] public section

/-!
# Pinned coincidences (`prop:pinned-collision`)

`paper/sections/16_extraction.tex`, `subsec:push:pinnedremainder` (the *Setting* paragraph) and
`prop:pinned-collision`.

## Setting

A finite field `F` with `q` elements (`F = 𝔽_p` in the paper; `WeilBound F` is Weil's theorem,
`thm:weil`(a), the literature input of `lem:extension`), `r = q^{-1/2}`, `n` coordinates
`Fin n`, a set `𝓜 ⊆ F` of `z = |𝓜|` fixed labels, and pins: `pin j β ∈ {0, ±1}`, a pin of `j`
being `(β, ε)` with `ε = pin j β ≠ 0` and `β ∈ 𝓜` (so the roots of the pins of `j` are distinct,
`pinRoots`); `ϖ_j = pinCount pin j ≤ ϖ`. `𝓘_pin = pinLab M pin` is the set of injective
`x : Fin n → F` with every `x_j` in the allowed set of `j` (`pinAllowed`: `t ∉ 𝓜` and
`ε(t - β)` a nonzero square for every pin `(β, ε)` of `j`; `mem_pinLab_iff` is the paper's
description), and `μ` is the uniform law on it. The cross pairs carry signs
`ς : Fin n → Fin n → ℤ` in `{0, ±1}` (`E_× = {ς ≠ 0}`, no symmetry), `N_X(i) = pinNX ς i`,
`N_Y(j) = pinNY ς j`. `e^pin_d = ePin q n z d = 2^d ((2n + z) r² + (d/2) r)`; `pinU`, `pinUps`,
`pinD` are `U`, `Υ`, `D` of the proposition for a family of neighbourhoods (`N_Y` or `N_X`).

## Results

* `pinned_collision_opBound` — **`prop:pinned-collision`**: under `e^pin_ϖ < 1`, the matrix
  `K(x, y)/|𝓘_pin|` (`pinKer`, the kernel
  `1{x([n]) ∩ y([n]) ≠ ∅} ∏_{(i,j) ∈ E_×} (1 + χ(ς_{ij}(y_j - x_i)))`) has `ℓ²(𝓘_pin)` operator
  norm at most `(D_X D_Y)^{1/2}`, which is `‖T^pin_coll‖_{L²(μ)} ≤ (D_X D_Y)^{1/2}` (same
  normalization as `collision_opBound`); `pinned_collision_sqrt_le_max` gives
  `(D_X D_Y)^{1/2} ≤ max(D_X, D_Y)`.
* `pinned_collision_D_eq` (with `pinD_eq_of_card`, `pin_inner_sum`): `D_X = D_Y` when the
  multisets of the row and column degrees coincide (a permutation `π` with
  `|N_X(π j)| = |N_Y(j)|`).
* `pin_rowSum_le`: every row sum is at most `D_Y` (`∑_y K(x, y) ≤ D_Y |𝓘_pin|`); the column sums
  are row sums of the transposed signs (`pinKer_swap`, `pinNY_swap`), bounded by `D_X`.
* `card_pinLab_ge`: `|𝓘_pin| ≥ ∏_j q 2^{-ϖ_j} (1 - e^pin_ϖ)` (`lem:extension`(c) along the
  coordinates, at most `n + z` excluded labels; `sum_pinPart_insert`).

## Proof

As in the paper. For fixed `x`, `ω_j = a_j + b_j` with `b_j` the part at the coincident values
`t ∈ x([n])`, and `K(x, y) = ∑_{∅ ≠ I} ∏_{j ∈ I} b_j(y_j) ∏_{j ∉ I} a_j(y_j)` (`pinKer_expand`,
`I` the coincident `y`-vertices; the paper's maps `φ : I → [n]` are the sums over `t ∈ x([n])`).
Each stratum is bounded by dropping injectivity (a sum over the product of the allowed sets,
`Finset.prod_univ_sum`) and by the one-coordinate bounds: the free values by
`lem:extraction-merged-count` with the pins as the conditions and no merged roots
(`pin_free_sum_le`; the cross roots `x_i` avoid `𝓜`), `≤ q 2^{-ϖ_j}(1 + e^pin_{ϖ+|N_Y(j)|})`
(`coarseError_le_ePin`, `ePin_mono`), and the coincident values by
`∑_i 2^{|N_Y(j)| - [i ∈ N_Y(j)]}` (`pin_coinc_sum_le`). Summing over `I` and dividing by the lower
count gives `D_Y` (`pin_algebra`: `∏(1 + e_j + u_j) - ∏(1 + e_j) ≤ Υ (e^{∑ u_j} - 1)`).
Schur's test (`Sarkozy.Influence.opBound_schur`) gives the norm.

## Deviations from the paper

* A general finite field `F` with `WeilBound F` in place of `𝔽_p`; `n ≥ 2` is not needed.
* The upper bounds do not use the order of the coordinates (injectivity is dropped, every
  coordinate excludes `𝓜 ∪ x([n])`); the lower count labels the coordinates in any order.
* Not formalized: the last sentence of the proposition (`D_X/r²`, `D_Y/r²`, `N^pin/r²` are
  admissible in the sense of `lem:majorant`).
-/

open scoped BigOperators
open Finset

namespace Sarkozy.ExtractionK

open Sarkozy.Labellings Sarkozy.Extraction

/-! ## The setting of `subsec:push:pinnedremainder` -/

section PinDefs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The roots of the pins of coordinate `j`: a pin is `(β, ε)` with `ε = pin j β ≠ 0`. -/
def pinRoots {n : ℕ} (pin : Fin n → F → ℤ) (j : Fin n) : Finset F :=
  univ.filter fun β => pin j β ≠ 0

/-- `ϖ_j`, the number of pins of coordinate `j`. -/
def pinCount {n : ℕ} (pin : Fin n → F → ℤ) (j : Fin n) : ℕ := (pinRoots pin j).card

/-- The allowed set of coordinate `j`: the `t ∉ 𝓜` with `ε(t - β)` a nonzero square for every
pin `(β, ε)` of `j`. -/
def pinAllowed {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ) (j : Fin n) : Finset F :=
  univ.filter fun t => t ∉ M ∧ ∀ β, pin j β ≠ 0 → quadraticChar F ((pin j β : F) * (t - β)) = 1

/-- `𝓘_pin`: the injective `x` with every `x_j` in the allowed set of `j`. -/
def pinLab {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ) : Finset (Fin n → F) :=
  univ.filter fun x => (∀ a b, x a = x b → a = b) ∧ ∀ j, x j ∈ pinAllowed M pin j

/-- The pinned labellings of a set `S` of coordinates (extended by `0`). -/
def pinPart {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ) (S : Finset (Fin n)) :
    Finset (Fin n → F) :=
  univ.filter fun y => (∀ j, j ∉ S → y j = 0) ∧ (∀ a ∈ S, ∀ b ∈ S, y a = y b → a = b) ∧
    ∀ j ∈ S, y j ∈ pinAllowed M pin j

/-- `N_Y(j) = {i : (i, j) ∈ E_×}`. -/
def pinNY {n : ℕ} (ς : Fin n → Fin n → ℤ) (j : Fin n) : Finset (Fin n) :=
  univ.filter fun i => ς i j ≠ 0

/-- `N_X(i) = {j : (i, j) ∈ E_×}`. -/
def pinNX {n : ℕ} (ς : Fin n → Fin n → ℤ) (i : Fin n) : Finset (Fin n) :=
  univ.filter fun j => ς i j ≠ 0

/-- The cross factors at the `y`-vertex `j` with label `t`:
`ω_j(t) = ∏_{i ∈ N_Y(j)} (1 + χ(ς_{ij}(t - x_i)))`. -/
noncomputable def pinOmega {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F) (j : Fin n) (t : F) :
    ℝ :=
  ∏ i ∈ pinNY ς j, (1 + (quadraticChar F ((ς i j : F) * (t - x i)) : ℝ))

/-- The kernel of `T^pin_coll`: `1{x([n]) ∩ y([n]) ≠ ∅} ∏_{(i,j) ∈ E_×} (1 + χ_{ij}(x, y))`. -/
noncomputable def pinKer {n : ℕ} (ς : Fin n → Fin n → ℤ) (x y : Fin n → F) : ℝ :=
  (if ∃ i j, x i = y j then (1 : ℝ) else 0) * ∏ j, pinOmega ς x j (y j)

/-- `e^pin_d = 2^d ((2n + z) r² + (d/2) r)`, `r = q^{-1/2}`. -/
noncomputable def ePin (q : ℝ) (n z d : ℕ) : ℝ :=
  2 ^ d * ((2 * n + z) * (Real.sqrt q)⁻¹ ^ 2 + d / 2 * (Real.sqrt q)⁻¹)

/-- `U_Y = r² ∑_{j,i} 2^{ϖ + |N(j)| - [i ∈ N(j)]}` for a family `N` of neighbourhoods. -/
noncomputable def pinU {n : ℕ} (q : ℝ) (ϖ : ℕ) (N : Fin n → Finset (Fin n)) : ℝ :=
  (Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i, (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0))

/-- `Υ_Y = ∏_j (1 + e^pin_{ϖ + |N(j)|})`. -/
noncomputable def pinUps {n : ℕ} (q : ℝ) (z ϖ : ℕ) (N : Fin n → Finset (Fin n)) : ℝ :=
  ∏ j, (1 + ePin q n z (ϖ + (N j).card))

/-- `D_Y = Υ_Y (1 - e^pin_ϖ)^{-n} (e^{U_Y} - 1)`. -/
noncomputable def pinD {n : ℕ} (q : ℝ) (z ϖ : ℕ) (N : Fin n → Finset (Fin n)) : ℝ :=
  pinUps q z ϖ N / (1 - ePin q n z ϖ) ^ n * (Real.exp (pinU q ϖ N) - 1)

end PinDefs

/-! ## Elementary facts -/

section PinFacts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [Fintype F] [DecidableEq F] in
theorem pin_char_cast_ne_zero {e : ℤ} (he : e = 1 ∨ e = -1) : (e : F) ≠ 0 := by
  rcases he with rfl | rfl <;> simp

theorem pin_char_pm {e : ℤ} (he : e = 1 ∨ e = -1) :
    quadraticChar F (e : F) = 1 ∨ quadraticChar F (e : F) = -1 :=
  quadraticChar_dichotomy (pin_char_cast_ne_zero he)

/-- `χ(ε a) = 1 ↔ χ(a) = χ(ε)` for `ε = ±1`. -/
theorem pin_cond_iff {e : ℤ} (he : e = 1 ∨ e = -1) (a : F) :
    quadraticChar F ((e : F) * a) = 1 ↔ quadraticChar F a = quadraticChar F (e : F) := by
  rw [map_mul]
  rcases pin_char_pm (F := F) he with h | h <;> rw [h] <;> omega

theorem pin_one_add_chi (a : F) :
    0 ≤ 1 + (quadraticChar F a : ℝ) ∧ 1 + (quadraticChar F a : ℝ) ≤ 2 := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> norm_num

theorem pinOmega_nonneg {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F) (j : Fin n) (t : F) :
    0 ≤ pinOmega ς x j t :=
  prod_nonneg fun _ _ => (pin_one_add_chi _).1

theorem pinKer_nonneg {n : ℕ} (ς : Fin n → Fin n → ℤ) (x y : Fin n → F) : 0 ≤ pinKer ς x y :=
  mul_nonneg (by split_ifs <;> norm_num) (prod_nonneg fun j _ => pinOmega_nonneg ς x j _)

/-- `e_d(q, 2n + z) ≤ e^pin_d` (`h_d ≤ d/2`). -/
theorem coarseError_le_ePin (q : ℝ) (n z d : ℕ) :
    coarseError d q (2 * n + z) ≤ ePin q n z d := by
  unfold coarseError ePin coarseH
  have hr : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have h1 : (2 : ℝ)⁻¹ ^ d ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have h2 : ((d : ℝ) / 2 - 1 + (2 : ℝ)⁻¹ ^ d) * (Real.sqrt q)⁻¹ ≤ (d : ℝ) / 2 * (Real.sqrt q)⁻¹ :=
    mul_le_mul_of_nonneg_right (by linarith) hr
  have h3 : (0 : ℝ) ≤ 2 ^ d := by positivity
  nlinarith [h2, h3]

theorem ePin_nonneg (q : ℝ) (n z d : ℕ) : 0 ≤ ePin q n z d := by
  unfold ePin
  positivity

theorem ePin_mono (q : ℝ) (n z : ℕ) {d d' : ℕ} (h : d ≤ d') : ePin q n z d ≤ ePin q n z d' := by
  unfold ePin
  have hr : 0 ≤ (Real.sqrt q)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hd : (d : ℝ) ≤ d' := by exact_mod_cast h
  have h1 : (2 : ℝ) ^ d ≤ 2 ^ d' := pow_le_pow_right₀ (by norm_num) h
  have h2 : (2 * n + z : ℝ) * (Real.sqrt q)⁻¹ ^ 2 + d / 2 * (Real.sqrt q)⁻¹ ≤
      (2 * n + z : ℝ) * (Real.sqrt q)⁻¹ ^ 2 + d' / 2 * (Real.sqrt q)⁻¹ := by
    have : (d : ℝ) / 2 * (Real.sqrt q)⁻¹ ≤ d' / 2 * (Real.sqrt q)⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) hr
    linarith
  have h0 : (0 : ℝ) ≤ (2 * n + z : ℝ) * (Real.sqrt q)⁻¹ ^ 2 + d / 2 * (Real.sqrt q)⁻¹ := by
    positivity
  exact mul_le_mul h1 h2 h0 (by positivity)

end PinFacts

/-! ## The one-coordinate sums -/

section PinOne

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The free values of a coordinate** (`lem:extraction-merged-count` with the pins as the
conditions and no merged roots, since the cross roots `x_i` avoid `𝓜`):
`∑_{t allowed, t ∉ x([n])} ω_j(t) ≤ q 2^{-ϖ_j} (1 + e_{ϖ_j + |N_Y(j)|}(q, 2n + z))`. -/
theorem pin_free_sum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (x : Fin n → F)
    (hxinj : Function.Injective x) (hxM : ∀ i, x i ∉ M) (j : Fin n) :
    ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∉ univ.image x), pinOmega ς x j t ≤
      (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin j *
        (1 + coarseError (pinCount pin j + (pinNY ς j).card) (Fintype.card F)
          (2 * n + M.card)) := by
  set ι := ↥(pinRoots pin j)
  set κ := ↥(pinNY ς j)
  let β : ι → F := fun b => b.1
  have hβ : Function.Injective β := fun a b h => Subtype.ext h
  let γ : κ → F := fun i => x i.1
  have hγ : Function.Injective γ := fun a b h => Subtype.ext (hxinj h)
  have hpm : ∀ b : ι, pin j b.1 = 1 ∨ pin j b.1 = -1 := by
    intro b
    have hb : pin j b.1 ≠ 0 := (mem_filter.mp b.2).2
    rcases hpin j b.1 with h | h | h
    · exact absurd h hb
    · exact Or.inl h
    · exact Or.inr h
  have hςpm : ∀ i : κ, ς i.1 j = 1 ∨ ς i.1 j = -1 := by
    intro i
    have hi : ς i.1 j ≠ 0 := (mem_filter.mp i.2).2
    rcases hς i.1 j with h | h | h
    · exact absurd h hi
    · exact Or.inl h
    · exact Or.inr h
  let s : ι → ℤ := fun b => quadraticChar F (pin j b.1 : F)
  have hs : ∀ b, s b = 1 ∨ s b = -1 := fun b => pin_char_pm (hpm b)
  let s' : κ → ℤ := fun i => quadraticChar F (ς i.1 j : F)
  have hs' : ∀ i, s' i = 1 ∨ s' i = -1 := fun i => pin_char_pm (hςpm i)
  set 𝒳 : Finset F := M ∪ univ.image x with h𝒳
  have hβX : ∀ b, β b ∈ 𝒳 := fun b =>
    mem_union_left _ (hpinM j b.1 (mem_filter.mp b.2).2)
  have hγX : ∀ i, γ i ∈ 𝒳 := fun i => mem_union_right _ (mem_image_of_mem x (mem_univ _))
  have hmc := merged_count_le_fintype hW β hβ γ hγ s hs s' hs' 𝒳 hβX hγX
    (n' := 2 * (n : ℝ) + M.card) (by positivity)
  have hm0 : mergedCount β γ = 0 := by
    unfold mergedCount
    rw [card_eq_zero, filter_eq_empty_iff]
    intro il _ h
    have h1 : β il.1 ∈ M := hpinM j il.1.1 (mem_filter.mp il.1.2).2
    have h2 : γ il.2 ∈ M := h ▸ h1
    exact hxM il.2.1 h2
  have hcι : Fintype.card ι = pinCount pin j := Fintype.card_coe _
  have hcκ : Fintype.card κ = (pinNY ς j).card := Fintype.card_coe _
  rw [hm0, hcι, hcκ, Nat.sub_zero, pow_zero, mul_one] at hmc
  have hset : (pinAllowed M pin j).filter (fun t => t ∉ univ.image x) =
      univ.filter (fun y => y ∉ 𝒳 ∧ ∀ b, quadraticChar F (y - β b) = s b) := by
    ext t
    simp only [pinAllowed, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨htM, hpins⟩, htx⟩
      refine ⟨⟨htM, htx⟩, fun b => ?_⟩
      exact (pin_cond_iff (hpm b) _).mp (hpins b.1 (mem_filter.mp b.2).2)
    · rintro ⟨⟨htM, htx⟩, hall⟩
      refine ⟨⟨htM, fun b hb => ?_⟩, htx⟩
      have hbm : b ∈ pinRoots pin j := mem_filter.mpr ⟨mem_univ _, hb⟩
      exact (pin_cond_iff (hpm ⟨b, hbm⟩) _).mpr (hall ⟨b, hbm⟩)
  have hsum : ∀ t, pinOmega ς x j t = ∏ l, ((1 : ℝ) + s' l * quadraticChar F (t - γ l)) := by
    intro t
    unfold pinOmega
    rw [← prod_coe_sort (pinNY ς j)]
    refine prod_congr rfl fun i _ => ?_
    simp only [s', γ, map_mul, Int.cast_mul]
  rw [hset, sum_congr rfl fun t _ => hsum t]
  exact hmc

/-- **The coincident values of a coordinate**: `∑_{t ∈ x([n])} ω_j(t) ≤
∑_i 2^{|N_Y(j)| - [i ∈ N_Y(j)]}` (the factor of the coincident pair is `1 + χ(0) = 1`). -/
theorem pin_coinc_sum_le {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F)
    (hxinj : Function.Injective x) (j : Fin n) (S : Finset F) :
    ∑ t ∈ S.filter (fun t => t ∈ univ.image x), pinOmega ς x j t ≤
      ∑ i, (2 : ℝ) ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) := by
  calc ∑ t ∈ S.filter (fun t => t ∈ univ.image x), pinOmega ς x j t
      ≤ ∑ t ∈ univ.image x, pinOmega ς x j t :=
        sum_le_sum_of_subset_of_nonneg (fun t ht => (mem_filter.mp ht).2)
          (fun t _ _ => pinOmega_nonneg ς x j t)
    _ = ∑ i, pinOmega ς x j (x i) := sum_image fun a _ b _ h => hxinj h
    _ ≤ _ := by
        refine sum_le_sum fun i _ => ?_
        unfold pinOmega
        have hg0 : ∀ i' ∈ pinNY ς j,
            0 ≤ 1 + (quadraticChar F ((ς i' j : F) * (x i - x i')) : ℝ) :=
          fun i' _ => (pin_one_add_chi _).1
        have hg2 : ∀ i' ∈ pinNY ς j,
            1 + (quadraticChar F ((ς i' j : F) * (x i - x i')) : ℝ) ≤ 2 :=
          fun i' _ => (pin_one_add_chi _).2
        split_ifs with hi
        · rw [← mul_prod_erase _ _ hi]
          simp only [sub_self, mul_zero, quadraticChar_zero, Int.cast_zero, add_zero, one_mul]
          rw [← card_erase_of_mem hi]
          calc ∏ i' ∈ (pinNY ς j).erase i,
                (1 + (quadraticChar F ((ς i' j : F) * (x i - x i')) : ℝ))
              ≤ ∏ _i' ∈ (pinNY ς j).erase i, (2 : ℝ) :=
                prod_le_prod₀ (fun i' hi' => hg0 i' (mem_of_mem_erase hi'))
                  (fun i' hi' => hg2 i' (mem_of_mem_erase hi'))
            _ = _ := prod_const 2
        · rw [Nat.sub_zero]
          calc ∏ i' ∈ pinNY ς j, (1 + (quadraticChar F ((ς i' j : F) * (x i - x i')) : ℝ))
              ≤ ∏ _i' ∈ pinNY ς j, (2 : ℝ) := prod_le_prod₀ hg0 hg2
            _ = _ := prod_const 2

end PinOne

/-! ## The lower count of `𝓘_pin` -/

section PinCount

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem mem_pinPart {n : ℕ} {M : Finset F} {pin : Fin n → F → ℤ} {S : Finset (Fin n)}
    {y : Fin n → F} :
    y ∈ pinPart M pin S ↔ (∀ j, j ∉ S → y j = 0) ∧ (∀ a ∈ S, ∀ b ∈ S, y a = y b → a = b) ∧
      ∀ j ∈ S, y j ∈ pinAllowed M pin j := by
  unfold pinPart
  simp only [mem_filter, mem_univ, true_and]

theorem mem_pinLab {n : ℕ} {M : Finset F} {pin : Fin n → F → ℤ} {x : Fin n → F} :
    x ∈ pinLab M pin ↔ (∀ a b, x a = x b → a = b) ∧ ∀ j, x j ∈ pinAllowed M pin j := by
  unfold pinLab
  simp only [mem_filter, mem_univ, true_and]

/-- The paper's description of `𝓘_pin`: injective, avoiding `𝓜`, with `ε(x_i - β)` a nonzero
square for every pin `(β, ε)` of every `i`. -/
theorem mem_pinLab_iff {n : ℕ} {M : Finset F} {pin : Fin n → F → ℤ} {x : Fin n → F} :
    x ∈ pinLab M pin ↔ Function.Injective x ∧ (∀ i, x i ∉ M) ∧
      ∀ i β, pin i β ≠ 0 → quadraticChar F ((pin i β : F) * (x i - β)) = 1 := by
  rw [mem_pinLab]
  simp only [pinAllowed, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun a b h => h1 a b h, fun i => (h2 i).1, fun i => (h2 i).2⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨fun a b h => h1 h, fun i => ⟨h2 i, h3 i⟩⟩

theorem pinPart_univ {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ) :
    pinPart M pin univ = pinLab M pin := by
  ext y
  rw [mem_pinPart, mem_pinLab]
  constructor
  · rintro ⟨-, h1, h2⟩
    exact ⟨fun a b h => h1 a (mem_univ _) b (mem_univ _) h, fun j => h2 j (mem_univ _)⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun j hj => absurd (mem_univ j) hj, fun a _ b _ h => h1 a b h, fun j _ => h2 j⟩

theorem pinPart_empty {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ) :
    pinPart M pin ∅ = {fun _ => 0} := by
  ext y
  rw [mem_pinPart, mem_singleton]
  constructor
  · rintro ⟨h, -, -⟩
    funext j
    exact h j (notMem_empty j)
  · rintro rfl
    exact ⟨fun _ _ => rfl, fun a ha => absurd ha (notMem_empty a), fun j hj =>
      absurd hj (notMem_empty j)⟩

/-- **Labelling one more coordinate.** -/
theorem sum_pinPart_insert {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ) {S : Finset (Fin n)}
    {v : Fin n} (hv : v ∉ S) (g : (Fin n → F) → ℝ) :
    ∑ c ∈ pinPart M pin (insert v S), g c =
      ∑ c ∈ pinPart M pin S, ∑ t ∈ (pinAllowed M pin v).filter (fun t => t ∉ S.image c),
        g (Function.update c v t) := by
  have hmaps : ∀ c ∈ pinPart M pin (insert v S), Function.update c v 0 ∈ pinPart M pin S := by
    intro c hc
    rw [mem_pinPart] at hc ⊢
    obtain ⟨hz, hinj, hal⟩ := hc
    refine ⟨fun u hu => ?_, fun a ha b hb hab => ?_, fun j hj => ?_⟩
    · by_cases huv : u = v
      · subst huv
        simp
      · rw [Function.update_of_ne huv]
        exact hz u (by simp [huv, hu])
    · have hav : a ≠ v := fun h => hv (h ▸ ha)
      have hbv : b ≠ v := fun h => hv (h ▸ hb)
      rw [Function.update_of_ne hav, Function.update_of_ne hbv] at hab
      exact hinj a (mem_insert_of_mem ha) b (mem_insert_of_mem hb) hab
    · have hjv : j ≠ v := fun h => hv (h ▸ hj)
      rw [Function.update_of_ne hjv]
      exact hal j (mem_insert_of_mem hj)
  rw [← sum_fiberwise_of_maps_to hmaps]
  refine sum_congr rfl fun c hc => ?_
  have hcv : c v = 0 := (mem_pinPart.mp hc).1 v hv
  have hfib : (pinPart M pin (insert v S)).filter (fun c'' => Function.update c'' v 0 = c) =
      ((pinAllowed M pin v).filter (fun t => t ∉ S.image c)).image
        (fun t => Function.update c v t) := by
    ext c''
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hc'', heq⟩
      have hcu : ∀ u, u ≠ v → c u = c'' u := fun u hu => by
        rw [← heq, Function.update_of_ne hu]
      obtain ⟨-, hinj'', hal''⟩ := mem_pinPart.mp hc''
      refine ⟨c'' v, ⟨hal'' v (mem_insert_self v S), ?_⟩, ?_⟩
      · rintro ⟨a, ha, hca⟩
        have hav : a ≠ v := fun h => hv (h ▸ ha)
        rw [hcu a hav] at hca
        exact hav (hinj'' a (mem_insert_of_mem ha) v (mem_insert_self v S) hca)
      · funext u
        by_cases huv : u = v
        · subst huv
          simp
        · rw [Function.update_of_ne huv, hcu u huv]
    · rintro ⟨t, ⟨htal, htS⟩, rfl⟩
      obtain ⟨hz, hinj, hal⟩ := mem_pinPart.mp hc
      refine ⟨?_, ?_⟩
      · rw [mem_pinPart]
        refine ⟨fun u hu => ?_, fun a ha b hb hab => ?_, fun j hj => ?_⟩
        · have huv : u ≠ v := fun h => hu (h ▸ mem_insert_self v S)
          rw [Function.update_of_ne huv]
          exact hz u (fun h => hu (mem_insert_of_mem h))
        · rcases mem_insert.mp ha with rfl | ha'
          · rcases mem_insert.mp hb with rfl | hb'
            · rfl
            · have hbv : b ≠ a := fun h => hv (h ▸ hb')
              rw [Function.update_self, Function.update_of_ne hbv] at hab
              exact absurd ⟨b, hb', hab.symm⟩ htS
          · have hav : a ≠ v := fun h => hv (h ▸ ha')
            rcases mem_insert.mp hb with rfl | hb'
            · rw [Function.update_self, Function.update_of_ne hav] at hab
              exact absurd ⟨a, ha', hab⟩ htS
            · have hbv : b ≠ v := fun h => hv (h ▸ hb')
              rw [Function.update_of_ne hav, Function.update_of_ne hbv] at hab
              exact hinj a ha' b hb' hab
        · rcases mem_insert.mp hj with rfl | hj'
          · rw [Function.update_self]
            exact htal
          · have hjv : j ≠ v := fun h => hv (h ▸ hj')
            rw [Function.update_of_ne hjv]
            exact hal j hj'
      · funext u
        by_cases huv : u = v
        · subst huv
          simp [hcv]
        · simp [Function.update_of_ne huv]
  rw [hfib, sum_image]
  intro t _ t' _ h
  simpa using congrFun h v

/-- One coordinate: at most `|𝓜| + n` labels are excluded, so `lem:extension`(c) gives
`|Φ| ≥ q 2^{-ϖ_v} (1 - e^pin_ϖ)`. -/
theorem pin_adm_card_ge (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (S : Finset (Fin n)) (c : Fin n → F) (v : Fin n) :
    (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin v *
        (1 - ePin (Fintype.card F) n M.card ϖ) ≤
      ((pinAllowed M pin v).filter (fun t => t ∉ S.image c)).card := by
  set ι := ↥(pinRoots pin v)
  let β : ι → F := fun b => b.1
  have hβ : Function.Injective β := fun a b h => Subtype.ext h
  have hpm : ∀ b : ι, pin v b.1 = 1 ∨ pin v b.1 = -1 := by
    intro b
    have hb : pin v b.1 ≠ 0 := (mem_filter.mp b.2).2
    rcases hpin v b.1 with h | h | h
    · exact absurd h hb
    · exact Or.inl h
    · exact Or.inr h
  let s : ι → ℤ := fun b => quadraticChar F (pin v b.1 : F)
  have hs : ∀ b, s b = 1 ∨ s b = -1 := fun b => pin_char_pm (hpm b)
  set 𝒳 : Finset F := M ∪ S.image c with h𝒳
  have hβX : ∀ b, β b ∈ 𝒳 := fun b => mem_union_left _ (hpinM v b.1 (mem_filter.mp b.2).2)
  have hset : (pinAllowed M pin v).filter (fun t => t ∉ S.image c) = admissible β s 𝒳 := by
    ext t
    simp only [pinAllowed, admissible, mem_filter, mem_univ, true_and, h𝒳, mem_union, not_or]
    constructor
    · rintro ⟨⟨htM, hpins⟩, htS⟩
      exact ⟨⟨htM, htS⟩, fun b => (pin_cond_iff (hpm b) _).mp (hpins b.1 (mem_filter.mp b.2).2)⟩
    · rintro ⟨⟨htM, htS⟩, hall⟩
      refine ⟨⟨htM, fun b hb => ?_⟩, htS⟩
      have hbm : b ∈ pinRoots pin v := mem_filter.mpr ⟨mem_univ _, hb⟩
      exact (pin_cond_iff (hpm ⟨b, hbm⟩) _).mpr (hall ⟨b, hbm⟩)
  rw [hset]
  have hlow := (extension_bounds hW β hβ s hs 𝒳 hβX).2
  have hcι : Fintype.card ι = pinCount pin v := Fintype.card_coe _
  rw [hcι] at hlow
  set t := pinCount pin v
  have hq1 : (1 : ℝ) ≤ Fintype.card F := by exact_mod_cast Fintype.card_pos
  have hX : (𝒳.card : ℝ) ≤ n + M.card := by
    have h1 : 𝒳.card ≤ M.card + S.card := (card_union_le _ _).trans
      (Nat.add_le_add_left card_image_le _)
    have h2 : S.card ≤ n := (card_le_univ S).trans (by simp)
    have : 𝒳.card ≤ n + M.card := by omega
    exact_mod_cast this
  have hsoft := coverRow_softError_le hq1 (n + M.card) t
  have hmono1 : coarseError t (Fintype.card F) ((n + M.card : ℕ) : ℝ) ≤
      coarseError t (Fintype.card F) (2 * n + M.card) :=
    coverRow_coarseError_mono_n t (by push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
  have hmono2 := coarseError_le_ePin (Fintype.card F) n M.card t
  have hmono3 := ePin_mono (Fintype.card F) n M.card (hϖ v)
  have hpos : (0 : ℝ) < 2 ^ t := by positivity
  have h2X := mul_le_mul_of_nonneg_left hX hpos.le
  have key : (Fintype.card F : ℝ) * (1 - ePin (Fintype.card F) n M.card ϖ) ≤
      2 ^ t * (admissible β s 𝒳).card := by
    have : (Fintype.card F : ℝ) * coarseError t (Fintype.card F) ((n + M.card : ℕ) : ℝ) ≤
        Fintype.card F * ePin (Fintype.card F) n M.card ϖ :=
      mul_le_mul_of_nonneg_left (hmono1.trans (hmono2.trans hmono3)) (by linarith)
    unfold softError at hsoft
    push_cast at hsoft h2X this
    nlinarith
  have hinv : (2 : ℝ)⁻¹ ^ t * 2 ^ t = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow]
  calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ t * (1 - ePin (Fintype.card F) n M.card ϖ)
      = (2 : ℝ)⁻¹ ^ t * ((Fintype.card F : ℝ) * (1 - ePin (Fintype.card F) n M.card ϖ)) := by
        ring
    _ ≤ (2 : ℝ)⁻¹ ^ t * (2 ^ t * (admissible β s 𝒳).card) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (admissible β s 𝒳).card := by rw [← mul_assoc, hinv, one_mul]

/-- **The lower count** (`lem:extension`(c) along the coordinates, as in Step 3 of the proof of
the pinned compressed classes): `|𝓘_pin| ≥ ∏_j q 2^{-ϖ_j} (1 - e^pin_ϖ)`, used by
`prop:pinned-collision`. -/
theorem card_pinLab_ge (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) :
    ∏ j, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin j *
        (1 - ePin (Fintype.card F) n M.card ϖ)) ≤ (pinLab M pin).card := by
  rw [← pinPart_univ]
  have hL0 : ∀ j, (0 : ℝ) ≤ (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin j *
      (1 - ePin (Fintype.card F) n M.card ϖ) := fun j =>
    mul_nonneg (by positivity) (by linarith)
  suffices h : ∀ S : Finset (Fin n), ∏ j ∈ S, ((Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin j *
      (1 - ePin (Fintype.card F) n M.card ϖ)) ≤ (pinPart M pin S).card from h univ
  intro S
  induction S using Finset.induction_on with
  | empty => simp [pinPart_empty]
  | insert v S hv ih =>
    rw [prod_insert hv]
    have hcard : ((pinPart M pin (insert v S)).card : ℝ) =
        ∑ c ∈ pinPart M pin S,
          ((((pinAllowed M pin v).filter (fun t => t ∉ S.image c)).card : ℕ) : ℝ) := by
      have := sum_pinPart_insert M pin hv (fun _ => (1 : ℝ))
      simp only [sum_const, nsmul_eq_mul, mul_one] at this
      exact this
    rw [hcard]
    calc (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin v *
          (1 - ePin (Fintype.card F) n M.card ϖ) * ∏ j ∈ S, ((Fintype.card F : ℝ) *
            (2 : ℝ)⁻¹ ^ pinCount pin j * (1 - ePin (Fintype.card F) n M.card ϖ))
        ≤ (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin v *
          (1 - ePin (Fintype.card F) n M.card ϖ) * (pinPart M pin S).card :=
          mul_le_mul_of_nonneg_left ih (hL0 v)
      _ = ∑ _c ∈ pinPart M pin S, (Fintype.card F : ℝ) * (2 : ℝ)⁻¹ ^ pinCount pin v *
          (1 - ePin (Fintype.card F) n M.card ϖ) := by
          rw [sum_const, nsmul_eq_mul]
          ring
      _ ≤ _ := sum_le_sum fun c _ =>
          pin_adm_card_ge hW M pin hpin hpinM ϖ hϖ S c v

end PinCount

/-! ## The row sums -/

section PinRows

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The factor `ω_j` split by coincidence: `a_j(t) = [t ∉ x([n])] ω_j(t)`. -/
noncomputable def pinA {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F) (j : Fin n) (t : F) : ℝ :=
  if t ∈ univ.image x then 0 else pinOmega ς x j t

/-- `b_j(t) = [t ∈ x([n])] ω_j(t)`. -/
noncomputable def pinB {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F) (j : Fin n) (t : F) : ℝ :=
  if t ∈ univ.image x then pinOmega ς x j t else 0

theorem pinA_nonneg {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F) (j : Fin n) (t : F) :
    0 ≤ pinA ς x j t := by
  unfold pinA
  split_ifs
  · exact le_rfl
  · exact pinOmega_nonneg ς x j t

theorem pinB_nonneg {n : ℕ} (ς : Fin n → Fin n → ℤ) (x : Fin n → F) (j : Fin n) (t : F) :
    0 ≤ pinB ς x j t := by
  unfold pinB
  split_ifs
  · exact pinOmega_nonneg ς x j t
  · exact le_rfl

/-- **The coincidence strata**: `K(x, y) = ∑_{∅ ≠ I ⊆ [n]} ∏_{j ∈ I} b_j(y_j) ∏_{j ∉ I} a_j(y_j)`,
`I` the set of coincident `y`-vertices. -/
theorem pinKer_expand {n : ℕ} (ς : Fin n → Fin n → ℤ) (x y : Fin n → F) :
    pinKer ς x y = ∑ I ∈ (univ : Finset (Fin n)).powerset.erase ∅,
      (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) := by
  have hω : ∀ j, pinOmega ς x j (y j) = pinB ς x j (y j) + pinA ς x j (y j) := by
    intro j
    unfold pinA pinB
    split_ifs <;> ring
  have hprod : ∏ j, pinOmega ς x j (y j) = ∑ I ∈ (univ : Finset (Fin n)).powerset,
      (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) := by
    rw [prod_congr rfl fun j _ => hω j]
    exact prod_add _ _ _
  rw [← add_sum_erase _ _ (empty_mem_powerset univ), prod_empty, one_mul, sdiff_empty] at hprod
  have hK : pinKer ς x y = ∏ j, pinOmega ς x j (y j) - ∏ j, pinA ς x j (y j) := by
    unfold pinKer
    split_ifs with hc
    · obtain ⟨i, j, hij⟩ := hc
      have hm : y j ∈ univ.image x := mem_image.mpr ⟨i, mem_univ _, hij⟩
      have h0 : pinA ς x j (y j) = 0 := by
        unfold pinA
        simp only [hm, ↓reduceIte]
      rw [prod_eq_zero (f := fun j => pinA ς x j (y j)) (mem_univ j) h0]
      ring
    · have hall : ∀ j, pinA ς x j (y j) = pinOmega ς x j (y j) := by
        intro j
        have hm : y j ∉ univ.image x := by
          rintro hm
          obtain ⟨i, -, hij⟩ := mem_image.mp hm
          exact hc ⟨i, j, hij⟩
        unfold pinA
        simp only [hm, ↓reduceIte]
      rw [prod_congr rfl fun j _ => hall j]
      ring
  rw [hK, hprod]
  ring

/-- The elementary inequality behind `D_Y`: with `A_j = c_j (1 + E_j)`, `B_j ≤ c_j u_j` and
`L_j = c_j (1 - e)`, `∏ (B + A) - ∏ A ≤ Υ (1 - e)^{-n} (e^{∑ u} - 1) ∏ L`. -/
theorem pin_algebra {n : ℕ} (c E u B : Fin n → ℝ) (e : ℝ) (hc : ∀ j, 0 < c j)
    (hE : ∀ j, 0 ≤ E j) (hu : ∀ j, 0 ≤ u j) (hB0 : ∀ j, 0 ≤ B j) (hB : ∀ j, B j ≤ c j * u j)
    (he : e < 1) :
    ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) ≤
      (∏ j, (1 + E j)) / (1 - e) ^ n * (Real.exp (∑ j, u j) - 1) * ∏ j, (c j * (1 - e)) := by
  have h1 : ∏ j, (B j + c j * (1 + E j)) ≤
      (∏ j, c j) * (∏ j, (1 + E j)) * ∏ j, (1 + u j) := by
    rw [← prod_mul_distrib, ← prod_mul_distrib]
    refine prod_le_prod₀ (fun j _ => add_nonneg (hB0 j)
      (mul_nonneg (hc j).le (by linarith [hE j]))) fun j _ => ?_
    have := hB j
    nlinarith [hc j, hE j, hu j, mul_nonneg (hc j).le (mul_nonneg (hE j) (hu j))]
  have h2 : ∏ j, (1 + u j) ≤ Real.exp (∑ j, u j) := by
    rw [Real.exp_sum]
    exact prod_le_prod₀ (fun j _ => by linarith [hu j]) fun j _ => by
      linarith [Real.add_one_le_exp (u j)]
  have hcE : 0 ≤ (∏ j, c j) * ∏ j, (1 + E j) :=
    mul_nonneg (prod_nonneg fun j _ => (hc j).le) (prod_nonneg fun j _ => by linarith [hE j])
  have h3 : ∏ j, (c j * (1 + E j)) = (∏ j, c j) * ∏ j, (1 + E j) := prod_mul_distrib
  have h4 : ∏ j, (c j * (1 - e)) = (∏ j, c j) * (1 - e) ^ n := by
    rw [prod_mul_distrib, prod_const, card_univ, Fintype.card_fin]
  have hne : (1 - e) ^ n ≠ 0 := pow_ne_zero _ (by linarith)
  rw [h3, h4]
  calc ∏ j, (B j + c j * (1 + E j)) - (∏ j, c j) * ∏ j, (1 + E j)
      ≤ (∏ j, c j) * (∏ j, (1 + E j)) * Real.exp (∑ j, u j) -
          (∏ j, c j) * ∏ j, (1 + E j) := by
        have := mul_le_mul_of_nonneg_left h2 hcE
        linarith
    _ = (∏ j, (1 + E j)) / (1 - e) ^ n * (Real.exp (∑ j, u j) - 1) *
          ((∏ j, c j) * (1 - e) ^ n) := by
        field_simp

theorem pinD_nonneg {n : ℕ} (q : ℝ) (z ϖ : ℕ) (N : Fin n → Finset (Fin n))
    (he : ePin q n z ϖ < 1) : 0 ≤ pinD q z ϖ N := by
  unfold pinD pinUps pinU
  have hU : 0 ≤ (Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
      (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0)) := by positivity
  have hexp : 0 ≤ Real.exp ((Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
      (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0))) - 1 := by
    have := Real.add_one_le_exp ((Real.sqrt q)⁻¹ ^ 2 * ∑ j, ∑ i,
      (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0)))
    linarith
  have hUps : 0 ≤ ∏ j, (1 + ePin q n z (ϖ + (N j).card)) :=
    prod_nonneg fun j _ => by linarith [ePin_nonneg q n z (ϖ + (N j).card)]
  have h1 : 0 < 1 - ePin q n z ϖ := by linarith
  exact mul_nonneg (div_nonneg hUps (pow_nonneg h1.le _)) hexp

/-- **Row sums of `T^pin_coll`** (the proof of `prop:pinned-collision`): for `x ∈ 𝓘_pin`,
`∑_{y ∈ 𝓘_pin} K(x, y) ≤ D_Y |𝓘_pin|`, i.e. `E_{y ∼ μ} K(x, y) ≤ D_Y`. -/
theorem pin_rowSum_le (hW : WeilBound F) {n : ℕ} (M : Finset F) (pin : Fin n → F → ℤ)
    (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) (x : Fin n → F) (hx : x ∈ pinLab M pin) :
    ∑ y ∈ pinLab M pin, pinKer ς x y ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) * (pinLab M pin).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq0 : 0 < q := by rw [hq]; exact_mod_cast Fintype.card_pos
  obtain ⟨hxinj, hxM, -⟩ := mem_pinLab_iff.mp hx
  set c : Fin n → ℝ := fun j => q * (2 : ℝ)⁻¹ ^ pinCount pin j with hcdef
  set E : Fin n → ℝ := fun j => ePin q n M.card (ϖ + (pinNY ς j).card) with hEdef
  set u : Fin n → ℝ := fun j => (Real.sqrt q)⁻¹ ^ 2 * ∑ i,
    (2 : ℝ) ^ (ϖ + ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)) with hudef
  set B : Fin n → ℝ := fun j => ∑ i,
    (2 : ℝ) ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) with hBdef
  have hc0 : ∀ j, 0 < c j := fun j => by simp only [hcdef]; positivity
  have hE0 : ∀ j, 0 ≤ E j := fun j => ePin_nonneg _ _ _ _
  have hu0 : ∀ j, 0 ≤ u j := fun j => by simp only [hudef]; positivity
  have hB0 : ∀ j, 0 ≤ B j := fun j => by simp only [hBdef]; positivity
  have hBu : ∀ j, B j ≤ c j * u j := by
    intro j
    simp only [hBdef, hcdef, hudef, mul_sum]
    refine sum_le_sum fun i _ => ?_
    have hr : q * (Real.sqrt q)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt hq0.le, mul_inv_cancel₀ hq0.ne']
    have h2 : (1 : ℝ) ≤ (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ := by
      have e2 : (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ = 2 ^ (ϖ - pinCount pin j) := by
        calc (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ
            = (2 : ℝ)⁻¹ ^ pinCount pin j * (2 ^ (ϖ - pinCount pin j) * 2 ^ pinCount pin j) := by
              rw [← pow_add, Nat.sub_add_cancel (hϖ j)]
          _ = 2 ^ (ϖ - pinCount pin j) * ((2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ pinCount pin j) := by
              ring
          _ = 2 ^ (ϖ - pinCount pin j) := by
              rw [← mul_pow, inv_mul_cancel₀ two_ne_zero, one_pow, mul_one]
      rw [e2]
      exact one_le_pow₀ (by norm_num)
    have h0 : (0 : ℝ) ≤ 2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) := by
      positivity
    calc (2 : ℝ) ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)
        ≤ ((2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ) *
            2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0) :=
          le_mul_of_one_le_left h0 h2
      _ = q * (2 : ℝ)⁻¹ ^ pinCount pin j * ((Real.sqrt q)⁻¹ ^ 2 *
            (2 : ℝ) ^ (ϖ + ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0))) := by
          rw [pow_add]
          calc (2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ *
                2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)
              = (q * (Real.sqrt q)⁻¹ ^ 2) * ((2 : ℝ)⁻¹ ^ pinCount pin j * 2 ^ ϖ *
                  2 ^ ((pinNY ς j).card - if i ∈ pinNY ς j then 1 else 0)) := by
                rw [hr, one_mul]
            _ = _ := by ring
  -- the one-coordinate bounds
  have hA : ∀ j, ∑ t ∈ pinAllowed M pin j, pinA ς x j t ≤ c j * (1 + E j) := by
    intro j
    have h1 : ∑ t ∈ pinAllowed M pin j, pinA ς x j t =
        ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∉ univ.image x), pinOmega ς x j t := by
      rw [sum_filter]
      refine sum_congr rfl fun t _ => ?_
      unfold pinA
      split_ifs <;> simp_all
    rw [h1]
    refine (pin_free_sum_le hW M pin hpin hpinM ς hς x hxinj hxM j).trans ?_
    simp only [hcdef, hEdef]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := (coarseError_le_ePin q n M.card (pinCount pin j + (pinNY ς j).card)).trans
      (ePin_mono q n M.card (Nat.add_le_add_right (hϖ j) _))
    linarith
  have hBb : ∀ j, ∑ t ∈ pinAllowed M pin j, pinB ς x j t ≤ B j := by
    intro j
    have h1 : ∑ t ∈ pinAllowed M pin j, pinB ς x j t =
        ∑ t ∈ (pinAllowed M pin j).filter (fun t => t ∈ univ.image x), pinOmega ς x j t := by
      rw [sum_filter]
      refine sum_congr rfl fun t _ => ?_
      unfold pinB
      split_ifs <;> simp_all
    rw [h1]
    exact pin_coinc_sum_le ς x hxinj j _
  -- each stratum
  have hstrat : ∀ I ∈ (univ : Finset (Fin n)).powerset.erase ∅,
      ∑ y ∈ pinLab M pin, (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) ≤
        (∏ j ∈ I, B j) * ∏ j ∈ univ \ I, (c j * (1 + E j)) := by
    intro I _
    have hite : ∀ y : Fin n → F, (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) =
        ∏ j, (if j ∈ I then pinB ς x j (y j) else pinA ς x j (y j)) := by
      intro y
      rw [prod_ite, filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff]
    have hite' : (∏ j ∈ I, B j) * ∏ j ∈ univ \ I, (c j * (1 + E j)) =
        ∏ j, (if j ∈ I then B j else c j * (1 + E j)) := by
      rw [prod_ite, filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff]
    rw [hite']
    calc ∑ y ∈ pinLab M pin, (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j)
        = ∑ y ∈ pinLab M pin, ∏ j, (if j ∈ I then pinB ς x j (y j) else pinA ς x j (y j)) :=
          sum_congr rfl fun y _ => hite y
      _ ≤ ∑ y ∈ Fintype.piFinset (fun j => pinAllowed M pin j),
            ∏ j, (if j ∈ I then pinB ς x j (y j) else pinA ς x j (y j)) := by
          refine sum_le_sum_of_subset_of_nonneg (fun y hy => ?_) fun y _ _ =>
            prod_nonneg fun j _ => ?_
          · rw [Fintype.mem_piFinset]
            exact (mem_pinLab.mp hy).2
          · split_ifs
            · exact pinB_nonneg ς x j _
            · exact pinA_nonneg ς x j _
      _ = ∏ j, ∑ t ∈ pinAllowed M pin j, (if j ∈ I then pinB ς x j t else pinA ς x j t) :=
          (prod_univ_sum (fun j => pinAllowed M pin j)
            (fun j t => if j ∈ I then pinB ς x j t else pinA ς x j t)).symm
      _ ≤ ∏ j, (if j ∈ I then B j else c j * (1 + E j)) := by
          refine prod_le_prod₀ (fun j _ => sum_nonneg fun t _ => ?_) fun j _ => ?_
          · split_ifs
            · exact pinB_nonneg ς x j t
            · exact pinA_nonneg ς x j t
          · split_ifs
            · exact hBb j
            · exact hA j
  -- the sum over the strata
  have hsumI : ∑ I ∈ (univ : Finset (Fin n)).powerset.erase ∅,
      (∏ j ∈ I, B j) * ∏ j ∈ univ \ I, (c j * (1 + E j)) =
        ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) := by
    have h := prod_add B (fun j => c j * (1 + E j)) univ
    rw [← add_sum_erase _ _ (empty_mem_powerset univ), prod_empty, one_mul, sdiff_empty] at h
    rw [h]
    ring
  have hrow : ∑ y ∈ pinLab M pin, pinKer ς x y ≤
      ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) := by
    rw [← hsumI]
    calc ∑ y ∈ pinLab M pin, pinKer ς x y
        = ∑ I ∈ (univ : Finset (Fin n)).powerset.erase ∅, ∑ y ∈ pinLab M pin,
            (∏ j ∈ I, pinB ς x j (y j)) * ∏ j ∈ univ \ I, pinA ς x j (y j) := by
          rw [sum_comm]
          exact sum_congr rfl fun y _ => pinKer_expand ς x y
      _ ≤ _ := sum_le_sum hstrat
  have halg := pin_algebra c E u B (ePin q n M.card ϖ) hc0 hE0 hu0 hB0 hBu he
  have hcount := card_pinLab_ge hW M pin hpin hpinM ϖ hϖ he
  have hD0 := pinD_nonneg q M.card ϖ (pinNY ς) he
  have hDeq : (∏ j, (1 + E j)) / (1 - ePin q n M.card ϖ) ^ n * (Real.exp (∑ j, u j) - 1) =
      pinD q M.card ϖ (pinNY ς) := by
    unfold pinD pinUps pinU
    congr 2
    simp only [hudef, ← mul_sum]
  rw [hDeq] at halg
  calc ∑ y ∈ pinLab M pin, pinKer ς x y
      ≤ ∏ j, (B j + c j * (1 + E j)) - ∏ j, (c j * (1 + E j)) := hrow
    _ ≤ pinD q M.card ϖ (pinNY ς) * ∏ j, (c j * (1 - ePin q n M.card ϖ)) := halg
    _ ≤ pinD q M.card ϖ (pinNY ς) * (pinLab M pin).card :=
        mul_le_mul_of_nonneg_left hcount hD0

end PinRows

/-! ## The operator bound -/

section PinOp

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The transposed signs `ςᵀ_{ji} = -ς_{ij}`, which exchange the two rows. -/
def pinSwap {n : ℕ} (ς : Fin n → Fin n → ℤ) : Fin n → Fin n → ℤ := fun i j => -ς j i

theorem pinNY_swap {n : ℕ} (ς : Fin n → Fin n → ℤ) : pinNY (pinSwap ς) = pinNX ς := by
  funext j
  unfold pinNY pinNX pinSwap
  exact filter_congr fun i _ => by simp

/-- Fubini for the products over the cross pairs. -/
theorem pin_prod_pairs {n : ℕ} (ς : Fin n → Fin n → ℤ) (g : Fin n → Fin n → ℝ) :
    ∏ j, ∏ i ∈ univ.filter (fun i => ς i j ≠ 0), g i j =
      ∏ i, ∏ j ∈ univ.filter (fun j => ς i j ≠ 0), g i j := by
  simp only [prod_filter]
  exact prod_comm

/-- Exchanging the two rows: `K(x, y) = Kᵀ(y, x)`, `Kᵀ` the kernel of the transposed signs
(`N_Y` of `ςᵀ` is `N_X` of `ς`). -/
theorem pinKer_swap {n : ℕ} (ς : Fin n → Fin n → ℤ) (x y : Fin n → F) :
    pinKer ς x y = pinKer (pinSwap ς) y x := by
  unfold pinKer pinOmega
  congr 1
  · have : (∃ i j, x i = y j) ↔ (∃ i j, y i = x j) :=
      ⟨fun ⟨i, j, h⟩ => ⟨j, i, h.symm⟩, fun ⟨i, j, h⟩ => ⟨j, i, h.symm⟩⟩
    simp only [this]
  · rw [pinNY_swap]
    unfold pinNY pinNX
    rw [pin_prod_pairs ς (fun i j => 1 + (quadraticChar F ((ς i j : F) * (y j - x i)) : ℝ))]
    refine prod_congr rfl fun i _ => prod_congr rfl fun j _ => ?_
    simp only [pinSwap, Int.cast_neg]
    congr 3
    ring

theorem pinSwap_signs {n : ℕ} {ς : Fin n → Fin n → ℤ}
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) :
    ∀ i j, pinSwap ς i j = 0 ∨ pinSwap ς i j = 1 ∨ pinSwap ς i j = -1 := by
  intro i j
  unfold pinSwap
  rcases hς j i with h | h | h <;> simp [h]

/-- **`prop:pinned-collision`**, the operator bound. In the setting of
`subsec:push:pinnedremainder` (pins `(β, pin j β)` with roots in `𝓜`, at most `ϖ` per coordinate,
cross signs `ς` with no symmetry), assume `e^pin_ϖ < 1`. The operator `T^pin_coll` on `L²(μ)`,
`μ` uniform on `𝓘_pin`, with kernel `K(x, y) = 1{x([n]) ∩ y([n]) ≠ ∅} ∏_{(i,j) ∈ E_×}
(1 + χ_{ij}(x, y))` relative to `μ ⊗ μ`, has norm at most `(D_X D_Y)^{1/2}`: in matrix form,
`K/|𝓘_pin|` has `ℓ²(𝓘_pin)` operator norm at most `(D_X D_Y)^{1/2}` (Schur's test; every row
sum is at most `D_Y`, every column sum at most `D_X`). `WeilBound F` is Weil's theorem. -/
theorem pinned_collision_opBound (hW : WeilBound F) {n : ℕ} (M : Finset F)
    (pin : Fin n → F → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, pinCount pin j ≤ ϖ)
    (he : ePin (Fintype.card F) n M.card ϖ < 1) (ς : Fin n → Fin n → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1) :
    Sarkozy.Influence.OpBound (pinLab M pin) (pinLab M pin)
      (fun x y => pinKer ς x y / (pinLab M pin).card)
      (Real.sqrt (pinD (Fintype.card F) M.card ϖ (pinNX ς) *
        pinD (Fintype.card F) M.card ϖ (pinNY ς))) := by
  set N : ℝ := ((pinLab M pin).card : ℝ)
  have hD0 := pinD_nonneg (Fintype.card F) M.card ϖ (pinNY ς) he
  have hD0' := pinD_nonneg (Fintype.card F) M.card ϖ (pinNX ς) he
  have hrow : ∀ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin, pinKer ς x y / N ≤
      pinD (Fintype.card F) M.card ϖ (pinNY ς) := by
    intro x hx
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (card_pos.mpr ⟨x, hx⟩)
    rw [← sum_div, div_le_iff₀ hN]
    exact pin_rowSum_le hW M pin hpin hpinM ϖ hϖ he ς hς x hx
  have hcol : ∀ y ∈ pinLab M pin, ∑ x ∈ pinLab M pin, pinKer ς x y / N ≤
      pinD (Fintype.card F) M.card ϖ (pinNX ς) := by
    intro y hy
    have hN : (0 : ℝ) < N := Nat.cast_pos.mpr (card_pos.mpr ⟨y, hy⟩)
    rw [← sum_div, div_le_iff₀ hN]
    have h := pin_rowSum_le hW M pin hpin hpinM ϖ hϖ he (pinSwap ς) (pinSwap_signs hς) y hy
    rw [pinNY_swap] at h
    calc ∑ x ∈ pinLab M pin, pinKer ς x y = ∑ x ∈ pinLab M pin, pinKer (pinSwap ς) y x :=
          sum_congr rfl fun x _ => pinKer_swap ς x y
      _ ≤ _ := h
  have h := Sarkozy.Influence.opBound_schur (R := pinLab M pin) (C := pinLab M pin)
    (A := fun x y => pinKer ς x y / N)
    (fun x y => div_nonneg (pinKer_nonneg ς x y) (Nat.cast_nonneg _)) hD0 hD0' hrow hcol
  rwa [mul_comm] at h

/-- `(D_X D_Y)^{1/2} ≤ max(D_X, D_Y)`. -/
theorem pinned_collision_sqrt_le_max {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ max a b := by
  have hm : 0 ≤ max a b := le_max_of_le_left ha
  calc Real.sqrt (a * b) ≤ Real.sqrt (max a b * max a b) :=
        Real.sqrt_le_sqrt (mul_le_mul (le_max_left a b) (le_max_right a b) hb hm)
    _ = max a b := Real.sqrt_mul_self hm

/-- The inner sum of `U`: `∑_i 2^{ϖ + |S| - [i ∈ S]} = |S| 2^{ϖ + |S| - 1} + (n - |S|) 2^{ϖ + |S|}`,
a function of `|S|` only. -/
theorem pin_inner_sum {n : ℕ} (ϖ : ℕ) (S : Finset (Fin n)) :
    ∑ i, (2 : ℝ) ^ (ϖ + (S.card - if i ∈ S then 1 else 0)) =
      S.card * 2 ^ (ϖ + (S.card - 1)) + ((n - S.card : ℕ) : ℝ) * 2 ^ (ϖ + S.card) := by
  have h : ∀ i, (2 : ℝ) ^ (ϖ + (S.card - if i ∈ S then 1 else 0)) =
      if i ∈ S then 2 ^ (ϖ + (S.card - 1)) else 2 ^ (ϖ + S.card) := by
    intro i
    split_ifs <;> simp
  rw [sum_congr rfl fun i _ => h i, sum_ite, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul,
    filter_mem_eq_inter, univ_inter, filter_notMem_eq_sdiff, card_univ_sdiff, Fintype.card_fin]

/-- **`prop:pinned-collision`, equal constants**: `U` and `Υ` depend only on the multiset of the
neighbourhood sizes, so `D_X = D_Y` when the row and column degrees coincide up to a
permutation `π`. -/
theorem pinD_eq_of_card {n : ℕ} (q : ℝ) (z ϖ : ℕ) (N N' : Fin n → Finset (Fin n))
    (π : Fin n ≃ Fin n) (h : ∀ j, (N (π j)).card = (N' j).card) :
    pinD q z ϖ N = pinD q z ϖ N' := by
  unfold pinD pinUps pinU
  have h1 : ∏ j, (1 + ePin q n z (ϖ + (N j).card)) = ∏ j, (1 + ePin q n z (ϖ + (N' j).card)) := by
    rw [← Equiv.prod_comp π]
    exact prod_congr rfl fun j _ => by rw [h j]
  have h2 : ∑ j, ∑ i, (2 : ℝ) ^ (ϖ + ((N j).card - if i ∈ N j then 1 else 0)) =
      ∑ j, ∑ i, (2 : ℝ) ^ (ϖ + ((N' j).card - if i ∈ N' j then 1 else 0)) := by
    simp only [pin_inner_sum]
    rw [← Equiv.sum_comp π]
    exact sum_congr rfl fun j _ => by rw [h j]
  rw [h1, h2]

/-- `D_X = D_Y` for the pinned collision kernel when there is a permutation `π` of the
coordinates with `|N_X(π j)| = |N_Y(j)|` (equal multisets of row and column degrees). -/
theorem pinned_collision_D_eq {n : ℕ} (q : ℝ) (z ϖ : ℕ) (ς : Fin n → Fin n → ℤ)
    (π : Fin n ≃ Fin n) (h : ∀ j, (pinNX ς (π j)).card = (pinNY ς j).card) :
    pinD q z ϖ (pinNX ς) = pinD q z ϖ (pinNY ς) :=
  pinD_eq_of_card q z ϖ _ _ π h

end PinOp

end Sarkozy.ExtractionK

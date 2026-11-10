module

public import Sarkozy.Labellings.Extension

/-!
# The L20 star kernel `𝖪` on the core (`lem:l20-star-matrix`(c), pointwise part)

`paper/sections/20_middle_reference.tex`, `subsec:middle-l20`, `lem:l20-star-matrix`(c).
`F` is a finite field with `χ(-1) = -1` (for `F = 𝔽_p`: `p ≡ 3 (mod 4)`), `χ = quadraticChar F`
read in `ℝ` (`chi`). A *core* is `C = (a₀, a₁, c₀, c₁) : Fin 4 → F` (the coordinates `0, 1, 4, 5`
of the half `x` of the paper), with the signs `s = (-1, -1, 1, 1)` (`sgn`). It is *admissible*
(`Adm`) if its four labels are distinct and `a_i → c_j` (`χ(c_j - a_i) = 1`) for all `i, j`.

For a label `z`:
* `Kz z C = 𝖪(z, C) = ∏_i (1 - χ(z - a_i)) ∏_j (1 + χ(z - c_j)) = ∏_k (1 + s_k χ(z - C_k))`;
* `ell z C = ℓ(z, C) = -χ(z - a₀) - χ(z - a₁) + χ(z - c₀) + χ(z - c₁)`;
* `Kstar z C = 𝖪_⋆ = 𝖪 - 1 - ℓ`;
* `psi S z C = ψ_S(z, x) = ∏_{k ∈ S} χ(z - x_k)` and `sig S = σ_S = ∏_{k ∈ S} s_k`.

Proved (all of the pointwise claims of (c), for admissible cores):
* `Kz_eq_ite`: `𝖪 = 16 · 𝟙{c₀, c₁ → z → a₀, a₁}`; `Kz_core`: `𝖪` vanishes at the core labels;
  `Kz_sq`: `𝖪² = 16 𝖪`; `Kz_mul_ell`: `𝖪 ℓ = 4 𝖪`; `Kz_nonneg`, `Kz_le`;
* `sum_ell_sq`: `E_z ℓ² = 4`, i.e. `∑_z ℓ(z, C)² = 4 |F|` (from `eq:two-root`, `sum_chi_mul_chi`);
* `Kz_expand`: `𝖪 = ∑_{S ⊆ {0,1,2,3}} σ_S ψ_S`; `Kstar_eq`: `𝖪_⋆` is the signed sum of the
  eleven higher stars (`card_higher = 11`);
* `Kz_affine`, `Adm_affine`: the square-affine maps `z ↦ αz + β`, `χ(α) = 1`, preserve `𝖪`, `ℓ`
  and admissibility (used for the column masses of `prop:l20-rectangular`(a)).

Not here: the operator identity `eq:l20-rank4-operator` of (c), which needs the features `V_k`,
`W_S` of `subsec:spec:actual-stars` relative to the half law; parts (a), (b) of the lemma.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The quadratic character of `F`, read in `ℝ`. -/
noncomputable def chi (y : F) : ℝ := (quadraticChar F y : ℝ)

theorem chi_zero : chi (0 : F) = 0 := by simp [chi]

theorem chi_of_ne {y : F} (hy : y ≠ 0) : chi y = 1 ∨ chi y = -1 := by
  rcases quadraticChar_dichotomy hy with h | h
  · left; simp [chi, h]
  · right; simp [chi, h]

theorem chi_mul (a b : F) : chi (a * b) = chi a * chi b := by
  simp only [chi, map_mul, Int.cast_mul]

theorem chi_neg (hm1 : quadraticChar F (-1) = -1) (y : F) : chi (-y) = -chi y := by
  have e : -y = (-1) * y := by ring
  rw [e, chi_mul]
  simp [chi, hm1]

theorem chi_sub_comm (hm1 : quadraticChar F (-1) = -1) (y y' : F) :
    chi (y - y') = -chi (y' - y) := by
  rw [← chi_neg hm1, neg_sub]

theorem chi_sq_of_ne {y : F} (hy : y ≠ 0) : chi y ^ 2 = 1 := by
  rcases chi_of_ne hy with h | h <;> rw [h] <;> norm_num

theorem chi_eq_one_iff (y : F) : chi y = 1 ↔ quadraticChar F y = 1 := by
  simp only [chi]
  exact_mod_cast Iff.rfl

/-- The core signs `s = (s₀, s₁, s₄, s₅) = (-1, -1, 1, 1)` (`lem:record:weighted-moment`). -/
def sgn (k : Fin 4) : ℝ := ![-1, -1, 1, 1] k

/-- `𝖪(z, C) = ∏_k (1 + s_k χ(z - C_k))`. -/
noncomputable def Kz (z : F) (C : Fin 4 → F) : ℝ := ∏ k, (1 + sgn k * chi (z - C k))

/-- `ℓ(z, C) = ∑_k s_k χ(z - C_k)`. -/
noncomputable def ell (z : F) (C : Fin 4 → F) : ℝ := ∑ k, sgn k * chi (z - C k)

/-- `ψ_S(z, C) = ∏_{k ∈ S} χ(z - C_k)`. -/
noncomputable def psi (S : Finset (Fin 4)) (z : F) (C : Fin 4 → F) : ℝ := ∏ k ∈ S, chi (z - C k)

/-- `σ_S = ∏_{k ∈ S} s_k`. -/
noncomputable def sig (S : Finset (Fin 4)) : ℝ := ∏ k ∈ S, sgn k

/-- `𝖪_⋆ = 𝖪 - 1 - ℓ`. -/
noncomputable def Kstar (z : F) (C : Fin 4 → F) : ℝ := Kz z C - 1 - ell z C

/-- The mean `\bar𝖪(C) = E_z 𝖪(z, C)` over the uniform label. -/
noncomputable def Kbar (C : Fin 4 → F) : ℝ := (∑ z, Kz z C) / Fintype.card F

/-- **Admissible cores**: distinct labels `a₀, a₁, c₀, c₁` with `a_i → c_j`, i.e.
`χ(c_j - a_i) = 1`. -/
def Adm (C : Fin 4 → F) : Prop :=
  Function.Injective C ∧ quadraticChar F (C 2 - C 0) = 1 ∧ quadraticChar F (C 3 - C 0) = 1 ∧
    quadraticChar F (C 2 - C 1) = 1 ∧ quadraticChar F (C 3 - C 1) = 1

instance (C : Fin 4 → F) : Decidable (Adm C) := by unfold Adm; infer_instance

theorem sgn_zero : sgn 0 = -1 := rfl
theorem sgn_one : sgn 1 = -1 := rfl
theorem sgn_two : sgn 2 = 1 := rfl
theorem sgn_three : sgn 3 = 1 := rfl

theorem Kz_four (z : F) (C : Fin 4 → F) :
    Kz z C = (1 - chi (z - C 0)) * (1 - chi (z - C 1)) * (1 + chi (z - C 2)) *
      (1 + chi (z - C 3)) := by
  rw [Kz, Fin.prod_univ_four, sgn_zero, sgn_one, sgn_two, sgn_three]
  ring

theorem ell_four (z : F) (C : Fin 4 → F) :
    ell z C = -chi (z - C 0) - chi (z - C 1) + chi (z - C 2) + chi (z - C 3) := by
  rw [ell, Fin.sum_univ_four, sgn_zero, sgn_one, sgn_two, sgn_three]
  ring

/-- The condition `c₀, c₁ → z → a₀, a₁`. -/
def Accepts (z : F) (C : Fin 4 → F) : Prop :=
  chi (z - C 0) = -1 ∧ chi (z - C 1) = -1 ∧ chi (z - C 2) = 1 ∧ chi (z - C 3) = 1

section Admissible

variable (hm1 : quadraticChar F (-1) = -1)
include hm1

theorem Kz_dichotomy {C : Fin 4 → F} (hC : Adm C) (z : F) :
    (Accepts z C ∧ Kz z C = 16) ∨ (¬ Accepts z C ∧ Kz z C = 0) := by
  obtain ⟨hinj, h20, h30, h21, h31⟩ := hC
  have c20 : chi (C 2 - C 0) = 1 := by rw [chi_eq_one_iff]; exact h20
  have c30 : chi (C 3 - C 0) = 1 := by rw [chi_eq_one_iff]; exact h30
  have c21 : chi (C 2 - C 1) = 1 := by rw [chi_eq_one_iff]; exact h21
  have c31 : chi (C 3 - C 1) = 1 := by rw [chi_eq_one_iff]; exact h31
  rw [Kz_four]
  unfold Accepts
  by_cases e0 : z = C 0
  · subst e0
    have : chi (C 0 - C 2) = -1 := by rw [chi_sub_comm hm1, c20]
    rw [this, sub_self, chi_zero]
    norm_num
  by_cases e1 : z = C 1
  · subst e1
    have : chi (C 1 - C 2) = -1 := by rw [chi_sub_comm hm1, c21]
    rw [this, sub_self, chi_zero]
    norm_num
  by_cases e2 : z = C 2
  · subst e2
    rw [c20, sub_self, chi_zero]
    norm_num
  by_cases e3 : z = C 3
  · subst e3
    rw [c30, sub_self, chi_zero]
    norm_num
  rcases chi_of_ne (sub_ne_zero.mpr e0) with h0 | h0 <;>
    rcases chi_of_ne (sub_ne_zero.mpr e1) with h1 | h1 <;>
    rcases chi_of_ne (sub_ne_zero.mpr e2) with h2 | h2 <;>
    rcases chi_of_ne (sub_ne_zero.mpr e3) with h3 | h3 <;>
    simp only [h0, h1, h2, h3] <;> norm_num

/-- **`lem:l20-star-matrix`(c)**: `𝖪 = 16 · 𝟙{c₀, c₁ → z → a₀, a₁}` on admissible cores. -/
theorem Kz_eq_ite {C : Fin 4 → F} (hC : Adm C) (z : F) [Decidable (Accepts z C)] :
    Kz z C = if Accepts z C then 16 else 0 := by
  rcases Kz_dichotomy hm1 hC z with ⟨h, h'⟩ | ⟨h, h'⟩
  · simp only [h, h', ↓reduceIte]
  · simp only [h, h', ↓reduceIte]

/-- **`𝖪` vanishes at the core labels** (`lem:l20-star-matrix`(c)). -/
theorem Kz_core {C : Fin 4 → F} (hC : Adm C) (k : Fin 4) : Kz (C k) C = 0 := by
  rcases Kz_dichotomy hm1 hC (C k) with ⟨h, -⟩ | ⟨-, h'⟩
  · exfalso
    obtain ⟨h0, h1, h2, h3⟩ := h
    fin_cases k <;> simp [sub_self, chi_zero] at h0 h1 h2 h3
  · exact h'

theorem Kz_cases {C : Fin 4 → F} (hC : Adm C) (z : F) :
    (Kz z C = 16 ∧ ell z C = 4) ∨ Kz z C = 0 := by
  rcases Kz_dichotomy hm1 hC z with ⟨h, h'⟩ | ⟨-, h'⟩
  · left
    refine ⟨h', ?_⟩
    obtain ⟨h0, h1, h2, h3⟩ := h
    rw [ell_four, h0, h1, h2, h3]
    norm_num
  · right; exact h'

/-- `𝖪² = 16 𝖪` (`lem:l20-star-matrix`(c)). -/
theorem Kz_sq {C : Fin 4 → F} (hC : Adm C) (z : F) : Kz z C ^ 2 = 16 * Kz z C := by
  rcases Kz_cases hm1 hC z with ⟨h, -⟩ | h <;> rw [h] <;> norm_num

/-- `𝖪 ℓ = 4 𝖪` (`lem:l20-star-matrix`(c)). -/
theorem Kz_mul_ell {C : Fin 4 → F} (hC : Adm C) (z : F) : Kz z C * ell z C = 4 * Kz z C := by
  rcases Kz_cases hm1 hC z with ⟨h, h'⟩ | h
  · rw [h, h']; norm_num
  · rw [h]; norm_num

theorem Kz_nonneg {C : Fin 4 → F} (hC : Adm C) (z : F) : 0 ≤ Kz z C := by
  rcases Kz_cases hm1 hC z with ⟨h, -⟩ | h <;> rw [h]
  norm_num

theorem Kz_le {C : Fin 4 → F} (hC : Adm C) (z : F) : Kz z C ≤ 16 := by
  rcases Kz_cases hm1 hC z with ⟨h, -⟩ | h <;> rw [h]
  norm_num

/-- `∑_z 𝖪² = 16 ∑_z 𝖪`. -/
theorem sum_Kz_sq {C : Fin 4 → F} (hC : Adm C) : ∑ z, Kz z C ^ 2 = 16 * ∑ z, Kz z C := by
  rw [mul_sum]
  exact sum_congr rfl fun z _ => Kz_sq hm1 hC z

end Admissible

/-! ## The star expansion -/

/-- **The star expansion** `𝖪 = ∑_{S ⊆ {0,1,2,3}} σ_S ψ_S` (`lem:l20-star-matrix`(c)). -/
theorem Kz_expand (z : F) (C : Fin 4 → F) :
    Kz z C = ∑ S : Finset (Fin 4), sig S * psi S z C := by
  rw [Kz, prod_one_add, powerset_univ]
  refine sum_congr rfl fun S _ => ?_
  rw [sig, psi, ← prod_mul_distrib]

/-- The eleven higher supports: the subsets of `{0,1,2,3}` with at least two elements. -/
def higher : Finset (Finset (Fin 4)) := univ.filter fun S => 2 ≤ S.card

theorem card_higher : higher.card = 11 := by decide

theorem lower_eq : (univ.filter fun S : Finset (Fin 4) => ¬ 2 ≤ S.card) =
    {∅, {0}, {1}, {2}, {3}} := by decide

/-- **`𝖪_⋆` is the signed sum of the eleven higher stars** `∑_{|S| ≥ 2} σ_S ψ_S`
(`lem:l20-star-matrix`(c)). -/
theorem Kstar_eq (z : F) (C : Fin 4 → F) :
    Kstar z C = ∑ S ∈ higher, sig S * psi S z C := by
  rw [Kstar, Kz_expand, ← sum_filter_add_sum_filter_not univ (fun S : Finset (Fin 4) => 2 ≤ S.card),
    lower_eq, ell_four]
  simp only [higher]
  rw [sum_insert (by decide), sum_insert (by decide), sum_insert (by decide),
    sum_insert (by decide), sum_singleton]
  simp only [sig, psi, prod_empty, prod_singleton, sgn]
  simp
  ring

/-! ## `E_z ℓ² = 4` -/

/-- **The two-root identity** in the form `∑_z χ(z - y) χ(z - y') = |F| 𝟙_{y = y'} - 1`
(`eq:two-root`). -/
theorem sum_chi_mul_chi (hF : ringChar F ≠ 2) (y y' : F) :
    ∑ z, chi (z - y) * chi (z - y') = if y = y' then (Fintype.card F : ℝ) - 1 else -1 := by
  by_cases h : y = y'
  · subst h
    simp only [↓reduceIte]
    have e : ∀ z, chi (z - y) * chi (z - y) = 1 - if z = y then 1 else 0 := by
      intro z
      by_cases hz : z = y
      · subst hz; simp [chi_zero]
      · simp only [hz, ↓reduceIte, sub_zero]
        rw [← sq, chi_sq_of_ne (sub_ne_zero.mpr hz)]
    rw [sum_congr rfl fun z _ => e z, sum_sub_distrib, sum_ite_eq' univ y (fun _ => (1 : ℝ))]
    simp
  · simp only [h, ↓reduceIte]
    have e : ∀ z, chi (z - y) * chi (z - y') =
        ((quadraticChar F (∏ a ∈ ({y, y'} : Finset F), (z - a)) : ℤ) : ℝ) := by
      intro z
      rw [prod_pair h, ← chi_mul]
      rfl
    rw [sum_congr rfl fun z _ => e z, ← Int.cast_sum]
    have := Sarkozy.Labellings.two_root hF h
    unfold Sarkozy.Labellings.rootSum at this
    rw [this]
    simp

/-- **`E_z ℓ² = 4`** (`lem:l20-star-matrix`(c)): for four distinct core labels,
`∑_z ℓ(z, C)² = 4 |F|`, by `eq:two-root` and `∑_k s_k = 0`. -/
theorem sum_ell_sq (hF : ringChar F ≠ 2) {C : Fin 4 → F} (hC : Function.Injective C) :
    ∑ z, ell z C ^ 2 = 4 * Fintype.card F := by
  have e : ∀ z, ell z C ^ 2 = ∑ k, ∑ k', sgn k * sgn k' * (chi (z - C k) * chi (z - C k')) := by
    intro z
    rw [ell, sq, sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun k' _ => ?_
    ring
  rw [sum_congr rfl fun z _ => e z, sum_comm]
  have e2 : ∀ k : Fin 4, ∑ z, ∑ k', sgn k * sgn k' * (chi (z - C k) * chi (z - C k')) =
      ∑ k', sgn k * sgn k' * (if k = k' then (Fintype.card F : ℝ) - 1 else -1) := by
    intro k
    rw [sum_comm]
    refine sum_congr rfl fun k' _ => ?_
    rw [← mul_sum, sum_chi_mul_chi hF]
    congr 2
    exact propext hC.eq_iff
  rw [sum_congr rfl fun k _ => e2 k]
  simp only [Fin.sum_univ_four, sgn]
  simp
  ring

/-! ## Square-affine invariance -/

/-- The square-affine map `z ↦ αz + β` on a core. -/
def affCore (α β : F) (C : Fin 4 → F) : Fin 4 → F := fun k => α * C k + β

theorem chi_affine {α : F} (hα : quadraticChar F α = 1) (β z w : F) :
    chi (α * z + β - (α * w + β)) = chi (z - w) := by
  have e : α * z + β - (α * w + β) = α * (z - w) := by ring
  rw [e, chi_mul]
  simp [chi, hα]

/-- **The square-affine maps preserve `𝖪`**: `𝖪(αz + β, αC + β) = 𝖪(z, C)` for `χ(α) = 1`. -/
theorem Kz_affine {α : F} (hα : quadraticChar F α = 1) (β z : F) (C : Fin 4 → F) :
    Kz (α * z + β) (affCore α β C) = Kz z C := by
  simp only [Kz, affCore, chi_affine hα]

theorem ell_affine {α : F} (hα : quadraticChar F α = 1) (β z : F) (C : Fin 4 → F) :
    ell (α * z + β) (affCore α β C) = ell z C := by
  simp only [ell, affCore, chi_affine hα]

theorem ne_zero_of_chi {α : F} (hα : quadraticChar F α = 1) : α ≠ 0 := by
  rintro rfl
  simp at hα

/-- **The square-affine maps preserve admissibility.** -/
theorem Adm_affine {α : F} (hα : quadraticChar F α = 1) (β : F) {C : Fin 4 → F} (hC : Adm C) :
    Adm (affCore α β C) := by
  have hα0 := ne_zero_of_chi hα
  obtain ⟨hinj, h20, h30, h21, h31⟩ := hC
  have key : ∀ i j, quadraticChar F (affCore α β C j - affCore α β C i) =
      quadraticChar F (C j - C i) := by
    intro i j
    have e : affCore α β C j - affCore α β C i = α * (C j - C i) := by simp only [affCore]; ring
    rw [e, map_mul, hα, one_mul]
  refine ⟨?_, by rw [key]; exact h20, by rw [key]; exact h30, by rw [key]; exact h21,
    by rw [key]; exact h31⟩
  intro i j hij
  apply hinj
  simp only [affCore] at hij
  exact mul_left_cancel₀ hα0 (add_right_cancel hij)

end Sarkozy.L20Cap

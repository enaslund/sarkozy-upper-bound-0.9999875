module

public import Sarkozy.NormBoundsPaper2.Constructor

@[expose] public section

/-!
# The matching laws on triples at one prime (NB3)

`paper/sections/21_middle_records.tex`, `subsec:record:e_side`, "The empty half law": "Let `H_E` be
the set of all halves, `|H_E| = p(p − 1)(p − 2)`, and `ν_E` its uniform law"; and
`lem:record:e-law`(a): "The kernel `K₁ = (1 + 𝖢 − δ_𝖢)(1 + 𝖣 − δ_𝖣)/z₁` is the density of a …
probability measure on `H_E × H_E` whose two half marginals both equal `ν_E`. It is `4/z₁` times
the indicator of the strict edges `x₁ → y₀` and `x₀ → y₁` … Fix a half `x`. … the pairs with
`x₁ → y₀` and `x₀ → y₁` number `((p − 1)/2)² − k_p = (p² − 3p + 4)/4`, the coincident ones being
the `k_p` common out-neighbours of `x₀` and `x₁` (`lem:paley-triple`(a)) … the column sums are one
by the same count with common in-neighbours."

A half of a matching record at one prime is a triple `((x₀, x₁), x₂)` of labels.

* `ind3`, `sum_ind3_fib`, `sum_ind3`: the injective triples, `p(p − 1)(p − 2)` of them;
  `m3 p = ν_E`, their uniform law (`sum_m3`);
* `rd`, `cmT`, `tw`: the coupling matrix of a law of labellings read at two triples of vertices,
  and its row and column sums (`cmT_row`, `cmT_col`);
* **`tw_match`**: V1's `E` law (six injective labels, `K^E_0`) read at one layer is `ν_E`
  (every bijection of `𝔽_p` preserves it and the injective triples are one orbit);
* `asm`, `P3`, **`P3_eq`**: `K₁` (`MiddleComparison.eLaw`) read at the two layers is
  `good x y / |eSet|`, `good x y = [x, y injective][x₁ → y₀][x₀ → y₁]`;
* **`row_good`**, **`col_good`**: the fibre counts `(p − 2)(p² − 3p + 4)/4` (`card_common_out`,
  `card_common_in`); **`eSet_card`**; **`P3_coupling`**: both half marginals of `K₁` are `ν_E`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper (p_gt_one)
open Sarkozy.NormBoundsPaper2 (off sum_off)

/-! ## Injective triples -/

section Triples

variable {X : Type} [Fintype X] [DecidableEq X]

/-- An injective triple `((x₀, x₁), x₂)`. -/
def Inj3 (x : (X × X) × X) : Prop := x.1.1 ≠ x.1.2 ∧ x.2 ≠ x.1.1 ∧ x.2 ≠ x.1.2

instance (x : (X × X) × X) : Decidable (Inj3 x) := by unfold Inj3; infer_instance

/-- The indicator of the injective triples. -/
def ind3 (x : (X × X) × X) : ℝ := if Inj3 x then 1 else 0

omit [Fintype X] in
theorem ind3_nonneg (x : (X × X) × X) : 0 ≤ ind3 x := by unfold ind3; split_ifs <;> norm_num

omit [Fintype X] in
theorem ind3_mul_self (x : (X × X) × X) : ind3 x * ind3 x = ind3 x := by
  unfold ind3; split_ifs <;> norm_num

omit [Fintype X] in
theorem ind3_le_one (x : (X × X) × X) : ind3 x ≤ 1 := by unfold ind3; split_ifs <;> norm_num

omit [Fintype X] in
theorem ind3_fib (a : X × X) (c : X) (ha : a.1 ≠ a.2) :
    ind3 (a, c) = 1 - (if c = a.1 then 1 else 0) - (if c = a.2 then 1 else 0) := by
  unfold ind3 Inj3
  split_ifs <;> simp_all

omit [Fintype X] in
theorem ind3_diag (a : X × X) (c : X) (ha : a.1 = a.2) : ind3 (a, c) = 0 := by
  unfold ind3 Inj3; simp [ha]

/-- The fibre of a pair: `p − 2` completions of an ordered distinct pair. -/
theorem sum_ind3_fib (a : X × X) :
    ∑ c, ind3 (a, c) = off a * ((Fintype.card X : ℝ) - 2) := by
  by_cases ha : a.1 = a.2
  · simp [ind3_diag a _ ha, off, ha]
  · simp only [ind3_fib a _ ha, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one,
      sum_ite_eq', mem_univ, ↓reduceIte, off, ha]
    ring

end Triples

/-! ## Reading a law at two triples -/

section Reading

variable {W : Type} [Fintype W] [DecidableEq W] {F : Type} [Fintype F] [DecidableEq F]

/-- The triple of a labelling at the vertices `u`. -/
def rd (z : W → F) (u : Fin 3 → W) : (F × F) × F := ((z (u 0), z (u 1)), z (u 2))

/-- The coupling matrix of a law of labellings read at the triples `u` and `v`. -/
noncomputable def cmT (μ : FiniteLaw (W → F)) (u v : Fin 3 → W) :
    Matrix ((F × F) × F) ((F × F) × F) ℝ :=
  fun x y => ∑ z, μ.weight z * (if rd z u = x ∧ rd z v = y then 1 else 0)

/-- The law of the triple at `u`. -/
noncomputable def tw (μ : FiniteLaw (W → F)) (u : Fin 3 → W) (x : (F × F) × F) : ℝ :=
  ∑ z, μ.weight z * (if rd z u = x then 1 else 0)

theorem cmT_nonneg (μ : FiniteLaw (W → F)) (u v : Fin 3 → W) (x y : (F × F) × F) :
    0 ≤ cmT μ u v x y :=
  sum_nonneg fun z _ => mul_nonneg (μ.nonneg z) (by split_ifs <;> norm_num)

theorem cmT_row (μ : FiniteLaw (W → F)) (u v : Fin 3 → W) (x : (F × F) × F) :
    ∑ y, cmT μ u v x y = tw μ u x := by
  unfold cmT tw
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum]
  congr 1
  by_cases hx : rd z u = x
  · simp [hx]
  · simp [hx]

theorem cmT_col (μ : FiniteLaw (W → F)) (u v : Fin 3 → W) (y : (F × F) × F) :
    ∑ x, cmT μ u v x y = tw μ v y := by
  unfold cmT tw
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum]
  congr 1
  by_cases hy : rd z v = y
  · simp [hy]
  · simp [hy]

theorem sum_tw (μ : FiniteLaw (W → F)) (u : Fin 3 → W) : ∑ x, tw μ u x = 1 := by
  unfold tw
  rw [sum_comm]
  have e : ∀ z : W → F, ∑ x, μ.weight z * (if rd z u = x then (1 : ℝ) else 0) = μ.weight z := by
    intro z
    rw [← mul_sum]
    simp
  simp only [e]
  exact μ.total

end Reading

/-! ## One prime -/

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem sum_ind3 :
    ∑ x : (ZMod p × ZMod p) × ZMod p, ind3 x = (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_ind3_fib, ZMod.card, ← sum_mul, sum_off]

/-- **`ν_E`**: the uniform law on the injective triples. -/
noncomputable def m3 (p : ℕ) [Fact p.Prime] (x : (ZMod p × ZMod p) × ZMod p) : ℝ :=
  ind3 x / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2))

omit [Fact p.Prime] in
theorem M3_pos (hp : 3 ≤ p) : 0 < (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) := by
  have : (3 : ℝ) ≤ p := by exact_mod_cast hp
  have h1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  positivity

theorem m3_nonneg (hp : 3 ≤ p) (x : (ZMod p × ZMod p) × ZMod p) : 0 ≤ m3 p x :=
  div_nonneg (ind3_nonneg x) (M3_pos hp).le

theorem sum_m3 (hp : 3 ≤ p) : ∑ x, m3 p x = 1 := by
  unfold m3
  rw [← sum_div, sum_ind3, div_self (M3_pos hp).ne']

/-! ### V1's `E` law read at one layer -/

variable (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)

/-- The three vertices of layer `ℓ`. -/
def lay (ℓ : Fin 2) : Fin 3 → Fin 3 × Fin 2 := fun k => (k, ℓ)

/-- A permutation of the labels, on triples. -/
def pmap (σ : Equiv.Perm (ZMod p)) (x : (ZMod p × ZMod p) × ZMod p) :
    (ZMod p × ZMod p) × ZMod p :=
  ((σ x.1.1, σ x.1.2), σ x.2)

theorem tw_match_perm (σ : Equiv.Perm (ZMod p)) (ℓ : Fin 2) (x : (ZMod p × ZMod p) × ZMod p) :
    tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) (pmap σ x) =
      tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) x := by
  unfold tw
  have hmem : ∀ z : Fin 3 × Fin 2 → ZMod p,
      (fun w => σ (z w)) ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) ↔
        z ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) := by
    intro z
    rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨fun x hx w hw hxw => h1 x hx w hw (congrArg σ hxw),
        fun e he => absurd he (Finset.notMem_empty _)⟩
    · rintro ⟨h1, -⟩
      exact ⟨fun x hx w hw hxw => h1 x hx w hw (σ.injective hxw),
        fun e he => absurd he (Finset.notMem_empty _)⟩
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ => σ) _ _ fun z => ?_).symm
  change _ = (graphLaw (matchGraph (Fin 2)) hne).weight (fun w => σ (z w)) *
    (if rd (fun w => σ (z w)) (lay ℓ) = pmap σ x then (1 : ℝ) else 0)
  have e : rd (fun w => σ (z w)) (lay ℓ) = pmap σ x ↔ rd z (lay ℓ) = x := by
    simp only [rd, pmap, Prod.ext_iff, σ.injective.eq_iff]
  refine congrArg₂ (· * ·) ?_ (if_congr e rfl rfl).symm
  unfold graphLaw
  simp only [hmem]

theorem tw_match_support {ℓ : Fin 2} {x : (ZMod p × ZMod p) × ZMod p}
    (h : tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) x ≠ 0) : Inj3 x := by
  obtain ⟨z, -, hz⟩ := exists_ne_zero_of_sum_ne_zero h
  have hw : (graphLaw (matchGraph (Fin 2)) hne).weight z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
  have hc : rd z (lay ℓ) = x := by
    by_contra hc
    exact hz (by rw [ite_eq_right hc, mul_zero])
  have hinj := (graphLaw_support (matchGraph (Fin 2)) hne hw).1
  have d : ∀ u v : Fin 3 × Fin 2, u ≠ v → z u ≠ z v := fun u v huv e =>
    huv (hinj u (mem_univ _) v (mem_univ _) e)
  subst hc
  refine ⟨d _ _ ?_, d _ _ ?_, d _ _ ?_⟩ <;> simp [lay]

/-- `0, 1, 2` are distinct labels. -/
theorem t0_inj (hp : 3 ≤ p) :
    Function.Injective (![(0 : ZMod p), 1, 2] : Fin 3 → ZMod p) := by
  have hval : ∀ k : Fin 3, (![(0 : ZMod p), 1, 2] : Fin 3 → ZMod p) k = ((k.val : ℕ) : ZMod p) := by
    intro k
    fin_cases k <;> simp
  intro i j hij
  rw [hval, hval, ZMod.natCast_eq_natCast_iff'] at hij
  rw [Nat.mod_eq_of_lt (by omega : i.val < p), Nat.mod_eq_of_lt (by omega : j.val < p)] at hij
  exact Fin.ext hij

theorem vec3_inj {X : Type} {a b c : X} (h : a ≠ b ∧ c ≠ a ∧ c ≠ b) :
    Function.Injective (![a, b, c] : Fin 3 → X) := by
  obtain ⟨h1, h2, h3⟩ := h
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all [eq_comm]

theorem tw_match_const (hp : 3 ≤ p) (ℓ : Fin 2) {x : (ZMod p × ZMod p) × ZMod p} (hx : Inj3 x) :
    tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) x =
      tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) ((0, 1), 2) := by
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ (t0_inj hp) (vec3_inj hx)
  have e0 : σ 0 = x.1.1 := hσ 0
  have e1 : σ 1 = x.1.2 := hσ 1
  have e2 : σ 2 = x.2 := hσ 2
  have := tw_match_perm hne σ ℓ ((0, 1), 2)
  simp only [pmap, e0, e1, e2] at this
  exact this

/-- **V1's `E` law read at one layer is `ν_E`**, the uniform law on the injective triples. -/
theorem tw_match (hp : 3 ≤ p) (ℓ : Fin 2) (x : (ZMod p × ZMod p) × ZMod p) :
    tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) x = m3 p x := by
  set κ := tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) ((0, 1), 2)
  have hform : ∀ x, tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ) x = κ * ind3 x := by
    intro x
    unfold ind3
    by_cases hx : Inj3 x
    · simp only [hx, ↓reduceIte, mul_one]
      exact tw_match_const hne hp ℓ hx
    · rw [ite_eq_right_iff.mpr (fun h => absurd h hx), mul_zero]
      by_contra h0
      exact hx (tw_match_support hne h0)
  have hs := sum_tw (graphLaw (matchGraph (Fin 2)) hne) (lay ℓ)
  simp only [hform, ← mul_sum, sum_ind3] at hs
  have hM := M3_pos (p := p) hp
  have hκ : κ = 1 / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2)) := by
    rw [eq_div_iff hM.ne']
    exact hs
  rw [hform, hκ, m3]
  ring

end Prime

end Sarkozy.NormBoundsPaper3

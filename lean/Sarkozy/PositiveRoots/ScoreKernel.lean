module

public import Sarkozy.PartV.PositiveRoot
public import Sarkozy.PositiveRoots.Moments

@[expose] public section

/-!
# The scores as kernels at the two cuts (`lem:positive-root-properties`(a), (c))

`paper/sections/20b_positive_roots.tex`, `lem:positive-root-properties` and the paragraphs
"The scores as kernels" (chamber cut) and "The two components" (layer cut). The scores are V1's
`PartV.rootScore p j x = r ∑_z χ(∏_{v ∈ {j,j+3}×{0,1}} (z − x_v))`.

* `rootScore_eq_pairScore`: `H_j(x) = r ∑_z ψ_a(z)ψ_c(z)` with `a = (x_{j,0}, x_{j,1})` and
  `c = (x_{j+3,0}, x_{j+3,1})` the two pairs of the base pair (`Moments.pairScore`);
* `abs_rootScore_le` (**`lem:positive-root-properties`(a)**, the bound): under Weil's bound
  (`Labellings.WeilBound`, H1, through `thm:weil`(b) = `Labellings.weil_even`), if the four labels
  of the base pair are distinct then `|H_j| ≤ 2 + r`; and `rootScore_mem` (`H_j ∈ rℤ`);
* **`lem:positive-root-properties`(c)**:
  - `basePair_reflect`: the reflection `u ↦ 5 − u` of `ϑ₀` maps the base pair `{0,3}` to `{2,5}`,
    fixes `{1,4}` and maps `{2,5}` to `{0,3}`, so it exchanges `H₀`, `H₂` and fixes `H₁`;
  - `rootScore_joinChamber`: at `ϑ₀`, with plus half `(a, b, c)` on the objects `0, 1, 2` and the
    reflected half `(a', b', c')` on the objects `5, 4, 3` (`joinChamber`), the scores pair `a`
    with `c'`, `b` with `b'` and `c` with `a'`: `H_j = H(x_j, x'_{2−j})` (`chamberScore`);
  - `chamberScore_swap`: the transposition of the halves permutes the scores by `j ↦ 2 − j` (the
    hypothesis `hσ` of `Chamber.root_chamber`);
  - `basePair_components`, `rootScore_joinLayer`: at `ι` (plus half = layer `0`, `joinLayer`) the
    base pair `{j, j+3}` has one base in each component (`j` and `j + 3` have different parities),
    and `H_j = r⟨f_j(x), f_j(x')⟩` with `f_j(x)(z) = χ(z − x_j)χ(z − x_{j+3})` (`layerScore`);
* `layerScore_psd`, `layerScore_sq_psd`: at `ι` each score, and its pointwise square, is a
  positive semidefinite (Gram) kernel — the positivity of the base term `(1⊗1)∘Υ` in the proof of
  `prop:root-layer`.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.L20Cap Sarkozy.PartV

/-! ## The score of a base pair as a product of two pair rows -/

section Score

variable {p : ℕ} [Fact p.Prime]

theorem chi_eq (y : ZMod p) : chi y = ((quadraticChar (ZMod p) y : ℤ) : ℝ) := rfl

/-- The four vertices of a base pair, in a fixed order. -/
theorem basePair_eq (j : Fin 3) :
    basePair j = {((j.val : ZMod 6), 0), ((j.val : ZMod 6), 1), ((j.val : ZMod 6) + 3, 0),
      ((j.val : ZMod 6) + 3, 1)} := rfl

theorem basePair_distinct : ∀ j : Fin 3,
    ((j.val : ZMod 6), (0 : Fin 2)) ∉ ({((j.val : ZMod 6), 1), ((j.val : ZMod 6) + 3, 0),
      ((j.val : ZMod 6) + 3, 1)} : Finset (ZMod 6 × Fin 2)) ∧
    ((j.val : ZMod 6), (1 : Fin 2)) ∉ ({((j.val : ZMod 6) + 3, 0), ((j.val : ZMod 6) + 3, 1)} :
      Finset (ZMod 6 × Fin 2)) ∧
    ((j.val : ZMod 6) + 3, (0 : Fin 2)) ∉
      ({((j.val : ZMod 6) + 3, 1)} : Finset (ZMod 6 × Fin 2)) := by
  decide

/-- The product over the base pair, factor by factor. -/
theorem prod_basePair (j : Fin 3) (g : ZMod 6 × Fin 2 → ZMod p) :
    ∏ v ∈ basePair j, g v = g ((j.val : ZMod 6), 0) * g ((j.val : ZMod 6), 1) *
      (g ((j.val : ZMod 6) + 3, 0) * g ((j.val : ZMod 6) + 3, 1)) := by
  obtain ⟨h1, h2, h3⟩ := basePair_distinct j
  rw [basePair_eq, prod_insert h1, prod_insert h2, prod_insert h3, prod_singleton]
  ring

/-- **The score as a product of two pair rows**: `H_j(x) = r ∑_z ψ_a(z)ψ_c(z)`, with
`a = (x_{j,0}, x_{j,1})`, `c = (x_{j+3,0}, x_{j+3,1})` and `ψ_y(z) = χ(z − y₀)χ(z − y₁)`. -/
theorem rootScore_eq_pairScore (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) :
    rootScore p j x = pairScore (x ((j.val : ZMod 6), 0), x ((j.val : ZMod 6), 1))
      (x ((j.val : ZMod 6) + 3, 0), x ((j.val : ZMod 6) + 3, 1)) := by
  unfold rootScore rootTrace pairScore
  rw [ZMod.card]
  congr 1
  push_cast
  refine sum_congr rfl fun z _ => ?_
  rw [prod_basePair j (fun v => z - x v)]
  simp only [map_mul, Int.cast_mul, psiP, chi_eq]

/-- **`H_j ∈ rℤ`** (`lem:positive-root-properties`(a)). -/
theorem rootScore_mem (j : Fin 3) (x : ZMod 6 × Fin 2 → ZMod p) :
    ∃ n : ℤ, rootScore p j x = n / Real.sqrt p :=
  ⟨rootTrace p j x, rfl⟩

/-- **`|H_j| ≤ 2 + r`** (`lem:positive-root-properties`(a)): if the four labels of the base pair
`{j, j+3}` are distinct, Weil's bound in the form `thm:weil`(b) (`|W_S + 1| ≤ 2√p` for `|S| = 4`)
gives `|H_j| ≤ 2 + 1/√p`. -/
theorem abs_rootScore_le (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (j : Fin 3)
    (x : ZMod 6 × Fin 2 → ZMod p) (hx : Set.InjOn x (basePair j : Set (ZMod 6 × Fin 2))) :
    |rootScore p j x| ≤ 2 + 1 / Real.sqrt p := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr (by linarith)
  set S := (basePair j).image x with hS
  have hcard : S.card = 4 := by
    have h4 : ∀ j : Fin 3, (basePair j).card = 4 := by decide
    rw [hS, card_image_of_injOn hx, h4 j]
  have htr : rootTrace p j x = Sarkozy.Labellings.rootSum S := by
    unfold rootTrace Sarkozy.Labellings.rootSum
    refine sum_congr rfl fun z _ => ?_
    rw [hS, prod_image (fun a ha b hb hab => hx ha hb hab)]
  have hb := Sarkozy.Labellings.weil_even hW (S := S) (by rw [hcard]; decide)
    (by rw [hcard]; norm_num)
  rw [hcard, ZMod.card] at hb
  have h1 : |(rootTrace p j x : ℝ)| ≤ 2 * Real.sqrt p + 1 := by
    rw [htr]
    have := abs_sub_abs_le_abs_sub ((Sarkozy.Labellings.rootSum S : ℝ)) (-1)
    rw [sub_neg_eq_add] at this
    norm_num at this hb
    linarith
  unfold rootScore
  rw [abs_div, abs_of_pos hs, div_le_iff₀ hs]
  have : (2 + 1 / Real.sqrt p) * Real.sqrt p = 2 * Real.sqrt p + 1 := by field_simp
  linarith

end Score

/-! ## The chamber cut `ϑ₀` -/

/-- **The reflection of `ϑ₀` on the base pairs** (`lem:positive-root-properties`(c)): `u ↦ 5 − u`
maps `{0,3}` to `{2,5}`, fixes `{1,4}` and maps `{2,5}` to `{0,3}`: it exchanges `H₀` and `H₂`
and fixes `H₁`. -/
theorem basePair_reflect (j : Fin 3) :
    (basePair j).image (fun v => (5 - v.1, v.2)) = basePair (Fin.rev j) := by
  revert j
  decide

/-- The pair of a vertex object of the joined labelling at `ϑ₀`: objects `0, 1, 2` carry the plus
half `(a, b, c)`, objects `5, 4, 3` the reflected half `(a', b', c')`. -/
def chamberPair {F : Type*} (x x' : Fin 3 → F × F) (u : ZMod 6) : F × F :=
  match u.val with
  | 0 => x 0
  | 1 => x 1
  | 2 => x 2
  | 3 => x' 2
  | 4 => x' 1
  | _ => x' 0

/-- **The joined labelling at `ϑ₀`** of a plus half `x` and a reflected half `x'` (each half is
three ordered pairs, one per object, the pair being the labels of the two layers). -/
def joinChamber {F : Type*} (x x' : Fin 3 → F × F) (v : ZMod 6 × Fin 2) : F :=
  if v.2 = 0 then (chamberPair x x' v.1).1 else (chamberPair x x' v.1).2

/-- **The chamber scores** `H_j(x, x') = H(x_j, x'_{2−j})`: `H₀` pairs `a` with `c'`, `H₁` pairs
`b` with `b'`, `H₂` pairs `c` with `a'`. -/
noncomputable def chamberScore {F : Type*} [Field F] [Fintype F] [DecidableEq F] (j : Fin 3)
    (x x' : Fin 3 → F × F) : ℝ :=
  pairScore (x j) (x' (Fin.rev j))

/-- **`lem:positive-root-properties`(c) at `ϑ₀`**: the score `H_j` of the joined labelling is
the chamber score, `H_j(x ⊔ x') = H(x_j, x'_{2−j})`. -/
theorem rootScore_joinChamber {p : ℕ} [Fact p.Prime] (j : Fin 3) (x x' : Fin 3 → ZMod p × ZMod p) :
    rootScore p j (joinChamber x x') = chamberScore j x x' := by
  rw [rootScore_eq_pairScore]
  unfold chamberScore
  fin_cases j <;> rfl

theorem pairScore_comm {F : Type*} [Field F] [Fintype F] [DecidableEq F] (y y' : F × F) :
    pairScore y y' = pairScore y' y := by
  unfold pairScore
  congr 1
  exact sum_congr rfl fun z _ => mul_comm _ _

/-- **The transposition permutes the chamber scores** by `j ↦ 2 − j`:
`H_j(x', x) = H_{2−j}(x, x')` (the hypothesis `hσ` of `root_chamber`). -/
theorem chamberScore_swap {F : Type*} [Field F] [Fintype F] [DecidableEq F] (j : Fin 3)
    (x x' : Fin 3 → F × F) : chamberScore j x' x = chamberScore (Fin.rev j) x x' := by
  unfold chamberScore
  rw [Fin.rev_rev, pairScore_comm]

/-! ## The layer cut `ι` -/

/-- **`lem:positive-root-properties`(c) at `ι`**: the base pair `{j, j+3}` has one base in each
component of `G_{L,2}` (the bases `j` and `j + 3` have different parities). -/
theorem basePair_components : ∀ j : Fin 3,
    ((j.val : ZMod 6).val % 2 = 0 ∧ ((j.val : ZMod 6) + 3).val % 2 = 1) ∨
      ((j.val : ZMod 6).val % 2 = 1 ∧ ((j.val : ZMod 6) + 3).val % 2 = 0) := by
  decide

/-- **The joined labelling at `ι`**: layer `0` from the plus half `x`, layer `1` from `x'`. -/
def joinLayer {F : Type*} (x x' : ZMod 6 → F) (v : ZMod 6 × Fin 2) : F :=
  if v.2 = 0 then x v.1 else x' v.1

/-- The selected-label row of a layer half, `f_j(x)(z) = χ(z − x_j)χ(z − x_{j+3})`. -/
noncomputable def layerRow {F : Type*} [Field F] [Fintype F] [DecidableEq F] (j : Fin 3)
    (x : ZMod 6 → F)
    (z : F) : ℝ :=
  chi (z - x (j.val : ZMod 6)) * chi (z - x ((j.val : ZMod 6) + 3))

/-- **The layer score** `H_j(x, x') = r⟨f_j(x), f_j(x')⟩ = r ∑_z f_j(x)(z) f_j(x')(z)`. -/
noncomputable def layerScore {F : Type*} [Field F] [Fintype F] [DecidableEq F] (j : Fin 3)
    (x x' : ZMod 6 → F) :
    ℝ :=
  (∑ z, layerRow j x z * layerRow j x' z) / Real.sqrt (Fintype.card F)

/-- **At `ι` the score is the layer score**: `H_j(x ⊔ x') = r⟨f_j(x), f_j(x')⟩`, each half
contributing its two selected labels (one per component, at the bases `j` and `j + 3`). -/
theorem rootScore_joinLayer {p : ℕ} [Fact p.Prime] (j : Fin 3) (x x' : ZMod 6 → ZMod p) :
    rootScore p j (joinLayer x x') = layerScore j x x' := by
  rw [rootScore_eq_pairScore]
  unfold pairScore layerScore layerRow psiP joinLayer
  simp only [↓reduceIte, one_ne_zero]
  congr 1
  exact sum_congr rfl fun z _ => by ring

/-- **The layer score is a positive semidefinite kernel**: `∑_{x,x'} c(x)c(x')H_j(x,x') ≥ 0`
(proof of `prop:root-layer`: "`𝖧` is a positive Gram kernel"). -/
theorem layerScore_psd {F : Type*} [Field F] [Fintype F] [DecidableEq F] (j : Fin 3) {ι : Type*}
    (s : Finset ι)
    (x : ι → ZMod 6 → F) (c : ι → ℝ) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, c a * c b * layerScore j (x a) (x b) := by
  have e : ∑ a ∈ s, ∑ b ∈ s, c a * c b * layerScore j (x a) (x b) =
      (∑ z, (∑ a ∈ s, c a * layerRow j (x a) z) ^ 2) / Real.sqrt (Fintype.card F) := by
    unfold layerScore
    simp only [mul_div_assoc', ← Finset.sum_div]
    congr 1
    calc ∑ a ∈ s, ∑ b ∈ s, c a * c b * ∑ z, layerRow j (x a) z * layerRow j (x b) z
        = ∑ a ∈ s, ∑ b ∈ s, ∑ z, c a * layerRow j (x a) z * (c b * layerRow j (x b) z) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z _ => by ring
      _ = ∑ a ∈ s, ∑ z, ∑ b ∈ s, c a * layerRow j (x a) z * (c b * layerRow j (x b) z) :=
          Finset.sum_congr rfl fun a _ => Finset.sum_comm
      _ = ∑ z, ∑ a ∈ s, ∑ b ∈ s, c a * layerRow j (x a) z * (c b * layerRow j (x b) z) :=
          Finset.sum_comm
      _ = _ := by simp only [sq, Finset.sum_mul_sum]
  rw [e]
  positivity

/-- **The pointwise square of the layer score is positive semidefinite** (Schur:
`H_j² = q ∑_{z,z'} (f_j(x)(z)f_j(x)(z'))(f_j(x')(z)f_j(x')(z'))`). -/
theorem layerScore_sq_psd {F : Type*} [Field F] [Fintype F] [DecidableEq F] (j : Fin 3)
    {ι : Type*} (s : Finset ι)
    (x : ι → ZMod 6 → F) (c : ι → ℝ) :
    0 ≤ ∑ a ∈ s, ∑ b ∈ s, c a * c b * layerScore j (x a) (x b) ^ 2 := by
  have e : ∑ a ∈ s, ∑ b ∈ s, c a * c b * layerScore j (x a) (x b) ^ 2 =
      (∑ z, ∑ z', (∑ a ∈ s, c a * (layerRow j (x a) z * layerRow j (x a) z')) ^ 2) /
        Real.sqrt (Fintype.card F) ^ 2 := by
    unfold layerScore
    simp only [div_pow, mul_div_assoc', ← Finset.sum_div]
    congr 1
    have h1 : ∀ a b, (∑ z, layerRow j (x a) z * layerRow j (x b) z) ^ 2 =
        ∑ z, ∑ z', (layerRow j (x a) z * layerRow j (x a) z') *
          (layerRow j (x b) z * layerRow j (x b) z') := by
      intro a b
      rw [sq, Finset.sum_mul_sum]
      exact sum_congr rfl fun z _ => sum_congr rfl fun z' _ => by ring
    simp only [h1]
    set g : ι → F → F → ℝ := fun a z z' => layerRow j (x a) z * layerRow j (x a) z'
    calc ∑ a ∈ s, ∑ b ∈ s, c a * c b * ∑ z, ∑ z', g a z z' * g b z z'
        = ∑ a ∈ s, ∑ b ∈ s, ∑ z, ∑ z', c a * g a z z' * (c b * g b z z') :=
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun z _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun z' _ => by ring
      _ = ∑ a ∈ s, ∑ z, ∑ z', ∑ b ∈ s, c a * g a z z' * (c b * g b z z') :=
          Finset.sum_congr rfl fun a _ => by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ z, ∑ z', ∑ a ∈ s, ∑ b ∈ s, c a * g a z z' * (c b * g b z z') := by
            rw [Finset.sum_comm]
            exact Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = _ := by simp only [sq, Finset.sum_mul_sum]; rfl
  rw [e]
  positivity

end Sarkozy.PositiveRoots

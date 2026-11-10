module

public import Sarkozy.SignedComponents.Components

@[expose] public section

/-!
# The fold components of `lem:signed-components` as `FoldPrimeComponents`, and on a block

`paper/sections/21_middle_records.tex`, `lem:signed-components`(a),(d), `def:record:mixture`(b)–(d).

* **`primeComponents`**: at a prime `p ≡ 3 (4)`, `p ≥ 19`, for `t ∈ [0, 1]` and constants
  `M_c ≥ 0` with the defect bound `|α|, |β| ≤ M_c` of `lem:signed-components`(c) (a hypothesis),
  the per-prime fold components of `Sarkozy.SignedComponents.Fold`:
  - for `F₁` (`j = 0`), the repaired laws `P_{uv}` of `Sarkozy.SignedComponents.Components`, as
    two-layer labellings `(x, y)`;
  - for `F₂` (`j = 1`), their reflected transposes `K^ς(x, y) = K(ς y, ς x)`
    (`def:record:mixture`(d), with `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)`);

  with the three properties: support on the query edge (`x₁ → y₀` for `F₁`; `x₂ → y₁` for `F₂`,
  since `𝖢^ς = χ(y₁ - x₂)`), translation invariance, and both half marginals `m₀` (for `F₂` by
  `g₀ ∘ ς = g₀`, `m0_refl`).
* `primeComponentsMax`: the same with `M = ∑|α| + ∑|β|`, with no hypothesis (non-vacuity of
  `FoldPrimeComponents`; it is not the paper's `M_c`).
* `blockComponents`, `blockComponentsMax`: the components at every prime of a middle block
  (`FoldComponents`), hence, with `Sarkozy.SignedComponents.Data.ofFold`, B7's
  `ReplacementData`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

section Field

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- The swap-reflection `(x, y) ↦ (ς y, ς x)` of a pair of halves. -/
def swapRefl (p : (Fin 3 → F) × (Fin 3 → F)) : (Fin 3 → F) × (Fin 3 → F) := (refl p.2, refl p.1)

omit [Fintype F] [DecidableEq F] in
theorem swapRefl_swapRefl (p : (Fin 3 → F) × (Fin 3 → F)) : swapRefl (swapRefl p) = p := by
  simp [swapRefl, refl_refl]

/-- The swap-reflection as an equivalence. -/
def swapReflEquiv : ((Fin 3 → F) × (Fin 3 → F)) ≃ ((Fin 3 → F) × (Fin 3 → F)) :=
  ⟨swapRefl, swapRefl, swapRefl_swapRefl, swapRefl_swapRefl⟩

/-- **The placement of the components of `F_{j+1}`**: `(x, y)` for `F₁`, the reflected
transpose `(ς y, ς x)` for `F₂`. -/
def placeEquiv (j : Fin 2) : ((Fin 3 → F) × (Fin 3 → F)) ≃ (Fin 3 × Fin 2 → F) :=
  if j = 0 then pairEquiv else swapReflEquiv.trans pairEquiv

omit [Fintype F] [DecidableEq F] in
theorem placeEquiv_zero_symm (y : Fin 3 × Fin 2 → F) :
    (placeEquiv 0).symm y = (lay y 0, lay y 1) := rfl

omit [Fintype F] [DecidableEq F] in
theorem placeEquiv_one_symm (y : Fin 3 × Fin 2 → F) :
    (placeEquiv 1).symm y = (refl (lay y 1), refl (lay y 0)) := rfl

omit [Fintype F] [DecidableEq F] in
theorem placeEquiv_zero (q : (Fin 3 → F) × (Fin 3 → F)) : placeEquiv 0 q = toY q := rfl

omit [Fintype F] [DecidableEq F] in
theorem placeEquiv_one (q : (Fin 3 → F) × (Fin 3 → F)) :
    placeEquiv 1 q = toY (refl q.2, refl q.1) := rfl

omit [Fintype F] [DecidableEq F] in
/-- The query difference of the reflected transpose. -/
theorem swap_query (y : Fin 3 × Fin 2 → F) :
    refl (lay y 0) 0 - refl (lay y 1) 1 = y (1, 1) - y (2, 0) := by
  simp only [refl, lay]
  rw [show Fin.rev (0 : Fin 3) = 2 from rfl, show Fin.rev (1 : Fin 3) = 1 from rfl]
  ring

theorem expect_fst_of_row {A : Type} [Fintype A] (μ : FiniteLaw (A × A)) (m : FiniteLaw A)
    (h : ∀ x, ∑ y, μ.weight (x, y) = m.weight x) (g : A → ℝ) :
    μ.expect (fun p => g p.1) = m.expect g := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  change ∑ y, μ.weight (x, y) * g x = m.weight x * g x
  rw [← sum_mul, h]

theorem expect_snd_of_col {A : Type} [Fintype A] (μ : FiniteLaw (A × A)) (m : FiniteLaw A)
    (h : ∀ y, ∑ x, μ.weight (x, y) = m.weight y) (g : A → ℝ) :
    μ.expect (fun p => g p.2) = m.expect g := by
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type_right]
  refine sum_congr rfl fun y _ => ?_
  change ∑ x, μ.weight (x, y) * g y = m.weight y * g y
  rw [← sum_mul, h]

theorem m0_expect_refl (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (g : (Fin 3 → F) → ℝ) : (m0 hF).expect (fun x => g (refl x)) = (m0 hF).expect g := by
  unfold FiniteLaw.expect
  refine Fintype.sum_equiv reflEquiv _ _ fun x => ?_
  change _ = (m0 hF).weight (refl x) * g (refl x)
  rw [m0_refl]

end Field

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem ringChar_zmod_ne_two (h3 : p % 4 = 3) : ringChar (ZMod p) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  omega

theorem card_zmod_mod (h3 : p % 4 = 3) : Fintype.card (ZMod p) % 4 = 3 := by
  rw [ZMod.card]
  exact h3

theorem card_zmod_ge (h19 : 19 ≤ p) : 19 ≤ Fintype.card (ZMod p) := by
  rw [ZMod.card]
  exact h19

variable (h3 : p % 4 = 3) (h19 : 19 ≤ p)
  (hF : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

/-- The repair data of the component `c` at the prime `p`. -/
noncomputable abbrev repairAt (c : Fin 3) : RepairInput (Fin 3 → ZMod p) :=
  repairInput (ringChar_zmod_ne_two h3) (card_zmod_mod h3) (card_zmod_ge h19) hF ht0 ht1 c

/-- The repaired law `P_{uv}` of the component `c` at the prime `p`, with the constant `M`. -/
noncomputable def compLaw (M : Fin 3 → ℝ) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c, (repairAt h3 h19 hF ht0 ht1 c).DefectBound (M c)) (c : Fin 3) :
    FiniteLaw ((Fin 3 → ZMod p) × (Fin 3 → ZMod p)) :=
  (repairAt h3 h19 hF ht0 ht1 c).repairLaw (hM0 c) (hM c) fun x => repair_Jβ x

/-- **The per-prime fold components of the paper** (`lem:signed-components`(a),(d)), for constants
`M_c ≥ 0` satisfying the defect bound of `lem:signed-components`(c). -/
noncomputable def primeComponents (M : Fin 3 → ℝ) (hM0 : ∀ c, 0 ≤ M c)
    (hM : ∀ c, (repairAt h3 h19 hF ht0 ht1 c).DefectBound (M c)) : FoldPrimeComponents p hF where
  law j c := (compLaw h3 h19 hF ht0 ht1 M hM0 hM c).map (placeEquiv j)
  query j c y hy := by
    rw [map_equiv_weight] at hy
    have hq := repair_query hy
    fin_cases j
    · simp only [Fin.zero_eta, placeEquiv_zero_symm] at hq
      exact hq
    · simp only [Fin.mk_one, placeEquiv_one_symm] at hq
      rw [swap_query] at hq
      exact hq
  translate j c a y := by
    rw [map_equiv_weight, map_equiv_weight]
    change (repairAt h3 h19 hF ht0 ht1 c).repair (M c) ((placeEquiv j).symm _) =
      (repairAt h3 h19 hF ht0 ht1 c).repair (M c) ((placeEquiv j).symm y)
    fin_cases j
    · simp only [Fin.zero_eta]
      exact repair_translate (M c) a ((placeEquiv 0).symm y)
    · simp only [Fin.mk_one]
      have e : (placeEquiv 1).symm (fun w => y w + a) = ptrans (-a) ((placeEquiv 1).symm y) := by
        rw [placeEquiv_one_symm, placeEquiv_one_symm]
        ext o
        · change -(y (Fin.rev o, 1) + a) = -y (Fin.rev o, 1) + -a
          exact neg_add _ _
        · change -(y (Fin.rev o, 0) + a) = -y (Fin.rev o, 0) + -a
          exact neg_add _ _
      rw [e]
      exact repair_translate (M c) (-a) _
  half j c ℓ g := by
    rw [FiniteLaw.expect_map]
    refine Eq.trans ?_ (m0_expect hF g)
    have hrow := (repairAt h3 h19 hF ht0 ht1 c).repair_row (hM0 c) (fun x => repair_Jβ x)
    have hcol := (repairAt h3 h19 hF ht0 ht1 c).repair_col (hM0 c) (fun y => repair_Jα y)
    fin_cases j <;> fin_cases ℓ
    · exact expect_fst_of_row _ (m0 hF) hrow g
    · exact expect_snd_of_col _ (m0 hF) hcol g
    · rw [← m0_expect_refl hF g]
      exact expect_snd_of_col _ (m0 hF) hcol (fun x => g (refl x))
    · rw [← m0_expect_refl hF g]
      exact expect_fst_of_row _ (m0 hF) hrow (fun x => g (refl x))

/-- **The per-prime fold components without any hypothesis**, with `M = ∑|α| + ∑|β|`
(non-vacuity of `FoldPrimeComponents`; not the paper's `M_c`). -/
noncomputable def primeComponentsMax : FoldPrimeComponents p hF :=
  primeComponents h3 h19 hF ht0 ht1 (fun c => (repairAt h3 h19 hF ht0 ht1 c).Mmax)
    (fun c => (repairAt h3 h19 hF ht0 ht1 c).Mmax_nonneg)
    (fun c => (repairAt h3 h19 hF ht0 ht1 c).defectBound_Mmax)

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i) (hne : MiddleNonempty pr) {t : ℝ}
  (ht0 : 0 ≤ t) (ht1 : t ≤ 1)

/-- **The fold components of a middle block** (`def:record:mixture`(b)), for constants `M_{c,p}`
with the defect bound of `lem:signed-components`(c) at every prime. -/
noncomputable def blockComponents (M : ι → Fin 3 → ℝ) (hM0 : ∀ i c, 0 ≤ M i c)
    (hM : ∀ i c, (repairAt (h3 i) (h19 i) (hne.F2 i) ht0 ht1 c).DefectBound (M i c)) :
    FoldComponents pr hne :=
  fun i => primeComponents (h3 i) (h19 i) (hne.F2 i) ht0 ht1 (M i) (hM0 i) (hM i)

/-- The fold components of a middle block without any hypothesis (`M = ∑|α| + ∑|β|`). -/
noncomputable def blockComponentsMax : FoldComponents pr hne :=
  fun i => primeComponentsMax (h3 i) (h19 i) (hne.F2 i) ht0 ht1

end Block

end Sarkozy.SignedComponents

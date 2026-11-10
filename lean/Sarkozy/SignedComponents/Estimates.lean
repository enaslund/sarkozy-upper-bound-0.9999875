module

public import Sarkozy.SignedComponents.Paper

@[expose] public section

/-!
# The defect bound from the estimates of `lem:signed-components`(b) and `lem:old-f-law`(a)

`paper/sections/21_middle_records.tex`, `lem:signed-components`(b),(c), `lem:old-f-law`(a).

The paper proves `|α|, |β| ≤ M_c = (2η_c + (1 + η_c) e₀)/(h_c (1 - e₀))`, `h_c = 1 - η_c`, from
three estimates:
* (b) the row and column means of `U_{uv}` under `ν_F` are within `η_c` of `1`
  (`|E_{y'} U(x, y') - 1| ≤ q R_row ≤ η_c`, likewise for the columns), and `|z_{uv} - 1| ≤ η_c`;
* `lem:old-f-law`(a): the density `g₀ = m₀/ν_F` satisfies `|g₀ - 1| ≤ e₀` on `H_F`.

This file proves that implication exactly, with the paper's constant:

* `Hset`, `Hcard` (`H_F` and `|H_F|`), `rowMean`, `colMean`, `zMean` (the means of `U_{uv}` under
  `ν_F`, `ν_F ⊗ ν_F`), `g0` (`m₀ |H_F|`, which is `g₀` on `H_F`); `m0_support` (`m₀` lives on
  `H_F`);
* **`SignedEstimates hF t c η e`**: the estimates (b) with `η` and `|g₀ - 1| ≤ e` (hypotheses);
* `Mc η e`: the paper's `M_c`; `alpha_eq`, `beta_eq` (`α = 1 - E_y U/(z g₀)`);
  `abs_one_sub_le_Mc` (the real inequality);
* **`defectBound_of_estimates`**: `|α|, |β| ≤ M_c` on the support of `m₀`;
* **`DefectConstants.ofEstimates`**: the defect constants of a middle block of the paper with
  `M = M_c(η_p, e_p)`, from the estimates at every prime and component.

So the remaining input of the fold records is `SignedEstimates`: the two estimates the paper
proves from `lem:paley-triple`(b), the Weil bound `thm:weil`(a) (for the rows) and the formula for
`g₀` of `lem:old-f-law`(a).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

section Field

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `H_F` as a finite set. -/
noncomputable def Hset : Finset (Fin 3 → F) := univ.filter HF

/-- `|H_F|`. -/
noncomputable def Hcard : ℝ := ((Hset (F := F)).card : ℝ)

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

/-- **`m₀` lives on `H_F`.** -/
theorem m0_support {x : Fin 3 → F} (hx : (m0 hF).weight x ≠ 0) : HF x := by
  change (∑ y, if lay y 0 = x then (K0 hF).weight y else 0) ≠ 0 at hx
  obtain ⟨y, -, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hx
  split_ifs at hy with hyx
  · subst hyx
    have hfeas := graphLaw_support (foldGraph (Fin 2)) hF hy
    refine ⟨fun a b hab => ?_, ?_⟩
    · have := hfeas.1 (a, 0) (mem_univ _) (b, 0) (mem_univ _) hab
      simpa using this
    · exact hfeas.2 ((0, 0), (2, 0)) ((mem_foldGraph (Fin 2) _).mpr ⟨rfl, rfl⟩) (mem_univ _)
        (mem_univ _)
  · exact absurd rfl hy

include hF in
theorem Hcard_pos : 0 < Hcard (F := F) := by
  obtain ⟨y, hy⟩ := id hF
  have hK : (K0 hF).weight y ≠ 0 := by
    change (if y ∈ injLabellings F (foldGraph (Fin 2)) then
      1 / ((injLabellings F (foldGraph (Fin 2))).card : ℝ) else 0) ≠ 0
    simp only [hy, ↓reduceIte]
    have : (0 : ℝ) < (injLabellings F (foldGraph (Fin 2))).card := by
      exact_mod_cast card_pos.mpr ⟨y, hy⟩
    positivity
  have hm : (m0 hF).weight (lay y 0) ≠ 0 :=
    (lt_of_lt_of_le (lt_of_le_of_ne ((K0 hF).nonneg y) (Ne.symm hK))
      (le_map_weight (K0 hF) (fun y => lay y 0) y)).ne'
  have hH : lay y 0 ∈ Hset (F := F) := mem_filter.mpr ⟨mem_univ _, m0_support hF hm⟩
  unfold Hcard
  exact_mod_cast card_pos.mpr ⟨_, hH⟩

/-- The row mean `E_{y ∼ ν_F} U(x, y)` (for `x ∈ H_F`). -/
noncomputable def rowMean (t u v : ℝ) (x : Fin 3 → F) : ℝ :=
  (∑ y, Ukernel t u v (x, y)) / Hcard (F := F)

/-- The column mean `E_{x ∼ ν_F} U(x, y)` (for `y ∈ H_F`). -/
noncomputable def colMean (t u v : ℝ) (y : Fin 3 → F) : ℝ :=
  (∑ x, Ukernel t u v (x, y)) / Hcard (F := F)

/-- `z_{uv} = E_{ν_F ⊗ ν_F} U_{uv}`. -/
noncomputable def zMean (t u v : ℝ) : ℝ := (∑ p, Ukernel (F := F) t u v p) / Hcard (F := F) ^ 2

/-- `m₀ |H_F|`, which is the density `g₀ = m₀/ν_F` on `H_F`. -/
noncomputable def g0 (x : Fin 3 → F) : ℝ := (m0 hF).weight x * Hcard (F := F)

/-- **The estimates of `lem:signed-components`(b) and `lem:old-f-law`(a)** for the component `c`
(hypotheses): the row and column means of `U_{uv}` and `z_{uv}` are within `η` of `1`, and
`|g₀ - 1| ≤ e` on `H_F`. -/
structure SignedEstimates (t : ℝ) (c : Fin 3) (η e : ℝ) : Prop where
  row : ∀ x : Fin 3 → F, HF x → |rowMean t (compU c) (compV c) x - 1| ≤ η
  col : ∀ y : Fin 3 → F, HF y → |colMean t (compU c) (compV c) y - 1| ≤ η
  z : |zMean (F := F) t (compU c) (compV c) - 1| ≤ η
  g : ∀ x : Fin 3 → F, HF x → |g0 hF x - 1| ≤ e

end Field

/-- **The paper's constant** `M_c = (2η + (1 + η) e)/((1 - η)(1 - e))` (`lem:signed-components`(c),
with `η = η_c`, `e = e₀`, `h_c = 1 - η_c`). -/
noncomputable def Mc (η e : ℝ) : ℝ := (2 * η + (1 + η) * e) / ((1 - η) * (1 - e))

theorem Mc_nonneg {η e : ℝ} (hη : 0 ≤ η) (hη1 : η < 1) (he : 0 ≤ e) (he1 : e < 1) :
    0 ≤ Mc η e := by
  unfold Mc
  have h1 : 0 < 1 - η := by linarith
  have h2 : 0 < 1 - e := by linarith
  positivity

/-- **The real inequality**: `|1 - ρ/(ζ g)| ≤ M_c` when `ρ, ζ` are within `η` of `1` and `g` within
`e`. -/
theorem abs_one_sub_le_Mc {η e ρ ζ g : ℝ} (hη : 0 ≤ η) (hη1 : η < 1) (he : 0 ≤ e) (he1 : e < 1)
    (hρ : |ρ - 1| ≤ η) (hζ : |ζ - 1| ≤ η) (hg : |g - 1| ≤ e) : |1 - ρ / (ζ * g)| ≤ Mc η e := by
  have hρ' := abs_le.mp hρ
  have hζ' := abs_le.mp hζ
  have hg' := abs_le.mp hg
  have hz0 : 0 < ζ := by linarith
  have hg0 : 0 < g := by linarith
  have hzg : 0 < ζ * g := mul_pos hz0 hg0
  have hD : (1 - η) * (1 - e) ≤ ζ * g :=
    mul_le_mul (by linarith) (by linarith) (by linarith) hz0.le
  have hD0 : 0 < (1 - η) * (1 - e) := mul_pos (by linarith) (by linarith)
  have e1 : 1 - ρ / (ζ * g) = (ζ * g - ρ) / (ζ * g) := by field_simp
  have hN : |ζ * g - ρ| ≤ 2 * η + (1 + η) * e := by
    have e2 : ζ * g - ρ = ζ * (g - 1) + (ζ - 1) - (ρ - 1) := by ring
    rw [e2]
    have h1 : |ζ * (g - 1)| ≤ (1 + η) * e := by
      rw [abs_mul, abs_of_pos hz0]
      exact mul_le_mul (by linarith) hg (abs_nonneg _) (by linarith)
    calc |ζ * (g - 1) + (ζ - 1) - (ρ - 1)| ≤ |ζ * (g - 1) + (ζ - 1)| + |ρ - 1| := abs_sub _ _
      _ ≤ |ζ * (g - 1)| + |ζ - 1| + |ρ - 1| := by gcongr; exact abs_add_le _ _
      _ ≤ (1 + η) * e + η + η := by linarith
      _ = 2 * η + (1 + η) * e := by ring
  rw [e1, abs_div, abs_of_pos hzg]
  unfold Mc
  calc |ζ * g - ρ| / (ζ * g) ≤ (2 * η + (1 + η) * e) / (ζ * g) :=
        div_le_div_of_nonneg_right hN hzg.le
    _ ≤ (2 * η + (1 + η) * e) / ((1 - η) * (1 - e)) :=
        div_le_div_of_nonneg_left (by nlinarith) hD0 hD

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
  {hR : ringChar F ≠ 2} {h3 : Fintype.card F % 4 = 3} {h19 : 19 ≤ Fintype.card F}
  {hF : (injLabellings F (foldGraph (Fin 2))).Nonempty} {t : ℝ} {ht0 : 0 ≤ t} {ht1 : t ≤ 1}
  {c : Fin 3}

theorem Z_eq : (repairInput hR h3 h19 hF ht0 ht1 c).Z =
    zMean (F := F) t (compU c) (compV c) * Hcard (F := F) ^ 2 := by
  unfold zMean
  have := (Hcard_pos (F := F) hF).ne'
  field_simp
  rfl

/-- `α(x) = 1 - E_y U(x, y)/(z g₀(x))` on the support of `m₀`. -/
theorem alpha_eq {x : Fin 3 → F} (hx : 0 < (m0 hF).weight x) :
    (repairInput hR h3 h19 hF ht0 ht1 c).α x =
      1 - rowMean t (compU c) (compV c) x / (zMean (F := F) t (compU c) (compV c) * g0 hF x) := by
  have hH := (Hcard_pos (F := F) hF).ne'
  have hZ : (repairInput hR h3 h19 hF ht0 ht1 c).Z ≠ 0 :=
    (repairInput hR h3 h19 hF ht0 ht1 c).W_pos.ne'
  unfold RepairInput.α RepairInput.a rowMean g0
  rw [← sum_div, Z_eq]
  change 1 - (∑ y, Ukernel t (compU c) (compV c) (x, y)) / _ / (m0 hF).weight x = _
  have hz : zMean (F := F) t (compU c) (compV c) ≠ 0 := by
    intro h0
    rw [Z_eq, h0, zero_mul] at hZ
    exact hZ rfl
  field_simp

/-- `β(y) = 1 - E_x U(x, y)/(z g₀(y))` on the support of `m₀`. -/
theorem beta_eq {y : Fin 3 → F} (hy : 0 < (m0 hF).weight y) :
    (repairInput hR h3 h19 hF ht0 ht1 c).β y =
      1 - colMean t (compU c) (compV c) y / (zMean (F := F) t (compU c) (compV c) * g0 hF y) := by
  have hH := (Hcard_pos (F := F) hF).ne'
  have hZ : (repairInput hR h3 h19 hF ht0 ht1 c).Z ≠ 0 :=
    (repairInput hR h3 h19 hF ht0 ht1 c).W_pos.ne'
  unfold RepairInput.β RepairInput.b colMean g0
  rw [← sum_div, Z_eq]
  change 1 - (∑ x, Ukernel t (compU c) (compV c) (x, y)) / _ / (m0 hF).weight y = _
  have hz : zMean (F := F) t (compU c) (compV c) ≠ 0 := by
    intro h0
    rw [Z_eq, h0, zero_mul] at hZ
    exact hZ rfl
  field_simp

/-- **`lem:signed-components`(c)**: the estimates give `|α|, |β| ≤ M_c` on the support of `m₀`. -/
theorem defectBound_of_estimates {η e : ℝ} (hη : 0 ≤ η) (hη1 : η < 1) (he : 0 ≤ e) (he1 : e < 1)
    (E : SignedEstimates hF t c η e) :
    (repairInput hR h3 h19 hF ht0 ht1 c).DefectBound (Mc η e) := by
  intro x hx
  have hHx : HF x := m0_support hF hx.ne'
  refine ⟨?_, ?_⟩
  · rw [alpha_eq hx]
    exact abs_one_sub_le_Mc hη hη1 he he1 (E.row x hHx) E.z (E.g x hHx)
  · rw [beta_eq hx]
    exact abs_one_sub_le_Mc hη hη1 he he1 (E.col x hHx) E.z (E.g x hHx)

end Prime

/-! ## The paper's middle blocks -/

section Paper

open Sarkozy.FirstStagePaper Sarkozy.PartVLaws Sarkozy.CancellationSteps Sarkozy.BlockFrame

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

omit [Fintype B] [DecidableEq B] in
/-- **The defect constants of a middle block from the estimates** (`M = M_c(η_p, e_p)` at every
prime, the paper's choice), given `SignedEstimates` at every prime and component. -/
noncomputable def DefectConstants.ofEstimates (b : B)
    (hne : MiddleNonempty (blockPrimes blockOf b)) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (η e : {j : PaperJ0 // paperAtomMap blockOf j = .inr b} → ℝ) (hη : ∀ i, 0 ≤ η i)
    (hη1 : ∀ i, η i < 1) (he : ∀ i, 0 ≤ e i) (he1 : ∀ i, e i < 1)
    (E : ∀ i c, SignedEstimates (hne.F2 i) t c (η i) (e i)) : DefectConstants b hne ht0 ht1 where
  M i _ := Mc (η i) (e i)
  nonneg i _ := Mc_nonneg (hη i) (hη1 i) (he i) (he1 i)
  bound i c := defectBound_of_estimates (hη i) (hη1 i) (he i) (he1 i) (E i c)

end Paper

end Sarkozy.SignedComponents

module

public import Sarkozy.SignedComponents.Reference

@[expose] public section

/-!
# The positive components `P_{uv}` at one prime (`lem:signed-components`)

`paper/sections/21_middle_records.tex`, `lem:signed-components`, `def:record:mixture`(b),(d).

At one prime `p ≡ 3 (4)`, `p ≥ 19`, for `0 ≤ t ≤ 1` and `(u, v) ∈ {(1,1), (-1,1), (-1,-1)}`, the
paper puts, on pairs of halves `(x, y) ∈ H_F × H_F`,

  `U_{uv} = 2 · 1[x₁ → y₀] (1 + (1 - t)𝖡)(1 + u𝖣)(1 + v𝖠)`,
  `𝖡 = χ(x₂ - y₀)`, `𝖣 = χ(y₁ - x₀)`, `𝖠 = χ(y₂ - x₀)`,

normalizes `U_{uv} ν_F ⊗ ν_F` and repairs it to the half marginal `m₀` with the query coupling
`J_C = 2/(1 - q) · 1[x₁ → y₀]` (`lem:signed-components`(c),(d), `cor:markov-completion`). This file
constructs these components:

* `Ukernel t u v`: `U_{uv} · 1_{H_F} ⊗ 1_{H_F}` (the measure `U_{uv} ν_F ⊗ ν_F` up to the factor
  `|H_F|⁻²`, which the normalization removes); `Jker`: `J_C`;
* `Ukernel_nonneg`, `Ukernel_translate`, **`Ukernel_pos`** (an explicit pair with `U > 0`, so
  `z_{uv} > 0`), `Jker_row`, `Jker_col` (`J_C` has both marginals `m₀`: "`Pr(x₁ → y₀) = (1-q)/2`");
* **`repairInput`**: the data of the repair; `repair_Jβ`, `repair_Jα` (`J_C β = 0`, `J_C* α = 0`,
  from translation invariance: "`E_{m₀}[β | y₀] = 0`");
* `repair_query`: the repaired law charges only pairs with `x₁ → y₀`.

The per-prime fold components (`FoldPrimeComponents`) built from these, for `F₁` and for their
reflected transposes `F₂`, are in `Sarkozy.SignedComponents.PrimeComponents`.

Not formalized: the estimates (b),(c) of `lem:signed-components` (`|z_{uv} - 1| ≤ 10q`,
`|α|, |β| ≤ M_c`, which use `thm:weil`), the norm estimate of (d), and `G_p`-invariance beyond
translations.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedComponents

open Sarkozy.Labellings Sarkozy.PartV Sarkozy.TraceMixing

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "χ" => quadraticChar F

/-- The signs `u` of the components `P_{++}, P_{-+}, P_{--}`. -/
def compU : Fin 3 → ℤ := ![1, -1, -1]

/-- The signs `v` of the components `P_{++}, P_{-+}, P_{--}`. -/
def compV : Fin 3 → ℤ := ![1, 1, -1]

theorem compU_cases (c : Fin 3) : compU c = 1 ∨ compU c = -1 := by
  fin_cases c <;> simp [compU]

theorem compV_cases (c : Fin 3) : compV c = 1 ∨ compV c = -1 := by
  fin_cases c <;> simp [compV]

/-- **The kernel `U_{uv}` on `H_F × H_F`** (`lem:signed-components`), as a weight on pairs of
halves. -/
noncomputable def Ukernel (t u v : ℝ) (p : (Fin 3 → F) × (Fin 3 → F)) : ℝ :=
  (if HF p.1 ∧ HF p.2 then 1 else 0) *
    (2 * (if χ (p.2 0 - p.1 1) = 1 then 1 else 0) * (1 + (1 - t) * (χ (p.1 2 - p.2 0) : ℝ)) *
      (1 + u * (χ (p.2 1 - p.1 0) : ℝ)) * (1 + v * (χ (p.2 2 - p.1 0) : ℝ)))

/-- **The query coupling `J_C = 2/(1 - q) · 1[x₁ → y₀]`**, relative to `m₀ ⊗ m₀`. -/
noncomputable def Jker (p : (Fin 3 → F) × (Fin 3 → F)) : ℝ :=
  2 * (Fintype.card F : ℝ) / ((Fintype.card F : ℝ) - 1) * (if χ (p.2 0 - p.1 1) = 1 then 1 else 0)

theorem one_add_mul_chi_nonneg {s : ℝ} (hs : |s| ≤ 1) (a : F) : 0 ≤ 1 + s * (χ a : ℝ) := by
  have := abs_le.mp hs
  rcases chi_cases a with h | h | h <;> rw [h] <;> push_cast <;> linarith

theorem Ukernel_nonneg {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : Fin 3) (p) :
    0 ≤ Ukernel (F := F) t (compU c) (compV c) p := by
  have h1 : |1 - t| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
  have hu : |(compU c : ℝ)| ≤ 1 := by rcases compU_cases c with h | h <;> simp [h]
  have hv : |(compV c : ℝ)| ≤ 1 := by rcases compV_cases c with h | h <;> simp [h]
  unfold Ukernel
  refine mul_nonneg (by split_ifs <;> norm_num) ?_
  refine mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by split_ifs <;> norm_num))
    (one_add_mul_chi_nonneg h1 _)) (one_add_mul_chi_nonneg hu _)) (one_add_mul_chi_nonneg hv _)

/-- The diagonal translation of a pair of halves. -/
def ptrans (c : F) (p : (Fin 3 → F) × (Fin 3 → F)) : (Fin 3 → F) × (Fin 3 → F) :=
  (fun o => p.1 o + c, fun o => p.2 o + c)

theorem Ukernel_translate (t u v : ℝ) (c : F) (p) :
    Ukernel (F := F) t u v (ptrans c p) = Ukernel t u v p := by
  unfold Ukernel ptrans
  have e : ∀ a b : F, (a + c) - (b + c) = a - b := fun a b => by ring
  simp only [e, HF_translate]

theorem Jker_translate (c : F) (p) : Jker (F := F) (ptrans c p) = Jker p := by
  unfold Jker ptrans
  have e : ∀ a b : F, (a + c) - (b + c) = a - b := fun a b => by ring
  simp only [e]

theorem Jker_nonneg (h7 : 7 ≤ Fintype.card F) (p) : 0 ≤ Jker (F := F) p := by
  unfold Jker
  have : (1 : ℝ) < Fintype.card F := by exact_mod_cast (by omega : 1 < Fintype.card F)
  refine mul_nonneg (div_nonneg (by positivity) (by linarith)) (by split_ifs <;> norm_num)

/-- **`U_{uv}` charges some pair** (`z_{uv} > 0`): `x = (0, b, 1)`, `y = (1, 0, d)` with `b → 1`
and `1 → d`, `χ(d) = v`, where `𝖡 = 𝖣 = 0` and `𝖠 = v`. -/
theorem Ukernel_pos (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ Fintype.card F)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : Fin 3) :
    0 < ∑ p, Ukernel (F := F) t (compU c) (compV c) p := by
  have h01 : (0 : F) ≠ 1 := zero_ne_one
  obtain ⟨b, hb0, hb1⟩ := exists_sign_pair hR h7 h01 (σ := 1) (σ' := -1) (Or.inl rfl)
    (Or.inr rfl)
  rw [sub_zero] at hb0
  have hb1' : χ (1 - b) = 1 := by rw [chi_swap h3, hb1]; ring
  obtain ⟨d, hd1, hd0⟩ := exists_sign_pair hR h7 h01.symm (σ := 1) (σ' := compV c) (Or.inl rfl)
    (compV_cases c)
  rw [sub_zero] at hd0
  have hne : ∀ {a a' : F} {s : ℤ}, χ (a - a') = s → (s = 1 ∨ s = -1) → a ≠ a' := by
    intro a a' s h hs e
    rw [e, sub_self, quadraticChar_zero] at h
    rcases hs with rfl | rfl <;> simp at h
  have hb0' : b ≠ 0 := hne (a' := 0) (by rw [sub_zero]; exact hb0) (Or.inl rfl)
  have hb1n : b ≠ 1 := hne hb1 (Or.inr rfl)
  have hd1n : d ≠ 1 := hne hd1 (Or.inl rfl)
  have hd0n : d ≠ 0 := hne (a' := 0) (by rw [sub_zero]; exact hd0) (compV_cases c)
  let x : Fin 3 → F := ![0, b, 1]
  let y : Fin 3 → F := ![1, 0, d]
  have hx : HF x := ⟨injective_three hb0'.symm h01 hb1n, by simp [x, map_one]⟩
  have hy : HF y := ⟨injective_three h01.symm hd1n.symm hd0n.symm, by simp [y, hd1]⟩
  have hval : Ukernel (F := F) t (compU c) (compV c) (x, y) = 4 := by
    unfold Ukernel
    have hv2 : ((compV c : ℝ)) * (compV c : ℝ) = 1 := by
      rcases compV_cases c with h | h <;> simp [h]
    simp only [hx, hy, and_self, ↓reduceIte, one_mul]
    simp only [x, y, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, sub_self, quadraticChar_zero, sub_zero, hb1', hd0,
      ↓reduceIte, Int.cast_zero, mul_zero, add_zero, mul_one]
    rw [hv2]
    norm_num
  have hle : Ukernel (F := F) t (compU c) (compV c) (x, y) ≤
      ∑ p, Ukernel (F := F) t (compU c) (compV c) p := by
    exact single_le_sum (f := Ukernel t (compU c) (compV c))
      (fun p _ => Ukernel_nonneg ht0 ht1 c p) (mem_univ _)
  linarith

/-! ## The coupling `J_C` has both marginals `m₀` -/

omit [DecidableEq F] in
/-- **Averaging over translations**: for a translation-invariant `f`,
`∑_y g(y_o) f(y) = (∑_c g(c)) (∑_y f(y)) / q`. -/
theorem sum_coord_mul (f : (Fin 3 → F) → ℝ) (hf : ∀ c y, f (fun o => y o + c) = f y) (o : Fin 3)
    (g : F → ℝ) :
    ∑ y, g (y o) * f y = (∑ c, g c) * (∑ y, f y) / (Fintype.card F : ℝ) := by
  have hshift : ∀ c : F, ∑ y, g (y o + c) * f y = ∑ y, g (y o) * f y := by
    intro c
    refine Fintype.sum_equiv (trans (W := Fin 3) c) _ _ fun y => ?_
    change g (y o + c) * f y = g ((fun o => y o + c) o) * f (fun o => y o + c)
    rw [hf]
  have hq : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have key : (Fintype.card F : ℝ) * ∑ y, g (y o) * f y = (∑ c, g c) * ∑ y, f y := by
    have h1 : (Fintype.card F : ℝ) * ∑ y, g (y o) * f y = ∑ c : F, ∑ y, g (y o + c) * f y := by
      rw [sum_congr rfl fun c _ => hshift c, sum_const, card_univ, nsmul_eq_mul]
    rw [h1, sum_comm, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    rw [← sum_mul]
    congr 1
    exact Fintype.sum_equiv (Equiv.addLeft (y o)) _ _ fun c => by simp [add_comm]
  field_simp
  linarith

theorem sum_out_ind (hR : ringChar F ≠ 2) (a : F) :
    ∑ c : F, (if χ (c - a) = 1 then (1 : ℝ) else 0) = ((Fintype.card F : ℝ) - 1) / 2 := by
  rw [sum_boole]
  have h := card_out hR a
  have h' : (2 : ℝ) * ((univ.filter fun b => χ (b - a) = 1).card : ℝ) = Fintype.card F - 1 := by
    exact_mod_cast h
  linarith

theorem sum_in_ind (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (a : F) :
    ∑ c : F, (if χ (a - c) = 1 then (1 : ℝ) else 0) = ((Fintype.card F : ℝ) - 1) / 2 := by
  rw [sum_boole]
  have h := card_in hR h3 a
  have h' : (2 : ℝ) * ((univ.filter fun b => χ (a - b) = 1).card : ℝ) = Fintype.card F - 1 := by
    exact_mod_cast h
  linarith

variable (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)

theorem m0_sum_coord (o : Fin 3) (g : F → ℝ) :
    ∑ y, g (y o) * (m0 hF).weight y = (∑ c, g c) / (Fintype.card F : ℝ) := by
  rw [sum_coord_mul (fun y => (m0 hF).weight y) (fun c y => m0_translate hF c y) o g,
    (m0 hF).total, mul_one]

/-- **`J_C` has row marginal `m₀`**: `∑_y J_C(x, y) m₀(y) = 1`. -/
theorem Jker_row (hR : ringChar F ≠ 2) (h7 : 7 ≤ Fintype.card F) (x : Fin 3 → F) :
    ∑ y, Jker (x, y) * (m0 hF).weight y = 1 := by
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast (by omega : 1 < Fintype.card F)
  unfold Jker
  simp only [mul_assoc]
  rw [← mul_sum]
  have h := m0_sum_coord hF 0 (fun c => if χ (c - x 1) = 1 then (1 : ℝ) else 0)
  rw [h, sum_out_ind hR]
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  field_simp

/-- **`J_C` has column marginal `m₀`**: `∑_x J_C(x, y) m₀(x) = 1` (in-degrees, `p ≡ 3 (4)`). -/
theorem Jker_col (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ Fintype.card F)
    (y : Fin 3 → F) : ∑ x, Jker (x, y) * (m0 hF).weight x = 1 := by
  have hq : (1 : ℝ) < Fintype.card F := by exact_mod_cast (by omega : 1 < Fintype.card F)
  unfold Jker
  simp only [mul_assoc]
  rw [← mul_sum]
  have h := m0_sum_coord hF 1 (fun c => if χ (y 0 - c) = 1 then (1 : ℝ) else 0)
  rw [h, sum_in_ind hR h3]
  have hq1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hq0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  field_simp

/-! ## The repair data and its orthogonality relations -/

variable {hF}

/-- **The data of the repair of `U_{uv}`** (`lem:signed-components`(c),(d)). -/
noncomputable def repairInput (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h19 : 19 ≤ Fintype.card F) (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) (c : Fin 3) : RepairInput (Fin 3 → F) where
  m := m0 hF
  W := Ukernel t (compU c) (compV c)
  W_nonneg := Ukernel_nonneg ht0 ht1 c
  W_pos := Ukernel_pos hR h3 (by omega) ht0 ht1 c
  W_supp x y hW := by
    have hxy : HF x ∧ HF y := by
      by_contra hn
      apply hW
      unfold Ukernel
      simp only [hn, ↓reduceIte, zero_mul]
    exact ⟨m0_pos hF hR h3 h19 hxy.1, m0_pos hF hR h3 h19 hxy.2⟩
  J := Jker
  J_nonneg := Jker_nonneg (by omega)
  J_row := Jker_row hF hR (by omega)
  J_col := Jker_col hF hR h3 (by omega)

section RepairFacts

variable {hR : ringChar F ≠ 2} {h3 : Fintype.card F % 4 = 3} {h19 : 19 ≤ Fintype.card F}
  {t : ℝ} {ht0 : 0 ≤ t} {ht1 : t ≤ 1} {c : Fin 3}

theorem repairInput_a_translate (d : F) (x : Fin 3 → F) :
    (repairInput hR h3 h19 hF ht0 ht1 c).a (fun o => x o + d) =
      (repairInput hR h3 h19 hF ht0 ht1 c).a x := by
  unfold RepairInput.a
  refine (Fintype.sum_equiv (trans d) _ _ fun y => ?_).symm
  change Ukernel t (compU c) (compV c) (x, y) / _ =
    Ukernel t (compU c) (compV c) ((fun o => x o + d), trans d y) / _
  rw [← Ukernel_translate t (compU c) (compV c) d (x, y)]
  rfl

theorem repairInput_b_translate (d : F) (y : Fin 3 → F) :
    (repairInput hR h3 h19 hF ht0 ht1 c).b (fun o => y o + d) =
      (repairInput hR h3 h19 hF ht0 ht1 c).b y := by
  unfold RepairInput.b
  refine (Fintype.sum_equiv (trans d) _ _ fun x => ?_).symm
  change Ukernel t (compU c) (compV c) (x, y) / _ =
    Ukernel t (compU c) (compV c) (trans d x, (fun o => y o + d)) / _
  rw [← Ukernel_translate t (compU c) (compV c) d (x, y)]
  rfl

theorem repairInput_α_translate (d : F) (x : Fin 3 → F) :
    (repairInput hR h3 h19 hF ht0 ht1 c).α (fun o => x o + d) =
      (repairInput hR h3 h19 hF ht0 ht1 c).α x := by
  unfold RepairInput.α
  rw [repairInput_a_translate]
  change 1 - _ / (m0 hF).weight _ = 1 - _ / (m0 hF).weight _
  rw [m0_translate]

theorem repairInput_β_translate (d : F) (y : Fin 3 → F) :
    (repairInput hR h3 h19 hF ht0 ht1 c).β (fun o => y o + d) =
      (repairInput hR h3 h19 hF ht0 ht1 c).β y := by
  unfold RepairInput.β
  rw [repairInput_b_translate]
  change 1 - _ / (m0 hF).weight _ = 1 - _ / (m0 hF).weight _
  rw [m0_translate]

/-- **`J_C β = 0`** (`lem:signed-components`(c): "`E_{m₀}[β | y₀] = 0`"). -/
theorem repair_Jβ (x : Fin 3 → F) :
    ∑ y, (repairInput hR h3 h19 hF ht0 ht1 c).J (x, y) * (repairInput hR h3 h19 hF ht0 ht1 c).β y *
      (repairInput hR h3 h19 hF ht0 ht1 c).m.weight y = 0 := by
  set R := repairInput hR h3 h19 hF ht0 ht1 c
  have e : ∀ y, R.J (x, y) * R.β y * R.m.weight y = 2 * (Fintype.card F : ℝ) /
      ((Fintype.card F : ℝ) - 1) * ((if χ (y 0 - x 1) = 1 then 1 else 0) *
        (R.m.weight y - R.b y)) := by
    intro y
    rw [← R.m_mul_β]
    change Jker (x, y) * _ * _ = _
    unfold Jker
    ring
  simp only [e]
  rw [← mul_sum, sum_coord_mul (fun y => R.m.weight y - R.b y) (fun d y => by
    change (m0 hF).weight _ - R.b _ = (m0 hF).weight _ - R.b _
    rw [m0_translate, repairInput_b_translate]) 0 (fun c => if χ (c - x 1) = 1 then 1 else 0)]
  rw [sum_sub_distrib, R.m.total, R.sum_b]
  ring

/-- **`J_C* α = 0`**. -/
theorem repair_Jα (y : Fin 3 → F) :
    ∑ x, (repairInput hR h3 h19 hF ht0 ht1 c).J (x, y) * (repairInput hR h3 h19 hF ht0 ht1 c).α x *
      (repairInput hR h3 h19 hF ht0 ht1 c).m.weight x = 0 := by
  set R := repairInput hR h3 h19 hF ht0 ht1 c
  have e : ∀ x, R.J (x, y) * R.α x * R.m.weight x = 2 * (Fintype.card F : ℝ) /
      ((Fintype.card F : ℝ) - 1) * ((if χ (y 0 - x 1) = 1 then 1 else 0) *
        (R.m.weight x - R.a x)) := by
    intro x
    rw [← R.m_mul_α]
    change Jker (x, y) * _ * _ = _
    unfold Jker
    ring
  simp only [e]
  rw [← mul_sum, sum_coord_mul (fun x => R.m.weight x - R.a x) (fun d x => by
    change (m0 hF).weight _ - R.a _ = (m0 hF).weight _ - R.a _
    rw [m0_translate, repairInput_a_translate]) 1 (fun c => if χ (y 0 - c) = 1 then 1 else 0)]
  rw [sum_sub_distrib, R.m.total, R.sum_a]
  ring

/-- The repaired weight is translation invariant. -/
theorem repair_translate (M : ℝ) (d : F) (p : (Fin 3 → F) × (Fin 3 → F)) :
    (repairInput hR h3 h19 hF ht0 ht1 c).repair M (ptrans d p) =
      (repairInput hR h3 h19 hF ht0 ht1 c).repair M p := by
  unfold RepairInput.repair
  change (Ukernel t (compU c) (compV c) (ptrans d p) / _ + Jker (ptrans d p) *
    (_ + _ + 2 * M) * (m0 hF).weight _ * (m0 hF).weight _) / _ = (Ukernel t (compU c) (compV c) p
    / _ + Jker p * (_ + _ + 2 * M) * (m0 hF).weight _ * (m0 hF).weight _) / _
  rw [Ukernel_translate, Jker_translate]
  simp only [ptrans, repairInput_α_translate, repairInput_β_translate, m0_translate]

/-- The repaired law charges only pairs with the query edge `x₁ → y₀`. -/
theorem repair_query {M : ℝ} {p : (Fin 3 → F) × (Fin 3 → F)}
    (hp : (repairInput hR h3 h19 hF ht0 ht1 c).repair M p ≠ 0) : χ (p.2 0 - p.1 1) = 1 := by
  by_contra hn
  rcases (repairInput hR h3 h19 hF ht0 ht1 c).repair_support hp with h | h
  · apply h
    change Ukernel t (compU c) (compV c) p = 0
    unfold Ukernel
    simp only [hn, ↓reduceIte, mul_zero, zero_mul]
  · apply h
    change Jker p = 0
    unfold Jker
    simp only [hn, ↓reduceIte, mul_zero]

end RepairFacts

end Sarkozy.SignedComponents

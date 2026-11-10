module

public import Sarkozy.NormBoundsPaper2.MirrorAlgebra
public import Sarkozy.PartVRecords.MergeQueried

@[expose] public section

/-!
# The mirror-edge replacement at one prime (NB2)

`paper/sections/21_middle_records.tex`, `lem:merge-repair`, paragraph "The mirror law": "Write
`C = χ(y₀ − x₁)` and `H = χ(y₁ − x₀)`. On the injective source, `P^c_p` has density `(1 + C)(1 + H)`
relative to `D_p`. Transposition exchanges `C, H` with `−H, −C` … `Sym(P^c_p − D_p) = D_p CH`,
`Skew(P^c_p − D_p) = D_p (C + H)` … `‖D_p CH‖ ≤ (1/(p − 1) + τ)/z = s^G_p` … `‖D_p(C + H)‖ ≤
(γ^G_p + 2τ)/z = a^G_p`, `‖P^c_p − J‖ ≤ α^G_p := d_p + s^G_p + a^G_p`."

* **`mirC_eq`**: V3's mirror-edge law read at the two pairs is `srcC · (1 + C)(1 + H)`
  (`mirrorLaw_expect`, `mirror_count_total`); **`mirC_split`**, **`mirC_split_swap`**: the mirror
  identities `mirC = D + D(C + H) + D·CH`, `mirCᵀ = D − D(C + H) + D·CH`;
* **`symK_form_le`**: `|⟨u, D·CH v⟩| ≤ s^G_p ‖u‖ ‖v‖` (the two-edge kernel `two_chi_le` and the
  collision kernel `coll_form_le`);
* **`skwK_form_le`**: `|⟨u, D(C + H) v⟩| ≤ a^G_p ‖u‖ ‖v‖` on mean-zero functions (`chi_form_le`,
  `rows_cols_le`, `coll_form_le`);
* **`mir_centred`**: the centred norm of the mirror law is `≤ α^G_p`;
* `mirC_coupling`: both marginals are `m_p` (`lem:merge-repair`, "the mirror law has both
  marginals `m_p`").
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.SignedGram
open Sarkozy.NormBoundsPaper (kD p_gt_one)
open Sarkozy.JointRows.PaleyGauss (chiR chiR_neg chiR_zero chiR_sq)
open Sarkozy.MiddleRecords (dG etaG sG aG)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

/-- `N = p(p − 1)(p − 2)(p − 3)`. -/
noncomputable def Nq (p : ℕ) : ℝ := (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3)

omit [Fact p.Prime] in
theorem Nq_pos (hp : 5 ≤ p) : 0 < Nq p := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  unfold Nq
  have h1 : 0 < ((p : ℝ) - 2) * ((p : ℝ) - 3) := by nlinarith
  have h2 : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
  nlinarith

/-- The two edge characters `C = χ(y₀ − x₁)`, `H = χ(y₁ − x₀)`. -/
noncomputable def chC (x y : ZMod p × ZMod p) : ℝ := chiR p (y.1 - x.2)

noncomputable def chH (x y : ZMod p × ZMod p) : ℝ := chiR p (y.2 - x.1)

/-- The kernel `D_p · CH`. -/
noncomputable def symK (x y : ZMod p × ZMod p) : ℝ := ind4 x y * (chC x y * chH x y) / Nq p

/-- The kernel `D_p (C + H)`. -/
noncomputable def skwK (x y : ZMod p × ZMod p) : ℝ := ind4 x y * (chC x y + chH x y) / Nq p

theorem dsum_ind (x : ZMod p × ZMod p) :
    ∑ a, ∑ b, (if a = b then (0 : ℝ) else if a = x.1 ∧ b = x.2 then 1 else 0) = off x := by
  rw [sum_eq_single x.1 (fun a _ ha => sum_eq_zero fun b _ => by simp [ha]) (by simp)]
  rw [sum_eq_single x.2 (fun b _ hb => by simp [hb]) (by simp)]
  simp [off]

/-! ## The off-diagonal parts -/

theorem off_sum (u : ZMod p × ZMod p → ℝ) :
    ∑ x, off x * u x = (p : ℝ) * ((p : ℝ) - 1) * ∑ x, mP p x * u x := by
  have hp : (1 : ℝ) < p := p_gt_one
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mP_eq_off]
  field_simp

theorem off_sq (u : ZMod p × ZMod p → ℝ) :
    ∑ x, (off x * u x) ^ 2 = (p : ℝ) * ((p : ℝ) - 1) * ∑ x, mP p x * u x ^ 2 := by
  have hp : (1 : ℝ) < p := p_gt_one
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mP_eq_off]
  have := off_mul_self x
  field_simp
  linear_combination u x ^ 2 * this

theorem sqrt_off_sq (u : ZMod p × ZMod p → ℝ) :
    Real.sqrt (∑ x, (off x * u x) ^ 2) =
      Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt (∑ x, mP p x * u x ^ 2) := by
  have hp : (1 : ℝ) < p := p_gt_one
  rw [off_sq, Real.sqrt_mul (by nlinarith)]

/-- A kernel `ind4 · c / N` read on `u, v` is the form of `ind4 · c` on `off·u, off·v`. -/
theorem kernel_form_eq (c : ZMod p × ZMod p → ZMod p × ZMod p → ℝ) (u v : ZMod p × ZMod p → ℝ) :
    ∑ x, ∑ y, u x * (ind4 x y * c x y / Nq p) * v y =
      (1 / Nq p) * (∑ x, ∑ y, (off x * u x) * (off y * v y) * c x y -
        ∑ x, ∑ y, (off x * u x) * coll x y * c x y * (off y * v y)) := by
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_sub_distrib, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  have h1 := off_mul_self x
  have h2 := off_mul_self y
  have h3 := ind4_off x y
  unfold coll
  have e : off x * u x * (off y * v y) * c x y -
      off x * u x * (off x * off y - ind4 x y) * c x y * (off y * v y) =
      u x * c x y * v y * ((off x * off y) - (off x * off x) * (off y * off y) +
        (off x * off y * ind4 x y)) := by ring
  rw [e, h1, h2, h3]
  ring

/-! ## The mirror law -/

variable (hm : (injLabellings (ZMod p) mirrorGraph).Nonempty)

/-- The mirror-edge coupling of a merge record at one prime. -/
noncomputable def mirC : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℝ :=
  cm (mirrorLaw hm) (0, 0) (1, 0) (0, 1) (1, 1)

theorem chiR_eq_one_iff (d : ZMod p) : chiR p d = 1 ↔ quadraticChar (ZMod p) d = 1 := by
  unfold chiR
  constructor
  · intro h; exact_mod_cast h
  · intro h; rw [h]; norm_num

theorem chiR_pm (d : ZMod p) (hd : d ≠ 0) : chiR p d = 1 ∨ chiR p d = -1 := by
  unfold chiR
  rcases quadraticChar_dichotomy hd with h | h
  · left; rw [h]; norm_num
  · right; rw [h]; norm_num

/-- **The mirror-edge law at the two pairs**: `ind4 · (1 + C)(1 + H) / N`. -/
theorem mirC_eq (hp : 5 ≤ p) (h3 : p % 4 = 3) (x y : ZMod p × ZMod p) :
    mirC hm x y = ind4 x y * ((1 + chC x y) * (1 + chH x y)) / Nq p := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hc : Fintype.card (ZMod p) % 4 = 3 := by rw [ZMod.card]; exact h3
  unfold mirC cm
  change (mirrorLaw hm).expect (fun z => if z (0, 0) = x.1 ∧ z (1, 0) = x.2 ∧ z (0, 1) = y.1 ∧
    z (1, 1) = y.2 then (1 : ℝ) else 0) = _
  rw [mirrorLaw_expect, mirror_count_total hF hc, ZMod.card]
  have hnum : (∑ t : ZMod p × ZMod p × ZMod p × ZMod p, if MirrorCond t then
      (if quadConfig t (0, 0) = x.1 ∧ quadConfig t (1, 0) = x.2 ∧ quadConfig t (0, 1) = y.1 ∧
        quadConfig t (1, 1) = y.2 then (1 : ℝ) else 0) else 0) =
      if MirrorCond (x.1, x.2, y.1, y.2) then 1 else 0 := by
    rw [sum_eq_single (x.1, x.2, y.1, y.2)]
    · obtain ⟨h1, h2, h3', h4⟩ := quadConfig_apply (x.1, x.2, y.1, y.2)
      simp only [h1, h2, h3', h4, and_self, ↓reduceIte]
    · intro t _ ht
      obtain ⟨h1, h2, h3', h4⟩ := quadConfig_apply t
      have : ¬ (quadConfig t (0, 0) = x.1 ∧ quadConfig t (1, 0) = x.2 ∧
          quadConfig t (0, 1) = y.1 ∧ quadConfig t (1, 1) = y.2) := by
        rintro ⟨e1, e2, e3, e4⟩
        apply ht
        rw [h1] at e1
        rw [h2] at e2
        rw [h3'] at e3
        rw [h4] at e4
        obtain ⟨a, b, c, d⟩ := t
        simp only at e1 e2 e3 e4
        rw [e1, e2, e3, e4]
      simp only [this, ↓reduceIte, ite_self]
    · exact fun h => absurd (mem_univ _) h
  rw [hnum]
  have hN : Nq p = (p : ℝ) * ((p : ℝ) - 1) * (((p : ℝ) - 3) * ((p : ℝ) - 2) / 4) * 4 := by
    unfold Nq; ring
  rw [hN]
  have hD : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) * (((p : ℝ) - 3) * ((p : ℝ) - 2) / 4) := by
    have h1 : 0 < ((p : ℝ) - 3) * ((p : ℝ) - 2) := by nlinarith
    have h2 : 0 < (p : ℝ) * ((p : ℝ) - 1) := by nlinarith
    positivity
  rw [ind4_eq]
  unfold chC chH
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  simp only
  by_cases hmc : MirrorCond (a, b, c, d)
  · obtain ⟨d1, d2, d3, d4, e1, e2⟩ := hmc
    have hc1 : chiR p (c - b) = 1 := (chiR_eq_one_iff _).mpr e1
    have hc2 : chiR p (d - a) = 1 := (chiR_eq_one_iff _).mpr e2
    have n1 : c ≠ b := fun h => by rw [h, sub_self, quadraticChar_zero] at e1; exact zero_ne_one e1
    have n2 : d ≠ a := fun h => by rw [h, sub_self, quadraticChar_zero] at e2; exact zero_ne_one e2
    have hall : a ≠ b ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b :=
      ⟨d1, d4, Ne.symm d2, n1, n2, Ne.symm d3⟩
    rw [ite_eq_left_of_eq_true _ _ (eq_true (⟨d1, d2, d3, d4, e1, e2⟩ : MirrorCond (a, b, c, d))),
      ite_eq_left_of_eq_true _ _ (eq_true hall), hc1, hc2]
    field_simp
    ring
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hmc), zero_div]
    by_cases hall : a ≠ b ∧ c ≠ d ∧ c ≠ a ∧ c ≠ b ∧ d ≠ a ∧ d ≠ b
    · rw [ite_eq_left_of_eq_true _ _ (eq_true hall), one_mul]
      obtain ⟨d1, d4, d2, n1, n2, d3⟩ := hall
      have hz : (1 + chiR p (c - b)) * (1 + chiR p (d - a)) = 0 := by
        rcases chiR_pm (c - b) (sub_ne_zero.mpr n1) with h1 | h1 <;>
          rcases chiR_pm (d - a) (sub_ne_zero.mpr n2) with h2 | h2
        · exfalso
          exact hmc ⟨d1, Ne.symm d2, Ne.symm d3, d4, (chiR_eq_one_iff _).mp h1,
            (chiR_eq_one_iff _).mp h2⟩
        · rw [h2]; ring
        · rw [h1]; ring
        · rw [h1]; ring
      rw [hz, zero_div]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false hall), zero_mul, zero_div]

/-- **The mirror identity**: `P^c = D + D(C + H) + D·CH`. -/
theorem mirC_split (hp : 5 ≤ p) (h3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (x y : ZMod p × ZMod p) :
    mirC hm x y = srcC hne x y + skwK x y + symK x y := by
  rw [mirC_eq hm hp h3, srcC_eq hne hp]
  unfold skwK symK Nq
  ring

theorem chC_swap (h3 : p % 4 = 3) (x y : ZMod p × ZMod p) : chC y x = -chH x y := by
  unfold chC chH
  rw [← chiR_neg h3, neg_sub]

theorem chH_swap (h3 : p % 4 = 3) (x y : ZMod p × ZMod p) : chH y x = -chC x y := by
  unfold chC chH
  rw [← chiR_neg h3, neg_sub]

/-- **Transposition exchanges `C, H` with `−H, −C`**: `(P^c)ᵀ = D − D(C + H) + D·CH`. -/
theorem mirC_split_swap (hp : 5 ≤ p) (h3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (x y : ZMod p × ZMod p) :
    mirC hm y x = srcC hne x y - skwK x y + symK x y := by
  rw [mirC_eq hm hp h3, srcC_eq hne hp, chC_swap h3 x y, chH_swap h3 x y, ind4_symm y x]
  unfold skwK symK Nq
  ring

theorem mirC_nonneg (x y : ZMod p × ZMod p) : 0 ≤ mirC hm x y := cm_nonneg _ _ _ _ _ x y

theorem mirC_coupling (hp : 7 ≤ p) (h3 : p % 4 = 3) (x : ZMod p × ZMod p) :
    ∑ y, mirC hm x y = mP p x ∧ ∑ y, mirC hm y x = mP p x := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; omega
  have hc : Fintype.card (ZMod p) % 4 = 3 := by rw [ZMod.card]; exact h3
  have h7 : 7 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; exact hp
  have hp' : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have hfin : ((p : ℝ) * ((p : ℝ) - 1))⁻¹ * off x = mP p x := by
    rw [mP_eq_off]; field_simp
  constructor
  · rw [mirC, cm_row]
    change (mirrorLaw hm).expect (fun z => if z (0, 0) = x.1 ∧ z (1, 0) = x.2 then (1 : ℝ)
      else 0) = _
    rw [mirrorLaw_half0 hF hc h7 hm (fun a b => if a = x.1 ∧ b = x.2 then (1 : ℝ) else 0),
      dsum_ind, ZMod.card, hfin]
  · rw [mirC, cm_col]
    change (mirrorLaw hm).expect (fun z => if z (0, 1) = x.1 ∧ z (1, 1) = x.2 then (1 : ℝ)
      else 0) = _
    rw [mirrorLaw_half1 hF hc h7 hm (fun a b => if a = x.1 ∧ b = x.2 then (1 : ℝ) else 0),
      dsum_ind, ZMod.card, hfin]


/-! ## The prime bounds of the mirror law -/

theorem abs_chC_mul_le (x y : ZMod p × ZMod p) : |chC x y * chH x y| ≤ 1 := by
  rw [abs_mul]
  have h1 := chiR_abs_le (p := p) (y.1 - x.2)
  have h2 := chiR_abs_le (p := p) (y.2 - x.1)
  unfold chC chH
  nlinarith [abs_nonneg (chiR p (y.1 - x.2)), abs_nonneg (chiR p (y.2 - x.1))]

theorem abs_chC_add_le (x y : ZMod p × ZMod p) : |chC x y + chH x y| ≤ 2 := by
  have h1 := chiR_abs_le (p := p) (y.1 - x.2)
  have h2 := chiR_abs_le (p := p) (y.2 - x.1)
  unfold chC chH
  calc |chiR p (y.1 - x.2) + chiR p (y.2 - x.1)|
      ≤ |chiR p (y.1 - x.2)| + |chiR p (y.2 - x.1)| := abs_add_le _ _
    _ ≤ 2 := by linarith

theorem dot_mulVec_eq (M : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℝ)
    (u v : ZMod p × ZMod p → ℝ) : u ⬝ᵥ (M *ᵥ v) = ∑ x, ∑ y, u x * M x y * v y := by
  simp only [dotProduct, Matrix.mulVec, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

omit [Fact p.Prime] in
/-- `(5p − 6) p(p − 1)/N = s^G_p`. -/
theorem sG_eq (hp : 5 ≤ p) : (5 * (p : ℝ) - 6) * ((p : ℝ) * ((p : ℝ) - 1)) / Nq p = sG p := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (p : ℝ) - 3 ≠ 0 := by linarith
  unfold sG Nq
  field_simp

/-- **`‖D_p · CH‖ ≤ s^G_p`** (form version, on all of `L²(m_p)`). -/
theorem symK_form_le (hp : 5 ≤ p) (h3 : p % 4 = 3) (u v : ZMod p × ZMod p → ℝ) :
    |∑ x, ∑ y, u x * symK x y * v y| ≤
      sG p * Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hN := Nq_pos hp
  have e := kernel_form_eq (fun x y => chC x y * chH x y) u v
  rw [show (∑ x, ∑ y, u x * symK x y * v y) =
    ∑ x, ∑ y, u x * (ind4 x y * (chC x y * chH x y) / Nq p) * v y from rfl, e]
  set g : ZMod p × ZMod p → ℝ := fun x => off x * u x
  set h : ZMod p × ZMod p → ℝ := fun x => off x * v x
  have hM1 := two_chi_le h3 g h
  have hM2 := coll_form_le hp (fun x y => chC x y * chH x y) (M := 1)
    (fun x y => abs_chC_mul_le x y) g h
  have hg := sqrt_off_sq u
  have hh := sqrt_off_sq v
  set Su := Real.sqrt (∑ x, mP p x * u x ^ 2)
  set Sv := Real.sqrt (∑ x, mP p x * v x ^ 2)
  have hSu : 0 ≤ Su := Real.sqrt_nonneg _
  have hSv : 0 ≤ Sv := Real.sqrt_nonneg _
  have hq : Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) * Real.sqrt ((p : ℝ) * ((p : ℝ) - 1)) =
      (p : ℝ) * ((p : ℝ) - 1) := Real.mul_self_sqrt (by nlinarith)
  change |∑ x, ∑ y, g x * h y * (chiR p (y.1 - x.2) * chiR p (y.2 - x.1))| ≤ _ at hM1
  rw [hg, hh] at hM1 hM2
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hN), ← sG_eq hp]
  have htri := abs_sub (∑ x, ∑ y, g x * h y * (chC x y * chH x y))
    (∑ x, ∑ y, g x * coll x y * (chC x y * chH x y) * h y)
  set Q := Real.sqrt ((p : ℝ) * ((p : ℝ) - 1))
  have hb : |∑ x, ∑ y, g x * h y * (chC x y * chH x y) -
      ∑ x, ∑ y, g x * coll x y * (chC x y * chH x y) * h y| ≤
      (5 * (p : ℝ) - 6) * ((p : ℝ) * ((p : ℝ) - 1)) * Su * Sv := by
    refine htri.trans ?_
    have : (p : ℝ) * (Q * Su) * (Q * Sv) + 1 * (4 * (p : ℝ) - 6) * (Q * Su) * (Q * Sv) =
        (5 * (p : ℝ) - 6) * ((p : ℝ) * ((p : ℝ) - 1)) * Su * Sv := by
      rw [← hq]; ring
    rw [← this]
    exact add_le_add hM1 hM2
  calc 1 / Nq p * |∑ x, ∑ y, g x * h y * (chC x y * chH x y) -
        ∑ x, ∑ y, g x * coll x y * (chC x y * chH x y) * h y|
      ≤ 1 / Nq p * ((5 * (p : ℝ) - 6) * ((p : ℝ) * ((p : ℝ) - 1)) * Su * Sv) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by field_simp

theorem main_lin1 (g h : ZMod p × ZMod p → ℝ) :
    ∑ x, ∑ y, g x * h y * chC x y = ∑ b, colS g b * ∑ c, chiR p (c - b) * rowS h c := by
  unfold chC colS rowS
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => sum_congr rfl fun a _ => sum_congr rfl fun c _ =>
    sum_congr rfl fun d _ => ?_
  ring

theorem main_lin2 (g h : ZMod p × ZMod p → ℝ) :
    ∑ x, ∑ y, g x * h y * chH x y = ∑ a, rowS g a * ∑ d, chiR p (d - a) * colS h d := by
  unfold chH colS rowS
  simp only [Fintype.sum_prod_type, Finset.sum_mul_sum]
  simp only [mul_sum]
  refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun d _ => sum_congr rfl fun c _ => ?_
  ring

omit [Fact p.Prime] in
theorem two_dot_le {a b c d : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d) :
    Real.sqrt a * Real.sqrt c + Real.sqrt b * Real.sqrt d ≤
      Real.sqrt (a + b) * Real.sqrt (c + d) := by
  rw [← Real.sqrt_mul (add_nonneg ha hb)]
  have hl : 0 ≤ Real.sqrt a * Real.sqrt c + Real.sqrt b * Real.sqrt d := by positivity
  rw [← Real.sqrt_sq hl]
  refine Real.sqrt_le_sqrt ?_
  have e1 := Real.sq_sqrt ha
  have e2 := Real.sq_sqrt hb
  have e3 := Real.sq_sqrt hc
  have e4 := Real.sq_sqrt hd
  nlinarith [sq_nonneg (Real.sqrt a * Real.sqrt d - Real.sqrt b * Real.sqrt c)]

/-- `a^G_p = (p√p + 8p − 12)/((p − 2)(p − 3))`. -/
theorem aG_eq {q : ℝ} (hq : 4 ≤ q) :
    aG q = (q * Real.sqrt q + 8 * q - 12) / ((q - 2) * (q - 3)) := by
  have hs : Real.sqrt q ^ 2 = q := Real.sq_sqrt (by linarith)
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr (by linarith)
  have h2 : q - 2 ≠ 0 := by linarith
  have h3 : q - 3 ≠ 0 := by linarith
  have hq0 : q ≠ 0 := by linarith
  unfold aG
  rw [div_eq_div_iff (by
    have : (1 - 2 / q) * (1 - 3 / q) = (q - 2) * (q - 3) / q ^ 2 := by field_simp
    rw [this]; positivity) (by positivity)]
  field_simp
  linear_combination (12 - 8 * q - q * Real.sqrt q) * hs

/-- **`‖D_p (C + H)‖ ≤ a^G_p`** (form version, on mean-zero functions of `L²(m_p)`). -/
theorem skwK_form_le (hp : 5 ≤ p) (h3 : p % 4 = 3) (u v : ZMod p × ZMod p → ℝ)
    (hu : ∑ x, mP p x * u x = 0) (hv : ∑ x, mP p x * v x = 0) :
    |∑ x, ∑ y, u x * skwK x y * v y| ≤
      aG p * Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < p := by linarith
  have hN := Nq_pos hp
  have e := kernel_form_eq (fun x y => chC x y + chH x y) u v
  rw [show (∑ x, ∑ y, u x * skwK x y * v y) =
    ∑ x, ∑ y, u x * (ind4 x y * (chC x y + chH x y) / Nq p) * v y from rfl, e]
  set g : ZMod p × ZMod p → ℝ := fun x => off x * u x
  set h : ZMod p × ZMod p → ℝ := fun x => off x * v x
  have hgd : OffDiag g := fun a => by simp [g, off]
  have hhd : OffDiag h := fun a => by simp [h, off]
  have hg0 : ∑ x, g x = 0 := by rw [off_sum, hu, mul_zero]
  have hh0 : ∑ x, h x = 0 := by rw [off_sum, hv, mul_zero]
  -- the linear term
  have hlin : ∑ x, ∑ y, g x * h y * (chC x y + chH x y) =
      ∑ b, colS g b * ∑ c, chiR p (c - b) * rowS h c +
        ∑ a, rowS g a * ∑ d, chiR p (d - a) * colS h d := by
    rw [← main_lin1, ← main_lin2, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib]
    exact sum_congr rfl fun y _ => by ring
  have hRg := rows_cols_le hgd hg0
  have hRh := rows_cols_le hhd hh0
  set Rg := ∑ a, rowS g a ^ 2
  set Cg := ∑ b, colS g b ^ 2
  set Rh := ∑ a, rowS h a ^ 2
  set Ch := ∑ b, colS h b ^ 2
  have hRg0 : 0 ≤ Rg := sum_nonneg fun a _ => sq_nonneg _
  have hCg0 : 0 ≤ Cg := sum_nonneg fun a _ => sq_nonneg _
  have hRh0 : 0 ≤ Rh := sum_nonneg fun a _ => sq_nonneg _
  have hCh0 : 0 ≤ Ch := sum_nonneg fun a _ => sq_nonneg _
  have hL1 := chi_form_le h3 (colS g) (rowS h)
  have hL2 := chi_form_le h3 (rowS g) (colS h)
  set Gs := ∑ x, g x ^ 2
  set Hs := ∑ x, h x ^ 2
  have hGs : 0 ≤ Gs := sum_nonneg fun a _ => sq_nonneg _
  have hHs : 0 ≤ Hs := sum_nonneg fun a _ => sq_nonneg _
  have hM1 : |∑ x, ∑ y, g x * h y * (chC x y + chH x y)| ≤
      (p : ℝ) * Real.sqrt p * Real.sqrt Gs * Real.sqrt Hs := by
    rw [hlin]
    have hd := two_dot_le hCg0 hRg0 hRh0 hCh0
    have hA : Real.sqrt (Cg + Rg) ≤ Real.sqrt p * Real.sqrt Gs := by
      rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt (by linarith)
    have hB : Real.sqrt (Rh + Ch) ≤ Real.sqrt p * Real.sqrt Hs := by
      rw [← Real.sqrt_mul hp0.le]; exact Real.sqrt_le_sqrt (by linarith)
    have hsq : Real.sqrt (p : ℝ) * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    calc |∑ b, colS g b * ∑ c, chiR p (c - b) * rowS h c +
          ∑ a, rowS g a * ∑ d, chiR p (d - a) * colS h d|
        ≤ Real.sqrt p * Real.sqrt Cg * Real.sqrt Rh + Real.sqrt p * Real.sqrt Rg * Real.sqrt Ch :=
          (abs_add_le _ _).trans (add_le_add hL1 hL2)
      _ = Real.sqrt p * (Real.sqrt Cg * Real.sqrt Rh + Real.sqrt Rg * Real.sqrt Ch) := by ring
      _ ≤ Real.sqrt p * (Real.sqrt (Cg + Rg) * Real.sqrt (Rh + Ch)) :=
          mul_le_mul_of_nonneg_left hd (Real.sqrt_nonneg _)
      _ ≤ Real.sqrt p * ((Real.sqrt p * Real.sqrt Gs) * (Real.sqrt p * Real.sqrt Hs)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hA hB (Real.sqrt_nonneg _) (by positivity))
            (Real.sqrt_nonneg _)
      _ = (Real.sqrt p * Real.sqrt p) * Real.sqrt p * Real.sqrt Gs * Real.sqrt Hs := by ring
      _ = _ := by rw [hsq]
  have hM2 := coll_form_le hp (fun x y => chC x y + chH x y) (M := 2)
    (fun x y => abs_chC_add_le x y) g h
  have hg := sqrt_off_sq u
  have hh := sqrt_off_sq v
  set Su := Real.sqrt (∑ x, mP p x * u x ^ 2)
  set Sv := Real.sqrt (∑ x, mP p x * v x ^ 2)
  have hSu : 0 ≤ Su := Real.sqrt_nonneg _
  have hSv : 0 ≤ Sv := Real.sqrt_nonneg _
  set Q := Real.sqrt ((p : ℝ) * ((p : ℝ) - 1))
  have hq : Q * Q = (p : ℝ) * ((p : ℝ) - 1) := Real.mul_self_sqrt (by nlinarith)
  change Real.sqrt Gs = Q * Su at hg
  change Real.sqrt Hs = Q * Sv at hh
  rw [hg, hh] at hM1
  rw [hg, hh] at hM2
  rw [abs_mul, abs_of_pos (one_div_pos.mpr hN)]
  have hb : |∑ x, ∑ y, g x * h y * (chC x y + chH x y) -
      ∑ x, ∑ y, g x * coll x y * (chC x y + chH x y) * h y| ≤
      ((p : ℝ) * Real.sqrt p + 8 * p - 12) * ((p : ℝ) * ((p : ℝ) - 1)) * Su * Sv := by
    refine (abs_sub _ _).trans ?_
    have : (p : ℝ) * Real.sqrt p * (Q * Su) * (Q * Sv) + 2 * (4 * (p : ℝ) - 6) * (Q * Su) * (Q * Sv)
        = ((p : ℝ) * Real.sqrt p + 8 * p - 12) * ((p : ℝ) * ((p : ℝ) - 1)) * Su * Sv := by
      rw [← hq]; ring
    rw [← this]
    exact add_le_add hM1 hM2
  rw [aG_eq (by linarith)]
  calc 1 / Nq p * |∑ x, ∑ y, g x * h y * (chC x y + chH x y) -
        ∑ x, ∑ y, g x * coll x y * (chC x y + chH x y) * h y|
      ≤ 1 / Nq p * (((p : ℝ) * Real.sqrt p + 8 * p - 12) * ((p : ℝ) * ((p : ℝ) - 1)) * Su * Sv) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = _ := by
      have h0 : (p : ℝ) ≠ 0 := by linarith
      have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
      have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
      have h3 : (p : ℝ) - 3 ≠ 0 := by linarith
      unfold Nq
      field_simp

/-- **The centred norm of the mirror law is at most `α^G_p = d_p + s^G_p + a^G_p`.** -/
theorem mir_centred (hp : 7 ≤ p) (h3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) :
    CentredNorm (mP p) (mirC hm) (dG p + sG p + aG p) := by
  have hp5 : 5 ≤ p := by omega
  have hp' : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have hd0 : 0 ≤ dG p := by unfold dG; exact div_nonneg (by norm_num) (by linarith)
  have hs0 : 0 ≤ sG p := by
    unfold sG; exact div_nonneg (by linarith) (mul_nonneg (by linarith) (by linarith))
  have ha0 : 0 ≤ aG p := by
    rw [aG_eq (by linarith)]
    have : 0 ≤ Real.sqrt p := Real.sqrt_nonneg _
    exact div_nonneg (by nlinarith) (mul_nonneg (by linarith) (by linarith))
  refine centredNorm_of_form mP_nonneg (mirC_nonneg hm) (fun a => (mirC_coupling hm hp h3 a).1)
    (fun b => (mirC_coupling hm hp h3 b).2) (by linarith) fun u v hu hv => ?_
  have e : u ⬝ᵥ (mirC hm *ᵥ v) = u ⬝ᵥ (srcC hne *ᵥ v) + ∑ x, ∑ y, u x * skwK x y * v y +
      ∑ x, ∑ y, u x * symK x y * v y := by
    rw [dot_mulVec_eq, dot_mulVec_eq, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun y _ => ?_
    rw [mirC_split hm hp5 h3 hne]
    ring
  rw [e]
  have h1 := src_form_le hne hp5 u v hu hv
  have h2 := skwK_form_le hp5 h3 u v hu hv
  have h3' := symK_form_le hp5 h3 u v
  calc |u ⬝ᵥ (srcC hne *ᵥ v) + ∑ x, ∑ y, u x * skwK x y * v y +
        ∑ x, ∑ y, u x * symK x y * v y|
      ≤ |u ⬝ᵥ (srcC hne *ᵥ v)| + |∑ x, ∑ y, u x * skwK x y * v y| +
        |∑ x, ∑ y, u x * symK x y * v y| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith

/-- The prime form of the change is a kernel form. -/
theorem chg1_eq (P C : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℝ) (α₁ α₂ β : ℝ)
    (u v : ZMod p × ZMod p → ℝ) :
    chg1 P C α₁ α₂ β u v = ∑ x, ∑ y, u x * (α₁ * P x y + α₂ * P y x - β * C x y) * v y := by
  unfold chg1
  rw [dot_mulVec_eq, dot_mulVec_eq, dot_mulVec_eq, sum_comm (f := fun x y => v x * P x y * u y),
    mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  exact sum_congr rfl fun y _ => by ring

/-- **The prime symmetric difference of the mirror merge**: `Sym(P^c − D_p) = D_p CH`, norm
`≤ s^G_p`. -/
theorem mir_single_sym (hp : 5 ≤ p) (h3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (u v : ZMod p × ZMod p → ℝ) :
    |chg1 (mirC hm) (srcC hne) (1 / 2) (1 / 2) 1 u v| ≤
      sG p * Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  rw [chg1_eq]
  have e : ∑ x, ∑ y, u x * (1 / 2 * mirC hm x y + 1 / 2 * mirC hm y x - 1 * srcC hne x y) * v y =
      ∑ x, ∑ y, u x * symK x y * v y := by
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [mirC_split hm hp h3 hne, mirC_split_swap hm hp h3 hne]
    ring
  rw [e]
  exact symK_form_le hp h3 u v

/-- **The prime skew part of the mirror merge**: `Skew(P^c − D_p) = D_p (C + H)`, norm `≤ a^G_p`
on mean-zero functions. -/
theorem mir_single_skew (hp : 5 ≤ p) (h3 : p % 4 = 3)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (u v : ZMod p × ZMod p → ℝ)
    (hu : ∑ x, mP p x * u x = 0) (hv : ∑ x, mP p x * v x = 0) :
    |chg1 (mirC hm) (srcC hne) (1 / 2) (-(1 / 2)) 0 u v| ≤
      aG p * Real.sqrt (∑ x, mP p x * u x ^ 2) * Real.sqrt (∑ x, mP p x * v x ^ 2) := by
  rw [chg1_eq]
  have e : ∑ x, ∑ y, u x * (1 / 2 * mirC hm x y + -(1 / 2) * mirC hm y x - 0 * srcC hne x y) *
      v y = ∑ x, ∑ y, u x * skwK x y * v y := by
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [mirC_split hm hp h3 hne, mirC_split_swap hm hp h3 hne]
    ring
  rw [e]
  exact skwK_form_le hp h3 u v hu hv

end Sarkozy.NormBoundsPaper2

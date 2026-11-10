module

public import Sarkozy.NormBoundsPaper.PairLaws
public import Sarkozy.SignedComponents.Data

@[expose] public section

/-!
# The constant families `Cs`, `Ca` of `NormBounds` (`lem:record:accepting-c2`), proved

`paper/sections/21_middle_records.tex`, `lem:record:accepting-c2`: "If `b ≥ 7` is the least
prime … and `r = b^{-1/2}`, the symmetric and skew norms of the normalized replacement minus the
source are at most `r²/(1 − 1/b)²`, `r/(1 − 1/b)`."

On V3's frame of a middle block (any root), for the two changed constant records
`t = .inr (.inr (.inr k))` of B8's `ofFold`:

* `form_emit`, `hsq_emit`: at the reserved cut a record emitted through a map that reads one
  object `o₀` on the plus half and `o₁` on the minus half has the form
  `E[F(const y_{o₀}) G(const y_{o₁})]`, and its actual half marginal gives
  `‖F‖² = E[F(const y_{o₀})²]`;
* `form_old`, `form_new`, `hsq_old`: the old record (V1's `E` law read at the object `0`) and the
  replacement `constRec` (the strict Paley edge) as pair kernels `N⁻¹ K_D(c − a)` and
  `N⁻¹ K_P(c − a)` (`PairLaws`); the norm is `N⁻¹ ∑_a f(a)²`;
* **`form_sym_eq`**, **`form_skew_eq`**: the symmetric and skew parts of the change are the
  convolution forms of `K^s`, `K^a` (`Block`);
* **`const_sym`**, **`const_skew`**: `FormBound` with constants `γ_b²` and `γ_b` for every
  `b ≥ 7` below every prime of the block;
* **`const_sym_paper`**, **`const_skew_paper`**: the paper's constants `r²/(1 − 1/b)²` and
  `r/(1 − 1/b)` for `r = b^{-1/2}`, i.e. the fields `Cs`, `Ca` of B8's `NormBounds`.

No hypothesis beyond the block's (`p ≡ 3 (4)`, `p ≥ b ≥ 7`) is used: no Weil bound (the Gauss
sum `G_χ = ±i√p` is exact).
-/

namespace Sarkozy.NormBoundsPaper

open Finset
open scoped BigOperators

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents

/-! ## Records reading one object per half -/

section Emit

variable {I X : Type} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

theorem form_emit (lam : FiniteLaw (I → X)) (π : Slot → I) (o₀ o₁ : I)
    (h0 : ∀ v : reservedCut.Half, π v.1 = o₀)
    (h1 : ∀ v : reservedCut.Half, π (reservedCut.flip v.1) = o₁)
    (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam π).weight) F G =
      lam.expect (fun y => F (fun _ => y o₀) * G (fun _ => y o₁)) := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  refine FiniteLaw.expect_congr _ fun y => ?_
  have e0 : (fun v : reservedCut.Half => (y ∘ π) v.1) = fun _ => y o₀ :=
    funext fun v => by simp only [Function.comp_apply, h0 v]
  have e1 : (fun v : reservedCut.Half => (y ∘ π) (reservedCut.flip v.1)) = fun _ => y o₁ :=
    funext fun v => by simp only [Function.comp_apply, h1 v]
  simp only [e0, e1]

theorem hsq_emit (lam : FiniteLaw (I → X)) (π : Slot → I) (o₀ : I)
    (h0 : ∀ v : reservedCut.Half, π v.1 = o₀) (F : (reservedCut.Half → X) → ℝ) :
    hsq reservedCut (plusMarginal reservedCut (emit lam π).weight) F =
      lam.expect (fun y => F (fun _ => y o₀) * F (fun _ => y o₀)) := by
  unfold hsq plusMarginal
  rw [sum_marginal_mul (fun z : Slot → X => fun v : reservedCut.Half => z v.1) (emit lam π).weight
    (fun x => F x * F x)]
  change (emit lam π).expect _ = _
  rw [expect_emit]
  refine FiniteLaw.expect_congr _ fun y => ?_
  have e0 : (fun v : reservedCut.Half => (y ∘ π) v.1) = fun _ => y o₀ :=
    funext fun v => by simp only [Function.comp_apply, h0 v]
  simp only [e0]

end Emit

theorem half_layer : ∀ v : Slot, v ∈ reservedCut.half → layerFin v.2.2 = 0 := by decide

theorem flip_layer : ∀ v : Slot, v ∈ reservedCut.half → layerFin (reservedCut.flip v).2.2 = 1 := by
  decide

/-! ## The two records of a constant change -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

omit [DecidableEq ι] in
theorem KD_neg (d : ∀ i, ZMod (pr i)) : KD pr (-d) = KD pr d := by
  unfold KD kD
  refine prod_congr rfl fun i _ => ?_
  have e : ((-d) i = 0) ↔ (d i = 0) := neg_eq_zero
  exact if_congr e rfl rfl

omit [DecidableEq ι] in
theorem KD_swap (a c : ∀ i, ZMod (pr i)) : KD pr (a - c) = KD pr (c - a) :=
  (congrArg (KD pr) (neg_sub c a).symm).trans (KD_neg pr (c - a))

omit [DecidableEq ι] in
theorem Ksym_eq (a c : ∀ i, ZMod (pr i)) :
    Ksym pr (c - a) = (1 / 2) * (KP pr (c - a) + KP pr (a - c)) - KD pr (c - a) := by
  have e : KP pr (-(c - a)) = KP pr (a - c) := congrArg (KP pr) (neg_sub c a)
  calc Ksym pr (c - a) = (1 / 2) * (KP pr (c - a) + KP pr (-(c - a))) - KD pr (c - a) := rfl
    _ = _ := by rw [e]

omit [DecidableEq ι] in
theorem Kskew_eq (a c : ∀ i, ZMod (pr i)) :
    Kskew pr (c - a) = (1 / 2) * (KP pr (c - a) - KP pr (a - c)) := by
  have e : KP pr (-(c - a)) = KP pr (a - c) := congrArg (KP pr) (neg_sub c a)
  calc Kskew pr (c - a) = (1 / 2) * (KP pr (c - a) - KP pr (-(c - a))) := rfl
    _ = _ := by rw [e]

theorem sum_KD : ∑ d : ∀ i, ZMod (pr i), KD pr d = 1 := by
  unfold KD
  rw [← Fintype.prod_sum (fun i x => kD (pr i) x)]
  exact prod_eq_one fun i _ => sum_kD

/-- The emission of the old constant record. -/
abbrev constOldEm : Slot → Fin 3 × Fin 2 := midEmission (fun _ => (0 : Fin 3))

theorem constOldEm_half (v : reservedCut.Half) : constOldEm v.1 = ((0 : Fin 3), (0 : Fin 2)) := by
  simp only [constOldEm, midEmission, half_layer v.1 v.2]

theorem constOldEm_flip (v : reservedCut.Half) :
    constOldEm (reservedCut.flip v.1) = ((0 : Fin 3), (1 : Fin 2)) := by
  simp only [constOldEm, midEmission, flip_layer v.1 v.2]

theorem layerEm_half (v : reservedCut.Half) : layerEmission v.1 = 0 := half_layer v.1 v.2

theorem layerEm_flip (v : reservedCut.Half) : layerEmission (reservedCut.flip v.1) = 1 :=
  flip_layer v.1 v.2

variable (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)

/-- The old constant record as a measure. -/
noncomputable abbrev oldC : SlotMeasure (BlockLabel pr) :=
  signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 2)) hE) constOldEm).weight

/-- The constant replacement as a measure. -/
noncomputable abbrev newC : SlotMeasure (BlockLabel pr) := signedIntegral (constRec pr).weight

/-- The value of a half function on the constant half `a`. -/
abbrev cst (F : (reservedCut.Half → BlockLabel pr) → ℝ) (a : BlockLabel pr) : ℝ := F (fun _ => a)

theorem form_old (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (oldC pr hE) F G =
      ∑ a, ∑ c, (invN pr * KD pr (c - a)) * (cst pr F a * cst pr G c) := by
  rw [form_emit _ _ _ _ constOldEm_half constOldEm_flip]
  exact expect_pair_match pr hE (fun a c => cst pr F a * cst pr G c) (by decide)

theorem form_new (hp2 : ∀ i, pr i ≠ 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (newC pr) F G =
      ∑ a, ∑ c, (invN pr * KP pr (c - a)) * (cst pr F a * cst pr G c) := by
  rw [newC, constRec, form_emit _ _ _ _ layerEm_half layerEm_flip]
  exact expect_pair_edge pr hp2 (fun a c => cst pr F a * cst pr G c)

theorem hsq_old (F : (reservedCut.Half → BlockLabel pr) → ℝ) :
    hsq reservedCut (plusMarginal reservedCut
        (emit (blockGraphLaw pr (matchGraph (Fin 2)) hE) constOldEm).weight) F =
      invN pr * ∑ a, cst pr F a ^ 2 := by
  rw [hsq_emit _ _ _ constOldEm_half]
  have := expect_pair_match pr hE (fun a _ => cst pr F a * cst pr F a) (u := (0, 0)) (v := (0, 1))
    (by decide)
  rw [this, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_mul, ← mul_sum,
    Fintype.sum_equiv (Equiv.subRight a) (fun c => KD pr (c - a)) (KD pr) (fun c => rfl),
    sum_KD, sq]
  ring

/-- Swapping the two arguments of a pair form reverses the kernel. -/
theorem sum_swap (K : BlockLabel pr → ℝ) (f g : BlockLabel pr → ℝ) :
    ∑ a, ∑ c, (invN pr * K (c - a)) * (g a * f c) =
      ∑ a, ∑ c, (invN pr * K (a - c)) * (f a * g c) := by
  rw [sum_comm]
  exact sum_congr rfl fun a _ => sum_congr rfl fun c _ => by ring

/-- **The symmetric part of the constant change is the convolution form of `K^s`.** -/
theorem form_sym_eq (hp2 : ∀ i, pr i ≠ 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (symPart reservedCut (newC pr - oldC pr hE)) F G =
      invN pr * ∑ a, ∑ c, Ksym pr (c - a) * cst pr F a * cst pr G c := by
  have hL : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (newC pr - oldC pr hE) F G =
        reservedCut.form (newC pr) F G - reservedCut.form (oldC pr hE) F G := fun _ _ => rfl
  unfold symPart
  rw [form_smul, form_add, form_reflect, hL, hL, form_new pr hp2, form_new pr hp2, form_old,
    form_old, sum_swap pr (KP pr) (cst pr F) (cst pr G),
    sum_swap pr (KD pr) (cst pr F) (cst pr G)]
  calc (1 / 2 : ℝ) * (∑ a, ∑ c, invN pr * KP pr (c - a) * (cst pr F a * cst pr G c) -
        ∑ a, ∑ c, invN pr * KD pr (c - a) * (cst pr F a * cst pr G c) +
        (∑ a, ∑ c, invN pr * KP pr (a - c) * (cst pr F a * cst pr G c) -
        ∑ a, ∑ c, invN pr * KD pr (a - c) * (cst pr F a * cst pr G c)))
      = ∑ a, ∑ c, (1 / 2) * (invN pr * KP pr (c - a) * (cst pr F a * cst pr G c) -
          invN pr * KD pr (c - a) * (cst pr F a * cst pr G c) +
          (invN pr * KP pr (a - c) * (cst pr F a * cst pr G c) -
          invN pr * KD pr (a - c) * (cst pr F a * cst pr G c))) := by
        simp only [mul_add, mul_sub, sum_add_distrib, sum_sub_distrib, mul_sum]
    _ = invN pr * ∑ a, ∑ c, Ksym pr (c - a) * cst pr F a * cst pr G c := by
        rw [mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun c _ => ?_
        rw [Ksym_eq, KD_swap]
        ring

/-- **The skew part of the constant change is the convolution form of `K^a`.** -/
theorem form_skew_eq (hp2 : ∀ i, pr i ≠ 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (skewPart reservedCut (newC pr - oldC pr hE)) F G =
      invN pr * ∑ a, ∑ c, Kskew pr (c - a) * cst pr F a * cst pr G c := by
  have hL : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (newC pr - oldC pr hE) F G =
        reservedCut.form (newC pr) F G - reservedCut.form (oldC pr hE) F G := fun _ _ => rfl
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  unfold skewPart
  rw [form_smul, hS, form_reflect, hL, hL, form_new pr hp2, form_new pr hp2, form_old,
    form_old, sum_swap pr (KP pr) (cst pr F) (cst pr G),
    sum_swap pr (KD pr) (cst pr F) (cst pr G)]
  calc (1 / 2 : ℝ) * (∑ a, ∑ c, invN pr * KP pr (c - a) * (cst pr F a * cst pr G c) -
        ∑ a, ∑ c, invN pr * KD pr (c - a) * (cst pr F a * cst pr G c) -
        (∑ a, ∑ c, invN pr * KP pr (a - c) * (cst pr F a * cst pr G c) -
        ∑ a, ∑ c, invN pr * KD pr (a - c) * (cst pr F a * cst pr G c)))
      = ∑ a, ∑ c, (1 / 2) * (invN pr * KP pr (c - a) * (cst pr F a * cst pr G c) -
          invN pr * KD pr (c - a) * (cst pr F a * cst pr G c) -
          (invN pr * KP pr (a - c) * (cst pr F a * cst pr G c) -
          invN pr * KD pr (a - c) * (cst pr F a * cst pr G c))) := by
        simp only [mul_sub, sum_sub_distrib, mul_sum]
    _ = invN pr * ∑ a, ∑ c, Kskew pr (c - a) * cst pr F a * cst pr G c := by
        rw [mul_sum]
        refine sum_congr rfl fun a _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun c _ => ?_
        rw [Kskew_eq, KD_swap]
        ring

/-- From the convolution bound to `FormBound`. -/
theorem formBound_of_conv {L : SlotMeasure (BlockLabel pr)} {K : BlockLabel pr → ℝ} {M : ℝ}
    (hM : 0 ≤ M)
    (hL : ∀ F G, reservedCut.form L F G = invN pr * ∑ a, ∑ c, K (c - a) * cst pr F a * cst pr G c)
    (hK : ∀ f g : BlockLabel pr → ℝ, |∑ a, ∑ c, K (c - a) * f a * g c| ≤
      M * Real.sqrt (∑ a, f a ^ 2) * Real.sqrt (∑ c, g c ^ 2)) :
    FormBound reservedCut (plusMarginal reservedCut
        (emit (blockGraphLaw pr (matchGraph (Fin 2)) hE) constOldEm).weight) L M := by
  refine ⟨hM, fun F G => ?_⟩
  rw [hsq_old, hsq_old, hL, abs_mul, abs_of_pos (invN_pos pr)]
  have hN := invN_pos pr
  rw [Real.sqrt_mul hN.le, Real.sqrt_mul hN.le]
  have hs : Real.sqrt (invN pr) * Real.sqrt (invN pr) = invN pr := Real.mul_self_sqrt hN.le
  calc invN pr * |∑ a, ∑ c, K (c - a) * cst pr F a * cst pr G c|
      ≤ invN pr * (M * Real.sqrt (∑ a, cst pr F a ^ 2) * Real.sqrt (∑ c, cst pr G c ^ 2)) :=
        mul_le_mul_of_nonneg_left (hK _ _) hN.le
    _ = (Real.sqrt (invN pr) * Real.sqrt (invN pr)) *
          (M * Real.sqrt (∑ a, cst pr F a ^ 2) * Real.sqrt (∑ c, cst pr G c ^ 2)) := by rw [hs]
    _ = M * (Real.sqrt (invN pr) * Real.sqrt (∑ a, cst pr F a ^ 2)) *
          (Real.sqrt (invN pr) * Real.sqrt (∑ a, cst pr G a ^ 2)) := by ring

end Block

/-! ## The fields `Cs`, `Ca` of `NormBounds` -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
theorem hp2_of (h : ClassThreeBlock pr) : ∀ i, pr i ≠ 2 := fun i hi => by
  have := h.mod4 i
  rw [hi] at this
  norm_num at this

/-- The changed constant record of the frame is the old record `oldC`. -/
theorem recM_const (k : PType.Pat .C) :
    recM (middleFrame pr hne root W I hr b h).F (true, chgPat (.inr (.inr (.inr k)))) =
      oldC pr hne.E2 := rfl

/-- Its actual half marginal. -/
theorem mOf_const (k : PType.Pat .C) :
    mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))) =
      plusMarginal reservedCut
        (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2) constOldEm).weight := rfl

/-- **`lem:record:accepting-c2`, symmetric norm**: `γ_b²` for every `b ≥ 7` below the primes. -/
theorem const_sym (C : FoldComponents pr hne) (t : ℝ) (k : PType.Pat .C) {b' : ℝ}
    (hb7 : 7 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .sym) (gam b' ^ 2) := by
  rw [mOf_const]
  exact formBound_of_conv pr hne.E2 (sq_nonneg _) (form_sym_eq pr hne.E2 (hp2_of pr h))
    (form_Ksym_le h.mod4 hb7 hbp)

/-- **`lem:record:accepting-c2`, skew norm**: `γ_b` for every `b ≥ 7` below the primes. -/
theorem const_skew (C : FoldComponents pr hne) (t : ℝ) (k : PType.Pat .C) {b' : ℝ}
    (hb7 : 7 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .skew) (gam b') := by
  rw [mOf_const]
  have hγ : 0 ≤ gam b' := by
    unfold gam
    exact div_nonneg (Real.sqrt_nonneg _) (by linarith)
  exact formBound_of_conv pr hne.E2 hγ (form_skew_eq pr hne.E2 (hp2_of pr h))
    (form_Kskew_le h.mod4 hb7 hbp)

/-- `γ_b = r/(1 − 1/b)` for `r = b^{-1/2}`. -/
theorem gam_eq {b' : ℝ} (hb : 1 < b') : gam b' = (1 / Real.sqrt b') / (1 - 1 / b') := by
  have hs : 0 < Real.sqrt b' := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt b' * Real.sqrt b' = b' := Real.mul_self_sqrt (by linarith)
  have hb0 : b' ≠ 0 := by linarith
  have hb1 : b' - 1 ≠ 0 := by linarith
  unfold gam
  rw [one_sub_div hb0, div_div_eq_mul_div]
  congr 1
  calc Real.sqrt b' = 1 / Real.sqrt b' * (Real.sqrt b' * Real.sqrt b') := by
        field_simp
    _ = 1 / Real.sqrt b' * b' := by rw [hss]

/-- **The field `Cs` of `NormBounds` at the paper's constant** (`lem:record:accepting-c2`):
`r²/(1 − 1/b)²` with `r = b^{-1/2}`, `b ≥ 7` below every prime of the block. -/
theorem const_sym_paper (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ} (hb7 : 7 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hrb : r = 1 / Real.sqrt b') (k : PType.Pat .C) :
    FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .sym)
      (r ^ 2 / (1 - 1 / b') ^ 2) := by
  have := const_sym pr h hne root W I hr b C t k hb7 hbp
  rwa [gam_eq (by linarith), div_pow, ← hrb] at this

/-- **The field `Ca` of `NormBounds` at the paper's constant** (`lem:record:accepting-c2`):
`r/(1 − 1/b)` with `r = b^{-1/2}`. -/
theorem const_skew_paper (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ} (hb7 : 7 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (hrb : r = 1 / Real.sqrt b') (k : PType.Pat .C) :
    FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inr k))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inr k))) .skew)
      (r / (1 - 1 / b')) := by
  have := const_skew pr h hne root W I hr b C t k hb7 hbp
  rwa [gam_eq (by linarith), ← hrb] at this

end Frame

end Sarkozy.NormBoundsPaper

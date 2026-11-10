module

public import Sarkozy.NormBoundsPaper.Const

@[expose] public section

/-!
# The skew norm of the first-coordinate merge replacements (`lem:merge-repair`, field `Ma₂`)

`paper/sections/21_middle_records.tex`, `lem:merge-repair` and its proof: "Let `V_i` embed a
singleton function as a function of coordinate `i` of `m_p`. The normalized strict Paley operator
`P` has … skew norm `γ^G_p` … Since `P^s_p = V_0 P V_0^*`, its difference from `D_p` has … skew
norm `γ^G_p` … For the first-coordinate difference the corresponding bounds are `ρ_b² + d_b²` and
`ρ_b²`."

For the two first-coordinate merge records `G_{s2}` of a middle block (V3's `firstLaw`, placed by
`mergeRec`), the skew part of the change `ν' − Π` at the reserved cut has norm at most
`γ^G_b = √b/(b − 1)` relative to the actual half marginal, for every `b ≥ 7` below the primes of
the block. The proof is the paper's, with the block structure done by the Fourier bound of
`Sarkozy.NormBoundsPaper.Block`:

* the old record is symmetric at the cut (`form_oldM_symm`: the `E` law is invariant under the
  layer swap), so only the skew part of the replacement counts;
* the replacement is `V_0 (⊗_p K_P) V_0^*` (`form_newM`: its form is
  `N⁻¹ ∑_{a,c} K_P(c − a) f̄(a) ḡ(c)`, `f̄ = V_0^* f` the conditional mean over the second label,
  from V3's `firstWeight = p⁻¹ k_P(y₀ − x₀) k_D(x₁ − x₀) k_D(y₁ − y₀)`, `firstWeight_eq`);
* `‖V_0^* f‖ ≤ ‖f‖` (`fbar_sq_le`, Jensen), and the skew eigenvalues of `⊗_p K_P` are at most
  `γ_b` (`form_Kskew_le`).

**`merge2_skew_paper`** is the field `Ma₂` of B8's `NormBounds`. The symmetric field `Ms₂`
(`d_b + η_b`) needs the spectral decomposition of the source operator `D_p` on ordered pairs and
is not proved here.
-/

namespace Sarkozy.NormBoundsPaper

open Finset
open scoped BigOperators

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SignedComponents
open Sarkozy.MiddleRecords (gammaG)

/-! ## The tensor law as a sum over configurations -/

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  {W : Type} [Fintype W] [DecidableEq W]

theorem expect_tensor_comm (μ : ∀ i, FiniteLaw (W → ZMod (pr i)))
    (H : (W → ∀ i, ZMod (pr i)) → ℝ) :
    (FiniteLaw.tensor μ).expect H =
      ∑ a : W → ∀ i, ZMod (pr i), (∏ i, (μ i).weight (fun w => a w i)) * H a := by
  rw [expect_tensor_eq_sum]
  exact Fintype.sum_equiv (Equiv.piComm _) _ _ (fun z => rfl)

end Tensor

/-! ## The four labels -/

section Quad

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The four labels `(x₀, x₁, y₀, y₁)` of a configuration of `Fin 2 × Fin 2` (objects × layers). -/
def quadEquiv : (X × X × X × X) ≃ (Fin 2 × Fin 2 → X) where
  toFun := quadConfig
  invFun y := (y (0, 0), y (1, 0), y (0, 1), y (1, 1))
  left_inv t := by
    obtain ⟨h1, h2, h3, h4⟩ := quadConfig_apply t
    change (quadConfig t (0, 0), quadConfig t (1, 0), quadConfig t (0, 1), quadConfig t (1, 1)) = t
    rw [h1, h2, h3, h4]
  right_inv y := by
    funext o
    obtain ⟨o1, o2⟩ := o
    fin_cases o1 <;> fin_cases o2 <;> rfl

omit [DecidableEq X] in
theorem sum_quad (G : (Fin 2 × Fin 2 → X) → ℝ) :
    ∑ y, G y = ∑ a₀, ∑ a₁, ∑ c₀, ∑ c₁, G (quadConfig (a₀, a₁, c₀, c₁)) := by
  rw [← Fintype.sum_equiv quadEquiv (fun t => G (quadConfig t)) G (fun t => rfl)]
  simp only [Fintype.sum_prod_type]

end Quad

/-! ## One prime: the first-coordinate law -/

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem firstLaw_weight (hF : ringChar (ZMod p) ≠ 2) (y : Fin 2 × Fin 2 → ZMod p) :
    (firstLaw (ZMod p) hF).weight y = firstWeight (y (0, 0), y (1, 0), y (0, 1), y (1, 1)) := by
  change ∑ t, (if quadConfig t = y then firstWeight t else 0) = _
  rw [sum_eq_single (y (0, 0), y (1, 0), y (0, 1), y (1, 1))]
  · have hq : quadConfig (y (0, 0), y (1, 0), y (0, 1), y (1, 1)) = y := quadEquiv.right_inv y
    rw [ite_eq_left hq]
  · intro t _ ht
    refine ite_eq_right fun h => ht ?_
    rw [← h]
    exact (quadEquiv.left_inv t).symm
  · exact fun h => absurd (mem_univ _) h

/-- **V3's first-coordinate weight factorizes**: `p⁻¹ k_P(y₀ − x₀) k_D(x₁ − x₀) k_D(y₁ − y₀)`. -/
theorem firstWeight_eq (a₀ a₁ c₀ c₁ : ZMod p) :
    firstWeight (a₀, a₁, c₀, c₁) =
      (1 / (p : ℝ)) * kP p (c₀ - a₀) * kD p (a₁ - a₀) * kD p (c₁ - c₀) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hp1 : (p : ℝ) - 1 ≠ 0 := by have := p_gt_one (p := p); linarith
  unfold firstWeight kP kD
  rw [ZMod.card]
  have hq : (1 : ℝ) - 1 / (p : ℝ) = ((p : ℝ) - 1) / p := by field_simp
  rw [hq]
  have e1 : (a₀ = a₁) ↔ (a₁ - a₀ = 0) :=
    ⟨fun h => by rw [h, sub_self], fun h => (sub_eq_zero.mp h).symm⟩
  have e2 : (c₀ = c₁) ↔ (c₁ - c₀ = 0) :=
    ⟨fun h => by rw [h, sub_self], fun h => (sub_eq_zero.mp h).symm⟩
  simp only [e1, e2]
  split_ifs <;> first | (simp; done) | field_simp

end Prime

/-! ## The block -/

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

omit [DecidableEq ι] in
theorem KD_nonneg (d : ∀ i, ZMod (pr i)) : 0 ≤ KD pr d := by
  unfold KD kD
  refine prod_nonneg fun i _ => ?_
  split_ifs
  · exact le_rfl
  · have : (1 : ℝ) < pr i := p_gt_one
    exact (one_div_pos.mpr (by linarith)).le

theorem sum_KD_shift (a : ∀ i, ZMod (pr i)) : ∑ c, KD pr (c - a) = 1 := by
  rw [Fintype.sum_equiv (Equiv.subRight a) (fun c => KD pr (c - a)) (KD pr) (fun c => rfl), sum_KD]

/-- The conditional mean over the second label, `f̄(a) = ∑_{a₁} K_D(a₁ − a) f(a, a₁)`. -/
noncomputable def fbar (f : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → ℝ) (a : ∀ i, ZMod (pr i)) :
    ℝ :=
  ∑ a₁, KD pr (a₁ - a) * f a a₁

/-- **Jensen**: `f̄(a)² ≤ ∑_{a₁} K_D(a₁ − a) f(a, a₁)²`. -/
theorem fbar_sq_le (f : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → ℝ) (a : ∀ i, ZMod (pr i)) :
    fbar pr f a ^ 2 ≤ ∑ a₁, KD pr (a₁ - a) * f a a₁ ^ 2 := by
  unfold fbar
  have h := Finset.sum_mul_sq_le_sq_mul_sq univ (fun a₁ => Real.sqrt (KD pr (a₁ - a)))
    (fun a₁ => Real.sqrt (KD pr (a₁ - a)) * f a a₁)
  have e1 : ∀ a₁, Real.sqrt (KD pr (a₁ - a)) * (Real.sqrt (KD pr (a₁ - a)) * f a a₁) =
      KD pr (a₁ - a) * f a a₁ := fun a₁ => by
    rw [← mul_assoc, Real.mul_self_sqrt (KD_nonneg pr _)]
  have e2 : ∀ a₁, Real.sqrt (KD pr (a₁ - a)) ^ 2 = KD pr (a₁ - a) :=
    fun a₁ => Real.sq_sqrt (KD_nonneg pr _)
  have e3 : ∀ a₁, (Real.sqrt (KD pr (a₁ - a)) * f a a₁) ^ 2 = KD pr (a₁ - a) * f a a₁ ^ 2 :=
    fun a₁ => by rw [mul_pow, e2]
  simp only [e1, e2, e3] at h
  rw [sum_KD_shift, one_mul] at h
  exact h

/-- The block first-coordinate law (V3's `blockMergeRepLaw` at `k = 2`) as a sum over the four
labels. -/
theorem expect_first (hF : ∀ i, ringChar (ZMod (pr i)) ≠ 2)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty)
    (H : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) →
      (∀ i, ZMod (pr i)) → ℝ) :
    (blockMergeRepLaw pr hF hne 2).expect (fun y => H (y (0, 0)) (y (1, 0)) (y (0, 1)) (y (1, 1))) =
      ∑ a₀, ∑ a₁, ∑ c₀, ∑ c₁, (invN pr * KP pr (c₀ - a₀) * KD pr (a₁ - a₀) * KD pr (c₁ - c₀)) *
        H a₀ a₁ c₀ c₁ := by
  have hlaw : (fun i => mergeRepLaw (hF i) (hne i) 2) = fun i => firstLaw (ZMod (pr i)) (hF i) :=
    funext fun i => ite_eq_left rfl
  unfold blockMergeRepLaw
  rw [hlaw, expect_tensor_comm, sum_quad]
  refine sum_congr rfl fun a₀ _ => sum_congr rfl fun a₁ _ => sum_congr rfl fun c₀ _ =>
    sum_congr rfl fun c₁ _ => ?_
  congr 1
  simp only [firstLaw_weight]
  obtain ⟨h1, h2, h3, h4⟩ := quadConfig_apply (a₀, a₁, c₀, c₁)
  simp only [h1, h2, h3, h4, firstWeight_eq]
  unfold invN KP KD
  rw [prod_mul_distrib, prod_mul_distrib, prod_mul_distrib]
  rfl

/-- The block form of the first-coordinate law: `N⁻¹ ∑_{a,c} K_P(c − a) f̄(a) ḡ(c)`. -/
theorem expect_first_bar (hF : ∀ i, ringChar (ZMod (pr i)) ≠ 2)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) mirrorGraph).Nonempty)
    (f g : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → ℝ) :
    (blockMergeRepLaw pr hF hne 2).expect
        (fun y => f (y (0, 0)) (y (1, 0)) * g (y (0, 1)) (y (1, 1))) =
      ∑ a, ∑ c, (invN pr * KP pr (c - a)) * (fbar pr f a * fbar pr g c) := by
  rw [expect_first pr hF hne (fun a₀ a₁ c₀ c₁ => f a₀ a₁ * g c₀ c₁)]
  refine sum_congr rfl fun a₀ _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun c₀ _ => ?_
  unfold fbar
  rw [sum_mul_sum, mul_sum]
  refine sum_congr rfl fun a₁ _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun c₁ _ => ?_
  ring

end Block

/-! ## The records at the reserved cut -/

section Cut

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The half configuration of a merge record with plus-half labels `a` (object `0`) and `b`
(object `1`). -/
def hf (s : Fin 2) (k : Fin 3) (a b : X) : reservedCut.Half → X :=
  fun v => if merge s k v.1.1 = 0 then a else b

theorem flip_fst : ∀ v : Slot, (reservedCut.flip v).1 = v.1 := by decide

theorem form_emit_gen {I : Type} [Fintype I] [DecidableEq I] (lam : FiniteLaw (I → X))
    (π : Slot → I) (R₀ R₁ : (I → X) → reservedCut.Half → X)
    (h0 : ∀ y, (fun v : reservedCut.Half => (y ∘ π) v.1) = R₀ y)
    (h1 : ∀ y, (fun v : reservedCut.Half => (y ∘ π) (reservedCut.flip v.1)) = R₁ y)
    (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam π).weight) F G =
      lam.expect (fun y => F (R₀ y) * G (R₁ y)) := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  refine FiniteLaw.expect_congr _ fun y => ?_
  simp only [h0, h1]

theorem hsq_emit_gen {I : Type} [Fintype I] [DecidableEq I] (lam : FiniteLaw (I → X))
    (π : Slot → I) (R₀ : (I → X) → reservedCut.Half → X)
    (h0 : ∀ y, (fun v : reservedCut.Half => (y ∘ π) v.1) = R₀ y)
    (F : (reservedCut.Half → X) → ℝ) :
    hsq reservedCut (plusMarginal reservedCut (emit lam π).weight) F =
      lam.expect (fun y => F (R₀ y) * F (R₀ y)) := by
  unfold hsq plusMarginal
  rw [sum_marginal_mul (fun z : Slot → X => fun v : reservedCut.Half => z v.1) (emit lam π).weight
    (fun x => F x * F x)]
  change (emit lam π).expect _ = _
  rw [expect_emit]
  refine FiniteLaw.expect_congr _ fun y => ?_
  simp only [h0]

omit [Fintype X] [DecidableEq X] in
theorem oldM_half (s : Fin 2) (k : Fin 3) (y : Fin 3 × Fin 2 → X) :
    (fun v : reservedCut.Half => (y ∘ midEmission (fun u => (merge s k u).castSucc)) v.1) =
      hf s k (y (0, 0)) (y (1, 0)) := by
  funext v
  simp only [Function.comp_apply, midEmission, half_layer v.1 v.2, hf]
  generalize merge s k v.1.1 = m
  fin_cases m <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem oldM_flip (s : Fin 2) (k : Fin 3) (y : Fin 3 × Fin 2 → X) :
    (fun v : reservedCut.Half =>
        (y ∘ midEmission (fun u => (merge s k u).castSucc)) (reservedCut.flip v.1)) =
      hf s k (y (0, 1)) (y (1, 1)) := by
  funext v
  simp only [Function.comp_apply, midEmission, flip_layer v.1 v.2, flip_fst, hf]
  generalize merge s k v.1.1 = m
  fin_cases m <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem newM_half (s : Fin 2) (k : Fin 3) (y : Fin 2 × Fin 2 → X) :
    (fun v : reservedCut.Half => (y ∘ mergeEmission s k) v.1) = hf s k (y (0, 0)) (y (1, 0)) := by
  funext v
  simp only [Function.comp_apply, mergeEmission, half_layer v.1 v.2, hf]
  generalize merge s k v.1.1 = m
  fin_cases m <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem newM_flip (s : Fin 2) (k : Fin 3) (y : Fin 2 × Fin 2 → X) :
    (fun v : reservedCut.Half => (y ∘ mergeEmission s k) (reservedCut.flip v.1)) =
      hf s k (y (0, 1)) (y (1, 1)) := by
  funext v
  simp only [Function.comp_apply, mergeEmission, flip_layer v.1 v.2, flip_fst, hf]
  generalize merge s k v.1.1 = m
  fin_cases m <;> rfl

end Cut

/-! ## The skew bound -/

section Frame

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- The old merge record `G_{sk}` as a measure. -/
noncomputable abbrev oldM (s : Fin 2) (k : Fin 3) : SlotMeasure (BlockLabel pr) :=
  signedIntegral (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
    (midEmission (fun u => (merge s k u).castSucc))).weight

/-- The value of a half function on the merge half `(a, b)`. -/
abbrev mh (s : Fin 2) (k : Fin 3) (F : (reservedCut.Half → BlockLabel pr) → ℝ)
    (a c : BlockLabel pr) : ℝ :=
  F (hf s k a c)

/-- **The old merge record is symmetric at the reserved cut** (the `E` law is invariant under the
layer swap). -/
theorem form_oldM_symm (s : Fin 2) (k : Fin 3) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (oldM pr hne s k) G F = reservedCut.form (oldM pr hne s k) F G := by
  rw [form_emit_gen _ _ _ _ (oldM_half s k) (oldM_flip s k),
    form_emit_gen _ _ _ _ (oldM_half s k) (oldM_flip s k)]
  let π : Fin 3 × Fin 2 ≃ Fin 3 × Fin 2 := Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)
  have h := blockGraphLaw_expect_auto pr (matchGraph (Fin 2)) hne.E2 π (matchGraph_auto (Fin 2) π)
    (fun y => F (hf s k (y (0, 0)) (y (1, 0))) * G (hf s k (y (0, 1)) (y (1, 1))))
  rw [← h]
  refine FiniteLaw.expect_congr _ fun y => ?_
  simp only [Function.comp_apply, π, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map,
    id_eq]
  rw [Equiv.swap_apply_left, Equiv.swap_apply_right, mul_comm]

theorem hsq_oldM (s : Fin 2) (k : Fin 3) (F : (reservedCut.Half → BlockLabel pr) → ℝ) :
    hsq reservedCut (plusMarginal reservedCut (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
        (midEmission (fun u => (merge s k u).castSucc))).weight) F =
      invN pr * ∑ a, ∑ a₁, KD pr (a₁ - a) * mh pr s k F a a₁ ^ 2 := by
  rw [hsq_emit_gen _ _ _ (oldM_half s k)]
  rw [expect_pair_match pr hne.E2 (fun a a₁ => mh pr s k F a a₁ * mh pr s k F a a₁) (by decide),
    mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun a₁ _ => ?_
  ring

theorem form_newM (s : Fin 2) (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (signedIntegral (mergeRec pr h (s, 2)).weight) F G =
      ∑ a, ∑ c, (invN pr * KP pr (c - a)) *
        (fbar pr (mh pr s 2 F) a * fbar pr (mh pr s 2 G) c) := by
  unfold mergeRec
  rw [form_emit_gen _ _ _ _ (newM_half s 2) (newM_flip s 2)]
  exact expect_first_bar pr h.ringChar_ne (blockMirror_nonempty pr h) (mh pr s 2 F) (mh pr s 2 G)

/-- **The skew part of the first-coordinate change is the convolution form of `K^a` on the
conditional means.** -/
theorem form_merge2_skew (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ)
    (F G : (reservedCut.Half → BlockLabel pr) → ℝ) :
    reservedCut.form (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .skew)
        F G =
      invN pr * ∑ a, ∑ c, Kskew pr (c - a) * fbar pr (mh pr s 2 F) a * fbar pr (mh pr s 2 G) c := by
  have hS : ∀ L₁ L₂ : SlotMeasure (BlockLabel pr), ∀ F G,
      reservedCut.form (L₁ - L₂) F G = reservedCut.form L₁ F G - reservedCut.form L₂ F G :=
    fun _ _ _ _ => rfl
  change reservedCut.form (skewPart reservedCut
    (signedIntegral (mergeRec pr h (s, 2)).weight - oldM pr hne s 2)) F G = _
  unfold skewPart
  rw [form_smul, hS, form_reflect, hS, hS, form_oldM_symm, form_newM, form_newM,
    sum_swap pr (KP pr) (fbar pr (mh pr s 2 F)) (fbar pr (mh pr s 2 G))]
  rw [show ∀ x y z : ℝ, x - z - (y - z) = x - y from fun x y z => by ring]
  rw [← sum_sub_distrib, mul_sum, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sub_distrib, mul_sum, mul_sum]
  refine sum_congr rfl fun c _ => ?_
  rw [Kskew_eq]
  ring

/-- **`lem:merge-repair`, skew norm of the first-coordinate replacement**: `γ_b` for every
`b ≥ 7` below the primes of the block. -/
theorem merge2_skew (s : Fin 2) (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ}
    (hb7 : 7 ≤ b') (hbp : ∀ i, b' ≤ (pr i : ℝ)) :
    FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .skew) (gam b') := by
  have hγ : 0 ≤ gam b' := by
    unfold gam
    exact div_nonneg (Real.sqrt_nonneg _) (by linarith)
  refine ⟨hγ, fun F G => ?_⟩
  change |_| ≤ gam b' * Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s 2 u).castSucc))).weight) F) *
    Real.sqrt (hsq reservedCut (plusMarginal reservedCut
    (emit (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (midEmission (fun u => (merge s 2 u).castSucc))).weight) G)
  rw [form_merge2_skew pr h hne root W I hr b s C t F G, hsq_oldM pr hne s 2 F,
    hsq_oldM pr hne s 2 G, abs_mul, abs_of_pos (invN_pos pr)]
  have hN := invN_pos pr
  have hK := form_Kskew_le h.mod4 hb7 hbp (fbar pr (mh pr s 2 F)) (fbar pr (mh pr s 2 G))
  have hJ : ∀ U : (reservedCut.Half → BlockLabel pr) → ℝ,
      ∑ a, fbar pr (mh pr s 2 U) a ^ 2 ≤ ∑ a, ∑ a₁, KD pr (a₁ - a) * mh pr s 2 U a a₁ ^ 2 :=
    fun U => sum_le_sum fun a _ => fbar_sq_le pr (mh pr s 2 U) a
  have hs : Real.sqrt (invN pr) * Real.sqrt (invN pr) = invN pr := Real.mul_self_sqrt hN.le
  rw [Real.sqrt_mul hN.le, Real.sqrt_mul hN.le]
  calc invN pr * |∑ a, ∑ c, Kskew pr (c - a) * fbar pr (mh pr s 2 F) a *
        fbar pr (mh pr s 2 G) c|
      ≤ invN pr * (gam b' * Real.sqrt (∑ a, fbar pr (mh pr s 2 F) a ^ 2) *
          Real.sqrt (∑ c, fbar pr (mh pr s 2 G) c ^ 2)) :=
        mul_le_mul_of_nonneg_left hK hN.le
    _ ≤ invN pr * (gam b' * Real.sqrt (∑ a, ∑ a₁, KD pr (a₁ - a) * mh pr s 2 F a a₁ ^ 2) *
          Real.sqrt (∑ a, ∑ a₁, KD pr (a₁ - a) * mh pr s 2 G a a₁ ^ 2)) := by
        refine mul_le_mul_of_nonneg_left ?_ hN.le
        refine mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (hJ F)) hγ)
          (Real.sqrt_le_sqrt (hJ G)) (Real.sqrt_nonneg _)
          (mul_nonneg hγ (Real.sqrt_nonneg _))
    _ = (Real.sqrt (invN pr) * Real.sqrt (invN pr)) *
          (gam b' * Real.sqrt (∑ a, ∑ a₁, KD pr (a₁ - a) * mh pr s 2 F a a₁ ^ 2) *
          Real.sqrt (∑ a, ∑ a₁, KD pr (a₁ - a) * mh pr s 2 G a a₁ ^ 2)) := by rw [hs]
    _ = _ := by ring

/-- **The field `Ma₂` of `NormBounds` at the paper's constant** (`lem:merge-repair`):
`γ^G_b = √b/(b − 1)`, `b ≥ 7` below every prime of the block. -/
theorem merge2_skew_paper (C : FoldComponents pr hne) (t : ℝ) {b' : ℝ} (hb7 : 7 ≤ b')
    (hbp : ∀ i, b' ≤ (pr i : ℝ)) (s : Fin 2) :
    FormBound reservedCut
      (mOf (middleFrame pr hne root W I hr b h) (.inr (.inr (.inl (s, 2)))))
      (foldChange pr h hne root W I hr b C t (.inr (.inr (.inl (s, 2)))) .skew) (gammaG b') :=
  merge2_skew pr h hne root W I hr b s C t hb7 hbp

end Frame

end Sarkozy.NormBoundsPaper

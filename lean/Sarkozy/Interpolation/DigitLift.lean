module

public import Sarkozy.Interpolation.SquarePairEndpoints

/-!
# The prime-square form of `lem:density:edge-moment`

`paper/sections/30_density_moment_upgrade.tex`, `lem:density:edge-moment`, last sentence: "The
conclusion persists on `ℤ/p²ℤ` when each label is written as `x + py` with `x, y ∈ 𝔽_p`, the two
`y`-coordinates are independent and uniform, and the pair of `x`-coordinates has either of these
laws." Proof: "first average each input over its high digit; this is an `L^r` contraction."

General form (`liftWeight_unitMixed`): let `φ : Z → X` have all fibres of size `m > 0`. Lift a
weight `π` on `Fin d → X` to `Fin d → Z` by making each label uniform in its fibre given its
image, independently (`liftWeight φ m π z = π(φ ∘ z)/m^d`). Then
`∑_z liftWeight z ∏_v f_v(z_v) = ∑_x π x ∏_v F_v(x_v)` with the fibre averages `F_v`
(`sum_liftWeight`), and `‖F_v‖_r ≤ ‖f_v‖_r` for `r ≥ 1` (`conditioningNorm_fibreAvg_le`,
Jensen). So unit mixed `L^r` lifts.

For `ℤ/p²ℤ`, `φ` is the reduction `lowDigit p : ℤ/p²ℤ → 𝔽_p`, whose fibres have `p` elements
(`card_lowDigit_fibre`). `digitLaw_eq_liftWeight` identifies the lifted weight with the paper's
law: labels `x_v + p y_v` (as in `Construction.cliqueDigit`), `x ∼ π`, `y` independent uniform on
`Fin p`. `square_pair_moment_prime_square` is the prime-square statement for both class laws,
with only the gate as hypothesis.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Interpolation

section Lift

variable {X Z : Type*} [Fintype X] [Fintype Z] [DecidableEq X]

/-- The fibre average `F(a) = (1/m) ∑_{φ z = a} f(z)`. -/
noncomputable def fibreAvg (φ : Z → X) (m : ℕ) (f : Z → ℝ) (a : X) : ℝ :=
  (∑ z ∈ univ.filter (fun z => φ z = a), f z) / m

/-- The lift of a weight `π` on `Fin d → X` along `φ : Z → X` with fibres of size `m`: given the
images, the labels are independent and uniform in their fibres. -/
noncomputable def liftWeight {d : ℕ} (φ : Z → X) (m : ℕ) (π : (Fin d → X) → ℝ) :
    (Fin d → Z) → ℝ :=
  fun z => π (fun v => φ (z v)) / (m : ℝ) ^ d

/-- Multilinear forms of the lifted weight are those of `π` at the fibre averages. -/
theorem sum_liftWeight {d : ℕ} (φ : Z → X) (m : ℕ) (π : (Fin d → X) → ℝ)
    (f : Fin d → Z → ℝ) :
    ∑ z, liftWeight φ m π z * ∏ v, f v (z v) = ∑ x, π x * ∏ v, fibreAvg φ m (f v) (x v) := by
  rw [← Finset.sum_fiberwise univ (fun z : Fin d → Z => fun v => φ (z v))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hfilt : (univ.filter fun z : Fin d → Z => (fun v => φ (z v)) = x) =
      Fintype.piFinset (fun v => univ.filter fun w => φ w = x v) := by
    ext z
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
  have hlw : ∀ z ∈ (univ.filter fun z : Fin d → Z => (fun v => φ (z v)) = x),
      liftWeight φ m π z * ∏ v, f v (z v) = π x / (m : ℝ) ^ d * ∏ v, f v (z v) := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    simp only [liftWeight, hz]
  rw [Finset.sum_congr rfl hlw, ← Finset.mul_sum, hfilt, ← Finset.prod_univ_sum]
  simp only [fibreAvg]
  rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  ring

theorem card_eq_of_fibres (φ : Z → X) {m : ℕ}
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) :
    Fintype.card Z = m * Fintype.card X := by
  rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := φ) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))]
  simp only [hfib, sum_const, card_univ, smul_eq_mul]
  ring

omit [Fintype X] in
/-- Jensen on a fibre: `|F(a)|^r ≤ (1/m) ∑_{φ z = a} |f z|^r`. -/
theorem fibreAvg_rpow_le (φ : Z → X) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) {r : ℝ} (hr : 1 ≤ r) (f : Z → ℝ)
    (a : X) :
    |fibreAvg φ m f a| ^ r ≤ (∑ z ∈ univ.filter (fun z => φ z = a), |f z| ^ r) / m := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have h1 : |fibreAvg φ m f a| ≤ ∑ z ∈ univ.filter (fun z => φ z = a), (m : ℝ)⁻¹ * |f z| := by
    unfold fibreAvg
    rw [abs_div, abs_of_pos hm', div_eq_inv_mul, ← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (inv_nonneg.mpr hm'.le)
  have hw : ∑ z ∈ univ.filter (fun z => φ z = a), (m : ℝ)⁻¹ = 1 := by
    rw [sum_const, hfib a, nsmul_eq_mul]
    field_simp
  have h2 := Real.rpow_arith_mean_le_arith_mean_rpow (univ.filter (fun z => φ z = a))
    (fun _ => (m : ℝ)⁻¹) (fun z => |f z|) (fun _ _ => inv_nonneg.mpr hm'.le) hw
    (fun _ _ => abs_nonneg _) hr
  calc |fibreAvg φ m f a| ^ r
      ≤ (∑ z ∈ univ.filter (fun z => φ z = a), (m : ℝ)⁻¹ * |f z|) ^ r :=
        Real.rpow_le_rpow (abs_nonneg _) h1 (by linarith)
    _ ≤ ∑ z ∈ univ.filter (fun z => φ z = a), (m : ℝ)⁻¹ * |f z| ^ r := h2
    _ = (∑ z ∈ univ.filter (fun z => φ z = a), |f z| ^ r) / m := by
        rw [← Finset.mul_sum, div_eq_inv_mul]

/-- **Averaging over fibres is an `L^r` contraction** (`r ≥ 1`, uniform norms). -/
theorem conditioningNorm_fibreAvg_le [Nonempty X] (φ : Z → X) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) {r : ℝ} (hr : 1 ≤ r) (f : Z → ℝ) :
    DensityUpgrade.conditioningNorm r (fibreAvg φ m f) ≤ DensityUpgrade.conditioningNorm r f := by
  have hm' : (0 : ℝ) < m := by exact_mod_cast hm
  have hX : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  unfold DensityUpgrade.conditioningNorm
  refine Real.rpow_le_rpow (div_nonneg (Finset.sum_nonneg fun _ _ =>
    Real.rpow_nonneg (abs_nonneg _) _) hX.le) ?_ (inv_nonneg.mpr (by linarith))
  rw [card_eq_of_fibres φ hfib]
  have hsum : ∑ a, |fibreAvg φ m f a| ^ r ≤ (∑ z, |f z| ^ r) / m := by
    calc ∑ a, |fibreAvg φ m f a| ^ r
        ≤ ∑ a, (∑ z ∈ univ.filter (fun z => φ z = a), |f z| ^ r) / m :=
          Finset.sum_le_sum fun a _ => fibreAvg_rpow_le φ hm hfib hr f a
      _ = (∑ a, ∑ z ∈ univ.filter (fun z => φ z = a), |f z| ^ r) / m := by
          rw [Finset.sum_div]
      _ = (∑ z, |f z| ^ r) / m := by rw [Finset.sum_fiberwise]
  calc (∑ a, |fibreAvg φ m f a| ^ r) / Fintype.card X
      ≤ ((∑ z, |f z| ^ r) / m) / Fintype.card X := div_le_div_of_nonneg_right hsum hX.le
    _ = (∑ z, |f z| ^ r) / ((m * Fintype.card X : ℕ) : ℝ) := by
        push_cast
        rw [div_div]

/-- **Unit mixed `L^r` lifts along equal-fibre maps** (`r ≥ 1`). -/
theorem liftWeight_unitMixed [Nonempty X] {d : ℕ} (φ : Z → X) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) (π : (Fin d → X) → ℝ) {r : ℝ}
    (hr : 1 ≤ r) (h : DensityUpgrade.conditioningUnitMixed π r) :
    DensityUpgrade.conditioningUnitMixed (liftWeight φ m π) r := by
  intro f
  rw [sum_liftWeight]
  refine (h fun v => fibreAvg φ m (f v)).trans ?_
  exact Finset.prod_le_prod₀ (fun v _ => DensityUpgrade.conditioningNorm_nonneg _ _)
    (fun v _ => conditioningNorm_fibreAvg_le φ hm hfib hr (f v))

omit [Fintype X] in
theorem fibreAvg_one (φ : Z → X) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) (a : X) :
    fibreAvg φ m (fun _ => (1 : ℝ)) a = 1 := by
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold fibreAvg
  rw [sum_const, hfib a, nsmul_eq_mul, mul_one, div_self hm']

/-- The lifted law of a `FiniteLaw` (`liftWeight` is a probability weight). -/
noncomputable def liftLaw {d : ℕ} (φ : Z → X) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) (μ : FiniteLaw (Fin d → X)) :
    FiniteLaw (Fin d → Z) where
  weight := liftWeight φ m μ.weight
  nonneg z := div_nonneg (μ.nonneg _) (by positivity)
  total := by
    have h := sum_liftWeight φ m μ.weight (fun _ _ => (1 : ℝ))
    simp only [prod_const_one, mul_one, fibreAvg_one φ hm hfib] at h
    rw [h]
    exact μ.total

/-- **Unit mixed `L^r` lifts**, `FiniteLaw` form (`MixedLpBound … 1`). -/
theorem liftLaw_mixedLpBound [Nonempty X] [Nonempty Z] {d : ℕ} (φ : Z → X) {m : ℕ} (hm : 0 < m)
    (hfib : ∀ a, (univ.filter fun z => φ z = a).card = m) (μ : FiniteLaw (Fin d → X)) {r : ℝ}
    (hr : 1 ≤ r) (h : MixedLpBound μ r 1) : MixedLpBound (liftLaw φ hm hfib μ) r 1 := by
  rw [EdgeGate.mixedLpBound_iff_conditioningUnitMixed] at h ⊢
  exact liftWeight_unitMixed φ hm hfib μ.weight hr h

end Lift

section PrimeSquare

open Sarkozy.InvariantPair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

/-- The low digit `ℤ/p²ℤ → 𝔽_p` (reduction mod `p`). -/
noncomputable def lowDigit (p : ℕ) : ZMod (p ^ 2) →+* ZMod p :=
  ZMod.castHom (dvd_pow_self p two_ne_zero) (ZMod p)

/-- Each residue class mod `p` in `ℤ/p²ℤ` has `p` elements. -/
theorem card_lowDigit_fibre (a : ZMod p) :
    (univ.filter fun z : ZMod (p ^ 2) => lowDigit p z = a).card = p := by
  have hsurj : Function.Surjective (lowDigit p) := ZMod.castHom_surjective _
  have heq : ∀ b, (univ.filter fun z : ZMod (p ^ 2) => lowDigit p z = b).card =
      (univ.filter fun z : ZMod (p ^ 2) => lowDigit p z = 0).card := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range (lowDigit p) (hsurj b) (hsurj 0)
  have htot := card_eq_sum_card_fiberwise (f := lowDigit p) (s := univ) (t := univ)
    (fun _ _ => mem_coe.mpr (mem_univ _))
  rw [Finset.sum_congr rfl (fun b _ => heq b), sum_const, card_univ, card_univ, ZMod.card,
    ZMod.card, smul_eq_mul] at htot
  rw [heq a]
  have hp0 : 0 < p := hp.out.pos
  have : p * p = p * (univ.filter fun z : ZMod (p ^ 2) => lowDigit p z = 0).card := by
    rw [← htot]
    ring
  exact (Nat.eq_of_mul_eq_mul_left hp0 this).symm

/-- The label `x + p k` of `ℤ/p²ℤ` with low digit `x` and high digit `k` (the form of
`Construction.cliqueDigit`). -/
noncomputable def digit (p : ℕ) (x : ZMod p) (k : Fin p) : ZMod (p ^ 2) :=
  ((x.val + p * k.val : ℕ) : ZMod (p ^ 2))

theorem lowDigit_digit (x : ZMod p) (k : Fin p) : lowDigit p (digit p x k) = x := by
  rw [digit, lowDigit, map_natCast, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul,
    add_zero, ZMod.natCast_zmod_val]

theorem val_digit (x : ZMod p) (k : Fin p) : (digit p x k).val = x.val + p * k.val := by
  unfold digit
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
  have hx := ZMod.val_lt x
  have hk : k.val + 1 ≤ p := k.isLt
  have h2 : p * (k.val + 1) ≤ p * p := Nat.mul_le_mul_left p hk
  nlinarith

/-- **The lifted weight is the digit law.** If the low digits `x` have law `π` and the high
digits `k` are independent and uniform on `Fin p`, the labels `x_v + p k_v` have law
`liftWeight (lowDigit p) p π`. -/
theorem digitLaw_eq_liftWeight {d : ℕ} (π : (Fin d → ZMod p) → ℝ)
    (F : (Fin d → ZMod (p ^ 2)) → ℝ) :
    ∑ x : Fin d → ZMod p, ∑ k : Fin d → Fin p,
        π x * ((p : ℝ) ^ d)⁻¹ * F (fun v => digit p (x v) (k v)) =
      ∑ z, liftWeight (lowDigit p) p π z * F z := by
  rw [← Finset.sum_fiberwise univ (fun z : Fin d → ZMod (p ^ 2) => fun v => lowDigit p (z v))]
  refine Finset.sum_congr rfl fun x _ => ?_
  have hlw : ∀ z ∈ (univ.filter fun z : Fin d → ZMod (p ^ 2) =>
      (fun v => lowDigit p (z v)) = x),
      liftWeight (lowDigit p) p π z * F z = π x * ((p : ℝ) ^ d)⁻¹ * F z := by
    intro z hz
    simp only [mem_filter, mem_univ, true_and] at hz
    simp only [liftWeight, hz, div_eq_mul_inv]
  rw [Finset.sum_congr rfl hlw, ← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  set D : (Fin d → Fin p) → (Fin d → ZMod (p ^ 2)) := fun k v => digit p (x v) (k v) with hD
  have hinj : Function.Injective D := by
    intro k k' h
    funext v
    have h1 := congrFun h v
    simp only [hD] at h1
    have hv := congrArg ZMod.val h1
    rw [val_digit, val_digit] at hv
    have hp0 : 0 < p := hp.out.pos
    exact Fin.ext (Nat.eq_of_mul_eq_mul_left hp0 (by omega))
  have hfilt : (univ.filter fun z : Fin d → ZMod (p ^ 2) => (fun v => lowDigit p (z v)) = x) =
      Fintype.piFinset (fun v => univ.filter fun w => lowDigit p w = x v) := by
    ext z
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
  have himage : univ.image D =
      univ.filter fun z : Fin d → ZMod (p ^ 2) => (fun v => lowDigit p (z v)) = x := by
    apply Finset.eq_of_subset_of_card_le
    · intro z hz
      obtain ⟨k, _, rfl⟩ := mem_image.mp hz
      simp only [mem_filter, mem_univ, true_and, hD]
      funext v
      exact lowDigit_digit (x v) (k v)
    · rw [card_image_of_injective _ hinj, card_univ, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_fin, hfilt, Fintype.card_piFinset]
      simp only [card_lowDigit_fibre, prod_const, card_univ, Fintype.card_fin, le_refl]
  rw [← himage, Finset.sum_image (fun k _ k' _ h => hinj h)]

/-- **`lem:density:edge-moment`, prime-square form.** Labels of `ℤ/p²ℤ` written `x + py`: the low
digits have a class law (strict square pairs, `c = 1`, or nonsquare pairs, `c = −1`) and, given
them, the labels are independent and uniform in their residue classes (equivalently the high
digits are independent and uniform, `digitLaw_eq_liftWeight`). Under the gate the law has unit
mixed `L^{1+1/j}`. -/
theorem square_pair_moment_prime_square (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) {j : ℕ}
    (hj : 1 ≤ j)
    (hgate : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1) :
    DensityUpgrade.conditioningUnitMixed
      (liftWeight (lowDigit p) p
        (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight)
      (1 + 1 / (j : ℝ)) := by
  have h := square_pair_moment_proved hp2 hc hj hgate
  rw [EdgeGate.mixedLpBound_iff_conditioningUnitMixed] at h
  have hr : (1 : ℝ) ≤ 1 + 1 / (j : ℝ) := by
    have : (0 : ℝ) ≤ 1 / (j : ℝ) := by positivity
    linarith
  exact liftWeight_unitMixed (lowDigit p) hp.out.pos card_lowDigit_fibre _ hr h

/-- **`lem:density:edge-moment`, prime-square form, as a `FiniteLaw`**: the digit-pair law on
`ℤ/p²ℤ` (low digits a class law, high digits independent uniform) satisfies
`MixedLpBound … (1 + 1/j) 1` under the gate. -/
theorem square_pair_moment_prime_square_law (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1)
    {j : ℕ} (hj : 1 ≤ j)
    (hgate : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1) :
    MixedLpBound (liftLaw (lowDigit p) hp.out.pos card_lowDigit_fibre
      (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc))) (1 + 1 / (j : ℝ)) 1 := by
  rw [EdgeGate.mixedLpBound_iff_conditioningUnitMixed]
  exact square_pair_moment_prime_square hp2 hc hj hgate

/-- **The pair input of `lem:density:clique36`, on each band.** For a prime `p ≥ 2^b` of band
`i` (`EdgeGate.bandB`, `EdgeGate.bandJ`), both class laws on `𝔽_p`, and their digit lifts to
`ℤ/p²ℤ`, have unit mixed `L^{1+1/j_b}`. The gate is `EdgeGate.edge_gate_band`. -/
theorem square_pair_moment_band (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (i : Fin 31)
    (hpb : (2 : ℝ) ^ EdgeGate.bandB i ≤ p) :
    MixedLpBound (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc))
        (1 + 1 / (EdgeGate.bandJ i : ℝ)) 1 ∧
      MixedLpBound (liftLaw (lowDigit p) hp.out.pos card_lowDigit_fibre
        (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)))
        (1 + 1 / (EdgeGate.bandJ i : ℝ)) 1 := by
  have hgate := EdgeGate.edge_gate_band i hpb
  rw [← one_div_pow] at hgate
  exact ⟨square_pair_moment_proved hp2 hc (EdgeGate.one_le_bandJ i) hgate,
    square_pair_moment_prime_square_law hp2 hc (EdgeGate.one_le_bandJ i) hgate⟩

end PrimeSquare

end Sarkozy.Interpolation

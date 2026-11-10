module

public import Sarkozy.Interpolation.EdgeInterp
public import Sarkozy.Certificates.SquarePairMoment

/-!
# The endpoint bounds for the square-pair laws (`lem:density:edge-moment`, step 1)

`paper/sections/30_density_moment_upgrade.tex`, proof of `lem:density:edge-moment`: "Relative to
uniform probability measure, the centered bilinear form of the pair law has norm at most
`L = (p+1)/(p−1)` on `L¹ × L¹` and at most `ρ = (√p+1)/(p−1) = 1/(√p−1)` on `L² × L²`."

Here the pair law is the uniform law on `classSet c = {z : χ(z₁ − z₀) = c}`, `c = ±1` (strict
square pairs, nonsquare pairs), as in `EdgeGate.square_pair_moment`. For every odd prime `p`,
either residue of `p` mod `4`, and either `c`:

* `class_L1`: the `L¹ × L¹` bound `L`. The kernel of the centred form is
  `π(a, b) − 1/p² ∈ {(p+1)/(p²(p−1)), −1/p²}` (`card_classSet`: `|classSet c| = p(p−1)/2`);
* `class_L2`: the `L² × L²` bound `1/(√p − 1)`. With `2·[χ(d) = c] = [d ≠ 0] + c χ(d)`,
  `p(p−1) B(f,g) = −Cov-term + c ∑_a f(a) ∑_b χ(b−a) g(b)` (`class_centredForm`). The first term
  is at most `‖f‖₂‖g‖₂ · p` by Cauchy–Schwarz; the second at most `√p · p ‖f‖₂‖g‖₂` by
  Cauchy–Schwarz and WP-S's Paley-operator identity `TraceMixing.norm_paleyOp`
  (`‖P g‖₂² = p⁻¹(‖g‖₂² − (E g)²)`). Sum: `(1 + √p)/(p − 1) = 1/(√p − 1)`.

Headline:
* `square_pair_interp`: the interpolated bound `hinterp` of `EdgeGate.square_pair_moment`,
  proved for both class laws;
* `square_pair_moment_proved`: `lem:density:edge-moment` (the `𝔽_p` part) for both class laws,
  with only the gate `eq:density:edge-integer-gate` as hypothesis;
* `invariant_pair_edge_proved`: `lem:density:invariant-pair` in the form of
  `EdgeGate.invariant_pair_edge`, with only the gate as hypothesis.

Not covered: the prime-square extension of `lem:density:edge-moment` ("The conclusion persists on
`ℤ/p²ℤ` …").
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.Interpolation

open Sarkozy.InvariantPair

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [hp : Fact p.Prime]

local notation "χ" => quadraticChar (ZMod p)

/-- `|classSet c| = p(p − 1)/2`. -/
theorem card_classSet (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) :
    2 * ((classSet (p := p) c).card : ℝ) = p * (p - 1) := by
  set S := classSet (p := p) c with hSdef
  have hfib0 : ∀ a' : ZMod p, ((univ.filter (fun x : Fin 2 → ZMod p => x 0 = a')) ∩ S).card =
      (univ.filter fun b : ZMod p => χ (b - a') = c).card := by
    intro a'
    apply Finset.card_nbij' (fun x => x 1) (fun b => ![a', b])
    · intro x hx
      simp only [Finset.mem_coe, mem_inter, mem_filter, mem_univ, true_and, hSdef, classSet] at hx
      simp only [mem_filter, mem_univ, true_and, Finset.mem_coe]
      rw [← hx.1]
      exact hx.2
    · intro b hb
      simp only [mem_filter, mem_univ, true_and, Finset.mem_coe] at hb
      simp only [mem_inter, mem_filter, mem_univ, true_and, hSdef, classSet, Finset.mem_coe,
        Matrix.cons_val_zero, Matrix.cons_val_one]
      first | exact ⟨rfl, hb⟩ | exact hb
    · intro x hx
      simp only [Finset.mem_coe, mem_inter, mem_filter, mem_univ, true_and] at hx
      funext k
      fin_cases k
      · simp [hx.1]
      · simp
    · intro b _
      simp
  have hScard : 2 * (S.card : ℤ) = p * (p - 1) := by
    have hsplit : S = (univ : Finset (ZMod p)).biUnion
        (fun a' => (univ.filter (fun x : Fin 2 → ZMod p => x 0 = a')) ∩ S) := by
      ext x
      simp
    rw [hsplit, card_biUnion]
    · push_cast
      rw [mul_sum]
      simp_rw [hfib0, EdgeGate.card_class_partners hp2 hc]
      rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    · intro a₁ _ a₂ _ hne
      rw [Function.onFun, disjoint_left]
      intro x hx1 hx2
      simp only [mem_inter, mem_filter, mem_univ, true_and] at hx1 hx2
      exact hne (hx1.1.symm.trans hx2.1)
  exact_mod_cast hScard

/-- The class law at a pair: `π(a, b) = 2/(p(p−1))` if `χ(b − a) = c`, else `0`. -/
theorem classWeight_pair (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (a b : ZMod p) :
    (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight ![a, b] =
      if χ (b - a) = c then 2 / ((p : ℝ) * (p - 1)) else 0 := by
  have hcard := card_classSet hp2 hc
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hS : ((classSet (p := p) c).card : ℝ) = p * (p - 1) / 2 := by linarith
  have hmem : ![a, b] ∈ classSet (p := p) c ↔ χ (b - a) = c := by
    simp [classSet]
  simp only [uniformOn, hmem]
  rw [hS]
  split_ifs
  · rw [one_div_div]
  · rfl

/-- **The class-law sum**: `∑_x π(x) f(x₀) g(x₁) =
(S_f S_g − ∑ f g + c ∑_a f(a) ∑_b χ(b − a) g(b)) / (p(p − 1))`. -/
theorem class_sum (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (f g : ZMod p → ℝ) :
    ∑ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight x *
        (f (x 0) * g (x 1)) =
      ((∑ a, f a) * (∑ b, g b) - ∑ a, f a * g a +
        c * ∑ a, f a * ∑ b, (χ (b - a) : ℝ) * g b) / ((p : ℝ) * (p - 1)) := by
  rw [sum_pair]
  simp_rw [classWeight_pair hp2 hc]
  have hterm : ∀ a b : ZMod p,
      (if χ (b - a) = c then 2 / ((p : ℝ) * (p - 1)) else 0) * f a * g b =
        (f a * g b - (if a = b then f a * g b else 0) +
          c * ((χ (b - a) : ℝ) * (f a * g b))) / ((p : ℝ) * (p - 1)) := by
    intro a b
    by_cases hab : a = b
    · subst hab
      have hc0 : (0 : ℤ) ≠ c := by
        rcases hc with rfl | rfl <;> norm_num
      simp [hc0]
    · have hne : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
      rcases quadraticChar_dichotomy hne with h | h <;> rcases hc with rfl | rfl <;>
        simp [h, hab] <;> ring
  simp_rw [hterm]
  have e1 : (∑ a, f a) * (∑ b, g b) = ∑ a, ∑ b, f a * g b := Finset.sum_mul_sum _ _ _ _
  have e2 : ∑ a, f a * g a = ∑ a, ∑ b, (if a = b then f a * g b else 0) := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_ite_eq]
    simp
  have e3 : (c : ℝ) * ∑ a, f a * ∑ b, (χ (b - a) : ℝ) * g b =
      ∑ a, ∑ b, (c : ℝ) * ((χ (b - a) : ℝ) * (f a * g b)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [e1, e2, e3, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, Finset.sum_div]

/-- **The centred form of a class law**:
`p(p−1) B(f,g) = −∑_a (f(a) − E f) g(a) + c ∑_a f(a) ∑_b χ(b − a) g(b)`. -/
theorem class_centredForm (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (f g : ZMod p → ℝ) :
    centredForm (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight f g =
      (-(∑ a, (f a - (∑ b, f b) / p) * g a) +
        c * ∑ a, f a * ∑ b, (χ (b - a) : ℝ) * g b) / ((p : ℝ) * (p - 1)) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hX : ∑ a, (f a - (∑ b, f b) / p) * g a =
      ∑ a, f a * g a - (∑ b, f b) / p * ∑ a, g a := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
  unfold centredForm
  rw [class_sum hp2 hc, ZMod.card, hX]
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp10 : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp
  ring

/-- `∑_a (f(a) − E f)² = ∑ f² − (∑ f)²/p ≤ ∑ f²`. -/
theorem sum_centred_sq_le (f : ZMod p → ℝ) :
    ∑ a, (f a - (∑ b, f b) / p) ^ 2 ≤ ∑ a, f a ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have h : ∑ a, (f a - (∑ b, f b) / p) ^ 2 = ∑ a, f a ^ 2 - (∑ b, f b) ^ 2 / p := by
    have hexp : ∀ a, (f a - (∑ b, f b) / p) ^ 2 =
        f a ^ 2 - 2 * ((∑ b, f b) / p) * f a + ((∑ b, f b) / p) ^ 2 := fun a => by ring
    simp only [hexp, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
    field_simp
    ring
  rw [h]
  have : 0 ≤ (∑ b, f b) ^ 2 / p := by positivity
  linarith

/-- **The `L¹ × L¹` endpoint** (`lem:density:edge-moment`, step 1): the centred form of either
class law has `L¹ × L¹` norm at most `(p + 1)/(p − 1)`. -/
theorem class_L1 (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (f g : ZMod p → ℝ) :
    |centredForm (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight f g| ≤
      ((p + 1) / (p - 1) : ℝ) * DensityUpgrade.conditioningNorm 1 f *
        DensityUpgrade.conditioningNorm 1 g := by
  rw [centredForm_eq_rbil]
  refine L1_uniform_of_kernel_le _ (fun a b => ?_) f g
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hp10 : (0 : ℝ) < p - 1 := by linarith
  simp only [centredKernel, classWeight_pair hp2 hc, ZMod.card]
  split_ifs
  · -- `2/(p(p−1)) − 1/p² = (p+1)/(p²(p−1)) > 0`
    have heq : 2 / ((p : ℝ) * (p - 1)) - (p : ℝ)⁻¹ * (p : ℝ)⁻¹ =
        ((p + 1) / (p - 1) : ℝ) * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by
      field_simp
      ring
    rw [heq, abs_of_nonneg (by positivity)]
  · rw [zero_sub, abs_neg, abs_of_nonneg (by positivity)]
    have hL : (1 : ℝ) ≤ (p + 1) / (p - 1) := by
      rw [le_div_iff₀ hp10]
      linarith
    have hpp : (0 : ℝ) ≤ (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by positivity
    calc (p : ℝ)⁻¹ * (p : ℝ)⁻¹ = 1 * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by ring
      _ ≤ ((p + 1) / (p - 1) : ℝ) * (p : ℝ)⁻¹ * (p : ℝ)⁻¹ := by
        rw [mul_assoc, mul_assoc]
        exact mul_le_mul_of_nonneg_right hL hpp

/-- **The `L² × L²` endpoint** (`lem:density:edge-moment`, step 1, the Paley character-spectrum
bound): the centred form of either class law has `L² × L²` norm at most
`(√p + 1)/(p − 1) = 1/(√p − 1)`, for every odd prime `p`. -/
theorem class_L2 (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) (f g : ZMod p → ℝ) :
    |centredForm (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight f g| ≤
      (1 / (Real.sqrt p - 1)) * DensityUpgrade.conditioningNorm 2 f *
        DensityUpgrade.conditioningNorm 2 g := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hp3 : (3 : ℝ) ≤ p := by
    have h2 := hp.out.two_le
    have : 3 ≤ p := by omega
    exact_mod_cast this
  set n : ℝ := (p : ℝ) with hn_def
  have hn0 : 0 < n := by linarith
  set s := Real.sqrt n with hs_def
  have hs2 : s ^ 2 = n := Real.sq_sqrt hn0.le
  have hs1 : 1 < s := by
    rw [hs_def, show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) (by linarith)
  set A := ∑ a, f a ^ 2 with hA_def
  set G := ∑ a, g a ^ 2 with hG_def
  have hA : 0 ≤ A := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hG : 0 ≤ G := Finset.sum_nonneg fun _ _ => sq_nonneg _
  set X := ∑ a, (f a - (∑ b, f b) / n) * g a with hX_def
  set Y := ∑ a, f a * ∑ b, (χ (b - a) : ℝ) * g b with hY_def
  -- Cauchy–Schwarz for the covariance term
  have hX2 : X ^ 2 ≤ A * G := by
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun a => f a - (∑ b, f b) / n) g
    have hle := sum_centred_sq_le (p := p) f
    calc X ^ 2 ≤ (∑ a, (f a - (∑ b, f b) / n) ^ 2) * G := hcs
      _ ≤ A * G := mul_le_mul_of_nonneg_right hle hG
  -- Cauchy–Schwarz and the Paley operator for the character term
  have hPdef : ∀ a : ZMod p, ∑ b, (χ (b - a) : ℝ) * g b = n * TraceMixing.paleyOp g a := by
    intro a
    unfold TraceMixing.paleyOp
    rw [ZMod.card, ← mul_assoc, mul_inv_cancel₀ hn0.ne', one_mul]
  have hPsum : ∑ a : ZMod p, TraceMixing.paleyOp g a ^ 2 ≤ G / n := by
    have h := TraceMixing.norm_paleyOp hF g
    rw [ZMod.card] at h
    have h' : ∑ a : ZMod p, TraceMixing.paleyOp g a ^ 2 = n⁻¹ * G - (n⁻¹ * ∑ s, g s) ^ 2 :=
      mul_left_cancel₀ (inv_ne_zero hn0.ne') h
    rw [h', div_eq_inv_mul]
    have : 0 ≤ (n⁻¹ * ∑ s, g s) ^ 2 := sq_nonneg _
    linarith
  have hY2 : Y ^ 2 ≤ n * (A * G) := by
    have hY : Y = ∑ a, f a * (n * TraceMixing.paleyOp g a) := by
      rw [hY_def]
      exact Finset.sum_congr rfl fun a _ => by rw [hPdef a]
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ f (fun a => n * TraceMixing.paleyOp g a)
    have hsq : ∑ a : ZMod p, (n * TraceMixing.paleyOp g a) ^ 2 =
        n ^ 2 * ∑ a : ZMod p, TraceMixing.paleyOp g a ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [hY]
    calc (∑ a, f a * (n * TraceMixing.paleyOp g a)) ^ 2
        ≤ A * (n ^ 2 * ∑ a : ZMod p, TraceMixing.paleyOp g a ^ 2) := by rw [← hsq]; exact hcs
      _ ≤ A * (n ^ 2 * (G / n)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact mul_le_mul_of_nonneg_left hPsum (by positivity)
      _ = n * (A * G) := by field_simp
  -- square roots
  set a := Real.sqrt A with ha_def
  set b := Real.sqrt G with hb_def
  have ha0 : 0 ≤ a := Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := Real.sqrt_nonneg _
  have ha2 : a ^ 2 = A := Real.sq_sqrt hA
  have hb2 : b ^ 2 = G := Real.sq_sqrt hG
  have hXab : |X| ≤ a * b := by
    have : |X| ^ 2 ≤ (a * b) ^ 2 := by rw [sq_abs, mul_pow, ha2, hb2]; exact hX2
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp this
  have hYab : |Y| ≤ s * (a * b) := by
    have : |Y| ^ 2 ≤ (s * (a * b)) ^ 2 := by
      rw [sq_abs, mul_pow, mul_pow, ha2, hb2, hs2]
      exact hY2
    exact (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) two_ne_zero).mp this
  have hc1 : |(c : ℝ)| = 1 := by rcases hc with rfl | rfl <;> norm_num
  -- the norms
  have hfn : DensityUpgrade.conditioningNorm 2 f = a / s := by
    rw [conditioningNorm_two, ZMod.card, Real.sqrt_div' _ hn0.le]
  have hgn : DensityUpgrade.conditioningNorm 2 g = b / s := by
    rw [conditioningNorm_two, ZMod.card, Real.sqrt_div' _ hn0.le]
  rw [class_centredForm hp2 hc, hfn, hgn, ← hn_def, ← hX_def, ← hY_def]
  have hden : 0 < n * (n - 1) := by nlinarith
  rw [abs_div, abs_of_pos hden, div_le_iff₀ hden]
  have hnum : |-X + c * Y| ≤ a * b + s * (a * b) := by
    calc |-X + c * Y| ≤ |-X| + |(c : ℝ) * Y| := abs_add_le _ _
      _ = |X| + |Y| := by rw [abs_neg, abs_mul, hc1, one_mul]
      _ ≤ a * b + s * (a * b) := add_le_add hXab hYab
  have hrhs : 1 / (s - 1) * (a / s) * (b / s) * (n * (n - 1)) = a * b + s * (a * b) := by
    rw [← hs2]
    have hs0 : s ≠ 0 := by linarith
    have hs10 : s - 1 ≠ 0 := by linarith
    field_simp
    ring
  rw [hrhs]
  exact hnum

/-- **`lem:density:edge-moment`, steps 1–2, for the paper's pair laws**: the interpolated
centred bound `hinterp` of `EdgeGate.square_pair_moment` holds for both class laws, every odd
prime `p` and every `j ≥ 1`. -/
theorem square_pair_interp (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) {j : ℕ} (hj : 1 ≤ j) :
    ∀ f g : ZMod p → ℝ, ∑ a, f a = 0 → ∑ a, g a = 0 →
      |∑ x, (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc)).weight x *
          (f (x 0) * g (x 1))| ≤
        (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (((j : ℝ) - 1) / ((j : ℝ) + 1)) *
          (1 / (Real.sqrt p - 1)) ^ ((2 : ℝ) / ((j : ℝ) + 1)) *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) f *
          DensityUpgrade.conditioningNorm (1 + 1 / (j : ℝ)) g := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.out.one_lt
  have hsq : 1 < Real.sqrt p := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hp1
  exact centred_interp_edge _ (div_nonneg (by linarith) (by linarith))
    (one_div_nonneg.mpr (by linarith)) hj (class_L1 hp2 hc) (class_L2 hp2 hc)

/-- **`lem:density:edge-moment` for the paper's pair laws, proved** (the `𝔽_p` part). Under the
gate `eq:density:edge-integer-gate`, the uniform strict square pair (`c = 1`) and the uniform
nonsquare pair (`c = −1`) have unit mixed `L^{1+1/j}`. No hypothesis besides the gate. -/
theorem square_pair_moment_proved (hp2 : p ≠ 2) {c : ℤ} (hc : c = 1 ∨ c = -1) {j : ℕ}
    (hj : 1 ≤ j)
    (hgate : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1) :
    MixedLpBound (uniformOn (classSet (p := p) c) (classSet_nonempty hp2 hc))
      (1 + 1 / (j : ℝ)) 1 :=
  EdgeGate.square_pair_moment hp2 hc hj hgate (square_pair_interp hp2 hc hj)

/-- **`lem:density:invariant-pair` with the square-pair moment, proved.** Under the gate, every
law on ordered distinct pairs of `𝔽_p` invariant under the square-affine maps has unit mixed
`L^{1+1/j}`. -/
theorem invariant_pair_edge_proved (hp2 : p ≠ 2) (μ : FiniteLaw (Fin 2 → ZMod p))
    (hdist : ∀ z, z 0 = z 1 → μ.weight z = 0)
    (hinv : ∀ s u : ZMod p, s ≠ 0 → IsSquare s → ∀ z,
      μ.weight (fun k => s * z k + u) = μ.weight z)
    {j : ℕ} (hj : 1 ≤ j)
    (hgate : (j : ℝ) ^ (j + 1) * (((p : ℝ) + 1) / ((p : ℝ) - 1)) ^ (j - 1) *
      (1 / (Real.sqrt p - 1)) ^ 2 ≤ 1) :
    MixedLpBound μ (1 + 1 / (j : ℝ)) 1 :=
  EdgeGate.invariant_pair_edge hp2 μ hdist hinv hj hgate
    (fun _ hc => square_pair_interp hp2 hc hj)

end Sarkozy.Interpolation

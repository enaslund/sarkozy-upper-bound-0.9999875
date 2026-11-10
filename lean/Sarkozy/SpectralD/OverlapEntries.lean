module

public import Sarkozy.SpectralD.OverlapBridge

@[expose] public section

/-!
# The entries of `N` from `lem:general-star`(e), and a sanity instance

`paper/sections/14_spectral.tex`, `lem:general-star`(e), stated for the normalised star features
`F_S = W_S/r`, with kernel `(x, a) ↦ r⁻¹ starKer S x a` (definitionally the kernel
`featKer 𝒮 (Sum.inr S)` of `Sarkozy.SpectralD.Features`), in the bilinear form of the hypothesis
`hoff` of `lem:general-star`(f):

* `star_feature_disjoint_entry` (and `_symm`): for `T ∩ S = ∅` and `ρ_S` bounding the maximal
  correlation of `x_S` and `x_{U∖S}`, `|⟨F_S h, F_T h'⟩_μ| ≤ ρ_S ‖h‖ ‖h'‖`;
* `star_feature_pair_entry` (and `_symm`): for `S = {a, b}`, `T = {a, b'}`,
  `|⟨F_S h, F_T h'⟩_μ| ≤ (2ρ/(1 − q) + q(q + r)²/(1 − q)²) ‖h‖ ‖h'‖` (`pairOverlapN`, the right
  side of `eq:pair-overlap`);
* `star_feature_pair_entry_sharp`: the same with `ρ + q(q + r)²/(1 − q)²` (`pairOverlapSharpN`,
  from `pair_overlap_sharp`), which is smaller (`pairOverlapSharpN_le`).

The `_symm` forms give the transposed entries `N_TS = N_ST` from the same hypothesis.

**Sanity check** (rule 9): `uniformInj` is the uniform law on the injective labellings
`U → 𝔽_p`; `uniformInj_hyps` shows that it satisfies the standing hypotheses (`μ ≥ 0`, total mass
one, `Aff_p`-invariance, injective support) whenever an injective labelling exists, and
`overlap_hyps_satisfiable` exhibits, at `p = 7` and `U = Fin 3`, all the hypotheses of
`pair_overlap` and `disjoint_star_bound` at once (with `ρ = 1`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Overlap

open Finset Complex Sarkozy.SpectralC Sarkozy.Peyre
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## The normalised features -/

omit [Fintype U] [DecidableEq U] in
lemma kerMap_rescale (S : Finset U) (h : ZMod p → ℂ) (x : U → ZMod p) :
    kerMap (fun y a => (rp p)⁻¹ * starKer S y a) h x =
      (((rp p)⁻¹ : ℝ) : ℂ) * kerMap (starKer S) h x := by
  unfold kerMap
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  push_cast
  ring

omit [Fact p.Prime] in
lemma rp_inv_mul_self : (rp p)⁻¹ * (rp p)⁻¹ = (p : ℝ) := by
  unfold rp
  rw [inv_inv, Real.mul_self_sqrt (Nat.cast_nonneg p)]

/-- `⟨F_S h, F_T h'⟩_μ = p ⟨W_S h, W_T h'⟩_μ`. -/
lemma sum_rescale (μ : (U → ZMod p) → ℝ) (S T : Finset U) (h h' : ZMod p → ℂ) :
    ∑ x, (μ x : ℂ) * (conj (kerMap (fun y a => (rp p)⁻¹ * starKer S y a) h x) *
        kerMap (fun y a => (rp p)⁻¹ * starKer T y a) h' x) =
      (p : ℂ) * ∑ x, (μ x : ℂ) * (conj (kerMap (starKer S) h x) * kerMap (starKer T) h' x) := by
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [kerMap_rescale, kerMap_rescale, map_mul, Complex.conj_ofReal]
  have e : (((rp p)⁻¹ : ℝ) : ℂ) * (((rp p)⁻¹ : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, rp_inv_mul_self]; push_cast; rfl
  calc (μ x : ℂ) * ((((rp p)⁻¹ : ℝ) : ℂ) * conj (kerMap (starKer S) h x) *
        ((((rp p)⁻¹ : ℝ) : ℂ) * kerMap (starKer T) h' x))
      = ((((rp p)⁻¹ : ℝ) : ℂ) * (((rp p)⁻¹ : ℝ) : ℂ)) *
          ((μ x : ℂ) * (conj (kerMap (starKer S) h x) * kerMap (starKer T) h' x)) := by ring
    _ = _ := by rw [e]

/-- `|⟨F_T h, F_S h'⟩| = |⟨F_S h', F_T h⟩|` (the Gram matrix is Hermitian). -/
lemma norm_sum_conj_swap (μ : (U → ZMod p) → ℝ) (F G : (U → ZMod p) → ℂ) :
    ‖∑ x, (μ x : ℂ) * (conj (G x) * F x)‖ = ‖∑ x, (μ x : ℂ) * (conj (F x) * G x)‖ := by
  rw [← Complex.norm_conj, map_sum]
  congr 1
  refine sum_congr rfl fun x _ => ?_
  rw [map_mul, map_mul, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- **The disjoint-support entry** (`lem:general-star`(e), first claim; `p ≡ 3 (mod 4)`):
`|⟨F_S h, F_T h'⟩_μ| ≤ ρ_S ‖h‖ ‖h'‖` for `F_S = W_S/r`, `T ∩ S = ∅`, `ρ_S ≥ 0` bounding the
maximal correlation of `x_S` and `x_{U∖S}` (hypothesis `hρ`). -/
theorem star_feature_disjoint_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hST : Disjoint S T) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : CorrBound μ S (univ \ S) ρ)
    (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (fun y a => (rp p)⁻¹ * starKer S y a) h x) *
        kerMap (fun y a => (rp p)⁻¹ * starKer T y a) h' x)‖ ≤
      ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rw [sum_rescale, norm_mul, Complex.norm_natCast]
  have hb := disjoint_star_bound hp2 hp3 μ hμ0 hμ1 hinv hinj hST hρ0 hρ h h' hh hh'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (p : ℝ) * ‖∑ x, (μ x : ℂ) * (conj (kerMap (starKer S) h x) * kerMap (starKer T) h' x)‖
      ≤ (p : ℝ) * (ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h')) :=
        mul_le_mul_of_nonneg_left hb hp0.le
    _ = ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by field_simp

/-- The transposed disjoint-support entry, from the same hypothesis. -/
theorem star_feature_disjoint_entry_symm (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hST : Disjoint S T) {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : CorrBound μ S (univ \ S) ρ)
    (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (fun y a => (rp p)⁻¹ * starKer T y a) h x) *
        kerMap (fun y a => (rp p)⁻¹ * starKer S y a) h' x)‖ ≤
      ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rw [norm_sum_conj_swap]
  have := star_feature_disjoint_entry hp2 hp3 μ hμ0 hμ1 hinv hinj hST hρ0 hρ h' h hh' hh
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The right side of `eq:pair-overlap`: `2ρ/(1 − q) + q(q + r)²/(1 − q)²`. -/
noncomputable def pairOverlapN (p : ℕ) (ρ : ℝ) : ℝ :=
  2 * ρ / (1 - (p : ℝ)⁻¹) + (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ + rp p) ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2

lemma natCast_mul_pairOverlapConst (ρ : ℝ) :
    (p : ℝ) * pairOverlapConst p ρ = pairOverlapN p ρ := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold pairOverlapConst pairOverlapN
  rw [← mul_assoc, mul_inv_cancel₀ hp0, one_mul]

/-- **The overlapping-pair entry** (`lem:general-star`(e), `eq:pair-overlap`; `p ≡ 3 (mod 4)`):
for `F_S = W_S/r`, `S = {a, b}`, `T = {a, b'}` (`a, b, b'` distinct) and `ρ ≥ 0` bounding the
conditional maximal correlation of `x_b` and `x_{U∖{a,b}}` given `x_a` (hypothesis `hρ`),
`|⟨F_S h, F_T h'⟩_μ| ≤ (2ρ/(1 − q) + q(q + r)²/(1 − q)²) ‖h‖ ‖h'‖`. -/
theorem star_feature_pair_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : CondCorrBound μ a b ρ) (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (fun y a' => (rp p)⁻¹ * starKer {a, b} y a') h x) *
        kerMap (fun y a' => (rp p)⁻¹ * starKer {a, b'} y a') h' x)‖ ≤
      pairOverlapN p ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rw [sum_rescale, norm_mul, Complex.norm_natCast]
  have hb := pair_overlap hp2 hp3 μ hμ0 hμ1 hinv hinj hab hab' hbb' hρ0 hρ h h' hh hh'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  calc (p : ℝ) * ‖∑ x, (μ x : ℂ) * (conj (kerMap (starKer {a, b}) h x) *
        kerMap (starKer {a, b'}) h' x)‖
      ≤ (p : ℝ) * (pairOverlapConst p ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h')) :=
        mul_le_mul_of_nonneg_left hb hp0.le
    _ = ((p : ℝ) * pairOverlapConst p ρ) * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by ring
    _ = _ := by rw [natCast_mul_pairOverlapConst]

/-- The transposed overlapping-pair entry, from the same hypothesis. -/
theorem star_feature_pair_entry_symm (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : CondCorrBound μ a b ρ) (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (fun y a' => (rp p)⁻¹ * starKer {a, b'} y a') h x) *
        kerMap (fun y a' => (rp p)⁻¹ * starKer {a, b} y a') h' x)‖ ≤
      pairOverlapN p ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rw [norm_sum_conj_swap]
  have := star_feature_pair_entry hp2 hp3 μ hμ0 hμ1 hinv hinj hab hab' hbb' hρ0 hρ h' h hh' hh
  calc _ ≤ _ := this
    _ = _ := by ring

/-- The sharp constant `ρ + q(q + r)²/(1 − q)²` of `pair_overlap_sharp` for `W_S/r` (it improves
the factor `2/(1 − q)` of `eq:pair-overlap` on `ρ` to `1`). -/
noncomputable def pairOverlapSharpN (p : ℕ) (ρ : ℝ) : ℝ :=
  ρ + (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ + rp p) ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2

lemma pairOverlapSharpN_le {ρ : ℝ} (hρ0 : 0 ≤ ρ) : pairOverlapSharpN p ρ ≤ pairOverlapN p ρ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have h1q : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  have hq0 : 0 < (p : ℝ)⁻¹ := by positivity
  unfold pairOverlapSharpN pairOverlapN
  have : ρ ≤ 2 * ρ / (1 - (p : ℝ)⁻¹) := by
    rw [le_div_iff₀ h1q]; nlinarith
  linarith

/-- **The overlapping-pair entry, sharp form** (proof of `lem:general-star`(e); `p ≡ 3 (mod 4)`):
under the hypotheses of `star_feature_pair_entry`,
`|⟨F_S h, F_T h'⟩_μ| ≤ (ρ + q(q + r)²/(1 − q)²) ‖h‖ ‖h'‖`. -/
theorem star_feature_pair_entry_sharp (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : CondCorrBound μ a b ρ) (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (fun y a' => (rp p)⁻¹ * starKer {a, b} y a') h x) *
        kerMap (fun y a' => (rp p)⁻¹ * starKer {a, b'} y a') h' x)‖ ≤
      pairOverlapSharpN p ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rw [sum_rescale, norm_mul, Complex.norm_natCast]
  have hb := pair_overlap_sharp hp2 hp3 μ hμ0 hμ1 hinv hinj hab hab' hbb' hρ0 hρ h h' hh hh'
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have e : (p : ℝ) * (ρ * (p : ℝ)⁻¹ + (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2) =
      pairOverlapSharpN p ρ := by
    unfold pairOverlapSharpN
    field_simp
  calc (p : ℝ) * ‖∑ x, (μ x : ℂ) * (conj (kerMap (starKer {a, b}) h x) *
        kerMap (starKer {a, b'}) h' x)‖
      ≤ (p : ℝ) * ((ρ * (p : ℝ)⁻¹ + (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2) *
          Real.sqrt (l2sq h) * Real.sqrt (l2sq h')) :=
        mul_le_mul_of_nonneg_left hb hp0.le
    _ = ((p : ℝ) * (ρ * (p : ℝ)⁻¹ + (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2)) *
          Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by ring
    _ = _ := by rw [e]

/-! ## Sanity check: the uniform law on injective labellings -/

/-- The uniform law on the injective labellings `U → 𝔽_p`. -/
noncomputable def uniformInj : (U → ZMod p) → ℝ :=
  fun x => if Function.Injective x then
    (((univ.filter (fun y : U → ZMod p => Function.Injective y)).card : ℝ))⁻¹ else 0

omit [Fintype U] [DecidableEq U] in
lemma injective_affLab {s : ZMod p} (hs : s ≠ 0) (c : ZMod p) (x : U → ZMod p) :
    Function.Injective (affLab s c x) ↔ Function.Injective x := by
  constructor
  · intro h i j hij
    apply h
    unfold affLab
    rw [hij]
  · intro h i j hij
    apply h
    unfold affLab at hij
    exact mul_left_cancel₀ hs (by linear_combination hij)

/-- **Sanity check** (rule 9): the uniform law on injective labellings satisfies the standing
hypotheses of `lem:general-star` whenever an injective labelling exists. -/
theorem uniformInj_hyps (hne : ∃ x : U → ZMod p, Function.Injective x) :
    (∀ x, 0 ≤ uniformInj (p := p) (U := U) x) ∧ ∑ x, uniformInj (p := p) (U := U) x = 1 ∧
    (∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s →
      uniformInj (p := p) (U := U) (affLab s c x) = uniformInj (p := p) (U := U) x) ∧
    (∀ (x : U → ZMod p) (k l : U), uniformInj (p := p) (U := U) x ≠ 0 → k ≠ l → x k ≠ x l) := by
  obtain ⟨x0, hx0⟩ := hne
  have hpos : 0 < ((univ.filter (fun y : U → ZMod p => Function.Injective y)).card : ℝ) := by
    have : x0 ∈ univ.filter (fun y : U → ZMod p => Function.Injective y) :=
      mem_filter.mpr ⟨mem_univ _, hx0⟩
    exact_mod_cast card_pos.mpr ⟨x0, this⟩
  refine ⟨fun x => ?_, ?_, fun s c x hs _ => ?_, fun x k l hx hkl => ?_⟩
  · unfold uniformInj
    split_ifs
    · positivity
    · exact le_refl 0
  · unfold uniformInj
    rw [← sum_filter, sum_const, nsmul_eq_mul, mul_inv_cancel₀ hpos.ne']
  · unfold uniformInj
    simp only [injective_affLab hs c x]
  · intro hxy
    unfold uniformInj at hx
    split_ifs at hx with hinj
    · exact hkl (hinj hxy)
    · exact hx rfl

/-- `7` is prime (for the sanity instance). -/
theorem fact_prime_seven : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩

attribute [local instance] fact_prime_seven

/-- **Sanity check** (rule 9): at `p = 7` (`≡ 3 (mod 4)`) and `U = Fin 3`, the uniform law on
injective labellings satisfies all the hypotheses of `pair_overlap` (with `a, b, b' = 0, 1, 2`)
and of `disjoint_star_bound` (with `S = {0}`, `T = {1, 2}`), with `ρ = 1`. -/
theorem overlap_hyps_satisfiable :
    (7 : ℕ) % 4 = 3 ∧
    (∀ x, 0 ≤ uniformInj (p := 7) (U := Fin 3) x) ∧ ∑ x, uniformInj (p := 7) (U := Fin 3) x = 1 ∧
    (∀ (s c : ZMod 7) (x : Fin 3 → ZMod 7), s ≠ 0 → IsSquare s →
      uniformInj (p := 7) (U := Fin 3) (affLab s c x) = uniformInj (p := 7) (U := Fin 3) x) ∧
    (∀ (x : Fin 3 → ZMod 7) (k l : Fin 3), uniformInj (p := 7) (U := Fin 3) x ≠ 0 → k ≠ l → x k ≠ x l) ∧
    ((0 : Fin 3) ≠ 1 ∧ (0 : Fin 3) ≠ 2 ∧ (1 : Fin 3) ≠ 2) ∧
    CondCorrBound (uniformInj (p := 7) (U := Fin 3)) 0 1 1 ∧
    Disjoint ({0} : Finset (Fin 3)) {1, 2} ∧
    CorrBound (uniformInj (p := 7) (U := Fin 3)) {0} (univ \ {0}) 1 := by
  have hne : ∃ x : Fin 3 → ZMod 7, Function.Injective x :=
    ⟨fun i => ((i : ℕ) : ZMod 7), by decide⟩
  obtain ⟨h0, h1, h2, h3⟩ := uniformInj_hyps (p := 7) (U := Fin 3) hne
  exact ⟨by norm_num, h0, h1, h2, h3, by decide, condCorrBound_one _ h0 0 1, by decide,
    corrBound_one _ h0 _ _⟩

end Sarkozy.SpectralD.Overlap

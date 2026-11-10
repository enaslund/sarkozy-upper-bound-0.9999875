module

public import Sarkozy.Cancellation.Moments
public import Sarkozy.Cancellation.CondExpectation

@[expose] public section

/-!
# Step 2 of `lem:record:density-can` for the laws of Step 1

The two moment bounds that `density_can_of_pair_laws` takes as hypotheses, derived from
`step2_holder_moments` (Hölder with `n` factors), the uniformity of the one-slot marginals of
`ϱ` ("under `ϱ` every `z_w` is uniform on `G_N`") and the moment input of
`lem:record:lift-moments`(c):

* `step2_other_slots`: `∫_x ‖W_x‖₂² ≤ M` when `W_x(b) = ∏_w G_w(z_w(x, b))` (the paper's `70`
  factors, moments of order `140`);
* `step2_pair_factor`: `∫_x ‖φ_x‖₂² ≤ M` for `φ_x = G_u ⊗ G_v` under `⊗_p Unif(Ω_p)` (fourth
  moments);
* `step3_fourth_moments`: the moment input of Step 3, `E(‖g₁‖₂² ‖g₂‖₂²) ≤ ‖G_u‖₄² ‖G_v‖₄² ≤ M`
  ("Cauchy–Schwarz and Jensen's inequality (`‖g₁‖₂⁴ ≤ E|g₁|⁴` over `X_{𝒮'}`) … because `(x_u, y_u)`
  together with the uniform outside label is uniform on `G_N`").

New material for this paper.
-/

namespace Sarkozy.Cancellation

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open Finset
open scoped BigOperators
open Sarkozy.Mixing Sarkozy.FourierArithmetic

section OtherSlots

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)]

/-- **Step 2, the other slots**: if `W_x(b) = ∏_{i} G_i(z_i(x, b))` for `n` factors whose slots are
uniform on `Z` under `x ∼ μ`, `b ∼` the other-slot marginal of `⊗_j κ_j`, and `E|G_i|^{2n} ≤ M`,
then `∫_x ‖W_x‖₂² ≤ M`. -/
theorem step2_other_slots {X I Z : Type*} [Fintype X] [Fintype I] [Fintype Z] [Nonempty Z]
    (μ : FiniteLaw X) (κ : ∀ j, FiniteLaw (A j × B j)) (n : ℕ) (hn : Fintype.card I = n)
    (hn0 : 0 < n) (z : I → X × (∀ j, B j) → Z) (G : I → Z → ℝ) (W : X → (∀ j, B j) → ℝ)
    (hW : ∀ x b, W x b = ∏ i, G i (z i (x, b)))
    (hunif : ∀ i (f : Z → ℝ), (μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b *
      f (z i (x, b))) = (FiniteLaw.uniform Z).expect f)
    {M : ℝ} (hM : 0 ≤ M)
    (hmom : ∀ i, (FiniteLaw.uniform Z).expect (fun y => |G i y| ^ ((2 * n : ℕ) : ℝ)) ≤ M) :
    (μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b * W x b ^ 2) ≤ M := by
  let lam : FiniteLaw (∀ j, B j) :=
    ⟨tgtWeight (prodJoint κ), tgtWeight_nonneg _, sum_tgtWeight _⟩
  have hexp : ∀ f : X × (∀ j, B j) → ℝ, (μ.product lam).expect f =
      μ.expect fun x => ∑ b, tgtWeight (prodJoint κ) b * f (x, b) := by
    intro f
    rw [FiniteLaw.expect_product]
    rfl
  have h := step2_holder_moments (μ.product lam) n hn hn0 z G
    (fun i f => by rw [hexp]; exact hunif i f) hM hmom
  rw [hexp] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  funext x
  apply sum_congr rfl
  intro b _
  rw [hW, ← prod_pow]

end OtherSlots

section PairFactor

variable {K : Type*} [Fintype K] [DecidableEq K] (q : K → ℕ) [∀ j, NeZero (q j)]
  [∀ j, Fact (q j).Prime]

/-- **Step 2, the pair factor**: if `F₁(x, y) = G_u(z_u(x, y))`, `F₂(x, y) = G_v(z_v(x, y))` with
both slots uniform on `Z` under `x ∼ μ`, `a ∼ Unif(∏_j Ω_{q_j})`, and `E|G_u|⁴, E|G_v|⁴ ≤ M`, then
`∫_x ‖φ_x‖₂² ≤ M` for `φ_x(a) = F₁(x, x(a)) F₂(x, y(a))`. -/
theorem step2_pair_factor {X Z : Type*} [Fintype X] [Fintype Z] [Nonempty Z] (μ : FiniteLaw X)
    (zu zv : X → ResidueSpace q → Z) (Gu Gv : Z → ℝ) (F₁ F₂ : X → ResidueSpace q → ℝ)
    (hF₁ : ∀ x y, F₁ x y = Gu (zu x y)) (hF₂ : ∀ x y, F₂ x y = Gv (zv x y))
    (hunif_u : ∀ f : Z → ℝ, (μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
      (fun a => f (zu x (pairsToVectors q a).1))) = (FiniteLaw.uniform Z).expect f)
    (hunif_v : ∀ f : Z → ℝ, (μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
      (fun a => f (zv x (pairsToVectors q a).2))) = (FiniteLaw.uniform Z).expect f)
    {M : ℝ} (hM : 0 ≤ M)
    (hmu : (FiniteLaw.uniform Z).expect (fun y => |Gu y| ^ ((4 : ℕ) : ℝ)) ≤ M)
    (hmv : (FiniteLaw.uniform Z).expect (fun y => |Gv y| ^ ((4 : ℕ) : ℝ)) ≤ M) :
    (μ.expect fun x => (FiniteLaw.uniform (∀ j, PairAlphabet q j)).expect
        (fun a => (F₁ x (pairsToVectors q a).1 * F₂ x (pairsToVectors q a).2) ^ 2)) ≤ M := by
  let ν := FiniteLaw.uniform (∀ j, PairAlphabet q j)
  let z : Bool → X × (∀ j, PairAlphabet q j) → Z := fun i ω =>
    if i then zu ω.1 (pairsToVectors q ω.2).1 else zv ω.1 (pairsToVectors q ω.2).2
  let G : Bool → Z → ℝ := fun i => if i then Gu else Gv
  have hexp : ∀ f : X × (∀ j, PairAlphabet q j) → ℝ, (μ.product ν).expect f =
      μ.expect fun x => ν.expect fun a => f (x, a) := fun f => FiniteLaw.expect_product μ ν f
  have h := step2_holder_moments (μ.product ν) 2 (by simp) (by norm_num) z G
    (fun i f => by
      rw [hexp]
      cases i
      · exact hunif_v f
      · exact hunif_u f) hM
    (fun i => by
      have h4 : ((2 * 2 : ℕ) : ℝ) = ((4 : ℕ) : ℝ) := by norm_num
      rw [h4]
      cases i
      · exact hmv
      · exact hmu)
  rw [hexp] at h
  refine le_of_eq_of_le ?_ h
  congr 1
  funext x
  congr 1
  funext a
  rw [Fintype.prod_bool]
  simp only [z, G, ite_true, Bool.false_eq_true, ite_false, hF₁, hF₂]
  ring

end PairFactor

/-! ## The moment input of Step 3 -/

/-- Jensen on a finite uniform average: `(E_y X(y))² ≤ E_y X(y)²`. -/
lemma sq_expect_le_expect_sq {Y : Type*} [Fintype Y] (X : Y → ℝ) :
    (𝔼 y, X y) ^ 2 ≤ 𝔼 y, X y ^ 2 := by
  rw [Fintype.expect_eq_sum_div_card, Fintype.expect_eq_sum_div_card]
  have h := sum_div_card_sq_le_sum_sq_div_card (s := (univ : Finset Y)) (f := X)
  simpa [card_univ] using h

/-- **The moment input of Step 3** (`lem:record:density-can`): if `|g_i(ω, ·)| = |G_i(z_i(ω, ·))|`
and the slots `z_i(ω, y)` are uniform on `Z` when `ω ∼ w` and `y` is uniform on `X_{𝒮'}`, then by
Cauchy–Schwarz and Jensen `E_ω(‖g₁(ω)‖₂² ‖g₂(ω)‖₂²) ≤ ‖G₁‖₄² ‖G₂‖₄² ≤ M` when `E|G_i|⁴ ≤ M`. -/
theorem step3_fourth_moments {Ω Y Z : Type*} [Fintype Y] [Fintype Z] [Nonempty Z]
    (s : Finset Ω) (w : Ω → ℝ) (hw : ∀ ω ∈ s, 0 ≤ w ω) (g₁ g₂ : Ω → Y → ℂ)
    (z₁ z₂ : Ω → Y → Z) (G₁ G₂ : Z → ℝ)
    (hg₁ : ∀ ω y, ‖g₁ ω y‖ = |G₁ (z₁ ω y)|) (hg₂ : ∀ ω y, ‖g₂ ω y‖ = |G₂ (z₂ ω y)|)
    (hunif₁ : ∀ f : Z → ℝ, ∑ ω ∈ s, w ω * 𝔼 y, f (z₁ ω y) = (FiniteLaw.uniform Z).expect f)
    (hunif₂ : ∀ f : Z → ℝ, ∑ ω ∈ s, w ω * 𝔼 y, f (z₂ ω y) = (FiniteLaw.uniform Z).expect f)
    {M : ℝ} (hM : 0 ≤ M)
    (hm₁ : (FiniteLaw.uniform Z).expect (fun y => |G₁ y| ^ 4) ≤ M)
    (hm₂ : (FiniteLaw.uniform Z).expect (fun y => |G₂ y| ^ 4) ≤ M) :
    ∑ ω ∈ s, w ω * ((𝔼 y, ‖g₁ ω y‖ ^ 2) * (𝔼 y, ‖g₂ ω y‖ ^ 2)) ≤ M := by
  set a : Ω → ℝ := fun ω => 𝔼 y, ‖g₁ ω y‖ ^ 2 with ha
  set b : Ω → ℝ := fun ω => 𝔼 y, ‖g₂ ω y‖ ^ 2 with hb
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => expect_nonneg (fun y _ => sq_nonneg _)
  have hb0 : ∀ ω, 0 ≤ b ω := fun ω => expect_nonneg (fun y _ => sq_nonneg _)
  -- Jensen
  have hja : ∀ ω, a ω ^ 2 ≤ 𝔼 y, |G₁ (z₁ ω y)| ^ 4 := by
    intro ω
    refine (sq_expect_le_expect_sq _).trans (le_of_eq ?_)
    apply Finset.expect_congr rfl
    intro y _
    rw [hg₁, ← pow_mul]
  have hjb : ∀ ω, b ω ^ 2 ≤ 𝔼 y, |G₂ (z₂ ω y)| ^ 4 := by
    intro ω
    refine (sq_expect_le_expect_sq _).trans (le_of_eq ?_)
    apply Finset.expect_congr rfl
    intro y _
    rw [hg₂, ← pow_mul]
  -- the fourth moments
  have hA : ∑ ω ∈ s, w ω * a ω ^ 2 ≤ M := by
    calc ∑ ω ∈ s, w ω * a ω ^ 2 ≤ ∑ ω ∈ s, w ω * 𝔼 y, |G₁ (z₁ ω y)| ^ 4 :=
          sum_le_sum (fun ω hω => mul_le_mul_of_nonneg_left (hja ω) (hw ω hω))
      _ = (FiniteLaw.uniform Z).expect (fun y => |G₁ y| ^ 4) := hunif₁ (fun y => |G₁ y| ^ 4)
      _ ≤ M := hm₁
  have hB : ∑ ω ∈ s, w ω * b ω ^ 2 ≤ M := by
    calc ∑ ω ∈ s, w ω * b ω ^ 2 ≤ ∑ ω ∈ s, w ω * 𝔼 y, |G₂ (z₂ ω y)| ^ 4 :=
          sum_le_sum (fun ω hω => mul_le_mul_of_nonneg_left (hjb ω) (hw ω hω))
      _ = (FiniteLaw.uniform Z).expect (fun y => |G₂ y| ^ 4) := hunif₂ (fun y => |G₂ y| ^ 4)
      _ ≤ M := hm₂
  -- Cauchy--Schwarz
  have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun ω => Real.sqrt (w ω) * a ω)
    (fun ω => Real.sqrt (w ω) * b ω)
  have hl : ∀ ω ∈ s, Real.sqrt (w ω) * a ω * (Real.sqrt (w ω) * b ω) = w ω * (a ω * b ω) := by
    intro ω hω
    rw [show Real.sqrt (w ω) * a ω * (Real.sqrt (w ω) * b ω) =
      (Real.sqrt (w ω)) ^ 2 * (a ω * b ω) by ring, Real.sq_sqrt (hw ω hω)]
  have hsa : ∀ ω ∈ s, (Real.sqrt (w ω) * a ω) ^ 2 = w ω * a ω ^ 2 := by
    intro ω hω
    rw [mul_pow, Real.sq_sqrt (hw ω hω)]
  have hsb : ∀ ω ∈ s, (Real.sqrt (w ω) * b ω) ^ 2 = w ω * b ω ^ 2 := by
    intro ω hω
    rw [mul_pow, Real.sq_sqrt (hw ω hω)]
  rw [sum_congr rfl hl, sum_congr rfl hsa, sum_congr rfl hsb] at hcs
  calc ∑ ω ∈ s, w ω * (a ω * b ω)
      ≤ Real.sqrt (∑ ω ∈ s, w ω * a ω ^ 2) * Real.sqrt (∑ ω ∈ s, w ω * b ω ^ 2) := hcs
    _ ≤ Real.sqrt M * Real.sqrt M :=
        mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
          (Real.sqrt_nonneg _)
    _ = M := Real.mul_self_sqrt hM

end Sarkozy.Cancellation

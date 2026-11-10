module

public import Sarkozy.JointRows.StarContractAllPrimes
public import Sarkozy.JointRows.StarNorms

/-!
# The scalar block majorant for pure stars

This proves the pure-star part of `eq:row-anova-stars` for both odd prime
classes. Single edges use a scalar operator bound, and higher supports
use the row sums of their nonnegative Gram matrices.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

section Scalar

variable {U V : Type*}

theorem sum_form_opBound (R : Finset U) (C : Finset V) (t N : U → V → ℝ)
    (a : U → ℝ) (b : V → ℝ) {d : ℝ} (hd : 0 ≤ d)
    (hN : Influence.OpBound R C N d)
    (ht : ∀ i ∈ R, ∀ j ∈ C, |t i j| ≤ N i j * a i * b j) :
    |∑ i ∈ R, ∑ j ∈ C, t i j| ≤
      d * Influence.vnorm R a * Influence.vnorm C b := by
  calc _ ≤ ∑ i ∈ R, ∑ j ∈ C, |t i j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ R, ∑ j ∈ C, N i j * a i * b j :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => ht i hi j hj
    _ = ∑ i ∈ R, a i * ∑ j ∈ C, N i j * b j := by
      apply sum_congr rfl
      intro i _
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    _ ≤ _ := Star.bilin_le_of_opBound hd hN a b

theorem sum_form_gram (R : Finset U) (C : Finset V) (t N : U → V → ℝ)
    (a : U → ℝ) (b : V → ℝ) {G : ℝ} (hG0 : 0 ≤ G)
    (hN : ∀ i j, 0 ≤ N i j)
    (hG : ∀ i ∈ R, ∑ i' ∈ R, ∑ j ∈ C, N i j * N i' j ≤ G)
    (ht : ∀ i ∈ R, ∀ j ∈ C, |t i j| ≤ N i j * a i * b j) :
    |∑ i ∈ R, ∑ j ∈ C, t i j| ≤
      Real.sqrt G * Influence.vnorm R a * Influence.vnorm C b := by
  calc _ ≤ ∑ i ∈ R, ∑ j ∈ C, |t i j| :=
      (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => abs_sum_le_sum_abs _ _)
    _ ≤ ∑ i ∈ R, ∑ j ∈ C, N i j * a i * b j :=
      sum_le_sum fun i hi => sum_le_sum fun j hj => ht i hi j hj
    _ = ∑ j ∈ C, b j * ∑ i ∈ R, N i j * a i := by
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      rw [mul_sum]
      exact sum_congr rfl fun i _ => by ring
    _ ≤ _ := Star.gram_bound N hN hG0 hG a b

end Scalar

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

theorem nrm_paley_le_odd (hp : p ≠ 2) (f : ZMod p → ℝ) :
    nrm (FiniteLaw.uniform (ZMod p)) (paley p f) ≤
      nrm (FiniteLaw.uniform (ZMod p)) f := by
  apply Real.sqrt_le_sqrt
  simp only [ip, FiniteLaw.expect_uniform, ZMod.card]
  exact div_le_div_of_nonneg_right (sum_paley_sq_le_odd hp f) (by positivity)

theorem nrm_sq_eq_ip {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (μ : FiniteLaw Ω) (f : Ω → ℝ) : nrm μ f ^ 2 = ip μ f f :=
  Real.sq_sqrt (FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _)

noncomputable def vectorNrm {I : Type*} (R : Finset I) (u : I → ZMod p → ℝ) : ℝ :=
  Influence.vnorm R (fun i => nrm (FiniteLaw.uniform (ZMod p)) (u i))

theorem vectorNrm_sq {I : Type*} (R : Finset I) (u : I → ZMod p → ℝ) :
    vectorNrm R u ^ 2 = ∑ i ∈ R, ip (FiniteLaw.uniform (ZMod p)) (u i) (u i) := by
  rw [vectorNrm, Influence.vnorm_sq]
  simp only [nrm_sq_eq_ip]

omit [DecidableEq X] [DecidableEq Y] in
theorem mForm_bound_odd (hp : p ≠ 2) (D : X → Y → ℝ)
    (𝒯 : Finset (Finset Y)) (A : X → Finset Y → ℝ)
    (𝒮 : Finset (Finset X)) (B : Y → Finset X → ℝ)
    {d G : ℝ} (hd : 0 ≤ d) (hG : 0 ≤ G)
    (hD : Influence.OpBound univ univ (fun i j => |D i j|) d)
    (hA : ∀ i, ∑ i', ∑ T ∈ 𝒯, |A i T| * |A i' T| ≤ G)
    (hB : ∀ j, ∑ j', ∑ S ∈ 𝒮, |B j S| * |B j' S| ≤ G)
    (u : X → ZMod p → ℝ) (uS : Finset X → ZMod p → ℝ)
    (v : Y → ZMod p → ℝ) (vT : Finset Y → ZMod p → ℝ) :
    |mForm D 𝒯 A 𝒮 B u uS v vT| ≤ Star.eStar d (Real.sqrt G) *
      Real.sqrt (vectorNrm univ u ^ 2 + vectorNrm 𝒮 uS ^ 2) *
      Real.sqrt (vectorNrm univ v ^ 2 + vectorNrm 𝒯 vT ^ 2) := by
  let μ := FiniteLaw.uniform (ZMod p)
  have h1 : |∑ i, ∑ j, D i j * ip μ (u i) (paley p (v j))| ≤
      d * vectorNrm univ u * vectorNrm univ v := by
    apply sum_form_opBound univ univ _ _ _ _ hd hD
    intro i _ j _
    rw [abs_mul]
    have h := (abs_ip_le μ (u i) (paley p (v j))).trans
      (mul_le_mul_of_nonneg_left (nrm_paley_le_odd hp (v j)) (FiveType.nrm_nonneg μ (u i)))
    exact (mul_le_mul_of_nonneg_left h (abs_nonneg _)).trans_eq (by ring)
  have h2 : |∑ i, ∑ T ∈ 𝒯, A i T * ip μ (u i) (vT T)| ≤
      Real.sqrt G * vectorNrm univ u * vectorNrm 𝒯 vT := by
    apply sum_form_gram univ 𝒯 _ (fun i T => |A i T|) _ _ hG
      (fun _ _ => abs_nonneg _) (fun i _ => hA i)
    intro i _ T _
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_ip_le μ (u i) (vT T))
      (abs_nonneg _)).trans_eq (by ring)
  have h3 : |∑ j, ∑ S ∈ 𝒮, B j S * ip μ (uS S) (v j)| ≤
      Real.sqrt G * vectorNrm univ v * vectorNrm 𝒮 uS := by
    apply sum_form_gram univ 𝒮 _ (fun j S => |B j S|) _ _ hG
      (fun _ _ => abs_nonneg _) (fun j _ => hB j)
    intro j _ S _
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left (abs_ip_le μ (uS S) (v j))
      (abs_nonneg _)).trans_eq (by ring)
  have ht : |mForm D 𝒯 A 𝒮 B u uS v vT| ≤
      d * vectorNrm univ u * vectorNrm univ v +
        Real.sqrt G * (vectorNrm univ u * vectorNrm 𝒯 vT +
          vectorNrm 𝒮 uS * vectorNrm univ v) := by
    unfold mForm
    have h12 := abs_add_le
      (∑ i, ∑ j, D i j * ip μ (u i) (paley p (v j)))
      (∑ i, ∑ T ∈ 𝒯, A i T * ip μ (u i) (vT T))
    have h123 := abs_add_le
      ((∑ i, ∑ j, D i j * ip μ (u i) (paley p (v j))) +
        ∑ i, ∑ T ∈ 𝒯, A i T * ip μ (u i) (vT T))
      (∑ j, ∑ S ∈ 𝒮, B j S * ip μ (uS S) (v j))
    change _ ≤ _ at h123
    dsimp [μ] at h1 h2 h3 h12 h123
    nlinarith
  exact ht.trans (Star.norm_matrix_two hd _ _ _ _)

theorem pureKernel_bound_odd (hp : p ≠ 2)
    (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (D : X → Y → ℝ) (𝒯 : Finset (Finset Y)) (A : X → Finset Y → ℝ)
    (𝒮 : Finset (Finset X)) (B : Y → Finset X → ℝ)
    {κ d G : ℝ} (hκ : 0 < κ) (hd : 0 ≤ d) (hG : 0 ≤ G)
    (hdensX : ∀ i a, (νp i).weight a ≤ κ / p)
    (hdensY : ∀ j a, (νq j).weight a ≤ κ / p)
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) (h𝒯 : ∀ T ∈ 𝒯, 2 ≤ T.card)
    (hD : Influence.OpBound univ univ (fun i j => |D i j|) d)
    (hA : ∀ i, ∑ i', ∑ T ∈ 𝒯, |A i T| * |A i' T| ≤ G)
    (hB : ∀ j, ∑ j', ∑ S ∈ 𝒮, |B j S| * |B j' S| ≤ G)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ)
    (hf : (blockLaw νp).expect f = 0) (hg : (blockLaw νq).expect g = 0) :
    |bform νp νq (pureKernel νp νq D 𝒯 A 𝒮 B) f g| ≤
      κ * (Real.sqrt p)⁻¹ * Star.eStar d (Real.sqrt G) * nrm (blockLaw νp) f *
        nrm (blockLaw νq) g := by
  rw [pure_block_identity νp νq D 𝒯 A 𝒮 B hκ f g hf hg, abs_mul,
    abs_of_nonneg (by positivity : 0 ≤ κ * (Real.sqrt p)⁻¹)]
  have h := mForm_bound_odd hp D 𝒯 A 𝒮 B hd hG hD hA hB
    (featU νp κ f) (featW νp κ f) (featU νq κ g) (featW νq κ g)
  have hx : Real.sqrt (vectorNrm univ (featU νp κ f) ^ 2 +
      vectorNrm 𝒮 (featW νp κ f) ^ 2) ≤ nrm (blockLaw νp) f := by
    apply Real.sqrt_le_sqrt
    simp only [vectorNrm_sq]
    exact featStar_norm_le_odd hp νp hκ hdensX 𝒮 h𝒮 hf
  have hy : Real.sqrt (vectorNrm univ (featU νq κ g) ^ 2 +
      vectorNrm 𝒯 (featW νq κ g) ^ 2) ≤ nrm (blockLaw νq) g := by
    apply Real.sqrt_le_sqrt
    simp only [vectorNrm_sq]
    exact featStar_norm_le_odd hp νq hκ hdensY 𝒯 h𝒯 hg
  have hbound := h.trans (mul_le_mul
    (mul_le_mul_of_nonneg_left hx (Star.eStar_nonneg hd)) hy
    (Real.sqrt_nonneg _) (mul_nonneg (Star.eStar_nonneg hd) (FiveType.nrm_nonneg _ _)))
  exact (mul_le_mul_of_nonneg_left hbound (by positivity)).trans_eq (by ring)

end Sarkozy.JointRows.StarOps

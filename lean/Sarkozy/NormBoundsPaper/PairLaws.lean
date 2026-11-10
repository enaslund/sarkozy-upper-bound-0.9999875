module

public import Sarkozy.NormBoundsPaper.Block
public import Sarkozy.MiddleComparison.Constants

@[expose] public section

/-!
# The one-object laws of the constant records (`lem:record:accepting-c2`)

`paper/sections/21_middle_records.tex`, proof of `lem:record:accepting-c2`: "Write `(a_p, b_p)`
for the labels of the single object of either constant record in layers `0` and `1` at the prime
`p` … They are uniform ordered distinct labels: this is the one-object marginal of the original
injective matching law. … Replace this law by the uniform strict Paley edge, independently at every
prime."

* `pw μ u v a c`: the law of the pair `(y_u, y_v)` under a law `μ` of labellings;
* **`expect_pair`**: for a tensor law over the primes, the pair law is the product of the
  one-prime pair laws;
* **`pw_match`**: under V1's `E` law (`matchGraph (Fin 2)`, no edges, injective labellings of
  six objects) the pair `(y_u, y_v)`, `u ≠ v`, is uniform on ordered distinct pairs:
  `p⁻¹ k_D(c − a)` (every bijection of `𝔽_p` preserves the law; the pairs are one orbit);
* **`pw_edge`**: under the Paley edge law the pair is `p⁻¹ k_P(c − a)`;
* **`expect_pair_match`**, **`expect_pair_edge`**: the block versions,
  `N⁻¹ K_D(c − a)` and `N⁻¹ K_P(c − a)`.
-/

namespace Sarkozy.NormBoundsPaper

open Finset Sarkozy.PartV Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.SpectralC
open scoped BigOperators

/-! ## Pair laws -/

section Pair

variable {W : Type} [Fintype W] [DecidableEq W] {F : Type} [Fintype F] [DecidableEq F]

/-- The law of the pair `(y_u, y_v)`. -/
noncomputable def pw (μ : FiniteLaw (W → F)) (u v : W) (a c : F) : ℝ :=
  ∑ y, μ.weight y * (if y u = a ∧ y v = c then 1 else 0)

theorem sum_pw (μ : FiniteLaw (W → F)) (u v : W) : ∑ a, ∑ c, pw μ u v a c = 1 := by
  unfold pw
  have h : ∀ y : W → F, ∑ a, ∑ c, μ.weight y * (if y u = a ∧ y v = c then (1 : ℝ) else 0) =
      μ.weight y := by
    intro y
    rw [sum_eq_single (y u) (fun a _ ha => sum_eq_zero fun c _ => by
      rw [ite_eq_right (show ¬(y u = a ∧ y v = c) from fun h => ha h.1.symm), mul_zero])
      (fun h => absurd (mem_univ _) h)]
    rw [sum_eq_single (y v) (fun c _ hc => by
      rw [ite_eq_right (show ¬(y u = y u ∧ y v = c) from fun h => hc h.2.symm), mul_zero])
      (fun h => absurd (mem_univ _) h)]
    simp
  calc ∑ a, ∑ c, ∑ y, μ.weight y * (if y u = a ∧ y v = c then (1 : ℝ) else 0)
      = ∑ y, ∑ a, ∑ c, μ.weight y * (if y u = a ∧ y v = c then (1 : ℝ) else 0) :=
        (sum_congr rfl fun a _ => sum_comm).trans sum_comm
    _ = ∑ y, μ.weight y := sum_congr rfl fun y _ => h y
    _ = 1 := μ.total

omit [DecidableEq F] in
/-- Two pair laws proportional to the same `φ` and both of total mass one coincide. -/
theorem prop_eq {q₁ q₂ φ : F → F → ℝ} {κ₁ κ₂ : ℝ} (h₁ : ∀ a c, q₁ a c = κ₁ * φ a c)
    (h₂ : ∀ a c, q₂ a c = κ₂ * φ a c) (s₁ : ∑ a, ∑ c, q₁ a c = 1) (s₂ : ∑ a, ∑ c, q₂ a c = 1)
    (a c : F) : q₁ a c = q₂ a c := by
  simp_rw [h₁, ← mul_sum] at s₁
  simp_rw [h₂, ← mul_sum] at s₂
  have hS : ∑ a, ∑ c, φ a c ≠ 0 := fun h0 => by rw [h0, mul_zero] at s₁; exact zero_ne_one s₁
  have : κ₁ = κ₂ := mul_right_cancel₀ hS (s₁.trans s₂.symm)
  rw [h₁, h₂, this]

end Pair

/-! ## The block pair law -/

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  {W : Type} [Fintype W] [DecidableEq W]

/-- **The pair law of a tensor law is the product of the one-prime pair laws.** -/
theorem expect_pair (μ : ∀ i, FiniteLaw (W → ZMod (pr i))) (u v : W)
    (H : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → ℝ) :
    (FiniteLaw.tensor μ).expect (fun y => H (y u) (y v)) =
      ∑ a, ∑ c, (∏ i, pw (μ i) u v (a i) (c i)) * H a c := by
  rw [expect_tensor_eq_sum]
  unfold pw
  simp_rw [Fintype.prod_sum (fun i y => (μ i).weight y *
    (if y u = _ ∧ y v = _ then (1 : ℝ) else 0)), sum_mul]
  have h : ∀ z : ∀ i, W → ZMod (pr i),
      ∑ a : ∀ i, ZMod (pr i), ∑ c : ∀ i, ZMod (pr i),
        (∏ i, (μ i).weight (z i) * (if z i u = a i ∧ z i v = c i then (1 : ℝ) else 0)) * H a c =
      (∏ i, (μ i).weight (z i)) * H (fun i => z i u) (fun i => z i v) := by
    intro z
    rw [sum_eq_single (fun i => z i u) (fun a _ ha => sum_eq_zero fun c _ => by
      obtain ⟨i, hi⟩ : ∃ i, z i u ≠ a i := by
        by_contra hc
        push Not at hc
        exact ha (funext fun i => (hc i).symm)
      rw [prod_eq_zero (mem_univ i) (by
        rw [ite_eq_right (show ¬(z i u = a i ∧ z i v = c i) from fun h => hi h.1), mul_zero]),
        zero_mul])
      (fun h => absurd (mem_univ _) h)]
    rw [sum_eq_single (fun i => z i v) (fun c _ hc => by
      obtain ⟨i, hi⟩ : ∃ i, z i v ≠ c i := by
        by_contra hc'
        push Not at hc'
        exact hc (funext fun i => (hc' i).symm)
      rw [prod_eq_zero (mem_univ i) (by
        rw [ite_eq_right (show ¬(z i u = z i u ∧ z i v = c i) from fun h => hi h.2), mul_zero]),
        zero_mul])
      (fun h => absurd (mem_univ _) h)]
    congr 1
    exact prod_congr rfl fun i _ => by simp
  exact (((sum_congr rfl fun a _ => sum_comm).trans sum_comm).trans
    (sum_congr rfl fun z _ => h z)).symm

end Tensor

/-! ## One prime -/

section Prime

variable {p : ℕ} [Fact p.Prime]

theorem sum_kP (hp2 : p ≠ 2) : ∑ d : ZMod p, kP p d = 1 := by
  have h := hatP_zero (p := p) hp2
  unfold hat1 at h
  simp_rw [ech_zero_left, mul_one] at h
  exact_mod_cast h

theorem sum_kD : ∑ d : ZMod p, kD p d = 1 := by
  have h := hatD_eq (p := p) 0
  rw [ite_eq_left rfl] at h
  unfold hat1 at h
  simp_rw [ech_zero_left, mul_one] at h
  exact_mod_cast h

/-- A kernel of mass one gives a pair law `p⁻¹ k(c − a)` of mass one. -/
theorem sum_kernel_pair {k : ZMod p → ℝ} (hk : ∑ d, k d = 1) :
    ∑ a : ZMod p, ∑ c : ZMod p, (1 / (p : ℝ)) * k (c - a) = 1 := by
  have h : ∀ a : ZMod p, ∑ c : ZMod p, (1 / (p : ℝ)) * k (c - a) = 1 / (p : ℝ) := by
    intro a
    rw [← mul_sum, Fintype.sum_equiv (Equiv.subRight a) (fun c => k (c - a)) k
      (fun c => rfl), hk, mul_one]
  rw [sum_congr rfl fun a _ => h a, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp

/-- **The Paley edge pair law**: `(y_0, y_1)` under the uniform strict Paley edge is
`p⁻¹ k_P(c − a)`. -/
theorem pw_edge (hp2 : p ≠ 2) (hne : (injLabellings (ZMod p) layerEdgeGraph).Nonempty)
    (a c : ZMod p) : pw (graphLaw layerEdgeGraph hne) 0 1 a c = (1 / (p : ℝ)) * kP p (c - a) := by
  have hmem : ∀ a c : ZMod p, (![a, c] ∈ injLabellings (ZMod p) layerEdgeGraph) ↔
      quadraticChar (ZMod p) (c - a) = 1 := by
    intro a c
    rw [mem_injLabellings_iff_feasible]
    constructor
    · rintro ⟨-, he⟩
      exact he ((0 : Fin 2), (1 : Fin 2)) (Finset.mem_singleton_self _) (mem_univ _) (mem_univ _)
    · intro hχ
      have hca : c - a ≠ 0 := ne_zero_of_quadraticChar_eq_one hχ
      refine ⟨fun x _ y _ hxy => ?_, fun e he _ _ => ?_⟩
      · fin_cases x <;> fin_cases y
        · rfl
        · exact absurd (sub_eq_zero.mpr hxy.symm) hca
        · exact absurd (sub_eq_zero.mpr hxy) hca
        · rfl
      · rw [Finset.mem_singleton.mp he]
        exact hχ
  have hpw : ∀ a c : ZMod p, pw (graphLaw layerEdgeGraph hne) 0 1 a c =
      (1 / ((injLabellings (ZMod p) layerEdgeGraph).card : ℝ)) *
        (if quadraticChar (ZMod p) (c - a) = 1 then 1 else 0) := by
    intro a c
    unfold pw
    rw [sum_eq_single ![a, c] (fun y _ hy => by
      rw [ite_eq_right (fun h => hy (funext fun x => by fin_cases x <;> simp [h.1, h.2])),
        mul_zero])
      (fun h => absurd (mem_univ _) h)]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, and_self, ↓reduceIte, mul_one]
    unfold graphLaw
    simp only [hmem]
    split_ifs <;> simp
  have h2 : ∀ a c : ZMod p, (1 / (p : ℝ)) * kP p (c - a) =
      (2 / ((p : ℝ) * ((p : ℝ) - 1))) *
        (if quadraticChar (ZMod p) (c - a) = 1 then 1 else 0) := by
    intro a c
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have : (p : ℝ) - 1 ≠ 0 := by have := p_gt_one (p := p); linarith
    unfold kP
    split_ifs
    · field_simp
    · simp
  exact prop_eq hpw h2 (sum_pw _ 0 1) (sum_kernel_pair (sum_kP hp2)) a c

/-- Every bijection of the labels preserves the `E` law. -/
theorem pw_match_perm (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)
    (u v : Fin 3 × Fin 2) (σ : ZMod p ≃ ZMod p) (a c : ZMod p) :
    pw (graphLaw (matchGraph (Fin 2)) hne) u v (σ a) (σ c) =
      pw (graphLaw (matchGraph (Fin 2)) hne) u v a c := by
  unfold pw
  have hmem : ∀ y : Fin 3 × Fin 2 → ZMod p,
      (fun w => σ (y w)) ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) ↔
        y ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) := by
    intro y
    rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨fun x hx z hz hxz => h1 x hx z hz (congrArg σ hxz),
        fun e he => absurd he (Finset.notMem_empty _)⟩
    · rintro ⟨h1, -⟩
      exact ⟨fun x hx z hz hxz => h1 x hx z hz (σ.injective hxz),
        fun e he => absurd he (Finset.notMem_empty _)⟩
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ => σ) _ _ fun y => ?_).symm
  change _ = (graphLaw (matchGraph (Fin 2)) hne).weight (fun w => σ (y w)) *
    (if σ (y u) = σ a ∧ σ (y v) = σ c then (1 : ℝ) else 0)
  simp only [σ.injective.eq_iff]
  congr 1
  unfold graphLaw
  simp only [hmem]

/-- **The `E` pair law**: `(y_{(0,0)}, y_{(0,1)})` under V1's `E` law is uniform on ordered distinct
pairs, `p⁻¹ k_D(c − a)`. -/
theorem pw_match (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)
    {u v : Fin 3 × Fin 2} (huv : u ≠ v) (a c : ZMod p) :
    pw (graphLaw (matchGraph (Fin 2)) hne) u v a c = (1 / (p : ℝ)) * kD p (c - a) := by
  set q := pw (graphLaw (matchGraph (Fin 2)) hne) u v
  have h10 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have hdiag : ∀ a, q a a = 0 := by
    intro a
    refine sum_eq_zero fun y _ => ?_
    by_cases hy : y ∈ injLabellings (ZMod p) (matchGraph (Fin 2))
    · rw [mem_injLabellings_iff_feasible] at hy
      have : ¬ (y u = a ∧ y v = a) := fun h =>
        huv (hy.1 u (mem_univ _) v (mem_univ _) (h.1.trans h.2.symm))
      rw [ite_eq_right this, mul_zero]
    · change (if y ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) then _ else 0) * _ = 0
      rw [ite_eq_right hy, zero_mul]
  have hoff : ∀ a c, a ≠ c → q a c = q 0 1 := by
    intro a c hac
    set x := Equiv.swap (0 : ZMod p) a 1
    have hxa : a ≠ x := by
      intro h
      have : Equiv.swap (0 : ZMod p) a 0 = Equiv.swap (0 : ZMod p) a 1 := by
        rw [Equiv.swap_apply_left]; exact h
      exact h10 ((Equiv.swap (0 : ZMod p) a).injective this).symm
    let σ := (Equiv.swap (0 : ZMod p) a).trans (Equiv.swap x c)
    have h0 : σ 0 = a := by
      change Equiv.swap x c (Equiv.swap 0 a 0) = a
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hxa hac]
    have h1 : σ 1 = c := by
      change Equiv.swap x c (Equiv.swap 0 a 1) = c
      exact Equiv.swap_apply_left x c
    rw [← h0, ← h1]
    exact pw_match_perm hne u v σ 0 1
  have hq : ∀ a c, q a c = q 0 1 * (if c - a = 0 then 0 else 1) := by
    intro a c
    by_cases h : c - a = 0
    · rw [sub_eq_zero.mp h, hdiag, ite_eq_left (sub_self a), mul_zero]
    · rw [ite_eq_right h, mul_one]
      exact hoff a c (fun h' => h (by rw [h', sub_self]))
  have h2 : ∀ a c : ZMod p, (1 / (p : ℝ)) * kD p (c - a) =
      (1 / ((p : ℝ) * ((p : ℝ) - 1))) * (if c - a = 0 then 0 else 1) := by
    intro a c
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
    have : (p : ℝ) - 1 ≠ 0 := by have := p_gt_one (p := p); linarith
    unfold kD
    split_ifs
    · simp
    · field_simp
  exact prop_eq hq h2 (sum_pw _ _ _) (sum_kernel_pair sum_kD) a c

end Prime

/-! ## The block pair laws of the constant records -/

section BlockPair

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- `N⁻¹ = ∏_i p_i⁻¹`. -/
noncomputable def invN : ℝ := ∏ i, (1 / (pr i : ℝ))

omit [DecidableEq ι] in
theorem invN_pos : 0 < invN pr :=
  prod_pos fun i _ => one_div_pos.mpr (by exact_mod_cast (Fact.out : (pr i).Prime).pos)

/-- **The pair law of V1's `E` law at two distinct vertices** (the old constant record reads the
object `0` in both layers; the old merge records read the objects `0, 1` of one layer). -/
theorem expect_pair_match (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph (Fin 2))).Nonempty)
    (H : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → ℝ) {u v : Fin 3 × Fin 2} (huv : u ≠ v) :
    (blockGraphLaw pr (matchGraph (Fin 2)) hE).expect (fun y => H (y u) (y v)) =
      ∑ a, ∑ c, (invN pr * KD pr (c - a)) * H a c := by
  unfold blockGraphLaw
  rw [expect_pair]
  refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
  congr 1
  unfold invN KD
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => pw_match (hE i) huv (a i) (c i)

/-- **The constant replacement's pair law** (the strict Paley edge at every prime). -/
theorem expect_pair_edge (hp2 : ∀ i, pr i ≠ 2)
    (H : (∀ i, ZMod (pr i)) → (∀ i, ZMod (pr i)) → ℝ) :
    (blockGraphLaw pr layerEdgeGraph (layerEdge_nonempty pr)).expect (fun y => H (y 0) (y 1)) =
      ∑ a, ∑ c, (invN pr * KP pr (c - a)) * H a c := by
  unfold blockGraphLaw
  rw [expect_pair]
  refine sum_congr rfl fun a _ => sum_congr rfl fun c _ => ?_
  congr 1
  unfold invN KP
  rw [← prod_mul_distrib]
  exact prod_congr rfl fun i _ => pw_edge (hp2 i) _ (a i) (c i)

end BlockPair

end Sarkozy.NormBoundsPaper

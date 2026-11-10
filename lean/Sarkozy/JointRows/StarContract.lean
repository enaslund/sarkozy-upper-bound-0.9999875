module

public import Sarkozy.JointRows.StarPure

/-!
# The contraction `𝓕_X` (`prop:conditional-star`, Step 1), on the actual operators

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`, Step 1: "As the
ranges are orthogonal, `𝓕_X((f_i)_i, (g_S)_S) = ∑_i U_i f_i/√κ + ∑_S W_S g_S/(√κ r)` is a
contraction from `ℋ^X ⊕ ℋ^{𝒮_X}` into `L²_0(ν_X)`".

* `uOp νp i u x = u(x_i) - E_{ν_i} u`: the centred evaluation `U_i`; `uOp_exactSupport`
  (`U_i u ∈ H_{{i}}`), `ip_uOp_self_le` (`‖U_i‖ ≤ √κ`), `ip_uOp_adj` (`U_i^*` is `uStar` on
  mean-zero functions);
* `featMap`: the map `𝓕_X`; **`featMap_norm_le`**: it is a contraction, for coordinate laws with
  densities at most `κ` and sets `S ∈ 𝒮` with at least two elements (by the Hoeffding
  orthogonality `Star.hoeffding_orthogonal`, `‖U_i‖ ≤ √κ` and `‖W_S‖ ≤ √κ r`);
* **`featStar_norm_le`**: `‖𝓕_X^* f‖ ≤ ‖f‖` for `f ∈ L²_0(ν_X)`, where
  `𝓕_X^* f = (StarOps.featU νp κ f, StarOps.featW νp κ f)` is the feature vector of
  `pure_block_identity`. This is the bound `hV` of `lem:joint-rows`(a) for one row.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The centred evaluation `U_i u = u(x_i) - E_{ν_i} u`. -/
noncomputable def uOp (νp : X → FiniteLaw (ZMod p)) (i : X) (u : ZMod p → ℝ) (x : X → ZMod p) :
    ℝ :=
  u (x i) - (νp i).expect u

/-- The map `𝓕_X(u, w) = ∑_i U_i u_i/√κ + ∑_{S∈𝒮} W_S w_S/(√κ r)`, `r = p^{-1/2}`. -/
noncomputable def featMap (νp : X → FiniteLaw (ZMod p)) (κ : ℝ) (𝒮 : Finset (Finset X))
    (u : X → ZMod p → ℝ) (w : Finset X → ZMod p → ℝ) (x : X → ZMod p) : ℝ :=
  (∑ i, (Real.sqrt κ)⁻¹ * uOp νp i (u i) x) +
    ∑ S ∈ 𝒮, (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wOp νp S (w S) x

/-- The marginal of a product law: `E_{x∼ν_X} h(x_i) = E_{ν_i} h`. -/
theorem expect_eval (νp : X → FiniteLaw (ZMod p)) (i : X) (h : ZMod p → ℝ) :
    (blockLaw νp).expect (fun x => h (x i)) = (νp i).expect h := by
  have := expect_prod_mem νp {i} (fun _ => h)
  simpa only [Finset.prod_singleton] using this

omit [Fintype X] in
theorem exactSupport_const_mul (νp : X → FiniteLaw (ZMod p)) {R : Finset X}
    {h : (X → ZMod p) → ℝ} (hh : Star.ExactSupport νp R h) (c : ℝ) :
    Star.ExactSupport νp R (fun x => c * h x) where
  depends x x' hxx' := by rw [hh.depends x x' hxx']
  centred i hi x := by
    have := hh.centred i hi x
    unfold Star.condMean at this ⊢
    rw [show ∑ t, (νp i).weight t * (c * h (Function.update x i t)) =
        c * ∑ t, (νp i).weight t * h (Function.update x i t) by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring, this, mul_zero]

omit [Fintype X] in
/-- `U_i u ∈ H_{{i}}`. -/
theorem uOp_exactSupport (νp : X → FiniteLaw (ZMod p)) (i : X) (u : ZMod p → ℝ) :
    Star.ExactSupport νp {i} (uOp νp i u) where
  depends x x' hxx' := by
    unfold uOp
    rw [hxx' i (Finset.mem_singleton_self i)]
  centred k hk x := by
    rw [Finset.mem_singleton] at hk
    subst hk
    unfold Star.condMean uOp
    simp only [Function.update_self]
    rw [show ∑ t, (νp k).weight t * (u t - (νp k).expect u) =
        (νp k).expect (fun t => u t - (νp k).expect u) from rfl, FiniteLaw.expect_sub,
      FiniteLaw.expect_const, sub_self]

/-- **`‖U_i‖ ≤ √κ`**: `‖U_i u‖²_{ν_X} ≤ κ ‖u‖²` for `ν_i(a) ≤ κ/p`. -/
theorem ip_uOp_self_le (νp : X → FiniteLaw (ZMod p)) (i : X) {κ : ℝ}
    (hκ : ∀ a, (νp i).weight a ≤ κ / p) (u : ZMod p → ℝ) :
    ip (blockLaw νp) (uOp νp i u) (uOp νp i u) ≤ κ * ip (FiniteLaw.uniform (ZMod p)) u u := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold ip uOp
  rw [expect_eval νp i (fun a => (u a - (νp i).expect u) * (u a - (νp i).expect u))]
  have h1 : (νp i).expect (fun a => (u a - (νp i).expect u) * (u a - (νp i).expect u)) =
      (νp i).expect (fun a => u a ^ 2) - (νp i).expect u ^ 2 := by
    rw [← FiniteLaw.expect_sq_sub_mean]
    exact FiniteLaw.expect_congr _ fun a => by ring
  have h2 : (νp i).expect (fun a => u a ^ 2) ≤ κ * (FiniteLaw.uniform (ZMod p)).expect
      (fun a => u a * u a) := by
    rw [FiniteLaw.expect_uniform, ZMod.card]
    unfold FiniteLaw.expect
    rw [mul_div_assoc', Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_le_sum fun a _ => by
      simp only [sq]
      rw [show κ * (u a * u a) / p = κ / p * (u a * u a) by ring]
      exact mul_le_mul_of_nonneg_right (hκ a) (mul_self_nonneg _)
  have h3 := sq_nonneg ((νp i).expect u)
  linarith

/-- **`U_i^*` on mean-zero functions**: `⟨U_i u, f⟩_{ν_X} = ⟨u, U_i^* f⟩` for `E f = 0`. -/
theorem ip_uOp_adj (νp : X → FiniteLaw (ZMod p)) (i : X) (u : ZMod p → ℝ)
    {f : (X → ZMod p) → ℝ} (hf : (blockLaw νp).expect f = 0) :
    ip (blockLaw νp) (uOp νp i u) f = ip (FiniteLaw.uniform (ZMod p)) u (uStar νp i f) := by
  unfold ip uOp
  rw [show (fun x => (u (x i) - (νp i).expect u) * f x) =
      fun x => u (x i) * f x - (νp i).expect u * f x from funext fun x => by ring,
    FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, hf, mul_zero, sub_zero, expect_eval_mul]

omit [DecidableEq X] in
theorem ip_sum_sum {Ω' ι ι' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω') (s : Finset ι)
    (v : ι → Ω' → ℝ) (t : Finset ι') (w : ι' → Ω' → ℝ) :
    ip μ (fun x => ∑ i ∈ s, v i x) (fun x => ∑ j ∈ t, w j x) =
      ∑ i ∈ s, ∑ j ∈ t, ip μ (v i) (w j) := by
  unfold ip
  simp only [Finset.sum_mul_sum, expect_finset_sum]

omit [DecidableEq X] in
theorem ip_add_add {Ω' : Type*} [Fintype Ω'] (μ : FiniteLaw Ω') (a b c d : Ω' → ℝ) :
    ip μ (fun x => a x + b x) (fun x => c x + d x) =
      ip μ a c + ip μ a d + ip μ b c + ip μ b d := by
  unfold ip
  rw [show (fun x => (a x + b x) * (c x + d x)) =
      fun x => a x * c x + a x * d x + b x * c x + b x * d x from funext fun x => by ring,
    FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_add]

omit [Fintype X] [DecidableEq X] in
theorem sum_sum_diag {ι : Type*} [DecidableEq ι] (s : Finset ι) (F : ι → ι → ℝ)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → F i j = 0) : ∑ i ∈ s, ∑ j ∈ s, F i j = ∑ i ∈ s, F i i :=
  Finset.sum_congr rfl fun i hi =>
    Finset.sum_eq_single i (fun j hj hji => h i hi j hj (Ne.symm hji)) (fun hi' => absurd hi hi')

/-- **`𝓕_X` is a contraction** (Step 1): `‖𝓕_X(u, w)‖² ≤ ∑_i ‖u_i‖² + ∑_{S∈𝒮} ‖w_S‖²` if every
`ν_i` has density at most `κ` and every `S ∈ 𝒮` has at least two elements. -/
theorem featMap_norm_le (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (𝒮 : Finset (Finset X))
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) (u : X → ZMod p → ℝ) (w : Finset X → ZMod p → ℝ) :
    ip (blockLaw νp) (featMap νp κ 𝒮 u w) (featMap νp κ 𝒮 u w) ≤
      (∑ i, ip (FiniteLaw.uniform (ZMod p)) (u i) (u i)) +
        ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (w S) (w S) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  set c : ℝ := (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ with hc
  set a : X → (X → ZMod p) → ℝ := fun i x => (Real.sqrt κ)⁻¹ * uOp νp i (u i) x with ha
  set b : Finset X → (X → ZMod p) → ℝ := fun S x => c * wOp νp S (w S) x with hb
  have hF : featMap νp κ 𝒮 u w = fun x => (∑ i, a i x) + ∑ S ∈ 𝒮, b S x := rfl
  have haS : ∀ i, Star.ExactSupport νp {i} (a i) := fun i =>
    exactSupport_const_mul νp (uOp_exactSupport νp i (u i)) _
  have hbS : ∀ S, Star.ExactSupport νp S (b S) := fun S =>
    exactSupport_const_mul νp (wOp_exactSupport νp S (w S)) _
  have hne : ∀ i, ∀ S ∈ 𝒮, ({i} : Finset X) ≠ S := fun i S hS hiS => by
    have := h𝒮 S hS
    rw [← hiS, Finset.card_singleton] at this
    omega
  rw [hF, ip_add_add, ip_sum_sum, ip_sum_sum, ip_sum_sum, ip_sum_sum]
  have haa : ∑ i, ∑ j, ip (blockLaw νp) (a i) (a j) = ∑ i, ip (blockLaw νp) (a i) (a i) :=
    sum_sum_diag _ _ fun i _ j _ hij => Star.hoeffding_orthogonal νp
      (by rw [Ne, Finset.singleton_inj]; exact hij) (haS i) (haS j)
  have hab : ∑ i, ∑ S ∈ 𝒮, ip (blockLaw νp) (a i) (b S) = 0 :=
    Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun S hS =>
      Star.hoeffding_orthogonal νp (hne i S hS) (haS i) (hbS S)
  have hba : ∑ S ∈ 𝒮, ∑ i, ip (blockLaw νp) (b S) (a i) = 0 :=
    Finset.sum_eq_zero fun S hS => Finset.sum_eq_zero fun i _ =>
      Star.hoeffding_orthogonal νp (Ne.symm (hne i S hS)) (hbS S) (haS i)
  have hbb : ∑ S ∈ 𝒮, ∑ T ∈ 𝒮, ip (blockLaw νp) (b S) (b T) =
      ∑ S ∈ 𝒮, ip (blockLaw νp) (b S) (b S) :=
    sum_sum_diag _ _ fun S _ T _ hST => Star.hoeffding_orthogonal νp hST (hbS S) (hbS T)
  rw [haa, hab, hba, hbb, add_zero, add_zero]
  have hka : ∀ i, ip (blockLaw νp) (a i) (a i) ≤ ip (FiniteLaw.uniform (ZMod p)) (u i) (u i) := by
    intro i
    have h1 := ip_uOp_self_le νp i (hdens i) (u i)
    have h2 : ip (blockLaw νp) (a i) (a i) =
        κ⁻¹ * ip (blockLaw νp) (uOp νp i (u i)) (uOp νp i (u i)) := by
      simp only [ha, ip]
      rw [← FiniteLaw.expect_const_mul]
      refine FiniteLaw.expect_congr _ fun x => ?_
      have hk : (Real.sqrt κ)⁻¹ * (Real.sqrt κ)⁻¹ = κ⁻¹ := by
        rw [← mul_inv, Real.mul_self_sqrt hκ.le]
      linear_combination (uOp νp i (u i) x * uOp νp i (u i) x) * hk
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (inv_nonneg.mpr hκ.le)
    rwa [← mul_assoc, inv_mul_cancel₀ hκ.ne', one_mul] at h3
  have hkb : ∀ S ∈ 𝒮, ip (blockLaw νp) (b S) (b S) ≤
      ip (FiniteLaw.uniform (ZMod p)) (w S) (w S) := by
    intro S hS
    have hSne : S.Nonempty := Finset.card_pos.mp (by have := h𝒮 S hS; omega)
    have h1 := wOp_norm_le hp νp S hSne (fun i _ a => hdens i a) (w S)
    have h2 : ip (blockLaw νp) (b S) (b S) = c * c * ip (blockLaw νp) (wOp νp S (w S))
        (wOp νp S (w S)) := by
      simp only [hb, ip]
      rw [← FiniteLaw.expect_const_mul]
      exact FiniteLaw.expect_congr _ fun x => by ring
    have hcc : c * c * (κ * (p : ℝ)⁻¹) = 1 := by
      rw [hc, ← mul_inv, mul_inv]
      have hsp0 : Real.sqrt p ≠ 0 := by positivity
      have hsκ0 : Real.sqrt κ ≠ 0 := by positivity
      field_simp
      rw [Real.sq_sqrt hp0.le, Real.sq_sqrt hκ.le]
      ring
    rw [h2]
    have h3 := mul_le_mul_of_nonneg_left h1 (mul_self_nonneg c)
    calc c * c * ip (blockLaw νp) (wOp νp S (w S)) (wOp νp S (w S))
        ≤ c * c * (κ * (p : ℝ)⁻¹ * ip (FiniteLaw.uniform (ZMod p)) (w S) (w S)) := h3
      _ = ip (FiniteLaw.uniform (ZMod p)) (w S) (w S) := by
        rw [← mul_assoc, hcc, one_mul]
  exact add_le_add (Finset.sum_le_sum fun i _ => hka i) (Finset.sum_le_sum hkb)

/-- **`‖𝓕_X^* f‖ ≤ ‖f‖`** for `f ∈ L²_0(ν_X)`: the feature vector of `pure_block_identity`
has norm at most `‖f‖`. This is `hV` of `lem:joint-rows`(a) for one row. -/
theorem featStar_norm_le (hp : p % 4 = 3) (νp : X → FiniteLaw (ZMod p)) {κ : ℝ} (hκ : 0 < κ)
    (hdens : ∀ i a, (νp i).weight a ≤ κ / p) (𝒮 : Finset (Finset X))
    (h𝒮 : ∀ S ∈ 𝒮, 2 ≤ S.card) {f : (X → ZMod p) → ℝ} (hf : (blockLaw νp).expect f = 0) :
    (∑ i, ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i) (featU νp κ f i)) +
        ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S) (featW νp κ f S) ≤
      ip (blockLaw νp) f f := by
  set N : ℝ := (∑ i, ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i) (featU νp κ f i)) +
    ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S) (featW νp κ f S) with hN
  set F := featMap νp κ 𝒮 (featU νp κ f) (featW νp κ f) with hFdef
  -- the adjoint identity `⟨𝓕(𝓕^* f), f⟩ = ‖𝓕^* f‖²`
  have hadj : ip (blockLaw νp) F f = N := by
    have hU : ∀ i, ip (blockLaw νp) (fun x => (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x) f =
        ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i) (featU νp κ f i) := by
      intro i
      have h1 := ip_uOp_adj νp i (featU νp κ f i) hf
      unfold ip at h1 ⊢
      rw [show (fun x => (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x * f x) =
          fun x => (Real.sqrt κ)⁻¹ * (uOp νp i (featU νp κ f i) x * f x) from
          funext fun x => by ring, FiniteLaw.expect_const_mul, h1, ← FiniteLaw.expect_const_mul]
      exact FiniteLaw.expect_congr _ fun a => by unfold featU; ring
    have hW : ∀ S, ip (blockLaw νp) (fun x => (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ *
        wOp νp S (featW νp κ f S) x) f =
        ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S) (featW νp κ f S) := by
      intro S
      have h1 := ip_wOp νp S (featW νp κ f S) f
      set c : ℝ := (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ with hc
      have hcen : featW νp κ f S =
          cen (FiniteLaw.uniform (ZMod p)) (fun t => c * wStar νp S f t) := by
        funext t; unfold featW cen; rw [FiniteLaw.expect_const_mul, hc]; ring
      have hmean : (FiniteLaw.uniform (ZMod p)).expect (featW νp κ f S) = 0 := by
        rw [hcen]; unfold cen
        rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]
      unfold ip at h1 ⊢
      rw [show (fun x => c * wOp νp S (featW νp κ f S) x * f x) =
          fun x => c * (wOp νp S (featW νp κ f S) x * f x) from funext fun x => by ring,
        FiniteLaw.expect_const_mul, h1, ← FiniteLaw.expect_const_mul]
      -- `c ⟨w, W^* f⟩ = ⟨w, w⟩` for `w = cen (c W^* f)`, which has mean zero
      have hw : ∀ t, c * wStar νp S f t = featW νp κ f S t +
          (FiniteLaw.uniform (ZMod p)).expect (fun t => c * wStar νp S f t) := by
        intro t; rw [hcen]; unfold cen; ring
      calc (FiniteLaw.uniform (ZMod p)).expect (fun ω => c * (featW νp κ f S ω * wStar νp S f ω))
          = (FiniteLaw.uniform (ZMod p)).expect (fun ω => featW νp κ f S ω * featW νp κ f S ω +
              (FiniteLaw.uniform (ZMod p)).expect (fun t => c * wStar νp S f t) *
                featW νp κ f S ω) :=
            FiniteLaw.expect_congr _ fun ω => by
              rw [show c * (featW νp κ f S ω * wStar νp S f ω) =
                featW νp κ f S ω * (c * wStar νp S f ω) by ring, hw ω]
              ring
        _ = _ := by rw [FiniteLaw.expect_add, FiniteLaw.expect_const_mul, hmean, mul_zero, add_zero]
    rw [hFdef]
    unfold featMap
    have hsplit := ip_add_add (blockLaw νp)
    unfold ip at hU hW ⊢
    rw [show (fun x => ((∑ i, (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x) +
        ∑ S ∈ 𝒮, (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wOp νp S (featW νp κ f S) x) * f x) =
        fun x => (∑ i, (Real.sqrt κ)⁻¹ * uOp νp i (featU νp κ f i) x * f x) +
          ∑ S ∈ 𝒮, (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wOp νp S (featW νp κ f S) x * f x from
        funext fun x => by rw [add_mul, Finset.sum_mul, Finset.sum_mul],
      FiniteLaw.expect_add, expect_finset_sum, expect_finset_sum]
    simp only [hU, hW, hN, ip]
  -- Cauchy–Schwarz and the contraction
  have hN0 : 0 ≤ N := by
    rw [hN]
    exact add_nonneg (Finset.sum_nonneg fun i _ => FiniteLaw.expect_nonneg _ fun _ =>
      mul_self_nonneg _) (Finset.sum_nonneg fun S _ => FiniteLaw.expect_nonneg _ fun _ =>
      mul_self_nonneg _)
  have hC := featMap_norm_le hp νp hκ hdens 𝒮 h𝒮 (featU νp κ f) (featW νp κ f)
  rw [← hFdef, ← hN] at hC
  have hcs := FiniteLaw.cauchy_schwarz_sq (blockLaw νp) F f
  have hsq : ∀ g : (X → ZMod p) → ℝ, (blockLaw νp).expect (fun x => g x ^ 2) =
      ip (blockLaw νp) g g := fun g => FiniteLaw.expect_congr _ fun x => sq (g x)
  rw [hsq, hsq] at hcs
  unfold ip at hadj
  rw [hadj] at hcs
  have hff : 0 ≤ ip (blockLaw νp) f f := FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  -- `N² ≤ ‖F‖² ‖f‖² ≤ N ‖f‖²`
  have h2 : N ^ 2 ≤ N * ip (blockLaw νp) f f := hcs.trans (mul_le_mul_of_nonneg_right hC hff)
  by_cases hN' : N = 0
  · rw [hN']; exact hff
  · have hNpos : 0 < N := lt_of_le_of_ne hN0 (Ne.symm hN')
    nlinarith

end Sarkozy.JointRows.StarOps

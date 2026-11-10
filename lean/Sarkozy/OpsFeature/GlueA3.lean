module

public import Sarkozy.OpsFeature.GlueChart
public import Sarkozy.MiddleRecords.ActualFeaturesNorms

@[expose] public section

/-!
# The label-`3` arms are contractions (`lem:actual-features`(e), `hcon3`)

`paper/sections/23_envelopes.tex`, `eq:signed-star` ("`A₃°` … a map of norm at most `r_p`");
`paper/sections/21_middle_records.tex`, `lem:actual-features`(c), (e).

* `Acp h = A₃ h − GA h` on pairs (OPS-L's `A₃° h`), `Acp_kernel` (linear in `h`), `K3_sum`
  (`∑_z c_z K(·; z) = A₃°(c − c̄)`);
* **`Acp_norm`**: `‖A₃° h‖²_{m₁₂} ≤ q ‖h‖²` for mean-zero `h`, from W6's `norm_A3_sq_le`
  (`‖A₃ h‖² ≤ q ‖h‖²`) and OPS-L's `A3_perp` (`A₃° h ⊥ GA h`);
* **`yThree_contraction`**: the label-`3` arms of the chart are contractions in `L²(m_{0,𝔅})`, the
  input `hcon3` of `hUa_three_chart`;
* `yT_orth` (prime: `A₃° ⊥ u(x₁) + v(x₂)`, OPS-L's `A3_perp`), `sum_mB_prod`, `block_orth_of_prime`,
  **`yThree_orth1`**, **`yThree_orth2`**: the inputs `hy1`, `hy2` (`A₃° ∈ 𝒦₁₂` at the block);
* **`hUa_fold_A3`**: `hUa` of `hdom_of_units` at a fold block for all four labels, with only the
  unit-lift identification and the block edge `12` (`hcor`) as inputs.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.OpsCore Sarkozy.SignedGram Sarkozy.PrimeGram Sarkozy.MiddleRecords
  Sarkozy.Envelopes Sarkozy.PartV

section Prime

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- `A₃° h = A₃ h − GA h` as a function of the pair `(x₁, x₂)`. -/
noncomputable def Acp (h : F → ℝ) (c1 c2 : F) : ℝ := A3op h c1 c2 - (uA h c1 + vA h c2)

theorem Acp_kernel (h : F → ℝ) (c1 c2 : F) :
    Acp h c1 c2 = ∑ s, h s * Acp (PrimeGram.delta s) c1 c2 := by
  have k1 := A3_kernel (F := F) h ![c1, c1, c2]
  have k2 := GA_kernel (F := F) h ![c1, c1, c2]
  simp only [A3, GA, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons] at k1 k2
  unfold Acp
  rw [k1, k2, ← sum_sub_distrib]
  exact sum_congr rfl fun s _ => by ring

theorem K3_sum (c : F → ℝ) (c1 c2 : F) :
    ∑ z, c z * K3 c1 c2 z =
      Acp (fun s => c s - (Fintype.card F : ℝ)⁻¹ * ∑ w, c w) c1 c2 := by
  rw [Acp_kernel]
  have e : ∀ z, K3 c1 c2 z = Acp (PrimeGram.delta z) c1 c2 -
      (Fintype.card F : ℝ)⁻¹ * ∑ s, Acp (PrimeGram.delta s) c1 c2 := fun z => rfl
  simp only [e, mul_sub, sub_mul, sum_sub_distrib]
  congr 1
  rw [← sum_mul, ← mul_sum]
  ring

/-- **`‖A₃° h‖² ≤ q ‖h‖²`** in the pair law, for mean-zero `h`. -/
theorem Acp_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3)
    (h7 : 7 ≤ (Fintype.card F : ℝ)) (h : F → ℝ) (hh : ∑ s, h s = 0) :
    ip12 (Acp h) (Acp h) ≤ (Fintype.card F : ℝ)⁻¹ * unifNormSq h := by
  have hperp := A3_perp hF h3 h7 h hh (uA h) (vA h) (sum_vA hF h3 h hh)
  have hm : ∀ a b, 0 ≤ m12 (F := F) a b := fun a b =>
    div_nonneg (sum_nonneg fun x _ => oldW_nonneg h7 _ _ _) (oldZ_pos hF h3 h7).le
  have hA := norm_A3_sq_le hF h3 h7 h hh
  have split : ∑ a, ∑ b, m12 a b * A3op h a b ^ 2 = ip12 (Acp h) (Acp h) +
      2 * ip12 (fun a b => A3op h a b - (uA h a + vA h b)) (fun a b => uA h a + vA h b) +
      ip12 (fun a b => uA h a + vA h b) (fun a b => uA h a + vA h b) := by
    unfold ip12 Acp
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => by ring
  have hG : 0 ≤ ip12 (fun a b => uA h a + vA h b) (fun a b => uA h a + vA h b) := by
    unfold ip12
    exact sum_nonneg fun a _ => sum_nonneg fun b _ => by
      have := hm a b; nlinarith [sq_nonneg (uA h a + vA h b)]
  rw [split, hperp] at hA
  linarith

end Prime

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]

omit [Fintype ι] [DecidableEq ι] in
/-- The prime law of the block on pair functions is W6's pair law `m₁₂`. -/
theorem mP_pair2 (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (j : ι) (f g : ZMod (pr j) → ZMod (pr j) → ℝ) :
    ∑ b : Ai pr j, mP hne j b * (f (b 1) (b 2) * g (b 1) (b 2)) = ip12 f g := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 j
  rw [← mip_pair f g]
  unfold mip m0W
  refine sum_congr rfl fun b _ => ?_
  unfold mP
  rw [m0_eq_oldW (hne.F2 j) hR h3' h19']
  ring

/-- **The label-`3` arms of the chart are contractions** (`hcon3` of `hUa_three_chart`;
`‖A₃°/r_p‖ ≤ 1`, `lem:actual-features`(e)). -/
theorem yThree_contraction (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3)
    (h19 : ∀ i, 19 ≤ pr i) (j : ι) (c : ZMod (pr j) → ℝ) :
    EnvelopeSteps.ip (mB hne) (∑ z, c z • yThree hne j z) (∑ z, c z • yThree hne j z) ≤
      ∑ z, c z ^ 2 := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 j
  set q : ℝ := (Fintype.card (ZMod (pr j)) : ℝ) with hqdef
  have hq : 0 < q := by rw [hqdef]; exact_mod_cast Fintype.card_pos
  have h7 : (7 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast le_trans (by norm_num) h19'
  set W : Ai pr j → ℝ := fun b => ∑ z, c z * K3 (b 1) (b 2) z with hW
  set EW := ∑ b : Ai pr j, mP hne j b * W b with hEW
  have hsum : ∀ x : ∀ i, Ai pr i, (∑ z, c z • yThree hne j z) x = q * (W (x j) - EW) := by
    intro x
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, yThree, ← hqdef, hW, hEW]
    have e : ∀ z, c z * (q * (K3 (x j 1) (x j 2) z - ∑ b, mP hne j b * K3 (b 1) (b 2) z)) =
        q * (c z * K3 (x j 1) (x j 2) z) - ∑ b, q * (mP hne j b * (c z * K3 (b 1) (b 2) z)) := by
      intro z
      rw [mul_sub, mul_sum, mul_sub, mul_sum]
      congr 1
      · ring
      · exact sum_congr rfl fun b _ => by ring
    rw [sum_congr rfl fun z _ => e z, sum_sub_distrib, sum_comm, mul_sub, mul_sum, mul_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [mul_sum, mul_sum]
  unfold EnvelopeSteps.ip
  simp only [hsum]
  rw [sum_mB_coord hne j (fun b => q * (W b - EW) * (q * (W b - EW)))]
  -- `∑ m (q(W − EW))² = q² (∑ m W² − EW²) ≤ q² ∑ m W²`
  have ht := mP_total hne j
  have hvar : ∑ b : Ai pr j, mP hne j b * (q * (W b - EW) * (q * (W b - EW))) =
      q ^ 2 * (∑ b : Ai pr j, mP hne j b * (W b * W b)) - q ^ 2 * EW ^ 2 := by
    have e2 : ∀ b : Ai pr j, mP hne j b * (q * (W b - EW) * (q * (W b - EW))) =
        q ^ 2 * (mP hne j b * (W b * W b)) - 2 * q ^ 2 * EW * (mP hne j b * W b) +
          q ^ 2 * EW ^ 2 * mP hne j b := fun b => by ring
    simp only [e2, sum_add_distrib, sum_sub_distrib, ← mul_sum, ht, ← hEW]
    ring
  rw [hvar]
  -- `∑ m W² = ‖A₃°(c − c̄)‖²_{m₁₂} ≤ q⁻² ∑ c²`
  set h : ZMod (pr j) → ℝ := fun s => c s - q⁻¹ * ∑ w, c w with hh
  have hW' : ∀ b : Ai pr j, W b = Acp h (b 1) (b 2) := fun b => K3_sum c (b 1) (b 2)
  have hmean : ∑ s, h s = 0 := by
    simp only [hh, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, ← hqdef]
    rw [← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul, sub_self]
  have hN := Acp_norm hR h3' h7 h hmean
  have hpair := mP_pair2 hne h3 h19 j (Acp h) (Acp h)
  have hWW : ∑ b : Ai pr j, mP hne j b * (W b * W b) = ip12 (Acp h) (Acp h) := by
    rw [← hpair]
    exact sum_congr rfl fun b _ => by rw [hW']
  have hvarc : ∑ s, h s ^ 2 ≤ ∑ z, c z ^ 2 := by
    set cbar := q⁻¹ * ∑ w, c w with hcbar
    have e3 : ∑ s, h s ^ 2 = ∑ z, c z ^ 2 - q * cbar ^ 2 := by
      have h1 : ∑ s, h s ^ 2 = ∑ w, c w ^ 2 - 2 * cbar * ∑ w, c w +
          ∑ _w : ZMod (pr j), cbar ^ 2 := by
        simp only [hh]
        rw [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
        exact sum_congr rfl fun w _ => by ring
      rw [h1, sum_const, card_univ, nsmul_eq_mul, ← hqdef]
      have h2 : ∑ w, c w = q * cbar := by
        rw [hcbar, ← mul_assoc, mul_inv_cancel₀ hq.ne', one_mul]
      rw [h2]
      ring
    rw [e3]
    have : 0 ≤ q * cbar ^ 2 := by positivity
    linarith
  have hU : unifNormSq h = q⁻¹ * ∑ s, h s ^ 2 := rfl
  rw [hWW]
  have hEW2 : 0 ≤ q ^ 2 * EW ^ 2 := by positivity
  have key : q ^ 2 * ip12 (Acp h) (Acp h) ≤ ∑ z, c z ^ 2 := by
    have h1 : ip12 (Acp h) (Acp h) ≤ q⁻¹ * (q⁻¹ * ∑ s, h s ^ 2) := by rw [← hU]; exact hN
    have h2 : q ^ 2 * (q⁻¹ * (q⁻¹ * ∑ s, h s ^ 2)) = ∑ s, h s ^ 2 := by
      field_simp
    calc q ^ 2 * ip12 (Acp h) (Acp h) ≤ q ^ 2 * (q⁻¹ * (q⁻¹ * ∑ s, h s ^ 2)) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ∑ s, h s ^ 2 := h2
      _ ≤ ∑ z, c z ^ 2 := hvarc
  linarith

/-- Integrals of product functions under the block law. -/
theorem sum_mB_prod (hne : MiddleNonempty pr) (j : ι) (G : Ai pr j → ℝ)
    (f : ∀ i, Ai pr i → ℝ) :
    ∑ x, mB hne x * (G (x j) * ∏ i, f i (x i)) =
      (∑ b, mP hne j b * (G b * f j b)) * ∏ i ∈ univ.erase j, ∑ c, mP hne i c * f i c := by
  set h : ∀ i, Ai pr i → ℝ :=
    Function.update (fun i c => mP hne i c * f i c) j (fun c => mP hne j c * (G c * f j c))
    with hh
  have e1 : ∀ x : (∀ i, Ai pr i), mB hne x * (G (x j) * ∏ i, f i (x i)) = ∏ i, h i (x i) := by
    intro x
    have sp1 : mB hne x = mP hne j (x j) * ∏ i ∈ univ.erase j, mP hne i (x i) := by
      unfold mB; exact (Finset.mul_prod_erase univ _ (mem_univ j)).symm
    have sp2 : ∏ i, f i (x i) = f j (x j) * ∏ i ∈ univ.erase j, f i (x i) :=
      (Finset.mul_prod_erase univ (fun i => f i (x i)) (mem_univ j)).symm
    have sp3 : ∏ i, h i (x i) = h j (x j) * ∏ i ∈ univ.erase j, h i (x i) :=
      (Finset.mul_prod_erase univ (fun i => h i (x i)) (mem_univ j)).symm
    have : ∏ i ∈ univ.erase j, h i (x i) =
        (∏ i ∈ univ.erase j, mP hne i (x i)) * ∏ i ∈ univ.erase j, f i (x i) := by
      rw [← prod_mul_distrib]
      exact prod_congr rfl fun i hi => by rw [hh, Function.update_of_ne (ne_of_mem_erase hi)]
    rw [sp1, sp2, sp3, this, hh, Function.update_self]
    ring
  simp only [e1]
  rw [sum_prod_coords, ← Finset.mul_prod_erase univ _ (mem_univ j), hh, Function.update_self]
  congr 1
  exact prod_congr rfl fun i hi => by rw [Function.update_of_ne (ne_of_mem_erase hi)]

/-- The prime label-`3` arm `y_{3,j,z}` as a function of the prime coordinates. -/
noncomputable def yT (hne : MiddleNonempty pr) (j : ι) (z : ZMod (pr j)) (b : Ai pr j) : ℝ :=
  (Fintype.card (ZMod (pr j)) : ℝ) *
    (K3 (b 1) (b 2) z - ∑ b' : Ai pr j, mP hne j b' * K3 (b' 1) (b' 2) z)

theorem K3_eq_Acp {F : Type} [Field F] [Fintype F] [DecidableEq F] (c1 c2 z : F) :
    K3 c1 c2 z = Acp (fun s => PrimeGram.delta z s - (Fintype.card F : ℝ)⁻¹) c1 c2 := by
  have h := K3_sum (PrimeGram.delta z) c1 c2
  have h1 : ∑ w, PrimeGram.delta z w * K3 c1 c2 w = K3 c1 c2 z := by
    simp only [PrimeGram.delta, ite_mul, one_mul, zero_mul, sum_ite_eq', mem_univ, ↓reduceIte]
  have h2 : ∑ w, PrimeGram.delta z w = (1 : ℝ) := by
    simp only [PrimeGram.delta, sum_ite_eq', mem_univ, ↓reduceIte]
  rw [h1, h2, mul_one] at h
  exact h

omit [Fintype ι] [DecidableEq ι] in
/-- **The prime label-`3` arm is orthogonal to the functions of `x₁` and of `x₂`** (OPS-L's
`A3_perp`), and it equals `q A₃°(δ_z − 1/p)` (its mean vanishes). -/
theorem yT_orth (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (j : ι) (z : ZMod (pr j)) (u v : ZMod (pr j) → ℝ) :
    ∑ b : Ai pr j, mP hne j b * (yT hne j z b * (u (b 1) + v (b 2))) = 0 := by
  obtain ⟨hR, h3', h19'⟩ := primeHyps h3 h19 j
  set q : ℝ := (Fintype.card (ZMod (pr j)) : ℝ) with hqdef
  have h7 : (7 : ℝ) ≤ q := by rw [hqdef]; exact_mod_cast le_trans (by norm_num) h19'
  set hz : ZMod (pr j) → ℝ := fun s => PrimeGram.delta z s - q⁻¹ with hhz
  have hzm : ∑ s, hz s = 0 := by
    have hq : q ≠ 0 := by positivity
    simp only [hhz, sum_sub_distrib, PrimeGram.delta, sum_ite_eq', mem_univ, ↓reduceIte,
      sum_const, card_univ, nsmul_eq_mul, ← hqdef]
    rw [mul_inv_cancel₀ hq, sub_self]
  have hK : ∀ b : Ai pr j, K3 (b 1) (b 2) z = Acp hz (b 1) (b 2) := fun b => K3_eq_Acp _ _ _
  -- `⟨A₃° hz, u'(x₁) + v'(x₂)⟩ = 0` for every `u'` and every `v'`
  have hperp : ∀ u' v' : ZMod (pr j) → ℝ,
      ∑ b : Ai pr j, mP hne j b * (Acp hz (b 1) (b 2) * (u' (b 1) + v' (b 2))) = 0 := by
    intro u' v'
    set vbar := q⁻¹ * ∑ w, v' w with hvbar
    have hv0 : ∑ w, (v' w - vbar) = 0 := by
      have hq : q ≠ 0 := by positivity
      rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, ← hqdef, hvbar, ← mul_assoc,
        mul_inv_cancel₀ hq, one_mul, sub_self]
    have := A3_perp hR h3' h7 hz hzm (fun a => u' a + vbar) (fun b => v' b - vbar) hv0
    rw [← mP_pair2 hne h3 h19 j] at this
    rw [← this]
    refine sum_congr rfl fun b _ => ?_
    simp only [Acp]
    ring
  have hE : ∑ b' : Ai pr j, mP hne j b' * K3 (b' 1) (b' 2) z = 0 := by
    have := hperp (fun _ => 1) (fun _ => 0)
    simp only [add_zero, mul_one] at this
    rw [← this]
    exact sum_congr rfl fun b _ => by rw [hK]
  unfold yT
  simp only [hE, sub_zero, ← hqdef]
  have := hperp u v
  calc ∑ b : Ai pr j, mP hne j b * (q * K3 (b 1) (b 2) z * (u (b 1) + v (b 2)))
      = q * ∑ b : Ai pr j, mP hne j b * (Acp hz (b 1) (b 2) * (u (b 1) + v (b 2))) := by
        rw [mul_sum]
        exact sum_congr rfl fun b _ => by rw [hK]; ring
    _ = 0 := by rw [this, mul_zero]

/-- A prime orthogonality to the functions of `x_{j,k}` gives the block orthogonality to every
function of the block coordinate `x_k` (product law, indicator decomposition). -/
theorem block_orth_of_prime (hne : MiddleNonempty pr) (j : ι) (k : Fin 3) (G : Ai pr j → ℝ)
    (hG : ∀ c : ZMod (pr j), ∑ b : Ai pr j, mP hne j b * (G b * (if b k = c then 1 else 0)) = 0)
    (u : (∀ i, ZMod (pr i)) → ℝ) :
    EnvelopeSteps.ip (mB hne) (fun x => G (x j)) (fun x => u (piA k x)) = 0 := by
  have hdec : ∀ x : ∀ i, Ai pr i, u (piA k x) =
      ∑ w : (∀ i, ZMod (pr i)), u w * ∏ i, (if x i k = w i then (1 : ℝ) else 0) := by
    intro x
    rw [Finset.sum_eq_single (piA k x)]
    · simp [piA]
    · intro w _ hw
      have : ∃ i, x i k ≠ w i := by
        by_contra hc
        simp only [not_exists, not_not] at hc
        exact hw (funext fun i => (hc i).symm)
      obtain ⟨i, hi⟩ := this
      rw [Finset.prod_eq_zero (mem_univ i) (by simp [hi]), mul_zero]
    · simp
  unfold EnvelopeSteps.ip
  simp only [hdec, mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun w _ => ?_
  have e : ∀ x : ∀ i, Ai pr i, mB hne x * (G (x j) * (u w * ∏ i, (if x i k = w i then (1 : ℝ)
      else 0))) = u w * (mB hne x * (G (x j) * ∏ i, (fun i (c : Ai pr i) =>
        if c k = w i then (1 : ℝ) else 0) i (x i))) := fun x => by ring
  simp only [e, ← mul_sum]
  rw [sum_mB_prod hne j G (fun i c => if c k = w i then (1 : ℝ) else 0), hG (w j), zero_mul,
    mul_zero]

/-- **The label-`3` arms are orthogonal to the functions of `x₁`** (`hy1` of `hUa_three_chart`). -/
theorem yThree_orth1 (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (j : ι) (z : ZMod (pr j)) (u : (∀ i, ZMod (pr i)) → ℝ) :
    EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun x => u (piA 1 x)) = 0 :=
  block_orth_of_prime hne j 1 (yT hne j z) (fun c => by
    have := yT_orth hne h3 h19 j z (fun a => if a = c then 1 else 0) (fun _ => 0)
    simpa using this) u

/-- **The label-`3` arms are orthogonal to the functions of `x₂`** (`hy2` of `hUa_three_chart`). -/
theorem yThree_orth2 (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (j : ι) (z : ZMod (pr j)) (v : (∀ i, ZMod (pr i)) → ℝ) :
    EnvelopeSteps.ip (mB hne) (yThree hne j z) (fun x => v (piA 2 x)) = 0 :=
  block_orth_of_prime hne j 2 (yT hne j z) (fun c => by
    have := yT_orth hne h3 h19 j z (fun _ => 0) (fun a => if a = c then 1 else 0)
    simpa using this) v

/-- **`hUa` of `hdom_of_units` at a fold block, all four labels, for the chart's sector maps**
(`chart_lead`, third arm `A₃°`): the arm facts are proved (`ySing_*`, `yThree_orth1/2`,
`yThree_contraction`); the remaining inputs are the identification of OPS-S's unit lifts with the
conditional expectations of `m_{0,𝔅}` (`hU`, `hU3`) and the correlation `ρ` of the centred functions
of `x₁` and `x₂` under `m_{0,𝔅}` (`hcor`, edge `12` of the block). -/
theorem hUa_fold_A3 (hne : MiddleNonempty pr) (h3 : ∀ i, pr i % 4 = 3) (h19 : ∀ i, 19 ≤ pr i)
    (x₀ : ∀ i, Ai pr i) {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1)
    (U : Fin 5 → Fin 5 → ((∀ i, Ai pr i) → ℝ) →ₗ[ℝ] ((∀ i, Ai pr i) → ℝ))
    (hU : ∀ a : Fin 3, U (Fin.castSucc (Fin.castSucc a)) (Fin.castSucc (Fin.castSucc a)) =
      uOp (mB hne) (piA a))
    (hU3 : U 3 3 = qOp (mB hne) (fun x => (piA 1 x, piA 2 x)) ρ)
    (hcor : ∀ (u v : (∀ i, ZMod (pr i)) → ℝ),
      EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun _ => 1) = 0 →
      EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun _ => 1) = 0 →
      |EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => v (piA 2 x))| ≤
        ρ * Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => u (piA 1 x)) (fun x => u (piA 1 x))) *
          Real.sqrt (EnvelopeSteps.ip (mB hne) (fun x => v (piA 2 x)) (fun x => v (piA 2 x))))
    (a : Fin 4) :
    (Matrix.of fun x x' : (∀ i, Ai pr i) =>
      EnvelopeSteps.kern (mB hne) (U (Fin.castSucc a) (Fin.castSucc a)) x x' -
      ∑ j, ∑ z, ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ •
          (CXi hne x₀ j * XiM (mP hne j) A3c)) x (a, z) *
        ((Real.sqrt (Fintype.card (ZMod (pr j))))⁻¹ • (CXi hne x₀ j * XiM (mP hne j) A3c))
          x' (a, z)).PosSemidef :=
  hUa_fold_chart hne x₀ hρ hρ1 U hU hU3 hcor (yThree_orth1 hne h3 h19) (yThree_orth2 hne h3 h19)
    (yThree_contraction hne h3 h19) a

end Block

end Sarkozy.OpsFeature

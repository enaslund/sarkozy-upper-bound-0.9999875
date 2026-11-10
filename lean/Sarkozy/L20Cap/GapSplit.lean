module

public import Sarkozy.L20Cap.Gap

/-!
# The splitting of `prop:l20-pair-gap`: the range of `𝐯'` and its complement

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-pair-gap`: "`𝐯' = 𝐯/√g_𝐯` is an
isometry into the mean-zero functions of the pair", and the decomposition of a function of the pair
into its component in the range of `𝐯'` and the orthogonal complement. Notation of
`Sarkozy.L20Cap.Gap`. Here `vOp h (b) = h(b₀) + h(b₁)` (`= √2 𝐯h`).

* `vOp_ip`: `⟨vOp h, vOp h'⟩ = 2 g_𝐯 ⟨h, h'⟩` on mean-zero `h, h'` (`𝐯^*𝐯 = g_𝐯 I`, bilinear);
* `vOp_adj`: `⟨vOp h, f⟩ = ∑_y h(y) G_f(y)` with `G_f(y) = E_b[(𝟙{b₀ = y} + 𝟙{b₁ = y}) f(b)]`;
* **`pair_split`**: every `f` is `vOp h_f + f₂` with `h_f` of mean zero and `f₂` orthogonal to the
  whole range of `vOp` on mean-zero functions;
* **`Rc_complement`**: on that complement the stars at the pair coordinates vanish (`G_g ≡ 0`,
  `Gf_zero`), so `𝖱_c g = E_b[(𝖪(b₀, C) - 1)(𝖪(b₁, C) - 1)g(b)]`: only the core-pair stars
  (`2r𝐰𝐞^*`) and the nonstars `𝖱_∘` remain;
* **`pair_gap_ranges`**: `prop:l20-pair-gap` with the three bounds stated as in the paper, on the
  range of `𝐯'` (`‖𝖱𝐯'h‖ ≤ τ_g‖𝐯'h‖`), on its complement in the mean-zero functions
  (`‖𝖱_c f₂‖ ≤ l_g‖f₂‖`) and across (`|⟨𝖱𝐯'h, 𝖱_c f₂⟩| ≤ x_g‖𝐯'h‖‖f₂‖`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (PairT F)]

/-- `vOp h (b) = h(b₀) + h(b₁)`, i.e. `√2 𝐯h`. -/
def vOp (h : F → ℝ) (b : PairT F) : ℝ := h b.1.1 + h b.1.2

/-- **`⟨vOp h, vOp h'⟩_{μ^pair} = 2 g_𝐯 ⟨h, h'⟩`** for mean-zero `h, h'`
(`g_𝐯 = (1 - 2q)/(1 - q)`, `⟨h, h'⟩ = (∑ hh')/p`), by polarization of `vfeat_sq`. -/
theorem vOp_ip (h h' : F → ℝ) (h0 : ∑ z, h z = 0) (h0' : ∑ z, h' z = 0) :
    ip (pairLaw (F := F)) (vOp h) (vOp h') =
      2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, h z * h' z) / Fintype.card F) := by
  have hp : ∑ z, (h z + h' z) = 0 := by rw [sum_add_distrib, h0, h0', add_zero]
  have hm : ∑ z, (h z - h' z) = 0 := by rw [sum_sub_distrib, h0, h0', sub_zero]
  have e1 := vfeat_sq (F := F) (fun z => h z + h' z) hp
  have e2 := vfeat_sq (F := F) (fun z => h z - h' z) hm
  have hpol : ip (pairLaw (F := F)) (vOp h) (vOp h') =
      ((pairLaw (F := F)).expect (fun b => ((h b.1.1 + h' b.1.1) + (h b.1.2 + h' b.1.2)) ^ 2) -
        (pairLaw (F := F)).expect
          (fun b => ((h b.1.1 - h' b.1.1) + (h b.1.2 - h' b.1.2)) ^ 2)) / 4 := by
    unfold ip
    rw [← FiniteLaw.expect_sub, div_eq_mul_inv, ← FiniteLaw.expect_mul_const]
    refine (pairLaw (F := F)).expect_congr fun b => ?_
    simp only [vOp]
    ring
  rw [hpol, e1, e2]
  have hs : ∑ z, (h z + h' z) ^ 2 - ∑ z, (h z - h' z) ^ 2 = 4 * ∑ z, h z * h' z := by
    rw [← sum_sub_distrib, mul_sum]
    exact sum_congr rfl fun z _ => by ring
  have : 2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, (h z + h' z) ^ 2) / Fintype.card F) -
      2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, (h z - h' z) ^ 2) / Fintype.card F) =
      2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) *
        ((∑ z, (h z + h' z) ^ 2 - ∑ z, (h z - h' z) ^ 2) / Fintype.card F) := by ring
  rw [this, hs]
  ring

/-- `G_f(y) = E_b[(𝟙{b₀ = y} + 𝟙{b₁ = y}) f(b)]`. -/
noncomputable def Gf (f : PairT F → ℝ) (y : F) : ℝ :=
  (pairLaw (F := F)).expect fun b =>
    ((if b.1.1 = y then 1 else 0) + (if b.1.2 = y then 1 else 0)) * f b

/-- **The adjoint of `vOp`**: `⟨vOp h, f⟩ = ∑_y h(y) G_f(y)`. -/
theorem vOp_adj (h : F → ℝ) (f : PairT F → ℝ) :
    ip (pairLaw (F := F)) (vOp h) f = ∑ y, h y * Gf f y := by
  unfold ip Gf FiniteLaw.expect
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [vOp]
  have e : ∀ y : F, h y * ((pairLaw (F := F)).weight b *
      (((if b.1.1 = y then 1 else 0) + (if b.1.2 = y then 1 else 0)) * f b)) =
      (pairLaw (F := F)).weight b * f b *
        ((if b.1.1 = y then h y else 0) + (if b.1.2 = y then h y else 0)) := by
    intro y; split_ifs <;> ring
  rw [sum_congr rfl fun y _ => e y, ← mul_sum, sum_add_distrib, sum_ite_eq, sum_ite_eq]
  simp only [mem_univ, ↓reduceIte]
  ring

/-- The coefficient of the projection onto the range of `vOp`:
`h_f = (G_f - \bar G_f)/(2g_𝐯 q)`. -/
noncomputable def hProj (f : PairT F → ℝ) (y : F) : ℝ :=
  (Gf f y - (∑ z, Gf f z) / Fintype.card F) /
    (2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) / Fintype.card F)

theorem hProj_mean (f : PairT F → ℝ) : ∑ y, hProj f y = 0 := by
  unfold hProj
  rw [← sum_div, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  field_simp
  ring

/-- **The splitting of the pair functions** (proof of `prop:l20-pair-gap`): every `f` is
`vOp h_f + f₂`, with `h_f` of mean zero and `f₂ ⊥ vOp h'` for every mean-zero `h'` (`q < 1/2`). -/
theorem pair_split (h5 : 5 ≤ Fintype.card F) (f : PairT F → ℝ) (h' : F → ℝ) (h0' : ∑ z, h' z = 0) :
    ip (pairLaw (F := F)) (vOp h') (fun b => f b - vOp (hProj f) b) = 0 := by
  have hp5 : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast h5
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  have h1 : 1 - (Fintype.card F : ℝ)⁻¹ ≠ 0 := by
    have : (Fintype.card F : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
    linarith
  have h2 : 1 - 2 * (Fintype.card F : ℝ)⁻¹ ≠ 0 := by
    have : (Fintype.card F : ℝ)⁻¹ ≤ 1 / 5 := by
      rw [one_div]; exact inv_anti₀ (by norm_num) hp5
    linarith
  have hsub : ip (pairLaw (F := F)) (vOp h') (fun b => f b - vOp (hProj f) b) =
      ip (pairLaw (F := F)) (vOp h') f - ip (pairLaw (F := F)) (vOp h') (vOp (hProj f)) := by
    unfold ip
    rw [← FiniteLaw.expect_sub]
    exact (pairLaw (F := F)).expect_congr fun b => by ring
  rw [hsub, vOp_adj, vOp_ip h' (hProj f) h0' (hProj_mean f)]
  set c := 2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹) / (1 - (Fintype.card F : ℝ)⁻¹) with hcdef
  have hc0 : c ≠ 0 := by
    rw [hcdef]
    exact div_ne_zero (mul_ne_zero two_ne_zero h2) h1
  have hD : c / Fintype.card F ≠ 0 := div_ne_zero hc0 hp0
  have key : ∑ z, h' z * hProj f z = (∑ z, h' z * Gf f z) / (c / Fintype.card F) := by
    unfold hProj
    rw [← hcdef]
    set Gb := (∑ z, Gf f z) / (Fintype.card F : ℝ)
    have : ∀ z, h' z * ((Gf f z - Gb) / (c / Fintype.card F)) =
        (h' z * Gf f z - Gb * h' z) / (c / Fintype.card F) := fun z => by ring
    rw [sum_congr rfl fun z _ => this z, ← sum_div, sum_sub_distrib, ← mul_sum, h0', mul_zero,
      sub_zero]
  rw [key]
  field_simp
  ring

/-! ## `prop:l20-pair-gap` with the bounds on the two ranges -/

theorem expect_vOp (h : F → ℝ) (h0 : ∑ z, h z = 0) : (pairLaw (F := F)).expect (vOp h) = 0 := by
  have e := pairLaw_expect (F := F) (fun y => h y.1 + h y.2)
  have e' : (pairLaw (F := F)).expect (vOp h) =
      (pairLaw (F := F)).expect (fun b => (fun y : F × F => h y.1 + h y.2) b.1) := rfl
  rw [e', e]
  have h1 : ∑ y : F, ∑ y' : F, (h (y, y').1 + h (y, y').2) = 0 := by
    simp only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, ← mul_sum, h0]
    ring
  have h2 : ∑ y : F, (h (y, y).1 + h (y, y).2) = 0 := by
    simp only [sum_add_distrib, h0]; ring
  rw [h1, h2]
  simp

theorem nrm_sub_mean_le {X : Type*} [Fintype X] (μ : FiniteLaw X) (g : X → ℝ) :
    nrm μ (fun x => g x - μ.expect g) ≤ nrm μ g := by
  apply Real.sqrt_le_sqrt
  unfold ip
  have e : ∀ x, (g x - μ.expect g) * (g x - μ.expect g) =
      g x * g x - 2 * μ.expect g * g x + μ.expect g ^ 2 := fun x => by ring
  rw [μ.expect_congr e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
    FiniteLaw.expect_const]
  nlinarith [sq_nonneg (μ.expect g)]

variable [Nonempty (CoreT F)]

omit [Nonempty (CoreT F)] in
theorem Rc_sub_const (g : PairT F → ℝ) (c : ℝ) :
    recOp (pairLaw (F := F)) Rc (fun b => g b - c) = recOp (pairLaw (F := F)) Rc g := by
  funext C
  have h1 := recOp_Rc_one (F := F) C
  unfold recOp at h1 ⊢
  have e : ∀ b, Rc C b * (g b - c) = Rc C b * g b - c * (Rc C b * 1) := fun b => by ring
  rw [(pairLaw (F := F)).expect_congr e, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, h1]
  ring

/-- **`prop:l20-pair-gap`, with the three bounds of the proof**: on the range of `𝐯'`
(`‖𝖱_c vOp h‖ ≤ τ_g ‖vOp h‖`), on its orthogonal complement in the mean-zero functions of the pair
(`‖𝖱_c g‖ ≤ l_g ‖g‖`) and across (`|⟨𝖱_c vOp h, 𝖱_c g⟩| ≤ x_g ‖vOp h‖ ‖g‖`); with `τ_g² ≥ 30q`
and `Δ_g = 30q - l_g² > 0`, `‖𝖱_c‖ ≤ c_gap`. -/
theorem pair_gap_ranges (h5 : 5 ≤ Fintype.card F) {q τg lg xg : ℝ} (hl : 0 ≤ lg) (hx : 0 ≤ xg)
    (hτq : 30 * q ≤ τg ^ 2) (hΔ : 0 < 30 * q - lg ^ 2)
    (hA : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        τg * nrm (pairLaw (F := F)) (vOp h))
    (hB : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc g) ≤ lg * nrm (pairLaw (F := F)) g)
    (hC : ∀ (h : F → ℝ) (g : PairT F → ℝ), ∑ z, h z = 0 → (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h))
          (recOp (pairLaw (F := F)) Rc g)| ≤
        xg * nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g)
    (f : PairT F → ℝ) :
    nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc f) ≤
      Real.sqrt (τg ^ 2 + xg ^ 2 / (30 * q - lg ^ 2)) * nrm (pairLaw (F := F)) f := by
  refine pair_gap hτq hΔ (fun f => ?_) f
  set h := hProj f with hhdef
  have hh0 : ∑ z, h z = 0 := hProj_mean f
  set g : PairT F → ℝ := fun b => f b - vOp h b with hgdef
  -- the centred complement
  set g0 : PairT F → ℝ := fun b => g b - (pairLaw (F := F)).expect g with hg0def
  have horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0 :=
    fun h' h0' => pair_split h5 f h' h0'
  have horth0 : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g0 = 0 := by
    intro h' h0'
    have e : ip (pairLaw (F := F)) (vOp h') g0 = ip (pairLaw (F := F)) (vOp h') g -
        (pairLaw (F := F)).expect g * (pairLaw (F := F)).expect (vOp h') := by
      unfold ip
      rw [← FiniteLaw.expect_const_mul, ← FiniteLaw.expect_sub]
      exact (pairLaw (F := F)).expect_congr fun b => by simp only [hg0def]; ring
    rw [e, horth h' h0', expect_vOp h' h0']
    ring
  have hg0mean : (pairLaw (F := F)).expect g0 = 0 := by
    simp only [hg0def]
    rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, sub_self]
  have hRg : recOp (pairLaw (F := F)) Rc g = recOp (pairLaw (F := F)) Rc g0 :=
    (Rc_sub_const g _).symm
  have hng : nrm (pairLaw (F := F)) g0 ≤ nrm (pairLaw (F := F)) g := nrm_sub_mean_le _ g
  refine ⟨vOp h, g, ?_, horth h hh0, hA h hh0, ?_, ?_⟩
  · funext b; simp only [hgdef]; ring
  · rw [hRg]
    exact (hB g0 hg0mean horth0).trans (mul_le_mul_of_nonneg_left hng hl)
  · rw [hRg]
    refine (hC h g0 hh0 hg0mean horth0).trans ?_
    exact mul_le_mul_of_nonneg_left hng (mul_nonneg hx (nrm_nonneg _ _))

/-! ## On the complement the stars at the pair coordinates vanish -/

omit [Nonempty (CoreT F)] in
/-- On the orthogonal complement of the range of `vOp` (mean-zero `h`), `G_g ≡ 0`. -/
theorem Gf_zero (g : PairT F → ℝ) (hg0 : (pairLaw (F := F)).expect g = 0)
    (horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) (y : F) :
    Gf g y = 0 := by
  -- `G_g` is constant
  have hconst : ∀ y y' : F, Gf g y = Gf g y' := by
    intro y y'
    have h := horth (fun z => (if z = y then 1 else 0) - (if z = y' then 1 else 0)) (by
      rw [sum_sub_distrib, sum_ite_eq', sum_ite_eq']; simp)
    rw [vOp_adj] at h
    have e : ∀ z, ((if z = y then (1 : ℝ) else 0) - (if z = y' then 1 else 0)) * Gf g z =
        (if z = y then Gf g z else 0) - (if z = y' then Gf g z else 0) := fun z => by
      split_ifs <;> ring
    rw [sum_congr rfl fun z _ => e z, sum_sub_distrib, sum_ite_eq', sum_ite_eq'] at h
    simp only [mem_univ, ↓reduceIte] at h
    linarith
  -- and sums to `2E g = 0`
  have hsum : ∑ z, Gf g z = 0 := by
    unfold Gf
    unfold FiniteLaw.expect
    rw [sum_comm]
    have : ∀ b : PairT F, ∑ z : F, (pairLaw (F := F)).weight b *
        (((if b.1.1 = z then 1 else 0) + (if b.1.2 = z then 1 else 0)) * g b) =
        2 * ((pairLaw (F := F)).weight b * g b) := by
      intro b
      have e : ∀ z : F, (pairLaw (F := F)).weight b *
          (((if b.1.1 = z then 1 else 0) + (if b.1.2 = z then 1 else 0)) * g b) =
          (if b.1.1 = z then (pairLaw (F := F)).weight b * g b else 0) +
            (if b.1.2 = z then (pairLaw (F := F)).weight b * g b else 0) := fun z => by
        split_ifs <;> ring
      rw [sum_congr rfl fun z _ => e z, sum_add_distrib, sum_ite_eq, sum_ite_eq]
      simp only [mem_univ, ↓reduceIte]
      ring
    rw [sum_congr rfl fun b _ => this b, ← mul_sum]
    unfold FiniteLaw.expect at hg0
    rw [hg0, mul_zero]
  have hp0 : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [sum_congr rfl fun z _ => hconst z y, sum_const, card_univ, nsmul_eq_mul] at hsum
  exact (mul_eq_zero.mp hsum).resolve_left hp0

omit [Nonempty (CoreT F)] in
/-- **The stars at the pair coordinates vanish on the complement** (proof of
`prop:l20-pair-gap`: "on the orthogonal complement of the range of `𝐯'` in the mean-zero functions
of the pair, `𝐯^* = 0`"): there `𝖱_c g = E_b[(𝖪(b₀, C) - 1)(𝖪(b₁, C) - 1) g(b)]`, the core-pair
stars `∑_kχ(b₀ - x_k)χ(b₁ - x_k)` (`2r𝐰𝐞^*`) and the nonstars `𝖱_∘`. -/
theorem Rc_complement (g : PairT F → ℝ) (hg0 : (pairLaw (F := F)).expect g = 0)
    (horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0)
    (C : CoreT F) :
    recOp (pairLaw (F := F)) Rc g C =
      (pairLaw (F := F)).expect (fun b => (Kz b.1.1 C.1 - 1) * (Kz b.1.2 C.1 - 1) * g b) := by
  have hG := Gf_zero g hg0 horth
  -- the singleton parts: `E_b[((𝖪(b₀) - 1) + (𝖪(b₁) - 1)) g] = ∑_y (𝖪(y) - 1) G_g(y) = 0`
  have hstar : ip (pairLaw (F := F)) (vOp (fun y => Kz y C.1 - 1)) g = 0 := by
    rw [vOp_adj]
    simp [hG]
  unfold recOp Rc
  have e : ∀ b : PairT F, (Rk C b - rmass C) * g b =
      (Kz b.1.1 C.1 - 1) * (Kz b.1.2 C.1 - 1) * g b +
        vOp (fun y => Kz y C.1 - 1) b * g b + (1 - rmass C) * g b := by
    intro b
    simp only [Rk, vOp]
    ring
  rw [(pairLaw (F := F)).expect_congr e, FiniteLaw.expect_add, FiniteLaw.expect_add,
    FiniteLaw.expect_const_mul, hg0, mul_zero, add_zero]
  unfold ip at hstar
  rw [hstar, add_zero]

end Sarkozy.L20Cap

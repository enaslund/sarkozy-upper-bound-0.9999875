module

public import Sarkozy.L20Cap.GapRange

/-!
# The cross bound `x_g` of `prop:l20-pair-gap`

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-pair-gap`: the off-diagonal block
`|⟨𝖱𝐯'h, 𝖱_c g⟩|` for `h ∈ 𝓗` and `g` in the complement of the range of `𝐯'`. On the complement
`𝖱_c g = E_b[N g] + ∑_kφ_g(C_k)` (`Rc_complement`). The nonstar part costs `τ_gN_A`. For the
core-pair stars the bilinear form is computed exactly by the orbit argument: the kernel
`L(z, y) = E_C[ψ(C)𝖪(z, C)∑_k𝟙{C_k = y}]` is square-affine invariant, vanishes on the diagonal
(`𝖪` vanishes at the core labels), and has no Paley part (where `𝖪 ≠ 0`, `∑_kχ(C_k - z) = 0`).
So it is `b(J - I)` with `b = 4E_C[ψ𝖪(0, C)]/(p - 1)`, and its form on mean-zero functions is
`-b∑hφ`.

* `Lker_affine`, `Lker_diag`, `Lker_chi_sum`: the three properties;
* `neg_orbit_const`, `Lker_10`, `Lker_eq`: `L(z, y) = b·𝟙{z ≠ y}`, `b = L(0, 1)` (the orbit
  `χ(y - z) = -1` is handled by the transposed invariant; `L(1, 0) = L(0, 1)` from the Paley
  sum);
* **`cross_star`**: `⟨𝖱 vOp h, ∑_kφ(C_k)⟩ = -(b/p)∑_z h(z)φ(z)` for mean-zero `φ`;
* **`hC_of_nonstar`**: `|⟨𝖱_c vOp h, 𝖱_c g⟩| ≤ x_g‖vOp h‖‖g‖` with
  `x_g = τ_gN_A + |b|(p/(2g_𝐯))^{1/2}/p` (an exact form of the paper's `2rw_g`);
* `Lker_row_sum`, `Lker_row_sum_eq`: `(p - 1)b = ∑_yL(0, y) = 4E_C[ψ𝖪(0, C)]`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- `L(z, y) = E_C[ψ(C)𝖪(z, C)∑_k𝟙{C_k = y}]`. -/
noncomputable def Lker (z y : F) : ℝ :=
  (coreLaw (F := F)).expect fun C => psiR C * Kz z C.1 * ∑ k, if C.1 k = y then (1 : ℝ) else 0

omit [Nonempty (PairT F)] in
theorem Lker_affine (α β : F) (hα : quadraticChar F α = 1) (z y : F) :
    Lker (α * z + β) (α * y + β) = Lker z y := by
  have hα0 := ne_zero_of_chi hα
  unfold Lker coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv hα β)]
  refine sum_congr rfl fun C _ => ?_
  simp only [affCoreEquiv, Equiv.coe_fn_mk, psiR, Kbar_affine hα, Kz_affine hα]
  congr 1
  refine sum_congr rfl fun k _ => ?_
  simp only [affCore]
  have : (α * C.1 k + β = α * y + β) ↔ (C.1 k = y) := by
    constructor
    · intro h; exact mul_left_cancel₀ hα0 (add_right_cancel h)
    · intro h; rw [h]
  simp only [this]

omit [Nonempty (PairT F)] in
theorem Lker_diag (hm1 : quadraticChar F (-1) = -1) (z : F) : Lker z z = 0 := by
  unfold Lker
  have : ∀ C : CoreT F, psiR C * Kz z C.1 * (∑ k, if C.1 k = z then (1 : ℝ) else 0) = 0 := by
    intro C
    by_cases hz : ∃ k, C.1 k = z
    · obtain ⟨k, hk⟩ := hz
      rw [← hk, Kz_core hm1 C.2 k]; ring
    · push Not at hz
      simp [hz]
  rw [(coreLaw (F := F)).expect_congr this, FiniteLaw.expect_const]

omit [Nonempty (PairT F)] in
/-- No Paley part: `∑_y χ(y - z)L(z, y) = 0`. -/
theorem Lker_chi_sum (hm1 : quadraticChar F (-1) = -1) (z : F) :
    ∑ y, chi (y - z) * Lker z y = 0 := by
  unfold Lker
  simp only [← FiniteLaw.expect_const_mul]
  rw [← expect_sum']
  have : ∀ C : CoreT F, ∑ y, chi (y - z) *
      (psiR C * Kz z C.1 * ∑ k, if C.1 k = y then (1 : ℝ) else 0) = 0 := by
    intro C
    have e : ∑ y, chi (y - z) * (psiR C * Kz z C.1 * ∑ k, if C.1 k = y then (1 : ℝ) else 0) =
        psiR C * Kz z C.1 * ∑ k, chi (C.1 k - z) := by
      have e1 : ∀ y, chi (y - z) * (psiR C * Kz z C.1 * ∑ k, if C.1 k = y then (1 : ℝ) else 0) =
          ∑ k, if C.1 k = y then chi (y - z) * (psiR C * Kz z C.1) else 0 := by
        intro y
        rw [mul_sum, mul_sum]
        refine sum_congr rfl fun k _ => ?_
        split_ifs <;> ring
      rw [sum_congr rfl fun y _ => e1 y, sum_comm, mul_sum]
      refine sum_congr rfl fun k _ => ?_
      rw [sum_ite_eq univ (C.1 k) (fun y => chi (y - z) * (psiR C * Kz z C.1))]
      simp only [mem_univ, ↓reduceIte]
      ring
    rw [e]
    rcases Kz_dichotomy hm1 C.2 z with ⟨hA, -⟩ | ⟨-, h0⟩
    · obtain ⟨a0, a1, a2, a3⟩ := hA
      have : ∑ k, chi (C.1 k - z) = 0 := by
        rw [Fin.sum_univ_four, chi_sub_comm hm1 (C.1 0), chi_sub_comm hm1 (C.1 1),
          chi_sub_comm hm1 (C.1 2), chi_sub_comm hm1 (C.1 3), a0, a1, a2, a3]
        ring
      rw [this, mul_zero]
    · rw [h0]; ring
  rw [(coreLaw (F := F)).expect_congr this, FiniteLaw.expect_const]

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
/-- The orbit `χ(y' - y) = -1`: a square-affine-invariant function is constant there too. -/
theorem neg_orbit_const (hm1 : quadraticChar F (-1) = -1) {m : F → F → ℝ}
    (hm : ∀ (α β : F), quadraticChar F α = 1 → ∀ y y', m (α * y + β) (α * y' + β) = m y y')
    {y y' z z' : F} (h : quadraticChar F (y' - y) = -1) (h' : quadraticChar F (z' - z) = -1) :
    m y y' = m z z' := by
  have flip : ∀ a b : F, quadraticChar F (a - b) = -quadraticChar F (b - a) := by
    intro a b
    have e : a - b = (-1) * (b - a) := by ring
    rw [e, map_mul, hm1, neg_one_mul]
  have h1 : quadraticChar F (y - y') = 1 := by rw [flip, h, neg_neg]
  have h2 : quadraticChar F (z - z') = 1 := by rw [flip, h', neg_neg]
  exact dir_const (m := fun a b => m b a) (fun α β hα a b => hm α β hα b a) h1 h2

omit [Nonempty (PairT F)] in
/-- `L(0, 1) = L(1, 0)`: the two orbits carry the same value (no Paley part). -/
theorem Lker_10 (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) :
    Lker (1 : F) 0 = Lker (0 : F) 1 := by
  have hinv := fun α β (hα : quadraticChar F α = 1) y y' => Lker_affine (F := F) α β hα y y'
  have h01 : quadraticChar F ((1 : F) - 0) = 1 := by simp
  have h10 : quadraticChar F ((0 : F) - 1) = -1 := by simp [hm1]
  have hpt : ∀ y : F, chi (y - 0) * Lker 0 y =
      (if quadraticChar F y = 1 then Lker (0 : F) 1 else 0) -
        (if quadraticChar F y = -1 then Lker (1 : F) 0 else 0) := by
    intro y
    by_cases hy : y = 0
    · subst hy; simp [chi_zero]
    · rcases quadraticChar_dichotomy hy with h | h
      · have : Lker (0 : F) y = Lker (0 : F) (1 : F) :=
          dir_const hinv (by rw [sub_zero]; exact h) h01
        simp [chi, h, this]
      · have : Lker (0 : F) y = Lker (1 : F) (0 : F) :=
          neg_orbit_const hm1 hinv (by rw [sub_zero]; exact h) h10
        have hne : (-1 : ℤ) ≠ 1 := by decide
        simp [chi, h, this, hne]
  have hsum := Lker_chi_sum hm1 (F := F) 0
  rw [sum_congr rfl fun y _ => hpt y, sum_sub_distrib, sum_ite, sum_ite, sum_const_zero,
    sum_const_zero, add_zero, add_zero, sum_const, sum_const, nsmul_eq_mul, nsmul_eq_mul] at hsum
  -- the two counts agree, by `∑ χ = 0`
  have hc : ((univ.filter fun y : F => quadraticChar F y = 1).card : ℝ) =
      ((univ.filter fun y : F => quadraticChar F y = -1).card : ℝ) := by
    have h0 := quadraticChar_sum_zero hF
    have e : ∀ y : F, (quadraticChar F y : ℝ) = (if quadraticChar F y = 1 then 1 else 0) -
        (if quadraticChar F y = -1 then 1 else 0) := by
      intro y
      by_cases hy : y = 0
      · subst hy; simp
      · rcases quadraticChar_dichotomy hy with h | h
        · simp [h]
        · have hne : (-1 : ℤ) ≠ 1 := by decide
          simp [h, hne]
    have h0' : ∑ y : F, (quadraticChar F y : ℝ) = 0 := by exact_mod_cast h0
    rw [sum_congr rfl fun y _ => e y, sum_sub_distrib, sum_boole, sum_boole] at h0'
    linarith
  have hpos : (0 : ℝ) < ((univ.filter fun y : F => quadraticChar F y = 1).card : ℝ) := by
    have : (1 : F) ∈ univ.filter fun y : F => quadraticChar F y = 1 := by simp
    exact_mod_cast card_pos.mpr ⟨1, this⟩
  rw [← hc] at hsum
  have := mul_left_cancel₀ hpos.ne'
    (by linarith : ((univ.filter fun y : F => quadraticChar F y = 1).card : ℝ) *
      Lker (0 : F) 1 = ((univ.filter fun y : F => quadraticChar F y = 1).card : ℝ) * Lker (1 : F) 0)
  exact this.symm

omit [Nonempty (PairT F)] in
/-- **`L = b(J - I)`**, `b = L(0, 1)`. -/
theorem Lker_eq (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (z y : F) :
    Lker z y = if z = y then 0 else Lker (0 : F) 1 := by
  have hinv := fun α β (hα : quadraticChar F α = 1) y y' => Lker_affine (F := F) α β hα y y'
  split_ifs with hzy
  · rw [hzy, Lker_diag hm1]
  · have hd : y - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hzy)
    rcases quadraticChar_dichotomy hd with h | h
    · exact dir_const hinv h (by simp)
    · rw [neg_orbit_const hm1 hinv h (by simp [hm1] : quadraticChar F ((0 : F) - 1) = -1),
        Lker_10 hm1 hF]

/-- **The core-pair stars across** (proof of `prop:l20-pair-gap`, the cross bound):
`⟨𝖱 vOp h, ∑_kφ(C_k)⟩ = -(L(0,1)/p)∑_z h(z)φ(z)` for `φ` of mean zero. -/
theorem cross_star (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (h φ : F → ℝ)
    (φ0 : ∑ z, φ z = 0) :
    ip (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Rk C b * vOp h b))
        (fun C => ∑ k, φ (C.1 k)) =
      -(Lker (0 : F) (1 : F) / Fintype.card F) * ∑ z, h z * φ z := by
  have hR : ∀ C : CoreT F, (pairLaw (F := F)).expect (fun b => Rk C b * vOp h b) =
      psiR C * ((∑ z, Kz z C.1 * h z) / Fintype.card F) := by
    intro C
    have := Rv_exact hm1 C h
    simp only [vOp]
    rw [this]
    rfl
  have hφ : ∀ C : CoreT F, ∑ k, φ (C.1 k) =
      ∑ y, φ y * ∑ k, (if C.1 k = y then (1 : ℝ) else 0) := by
    intro C
    simp only [mul_sum]
    rw [sum_comm]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_mul_boole]
    simp
  have e : ∀ C : CoreT F, (pairLaw (F := F)).expect (fun b => Rk C b * vOp h b) *
      ∑ k, φ (C.1 k) = (Fintype.card F : ℝ)⁻¹ * ∑ z, ∑ y, h z * φ y *
        (psiR C * Kz z C.1 * ∑ k, (if C.1 k = y then (1 : ℝ) else 0)) := by
    intro C
    rw [hR, hφ]
    calc psiR C * ((∑ z, Kz z C.1 * h z) / Fintype.card F) *
          ∑ y, φ y * ∑ k, (if C.1 k = y then (1 : ℝ) else 0)
        = (Fintype.card F : ℝ)⁻¹ * ((∑ z, Kz z C.1 * h z) *
            ∑ y, φ y * ∑ k, (if C.1 k = y then (1 : ℝ) else 0)) * psiR C := by ring
      _ = (Fintype.card F : ℝ)⁻¹ * (∑ z, ∑ y, (Kz z C.1 * h z) *
            (φ y * ∑ k, (if C.1 k = y then (1 : ℝ) else 0))) * psiR C := by rw [sum_mul_sum]
      _ = _ := by
          rw [mul_assoc, sum_mul]
          congr 1
          refine sum_congr rfl fun z _ => ?_
          rw [sum_mul]
          exact sum_congr rfl fun y _ => by ring
  have hE : (coreLaw (F := F)).expect (fun C => ∑ z, ∑ y, h z * φ y *
      (psiR C * Kz z C.1 * ∑ k, (if C.1 k = y then (1 : ℝ) else 0))) =
      ∑ z, ∑ y, h z * φ y * Lker z y := by
    rw [expect_sum' (coreLaw (F := F)) (fun z C => ∑ y, h z * φ y *
      (psiR C * Kz z C.1 * ∑ k, (if C.1 k = y then (1 : ℝ) else 0)))]
    refine sum_congr rfl fun z _ => ?_
    rw [expect_sum' (coreLaw (F := F)) (fun y C => h z * φ y *
      (psiR C * Kz z C.1 * ∑ k, (if C.1 k = y then (1 : ℝ) else 0)))]
    refine sum_congr rfl fun y _ => ?_
    rw [FiniteLaw.expect_const_mul]
    rfl
  unfold ip
  rw [(coreLaw (F := F)).expect_congr e, FiniteLaw.expect_const_mul, hE]
  have e3 : ∀ z y : F, h z * φ y * Lker z y =
      h z * φ y * (if z = y then 0 else Lker (0 : F) (1 : F)) := fun z y => by
    rw [Lker_eq hm1 hF z y]
  simp only [e3]
  have e2 : ∀ z : F, ∑ y, h z * φ y * (if z = y then 0 else Lker (0 : F) (1 : F)) =
      Lker (0 : F) (1 : F) * (h z * ∑ y, φ y) - Lker (0 : F) (1 : F) * (h z * φ z) := by
    intro z
    have : ∀ y, h z * φ y * (if z = y then 0 else Lker (0 : F) (1 : F)) =
        Lker (0 : F) (1 : F) * (h z * φ y) -
          (if z = y then Lker (0 : F) (1 : F) * (h z * φ y) else 0) := by
      intro y; split_ifs <;> ring
    rw [sum_congr rfl fun y _ => this y, sum_sub_distrib, sum_ite_eq univ z]
    simp only [mem_univ, ↓reduceIte]
    rw [← mul_sum, ← mul_sum]
  rw [sum_congr rfl fun z _ => e2 z, sum_sub_distrib, ← mul_sum, ← mul_sum, φ0]
  simp only [mul_zero, sum_const_zero]
  ring

omit [Nonempty (CoreT F)] in
/-- On the complement, `𝖱_c g = E_b[N g] + ∑_kφ_g(C_k)`. -/
theorem Rc_complement_split (g : PairT F → ℝ) (hg0 : (pairLaw (F := F)).expect g = 0)
    (horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) :
    recOp (pairLaw (F := F)) Rc g = fun C =>
      (pairLaw (F := F)).expect (fun b => Nrect C b * g b) + ∑ k, phiG g (C.1 k) := by
  funext C
  rw [Rc_complement g hg0 horth C]
  unfold phiG Nrect
  rw [← expect_sum' (pairLaw (F := F))
    (fun k b => chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k) * g b), ← FiniteLaw.expect_add]
  refine (pairLaw (F := F)).expect_congr fun b => ?_
  have hs : ∑ k, chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k) * g b =
      (∑ k, chi (b.1.1 - C.1 k) * chi (b.1.2 - C.1 k)) * g b := by rw [sum_mul]
  rw [hs]
  ring

/-- **`hC` of `pair_gap_ranges`** (`prop:l20-pair-gap`, the cross bound): for `h` of mean zero
and `g` in the complement, `|⟨𝖱_c vOp h, 𝖱_c g⟩| ≤ x_g‖vOp h‖‖g‖` with
`x_g = τN_A + (|L(0,1)|/p)(p(1 - q)/(2(1 - 2q)))^{1/2}`, given the range bound `τ` and the
nonstar bound `N_A`. -/
theorem hC_of_nonstar (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (h5 : 5 ≤ Fintype.card F) {τ NA : ℝ} (hτ0 : 0 ≤ τ)
    (hτ : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        τ * nrm (pairLaw (F := F)) (vOp h))
    (hN : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
        NA * nrm (pairLaw (F := F)) g)
    (h : F → ℝ) (g : PairT F → ℝ) (h0 : ∑ z, h z = 0) (hg0 : (pairLaw (F := F)).expect g = 0)
    (horth : ∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) :
    |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) (recOp (pairLaw (F := F)) Rc g)| ≤
      (τ * NA + |Lker (0 : F) (1 : F)| / Fintype.card F *
        Real.sqrt (Fintype.card F * (1 - (Fintype.card F : ℝ)⁻¹) /
          (2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹)))) *
        nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g := by
  have hp5 : (5 : ℝ) ≤ Fintype.card F := by exact_mod_cast h5
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  set q := (Fintype.card F : ℝ)⁻¹ with hqdef
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq5 : q ≤ 1 / 5 := by rw [hqdef, one_div]; exact inv_anti₀ (by norm_num) hp5
  have hRv : recOp (pairLaw (F := F)) Rc (vOp h) =
      fun C => (pairLaw (F := F)).expect (fun b => Rk C b * vOp h b) := by
    funext C
    unfold recOp Rc
    have e : ∀ b, (Rk C b - rmass C) * vOp h b = Rk C b * vOp h b - rmass C * vOp h b :=
      fun b => by ring
    rw [(pairLaw (F := F)).expect_congr e, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
      expect_vOp h h0, mul_zero, sub_zero]
  set A := recOp (pairLaw (F := F)) Rc (vOp h) with hA
  set B1 : CoreT F → ℝ := fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b) with hB1
  set B2 : CoreT F → ℝ := fun C => ∑ k, phiG g (C.1 k) with hB2
  have hsplit : recOp (pairLaw (F := F)) Rc g = fun C => B1 C + B2 C :=
    Rc_complement_split g hg0 horth
  rw [hsplit]
  have hip : ip (coreLaw (F := F)) A (fun C => B1 C + B2 C) =
      ip (coreLaw (F := F)) A B1 + ip (coreLaw (F := F)) A B2 := by
    unfold ip
    rw [← FiniteLaw.expect_add]
    exact (coreLaw (F := F)).expect_congr fun C => by ring
  rw [hip]
  -- the nonstar part
  have h1 : |ip (coreLaw (F := F)) A B1| ≤ τ * nrm (pairLaw (F := F)) (vOp h) *
      (NA * nrm (pairLaw (F := F)) g) := by
    refine (abs_ip_le _ _ _).trans ?_
    exact mul_le_mul (hτ h h0) (hN g hg0 horth) (nrm_nonneg _ _)
      (mul_nonneg hτ0 (nrm_nonneg _ _))
  -- the core-pair stars
  have hc := cross_star hm1 hF h (phiG g) (phiG_mean hF g hg0)
  rw [← hRv] at hc
  have hcs : |∑ z, h z * phiG g z| ≤ Real.sqrt (∑ z, h z ^ 2) * Real.sqrt (∑ z, phiG g z ^ 2) := by
    rw [← Real.sqrt_mul (sum_nonneg fun z _ => sq_nonneg _)]
    apply Real.abs_le_sqrt
    exact sum_mul_sq_le_sq_mul_sq univ h (phiG g)
  -- `∑h² = p(1 - q)/(2(1 - 2q)) ‖vOp h‖²`
  have hv := vfeat_sq (F := F) h h0
  have hvn : nrm (pairLaw (F := F)) (vOp h) ^ 2 =
      2 * (1 - 2 * q) / (1 - q) * ((∑ z, h z ^ 2) / Fintype.card F) := by
    rw [nrm_sq_expect]; exact hv
  have h1q : 0 < 1 - q := by linarith
  have h12q : 0 < 1 - 2 * q := by linarith
  have hh2 : ∑ z, h z ^ 2 = Fintype.card F * (1 - q) / (2 * (1 - 2 * q)) *
      nrm (pairLaw (F := F)) (vOp h) ^ 2 := by
    have h1' : 1 - q ≠ 0 := h1q.ne'
    have h2' : 1 - 2 * q ≠ 0 := h12q.ne'
    have h2'' : 1 - q * 2 ≠ 0 := by linarith
    have hp' : (Fintype.card F : ℝ) ≠ 0 := hp0.ne'
    rw [hvn]; field_simp
  have hsh : Real.sqrt (∑ z, h z ^ 2) = Real.sqrt (Fintype.card F * (1 - q) / (2 * (1 - 2 * q))) *
      nrm (pairLaw (F := F)) (vOp h) := by
    rw [hh2, Real.sqrt_mul (by positivity), Real.sqrt_sq (nrm_nonneg _ _)]
  -- `∑φ_g² ≤ ‖g‖²`
  have hφn := phiG_norm hF h5 g hg0
  have hcq : q * (1 - 2 * q - q ^ 2) / (1 - q) ≤ q := by
    rw [div_le_iff₀ h1q]; nlinarith
  have hφ2 : ∑ z, phiG g z ^ 2 ≤ nrm (pairLaw (F := F)) g ^ 2 := by
    have hg2 : 0 ≤ nrm (pairLaw (F := F)) g ^ 2 := sq_nonneg _
    have := hφn.trans (mul_le_mul_of_nonneg_right hcq hg2)
    rw [div_le_iff₀ hp0] at this
    have hqp : q * nrm (pairLaw (F := F)) g ^ 2 * Fintype.card F =
        nrm (pairLaw (F := F)) g ^ 2 := by
      rw [hqdef]; field_simp
    linarith
  have hsφ : Real.sqrt (∑ z, phiG g z ^ 2) ≤ nrm (pairLaw (F := F)) g := by
    calc Real.sqrt (∑ z, phiG g z ^ 2) ≤ Real.sqrt (nrm (pairLaw (F := F)) g ^ 2) :=
          Real.sqrt_le_sqrt hφ2
      _ = nrm (pairLaw (F := F)) g := Real.sqrt_sq (nrm_nonneg _ _)
  have h2 : |ip (coreLaw (F := F)) A B2| ≤ |Lker (0 : F) (1 : F)| / Fintype.card F *
      (Real.sqrt (Fintype.card F * (1 - q) / (2 * (1 - 2 * q))) *
        nrm (pairLaw (F := F)) (vOp h)) * nrm (pairLaw (F := F)) g := by
    rw [hc, abs_mul, abs_neg, abs_div, abs_of_pos hp0]
    have hL0 : 0 ≤ |Lker (0 : F) (1 : F)| / Fintype.card F := by positivity
    calc |Lker (0 : F) (1 : F)| / Fintype.card F * |∑ z, h z * phiG g z|
        ≤ |Lker (0 : F) (1 : F)| / Fintype.card F *
            (Real.sqrt (∑ z, h z ^ 2) * Real.sqrt (∑ z, phiG g z ^ 2)) :=
          mul_le_mul_of_nonneg_left hcs hL0
      _ ≤ |Lker (0 : F) (1 : F)| / Fintype.card F *
            (Real.sqrt (Fintype.card F * (1 - q) / (2 * (1 - 2 * q))) *
              nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g) := by
          rw [hsh]
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hsφ (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _ _))) hL0
      _ = _ := by ring
  calc |ip (coreLaw (F := F)) A B1 + ip (coreLaw (F := F)) A B2|
      ≤ |ip (coreLaw (F := F)) A B1| + |ip (coreLaw (F := F)) A B2| := abs_add_le _ _
    _ ≤ τ * nrm (pairLaw (F := F)) (vOp h) * (NA * nrm (pairLaw (F := F)) g) +
          |Lker (0 : F) (1 : F)| / Fintype.card F *
            (Real.sqrt (Fintype.card F * (1 - q) / (2 * (1 - 2 * q))) *
              nrm (pairLaw (F := F)) (vOp h)) * nrm (pairLaw (F := F)) g := add_le_add h1 h2
    _ = _ := by ring

omit [Nonempty (PairT F)] in
/-- `∑_y L(z, y) = 4E_C[ψ(C)𝖪(z, C)]`. -/
theorem Lker_row_sum (z : F) :
    ∑ y, Lker z y = 4 * (coreLaw (F := F)).expect (fun C => psiR C * Kz z C.1) := by
  unfold Lker
  rw [← expect_sum' (coreLaw (F := F))
    (fun y C => psiR C * Kz z C.1 * ∑ k, if C.1 k = y then (1 : ℝ) else 0),
    ← FiniteLaw.expect_const_mul]
  refine (coreLaw (F := F)).expect_congr fun C => ?_
  rw [← mul_sum, sum_comm]
  have h4 : ∑ k : Fin 4, ∑ y : F, (if C.1 k = y then (1 : ℝ) else 0) = 4 := by simp
  rw [h4]
  ring

omit [Nonempty (PairT F)] in
/-- `∑_y L(0, y) = (p - 1)L(0, 1)`. -/
theorem Lker_row_sum_eq (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) :
    ∑ y, Lker (0 : F) y = ((Fintype.card F : ℝ) - 1) * Lker (0 : F) (1 : F) := by
  rw [sum_congr rfl fun y _ => Lker_eq hm1 hF (0 : F) y]
  have e : ∀ y : F, (if (0 : F) = y then (0 : ℝ) else Lker (0 : F) (1 : F)) =
      Lker (0 : F) (1 : F) - if (0 : F) = y then Lker (0 : F) (1 : F) else 0 := by
    intro y; split_ifs <;> ring
  rw [sum_congr rfl fun y _ => e y, sum_sub_distrib, sum_ite_eq]
  simp only [sum_const, card_univ, nsmul_eq_mul, mem_univ, ↓reduceIte]
  ring

end Sarkozy.L20Cap

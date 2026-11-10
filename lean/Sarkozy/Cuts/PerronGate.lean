module

public import Sarkozy.Cuts.Schur

/-!
# Cuts, VIII‴: the Perron gate (`lem:weighted-frame` (c))

`13_cuts_correlations.tex`, `lem:weighted-frame` (c). Let `G` be a symmetric matrix with
nonnegative entries, preserved by a finite group of permutations of the index set
(`G_{σi,σj} = G_{ij}`).

* `perron_gate`, `perron_gate_bar`: if `sᵀ G s ≤ λ |s|²` for every invariant `s` (for instance if
  `λ I - Ḡ ⪰ 0`), then `vᵀ G v ≤ λ |v|²` for every
  `v`. That is, `λ_max(G)` equals the largest eigenvalue of the restriction of `G` to the
  invariant vectors. In the orthonormal basis `e_a = 1_{O_a}/|O_a|^{1/2}` of the invariant
  vectors, this restriction has the matrix `Ḡ`. So `λ_max(G) ≤ λ` as soon as `λ I - Ḡ ⪰ 0`.

The proof is the paper's. Take a maximizer `v` of the Rayleigh quotient (by compactness of the
unit sphere). Then `|v|` is a maximizer, since `G ≥ 0`, and so is every `|v| ∘ σ`. Maximizers lie
in the kernel of `λ₁ I - G` (`kernel_of_form_zero`), so their sum is an invariant maximizer.
`perron_gate_bar` states the bound with the matrix `Ḡ` itself (orbits of a `MulAction`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

section Perron

variable {I : Type*} [Fintype I] [DecidableEq I]

/-- The quadratic form `vᵀ G v`. -/
def quadF (G : I → I → ℝ) (v : I → ℝ) : ℝ := ∑ i, ∑ j, v i * G i j * v j

/-- `|v|² = ∑_i v_i²`. -/
def sqn (v : I → ℝ) : ℝ := ∑ i, v i ^ 2

omit [DecidableEq I] in
theorem sqn_nonneg (v : I → ℝ) : 0 ≤ sqn v := Finset.sum_nonneg (fun _ _ => sq_nonneg _)

omit [DecidableEq I] in
theorem eq_zero_of_sqn_eq_zero {v : I → ℝ} (h : sqn v = 0) : v = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (v j))).1 h i (Finset.mem_univ _)
  simpa using this

omit [DecidableEq I] in
theorem quadF_smul (G : I → I → ℝ) (c : ℝ) (v : I → ℝ) :
    quadF G (fun i => c * v i) = c ^ 2 * quadF G v := by
  unfold quadF
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

omit [DecidableEq I] in
theorem sqn_smul (c : ℝ) (v : I → ℝ) : sqn (fun i => c * v i) = c ^ 2 * sqn v := by
  unfold sqn
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- If `M ⪰ 0` is symmetric and `wᵀ M w = 0`, then `M w = 0`. -/
theorem kernel_of_form_zero (M : I → I → ℝ) (hMs : ∀ i j, M i j = M j i)
    (hM : ∀ v, 0 ≤ quadF M v) {w : I → ℝ} (hw : quadF M w = 0) (i : I) :
    ∑ j, M i j * w j = 0 := by
  set a := ∑ j, M i j * w j
  set b := M i i
  have hb : 0 ≤ b := by
    have := hM (Pi.single i 1)
    unfold quadF at this
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true] at this
    exact this
  have hexp : ∀ t : ℝ, quadF M (fun j => w j + t * (Pi.single i (1 : ℝ) : I → ℝ) j) =
      quadF M w + 2 * t * a + t ^ 2 * b := by
    intro t
    unfold quadF
    have e : ∀ k l, (w k + t * (Pi.single i (1 : ℝ) : I → ℝ) k) * M k l *
        (w l + t * (Pi.single i (1 : ℝ) : I → ℝ) l) =
        w k * M k l * w l + t * ((Pi.single i (1 : ℝ) : I → ℝ) k * M k l * w l) +
          t * (w k * M k l * (Pi.single i (1 : ℝ) : I → ℝ) l) +
          t ^ 2 * ((Pi.single i (1 : ℝ) : I → ℝ) k * M k l * (Pi.single i (1 : ℝ) : I → ℝ) l) := by
      intro k l; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have hsym : ∑ k, w k * M k i = a := by
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [hMs k i]
      ring
    rw [hsym]
    have h3 : (∑ x, ∑ x_1, if x = i then M x x_1 * w x_1 else (0 : ℝ)) = a := by
      rw [Finset.sum_eq_single i (fun x _ hx => by simp [hx])
        (fun h => absurd (Finset.mem_univ i) h)]
      exact Finset.sum_congr rfl (fun x1 _ => ite_eq_left rfl)
    rw [h3]
    ring
  have h := hM (fun j => w j + (-(a / (b + 1))) * (Pi.single i (1 : ℝ) : I → ℝ) j)
  rw [hexp, hw] at h
  have hb1 : 0 < b + 1 := by linarith
  have key : 0 ≤ a ^ 2 * (-(b + 2)) / (b + 1) ^ 2 := by
    have e : 0 + 2 * -(a / (b + 1)) * a + (-(a / (b + 1))) ^ 2 * b =
        a ^ 2 * (-(b + 2)) / (b + 1) ^ 2 := by
      field_simp
      ring
    rw [← e]
    exact h
  have : a ^ 2 * (-(b + 2)) ≥ 0 := by
    have h2 := mul_nonneg key (sq_nonneg (b + 1))
    rwa [div_mul_cancel₀ _ (by positivity)] at h2
  have ha : a ^ 2 = 0 := by nlinarith [sq_nonneg a]
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp ha

omit [DecidableEq I] in
/-- The unit sphere `{|v|² = 1}` is compact. -/
theorem isCompact_sphere : IsCompact {v : I → ℝ | sqn v = 1} := by
  have hcl : IsClosed {v : I → ℝ | sqn v = 1} :=
    isClosed_eq (by unfold sqn; fun_prop) continuous_const
  refine (isCompact_univ_pi (fun _ : I => isCompact_Icc (a := (-1 : ℝ)) (b := 1))).of_isClosed_subset
    hcl (fun v hv => ?_)
  simp only [Set.mem_ofPred_eq] at hv
  simp only [Set.mem_pi, Set.mem_univ, Set.mem_Icc, true_implies]
  intro i
  have h1 : v i ^ 2 ≤ 1 := by
    rw [← hv]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (v j)) (Finset.mem_univ i)
  constructor <;> nlinarith [sq_nonneg (v i + 1), sq_nonneg (v i - 1)]

/-- **`lem:weighted-frame` (c), the Perron gate.** If `G ≥ 0` is symmetric and invariant under a
finite group of permutations, and `sᵀ G s ≤ λ |s|²` for every invariant `s`, then
`vᵀ G v ≤ λ |v|²` for every `v`. -/
theorem perron_gate {Γ : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I] (G : I → I → ℝ)
    (hG0 : ∀ i j, 0 ≤ G i j) (hGs : ∀ i j, G i j = G j i)
    (hGinv : ∀ (σ : Γ) i j, G (σ • i) (σ • j) = G i j) {lam : ℝ}
    (hinv : ∀ s : I → ℝ, (∀ (σ : Γ) i, s (σ • i) = s i) → quadF G s ≤ lam * sqn s)
    (v : I → ℝ) : quadF G v ≤ lam * sqn v := by
  rcases isEmpty_or_nonempty I with hI | hI
  · simp [quadF, sqn]
  obtain ⟨i₀⟩ := hI
  -- a maximizer on the sphere
  have hne : ({v : I → ℝ | sqn v = 1}).Nonempty :=
    ⟨Pi.single i₀ 1, by simp [sqn, Pi.single_apply, Finset.sum_ite_eq']⟩
  obtain ⟨w, hwS, hwmax⟩ := isCompact_sphere.exists_isMaxOn hne
    (f := quadF G) (show Continuous (quadF G) by unfold quadF; fun_prop).continuousOn
  simp only [Set.mem_ofPred_eq] at hwS
  set lam₁ := quadF G w
  -- every vector is bounded by `λ₁`
  have hall : ∀ v, quadF G v ≤ lam₁ * sqn v := by
    intro v
    rcases (sqn_nonneg v).lt_or_eq with hpos | hzero
    · set c := √(sqn v)
      have hc : 0 < c := Real.sqrt_pos.mpr hpos
      have hc2 : c ^ 2 = sqn v := Real.sq_sqrt hpos.le
      have hu : sqn (fun i => c⁻¹ * v i) = 1 := by
        rw [sqn_smul, inv_pow, hc2, inv_mul_cancel₀ hpos.ne']
      have h := hwmax (show (fun i => c⁻¹ * v i) ∈ {v : I → ℝ | sqn v = 1} from hu)
      simp only [Set.mem_ofPred_eq] at h
      rw [quadF_smul, inv_pow, hc2] at h
      have := mul_le_mul_of_nonneg_left h hpos.le
      rwa [← mul_assoc, mul_inv_cancel₀ hpos.ne', one_mul, mul_comm] at this
    · have hv0 := eq_zero_of_sqn_eq_zero hzero.symm
      rw [← hzero, hv0]
      simp [quadF]
  -- `M = λ₁ - G ⪰ 0`
  set M : I → I → ℝ := fun i j => (if i = j then lam₁ else 0) - G i j with hM
  have hMs : ∀ i j, M i j = M j i := by
    intro i j
    simp only [hM, hGs i j]
    by_cases h : i = j
    · subst h; rfl
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]
  have hquadM : ∀ v, quadF M v = lam₁ * sqn v - quadF G v := by
    intro v
    unfold quadF sqn
    simp only [hM, mul_sub, sub_mul, Finset.sum_sub_distrib]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [mul_ite, ite_mul, mul_zero, zero_mul]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, ite_true]
    ring
  have hMpsd : ∀ v, 0 ≤ quadF M v := fun v => by rw [hquadM]; linarith [hall v]
  -- `|w|` is a maximizer, and so is every `|w| ∘ σ`
  set u : I → ℝ := fun i => |w i| with hu
  have husq : sqn u = 1 := by
    rw [← hwS]
    unfold sqn
    exact Finset.sum_congr rfl (fun i _ => by simp only [hu, sq_abs])
  have hquad_u : quadF G u = lam₁ := by
    apply le_antisymm
    · have := hall u
      rwa [husq, mul_one] at this
    · unfold quadF
      refine Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ => ?_))
      simp only [hu]
      have h1 : w i * G i j * w j ≤ |w i * G i j * w j| := le_abs_self _
      rw [abs_mul, abs_mul, abs_of_nonneg (hG0 i j)] at h1
      exact h1
  have hperm : ∀ σ : Γ, quadF M (fun i => u (σ • i)) = 0 := by
    intro σ
    have hsq : sqn (fun i => u (σ • i)) = sqn u := by
      unfold sqn
      exact Fintype.sum_equiv (MulAction.toPerm σ) _ _ (fun i => rfl)
    have hq : quadF G (fun i => u (σ • i)) = quadF G u := by
      unfold quadF
      refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ (fun i => ?_)
      refine Fintype.sum_equiv (MulAction.toPerm σ) _ _ (fun j => ?_)
      simp only [MulAction.toPerm_apply, hGinv]
    rw [hquadM, hsq, hq, husq, hquad_u]
    ring
  -- the invariant maximizer `s = ∑_σ |w| ∘ σ`
  set s : I → ℝ := fun i => ∑ σ : Γ, u (σ • i) with hs
  have hMs0 : ∀ i, ∑ j, M i j * s j = 0 := by
    intro i
    simp only [hs, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero (fun σ _ => kernel_of_form_zero M hMs hMpsd (hperm σ) i)
  have hquad_s : quadF M s = 0 := by
    unfold quadF
    refine Finset.sum_eq_zero (fun i _ => ?_)
    have := hMs0 i
    calc ∑ j, s i * M i j * s j = s i * ∑ j, M i j * s j := by
          rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
      _ = 0 := by rw [this, mul_zero]
  have hsinv : ∀ (τ : Γ) i, s (τ • i) = s i := by
    intro τ i
    simp only [hs]
    exact Fintype.sum_equiv (Equiv.mulRight τ) _ _ (fun σ => by
      simp only [Equiv.coe_mulRight, mul_smul])
  have hspos : 0 < sqn s := by
    rcases (sqn_nonneg s).lt_or_eq with h | h
    · exact h
    · exfalso
      have hs0 := eq_zero_of_sqn_eq_zero h.symm
      -- `∑_i s_i = |Γ| ∑_i |w_i| > 0`
      have hsum : ∑ i, s i = ∑ σ : Γ, ∑ i, u (σ • i) := by
        simp only [hs]
        exact Finset.sum_comm
      have hsum2 : ∀ σ : Γ, ∑ i, u (σ • i) = ∑ i, u i := fun σ =>
        Fintype.sum_equiv (MulAction.toPerm σ) _ _ (fun i => rfl)
      simp only [hsum2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
      have hu0 : 0 < ∑ i, u i := by
        rcases (Finset.sum_nonneg (fun i (_ : i ∈ Finset.univ) => abs_nonneg (w i))).lt_or_eq
          with h' | h'
        · exact h'
        · exfalso
          have hw0 : ∀ i, w i = 0 := fun i => by
            have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => abs_nonneg (w j))).1 h'.symm i
              (Finset.mem_univ _)
            exact abs_eq_zero.mp this
          have : sqn w = 0 := by
            unfold sqn
            simp [hw0]
          rw [hwS] at this
          exact one_ne_zero this
      have hΓ : (0 : ℝ) < Fintype.card Γ := by exact_mod_cast Fintype.card_pos
      rw [hs0] at hsum
      simp only [Pi.zero_apply, Finset.sum_const_zero] at hsum
      nlinarith
  have hlam : lam₁ ≤ lam := by
    have h1 := hinv s hsinv
    rw [hquadM] at hquad_s
    have h2 : quadF G s = lam₁ * sqn s := by linarith
    rw [h2] at h1
    exact le_of_mul_le_mul_right h1 hspos
  exact (hall v).trans (mul_le_mul_of_nonneg_right hlam (sqn_nonneg v))

section Bar

variable {Γ : Type*} [Group Γ] [Fintype Γ] [MulAction Γ I]
  [Fintype (MulAction.orbitRel.Quotient Γ I)] [DecidableEq (MulAction.orbitRel.Quotient Γ I)]

/-- The orbit of `i`. -/
def orb (Γ : Type*) [Group Γ] [MulAction Γ I] (i : I) : MulAction.orbitRel.Quotient Γ I :=
  Quotient.mk _ i

/-- `|O_a|`. -/
def orbCard (a : MulAction.orbitRel.Quotient Γ I) : ℕ :=
  (Finset.univ.filter (fun i : I => orb Γ i = a)).card

/-- `Ḡ_{ab} = (|O_a| |O_b|)^{-1/2} ∑_{i ∈ O_a, j ∈ O_b} G_{ij}`. -/
noncomputable def Gbar (G : I → I → ℝ) (a b : MulAction.orbitRel.Quotient Γ I) : ℝ :=
  (√((orbCard (Γ := Γ) a : ℝ) * orbCard (Γ := Γ) b))⁻¹ *
    ∑ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a),
      ∑ j ∈ Finset.univ.filter (fun j : I => orb Γ j = b), G i j

omit [Fintype I] [DecidableEq I] [Fintype Γ] [Fintype (MulAction.orbitRel.Quotient Γ I)]
  [DecidableEq (MulAction.orbitRel.Quotient Γ I)] in
theorem invariant_eq_out {s : I → ℝ} (hs : ∀ (σ : Γ) i, s (σ • i) = s i) (i : I) :
    s i = s (orb Γ i).out := by
  have h' : (MulAction.orbitRel Γ I) (orb Γ i).out i :=
    Quotient.exact (s := MulAction.orbitRel Γ I) (Quotient.out_eq (orb Γ i))
  rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at h'
  obtain ⟨σ, hσ⟩ := h'
  rw [← hσ, hs]

omit [DecidableEq I] [Fintype Γ] [Fintype (MulAction.orbitRel.Quotient Γ I)] in
theorem orbCard_pos (a : MulAction.orbitRel.Quotient Γ I) : 0 < orbCard (Γ := Γ) a := by
  unfold orbCard
  refine Finset.card_pos.mpr ⟨a.out, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
  exact Quotient.out_eq a

/-- **`lem:weighted-frame` (c), with the matrix `Ḡ`.** If `λ I - Ḡ ⪰ 0` on the orbits, then
`vᵀ G v ≤ λ |v|²` for every `v`, so `λ_max(G) ≤ λ`. -/
theorem perron_gate_bar (G : I → I → ℝ) (hG0 : ∀ i j, 0 ≤ G i j) (hGs : ∀ i j, G i j = G j i)
    (hGinv : ∀ (σ : Γ) i j, G (σ • i) (σ • j) = G i j) {lam : ℝ}
    (hbar : ∀ t : MulAction.orbitRel.Quotient Γ I → ℝ,
      ∑ a, ∑ b, t a * Gbar (Γ := Γ) G a b * t b ≤ lam * ∑ a, t a ^ 2)
    (v : I → ℝ) : quadF G v ≤ lam * sqn v := by
  refine perron_gate (Γ := Γ) G hG0 hGs hGinv (fun s hs => ?_) v
  set sb : MulAction.orbitRel.Quotient Γ I → ℝ := fun a => s a.out
  set n : MulAction.orbitRel.Quotient Γ I → ℝ := fun a => (orbCard (Γ := Γ) a : ℝ)
  have hn : ∀ a, 0 < n a := fun a => by
    simp only [n]
    exact_mod_cast orbCard_pos a
  have hsi : ∀ i, s i = sb (orb Γ i) := fun i => invariant_eq_out hs i
  set t : MulAction.orbitRel.Quotient Γ I → ℝ := fun a => √(n a) * sb a
  have hfib : ∀ f : I → ℝ, ∑ i, f i =
      ∑ a, ∑ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a), f i := fun f =>
    (Finset.sum_fiberwise Finset.univ (orb Γ) f).symm
  have hq : quadF G s = ∑ a, ∑ b, t a * Gbar (Γ := Γ) G a b * t b := by
    unfold quadF
    rw [hfib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have e1 : ∑ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a), ∑ j, s i * G i j * s j =
        ∑ b, sb a * sb b * ∑ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a),
          ∑ j ∈ Finset.univ.filter (fun j : I => orb Γ j = b), G i j := by
      have e0 : ∀ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a), ∑ j, s i * G i j * s j =
          ∑ b, ∑ j ∈ Finset.univ.filter (fun j : I => orb Γ j = b), sb a * sb b * G i j := by
        intro i hi
        rw [hfib]
        refine Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun j hj => ?_))
        rw [hsi i, hsi j, (Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2]
        ring
      rw [Finset.sum_congr rfl e0, Finset.sum_comm]
      refine Finset.sum_congr rfl (fun b _ => ?_)
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by rw [Finset.mul_sum])
    rw [e1]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp only [t, Gbar]
    have hab : √(n a) * √(n b) = √(n a * n b) := (Real.sqrt_mul (hn a).le _).symm
    have hpos : 0 < √(n a * n b) := Real.sqrt_pos.mpr (mul_pos (hn a) (hn b))
    change _ = √(n a) * sb a * ((√(n a * n b))⁻¹ * _) * (√(n b) * sb b)
    rw [show √(n a) * sb a * ((√(n a * n b))⁻¹ * (∑ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a),
        ∑ j ∈ Finset.univ.filter (fun j : I => orb Γ j = b), G i j)) * (√(n b) * sb b) =
        (√(n a) * √(n b)) * (√(n a * n b))⁻¹ * (sb a * sb b * ∑ i ∈ Finset.univ.filter
          (fun i : I => orb Γ i = a), ∑ j ∈ Finset.univ.filter (fun j : I => orb Γ j = b), G i j)
        by ring, hab, mul_inv_cancel₀ hpos.ne', one_mul]
  have hsq : sqn s = ∑ a, t a ^ 2 := by
    unfold sqn
    rw [hfib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have e : ∀ i ∈ Finset.univ.filter (fun i : I => orb Γ i = a), s i ^ 2 = sb a ^ 2 := by
      intro i hi
      rw [hsi i, (Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl e, Finset.sum_const, nsmul_eq_mul]
    simp only [t, mul_pow, Real.sq_sqrt (hn a).le]
    rfl
  rw [hq, hsq]
  exact hbar t

end Bar

end Perron

end Sarkozy.Cuts

module

public import Sarkozy.Slots

/-!
# The reflection seminorm

`cor:seminorm` and parts (c), (d) of `lem:record:holder`
(`paper/sections/05_positivity.tex`). For a linear functional `L` on functions of
labellings `z : V → X` whose diagonal energies `Z(g) = L(∏ᵥ g(zᵥ))` are nonnegative
and which satisfies the signed Hölder inequality
`|L(∏ᵥ aᵥ(zᵥ))| ≤ ∏ᵥ Z(aᵥ)^(1/d)`, `d = |V|`, the map `g ↦ Z(g)^(1/d)` is a seminorm.
Hence finite signed combinations obey Minkowski's inequality, and averaging over a
family of functions with equal energies does not increase the energy.

The Hölder hypothesis is exactly the conclusion of `Sarkozy.signed_holder_of_sorting`,
and `Sarkozy.slot_signed_holder` supplies it for the paper's 72 slots.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy

variable {V X : Type*} [Fintype V]

/-- The root energy `Z(g)^(1/d)`. -/
noncomputable def rootEnergy (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (g : X → ℝ) : ℝ :=
  diagonalIntegral L g ^ ((1 : ℝ) / (Fintype.card V : ℝ))

/-- The signed Hölder property of a functional. -/
def SignedHolder (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  (∀ g, 0 ≤ diagonalIntegral L g) ∧
    ∀ a : V → X → ℝ, |multilinearIntegral L a| ≤ ∏ v, rootEnergy L (a v)

theorem slot_signedHolder {X : Type*} {L : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ} (hp : SlotReflectionPositive L) :
    SignedHolder L := by
  refine ⟨slot_diagonal_nonneg hp, fun a => ?_⟩
  have h := slot_signed_holder hp a
  simpa only [rootEnergy, card_slot, Nat.cast_ofNat] using h

namespace SignedHolder

variable {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ}

theorem rootEnergy_nonneg (h : SignedHolder L) (g : X → ℝ) : 0 ≤ rootEnergy L g :=
  Real.rpow_nonneg (h.1 g) _

theorem rootEnergy_pow [Nonempty V] (h : SignedHolder L) (g : X → ℝ) :
    rootEnergy L g ^ Fintype.card V = diagonalIntegral L g := by
  unfold rootEnergy
  rw [← Real.rpow_mul_natCast (h.1 g)]
  have hd : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [one_div_mul_cancel hd, Real.rpow_one]

/-- Expanding a sum at every slot (multilinearity). -/
theorem diagonalIntegral_add [DecidableEq V] (f g : X → ℝ) :
    diagonalIntegral L (f + g) = ∑ t ∈ (Finset.univ : Finset V).powerset,
      multilinearIntegral L (fun v => if v ∈ t then f else g) := by
  unfold diagonalIntegral multilinearIntegral
  rw [← map_sum]
  congr 1
  funext z
  rw [Finset.sum_apply]
  simp only [Pi.add_apply]
  rw [Finset.prod_add]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show (∏ v, (if v ∈ t then f else g) (z v)) =
      ∏ v, (if v ∈ t then f (z v) else g (z v)) by
    refine Finset.prod_congr rfl fun v _ => ?_
    split_ifs <;> rfl]
  rw [Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.univ_inter]
  congr 1
  refine Finset.prod_congr ?_ fun _ _ => rfl
  ext v
  simp

/-- The triangle inequality for the root energy. -/
theorem rootEnergy_add_le [DecidableEq V] [Nonempty V] (h : SignedHolder L) (f g : X → ℝ) :
    rootEnergy L (f + g) ≤ rootEnergy L f + rootEnergy L g := by
  set x := rootEnergy L f
  set y := rootEnergy L g
  have hx : 0 ≤ x := h.rootEnergy_nonneg f
  have hy : 0 ≤ y := h.rootEnergy_nonneg g
  have hterm (t : Finset V) : |multilinearIntegral L (fun v => if v ∈ t then f else g)| ≤
      x ^ t.card * y ^ (Finset.univ \ t).card := by
    refine (h.2 _).trans_eq ?_
    rw [show (∏ v, rootEnergy L (if v ∈ t then f else g)) =
        ∏ v, (if v ∈ t then x else y) by
      refine Finset.prod_congr rfl fun v _ => ?_
      split_ifs <;> rfl]
    rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const, Finset.filter_mem_eq_inter,
      Finset.univ_inter,
      show (Finset.univ.filter fun v => v ∉ t) = Finset.univ \ t by ext v; simp]
  have hsum : diagonalIntegral L (f + g) ≤ (x + y) ^ Fintype.card V := by
    rw [diagonalIntegral_add]
    have hbin : (x + y) ^ Fintype.card V = ∑ t ∈ (Finset.univ : Finset V).powerset,
        x ^ t.card * y ^ (Finset.univ \ t).card := by
      rw [← Finset.card_univ, ← Finset.prod_const, Finset.prod_add]
      simp only [Finset.prod_const]
    rw [hbin]
    exact Finset.sum_le_sum fun t _ => (le_abs_self _).trans (hterm t)
  have hroot := Real.rpow_le_rpow (h.1 (f + g)) hsum
    (by positivity : (0 : ℝ) ≤ 1 / (Fintype.card V : ℝ))
  unfold rootEnergy at hroot ⊢
  refine hroot.trans_eq ?_
  rw [← Real.rpow_natCast, ← Real.rpow_mul (add_nonneg hx hy)]
  have hd : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_one_div_cancel hd, Real.rpow_one]

/-- Absolute homogeneity of the root energy. -/
theorem rootEnergy_smul [Nonempty V] (h : SignedHolder L) (c : ℝ) (g : X → ℝ) :
    rootEnergy L (c • g) = |c| * rootEnergy L g := by
  have hmul : diagonalIntegral L (c • g) = c ^ Fintype.card V * diagonalIntegral L g := by
    unfold diagonalIntegral multilinearIntegral
    rw [← smul_eq_mul, ← map_smul]
    congr 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib, Finset.prod_const,
      Finset.card_univ]
  have habs : diagonalIntegral L (c • g) = |c| ^ Fintype.card V * diagonalIntegral L g := by
    have h0 := h.1 (c • g)
    have h1 := h.1 g
    rw [← abs_of_nonneg h0, hmul, abs_mul, abs_pow, abs_of_nonneg h1]
  unfold rootEnergy
  rw [habs, Real.mul_rpow (pow_nonneg (abs_nonneg c) _) (h.1 g), ← Real.rpow_natCast,
    ← Real.rpow_mul (abs_nonneg c)]
  have hd : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [mul_one_div_cancel hd, Real.rpow_one]

/-- Minkowski's inequality for finite signed combinations. -/
theorem rootEnergy_sum_le [DecidableEq V] [Nonempty V] (h : SignedHolder L) {ι : Type*} (s : Finset ι)
    (c : ι → ℝ) (g : ι → X → ℝ) :
    rootEnergy L (∑ i ∈ s, c i • g i) ≤ ∑ i ∈ s, |c i| * rootEnergy L (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have h0 := h.rootEnergy_smul 0 (0 : X → ℝ)
    simp only [zero_smul, abs_zero, zero_mul] at h0
    exact h0.le
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (h.rootEnergy_add_le _ _).trans (add_le_add ?_ ih)
    exact (h.rootEnergy_smul (c i) (g i)).le

/-- Averaging a family of functions of root energy at most `M` gives root energy at
most `M` (part (d) of `lem:record:holder`, in the form used for averages over
translates and over the progressions of a square step). -/
theorem rootEnergy_average_le [DecidableEq V] [Nonempty V] (h : SignedHolder L) {ι : Type*} (s : Finset ι)
    (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1) (g : ι → X → ℝ)
    {M : ℝ} (hM : ∀ i ∈ s, rootEnergy L (g i) ≤ M) :
    rootEnergy L (∑ i ∈ s, w i • g i) ≤ M := by
  refine (h.rootEnergy_sum_le s w g).trans ?_
  calc
    ∑ i ∈ s, |w i| * rootEnergy L (g i) ≤ ∑ i ∈ s, w i * M := by
      refine Finset.sum_le_sum fun i hi => ?_
      rw [abs_of_nonneg (hw i hi)]
      exact mul_le_mul_of_nonneg_left (hM i hi) (hw i hi)
    _ = M := by rw [← Finset.sum_mul, hsum, one_mul]

/-- The energy form of the averaging bound. -/
theorem diagonalIntegral_average_le [DecidableEq V] [Nonempty V] (h : SignedHolder L) {ι : Type*}
    (s : Finset ι) (w : ι → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hsum : ∑ i ∈ s, w i = 1)
    (g : ι → X → ℝ) {M : ℝ} (hM : ∀ i ∈ s, diagonalIntegral L (g i) ≤ M) :
    diagonalIntegral L (∑ i ∈ s, w i • g i) ≤ M := by
  by_cases hs : s.Nonempty
  · obtain ⟨i₀, hi₀⟩ := hs
    have hM0 : 0 ≤ M := (h.1 (g i₀)).trans (hM i₀ hi₀)
    have hroot : ∀ i ∈ s, rootEnergy L (g i) ≤ M ^ ((1 : ℝ) / (Fintype.card V : ℝ)) :=
      fun i hi => Real.rpow_le_rpow (h.1 _) (hM i hi) (by positivity)
    have ha := h.rootEnergy_average_le s w hw hsum g hroot
    have hp := pow_le_pow_left₀ (h.rootEnergy_nonneg _) ha (Fintype.card V)
    rw [h.rootEnergy_pow] at hp
    refine hp.trans_eq ?_
    rw [← Real.rpow_natCast, ← Real.rpow_mul hM0]
    have hd : (Fintype.card V : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [one_div_mul_cancel hd, Real.rpow_one]
  · rw [Finset.not_nonempty_iff_eq_empty] at hs
    subst hs
    simp at hsum

/-- Invariance (part (c) of `lem:record:holder`): if `L` is invariant under applying
`ψ` at every slot, the energy of `g ∘ ψ` equals that of `g`. -/
theorem diagonalIntegral_comp_of_invariant (ψ : X → X)
    (hinv : ∀ F : (V → X) → ℝ, L (fun z => F (fun v => ψ (z v))) = L F) (g : X → ℝ) :
    diagonalIntegral L (g ∘ ψ) = diagonalIntegral L g := by
  unfold diagonalIntegral multilinearIntegral
  exact hinv (fun z => ∏ v, g (z v))

end SignedHolder
end Sarkozy

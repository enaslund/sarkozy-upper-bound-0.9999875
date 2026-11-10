module

public import Sarkozy.SpectralC.AffinePairs
public import Sarkozy.SpectralC.CouplingData
public import Sarkozy.SpectralC.CovariantFields

@[expose] public section

/-!
# The degree-one block (`lem:spec:degone`(a))

`paper/sections/14_spectral.tex`, `lem:spec:degone`(a). Let `λ` be the cut law of the pair of
labellings `(x, x')` of the two halves (`Λ` on `(U⁺ → 𝔽_p)²`), invariant under the diagonal
action of `Aff_p` and with `x_k ≠ x'_l` almost surely (injectivity across the cut). For
`v = ∑_k g_k(x_k)`, `v' = ∑_k h_k(x'_k)` with mean-zero `g_k, h_k`:
`E_λ[\overline{v(x)} v'(x')] = ∑_{ξ ≠ 0} ĝ(ξ)^* 𝐐(ξ) ĥ(ξ)`, with
`𝐐(ξ)_kl = −1/(p − 1) + (p/(p − 1)) c_ξ δ^×_kl` and `δ^×_kl = E_λ χ(x'_l − x_k)`
(`degone_bilinear`). If `λ` is also invariant under the swap `(x, x') ↦ (x', x)`,
`δ^×_lk = χ(−1) δ^×_kl` (`deltaX_swap`, the last claim of `lem:spec:small`(a)), `𝐐(ξ)` is
Hermitian and `𝐐(−ξ) = \overline{𝐐(ξ)}` (`degoneQ_hermitian`, `degoneQ_neg`).

`lem:spec:degone`(c), the identity part: for the half law `μ` (invariant, injective), `ξ ≠ 0`
and `w`, `‖∑_k w_k e_ξ(x_k)‖²_μ = w^*𝐍(ξ)w` with
`𝐍(ξ) = I − (𝟙𝟙ᵀ − I)/(p − 1) + (p/(p − 1)) c_ξ Δ^μ`, `Δ^μ_kl = E_μ χ(x_l − x_k)` (`k ≠ l`),
`Δ^μ_kk = 0` (`degone_norm`); different mode components are orthogonal (`degone_modes_orth`).
The bound `‖𝐍(ξ) − I‖ ≤ ε_V` is `degoneN_sub_one` (`Sarkozy.SpectralC.MatrixNorms`), and the norm
equivalence `(1 ± ε_V)‖g‖²` is `degone_equiv_bounds` (`Sarkozy.SpectralC.DegreeOneEquiv`).
Part (b) is in `Sarkozy.SpectralC.MatrixNorms`.

The identity `E_λ[\overline{v(x)} v'(x')] = ⟨v, Op v'⟩_μ` is `lem:spec:cutkernel`(b) and is not
restated. New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The pair marginal `π_kl(a, b) = λ(x_k = a, x'_l = b)`. -/
noncomputable def pairMarg (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (k l : U) (a b : ZMod p) : ℝ :=
  ∑ z, if z.1 k = a ∧ z.2 l = b then Λ z else 0

/-- `δ^×_kl = E_λ χ(x'_l − x_k)`. -/
noncomputable def deltaX (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (k l : U) : ℂ :=
  ∑ z, (Λ z : ℂ) * chiC p (z.2 l - z.1 k)

/-- `𝐐(ξ)_kl = −1/(p − 1) + (p/(p − 1)) c_ξ δ^×_kl`. -/
noncomputable def degoneQ (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (ξ : ZMod p) (k l : U) : ℂ :=
  -1 / ((p : ℂ) - 1) + (p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ * deltaX Λ k l

/-- The expectation of a function of `(x_k, x'_l)` through the pair marginal. -/
lemma sum_pairMarg (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (k l : U)
    (F : ZMod p → ZMod p → ℂ) :
    ∑ a, ∑ b, (pairMarg Λ k l a b : ℂ) * F a b = ∑ z, (Λ z : ℂ) * F (z.1 k) (z.2 l) := by
  unfold pairMarg
  have h : ∀ a b, ((∑ z, if z.1 k = a ∧ z.2 l = b then Λ z else 0 : ℝ) : ℂ) * F a b =
      ∑ z, (if z.1 k = a then (if z.2 l = b then (Λ z : ℂ) * F a b else 0) else 0) := by
    intro a b
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro z _
    by_cases h1 : z.1 k = a <;> by_cases h2 : z.2 l = b <;> simp [h1, h2]
  simp_rw [h]
  refine (sum_congr rfl fun a _ => sum_comm).trans ?_
  refine sum_comm.trans ?_
  apply sum_congr rfl
  intro z _
  rw [sum_eq_single (z.1 k)]
  · rw [sum_eq_single (z.2 l)]
    · rw [ite_eq_left rfl, ite_eq_left rfl]
    · intro b _ hb; rw [ite_eq_left rfl, ite_eq_right (Ne.symm hb)]
    · intro h0; exact absurd (mem_univ _) h0
  · intro a _ ha
    apply sum_eq_zero
    intro b _
    rw [ite_eq_right (Ne.symm ha)]
  · intro h0; exact absurd (mem_univ _) h0

lemma pairMarg_inv (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      Λ (affLab s c z.1, affLab s c z.2) = Λ z) (k l : U) :
    IsAffInv (pairMarg Λ k l) := by
  intro s c a b hs hsq
  unfold pairMarg
  have hbij : Function.Bijective (Prod.map (affLab (U := U) s c) (affLab (U := U) s c)) :=
    (affLab_bijective hs c).prodMap (affLab_bijective hs c)
  rw [← hbij.sum_comp]
  apply sum_congr rfl
  intro z _
  simp only [Prod.map_fst, Prod.map_snd]
  have hmap : Λ (Prod.map (affLab s c) (affLab s c) z) = Λ z := hinv s c z hs hsq
  rw [hmap]
  have h1 : (affLab s c z.1 k = s * a + c) ↔ z.1 k = a := by
    unfold affLab
    constructor
    · intro h; exact mul_left_cancel₀ hs (by linear_combination h)
    · intro h; rw [h]
  have h2 : (affLab s c z.2 l = s * b + c) ↔ z.2 l = b := by
    unfold affLab
    constructor
    · intro h; exact mul_left_cancel₀ hs (by linear_combination h)
    · intro h; rw [h]
  by_cases ha : z.1 k = a <;> by_cases hb : z.2 l = b <;> simp [h1, h2, ha, hb]

/-- **`lem:spec:degone`(a)**: `E_λ[\overline{v(x)} v'(x')] = ∑_{ξ ≠ 0} ĝ(ξ)^* 𝐐(ξ) ĥ(ξ)`. -/
theorem degone_bilinear (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (hΛ1 : ∑ z, Λ z = 1)
    (hinv : ∀ (s c : ZMod p) (z : (U → ZMod p) × (U → ZMod p)), s ≠ 0 → IsSquare s →
      Λ (affLab s c z.1, affLab s c z.2) = Λ z)
    (hinj : ∀ (z : (U → ZMod p) × (U → ZMod p)) (k l : U), Λ z ≠ 0 → z.1 k ≠ z.2 l)
    (g h : U → ZMod p → ℂ) (hg : ∀ k, ∑ a, g k a = 0) (hh : ∀ k, ∑ a, h k a = 0) :
    ∑ z, (Λ z : ℂ) * (conj (∑ k, g k (z.1 k)) * ∑ l, h l (z.2 l)) =
      ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0),
        ∑ k, ∑ l, conj (fcoef (g k) ξ) * degoneQ Λ ξ k l * fcoef (h l) ξ := by
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (oddChar (p := p) hp2)
  have hpC := p_ne_zero_C (p := p)
  -- one pair `(k, l)`
  have hkl : ∀ k l, ∑ z, (Λ z : ℂ) * (conj (g k (z.1 k)) * h l (z.2 l)) =
      ∑ ξ, conj (fcoef (g k) ξ) * degoneQ Λ ξ k l * fcoef (h l) ξ := by
    intro k l
    have htot : ∑ a, ∑ b, pairMarg Λ k l a b = 1 := by
      have := sum_pairMarg Λ k l (fun _ _ => (1 : ℂ))
      simp only [mul_one] at this
      have h2 : ((∑ a, ∑ b, pairMarg Λ k l a b : ℝ) : ℂ) = ((∑ z, Λ z : ℝ) : ℂ) := by
        push_cast; exact this
      rw [hΛ1] at h2
      exact_mod_cast h2
    obtain ⟨_, _, _, hbil⟩ := affPair_law hp2 (pairMarg Λ k l) htot (pairMarg_inv Λ hinv k l) hn
    have hmg : meanC (g k) = 0 := by unfold meanC; rw [hg k, mul_zero]
    have hmh : meanC (h l) = 0 := by unfold meanC; rw [hh l, mul_zero]
    have hb := hbil (g k) (h l) hmg hmh
    -- `π^= = 0`
    have heq : ∑ a, pairMarg Λ k l a a = 0 := by
      have := sum_pairMarg Λ k l (fun a b => if a = b then (1 : ℂ) else 0)
      have h3 : ∑ z, (Λ z : ℂ) * (if z.1 k = z.2 l then (1 : ℂ) else 0) = 0 := by
        apply sum_eq_zero
        intro z _
        by_cases hz : Λ z = 0
        · rw [hz]; simp
        · rw [ite_eq_right (hinj z k l hz), mul_zero]
      rw [h3] at this
      have h4 : ∑ a, ∑ b, (pairMarg Λ k l a b : ℂ) * (if a = b then (1 : ℂ) else 0) =
          ((∑ a, pairMarg Λ k l a a : ℝ) : ℂ) := by
        push_cast
        apply sum_congr rfl
        intro a _
        rw [sum_eq_single a]
        · simp
        · intro b _ hb; rw [ite_eq_right (Ne.symm hb), mul_zero]
        · intro h0; exact absurd (mem_univ a) h0
      rw [h4] at this
      exact_mod_cast this
    -- `D = δ^×_kl`
    have hD : ∑ a, ∑ b, (pairMarg Λ k l a b : ℂ) * chiC p (b - a) = deltaX Λ k l :=
      sum_pairMarg Λ k l (fun a b => chiC p (b - a))
    have hLHS : ∑ z, (Λ z : ℂ) * (conj (g k (z.1 k)) * h l (z.2 l)) =
        ∑ a, ∑ b, (pairMarg Λ k l a b : ℂ) * conj (g k a) * h l b := by
      rw [← sum_pairMarg Λ k l (fun a b => conj (g k a) * h l b)]
      apply sum_congr rfl; intro a _
      apply sum_congr rfl; intro b _
      ring
    rw [hLHS, hb, heq, hD, ip_eq_sum_fcoef, ip_eq_sum_fcoef]
    simp_rw [fcoef_gaussOp hp2]
    simp only [mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
    apply sum_congr rfl
    intro ξ _
    unfold degoneQ
    push_cast
    ring
  -- sum over `(k, l)`
  have hexp : ∑ z, (Λ z : ℂ) * (conj (∑ k, g k (z.1 k)) * ∑ l, h l (z.2 l)) =
      ∑ k, ∑ l, ∑ z, (Λ z : ℂ) * (conj (g k (z.1 k)) * h l (z.2 l)) := by
    simp_rw [map_sum, sum_mul_sum, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl; intro k _
    rw [sum_comm]
  rw [hexp]
  simp_rw [hkl]
  -- exchange and drop `ξ = 0`
  have hperm : ∑ k, ∑ l, ∑ ξ, conj (fcoef (g k) ξ) * degoneQ Λ ξ k l * fcoef (h l) ξ =
      ∑ ξ, ∑ k, ∑ l, conj (fcoef (g k) ξ) * degoneQ Λ ξ k l * fcoef (h l) ξ :=
    (sum_congr rfl fun k _ => sum_comm).trans sum_comm
  rw [hperm, ← sum_filter_add_sum_filter_not univ (fun ξ : ZMod p => ξ ≠ 0)]
  have hz : ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ¬ ξ ≠ 0),
      ∑ k, ∑ l, conj (fcoef (g k) ξ) * degoneQ Λ ξ k l * fcoef (h l) ξ = 0 := by
    apply sum_eq_zero
    intro ξ hξ
    rw [mem_filter, not_not] at hξ
    rw [hξ.2]
    simp_rw [fcoef_zero, hh, mul_zero, sum_const_zero]
  rw [hz, add_zero]

lemma conj_deltaX (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (k l : U) :
    conj (deltaX Λ k l) = deltaX Λ k l := by
  unfold deltaX
  rw [map_sum]
  apply sum_congr rfl
  intro z _
  rw [map_mul, Complex.conj_ofReal, conj_chiC]

/-- **`lem:spec:small`(a), last claim**: under the swap invariance of `λ`,
`E_λ χ(x'_k − x_l) = χ(−1) E_λ χ(x'_l − x_k)`. -/
theorem deltaX_swap (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (hswap : ∀ z, Λ (z.2, z.1) = Λ z)
    (k l : U) : deltaX Λ l k = chiC p (-1) * deltaX Λ k l := by
  unfold deltaX
  rw [← Fintype.sum_equiv (Equiv.prodComm _ _) (fun z => (Λ (z.2, z.1) : ℂ) *
    chiC p (z.1 k - z.2 l)) _ (fun z => rfl)]
  rw [mul_sum]
  apply sum_congr rfl
  intro z _
  rw [hswap, show z.1 k - z.2 l = -1 * (z.2 l - z.1 k) by ring, map_mul]
  ring

/-- **`lem:spec:degone`(a)**: `𝐐(ξ)` is Hermitian (swap-invariant `λ`). -/
theorem degoneQ_hermitian (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (hswap : ∀ z, Λ (z.2, z.1) = Λ z) (ξ : ZMod p) (k l : U) :
    conj (degoneQ Λ ξ l k) = degoneQ Λ ξ k l := by
  unfold degoneQ
  simp only [map_add, map_div₀, map_neg, map_one, map_sub, map_mul, Complex.conj_natCast]
  rw [conj_gaussEig hp2, conj_deltaX, deltaX_swap Λ hswap, gaussEig_neg]
  have h1 : chiC p (-1) * chiC p (-1) = 1 := by rw [← map_mul]; norm_num
  linear_combination (p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ * deltaX Λ k l * h1

/-- **`lem:spec:degone`(a)**: `𝐐(−ξ) = \overline{𝐐(ξ)}` (entrywise). -/
theorem degoneQ_neg (hp2 : p ≠ 2) (Λ : (U → ZMod p) × (U → ZMod p) → ℝ) (ξ : ZMod p)
    (k l : U) : degoneQ Λ (-ξ) k l = conj (degoneQ Λ ξ k l) := by
  unfold degoneQ
  simp only [map_add, map_div₀, map_neg, map_one, map_sub, map_mul, Complex.conj_natCast]
  rw [conj_gaussEig hp2, conj_deltaX]

/-! ## The half law (`lem:spec:degone`(c)) -/

/-- The pair marginal `(x_k, x_l)` of a law of one labelling. -/
noncomputable def pairMarg1 (μ : (U → ZMod p) → ℝ) (k l : U) (a b : ZMod p) : ℝ :=
  ∑ x, if x k = a ∧ x l = b then μ x else 0

lemma sum_pairMarg1 (μ : (U → ZMod p) → ℝ) (k l : U) (F : ZMod p → ZMod p → ℂ) :
    ∑ a, ∑ b, (pairMarg1 μ k l a b : ℂ) * F a b = ∑ x, (μ x : ℂ) * F (x k) (x l) := by
  unfold pairMarg1
  have h : ∀ a b, ((∑ x, if x k = a ∧ x l = b then μ x else 0 : ℝ) : ℂ) * F a b =
      ∑ x, (if x k = a then (if x l = b then (μ x : ℂ) * F a b else 0) else 0) := by
    intro a b
    push_cast
    rw [sum_mul]
    apply sum_congr rfl
    intro x _
    by_cases h1 : x k = a <;> by_cases h2 : x l = b <;> simp [h1, h2]
  simp_rw [h]
  refine (sum_congr rfl fun a _ => sum_comm).trans ?_
  refine sum_comm.trans ?_
  apply sum_congr rfl
  intro x _
  rw [sum_eq_single (x k)]
  · rw [sum_eq_single (x l)]
    · rw [ite_eq_left rfl, ite_eq_left rfl]
    · intro b _ hb; rw [ite_eq_left rfl, ite_eq_right (Ne.symm hb)]
    · intro h0; exact absurd (mem_univ _) h0
  · intro a _ ha
    apply sum_eq_zero
    intro b _
    rw [ite_eq_right (Ne.symm ha)]
  · intro h0; exact absurd (mem_univ _) h0

lemma pairMarg1_inv (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (k l : U) : IsAffInv (pairMarg1 μ k l) := by
  intro s c a b hs hsq
  unfold pairMarg1
  rw [← (affLab_bijective (U := U) hs c).sum_comp]
  apply sum_congr rfl
  intro x _
  rw [hinv s c x hs hsq]
  have h1 : (affLab s c x k = s * a + c) ↔ x k = a := by
    unfold affLab
    constructor
    · intro h; exact mul_left_cancel₀ hs (by linear_combination h)
    · intro h; rw [h]
  have h2 : (affLab s c x l = s * b + c) ↔ x l = b := by
    unfold affLab
    constructor
    · intro h; exact mul_left_cancel₀ hs (by linear_combination h)
    · intro h; rw [h]
  by_cases ha : x k = a <;> by_cases hb : x l = b <;> simp [h1, h2, ha, hb]

/-- `Δ^μ_kl = E_μ χ(x_l − x_k)` for `k ≠ l`, `Δ^μ_kk = 0`. -/
noncomputable def deltaMu (μ : (U → ZMod p) → ℝ) (k l : U) : ℂ :=
  if k = l then 0 else ∑ x, (μ x : ℂ) * chiC p (x l - x k)

/-- `𝐍(ξ) = I − (𝟙𝟙ᵀ − I)/(p − 1) + (p/(p − 1)) c_ξ Δ^μ`. -/
noncomputable def degoneN (μ : (U → ZMod p) → ℝ) (ξ : ZMod p) (k l : U) : ℂ :=
  (if k = l then 1 else 0) - (if k = l then 0 else 1) / ((p : ℂ) - 1) +
    (p : ℂ) / ((p : ℂ) - 1) * gaussEig ξ * deltaMu μ k l

lemma ip_ech_gaussOp (hp2 : p ≠ 2) (ξ : ZMod p) : ip (ech ξ) (gaussOp (ech ξ)) = gaussEig ξ := by
  have h : gaussOp (ech ξ) = fun a => gaussEig ξ * ech ξ a := funext (gaussOp_ech hp2 ξ)
  rw [h]
  have h2 : ip (ech ξ) (fun a => gaussEig ξ * ech ξ a) = gaussEig ξ * ip (ech ξ) (ech ξ) := by
    unfold ip
    dsimp only
    simp only [mul_sum]
    apply sum_congr rfl; intro a _; ring
  rw [h2, ip_ech_ech, ite_eq_left rfl, mul_one]

/-- **`lem:spec:degone`(c), the identity**: `‖∑_k w_k e_ξ(x_k)‖²_μ = w^*𝐍(ξ)w` for `ξ ≠ 0`. -/
theorem degone_norm (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {ξ : ZMod p} (hξ : ξ ≠ 0) (w : U → ℂ) :
    ∑ x, (μ x : ℂ) * ((‖∑ k, w k * ech ξ (x k)‖ ^ 2 : ℝ) : ℂ) = qform (degoneN μ ξ) w := by
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare (oddChar (p := p) hp2)
  have hpC := p_ne_zero_C (p := p)
  have hmean : meanC (ech ξ) = 0 := by rw [meanC_ech, ite_eq_right hξ]
  -- one pair `(k, l)`
  have hkl : ∀ k l, ∑ x, (μ x : ℂ) * (conj (ech ξ (x k)) * ech ξ (x l)) = degoneN μ ξ k l := by
    intro k l
    by_cases hkl : k = l
    · subst hkl
      have h1 : ∀ x : U → ZMod p, conj (ech ξ (x k)) * ech ξ (x k) = 1 := by
        intro x; rw [mul_comm, Complex.mul_conj', norm_ech]; simp
      simp_rw [h1, mul_one]
      unfold degoneN deltaMu
      simp only [ite_true, sub_zero, zero_div, mul_zero, add_zero]
      exact_mod_cast hμ1
    · have htot : ∑ a, ∑ b, pairMarg1 μ k l a b = 1 := by
        have := sum_pairMarg1 μ k l (fun _ _ => (1 : ℂ))
        simp only [mul_one] at this
        have h2 : ((∑ a, ∑ b, pairMarg1 μ k l a b : ℝ) : ℂ) = ((∑ x, μ x : ℝ) : ℂ) := by
          push_cast; exact this
        rw [hμ1] at h2
        exact_mod_cast h2
      obtain ⟨_, _, _, hbil⟩ := affPair_law hp2 (pairMarg1 μ k l) htot
        (pairMarg1_inv μ hinv k l) hn
      have hb := hbil (ech ξ) (ech ξ) hmean hmean
      have heq : ∑ a, pairMarg1 μ k l a a = 0 := by
        have := sum_pairMarg1 μ k l (fun a b => if a = b then (1 : ℂ) else 0)
        have h3 : ∑ x, (μ x : ℂ) * (if x k = x l then (1 : ℂ) else 0) = 0 := by
          apply sum_eq_zero
          intro x _
          by_cases hx : μ x = 0
          · rw [hx]; simp
          · rw [ite_eq_right (hinj x k l hx hkl), mul_zero]
        rw [h3] at this
        have h4 : ∑ a, ∑ b, (pairMarg1 μ k l a b : ℂ) * (if a = b then (1 : ℂ) else 0) =
            ((∑ a, pairMarg1 μ k l a a : ℝ) : ℂ) := by
          push_cast
          apply sum_congr rfl
          intro a _
          rw [sum_eq_single a]
          · simp
          · intro b _ hb; rw [ite_eq_right (Ne.symm hb), mul_zero]
          · intro h0; exact absurd (mem_univ a) h0
        rw [h4] at this
        exact_mod_cast this
      have hD : ∑ a, ∑ b, (pairMarg1 μ k l a b : ℂ) * chiC p (b - a) = deltaMu μ k l := by
        rw [sum_pairMarg1 μ k l (fun a b => chiC p (b - a))]
        unfold deltaMu
        rw [ite_eq_right hkl]
      have hLHS : ∑ x, (μ x : ℂ) * (conj (ech ξ (x k)) * ech ξ (x l)) =
          ∑ a, ∑ b, (pairMarg1 μ k l a b : ℂ) * conj (ech ξ a) * ech ξ b := by
        rw [← sum_pairMarg1 μ k l (fun a b => conj (ech ξ a) * ech ξ b)]
        apply sum_congr rfl; intro a _
        apply sum_congr rfl; intro b _
        ring
      rw [hLHS, hb, heq, hD, ip_ech_ech, ite_eq_left rfl, ip_ech_gaussOp hp2]
      unfold degoneN
      rw [ite_eq_right hkl, ite_eq_right hkl]
      push_cast
      ring
  have hnorm : ∀ z : ℂ, ((‖z‖ ^ 2 : ℝ) : ℂ) = conj z * z := by
    intro z
    rw [Complex.ofReal_pow, ← Complex.mul_conj', mul_comm]
  simp_rw [hnorm]
  have hL : ∀ x : U → ZMod p, conj (∑ k, w k * ech ξ (x k)) * ∑ l, w l * ech ξ (x l) =
      ∑ k, ∑ l, conj (w k) * (conj (ech ξ (x k)) * ech ξ (x l)) * w l := by
    intro x
    rw [map_sum, sum_mul_sum]
    apply sum_congr rfl; intro k _
    apply sum_congr rfl; intro l _
    rw [map_mul]
    ring
  simp_rw [hL, mul_sum]
  unfold qform
  simp_rw [← hkl]
  simp only [mul_sum, sum_mul]
  refine sum_comm.trans ?_
  refine sum_congr rfl fun k _ => ?_
  refine sum_comm.trans ?_
  refine sum_congr rfl fun l _ => sum_congr rfl fun x _ => ?_
  ring

/-- **`lem:spec:degone`(c)**: different mode components are orthogonal in `L²(μ)`. -/
theorem degone_modes_orth (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    {ξ η : ZMod p} (hξη : ξ ≠ η) (w w' : U → ℂ) :
    ∑ x, (μ x : ℂ) * (conj (∑ k, w k * ech ξ (x k)) * ∑ l, w' l * ech η (x l)) = 0 := by
  set S := ∑ x, (μ x : ℂ) * (conj (∑ k, w k * ech ξ (x k)) * ∑ l, w' l * ech η (x l)) with hS
  have hbij := affLab_bijective (U := U) (one_ne_zero : (1 : ZMod p) ≠ 0) 1
  have htr : ∀ (ζ : ZMod p) (v : U → ℂ) (x : U → ZMod p),
      ∑ k, v k * ech ζ (affLab 1 1 x k) = ech ζ 1 * ∑ k, v k * ech ζ (x k) := by
    intro ζ v x
    rw [mul_sum]
    apply sum_congr rfl; intro k _
    unfold affLab
    rw [one_mul, ech_add_right]
    ring
  have h1 : S = conj (ech ξ 1) * ech η 1 * S := by
    conv_lhs => rw [hS, ← hbij.sum_comp]
    rw [hS, mul_sum]
    apply sum_congr rfl
    intro x _
    rw [hinv 1 1 x one_ne_zero ⟨1, by ring⟩, htr, htr, map_mul]
    ring
  have h2 : conj (ech ξ 1) * ech η 1 = ech (η - ξ) 1 := by
    rw [conj_ech, ← ech_add_left]
    ring_nf
  have h3 : ech (η - ξ) (1 : ZMod p) ≠ 1 := by
    intro h
    unfold ech at h
    rw [mul_one, ← AddChar.map_zero_eq_one (ZMod.stdAddChar (N := p))] at h
    exact hξη (sub_eq_zero.mp (ZMod.injective_stdAddChar h)).symm
  rw [h2] at h1
  have : (1 - ech (η - ξ) (1 : ZMod p)) * S = 0 := by linear_combination h1
  rcases mul_eq_zero.mp this with h | h
  · exact absurd (sub_eq_zero.mp h).symm h3
  · exact h

end Sarkozy.SpectralC

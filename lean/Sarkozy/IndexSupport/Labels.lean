module

public import Sarkozy.IndexSupport.Coupling

/-!
# Conditional expectations, residue chains, and convolution transitions

This file shows that the paper's instances satisfy the hypotheses used in
`Sarkozy/IndexSupport/Filtration.lean` and `Sarkozy/IndexSupport/SignedIndex.lean`.

* `condExpMatrix π`: conditional expectation, for the uniform law on a finite set, given
  a labeling `π` (`condExpMatrix_mulVec`: the average over the fibre). It is symmetric,
  nested labelings give `E_π E_ρ = E_ρ E_π = E_π` (`condExpMatrix_mul_of_le`), a constant
  labeling gives the average and an injective one the identity.
* `Chain.ofLabels`: a chain of conditional-expectation projections from nested labelings;
  `Chain.residues p h`: conditioning a residue `s ∈ ℤ/p^hℤ` on `s mod p^l`, `0 ≤ l ≤ h`
  (`def:hyb:coupled`(e), the residue coordinates after the Chinese remainder theorem).
  The interval coordinate uses `Chain.whole` (constants and identity).
* `convMatrix μ`: the transition `T f(s) = ∑_r μ(r) f(s + r)` on a finite abelian group
  (`def:hyb:coupled`(c): the convolution with the law of the square increments, and the
  cyclic shift of the interval, `μ` the point mass at `1`). A law gives a doubly
  stochastic matrix (`convMatrix_doublyStochastic`). Convolutions commute with every
  translation-invariant matrix, in particular with the residue conditional expectations,
  so they map every exact-conductor space `ran(E_l - E_{l-1})` into itself
  (`conv_rangeBound`; the claim "convolution preserves each exact conductor space" in the
  proof of `cor:index-support-frame`(i)). Only the norm bound by the chosen tail remains a
  hypothesis there, as in the paper. The cyclic shift is an isometry, so the interval
  coordinate has tail one (`shift_rangeBound`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section CondExp

variable {Ω γ : Type*} [Fintype Ω] [DecidableEq γ]

/-- The fibre of the labeling `π` through `x`. -/
def fibre (π : Ω → γ) (x : Ω) : Finset Ω := univ.filter (fun z => π z = π x)

theorem mem_fibre_self (π : Ω → γ) (x : Ω) : x ∈ fibre π x := by
  simp [fibre]

theorem fibre_card_pos (π : Ω → γ) (x : Ω) : (0 : ℝ) < (fibre π x).card := by
  exact_mod_cast Finset.card_pos.mpr ⟨x, mem_fibre_self π x⟩

theorem fibre_eq {π : Ω → γ} {x y : Ω} (h : π x = π y) : fibre π x = fibre π y := by
  ext z
  simp only [fibre, mem_filter, mem_univ, true_and, h]

/-- Conditional expectation given the labeling `π` for the uniform law. -/
noncomputable def condExpMatrix (π : Ω → γ) : Matrix Ω Ω ℝ :=
  fun x y => if π x = π y then ((fibre π x).card : ℝ)⁻¹ else 0

/-- `(E_π f)(x)` is the average of `f` over the fibre of `x`. -/
theorem condExpMatrix_mulVec (π : Ω → γ) (f : Ω → ℝ) (x : Ω) :
    (condExpMatrix π *ᵥ f) x = ((fibre π x).card : ℝ)⁻¹ * ∑ y ∈ fibre π x, f y := by
  simp only [Matrix.mulVec, dotProduct, condExpMatrix, ite_mul, zero_mul, fibre,
    Finset.sum_filter, Finset.mul_sum]
  apply sum_congr rfl
  intro y _
  by_cases h : π x = π y
  · rw [ite_eq_left h, ite_eq_left h.symm]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h), mul_zero]

theorem condExpMatrix_transpose (π : Ω → γ) : (condExpMatrix π)ᵀ = condExpMatrix π := by
  ext x y
  simp only [Matrix.transpose_apply, condExpMatrix]
  by_cases h : π x = π y
  · rw [ite_eq_left h, ite_eq_left h.symm, fibre_eq h]
  · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]

/-- For a labeling `ρ` finer than `π`, `E_π E_ρ = E_π`. -/
theorem condExpMatrix_mul_of_le {γ' : Type*} [DecidableEq γ'] {π : Ω → γ} {ρ : Ω → γ'}
    (h : ∀ x y, ρ x = ρ y → π x = π y) :
    condExpMatrix π * condExpMatrix ρ = condExpMatrix π := by
  ext x z
  simp only [Matrix.mul_apply, condExpMatrix]
  by_cases hxz : π x = π z
  · rw [ite_eq_left hxz]
    have hterm (y : Ω) : (if π x = π y then ((fibre π x).card : ℝ)⁻¹ else 0) *
        (if ρ y = ρ z then ((fibre ρ y).card : ℝ)⁻¹ else 0) =
        if ρ y = ρ z then ((fibre π x).card : ℝ)⁻¹ * ((fibre ρ z).card : ℝ)⁻¹ else 0 := by
      by_cases hy : ρ y = ρ z
      · have hπy : π x = π y := hxz.trans (h y z hy).symm
        rw [ite_eq_left hπy, ite_eq_left hy, ite_eq_left hy, fibre_eq hy]
      · rw [ite_eq_right hy, ite_eq_right hy, mul_zero]
    simp only [hterm]
    rw [← Finset.sum_filter, sum_const, nsmul_eq_mul]
    have hcard : ((univ.filter (fun y => ρ y = ρ z)).card : ℝ) = (fibre ρ z).card := rfl
    rw [hcard]
    have hpos := fibre_card_pos ρ z
    field_simp
  · rw [ite_eq_right hxz]
    apply Finset.sum_eq_zero
    intro y _
    by_cases hy : ρ y = ρ z
    · have hn : ¬ π x = π y := fun h' => hxz (h'.trans (h y z hy))
      rw [ite_eq_right hn, zero_mul]
    · rw [ite_eq_right hy, mul_zero]

theorem condExpMatrix_const {π : Ω → γ} (h : ∀ x y, π x = π y) :
    condExpMatrix π = meanMatrix Ω := by
  ext x y
  have hf : fibre π x = univ := by
    ext z
    simp [fibre, h z x]
  simp only [condExpMatrix, ite_eq_left (h x y), hf, card_univ, meanMatrix_apply]

theorem condExpMatrix_injective [DecidableEq Ω] {π : Ω → γ} (h : Function.Injective π) :
    condExpMatrix π = 1 := by
  ext x y
  have hf : fibre π x = {x} := by
    ext z
    simp only [fibre, mem_filter, mem_univ, true_and, mem_singleton]
    exact ⟨fun hz => h hz, fun hz => by rw [hz]⟩
  simp only [condExpMatrix, Matrix.one_apply, hf, card_singleton, Nat.cast_one, inv_one]
  by_cases hxy : x = y
  · rw [ite_eq_left (congrArg π hxy), ite_eq_left hxy]
  · rw [ite_eq_right (fun h' => hxy (h h')), ite_eq_right hxy]

/-- A chain of conditional-expectation projections given nested labelings
`π_0, …, π_h` with `π_0` constant and `π_h` injective. -/
noncomputable def Chain.ofLabels [DecidableEq Ω] (h : ℕ) (π : ℕ → Ω → γ)
    (hnest : ∀ l l', l ≤ l' → l' ≤ h → ∀ x y, π l' x = π l' y → π l x = π l y)
    (h0 : ∀ x y, π 0 x = π 0 y) (htop : Function.Injective (π h)) : Chain Ω where
  depth := h
  cond l := condExpMatrix (π l)
  transpose_cond l _ := condExpMatrix_transpose (π l)
  cond_mul_cond l l' hl hl' := by
    rcases le_total l l' with hle | hle
    · rw [min_eq_left hle]
      exact condExpMatrix_mul_of_le (hnest l l' hle hl')
    · rw [min_eq_right hle]
      have h1 := condExpMatrix_mul_of_le (hnest l' l hle hl)
      calc condExpMatrix (π l) * condExpMatrix (π l') =
          (condExpMatrix (π l') * condExpMatrix (π l))ᵀ := by
            rw [Matrix.transpose_mul, condExpMatrix_transpose, condExpMatrix_transpose]
        _ = condExpMatrix (π l') := by rw [h1, condExpMatrix_transpose]
  cond_zero := condExpMatrix_const h0
  cond_top := condExpMatrix_injective htop

theorem Chain.ofLabels_cond [DecidableEq Ω] (h : ℕ) (π : ℕ → Ω → γ)
    (hnest : ∀ l l', l ≤ l' → l' ≤ h → ∀ x y, π l' x = π l' y → π l x = π l y)
    (h0 : ∀ x y, π 0 x = π 0 y) (htop : Function.Injective (π h)) (l : ℕ) :
    (Chain.ofLabels h π hnest h0 htop).cond l = condExpMatrix (π l) := rfl

end CondExp

section Residues

/-- The residue labels `s ↦ s mod p^l` on `ℤ/p^hℤ`. -/
def residueLabel (p h : ℕ) (l : ℕ) (s : ZMod (p ^ h)) : ℕ := s.val % p ^ l

theorem residueLabel_nested (p h : ℕ) {l l' : ℕ} (hll' : l ≤ l') (x y : ZMod (p ^ h))
    (hxy : residueLabel p h l' x = residueLabel p h l' y) :
    residueLabel p h l x = residueLabel p h l y := by
  unfold residueLabel at *
  have hd : p ^ l ∣ p ^ l' := Nat.pow_dvd_pow p hll'
  rw [← Nat.mod_mod_of_dvd x.val hd, ← Nat.mod_mod_of_dvd y.val hd, hxy]

theorem residueLabel_zero (p h : ℕ) (x y : ZMod (p ^ h)) :
    residueLabel p h 0 x = residueLabel p h 0 y := by
  unfold residueLabel
  rw [pow_zero, Nat.mod_one, Nat.mod_one]

theorem residueLabel_top_injective (p h : ℕ) [NeZero (p ^ h)] :
    Function.Injective (residueLabel p h h) := by
  intro x y hxy
  unfold residueLabel at hxy
  rw [Nat.mod_eq_of_lt (ZMod.val_lt x), Nat.mod_eq_of_lt (ZMod.val_lt y)] at hxy
  exact ZMod.val_injective _ hxy

/-- The residue chain: `E_l` is the conditional expectation of a uniform residue modulo
`p^h` given its residue modulo `p^l` (`def:hyb:coupled`(e)). -/
noncomputable def Chain.residues (p h : ℕ) [NeZero (p ^ h)] : Chain (ZMod (p ^ h)) :=
  Chain.ofLabels h (residueLabel p h)
    (fun _ _ hll' _ x y hxy => residueLabel_nested p h hll' x y hxy)
    (residueLabel_zero p h) (residueLabel_top_injective p h)

theorem Chain.residues_cond (p h : ℕ) [NeZero (p ^ h)] (l : ℕ) :
    (Chain.residues p h).cond l = condExpMatrix (residueLabel p h l) := rfl

/-- The residue labels are translation invariant. -/
theorem residueLabel_add (p h : ℕ) [NeZero (p ^ h)] {l : ℕ} (hl : l ≤ h)
    (x y c : ZMod (p ^ h)) :
    residueLabel p h l (x + c) = residueLabel p h l (y + c) ↔
      residueLabel p h l x = residueLabel p h l y := by
  unfold residueLabel
  have hd : p ^ l ∣ p ^ h := Nat.pow_dvd_pow p hl
  rw [ZMod.val_add, ZMod.val_add, Nat.mod_mod_of_dvd _ hd, Nat.mod_mod_of_dvd _ hd]
  constructor
  · intro h'
    exact Nat.ModEq.add_right_cancel' c.val h'
  · intro h'
    exact Nat.ModEq.add_right c.val h'

end Residues

section Convolution

variable {G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

/-- The convolution transition `T f(s) = ∑_r μ(r) f(s + r)`. -/
def convMatrix (μ : G → ℝ) : Matrix G G ℝ := fun s s' => μ (s' - s)

omit [DecidableEq G] in
theorem convMatrix_mulVec (μ : G → ℝ) (f : G → ℝ) (s : G) :
    (convMatrix μ *ᵥ f) s = ∑ r, μ r * f (s + r) := by
  simp only [Matrix.mulVec, dotProduct, convMatrix]
  exact Fintype.sum_equiv (Equiv.subRight s) _ _ (fun s' => by simp)

omit [DecidableEq G] in
/-- The convolution with a probability law is doubly stochastic. -/
theorem convMatrix_doublyStochastic {μ : G → ℝ} (hμ : ∀ r, 0 ≤ μ r) (hμ1 : ∑ r, μ r = 1) :
    DoublyStochastic (convMatrix μ) where
  nonneg x y := hμ _
  row_sum x := by
    simp only [convMatrix]
    rw [← hμ1]
    exact Fintype.sum_equiv (Equiv.subRight x) _ _ (fun s' => rfl)
  col_sum y := by
    simp only [convMatrix]
    rw [← hμ1]
    exact Fintype.sum_equiv (Equiv.subLeft y) _ _ (fun s' => rfl)

omit [DecidableEq G] in
/-- A translation-invariant matrix commutes with every convolution. -/
theorem convMatrix_comm {A : Matrix G G ℝ} (hA : ∀ x y c, A (x + c) (y + c) = A x y)
    (μ : G → ℝ) : convMatrix μ * A = A * convMatrix μ := by
  ext s s''
  simp only [Matrix.mul_apply, convMatrix]
  refine Fintype.sum_equiv (Equiv.subLeft (s + s'')) _ _ (fun u => ?_)
  simp only [Equiv.subLeft_apply]
  have h1 : A u s'' = A s (s + s'' - u) := by
    have := hA s (s + s'' - u) (u - s)
    rw [show s + (u - s) = u by abel, show s + s'' - u + (u - s) = s'' by abel] at this
    exact this
  rw [h1, show s'' - (s + s'' - u) = u - s by abel]
  ring

omit [DecidableEq G] in
theorem condExpMatrix_translate {γ : Type*} [DecidableEq γ] {π : G → γ}
    (hπ : ∀ x y c, π (x + c) = π (y + c) ↔ π x = π y) (x y c : G) :
    condExpMatrix π (x + c) (y + c) = condExpMatrix π x y := by
  have hfib : (fibre π (x + c)).card = (fibre π x).card := by
    apply Finset.card_bij (fun z _ => z - c)
    · intro z hz
      simp only [fibre, mem_filter, mem_univ, true_and] at hz ⊢
      have := (hπ (z - c) x c).mp (by rw [sub_add_cancel]; exact hz)
      exact this
    · intro a _ b _ hab
      exact sub_left_injective hab
    · intro z hz
      refine ⟨z + c, ?_, by simp⟩
      simp only [fibre, mem_filter, mem_univ, true_and] at hz ⊢
      exact (hπ z x c).mpr hz
  simp only [condExpMatrix, hπ x y c, hfib]

omit [DecidableEq G] in
theorem meanMatrix_translate (x y c : G) : meanMatrix G (x + c) (y + c) = meanMatrix G x y :=
  rfl

omit [Fintype G] in
theorem one_translate (x y c : G) : (1 : Matrix G G ℝ) (x + c) (y + c) = (1 : Matrix G G ℝ) x y := by
  simp only [Matrix.one_apply, add_left_inj]

/-- A convolution transition maps every exact-depth space of a chain of translation-invariant
projections into itself; with a norm bound by `c` on that space it is `c`-bounded there. -/
theorem conv_rangeBound (C : Chain G)
    (hC : ∀ l, l ≤ C.depth → ∀ x y c, C.cond l (x + c) (y + c) = C.cond l x y)
    (μ : G → ℝ) {l : ℕ} (hl : l ≤ C.depth) {c : ℝ}
    (hnorm : ∀ f, C.diff l *ᵥ f = f →
      (convMatrix μ *ᵥ f) ⬝ᵥ (convMatrix μ *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f)) :
    RangeBound (C.diff l) (convMatrix μ) c := by
  have hcomm : convMatrix μ * C.diff l = C.diff l * convMatrix μ := by
    unfold Chain.diff
    split_ifs
    · exact convMatrix_comm (hC 0 (Nat.zero_le _)) μ
    · rw [Matrix.mul_sub, Matrix.sub_mul, convMatrix_comm (hC l hl) μ,
        convMatrix_comm (hC (l - 1) (by omega)) μ]
  have hPP : C.diff l * C.diff l = C.diff l := by
    rw [C.diff_mul_diff hl hl, ite_eq_left rfl]
  apply RangeBound.of_vec (C.transpose_diff hl) hPP
  · intro f hf
    rw [Matrix.mulVec_mulVec, ← hcomm, ← Matrix.mulVec_mulVec, hf]
  · exact hnorm

/-- The cyclic shift `f ↦ f(· + 1)` of the interval coordinate, as a convolution. -/
def shiftMatrix (one : G) : Matrix G G ℝ := convMatrix (fun r => if r = one then 1 else 0)

theorem shiftMatrix_mulVec (one : G) (f : G → ℝ) (s : G) :
    (shiftMatrix one *ᵥ f) s = f (s + one) := by
  rw [shiftMatrix, convMatrix_mulVec]
  simp [ite_mul]

theorem shiftMatrix_isometry (one : G) (f : G → ℝ) :
    (shiftMatrix one *ᵥ f) ⬝ᵥ (shiftMatrix one *ᵥ f) = f ⬝ᵥ f := by
  simp only [dotProduct, shiftMatrix_mulVec]
  exact Fintype.sum_equiv (Equiv.addRight one) _ _ (fun s => rfl)

theorem shiftMatrix_doublyStochastic (one : G) : DoublyStochastic (shiftMatrix one) :=
  convMatrix_doublyStochastic (fun r => by split <;> norm_num) (by simp)

/-- The interval coordinate: the cyclic shift preserves the constants and the functions of
mean zero, with tail one. -/
theorem shift_rangeBound [Nonempty G] (one : G) (l : Fin ((Chain.whole G).depth + 1)) :
    RangeBound ((Chain.whole G).diff l) (shiftMatrix one)
      ((Tails.bernoulli 1 zero_le_one le_rfl).tail l) :=
  (shiftMatrix_doublyStochastic one).rangeBound zero_le_one le_rfl
    (fun f _ => by rw [shiftMatrix_isometry, one_pow, one_mul]) l

theorem Chain.whole_translate [Nonempty G] (l : ℕ) (x y c : G) :
    (Chain.whole G).cond l (x + c) (y + c) = (Chain.whole G).cond l x y := by
  change (if l = 0 then meanMatrix G else 1) (x + c) (y + c) =
    (if l = 0 then meanMatrix G else 1) x y
  split_ifs
  · rfl
  · exact one_translate x y c

/-- The convolution with a probability law fixes the constants. -/
theorem conv_mul_cond_zero (C : Chain G) {μ : G → ℝ} (hμ : ∀ r, 0 ≤ μ r)
    (hμ1 : ∑ r, μ r = 1) : convMatrix μ * C.cond 0 = C.cond 0 := by
  rw [C.cond_zero]
  exact (convMatrix_doublyStochastic hμ hμ1).mul_mean

end Convolution

theorem Chain.residues_translate (p h : ℕ) [NeZero (p ^ h)] {l : ℕ}
    (hl : l ≤ (Chain.residues p h).depth) (x y c : ZMod (p ^ h)) :
    (Chain.residues p h).cond l (x + c) (y + c) = (Chain.residues p h).cond l x y := by
  rw [Chain.residues_cond]
  exact condExpMatrix_translate (fun x y c => residueLabel_add p h hl x y c) x y c

/-- The residue coordinates (`def:hyb:coupled`(c),(e) and (CP0)(d)): for any law `μ` of the
increments on `ℤ/p^hℤ`, the convolution transition maps every exact-conductor space
`ran(E_l - E_{l-1})` into itself and fixes the constants; with tails bounding its norm on
these spaces it satisfies the per-coordinate hypotheses of `signedIndexOp_sectorOperator`. -/
theorem residue_conv_hypotheses (p h : ℕ) [NeZero (p ^ h)] {μ : ZMod (p ^ h) → ℝ}
    (hμ : ∀ r, 0 ≤ μ r) (hμ1 : ∑ r, μ r = 1) (t : Tails (Chain.residues p h).depth)
    (hnorm : ∀ (l : Fin ((Chain.residues p h).depth + 1)) f,
      (Chain.residues p h).diff l *ᵥ f = f →
      (convMatrix μ *ᵥ f) ⬝ᵥ (convMatrix μ *ᵥ f) ≤ t.tail l ^ 2 * (f ⬝ᵥ f)) :
    (∀ l : Fin ((Chain.residues p h).depth + 1),
      RangeBound ((Chain.residues p h).diff l) (convMatrix μ) (t.tail l)) ∧
    convMatrix μ * (Chain.residues p h).cond 0 = (Chain.residues p h).cond 0 :=
  ⟨fun l => conv_rangeBound (Chain.residues p h)
      (fun _ hl x y c => Chain.residues_translate p h hl x y c) μ (by omega) (hnorm l),
    conv_mul_cond_zero (Chain.residues p h) hμ hμ1⟩


section Product

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  {γ : K → Type*} [∀ j, DecidableEq (γ j)]

/-- A tensor product of conditional expectations is the conditional expectation given the
product labeling. -/
theorem piKron_condExpMatrix (π : ∀ j, Ω j → γ j) :
    piKron (fun j => condExpMatrix (π j)) =
      condExpMatrix (fun ω : (∀ j, Ω j) => fun j => π j (ω j)) := by
  ext ω η
  have hfib : fibre (fun ω : (∀ j, Ω j) => fun j => π j (ω j)) ω =
      Fintype.piFinset (fun j => fibre (π j) (ω j)) := by
    ext ζ
    simp only [fibre, mem_filter, mem_univ, true_and, Fintype.mem_piFinset, funext_iff]
  simp only [piKron_apply, condExpMatrix, hfib, Fintype.card_piFinset, Nat.cast_prod]
  by_cases h : ∀ j, π j (ω j) = π j (η j)
  · rw [ite_eq_left (funext h), ← prod_inv_distrib]
    exact prod_congr rfl (fun j _ => by rw [ite_eq_left (h j)])
  · obtain ⟨j, hj⟩ := not_forall.mp h
    rw [ite_eq_right (fun h' => hj (congrFun h' j))]
    exact prod_eq_zero (mem_univ j) (by rw [ite_eq_right hj])

/-- For chains of conditional expectations given labelings, the revealed projection at the
depth vector `𝒥` is the conditional expectation given the revealed labels
`(π_{j,𝒥_j}(ω_j))_j` (for the residue coordinates: given `s_j mod p^{𝒥_j}`). -/
theorem depthReveal_ofLabels [∀ j, DecidableEq (Ω j)] {γ' : Type*} [DecidableEq γ']
    (h : K → ℕ) (π : ∀ j, ℕ → Ω j → γ')
    (hnest : ∀ j l l', l ≤ l' → l' ≤ h j → ∀ x y, π j l' x = π j l' y → π j l x = π j l y)
    (h0 : ∀ j x y, π j 0 x = π j 0 y) (htop : ∀ j, Function.Injective (π j (h j)))
    {ι : Type*} (J : ∀ j, Fin ((Chain.ofLabels (h j) (π j) (hnest j) (h0 j) (htop j)).depth + 1))
    (Z : (∀ j, Ω j) → ι → ℝ) :
    depthReveal (fun j => Chain.ofLabels (h j) (π j) (hnest j) (h0 j) (htop j)) J Z =
      act (condExpMatrix (fun ω : (∀ j, Ω j) => fun j => π j (J j) (ω j))) Z := by
  unfold depthReveal
  rw [← piKron_condExpMatrix (fun j => π j (J j))]
  rfl

end Product

section WholeCoordinate

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)] [∀ j, Nonempty (Ω j)]

theorem Chain.whole_cond_eq_condExp {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    (l : ℕ) :
    (Chain.whole G).cond l = condExpMatrix (fun x : G => if l = 0 then none else some x) := by
  by_cases hl : l = 0
  · subst hl
    rw [condExpMatrix_const (fun x y => by simp)]
    rfl
  · rw [condExpMatrix_injective (fun x y hxy => by simpa [hl] using hxy)]
    change (if l = 0 then meanMatrix G else 1) = 1
    rw [ite_eq_right hl]

/-- Whole-coordinate case: `Z^𝒥 = E[Z | ω_𝒥]`, the conditional expectation given the
coordinates `j` with `𝒥_j = 1`. -/
theorem depthReveal_whole {ι : Type*} (J : ∀ j, Fin ((wholeChains Ω j).depth + 1))
    (Z : (∀ j, Ω j) → ι → ℝ) :
    depthReveal (wholeChains Ω) J Z =
      act (condExpMatrix (fun ω : (∀ j, Ω j) =>
        fun j => if (J j : ℕ) = 0 then none else some (ω j))) Z := by
  unfold depthReveal
  rw [← piKron_condExpMatrix (fun j (x : Ω j) => if (J j : ℕ) = 0 then none else some x)]
  congr 1
  congr 1
  funext j
  exact Chain.whole_cond_eq_condExp (J j : ℕ)

end WholeCoordinate

end Sarkozy.IndexSupport

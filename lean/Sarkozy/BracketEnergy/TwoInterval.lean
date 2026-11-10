module

public import Sarkozy.BracketEnergy.Bundles
public import Sarkozy.IndexSupport.CRT
public import Sarkozy.Functional.IndexAverages

@[expose] public section

/-!
# `lem:twointerval`(ii) for the revealed inputs of the envelope energies

The proof of `lem:envelope-energy` begins: "Fix `𝒥` and the intervals. The revealed depths
determine `s_e` modulo `D_{𝒥_e} = ∏_p p^{𝒥_{e,p}}`, a divisor of `M₀`. By `lem:twointerval` …
`X^𝒥` carries `g^{I_{b_e}, D_{𝒥_e}, s_e mod D_{𝒥_e}}` at `u_e`." This file proves that step for
the formal revealed slot functions (WP-S's `revealedSlot`, the slot functions of B5's
`FixedIntervalInputsCRT`):

* `revealedSlot_eq_fibre`: the revealed slot function at the depth vector `𝒥` is the average of
  the slot function over the fibre of the index `(b, s) ∈ ℤ/Kℤ × ℤ/M₀ℤ` given the revealed labels
  `(b if revealed, s mod D_𝒥)` (from `unsplitRevelation_reveal_mod`'s labels);
* `fibre_revLabel_eq`, `average_snd_fibre`: the fibre is a product, and the average of a function
  of `s` alone is the average over the residue fibre `{s' ≡ s (mod D_𝒥)}`;
* **`revealedSlot_wrapInputCRT`** (`lem:twointerval`(ii), `cor:index-support-frame`(ii)): for
  the wrapped inputs at the fixed interval `t`, the revealed slot function at a query `e ∈ 𝒮` is
  `g^{I_t, D_{𝒥_e}, s mod D_{𝒥_e}}` (`revealedResidue`), and `F_A` at the other queries.
-/

open Finset Function Complex
open scoped BigOperators Matrix

namespace Sarkozy.BracketEnergy

open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.FourierArithmetic

variable {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- `D_𝒥 ∣ M₀`. -/
theorem revealedModulus_dvd (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1)) :
    revealedModulus blockScale pr h J ∣ modulus pr h := by
  unfold revealedModulus modulus
  apply Finset.prod_dvd_prod_of_dvd
  intro q _
  apply Nat.pow_dvd_pow
  have := (J (some q)).isLt
  change (J (some q) : ℕ) < h q + 1 at this
  omega

/-- The revealed residue `s mod D_𝒥` of the index `η` (`s` its CRT residue in `ℤ/M₀ℤ`). -/
noncomputable def revealedResidue (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (η : ∀ j, CoordSpace blockScale pr h j) : ZMod (revealedModulus blockScale pr h J) :=
  ZMod.castHom (revealedModulus_dvd J) (ZMod (revealedModulus blockScale pr h J))
    ((crtEquiv blockScale pr h hcop).symm η).2

/-- The revealed labels of the unsplit index: the interval label and `s mod D_𝒥`. -/
noncomputable def revLabel (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (x : ZMod blockScale × ZMod (modulus pr h)) : ℕ × ℕ :=
  (coordLabel blockScale pr h none (J none) x.1, x.2.val % revealedModulus blockScale pr h J)

/-- The revealed labels have the fibres of the CRT coordinate labels (the iff of
`unsplitRevelation_reveal_mod`). -/
theorem revLabel_iff (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (x y : ZMod blockScale × ZMod (modulus pr h)) :
    (fun j => coordLabel blockScale pr h j (J j) (crtEquiv blockScale pr h hcop x j)) =
        (fun j => coordLabel blockScale pr h j (J j) (crtEquiv blockScale pr h hcop y j)) ↔
      revLabel J x = revLabel J y := by
  have hJ (q : P) : (J (some q) : ℕ) ≤ h q := by
    have := (J (some q)).isLt
    change (J (some q) : ℕ) < h q + 1 at this
    omega
  have hcopJ : ∀ q ∈ (Finset.univ : Finset P), ∀ q' ∈ (Finset.univ : Finset P), q ≠ q' →
      Nat.Coprime (pr q ^ (J (some q) : ℕ)) (pr q' ^ (J (some q') : ℕ)) := by
    intro q _ q' _ hqq
    exact ((hcop hqq).coprime_dvd_left (Nat.pow_dvd_pow _ (hJ q))).coprime_dvd_right
      (Nat.pow_dvd_pow _ (hJ q'))
  unfold revLabel
  constructor
  · intro hxy
    refine Prod.ext (congrFun hxy none) ?_
    change x.2.val ≡ y.2.val [MOD revealedModulus blockScale pr h J]
    rw [revealedModulus, modEq_prod_iff _ _ hcopJ]
    intro q _
    have h1 := congrFun hxy (some q)
    change residueLabel (pr q) (h q) (J (some q)) (crtResidues pr h hcop x.2 q) =
      residueLabel (pr q) (h q) (J (some q)) (crtResidues pr h hcop y.2 q) at h1
    unfold residueLabel at h1
    rw [crtResidues_val_mod pr h hcop _ q (hJ q), crtResidues_val_mod pr h hcop _ q (hJ q)] at h1
    exact h1
  · intro hxy
    have h1 : coordLabel blockScale pr h none (J none) x.1 =
        coordLabel blockScale pr h none (J none) y.1 := congrArg Prod.fst hxy
    have h2 : x.2.val ≡ y.2.val [MOD revealedModulus blockScale pr h J] := congrArg Prod.snd hxy
    rw [revealedModulus, modEq_prod_iff _ _ hcopJ] at h2
    funext j
    match j with
    | none => exact h1
    | some q =>
      change residueLabel (pr q) (h q) (J (some q)) (crtResidues pr h hcop x.2 q) =
        residueLabel (pr q) (h q) (J (some q)) (crtResidues pr h hcop y.2 q)
      unfold residueLabel
      rw [crtResidues_val_mod pr h hcop _ q (hJ q), crtResidues_val_mod pr h hcop _ q (hJ q)]
      exact h2 q (Finset.mem_univ q)

variable {E : Type} [Fintype E] [DecidableEq E]

omit [Fintype E] [DecidableEq E] in
/-- **The revealed slot function is a fibre average** (`cor:index-support-frame`(ii)): at the
depth vector `𝒥`, `revealedSlot 𝒥 φ e η` is the average of `φ e` over the indices whose revealed
labels (`b` if revealed, `s mod D_{𝒥_e}`) are those of `η`. -/
theorem revealedSlot_eq_fibre (Jq : ∀ (_e : E) (j : Option P),
      Fin ((coordChain blockScale pr h j).depth + 1)) {Lb : Type}
    (φ : E → (∀ j : Option P, CoordSpace blockScale pr h j) → Lb → ℝ) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (x : Lb) :
    revealedSlot Jq φ e η x =
      ((fibre (revLabel (Jq e)) ((crtEquiv blockScale pr h hcop).symm η)).card : ℝ)⁻¹ *
        ∑ y ∈ fibre (revLabel (Jq e)) ((crtEquiv blockScale pr h hcop).symm η),
          φ e (crtEquiv blockScale pr h hcop y) x := by
  set σ := crtEquiv blockScale pr h hcop
  have h1 : piKron (fun j => (coordChain blockScale pr h j).cond (Jq e j)) =
      condExpMatrix (fun ω : (∀ j, CoordSpace blockScale pr h j) =>
        fun j => coordLabel blockScale pr h j (Jq e j) (ω j)) := by
    rw [← piKron_condExpMatrix (fun j => coordLabel blockScale pr h j (Jq e j))]
    congr 1
    funext j
    exact coordChain_cond_eq blockScale pr h j (by have := (Jq e j).isLt; omega)
  unfold revealedSlot
  rw [h1]
  set M := condExpMatrix (fun ω : (∀ j, CoordSpace blockScale pr h j) =>
    fun j => coordLabel blockScale pr h j (Jq e j) (ω j))
  set f : (∀ j, CoordSpace blockScale pr h j) → ℝ := fun η' => φ e η' x
  have h2 : (M *ᵥ f) η = ((M.submatrix σ σ) *ᵥ (f ∘ σ)) (σ.symm η) := by
    rw [Matrix.submatrix_mulVec_equiv]
    simp only [Function.comp_apply, Equiv.apply_symm_apply]
    rw [Function.comp_assoc, Equiv.self_comp_symm, Function.comp_id]
  rw [h2, condExpMatrix_submatrix]
  have h3 : condExpMatrix ((fun ω : (∀ j, CoordSpace blockScale pr h j) =>
      fun j => coordLabel blockScale pr h j (Jq e j) (ω j)) ∘ σ) =
      condExpMatrix (revLabel (Jq e)) :=
    condExpMatrix_congr fun x y => revLabel_iff hcop (Jq e) x y
  rw [h3, condExpMatrix_mulVec]
  rfl

omit [DecidableEq P] in
/-- The fibre of the revealed labels is a product. -/
theorem fibre_revLabel_eq (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (x : ZMod blockScale × ZMod (modulus pr h)) :
    fibre (revLabel J) x = fibre (coordLabel blockScale pr h none (J none)) x.1 ×ˢ
      fibre (fun s : ZMod (modulus pr h) => s.val % revealedModulus blockScale pr h J) x.2 := by
  ext y
  simp only [fibre, revLabel, mem_filter, mem_univ, true_and, mem_product, Prod.mk.injEq]

/-- The average over a product fibre of a function of the second coordinate. -/
theorem average_snd_product {X Y : Type*} (F1 : Finset X) (F2 : Finset Y) (hF1 : F1.Nonempty)
    (G : Y → ℝ) :
    ((F1 ×ˢ F2).card : ℝ)⁻¹ * ∑ y ∈ F1 ×ˢ F2, G y.2 = (F2.card : ℝ)⁻¹ * ∑ s ∈ F2, G s := by
  have h1 : (F1.card : ℝ) ≠ 0 := by exact_mod_cast hF1.card_pos.ne'
  rw [card_product, sum_product]
  simp only [sum_const, nsmul_eq_mul, Nat.cast_mul]
  calc ((F1.card : ℝ) * F2.card)⁻¹ * (F1.card * ∑ s ∈ F2, G s)
      = ((F1.card : ℝ)⁻¹ * F1.card) * ((F2.card : ℝ)⁻¹ * ∑ s ∈ F2, G s) := by
        rw [mul_inv]; ring
    _ = (F2.card : ℝ)⁻¹ * ∑ s ∈ F2, G s := by rw [inv_mul_cancel₀ h1, one_mul]

omit [DecidableEq P] in
/-- The residue fibre of `s mod D_𝒥` is `residueFibre`. -/
theorem fibre_mod_eq_residueFibre (J : ∀ j, Fin ((coordChain blockScale pr h j).depth + 1))
    (s : ZMod (modulus pr h)) :
    fibre (fun s : ZMod (modulus pr h) => s.val % revealedModulus blockScale pr h J) s =
      residueFibre (revealedModulus_dvd J)
        (ZMod.castHom (revealedModulus_dvd J) (ZMod (revealedModulus blockScale pr h J)) s) := by
  ext s'
  simp only [fibre, residueFibre, mem_filter, mem_univ, true_and, ZMod.castHom_apply,
    ZMod.cast_eq_val]
  rw [ZMod.natCast_eq_natCast_iff']

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

omit [∀ q, NeZero (pr q ^ h q)] [Fintype E] [DecidableEq J₀] in
/-- The wrapped input at an index: `g^{I_t, M₀, s}` for `e ∈ 𝒮` (`s` the CRT residue). -/
theorem wrapInputCRT_crtEquiv (L : ℕ) (A : Finset ℤ) (S : Finset E) (t : ZMod blockScale)
    (e : E) (he : e ∈ S) (x : ZMod blockScale × ZMod (modulus pr h))
    (y : ResidueSpace (crtModuli m₀ blk p L)) :
    wrapInputCRT blk hcop L A S t e (crtEquiv blockScale pr h hcop x) y =
      (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) (blockInterval blockScale L t)
        (modulus pr h) x.2 A y).re := by
  unfold wrapInputCRT
  simp only [he, ↓reduceIte]
  have hx : (crtEquiv blockScale pr h hcop).symm
      (Function.update (crtEquiv blockScale pr h hcop x) none
        (t : CoordSpace blockScale pr h none)) =
      (t, x.2) := by
    rw [Equiv.symm_apply_eq]
    funext j
    match j with
    | none => rfl
    | some q => rfl
  rw [hx]
  rfl

omit [Fintype E] [DecidableEq J₀] in
/-- **`lem:twointerval`(ii) for the wrapped revealed inputs** (`lem:envelope-energy`, proof;
`cor:index-support-frame`(ii)): at the depth vector `𝒥`, the revealed slot function of the
wrapped inputs at the interval `t` is `g^{I_t, D_{𝒥_e}, s mod D_{𝒥_e}}` at a query `e ∈ 𝒮`
(`s` the CRT residue of the index), and `F_A` at the other queries. -/
theorem revealedSlot_wrapInputCRT (L : ℕ) (A : Finset ℤ) (S : Finset E) (t : ZMod blockScale)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    revealedSlot Jq (wrapInputCRT blk hcop L A S t) e η y =
      if e ∈ S then
        (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
          (blockInterval blockScale L t) (revealedModulus blockScale pr h (Jq e))
          (revealedResidue hcop (Jq e) η) A y).re
      else unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L y := by
  rw [revealedSlot_eq_fibre hcop]
  set x0 := (crtEquiv blockScale pr h hcop).symm η
  split_ifs with he
  · have hsum : ∀ y' ∈ fibre (revLabel (Jq e)) x0,
        wrapInputCRT blk hcop L A S t e (crtEquiv blockScale pr h hcop y') y =
          (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
            (blockInterval blockScale L t) (modulus pr h) y'.2 A y).re :=
      fun y' _ => wrapInputCRT_crtEquiv hcop blk L A S t e he y' y
    rw [sum_congr rfl hsum, fibre_revLabel_eq,
      average_snd_product _ _ ⟨x0.1, mem_fibre_self _ _⟩
        (fun s => (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
          (blockInterval blockScale L t) (modulus pr h) s A y).re),
      fibre_mod_eq_residueFibre]
    have hfa := congrArg Complex.re (fibreAverage_input (crtModuli m₀ blk p L)
      (paperCutoff (blockScale * L)) (blockInterval blockScale L t) (revealedModulus_dvd (Jq e))
      (ZMod.castHom (revealedModulus_dvd (Jq e)) (ZMod (revealedModulus blockScale pr h (Jq e)))
        x0.2) A y)
    have hre : ∀ (n : ℕ) (w : ℂ), ((n : ℂ)⁻¹ * w).re = (n : ℝ)⁻¹ * w.re := by
      intro n w
      rw [show ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
    rw [hre, Complex.re_sum] at hfa
    exact hfa
  · have hc : ∀ y' ∈ fibre (revLabel (Jq e)) x0,
        wrapInputCRT blk hcop L A S t e (crtEquiv blockScale pr h hcop y') y =
          unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L y := by
      intro y' _
      unfold wrapInputCRT
      simp only [he, ↓reduceIte]
    rw [sum_congr rfl hc, sum_const, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (fibre_card_pos _ _).ne', one_mul]

/-- The average over a product fibre. -/
theorem average_product {X Y : Type*} (F1 : Finset X) (F2 : Finset Y) (G : X → Y → ℝ) :
    ((F1 ×ˢ F2).card : ℝ)⁻¹ * ∑ y ∈ F1 ×ˢ F2, G y.1 y.2 =
      (F1.card : ℝ)⁻¹ * ∑ b ∈ F1, ((F2.card : ℝ)⁻¹ * ∑ s ∈ F2, G b s) := by
  rw [card_product, sum_product, Nat.cast_mul, mul_inv, ← mul_sum, mul_assoc]

omit [Fintype P] [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- The interval fibre at depth `0` is everything. -/
theorem fibre_coordLabel_zero (b : ZMod blockScale) :
    fibre (coordLabel blockScale pr h none 0) b = univ := by
  ext b'
  simp [fibre, coordLabel]

omit [Fintype P] [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- The interval fibre at a positive depth is the point. -/
theorem fibre_coordLabel_pos {l : ℕ} (hl : l ≠ 0) (b : ZMod blockScale) :
    fibre (coordLabel blockScale pr h none l) b = {b} := by
  ext b'
  simp only [fibre, coordLabel, mem_filter, mem_univ, true_and, mem_singleton, hl, ↓reduceIte,
    add_left_inj]
  exact ⟨fun h' => ZMod.val_injective _ h', fun h' => by rw [h']⟩

/-- The revealed input of `envC` at a query: `g^{I_b, D_𝒥, s mod D_𝒥}` when the interval
coordinate `b` is revealed, and its average over `b` (`= g^{[N], D_𝒥, s mod D_𝒥}`, by
`lem:twointerval`(i), `average_blocks_input`) when it is not. -/
noncomputable def revealedEnvInput (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    ℝ :=
  if (Jq e none : ℕ) = 0 then
    (blockScale : ℝ)⁻¹ * ∑ b : ZMod blockScale,
      (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) (blockInterval blockScale L b)
        (revealedModulus blockScale pr h (Jq e)) (revealedResidue hcop (Jq e) η) A y).re
  else
    (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
      (blockInterval blockScale L (η none)) (revealedModulus blockScale pr h (Jq e))
      (revealedResidue hcop (Jq e) η) A y).re

omit [Fintype E] [DecidableEq E] [DecidableEq J₀] in
/-- The revealed slot functions of the indexed inputs `g^{I_b, M₀, s}`: `revealedEnvInput`. -/
theorem revealedSlot_indexedInput (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    revealedSlot Jq (fun _ η' y =>
      indexedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) blockScale L
        (modulus pr h) A ((crtEquiv blockScale pr h hcop).symm η') y) e η y =
      revealedEnvInput hcop blk L A Jq e η y := by
  rw [revealedSlot_eq_fibre hcop]
  set x0 := (crtEquiv blockScale pr h hcop).symm η
  have hsum : ∀ y' ∈ fibre (revLabel (Jq e)) x0,
      indexedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) blockScale L
        (modulus pr h) A ((crtEquiv blockScale pr h hcop).symm (crtEquiv blockScale pr h hcop y'))
        y =
      (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
        (blockInterval blockScale L y'.1) (modulus pr h) y'.2 A y).re := by
    intro y' _
    rw [Equiv.symm_apply_apply]
    rfl
  rw [sum_congr rfl hsum, fibre_revLabel_eq,
    average_product _ _ (fun b s => (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
      (blockInterval blockScale L b) (modulus pr h) s A y).re), fibre_mod_eq_residueFibre]
  have hre : ∀ (n : ℕ) (w : ℂ), ((n : ℂ)⁻¹ * w).re = (n : ℝ)⁻¹ * w.re := by
    intro n w
    rw [show ((n : ℂ))⁻¹ = (((n : ℝ)⁻¹ : ℝ) : ℂ) by push_cast; rfl, Complex.re_ofReal_mul]
  have hfa : ∀ b : ZMod blockScale,
      (((residueFibre (revealedModulus_dvd (Jq e)) (ZMod.castHom (revealedModulus_dvd (Jq e))
          (ZMod (revealedModulus blockScale pr h (Jq e))) x0.2)).card : ℝ))⁻¹ *
        ∑ s ∈ residueFibre (revealedModulus_dvd (Jq e)) (ZMod.castHom (revealedModulus_dvd (Jq e))
          (ZMod (revealedModulus blockScale pr h (Jq e))) x0.2),
          (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
            (blockInterval blockScale L b) (modulus pr h) s A y).re =
        (input (crtModuli m₀ blk p L) (paperCutoff (blockScale * L))
          (blockInterval blockScale L b) (revealedModulus blockScale pr h (Jq e))
          (revealedResidue hcop (Jq e) η) A y).re := by
    intro b
    have h := congrArg Complex.re (fibreAverage_input (crtModuli m₀ blk p L)
      (paperCutoff (blockScale * L)) (blockInterval blockScale L b) (revealedModulus_dvd (Jq e))
      (ZMod.castHom (revealedModulus_dvd (Jq e)) (ZMod (revealedModulus blockScale pr h (Jq e)))
        x0.2) A y)
    rw [hre, Complex.re_sum] at h
    exact h
  rw [sum_congr rfl fun b _ => hfa b]
  unfold revealedEnvInput
  split_ifs with hJ
  · have hl : (coordLabel blockScale pr h none (Jq e none)) =
        coordLabel blockScale pr h none 0 := by rw [hJ]
    rw [hl, fibre_coordLabel_zero, card_univ, ZMod.card]
  · rw [fibre_coordLabel_pos hJ, card_singleton, sum_singleton, Nat.cast_one, inv_one, one_mul]
    rfl

/-- **`lem:twointerval`(ii) for the revealed inputs of `envC`** (`lem:envelope-energy`, proof;
`cor:index-support-frame`(ii)): `revealedInputCRT` at the depth vector `𝒥` and the index `η` is
`g^{I_b, D_{𝒥_e}, s mod D_{𝒥_e}}` (`revealedEnvInput`; averaged over `b` if the interval is not
revealed). The chains of `D.index` are the coordinate chains by definition
(`paperCoupledIndex`). -/
theorem revealedInputCRT_eq {a : ℝ} (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) (e : E)
    (η : ∀ j : Option P, CoordSpace blockScale pr h j) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    revealedInputCRT blk hcop D L A Jq e η y = revealedEnvInput hcop blk L A Jq e η y :=
  revealedSlot_indexedInput hcop blk L A Jq e η y

end Sarkozy.BracketEnergy

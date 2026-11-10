module

public import Sarkozy.EnvelopeEnergiesPaper.CRTLift
public import Sarkozy.BlockFrame.Atoms
public import Sarkozy.Structured.EnvelopeE1
public import Sarkozy.RecordExpansion.Multilinear

@[expose] public section

/-!
# The block atoms as cyclic coordinates (CRT transport)

The paper's prefix atoms are blocks `β` of fixed coordinates, with alphabet
`BlockRes β = ∏_{blk i = β} ℤ/m₀ᵢℤ` and joint laws on it (`def:record:exact-blocks`,
`def:record:upper-bands`, `def:cp0`(b)). The formal density-structured chain (WP-R's `Structured`,
`DensityDC`; I1's `abs_tensor_energy_le_unchanged_atoms`) runs on coordinates with cyclic
alphabets `ℤ/m_b` and pairwise coprime moduli. G1 found that the bridge from WP-FI's atoms asks
the prefix factor to be a product over the prefix coordinates, which fails for the middle and
upper blocks. This file removes that hypothesis by the Chinese remainder theorem: when the moduli
are pairwise coprime, `BlockRes β ≅ ℤ/D_β` with `D_β = ∏_{blk i = β} m₀ᵢ` (`ZMod.prodEquivPi`),
so the block atoms *are* cyclic coordinates, with moduli `crtModuli = (D_β)_β ⊔ (p_j)_j`.

* `crtModuli_pairwise`, `prod_crtModuli`: the CRT moduli are pairwise coprime and have the same
  product as the joined moduli of `G_N`;
* `crtLabelEquiv`: the cyclic labels `∏_b ℤ/crtModuli_b ≃ ∏_b BlockLabel_b`;
* **`blockLift_crtLabel`**: the paper's lift `F_A` on the block labels is the unchanged input
  `unchangedInput crtModuli` of the cyclic coordinates (by `CRTLift.lift_comp_eq`);
* `pullLaw`, `lawDensity_pullLaw`, `tensorLaw_pullLaw`: laws read through the alphabet
  equivalences;
* **`diagonalIntegral_blockLift_eq_crt`**, `multilinearIntegral_crt`: every energy on the block
  atoms is the energy of the pulled laws on the cyclic coordinates, *for every block law* (no
  product hypothesis);
* `sum_abs_lawDensity_pullLaw`: the total variations agree.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame Sarkozy.BlockFrame
  Sarkozy.Structured

/-! ## Laws read through alphabet equivalences -/

section Pull

variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

/-- The functional `Λ` on `Slot → X` read on `Slot → X'` through `e : X' ≃ X`:
`(pullLaw e Λ) g = Λ (g ∘ e⁻¹)`. -/
noncomputable def pullLaw (e : X' ≃ X) (Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) :
    ((Slot → X') → ℝ) →ₗ[ℝ] ℝ :=
  Λ ∘ₗ LinearMap.funLeft ℝ ℝ (fun x v => e.symm (x v))

omit [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] in
theorem pullLaw_apply (e : X' ≃ X) (Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (g : (Slot → X') → ℝ) :
    pullLaw e Λ g = Λ (fun x => g (fun v => e.symm (x v))) := rfl

omit [Fintype X] [Fintype X'] in
/-- The density of the pulled law: `(pullLaw e Λ)({y}) = Λ({e ∘ y})`. -/
theorem lawDensity_pullLaw (e : X' ≃ X) (Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) (y : Slot → X') :
    lawDensity (pullLaw e Λ) y = lawDensity Λ (fun v => e (y v)) := by
  unfold lawDensity
  rw [pullLaw_apply]
  congr 1
  funext x
  have hiff : (fun v => e.symm (x v)) = y ↔ x = fun v => e (y v) := by
    constructor
    · rintro rfl
      funext v
      simp
    · rintro rfl
      funext v
      simp
  exact if_congr hiff rfl rfl

/-- The total variations of `Λ` and of the pulled law agree. -/
theorem sum_abs_lawDensity_pullLaw (e : X' ≃ X) (Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) :
    ∑ y : Slot → X', |lawDensity (pullLaw e Λ) y| = ∑ x : Slot → X, |lawDensity Λ x| := by
  simp only [lawDensity_pullLaw]
  exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl Slot) e) _ _ fun y => rfl

omit [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] in
/-- Pulling back along `e` and then along `e.symm` gives the law back. -/
theorem pullLaw_symm_pullLaw (e : X' ≃ X) (Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) :
    pullLaw e.symm (pullLaw e Λ) = Λ := by
  apply LinearMap.ext
  intro g
  rw [pullLaw_apply, pullLaw_apply]
  congr 1
  funext x
  congr 1
  funext v
  simp

end Pull

section Tensor

variable {B : Type*} [Fintype B] [DecidableEq B] {X X' : B → Type*} [∀ b, Fintype (X b)]
  [∀ b, DecidableEq (X b)] [∀ b, Fintype (X' b)] [∀ b, DecidableEq (X' b)]

/-- **A tensor law read through alphabet equivalences** is the tensor law of the pulled factors:
`(⊗_b pullLaw e_b Λ_b) G = (⊗_b Λ_b)(G ∘ e⁻¹)`. -/
theorem tensorLaw_pullLaw (e : ∀ b, X' b ≃ X b) (Λ : ∀ b, ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ)
    (G : (Slot → ∀ b, X' b) → ℝ) :
    tensorLaw (fun b => pullLaw (e b) (Λ b)) G =
      tensorLaw Λ (fun x => G (fun v b => (e b).symm (x v b))) := by
  rw [RecordExpansion.tensorLaw_apply, RecordExpansion.tensorLaw_apply]
  simp only [lawDensity_pullLaw]
  refine Fintype.sum_equiv (Equiv.piCongrRight fun b => Equiv.arrowCongr (Equiv.refl Slot) (e b))
    _ _ fun z => ?_
  congr 1
  congr 1
  funext v b
  simp [Equiv.piCongrRight, Equiv.arrowCongr]

end Tensor

/-! ## The CRT moduli of the block atoms -/

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The order `D_β = ∏_{blk i = β} m₀ᵢ` of the block alphabet. -/
abbrev blockModulus (β : Bk) : ℕ := ∏ i, blockModuli m₀ blk β i

instance blockModulus_neZero (β : Bk) : NeZero (blockModulus m₀ blk β) :=
  ⟨Finset.prod_ne_zero_iff.mpr fun i _ => NeZero.ne (m₀ i.1)⟩

/-- The cyclic moduli of the block atoms: `D_β` at a block, `p_j` at a tail prime. -/
abbrev crtModuli (L : ℕ) : BlockAtom Bk J L → ℕ := Sum.elim (blockModulus m₀ blk) (p L)

instance crtModuli_neZero (L : ℕ) : ∀ b, NeZero (crtModuli m₀ blk p L b)
  | .inl β => blockModulus_neZero m₀ blk β
  | .inr j => inferInstanceAs (NeZero (p L j))

variable {m₀ p}

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
/-- The prefix moduli are pairwise coprime if the joined moduli are. -/
theorem prefix_pairwise {L : ℕ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)) :
    Pairwise fun i j => (m₀ i).Coprime (m₀ j) :=
  fun _ _ hij => hpair (fun h => hij (Sum.inl_injective h))

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [Fintype Bk] [DecidableEq Bk] in
/-- The moduli of one block are pairwise coprime. -/
theorem blockModuli_pairwise (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (β : Bk) :
    Pairwise (Nat.Coprime on blockModuli m₀ blk β) :=
  fun _ _ hij => h0 (fun h => hij (Subtype.ext h))

omit [DecidableEq J₀] [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [∀ i, NeZero (m₀ i)]
  [Fintype Bk] [∀ L j, NeZero (p L j)] in
/-- **The CRT moduli are pairwise coprime.** -/
theorem crtModuli_pairwise {L : ℕ}
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)) :
    Pairwise fun b b' => (crtModuli m₀ blk p L b).Coprime (crtModuli m₀ blk p L b') := by
  have h0 := prefix_pairwise hpair
  rintro (β | j) (β' | j') hne
  · have hβ : β ≠ β' := fun h => hne (h ▸ rfl)
    refine Nat.Coprime.prod_left fun i _ => Nat.Coprime.prod_right fun i' _ => h0 ?_
    intro h
    apply hβ
    rw [← i.2, ← i'.2, h]
  · exact Nat.Coprime.prod_left fun i _ => hpair (i := Sum.inl i.1) (j := Sum.inr j')
      (by simp)
  · exact Nat.Coprime.prod_right fun i _ => hpair (i := Sum.inr j) (j := Sum.inl i.1)
      (by simp)
  · exact hpair (i := Sum.inr j) (j := Sum.inr j') (fun h => hne (by rw [Sum.inr_injective h]))

omit [DecidableEq J₀] [∀ L, DecidableEq (J L)] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
/-- The CRT moduli have the product of the joined moduli: `∏_β D_β ∏_j p_j = ∏_i m₀ᵢ ∏_j p_j`. -/
theorem prod_crtModuli (L : ℕ) :
    ∏ b, crtModuli m₀ blk p L b = ∏ k, joinModuli m₀ (p L) k := by
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  congr 1
  exact Fintype.prod_fiberwise blk m₀

/-! ## The labels -/

/-- The CRT isomorphism of an atom: `ℤ/D_β ≃ BlockRes β` at a block, the identity at a tail
prime. -/
noncomputable def crtAtomEquiv (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ) :
    ∀ b : BlockAtom Bk J L, ZMod (crtModuli m₀ blk p L b) ≃ BlockLabel m₀ blk p L b
  | .inl β => (ZMod.prodEquivPi (blockModuli m₀ blk β) (blockModuli_pairwise blk h0 β)).toEquiv
  | .inr _ => Equiv.refl _

/-- The cyclic labels of the block atoms are the block labels. -/
noncomputable def crtLabelEquiv (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ) :
    ResidueSpace (crtModuli m₀ blk p L) ≃ (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b) :=
  Equiv.piCongrRight (crtAtomEquiv blk h0 L)

omit [DecidableEq J₀] [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [∀ i, NeZero (m₀ i)]
  [Fintype Bk] [∀ L j, NeZero (p L j)] in
/-- The CRT labels send the residue of an integer to the residue of the same integer. -/
theorem blockGroupEquiv_crtLabel_integerResidue
    (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ) (k : ℤ) :
    blockGroupEquiv m₀ blk p L (crtLabelEquiv blk h0 L (integerResidue (crtModuli m₀ blk p L) k)) =
      integerResidue (joinModuli m₀ (p L)) k := by
  funext c
  rcases c with i | j
  · change (ZMod.prodEquivPi (blockModuli m₀ blk (blk i)) (blockModuli_pairwise blk h0 (blk i))
        ((k : ZMod (blockModulus m₀ blk (blk i))))) ⟨i, rfl⟩ = (k : ZMod (m₀ i))
    rw [ZMod.prodEquivPi_apply, map_intCast]
  · rfl

/-- **The paper's lift on the block labels is the unchanged input of the cyclic coordinates**:
`F_A(crt y) = unchangedInput crtModuli … y` (`def:record:functional`(e), by
`CRTLift.lift_comp_eq`). -/
theorem blockLift_crtLabel (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ) (y : ResidueSpace (crtModuli m₀ blk p L)) :
    blockLift m₀ blk p L A (crtLabelEquiv blk (prefix_pairwise hpair) L y) =
      unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L y := by
  rw [blockLift_eq]
  unfold unchangedInput
  congr 1
  unfold wholeLift input
  have h := lift_comp_eq (joinModuli m₀ (p L)) (crtModuli m₀ blk p L) hpair
    (crtModuli_pairwise blk hpair) (prod_crtModuli blk L).symm
    (fun y => blockGroupEquiv m₀ blk p L (crtLabelEquiv blk (prefix_pairwise hpair) L y))
    (blockGroupEquiv_crtLabel_integerResidue blk (prefix_pairwise hpair) L)
    (paperCutoff (blockScale * L)) (Icc 1 ((blockScale * L : ℕ) : ℤ))
  rw [show indicator A = inputFun 1 0 A from ?_]
  · exact h (inputFun 1 0 A) y
  · funext n
    unfold indicator inputFun
    have : ((n : ZMod 1) = 0) := Subsingleton.elim _ _
    simp [this]

/-! ## Energies on the block atoms are energies on the cyclic coordinates -/

/-- The block-atom laws read on the cyclic coordinates: `Λ_β` through `ℤ/D_β ≃ BlockRes β`, `Λ_j`
unchanged. -/
noncomputable def crtLaws (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ b : BlockAtom Bk J L, ((Slot → ZMod (crtModuli m₀ blk p L b)) → ℝ) →ₗ[ℝ] ℝ :=
  fun b => pullLaw (crtAtomEquiv blk h0 L b) (Λ b)

/-- **Every multilinear energy on the block atoms is an energy on the cyclic coordinates**:
`∫ ∏_v a_v(x_v) d(⊗_b Λ_b) = ∫ ∏_v a_v(crt y_v) d(⊗_b crtLaws(Λ)_b)`, for every block law. -/
theorem multilinearIntegral_crt (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j)) (L : ℕ)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (a : Slot → (∀ b : BlockAtom Bk J L, BlockLabel m₀ blk p L b) → ℝ) :
    multilinearIntegral (tensorLaw Λ) a =
      multilinearIntegral (tensorLaw (crtLaws blk h0 L Λ))
        (fun v y => a v (crtLabelEquiv blk h0 L y)) := by
  unfold multilinearIntegral crtLaws
  rw [tensorLaw_pullLaw]
  congr 1
  funext x
  refine Finset.prod_congr rfl fun v _ => ?_
  congr 1
  funext b
  simp [crtLabelEquiv, Equiv.piCongrRight]

/-- **The energy of the paper's lift on the block atoms, in cyclic coordinates** (G1's gap 2):
for every block-atom law `⊗_b Λ_b` (joint laws on the blocks allowed),
`Y_{⊗_b Λ_b}(F_A) = Y_{⊗_b crtLaws(Λ)_b}(unchangedInput crtModuli … (paperCutoff N) A L)`.
This replaces the product-prefix hypothesis `Λ_none = ⊗_i λ0_i` of
`EnvelopeInputs.diagonalIntegral_atomLift_eq`. -/
theorem diagonalIntegral_blockLift_eq_crt (L : ℕ)
    (hpair : Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    (A : Finset ℤ)
    (Λ : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) :
    diagonalIntegral (tensorLaw Λ) (blockLift m₀ blk p L A) =
      diagonalIntegral (tensorLaw (crtLaws blk (prefix_pairwise hpair) L Λ))
        (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) := by
  unfold diagonalIntegral
  rw [multilinearIntegral_crt blk (prefix_pairwise hpair) L Λ]
  congr 1
  funext v y
  exact blockLift_crtLabel blk L hpair A y

end Sarkozy.EnvelopeEnergiesPaper

module

public import Sarkozy.IndexSupport.HalfFunctions
public import Sarkozy.IndexSupport.Labels

/-!
# The coupled index of `def:hyb:coupled`, in product coordinates

After the Chinese remainder theorem, the index of one query is
`Ω_e = ℤ/Kℤ × ∏_{p | M_0} ℤ/p^{h_p}ℤ` (`def:hyb:coupled`(a)). We index its coordinates by
`Option P`: `none` is the interval coordinate `b_e ∈ ℤ/Kℤ`, `some p` the residue
coordinate modulo `p^{h_p}` (`CoordSpace`). The coordinate chains are the two-step chain on
the interval coordinate and the residue chains (`coordChain`; `def:hyb:coupled`(e): the
interval is always revealed in the sense that its tail is one); the coordinate transitions
are the cyclic shift and the convolutions with the laws `μ_{e,p}` of the square increments
(`coordTransition`; `def:hyb:coupled`(c)).

`coupled_index_sectorOperator` proves `cor:index-support-frame`(i) for this index: `𝒯` and
`𝒯ᵀ` preserve every exact-conductor sector, are the identity on `H_0` and have norm at
most `δ_S` on `H_S`, given only that the chosen residue tails bound the convolution norms
on the exact-conductor spaces (`hnorm`; the paper's choice of tails, e.g.
`lem:imp:padic-envelope`). The moduli need not be prime powers of distinct primes for this
statement; that matters only for the identification with `ℤ/Kℤ × ℤ/M_0ℤ`, which is not
formalized here.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section Coordinates

variable (Kint : ℕ) {P : Type*} (pr h : P → ℕ)

/-- The coordinate sets of one query: `ℤ/Kℤ` (interval) and `ℤ/p^{h_p}ℤ` (residues). -/
abbrev CoordSpace : Option P → Type
  | none => ZMod Kint
  | some p => ZMod (pr p ^ h p)

variable [NeZero Kint] [∀ p, NeZero (pr p ^ h p)]

instance coordFintype : ∀ j, Fintype (CoordSpace Kint pr h j)
  | none => inferInstanceAs (Fintype (ZMod Kint))
  | some p => inferInstanceAs (Fintype (ZMod (pr p ^ h p)))

instance coordDecidableEq : ∀ j, DecidableEq (CoordSpace Kint pr h j)
  | none => inferInstanceAs (DecidableEq (ZMod Kint))
  | some p => inferInstanceAs (DecidableEq (ZMod (pr p ^ h p)))

instance coordNonempty : ∀ j, Nonempty (CoordSpace Kint pr h j)
  | none => inferInstanceAs (Nonempty (ZMod Kint))
  | some p => inferInstanceAs (Nonempty (ZMod (pr p ^ h p)))

/-- The coordinate chains: constants/identity on the interval, residues mod `p^l`. -/
noncomputable def coordChain : ∀ j, Chain (CoordSpace Kint pr h j)
  | none => Chain.whole (ZMod Kint)
  | some p => Chain.residues (pr p) (h p)

/-- The coordinate transitions: the cyclic shift `b ↦ b + 1` and the convolutions with the
increment laws `μ p`. -/
noncomputable def coordTransition (μ : ∀ p, ZMod (pr p ^ h p) → ℝ) :
    ∀ j, Matrix (CoordSpace Kint pr h j) (CoordSpace Kint pr h j) ℝ
  | none => (shiftMatrix (1 : ZMod Kint) : Matrix (ZMod Kint) (ZMod Kint) ℝ)
  | some p => (convMatrix (μ p) : Matrix (ZMod (pr p ^ h p)) (ZMod (pr p ^ h p)) ℝ)

/-- The coordinate tails: one on the interval coordinate, the chosen residue tails. -/
def coordTails (t : ∀ p, Tails (Chain.residues (pr p) (h p)).depth) :
    ∀ j, Tails (coordChain Kint pr h j).depth
  | none => Tails.bernoulli 1 zero_le_one le_rfl
  | some p => t p

theorem coordTransition_hypotheses (μ : ∀ p, ZMod (pr p ^ h p) → ℝ)
    (hμ : ∀ p r, 0 ≤ μ p r) (hμ1 : ∀ p, ∑ r, μ p r = 1)
    (t : ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (hnorm : ∀ p (l : Fin ((Chain.residues (pr p) (h p)).depth + 1)) f,
      (Chain.residues (pr p) (h p)).diff l *ᵥ f = f →
      (convMatrix (μ p) *ᵥ f) ⬝ᵥ (convMatrix (μ p) *ᵥ f) ≤ (t p).tail l ^ 2 * (f ⬝ᵥ f))
    (j : Option P) :
    (∀ l : Fin ((coordChain Kint pr h j).depth + 1),
      RangeBound ((coordChain Kint pr h j).diff l) (coordTransition Kint pr h μ j)
        ((coordTails Kint pr h t j).tail l)) ∧
    coordTransition Kint pr h μ j * (coordChain Kint pr h j).cond 0 =
      (coordChain Kint pr h j).cond 0 := by
  match j with
  | none =>
    exact ⟨fun l => shift_rangeBound (1 : ZMod Kint) l,
      (shiftMatrix_doublyStochastic (1 : ZMod Kint)).mul_mean⟩
  | some p =>
    exact residue_conv_hypotheses (pr p) (h p) (hμ p) (hμ1 p) (t p) (hnorm p)

end Coordinates

/-- **`cor:index-support-frame`(i) for the coupled index of `def:hyb:coupled`.**
For queries `e ∈ E`, each with the interval coordinate `ℤ/Kℤ` and residue coordinates
`ℤ/p^{h_p}ℤ`, cyclic interval shift and convolutions with increment laws `μ_{e,p}` whose norms
on the exact-conductor spaces are bounded by the chosen tails, the signed index operator
`𝒯 = ⊗_e (2P_e - T_e)` and its adjoint map every exact-conductor sector `H_S` into itself, are
the identity on `H_0`, and have norm at most `δ_S` on `H_S`. -/
theorem coupled_index_sectorOperator (Kint : ℕ) [NeZero Kint] {P : Type*} [Fintype P]
    [DecidableEq P] (pr h : P → ℕ) [∀ p, NeZero (pr p ^ h p)]
    {E : Type*} [Fintype E] [DecidableEq E]
    (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ) (hμ : ∀ e p r, 0 ≤ μ e p r)
    (hμ1 : ∀ e p, ∑ r, μ e p r = 1)
    (t : E → ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (hnorm : ∀ e p (l : Fin ((Chain.residues (pr p) (h p)).depth + 1)) f,
      (Chain.residues (pr p) (h p)).diff l *ᵥ f = f →
      (convMatrix (μ e p) *ᵥ f) ⬝ᵥ (convMatrix (μ e p) *ᵥ f) ≤ (t e p).tail l ^ 2 * (f ⬝ᵥ f)) :
    SectorOperator (querySectors (fun (_ : E) => coordChain Kint pr h))
        (signedIndexOp (fun e => coordTransition Kint pr h (μ e)))
        (queryWeight (fun (_ : E) => coordChain Kint pr h) (fun e => coordTails Kint pr h (t e))) ∧
      SectorOperator (querySectors (fun (_ : E) => coordChain Kint pr h))
        (signedIndexOp (fun e => coordTransition Kint pr h (μ e)))ᵀ
        (queryWeight (fun (_ : E) => coordChain Kint pr h) (fun e => coordTails Kint pr h (t e))) :=
  signedIndexOp_sectorOperator _ _ _
    (fun e j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).1)
    (fun e j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).2)

/-- **`eq:cp:mean-step` for the coupled index of `def:hyb:coupled`** (product coordinates):
`cor:index-support-frame`(iii) with the index data of `coupled_index_sectorOperator`, per-atom
brackets at the cut (CP6), and product half-functions whose slot functions average to `F`
(the abstract form of (ii)). The conclusion is that of `cut_signed_index_bounds`. -/
theorem coupled_index_mean_step (Kint : ℕ) [NeZero Kint] {P : Type*} [Fintype P]
    [DecidableEq P] (pr h : P → ℕ) [∀ p, NeZero (pr p ^ h p)]
    {E : Type*} [Fintype E] [DecidableEq E]
    (μ : E → ∀ p, ZMod (pr p ^ h p) → ℝ) (hμ : ∀ e p r, 0 ≤ μ e p r)
    (hμ1 : ∀ e p, ∑ r, μ e p r = 1)
    (t : E → ∀ p, Tails (Chain.residues (pr p) (h p)).depth)
    (hnorm : ∀ e p (l : Fin ((Chain.residues (pr p) (h p)).depth + 1)) f,
      (Chain.residues (pr p) (h p)).diff l *ᵥ f = f →
      (convMatrix (μ e p) *ᵥ f) ⬝ᵥ (convMatrix (μ e p) *ᵥ f) ≤ (t e p).tail l ^ 2 * (f ⬝ᵥ f))
    {V : Type*} [Fintype V] [DecidableEq V]
    {𝔅 : Type*} [Fintype 𝔅] [DecidableEq 𝔅] {Xb : 𝔅 → Type*} [∀ b, Fintype (Xb b)]
    [∀ b, DecidableEq (Xb b)]
    (c : ReflectionCut V) (ML ν MR : ∀ b, ((V → Xb b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ b, c.Bracket (ML b) (ν b) (MR b))
    {u w : E → c.Half} (hu : Function.Injective u) (hw : Function.Injective w)
    (φ ψ : ∀ _ : E, (∀ j, CoordSpace Kint pr h j) → (∀ b, Xb b) → ℝ) (F : (∀ b, Xb b) → ℝ)
    (hφ : ∀ e y, (FiniteLaw.uniform (∀ j, CoordSpace Kint pr h j)).expect
      (fun η => φ e η y) = F y)
    (hψ : ∀ e y, (FiniteLaw.uniform (∀ j, CoordSpace Kint pr h j)).expect
      (fun η => ψ e η y) = F y) :
    let C := fun (_ : E) => coordChain Kint pr h
    let tt := fun e => coordTails Kint pr h (t e)
    let Tc := fun e => coordTransition Kint pr h (μ e)
    let X := productHalf u φ F
    let Y := productHalf w ψ F
    let Xbar : (c.Half → ∀ b, Xb b) → ℝ := fun x => ∏ v, F (x v)
    let unif := FiniteLaw.uniform (E → ∀ j, CoordSpace Kint pr h j)
    let Jν := unif.expect (fun ω => c.form (tensorLaw ν) (X ω) (act (signedIndexOp Tc) Y ω))
    let Yν := c.form (tensorLaw ν) Xbar Xbar
    let eL := c.form (tensorLaw ML) Xbar Xbar
    let eR := c.form (tensorLaw MR) Xbar Xbar
    let VL := (queryLaw C tt).expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw ML) (queryReveal C J X ω) (queryReveal C J X ω)))
    let VR := (queryLaw C tt).expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw MR) (queryReveal C J Y ω) (queryReveal C J Y ω)))
    eL ≤ VL ∧ 0 ≤ eL ∧ eR ≤ VR ∧ 0 ≤ eR ∧
      |Jν - Yν| ≤ (1 / 2) * ((VL - eL) + (VR - eR)) ∧
      |Jν| ≤ Real.sqrt VL * Real.sqrt VR ∧
      Jν ≤ Yν + (1 / 2) * ((VL - eL) + (VR - eR)) :=
  cut_signed_index_bounds_of_product (fun (_ : E) => coordChain Kint pr h)
    (fun e => coordTails Kint pr h (t e)) (fun e => coordTransition Kint pr h (μ e))
    (fun e j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).1)
    (fun e j => (coordTransition_hypotheses Kint pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).2)
    c ML ν MR hbr hu hw φ ψ F hφ hψ

end Sarkozy.IndexSupport

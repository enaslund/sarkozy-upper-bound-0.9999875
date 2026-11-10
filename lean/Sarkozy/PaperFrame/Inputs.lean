module

public import Sarkozy.PaperFrame.Atoms
public import Sarkozy.Functional.CoupledInputs
public import Sarkozy.Functional.IndexCoordinates
public import Sarkozy.IndexSupport.CRT
public import Sarkozy.Comparison.ConcreteFrame

@[expose] public section

/-!
# The paper's inputs and coupled index for the closing frame (`def:hyb:coupled`)

The concrete energies of `Sarkozy.Comparison.ConcreteFrame` take a coupled index
(`CoupledIndex`: coordinates, chains, tails, transitions, query slots), inputs `φ, ψ` at
the query ends and a function `F` at the other slots. This module supplies the paper's
objects:

* the index coordinates of a query are those of `def:hyb:coupled`(a): the interval
  coordinate `ℤ/Kℤ` (`K = blockScale`) and the prime-power residues `ℤ/p^{h_p}ℤ`
  (`IndexSupport.CoordSpace`), with `M₀ = ∏_p p^{h_p}` (`IndexSupport.modulus`);
* `paperCoupledIndex`: the chains, tails and transitions of `IndexSupport.CoupledIndex`
  (interval shift; convolutions by the increment laws `μ_{e,p}`). Its hypotheses `hT` and
  `hT0` are proved from the residue-tail bound `hnorm` (`lem:imp:padic-envelope`, an
  explicit hypothesis) by `coordTransition_hypotheses`;
* `atomInput`: the inputs `g^{I_b,M₀,s}` of `def:record:functional`(f) at the index
  `η = (b, (s mod p^{h_p})_p)`, read on the atom labels; `F = atomLift` is the lift `F_A`;
* `expect_atomInput`: the mean identities `hφ = hψ` of the frame,
  `E_η g^{I_b,M₀,s} = F_A` (`lem:twointerval`(iii)), for every scale (both sides vanish
  at `L = 0`);
* `paper_frame`: the frame estimate `eq:cp:mean-step` for these objects, from the
  per-atom brackets alone.
-/

open Finset Function
open scoped BigOperators Matrix

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison

instance blockScale_neZero : NeZero blockScale := ⟨by norm_num [blockScale]⟩

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The input `g^{I_b, M₀, s}` (`def:record:functional`(f)) at the query index
`η = (b, (s mod p^{h_p})_p) ∈ ℤ/Kℤ × ∏_p ℤ/p^{h_p}ℤ`, read on the atom labels. The input
does not depend on the query. -/
noncomputable def atomInput (L : ℕ) (A : Finset ℤ) {E : Type} (_e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) (x : ∀ b, AtomLabel m₀ p L b) : ℝ :=
  indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L
    (modulus pr h) A ((crtEquiv blockScale pr h hcop).symm η) (atomGroupEquiv m₀ p L x)

omit [DecidableEq J₀] [∀ L, DecidableEq (J L)] in
theorem liftOn_empty_interval {Jx : Type} [Fintype Jx] (m : Jx → ℕ) [∀ j, NeZero (m j)]
    (T : Finset (ResidueSpace m)) (f : ℤ → ℂ) (z : ResidueSpace m) :
    liftOn m T ∅ f z = 0 := by
  simp [liftOn, intervalCoeff]

/-- The mean identities `hφ = hψ` of the frame: the uniform average of the paper's input
over the index of a query is the lift, `E_η g^{I_b,M₀,s} = F_A` (`lem:twointerval`(iii),
transported along the CRT coordinates `crtEquiv`). -/
theorem expect_atomInput (L : ℕ) (A : Finset ℤ) {E : Type} (e : E)
    (x : ∀ b, AtomLabel m₀ p L b) :
    (FiniteLaw.uniform (∀ j, CoordSpace blockScale pr h j)).expect
        (fun η => atomInput m₀ p pr h hcop L A e η x) = atomLift m₀ p L A x := by
  have hmap := uniform_map_equiv (crtEquiv blockScale pr h hcop)
  rw [← hmap, FiniteLaw.expect_map]
  unfold atomInput
  simp only [Function.comp_def, Equiv.symm_apply_apply]
  rcases Nat.eq_zero_or_pos L with hL | hL
  · subst hL
    have h0 : ∀ ω : ZMod blockScale × ZMod (modulus pr h),
        indexedInput (joinModuli m₀ (p 0)) (paperCutoff (blockScale * 0)) blockScale 0
          (modulus pr h) A ω (atomGroupEquiv m₀ p 0 x) = 0 := by
      intro ω
      have hI : blockInterval blockScale 0 ω.1 = ∅ := by
        ext n
        simp [blockInterval]
      simp only [indexedInput, input, lift, hI, liftOn_empty_interval, Complex.zero_re]
    simp only [h0, FiniteLaw.expect_const]
    have hN : (Icc 1 ((blockScale * 0 : ℕ) : ℤ)) = ∅ := by simp
    simp only [atomLift, wholeLift, lift, hN, liftOn_empty_interval, Complex.zero_re]
  · exact expect_indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) hL A
      (atomGroupEquiv m₀ p L x)

variable {E : Type} [Fintype E] [DecidableEq E]

/-- The paper's coupled index (`def:hyb:coupled`(a),(c),(e), (CP0)(d)): for every query the
interval coordinate and the prime-power residues, with the coordinate chains, the chosen
tails, and the transitions `T_e` (interval shift ⊗ convolutions by the increment laws
`μ_{e,p}`). The hypotheses `hT` (norm bound on each exact-conductor space) and `hT0`
(constants fixed) of `CoupledIndex` are discharged from the residue-tail bound `hnorm`. -/
noncomputable def paperCoupledIndex (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w) :
    CoupledIndex E (fun _ => Option P) (fun _ => CoordSpace blockScale pr h) where
  C _ j := coordChain blockScale pr h j
  t e j := coordTails blockScale pr h (t e) j
  Tc e j := coordTransition blockScale pr h (μ e) j
  hT e j l :=
    (coordTransition_hypotheses blockScale pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).1 l
  hT0 e j :=
    (coordTransition_hypotheses blockScale pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e) j).2
  u := u
  w := w
  hu := hu
  hw := hw

/-- The frame estimate `eq:cp:mean-step` for the paper's objects: with the per-atom brackets
`(M_L, ν, M_R)` at the reserved cut (CP6), the signed index form of the paper's inputs is
at most `Y_ν + ½[(V_L − e_L) + (V_R − e_R)]`. The mean identities are `expect_atomInput`. -/
theorem paper_frame (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ML ν MR : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b)) (L : ℕ) (A : Finset ℤ) :
    signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => atomInput m₀ p pr h hcop L A e) (fun L A e => atomInput m₀ p pr h hcop L A e)
        (atomLift m₀ p) L A ≤
      energyComparison ν (atomLift m₀ p) L A +
        ((inclusionEnergyL (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ML
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A -
            energyMean (atomLift m₀ p) ML L A) +
          (inclusionEnergyR (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) MR
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A -
            energyMean (atomLift m₀ p) MR L A)) / 2 :=
  frame_of_brackets _ ML ν MR _ _ (atomLift m₀ p) hbr
    (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
    (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y) L A

end Sarkozy.PaperFrame

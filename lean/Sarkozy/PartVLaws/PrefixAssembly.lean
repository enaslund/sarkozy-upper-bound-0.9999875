module

public import Sarkozy.PartVLaws.ReferenceFields
public import Sarkozy.PartVLaws.BlockRP
public import Sarkozy.TensorMarginals

@[expose] public section

/-!
# The prefix law `μ₀` of `TheoremC.Reference`, assembled from atoms (`def:cp1`)

`paper/sections/09_comparison_theorem.tex`, `def:cp1` ("the product `μ = ⊗_𝔟 μ_𝔟` of the prefix
law and the tail laws"); `paper/sections/18_design.tex`, `def:construction`(b) (the atoms of the
prefix: the square-clique prefix, the middle blocks and the upper blocks).

`Reference.μ₀` is one law on `Slot → ResidueSpace m₀`, the product of the residue rings of all the
prefix moduli. The prefix is a finite family of atoms `a` (the prefix coordinates, the middle
blocks, the upper blocks), each with its own finite set `I a` of moduli `m a i` and its own law
`μ_a` on `Slot → ∏_{i ∈ I a} ℤ/m_{a,i}`. With `J₀ = Σ_a I a` and `m₀ (a, i) = m a i`:

* **`prefixAssembly μ`** `= (⊗_a μ_a)` carried to `ResidueSpace m₀` by the bijection
  `∏_a ∏_i ℤ/m_{a,i} ≃ ∏_{(a,i)} ℤ/m_{a,i}` (`atomsEquiv`);
* `prefixAssembly_rp`, `prefixAssembly_inv`, `prefixAssembly_unif`: the three fields `rp₀`,
  `inv₀`, `unif₀` of `Reference`, from the same properties of the atoms (tensors of reflection
  positive laws are reflection positive, `FiniteLaw.tensor_positive`; factorwise invariance,
  `expect_tensor_comp`; uniform marginals, `tensor_uniform_marginals`).

For the paper's atoms the atom properties are V1's and this package's results: the upper blocks
(`upperBlock_R1R3`, given the spectral inputs), the middle blocks (V1's
`middleBlockReference_*_familyPositive`, `_affine`, `_uniform`, given theirs), the square-clique
prefix (`Construction/`). The block partitions (the exact middle blocks and the upper bands) are
data and are not entered here.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.PartV

variable {A : Type} [Fintype A] [DecidableEq A] {I : A → Type} [∀ a, Fintype (I a)]
  [∀ a, DecidableEq (I a)] (m : (a : A) → I a → ℕ) [∀ a i, NeZero (m a i)]

/-- The moduli of the prefix, indexed by `J₀ = Σ_a I a`. -/
def prefixModuli (j : Σ a, I a) : ℕ := m j.1 j.2

instance prefixModuli_neZero (j : Σ a, I a) : NeZero (prefixModuli m j) :=
  inferInstanceAs (NeZero (m j.1 j.2))

/-- The labels of the atoms as residues of the prefix moduli. -/
def atomsEquiv :
    (∀ a, ∀ i : I a, ZMod (m a i)) ≃ FourierArithmetic.ResidueSpace (prefixModuli m) where
  toFun x j := x j.1 j.2
  invFun y a i := y ⟨a, i⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The prefix law** `μ₀ = ⊗_a μ_a`, carried to `ResidueSpace m₀`. -/
noncomputable def prefixAssembly (μ : ∀ a, FiniteLaw (Slot → ∀ i : I a, ZMod (m a i))) :
    FiniteLaw (Slot → FourierArithmetic.ResidueSpace (prefixModuli m)) :=
  (FiniteLaw.tensor μ).map fun z v => atomsEquiv m (z v)

theorem prefixAssembly_expect (μ : ∀ a, FiniteLaw (Slot → ∀ i : I a, ZMod (m a i)))
    (F : (Slot → FourierArithmetic.ResidueSpace (prefixModuli m)) → ℝ) :
    (prefixAssembly m μ).expect F =
      (FiniteLaw.tensor μ).expect (fun z => F (fun v => atomsEquiv m (z v))) := by
  unfold prefixAssembly
  rw [FiniteLaw.expect_map]
  rfl

/-- **`Reference.rp₀`**: reflection positivity at every cut of `𝔉` passes from the atoms to the
prefix law. -/
theorem prefixAssembly_rp (μ : ∀ a, FiniteLaw (Slot → ∀ i : I a, ZMod (m a i)))
    (hμ : ∀ a, TheoremC.FamilyReflectionPositive (signedIntegral (μ a).weight)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (prefixAssembly m μ).weight) := by
  intro c hc
  have ht := FiniteLaw.tensor_positive μ c (fun a => hμ a c hc)
  have heq : signedIntegral (prefixAssembly m μ).weight =
      pushFunctional (signedIntegral (FiniteLaw.tensor μ).weight)
        (fun z v => atomsEquiv m (z v)) := by
    refine LinearMap.ext fun F => ?_
    rw [← FiniteLaw.expect_eq_signedIntegral, prefixAssembly_expect]
    rfl
  rw [heq]
  exact FiveType.TwoCoord.positive_push_halfLocal c ht _ (fun x w => atomsEquiv m (x w))
    (fun _ => rfl) (fun _ => rfl)

/-- The uniform law is carried to the uniform law by a bijection. -/
theorem uniform_expect_equiv' {Ω Ω' : Type*} [Fintype Ω] [Nonempty Ω] [Fintype Ω'] [Nonempty Ω']
    (e : Ω ≃ Ω') (f : Ω' → ℝ) :
    (FiniteLaw.uniform Ω).expect (fun ω => f (e ω)) = (FiniteLaw.uniform Ω').expect f := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, Fintype.card_congr e]
  congr 1
  exact Fintype.sum_equiv e _ _ fun _ => rfl

/-- **`Reference.unif₀`**: uniform one-slot marginals pass from the atoms to the prefix law. -/
theorem prefixAssembly_unif (μ : ∀ a, FiniteLaw (Slot → ∀ i : I a, ZMod (m a i)))
    (hμ : ∀ a, HasUniformMarginals (μ a)) : HasUniformMarginals (prefixAssembly m μ) := by
  intro v f
  rw [prefixAssembly_expect]
  have h := tensor_uniform_marginals μ hμ v (fun x => f (atomsEquiv m x))
  rw [h]
  exact uniform_expect_equiv' (atomsEquiv m) f

/-- The square-affine map of one atom, `z_{v,i} ↦ α_i z_{v,i} + β_i`. -/
def atomAffine {a : A} (α : ∀ i : I a, (ZMod (m a i))ˣ) (β : ∀ i : I a, ZMod (m a i)) :
    (Slot → ∀ i : I a, ZMod (m a i)) ≃ (Slot → ∀ i : I a, ZMod (m a i)) where
  toFun z v i := (α i : ZMod (m a i)) * z v i + β i
  invFun z v i := ((α i)⁻¹ : (ZMod (m a i))ˣ) * (z v i - β i)
  left_inv z := by
    funext v i
    simp only [add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv z := by
    funext v i
    simp only [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]

/-- **`Reference.inv₀`**: square-affine invariance passes from the atoms to the prefix law. -/
theorem prefixAssembly_inv (μ : ∀ a, FiniteLaw (Slot → ∀ i : I a, ZMod (m a i)))
    (hμ : ∀ a (α : ∀ i : I a, (ZMod (m a i))ˣ) (β : ∀ i : I a, ZMod (m a i)),
      (∀ i, IsSquare (α i : ZMod (m a i))) → ∀ H : (Slot → ∀ i : I a, ZMod (m a i)) → ℝ,
        (μ a).expect (fun z => H (atomAffine m α β z)) = (μ a).expect H)
    (α : ∀ j, (ZMod (prefixModuli m j))ˣ) (β : FourierArithmetic.ResidueSpace (prefixModuli m))
    (hα : ∀ j, IsSquare (α j : ZMod (prefixModuli m j)))
    (F : (Slot → FourierArithmetic.ResidueSpace (prefixModuli m)) → ℝ) :
    (prefixAssembly m μ).expect
        (fun z => F (fun v => PaperFrame.piAffineEquiv (prefixModuli m) α β (z v))) =
      (prefixAssembly m μ).expect F := by
  rw [prefixAssembly_expect, prefixAssembly_expect]
  let T : ∀ a, (Slot → ∀ i : I a, ZMod (m a i)) ≃ (Slot → ∀ i : I a, ZMod (m a i)) :=
    fun a => atomAffine m (fun i => α ⟨a, i⟩) (fun i => β ⟨a, i⟩)
  have hT : ∀ a y, (μ a).weight (T a y) = (μ a).weight y := fun a y =>
    weight_comp_of_expect (μ a) (T a)
      (fun H => hμ a _ _ (fun i => hα ⟨a, i⟩) H) y
  have h := expect_tensor_comp μ T hT (fun z => F (fun v => atomsEquiv m (z v)))
  refine Eq.trans ?_ h
  rfl

/-! ## Block atoms and the reference -/

section BlockAtom

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The atom form of (R3) for a block law**: invariance under `z_{v,i} ↦ α_i z_{v,i} + β_i` with
`χ_{p_i}(α_i) = 1` (V1's form) gives the form of `prefixAssembly_inv` (units that are squares;
the map is `atomAffine` by definition). -/
theorem atomInv_of_affine (μ : FiniteLaw (Slot → BlockLabel pr))
    (h : ∀ (α β : BlockLabel pr), (∀ i, quadraticChar (ZMod (pr i)) (α i) = 1) →
      ∀ H : (Slot → BlockLabel pr) → ℝ,
        μ.expect (fun z => H (fun v i => α i * z v i + β i)) = μ.expect H)
    (α : ∀ i, (ZMod (pr i))ˣ) (β : BlockLabel pr) (hα : ∀ i, IsSquare (α i : ZMod (pr i)))
    (H : (Slot → BlockLabel pr) → ℝ) :
    μ.expect (fun z => H (fun v i => (α i : ZMod (pr i)) * z v i + β i)) = μ.expect H :=
  h (fun i => (α i : ZMod (pr i))) β
    (fun i => (quadraticChar_one_iff_isSquare (α i).ne_zero).mpr (hα i)) H

end BlockAtom

section Reference

/-- **The reference of `def:cp1` from Part V's atoms**: the prefix law assembled from atom laws
with (R1)–(R3) (`prefixAssembly`), and the tail laws `tailFamilyFrom P₄`. For an upper block the
atom properties are `upperBlock_R1R3` (with `atomInv_of_affine`). -/
noncomputable def partVReference (μ : ∀ a, FiniteLaw (Slot → ∀ i : I a, ZMod (m a i)))
    (hrp : ∀ a, TheoremC.FamilyReflectionPositive (signedIntegral (μ a).weight))
    (hinv : ∀ a (α : ∀ i : I a, (ZMod (m a i))ˣ) (β : ∀ i : I a, ZMod (m a i)),
      (∀ i, IsSquare (α i : ZMod (m a i))) → ∀ H : (Slot → ∀ i : I a, ZMod (m a i)) → ℝ,
        (μ a).expect (fun z => H (atomAffine m α β z)) = (μ a).expect H)
    (hunif : ∀ a, HasUniformMarginals (μ a)) (hW : Target.Weil) (hV : TailInputsValid P4)
    (P5 : ℕ) (hP5 : P4 ≤ P5)
    (hmix : ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
      Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ (tailLawFamily q) {v}) :
    TheoremC.Reference (prefixModuli m) :=
  tailReference (prefixModuli m) (prefixAssembly m μ) (prefixAssembly_rp m μ hrp)
    (prefixAssembly_inv m μ hinv) (prefixAssembly_unif m μ hunif) hW hV P5 hP5 hmix

end Reference

end Sarkozy.PartVLaws

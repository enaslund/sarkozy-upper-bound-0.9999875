module

public import Sarkozy.PartVLaws.TailRP
public import Sarkozy.PartV.TailFamily
public import Sarkozy.Mixing.Conditional
public import Sarkozy.Comparison.AnalyticStage
public import Sarkozy.TheoremC.Data

@[expose] public section

/-!
# The tail fields of `TheoremC.Reference` (`def:cp1`, `hyp:record:reference`)

`paper/sections/09_comparison_theorem.tex`, `def:cp1`; `paper/sections/27_tail_index.tex`,
`lem:tail-law`, `lem:record:tail-mixing`.

`TheoremC.Reference` asks for one law `μp q` at every modulus `q`, reflection positive at every
cut of `𝔉` at every prime (`rpp`). The tail atoms of the paper are the primes of
`𝒯_N = {p : P₄ ≤ p ≤ N^{1/20}}` (`PaperFrame.tailPrimes`), and the tail law is used only there:
below `P₄` the spectral inputs of the tail datum are not available. V1's `tailLawFamily` takes
the tail law at *every* prime with nonempty labelling sets, so it cannot satisfy `rpp` from the
paper's inputs. Here:

* **`tailFamilyFrom P`**: the tail law at the primes `q ≥ P` (with nonempty labelling sets), the
  uniform law elsewhere. For `P ≥ P₄` it agrees with V1's family at every prime `q ≥ P`
  (`tailFamilyFrom_eq`), in particular wherever `Reference.mixing` is asked (`q ≥ P₅ ≥ P`).
* **The fields**:
  - `invp`: `tailFamilyFrom_invp`, at every modulus;
  - `unifp`: `tailFamilyFrom_unifp`, at every prime;
  - `rpp`: **`tailFamilyFrom_rpp`**, at every prime, from Weil's bound and the validity of the
    tail inputs at the tail primes (`lem:tail-law`(i), a hypothesis: (V1)–(V3) are spectral);
    the uniform law is reflection positive at every cut (`uniform_familyPositive`, an i.i.d.
    law);
  - `mixing`: `tailFamilyFrom_mixing` transfers the mixing of V1's `tailLawFamily` at
    `q ≥ P₅` (`lem:record:tail-mixing`(c)) to `tailFamilyFrom P` for `P ≤ P₅`. The mixing of
    `tailLawFamily` itself is `lem:record:tail-mixing`, which V3 formalizes in
    `Sarkozy.PartVRecords.TailMixing` (`tailLawFamily_mixing`, with `P₅ = 2^{65536}`); it is
    taken here as the hypothesis `hmix` so that this file does not depend on work in progress.
* **`tailReference`**: the `TheoremC.Reference` with `μp := tailFamilyFrom P₄`, from a prefix
  law `μ₀` with its three fields (`rp₀`, `inv₀`, `unif₀`; the prefix and block laws carried to
  `ResidueSpace m₀`, not assembled here), Weil's bound, the tail inputs and the mixing.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV

/-! ## The uniform law is reflection positive -/

theorem uniform_eq_iid {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    [Nonempty X] :
    signedIntegral (FiniteLaw.uniform (I → X)).weight =
      ReflectionCut.iidLaw (I := I) (FiniteLaw.uniform X) := by
  unfold ReflectionCut.iidLaw
  congr 1
  funext y
  change (Fintype.card (I → X) : ℝ)⁻¹ = ∏ i : I, (Fintype.card X : ℝ)⁻¹
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, inv_pow]

/-- **The uniform law on the labellings of the slots is reflection positive at every cut** (it is
i.i.d.). -/
theorem uniform_familyPositive {X : Type} [Fintype X] [DecidableEq X] [Nonempty X] :
    TheoremC.FamilyReflectionPositive (signedIntegral (FiniteLaw.uniform (Slot → X)).weight) := by
  intro c _
  rw [uniform_eq_iid]
  exact ReflectionCut.iidLaw_positive c _

/-! ## The family -/

/-- **The tail family from the threshold `P`**: the tail law at the primes `q ≥ P` whose labelling
sets are nonempty, the uniform law at every other modulus. -/
noncomputable def tailFamilyFrom (P : ℕ) (q : ℕ) [NeZero q] : FiniteLaw (Slot → ZMod q) :=
  if h : q.Prime ∧ P ≤ q then
    haveI : Fact q.Prime := ⟨h.1⟩
    haveI := Classical.propDecidable (TailNonempty q)
    if h' : TailNonempty q then tailLaw q h' else FiniteLaw.uniform _
  else FiniteLaw.uniform _

/-- At the primes `q ≥ P`, the family is V1's `tailLawFamily`. -/
theorem tailFamilyFrom_eq (P q : ℕ) [NeZero q] (hq : q.Prime) (hPq : P ≤ q) :
    tailFamilyFrom P q = tailLawFamily q := by
  unfold tailFamilyFrom tailLawFamily
  rw [dite_eq_left (⟨hq, hPq⟩ : q.Prime ∧ P ≤ q), dite_eq_left hq]

/-- **`Reference.invp`**, at every modulus. -/
theorem tailFamilyFrom_invp (P q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q)
    (ha : IsSquare (a : ZMod q)) (F : (Slot → ZMod q) → ℝ) :
    (tailFamilyFrom P q).expect (fun z => F (fun v => PaperFrame.affineEquiv a b (z v))) =
      (tailFamilyFrom P q).expect F := by
  unfold tailFamilyFrom
  split_ifs with hq h'
  · have : Fact q.Prime := ⟨hq.1⟩
    exact tailLaw_invp q h' a b ha F
  · exact uniform_expect_equiv (Equiv.piCongrRight fun _ => PaperFrame.affineEquiv a b) F
  · exact uniform_expect_equiv (Equiv.piCongrRight fun _ => PaperFrame.affineEquiv a b) F

/-- **`Reference.unifp`**, at every prime. -/
theorem tailFamilyFrom_unifp (P q : ℕ) [NeZero q] (hq : q.Prime) :
    HasUniformMarginals (tailFamilyFrom P q) := by
  have : Fact q.Prime := ⟨hq⟩
  unfold tailFamilyFrom
  split_ifs with h h'
  · exact tailLaw_uniform q h'
  · intro v g
    exact vertex_uniform_of_translation (FiniteLaw.uniform (Slot → ZMod q)) (fun _ _ => rfl) v g
  · intro v g
    exact vertex_uniform_of_translation (FiniteLaw.uniform (Slot → ZMod q)) (fun _ _ => rfl) v g

/-- **The validity of the tail inputs at the tail primes** (`lem:tail-law`(i), the spectral input,
as a hypothesis): at every prime `q ≥ P` with nonempty labelling sets, the inputs of the tail
datum are valid on `{q}`. -/
def TailInputsValid (P : ℕ) : Prop :=
  ∀ (q : ℕ) [Fact q.Prime], P ≤ q → ∀ (hne : TailNonempty q) (hW : WeilBound (ZMod q))
    (hp : (2 : ℝ) ^ 20 ≤ q),
      ValidInputs (tailFieldLaws q hne) (tail_upperDatumHyp q hW hp hne) (tailR q) tailOrd tailRes
        tailCap

/-- **`Reference.rpp`**, at every prime: the family is reflection positive at every cut of `𝔉`,
given Weil's bound and the validity of the tail inputs at the primes `q ≥ P ≥ P₄`. -/
theorem tailFamilyFrom_rpp (hW : Target.Weil) {P : ℕ} (hP : P4 ≤ P) (hV : TailInputsValid P)
    (q : ℕ) [NeZero q] (_hq : q.Prime) :
    TheoremC.FamilyReflectionPositive (signedIntegral (tailFamilyFrom P q).weight) := by
  unfold tailFamilyFrom
  split_ifs with h h'
  · have : Fact q.Prime := ⟨h.1⟩
    exact (tailLaw_R1R3 q hW (hP.trans h.2) h' fun hW' hp' => hV q h.2 h' hW' hp').1
  · exact uniform_familyPositive
  · exact uniform_familyPositive

/-- **`Reference.mixing` from the mixing of V1's tail family**: for `P ≤ P₅` the two families agree
at every prime `q ≥ P₅`, so the `(γ, v)`-mixing of `tailLawFamily` there
(`lem:record:tail-mixing`(c), V3's `tailLawFamily_mixing`) is that of `tailFamilyFrom P`. -/
theorem tailFamilyFrom_mixing {P P5 : ℕ} (hP : P ≤ P5)
    (hmix : ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
      Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ (tailLawFamily q) {v}) :
    ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
      Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ (tailFamilyFrom P q) {v} := by
  intro q _ hq h5 v
  rw [tailFamilyFrom_eq P q hq (hP.trans h5)]
  exact hmix q hq h5 v

/-! ## The reference -/

section Assembly

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]

/-- **The reference of `def:cp1` with the paper's tail laws**: the prefix law `μ₀` with its fields
(supplied: the prefix and block laws carried to `ResidueSpace m₀`), and `μp := tailFamilyFrom P₄`
with `rpp`, `invp`, `unifp` proved here and `mixing` from the mixing of the tail laws at `P₅`. -/
noncomputable def tailReference (μ₀ : FiniteLaw (Slot → FourierArithmetic.ResidueSpace m₀))
    (rp₀ : TheoremC.FamilyReflectionPositive (signedIntegral μ₀.weight))
    (inv₀ : ∀ (a : ∀ i, (ZMod (m₀ i))ˣ) (b : FourierArithmetic.ResidueSpace m₀),
      (∀ i, IsSquare ((a i : ZMod (m₀ i)))) → ∀ F : (Slot → FourierArithmetic.ResidueSpace m₀) → ℝ,
        μ₀.expect (fun z => F (fun v => PaperFrame.piAffineEquiv m₀ a b (z v))) = μ₀.expect F)
    (unif₀ : HasUniformMarginals μ₀) (hW : Target.Weil) (hV : TailInputsValid P4) (P5 : ℕ)
    (hP5 : P4 ≤ P5)
    (hmix : ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
      Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ (tailLawFamily q) {v}) :
    TheoremC.Reference m₀ where
  μ₀ := μ₀
  μp q _ := tailFamilyFrom P4 q
  rp₀ := rp₀
  rpp q _ hq := tailFamilyFrom_rpp hW le_rfl hV q hq
  inv₀ := inv₀
  invp q _ a b ha F := tailFamilyFrom_invp P4 q a b ha F
  unif₀ := unif₀
  unifp q _ hq := tailFamilyFrom_unifp P4 q hq
  P5 := P5
  mixing := tailFamilyFrom_mixing hP5 hmix

end Assembly

end Sarkozy.PartVLaws

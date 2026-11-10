module

public import Sarkozy.PartVLaws.ReferenceFields
public import Sarkozy.PartVLaws.BlockRP

@[expose] public section

/-!
# Explicit thresholds for the labelling sets of the upper and tail laws

`paper/sections/12_labellings.tex`, `lem:graphs:sequential`; `paper/sections/25_upper_reference.tex`
and `paper/sections/27_tail_index.tex` (the upper reference at the primes of `[P₃, P₄)`, the tail
law at `p ≥ P₄`).

V1's `NonVacuity.lean` proves that the labelling sets `Inj_p(G_{φ₀φ₁,j})` are nonempty at every
`p ≥ p₀` for some unspecified `p₀` (from a limit), and notes that an explicit threshold "would
follow from the explicit sequential counts". It does:

* `fieldGraph_degree_two`, `fieldGraph_degree_one`: the eighteen graphs `G_{φ₀φ₁,j}` have
  maximum degree at most `20` (kernel `decide`; the root attains it);
* `threshold_twenty`: `q - 𝔈_t - 2^t n > 0` for `t ≤ 20`, `n ≤ 72` at every `q ≥ 81·10¹²`;
* `injLabellings_nonempty_of_degree`: under Weil's bound a graph of degree at most `D` has an
  injective strict-square labelling once these one-step bounds are positive (the extension of
  the empty labelling, `exists_extension`);
* **`tailNonempty_explicit`**, **`upperNonempty_explicit`**: under H1 the tail law is defined at
  every prime `p ≥ 81·10¹²` and the upper block laws on every block of such primes; both
  thresholds lie below `P₃ = 167·2⁴⁰` (`threshold_le_P3`), so they cover every upper band and the
  whole tail;
* `tailFamilyFrom_eq_tailLaw`: at every tail prime `q ≥ P₄` the family `tailFamilyFrom P₄` is the
  tail law itself (the uniform fallback is never used there).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV

/-! ## Degrees of the eighteen graphs -/

theorem degree_LL_two_le : ∀ v : ZMod 6 × ZMod 6 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeL typeL u v = true ∨
      twoLayerEdge typeL typeL v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeL
  decide +kernel

theorem degree_LF_two_le : ∀ v : ZMod 6 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeL typeF u v = true ∨
      twoLayerEdge typeL typeF v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeF typeL
  decide +kernel

theorem degree_LE_two_le : ∀ v : ZMod 6 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeL typeE u v = true ∨
      twoLayerEdge typeL typeE v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_FL_two_le : ∀ v : Fin 3 × ZMod 6 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeF typeL u v = true ∨
      twoLayerEdge typeF typeL v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeF typeL
  decide +kernel

theorem degree_FF_two_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeF typeF u v = true ∨
      twoLayerEdge typeF typeF v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeF
  decide +kernel

theorem degree_FE_two_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeF typeE u v = true ∨
      twoLayerEdge typeF typeE v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EL_two_le : ∀ v : Fin 3 × ZMod 6 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeE typeL u v = true ∨
      twoLayerEdge typeE typeL v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_EF_two_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeE typeF u v = true ∨
      twoLayerEdge typeE typeF v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EE_two_le : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeE typeE u v = true ∨
      twoLayerEdge typeE typeE v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE
  decide +kernel

theorem degree_LL_one_le : ∀ v : ZMod 6 × ZMod 6 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeL typeL u v = true ∨
      twoLayerEdge typeL typeL v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeL
  decide +kernel

theorem degree_LF_one_le : ∀ v : ZMod 6 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeL typeF u v = true ∨
      twoLayerEdge typeL typeF v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeF typeL
  decide +kernel

theorem degree_LE_one_le : ∀ v : ZMod 6 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeL typeE u v = true ∨
      twoLayerEdge typeL typeE v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_FL_one_le : ∀ v : Fin 3 × ZMod 6 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeF typeL u v = true ∨
      twoLayerEdge typeF typeL v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeF typeL
  decide +kernel

theorem degree_FF_one_le : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeF typeF u v = true ∨
      twoLayerEdge typeF typeF v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeF
  decide +kernel

theorem degree_FE_one_le : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeF typeE u v = true ∨
      twoLayerEdge typeF typeE v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EL_one_le : ∀ v : Fin 3 × ZMod 6 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeE typeL u v = true ∨
      twoLayerEdge typeE typeL v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_EF_one_le : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeE typeF u v = true ∨
      twoLayerEdge typeE typeF v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EE_one_le : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeE typeE u v = true ∨
      twoLayerEdge typeE typeE v u = true).card ≤ 20 := by
  unfold twoLayerEdge typeE
  decide +kernel

theorem fieldGraph_degree_two (f₀ f₁ : FType) (v : f₀.Obj × f₁.Obj × Fin 2) :
    nbrCount (fieldGraph f₀ f₁ (Fin 2)) univ v ≤ 20 := by
  rw [fieldGraph, nbrCount_twoLayer]
  cases f₀ <;> cases f₁
  · exact degree_LL_two_le v
  · exact degree_LF_two_le v
  · exact degree_LE_two_le v
  · exact degree_FL_two_le v
  · exact degree_FF_two_le v
  · exact degree_FE_two_le v
  · exact degree_EL_two_le v
  · exact degree_EF_two_le v
  · exact degree_EE_two_le v

theorem fieldGraph_degree_one (f₀ f₁ : FType) (v : f₀.Obj × f₁.Obj × Fin 1) :
    nbrCount (fieldGraph f₀ f₁ (Fin 1)) univ v ≤ 20 := by
  rw [fieldGraph, nbrCount_twoLayer]
  cases f₀ <;> cases f₁
  · exact degree_LL_one_le v
  · exact degree_LF_one_le v
  · exact degree_LE_one_le v
  · exact degree_FL_one_le v
  · exact degree_FF_one_le v
  · exact degree_FE_one_le v
  · exact degree_EL_one_le v
  · exact degree_EF_one_le v
  · exact degree_EE_one_le v

/-! ## The threshold -/

theorem gradedA_le_twenty {t : ℕ} (ht : t ≤ 20) : gradedA t ≤ 8912898 := by
  interval_cases t <;> norm_num [gradedA]

theorem gradedB_le_twenty {t : ℕ} (ht : t ≤ 20) : gradedB t ≤ 524287 := by
  interval_cases t <;> norm_num [gradedB]

/-- **The threshold for degree `20` and `72` vertices**: at every `q ≥ 81·10¹²`,
`q - 𝔈_t - 2^t n > 0` for all `t ≤ 20` and `n ≤ 72`. -/
theorem threshold_twenty {q : ℝ} (hq : 81 * 10 ^ 12 ≤ q) {n : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ 72) :
    ∀ t ≤ 20, 0 < q - softError q t - 2 ^ t * n := by
  intro t ht
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hs : (9000000 : ℝ) ≤ Real.sqrt q := by
    have h1 : Real.sqrt (81 * 10 ^ 12 : ℝ) = 9000000 := by
      rw [show (81 * 10 ^ 12 : ℝ) = 9000000 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h1]
    exact Real.sqrt_le_sqrt hq
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
  have hA := gradedA_le_twenty ht
  have hB := gradedB_le_twenty ht
  have h2t : (2 : ℝ) ^ t ≤ 1048576 := by
    calc (2 : ℝ) ^ t ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) ht
      _ = 1048576 := by norm_num
  have hA' : gradedA t * Real.sqrt q ≤ 8912898 * Real.sqrt q :=
    mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg q)
  have h2n : (2 : ℝ) ^ t * n ≤ 1048576 * 72 :=
    mul_le_mul h2t hn hn0 (by norm_num)
  have hkey : (9000000 : ℝ) * (Real.sqrt q - 8912898) ≤ Real.sqrt q * (Real.sqrt q - 8912898) :=
    mul_le_mul_of_nonneg_right hs (by linarith)
  unfold softError
  nlinarith

/-- **A graph of bounded degree has labellings** at every field where the one-step bounds are
positive (under Weil's bound): the empty labelling extends. -/
theorem injLabellings_nonempty_of_degree {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {W : Type*} [Fintype W] [DecidableEq W] (hW : WeilBound F) (G : OrientedGraph W) {D : ℕ}
    (hdeg : ∀ v, nbrCount G univ v ≤ D)
    (hq : ∀ t ≤ D, 0 < (Fintype.card F : ℝ) - softError (Fintype.card F) t -
      2 ^ t * (Fintype.card W : ℝ)) :
    (injLabellings F G).Nonempty := by
  obtain ⟨y, hy, -⟩ := exists_extension hW G hdeg hq (A := ∅) (x := fun _ => 0)
    ⟨fun a ha => absurd ha (Finset.notMem_empty a), fun _ _ h1 => absurd h1 (Finset.notMem_empty _)⟩
  exact ⟨y, hy⟩

theorem card_fieldVertices_le (f₀ f₁ : FType) {Λ' : Type} [Fintype Λ'] (hΛ : Fintype.card Λ' ≤ 2) :
    (Fintype.card (f₀.Obj × f₁.Obj × Λ') : ℝ) ≤ 72 := by
  have h0 := card_obj_le f₀
  have h1 := card_obj_le f₁
  have : Fintype.card (f₀.Obj × f₁.Obj × Λ') ≤ 72 := by
    rw [Fintype.card_prod, Fintype.card_prod]
    calc Fintype.card f₀.Obj * (Fintype.card f₁.Obj * Fintype.card Λ') ≤ 6 * (6 * 2) :=
          Nat.mul_le_mul h0 (Nat.mul_le_mul h1 hΛ)
      _ = 72 := by norm_num
  exact_mod_cast this

/-! ## The upper and tail laws are defined above `81·10¹²` -/

/-- **The tail law is defined at every prime `p ≥ 81·10¹²`**, under Weil's bound (explicit form of
V1's `tailNonempty_of_large`). -/
theorem tailNonempty_explicit (p : ℕ) [Fact p.Prime] (hW : WeilBound (ZMod p))
    (hp : (81 * 10 ^ 12 : ℝ) ≤ p) : TailNonempty p := by
  have hq : (81 * 10 ^ 12 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ) := by rw [ZMod.card]; exact hp
  exact ⟨fun f₀ f₁ => injLabellings_nonempty_of_degree hW _ (fieldGraph_degree_two f₀ f₁)
      (threshold_twenty hq (Nat.cast_nonneg _) (card_fieldVertices_le f₀ f₁ (by simp))),
    fun f₀ f₁ => injLabellings_nonempty_of_degree hW _ (fieldGraph_degree_one f₀ f₁)
      (threshold_twenty hq (Nat.cast_nonneg _) (card_fieldVertices_le f₀ f₁ (by simp)))⟩

/-- **The upper block laws are defined on every block of primes `≥ 81·10¹²`**, under Weil's bound
at each prime (explicit form of V1's `upperNonempty_of_large`). -/
theorem upperNonempty_explicit {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ i, Fact (pr i).Prime] (hW : ∀ i, WeilBound (ZMod (pr i)))
    (hp : ∀ i, (81 * 10 ^ 12 : ℝ) ≤ pr i) : UpperNonempty pr :=
  ⟨fun f₀ f₁ i => (tailNonempty_explicit (pr i) (hW i) (hp i)).two f₀ f₁,
    fun f₀ f₁ i => (tailNonempty_explicit (pr i) (hW i) (hp i)).one f₀ f₁⟩

/-- **The threshold lies below `P₃ = 167·2⁴⁰`**, the least prime of the upper bands. -/
theorem threshold_le_P3 : (81 * 10 ^ 12 : ℝ) ≤ (P3 : ℝ) := by
  rw [show P3 = 167 * 2 ^ 40 from rfl]
  norm_num

theorem threshold_le_P4 : (81 * 10 ^ 12 : ℝ) ≤ (P4 : ℝ) := by
  have h : (P3 : ℝ) ≤ P4 := by exact_mod_cast P3_lt_P4.le
  exact threshold_le_P3.trans h

/-- **At every tail prime `q ≥ P₄`, the tail family is the tail law** (under H1). -/
theorem tailFamilyFrom_eq_tailLaw (hW : Target.Weil) {P : ℕ} (hP : P4 ≤ P) (q : ℕ) [NeZero q]
    [Fact q.Prime] (hPq : P ≤ q) :
    ∃ hne : TailNonempty q, tailFamilyFrom P q = tailLaw q hne := by
  have hq2 : q ≠ 2 := by
    intro h
    have : (81 * 10 ^ 12 : ℝ) ≤ q := threshold_le_P4.trans (by exact_mod_cast hP.trans hPq)
    rw [h] at this
    norm_num at this
  have hne := tailNonempty_explicit q (weilBound_of_target hW q hq2)
    (threshold_le_P4.trans (by exact_mod_cast hP.trans hPq))
  refine ⟨hne, ?_⟩
  unfold tailFamilyFrom
  rw [dite_eq_left (⟨Fact.out, hPq⟩ : q.Prime ∧ P ≤ q)]
  exact dite_eq_left hne

/-- **`lem:tail-law`(ii) at every tail prime** (except admissibility): under H1 and the validity
of the tail inputs at the tail primes (`lem:tail-law`(i), a hypothesis), the tail law exists at
every prime `p ≥ P₄` and is reflection positive at every cut of `𝔉`, square-affine invariant,
with uniform one-slot marginals. -/
theorem tailLaw_R1R3_all (hW : Target.Weil) (hV : TailInputsValid P4) (p : ℕ) [Fact p.Prime]
    (hp : P4 ≤ p) :
    ∃ hne : TailNonempty p,
      TheoremC.FamilyReflectionPositive (signedIntegral (tailLaw p hne).weight) ∧
      (∀ {s : ZMod p}, quadraticChar (ZMod p) s = 1 → ∀ (u : ZMod p) (H : (Slot → ZMod p) → ℝ),
        (tailLaw p hne).expect (fun z => H (fun v => s * z v + u)) = (tailLaw p hne).expect H) ∧
      HasUniformMarginals (tailLaw p hne) := by
  have hp' : (81 * 10 ^ 12 : ℝ) ≤ p := threshold_le_P4.trans (by exact_mod_cast hp)
  have hq2 : p ≠ 2 := by
    intro h
    rw [h] at hp'
    norm_num at hp'
  have hne := tailNonempty_explicit p (weilBound_of_target hW p hq2) hp'
  exact ⟨hne, tailLaw_R1R3 p hW hp hne fun hW' hp'' => hV p hp hne hW' hp''⟩

/-- **(R1)–(R3) for every upper block of primes `≥ 81·10¹²`** (`lem:upper-reference-rp`(ii), given
the validity of the band inputs (V1)–(V3) on the block, a hypothesis): the block laws exist, and
the upper block reference with weights passing the gates is reflection positive at every cut of
`𝔉`, with uniform one-slot marginals and square-affine invariance. Every upper band lies above
`P₃ > 81·10¹²` (`threshold_le_P3`). -/
theorem upperBlock_R1R3_explicit {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ)
    [∀ i, Fact (pr i).Prime] (hW : Target.Weil) (hp : ∀ i, (81 * 10 ^ 12 : ℝ) ≤ pr i)
    (W : UpperWeights) {r : ℝ} (hr : 0 < r) {ord res : FiveType.TwoCoord.FieldTy → CompletionInput}
    {k : PType → PType → ℝ} (hWOK : WeightsOK W ord res k)
    (hV : ∀ hne hW' hp', ValidInputs (upperBlockFieldLaws pr hne)
      (block_upperDatumHyp pr hW' hp' hne) r ord res k) :
    ∃ hne : UpperNonempty pr,
      TheoremC.FamilyReflectionPositive
          (signedIntegral (upperBlockReference pr hne W hr.le).weight) ∧
        HasUniformMarginals (upperBlockReference pr hne W hr.le) ∧
        ∀ (α β : BlockLabel pr), (∀ i, quadraticChar (ZMod (pr i)) (α i) = 1) →
          ∀ H : (Slot → BlockLabel pr) → ℝ,
            (upperBlockReference pr hne W hr.le).expect
                (fun z => H (fun v i => α i * z v i + β i)) =
              (upperBlockReference pr hne W hr.le).expect H := by
  have hp2 : ∀ i, pr i ≠ 2 := by
    intro i h
    have := hp i
    rw [h] at this
    norm_num at this
  have hW' : ∀ i, WeilBound (ZMod (pr i)) := fun i => weilBound_of_target hW (pr i) (hp2 i)
  have h20 : ∀ i, (2 : ℝ) ^ 20 ≤ pr i := fun i => le_trans (by norm_num) (hp i)
  have hne := upperNonempty_explicit pr hW' hp
  exact ⟨hne, upperBlock_R1R3 pr hW h20 hne W hr hWOK fun hW'' => hV hne hW'' h20⟩

end Sarkozy.PartVLaws

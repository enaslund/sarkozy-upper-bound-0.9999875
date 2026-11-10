module

public import Sarkozy.PaperFrame.Assembly
public import Sarkozy.Comparison.WrapAssembly

@[expose] public section

/-!
# The split of the coupled forms by the wrapping queries (`lem:record:wrap-expansion`)

In `lem:record:wrap-expansion` each coupled form splits as `I_{ν,𝒮} = ∑_{𝒲 ⊆ 𝒮} I_{ν,𝒮,𝒲}`,
`𝒲` the set of active queries whose interval shift wraps (`I_K → I_1`, i.e. `b = 0` in
`ℤ/Kℤ`, whose least positive residue is `K`). The interval shift is the sum of its wrapping
and non-wrapping parts (`shift_split`), so every query transition splits
(`piKron_coordTransition_split`), and the product over the active queries expands
(`piKron_active_split`). `paper_wrap_hexp` is the hypothesis `hexp` of
`Sarkozy.Comparison.wrap_summation` for the paper's objects:

`J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} ∑_{𝒲 ⊆ 𝒮} I_{ν,𝒮,𝒲}`.
-/

open Finset Function
open scoped BigOperators Matrix

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison

section Shift

variable (K : ℕ) [NeZero K]

/-- The wrapping part of the interval shift: from `I_K` (`b = 0`) to `I_1`. -/
noncomputable def wrapShift : Matrix (ZMod K) (ZMod K) ℝ :=
  fun b b' => if b = 0 then shiftMatrix (1 : ZMod K) b b' else 0

/-- The non-wrapping part of the interval shift: `I_b → I_{b+1}` for `b ≠ K`. -/
noncomputable def nowrapShift : Matrix (ZMod K) (ZMod K) ℝ :=
  fun b b' => if b = 0 then 0 else shiftMatrix (1 : ZMod K) b b'

omit [NeZero K] in
theorem shift_split : shiftMatrix (1 : ZMod K) = wrapShift K + nowrapShift K := by
  ext b b'
  simp only [Matrix.add_apply, wrapShift, nowrapShift]
  split_ifs <;> simp

/-- The wrap at the interval `I_b` happens exactly at the least positive residue `K`. -/
theorem wrap_iff_leastPosRep (b : ZMod K) : b = 0 ↔ leastPosRep b = K := by
  unfold leastPosRep
  constructor
  · intro h
    subst h
    simp
  · intro h
    split_ifs at h with h0
    · exact (ZMod.val_eq_zero b).mp h0
    · exact absurd h (Nat.ne_of_lt (ZMod.val_lt b))

end Shift

section Query

variable (K : ℕ) [NeZero K] {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

/-- The coordinate transitions of a query with the interval factor replaced by `A`. -/
noncomputable def coordTransitionWith (A : Matrix (ZMod K) (ZMod K) ℝ)
    (μ : ∀ q, ZMod (pr q ^ h q) → ℝ) :
    ∀ j, Matrix (CoordSpace K pr h j) (CoordSpace K pr h j) ℝ
  | none => A
  | some q => (convMatrix (μ q) : Matrix (ZMod (pr q ^ h q)) (ZMod (pr q ^ h q)) ℝ)

omit [NeZero K] [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- A query transition splits into its wrapping and non-wrapping parts. -/
theorem piKron_coordTransition_split (μ : ∀ q, ZMod (pr q ^ h q) → ℝ) :
    piKron (coordTransition K pr h μ) =
      piKron (coordTransitionWith K pr h (wrapShift K) μ) +
        piKron (coordTransitionWith K pr h (nowrapShift K) μ) := by
  ext x y
  simp only [piKron_apply, Matrix.add_apply, Fintype.prod_option]
  have hs : coordTransition K pr h μ none (x none) (y none) =
      wrapShift K (x none) (y none) + nowrapShift K (x none) (y none) := by
    change shiftMatrix (1 : ZMod K) (x none) (y none) = _
    rw [shift_split]
    rfl
  rw [hs, add_mul]
  rfl

end Query

section Active

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]

omit [∀ e, Fintype (Ω e)] in
/-- The product over the active queries expands over the subsets `𝒲 ⊆ 𝒮` of wrapping
queries: `⊗_e (e ∈ 𝒮 ? T_e^w + T_e^{nw} : P_e) = ∑_{𝒲 ⊆ 𝒮} ⊗_e (e ∈ 𝒲 ? T_e^w : e ∈ 𝒮 ? T_e^{nw} : P_e)`. -/
theorem piKron_active_split (Tw Tnw Pm : ∀ e, Matrix (Ω e) (Ω e) ℝ) (S : Finset E) :
    piKron (fun e => if e ∈ S then Tw e + Tnw e else Pm e) =
      ∑ W ∈ S.powerset, piKron (fun e => if e ∈ W then Tw e else if e ∈ S then Tnw e else Pm e) := by
  ext x y
  simp only [piKron_apply, Matrix.sum_apply]
  rw [← prod_mul_prod_compl S]
  have h1 : ∏ e ∈ S, (if e ∈ S then Tw e + Tnw e else Pm e) (x e) (y e) =
      ∏ e ∈ S, (Tw e (x e) (y e) + Tnw e (x e) (y e)) :=
    prod_congr rfl fun e he => by rw [ite_eq_left he, Matrix.add_apply]
  have h2 : ∏ e ∈ Sᶜ, (if e ∈ S then Tw e + Tnw e else Pm e) (x e) (y e) =
      ∏ e ∈ Sᶜ, Pm e (x e) (y e) :=
    prod_congr rfl fun e he => by rw [ite_eq_right (mem_compl.mp he)]
  rw [h1, h2, prod_add, sum_mul]
  apply sum_congr rfl
  intro W hW
  have hWS := mem_powerset.mp hW
  rw [← prod_mul_prod_compl S (fun e => (if e ∈ W then Tw e else if e ∈ S then Tnw e else Pm e)
    (x e) (y e))]
  congr 1
  · rw [← prod_filter_mul_prod_filter_not S (fun e => e ∈ W)]
    have hf1 : S.filter (fun e => e ∈ W) = W := by
      ext e; simp only [mem_filter]; exact ⟨fun h => h.2, fun h => ⟨hWS h, h⟩⟩
    have hf2 : S.filter (fun e => e ∉ W) = S \ W := by
      ext e; simp [mem_filter, mem_sdiff]
    rw [hf1, hf2]
    congr 1
    · exact prod_congr rfl fun e he => by rw [ite_eq_left he]
    · exact prod_congr rfl fun e he => by
        rw [ite_eq_right (mem_sdiff.mp he).2, ite_eq_left (mem_sdiff.mp he).1]
  · exact prod_congr rfl fun e he => by
      have heS := mem_compl.mp he
      rw [ite_eq_right (fun hW' => heS (hWS hW')), ite_eq_right heS]

end Active

section Paper

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- The coupled form `I_{ν,𝒮,𝒲}` with the wrapping queries `𝒲 ⊆ 𝒮` (WP-S operator form). -/
noncomputable def wrapForm (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (u w : E → reservedCut.Half)
    (ν : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ)
    (S W : Finset E) : ℝ :=
  (FiniteLaw.uniform (E → ∀ j, CoordSpace blockScale pr h j)).expect (fun ω =>
    reservedCut.form (tensorLaw (ν L))
      (productHalf u (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) ω)
      (act (piKron (fun e => if e ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (μ e))
          else if e ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (μ e))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)))
        (productHalf w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A)) ω))

/-- **The hypothesis `hexp` of `wrap_summation` for the paper's objects**:
`J_ν − 2^k Y_ν = ∑_{𝒮 ≠ ∅} (−1)^{|𝒮|} 2^{k−|𝒮|} ∑_{𝒲 ⊆ 𝒮} I_{ν,𝒮,𝒲}`. -/
theorem paper_wrap_hexp (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ) :
    signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => atomInput m₀ p pr h hcop L A e)
        (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A -
        2 ^ Fintype.card E * energyComparison ν (atomLift m₀ p) L A =
      ∑ S ∈ (univ : Finset E).powerset.filter (fun S => S ≠ ∅),
        (-1 : ℝ) ^ S.card * 2 ^ (Fintype.card E - S.card) *
          ∑ W ∈ S.powerset, wrapForm m₀ p pr h hcop μ u w ν L A S W := by
  rw [paper_signedIndexForm_sub_eq m₀ p pr h hcop μ hμ hμ1 t hnorm u w hu hw ν L A]
  apply sum_congr rfl
  intro S _
  congr 1
  unfold wrapForm
  rw [← expect_finset_sum]
  apply FiniteLaw.expect_congr
  intro ω
  have hsplit : piKron (fun e => if e ∈ S then piKron (coordTransition blockScale pr h (μ e))
      else meanMatrix (∀ j, CoordSpace blockScale pr h j)) =
      ∑ W ∈ S.powerset, piKron (fun e => if e ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (μ e))
        else if e ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (μ e))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) := by
    simp_rw [piKron_coordTransition_split]
    exact piKron_active_split _ _ _ S
  rw [hsplit, act_sum_left, Finset.sum_apply, ← cutBilin_apply, map_sum]
  simp only [cutBilin_apply]

/-- **The wrap summation for the paper's objects** (`lem:record:wrap-expansion`): if every
non-wrapping coupled form `I_{ν,𝒮,𝒲}` (`𝒲 ≠ 𝒮`) is at most `r` in absolute value and every
fully wrapping one `I_{ν,𝒮,𝒮}` at most `(B' x^{|𝒮|} + ε) Y + r'`, then
`|J_ν − 2^k Y_ν| ≤ B'[(2 + x)^k − 2^k] Y + 3^k ε Y + 4^k r + 3^k r'`
(`Sarkozy.Comparison.wrap_summation` with `paper_wrap_hexp`). -/
theorem paper_wrap_bound (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ)
    {Y B' x ε r r' : ℝ} (hY : 0 ≤ Y) (hε : 0 ≤ ε) (hr : 0 ≤ r) (hr' : 0 ≤ r')
    (hnon : ∀ S W, W ⊆ S → W ≠ S → |wrapForm m₀ p pr h hcop μ u w ν L A S W| ≤ r)
    (hwrap : ∀ S, S ≠ ∅ → |wrapForm m₀ p pr h hcop μ u w ν L A S S| ≤
      (B' * x ^ S.card + ε) * Y + r') :
    |signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
        (fun L A e => atomInput m₀ p pr h hcop L A e)
        (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A -
        2 ^ Fintype.card E * energyComparison ν (atomLift m₀ p) L A| ≤
      B' * ((2 + x) ^ Fintype.card E - 2 ^ Fintype.card E) * Y +
        3 ^ Fintype.card E * ε * Y + 4 ^ Fintype.card E * r + 3 ^ Fintype.card E * r' :=
  wrap_summation (wrapForm m₀ p pr h hcop μ u w ν L A) hY hε hr hr'
    (paper_wrap_hexp m₀ p pr h hcop μ hμ hμ1 t hnorm u w hu hw ν L A) hnon hwrap

end Paper

end Sarkozy.PaperFrame

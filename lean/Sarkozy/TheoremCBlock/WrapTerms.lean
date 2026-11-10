module

public import Sarkozy.TheoremCBlock.Main
public import Sarkozy.TheoremC.WrapTerms

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCBlock

open Sarkozy.TheoremC
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ## Brackets add -/

/-! ## Stage 2: matrices -/

/-! ## Stage 2: the reduction of the fully wrapping term -/

section Reduction

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- The fixed-interval source inputs of the wrapping term of `𝒮`: `g^{I_K, M₀, s_e}` (interval
coordinate `b_e = 0`, i.e. `I_K`) for `e ∈ 𝒮`, and `F_A` for `e ∉ 𝒮`. -/
noncomputable def wrapSourceInput (L : ℕ) (A : Finset ℤ) (S : Finset E) (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) (x : ∀ b, BlockLabel m₀ blk p L b) : ℝ :=
  if e ∈ S then blockInput m₀ blk p pr h hcop L A e
    (Function.update η none ((0 : ZMod blockScale) : CoordSpace blockScale pr h none)) x
  else blockLift m₀ blk p L A x

/-- The fixed-interval target inputs: `g^{I_1, M₀, s_e}` (`b_e = 1`) for `e ∈ 𝒮`, `F_A`
otherwise. -/
noncomputable def wrapTargetInput (L : ℕ) (A : Finset ℤ) (S : Finset E) (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) (x : ∀ b, BlockLabel m₀ blk p L b) : ℝ :=
  if e ∈ S then blockInput m₀ blk p pr h hcop L A e
    (Function.update η none ((1 : ZMod blockScale) : CoordSpace blockScale pr h none)) x
  else blockLift m₀ blk p L A x

/-- The half-function `X'` of the wrapping term: the fixed-interval source inputs at the
sources `u_e`, `F_A` elsewhere. -/
noncomputable def wrapSourceHalf (u : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    (E → ∀ j, CoordSpace blockScale pr h j) →
        (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ :=
  productHalf u (wrapSourceInput m₀ blk p pr h hcop L A S) (blockLift m₀ blk p L A)

/-- The half-function `Y'` of the wrapping term, at the reflected targets `ι v_e`. -/
noncomputable def wrapTargetHalf (w : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    (E → ∀ j, CoordSpace blockScale pr h j) →
        (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ :=
  productHalf w (wrapTargetInput m₀ blk p pr h hcop L A S) (blockLift m₀ blk p L A)

omit [Fintype Bk] [DecidableEq Bk] in
theorem act_source_half (u : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ) (S : Finset E) :
    act (piKron (fun e => qInactive blockScale pr h S e * qEval blockScale pr h S 0 e))
        (productHalf u (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A)) =
      wrapSourceHalf m₀ blk p pr h hcop u L A S := by
  rw [act_productHalf]
  unfold wrapSourceHalf
  congr 1
  funext e ωe y
  unfold wrapSourceInput qInactive qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, Matrix.one_mul]
    exact piKron_intervalMat_eval_mulVec blockScale pr h 0 _ ωe
  · simp only [he, ↓reduceIte, Matrix.mul_one]
    rw [meanMatrix_mulVec, ← expect_blockInput m₀ blk p pr h hcop L A e y,
      FiniteLaw.expect_uniform, div_eq_inv_mul]

omit [Fintype Bk] [DecidableEq Bk] in
theorem act_target_half (w : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ) (S : Finset E) :
    act (piKron (fun e => qInactive blockScale pr h S e * qEval blockScale pr h S 1 e))
        (productHalf w (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A)) =
      wrapTargetHalf m₀ blk p pr h hcop w L A S := by
  rw [act_productHalf]
  unfold wrapTargetHalf
  congr 1
  funext e ωe y
  unfold wrapTargetInput qInactive qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, Matrix.one_mul]
    exact piKron_intervalMat_eval_mulVec blockScale pr h 1 _ ωe
  · simp only [he, ↓reduceIte, Matrix.mul_one]
    rw [meanMatrix_mulVec, ← expect_blockInput m₀ blk p pr h hcop L A e y,
      FiniteLaw.expect_uniform, div_eq_inv_mul]

/-- **The reduction of the fully wrapping term**: all `|𝒮|` intervals wrap with
probability `K^{-|𝒮|}`, and then the term is the coupled form of the fixed-interval
half-functions under the residue coupling `𝒯'`:
`I_{ν,𝒮,𝒮} = K^{-|𝒮|} E_ω⟨X'_ω, C_ι(ν) (𝒯' Y')_ω⟩`. -/
theorem wrapForm_eq (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (u w : E → reservedCut.Half)
    (ν : ∀ L b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    blockWrapForm m₀ blk p pr h hcop μ u w ν L A S S =
      ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
        pairing (reservedCut.matrix (tensorLaw (ν L))) (wrapSourceHalf m₀ blk p pr h hcop u L A S)
          (act (wrapCoupling pr h S μ) (wrapTargetHalf m₀ blk p pr h hcop w L A S)) := by
  have hW : (fun e => if e ∈ S then
      piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (μ e))
    else if e ∈ S then piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (μ e))
    else meanMatrix (∀ j, CoordSpace blockScale pr h j)) = qWrap blockScale pr h S μ := by
    funext e
    unfold qWrap
    by_cases he : e ∈ S <;> simp [he]
  have h1 : blockWrapForm m₀ blk p pr h hcop μ u w ν L A S S =
      pairing (reservedCut.matrix (tensorLaw (ν L)))
        (productHalf u (fun e => blockInput m₀ blk p pr h hcop L A e) (blockLift m₀ blk p L A))
        (act (piKron (qWrap blockScale pr h S μ))
          (productHalf w (fun e => blockInput m₀ blk p pr h hcop L A e)
              (blockLift m₀ blk p L A))) := by
    unfold blockWrapForm
    rw [hW]
    exact expect_form_eq_pairing (Ωc := fun _ => CoordSpace blockScale pr h) reservedCut
      (tensorLaw (ν L)) _ _
  have hA : piKron (qWrap blockScale pr h S μ) = piKron (qDiag blockScale pr h S) *
      piKron (qCoupling blockScale pr h S μ) * piKron (qEval blockScale pr h S 1) := by
    rw [piKron_mul, piKron_mul]
    congr 1
    funext e
    exact qWrap_eq blockScale pr h S μ e
  have hB : piKron (qCoupling blockScale pr h S μ) =
      piKron (qMean blockScale pr h S) * piKron (qCoupling blockScale pr h S μ) := by
    rw [piKron_mul]
    congr 1
    funext e
    exact qCoupling_eq_mean_mul blockScale pr h S μ e
  have hC : piKron (qMean blockScale pr h S) * piKron (qDiag blockScale pr h S) *
      piKron (qEval blockScale pr h S 0) =
      ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card • piKron (qEval blockScale pr h S 0) := by
    rw [piKron_mul, piKron_mul]
    have : (fun e => qMean blockScale pr h S e * qDiag blockScale pr h S e *
        qEval blockScale pr h S 0 e) =
        fun e => (if e ∈ S then (Fintype.card (ZMod blockScale) : ℝ)⁻¹ else 1) •
          qEval blockScale pr h S 0 e :=
      funext fun e => qMean_qDiag_qEval blockScale pr h S e
    rw [this, piKron_smul]
    congr 1
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hD : piKron (qDiag blockScale pr h S) =
      piKron (qDiag blockScale pr h S) * piKron (qEval blockScale pr h S 0) := by
    rw [piKron_mul]
    congr 1
    funext e
    exact qDiag_eq_mul_qEval blockScale pr h S e
  have hDt : (piKron (qDiag blockScale pr h S))ᵀ = piKron (qDiag blockScale pr h S) := by
    rw [piKron_transpose]
    congr 1
    funext e
    exact qDiag_transpose blockScale pr h S e
  have hMt : (piKron (qMean blockScale pr h S))ᵀ = piKron (qMean blockScale pr h S) := by
    rw [piKron_transpose]
    congr 1
    funext e
    exact qMean_transpose blockScale pr h S e
  have hIt : (piKron (qInactive blockScale pr h S))ᵀ = piKron (qInactive blockScale pr h S) := by
    rw [piKron_transpose]
    congr 1
    funext e
    exact qInactive_transpose blockScale pr h S e
  have hF : piKron (qCoupling blockScale pr h S μ) = piKron (qInactive blockScale pr h S) *
      piKron (qCoupling blockScale pr h S μ) * piKron (qInactive blockScale pr h S) := by
    rw [piKron_mul, piKron_mul]
    congr 1
    funext e
    exact qCoupling_eq_inactive blockScale pr h S μ e
  have e0 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ,
      act (piKron (qWrap blockScale pr h S μ)) Z = act (piKron (qDiag blockScale pr h S))
        (act (piKron (qCoupling blockScale pr h S μ)) (act (piKron
            (qEval blockScale pr h S 1)) Z)) :=
    fun Z => by rw [act_act, act_act, ← hA]
  have e1 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ,
      act (piKron (qDiag blockScale pr h S)) Z = act (piKron (qDiag blockScale pr h S))
        (act (piKron (qEval blockScale pr h S 0)) Z) :=
    fun Z => by rw [act_act, ← hD]
  have e2 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ,
      act (piKron (qCoupling blockScale pr h S μ)) Z = act (piKron (qMean blockScale pr h S))
        (act (piKron (qCoupling blockScale pr h S μ)) Z) :=
    fun Z => by rw [act_act, ← hB]
  have e3 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ,
      act (piKron (qCoupling blockScale pr h S μ)) Z = act (piKron (qInactive blockScale pr h S))
        (act (piKron (qCoupling blockScale pr h S μ)) (act (piKron
            (qInactive blockScale pr h S)) Z)) :=
    fun Z => by rw [act_act, act_act, ← hF]
  rw [h1, e0, pairing_act_right, hDt, e1, e2, pairing_act_right, hMt, act_act, act_act, hC,
    act_smul, pairing_smul_left, e3, pairing_act_right, hIt,
    act_act (piKron (qInactive blockScale pr h S)) (piKron (qEval blockScale pr h S 0)),
    act_act (piKron (qInactive blockScale pr h S)) (piKron (qEval blockScale pr h S 1)),
    piKron_mul, piKron_mul, act_source_half, act_target_half]
  rfl

/-- The single-half random-inclusion energy `V_{⊗M}(Z) = E_𝒥 E_ω Q_{⊗M}(Z^𝒥_ω, Z^𝒥_ω)` of a
half-function `Z`, with the revelation of (CP0)(d) (the interval coordinates are always
revealed, the residue depths have the tails `t`), as in `inclusionEnergyL` of
`Sarkozy.Comparison.ConcreteFrame`. For the fixed-interval half-functions the revealed
interval coordinates of the active queries and the coordinates of the inactive queries do
not enter (the half-functions do not depend on them), so this is the paper's `V'_s`; that
remark is not used in the proofs. -/
noncomputable def wrapInclusionEnergy (L : ℕ)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (M : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Z : (E → ∀ j, CoordSpace blockScale pr h j) →
        (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ) :
    ℝ :=
  (queryLaw (fun (_ : E) => coordChain blockScale pr h) (fun e => coordTails blockScale pr h
      (t e))).expect
    (fun J => (FiniteLaw.uniform (E → ∀ j, CoordSpace blockScale pr h j)).expect (fun ω =>
      reservedCut.form (tensorLaw M)
        (queryReveal (fun (_ : E) => coordChain blockScale pr h) J Z ω)
        (queryReveal (fun (_ : E) => coordChain blockScale pr h) J Z ω)))

theorem wrapInclusionEnergy_eq (L : ℕ) (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (M : ∀ b : BlockAtom Bk J L, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Z : (E → ∀ j, CoordSpace blockScale pr h j) →
        (reservedCut.Half → ∀ b, BlockLabel m₀ blk p L b) → ℝ) :
    (queryRevelation (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (t e))).energy (reservedCut.matrix (tensorLaw M)) Z =
      wrapInclusionEnergy m₀ blk p pr h L t M Z := by
  rw [queryRevelation_energy]
  unfold queryEnergy wrapInclusionEnergy
  apply FiniteLaw.expect_congr
  intro J
  exact (expect_form_eq_pairing (Ωc := fun _ => CoordSpace blockScale pr h) reservedCut _ _ _).symm

/-- **`lem:record:common-mean`(b) for the fully wrapping term**: with a per-atom bracket
`(M_𝔟 ν_𝔟; ν_𝔟* M_𝔟) ⪰_ι 0`,
`|I_{ν,𝒮,𝒮}| ≤ K^{-|𝒮|} V'_L^{1/2} V'_R^{1/2}`, where `V'_L`, `V'_R` are the single-half
random-inclusion energies under `⊗_𝔟 M_𝔟` of the fixed-interval half-functions. -/
theorem abs_wrapForm_le (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (ν M : ∀ L b, ((Slot → BlockLabel m₀ blk p L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (M L b) (ν L b) (M L b)) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    |blockWrapForm m₀ blk p pr h hcop μ u w ν L A S S| ≤
      ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
        (Real.sqrt (wrapInclusionEnergy m₀ blk p pr h L t (M L)
            (wrapSourceHalf m₀ blk p pr h hcop u L A S)) *
          Real.sqrt (wrapInclusionEnergy m₀ blk p pr h L t (M L)
              (wrapTargetHalf m₀ blk p pr h hcop w L A S))) := by
  have hG : (Matrix.fromBlocks (reservedCut.matrix (tensorLaw (M L)))
      (reservedCut.matrix (tensorLaw (ν L))) (reservedCut.matrix (tensorLaw (ν L)))ᵀ
      (reservedCut.matrix (tensorLaw (M L)))).PosSemidef :=
    (reservedCut.bracket_iff_blockMatrix_posSemidef _ _ _).mp (ReflectionCut.Bracket.tensor (hbr L))
  have hop := wrapCoupling_sectorOperator pr h S μ hμ hμ1 t hnorm
  have hb := form_le_energies
    (queryRevelation (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (t e)))
    (queryWeight_nonneg _ _) (fun s => (queryRevelation_prob _ _ s).symm.le) hop hG
    (wrapSourceHalf m₀ blk p pr h hcop u L A S) (wrapTargetHalf m₀ blk p pr h hcop w L A S)
  rw [wrapInclusionEnergy_eq, wrapInclusionEnergy_eq] at hb
  have hk : 0 ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card := by positivity
  rw [wrapForm_eq, abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left hb hk

end Reduction

/-! ## Stage 1: the envelope of the wrapping terms -/

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] (D : ComparisonData a m₀ blk p pr h E)

/-- The law `M_𝔟 = Ñ_𝔟 + ∑_t (π̃^s_{𝔟,t} D^s_{𝔟,t} + π̃^a_{𝔟,t} D^a_{𝔟,t})` dominating `ν_𝔟`
in the wrapping terms. -/
noncomputable def wrapEnvelope (L : ℕ) (b : BlockAtom Bk J L) : AtomMeasure m₀ blk p L b :=
  D.GB.N L b + ∑ t, (D.CL.πt L b t .sym • D.CL.D L b t .sym +
    D.CL.πt L b t .skew • D.CL.D L b t .skew)

omit [DecidableEq P] in
/-- **The brackets of (CP3) and (CP4) add up**: `(M_𝔟 ν_𝔟; ν_𝔟* M_𝔟) ⪰_ι 0`. -/
theorem wrapEnvelope_bracket (L : ℕ) (b : BlockAtom Bk J L) :
    reservedCut.Bracket (D.wrapEnvelope L b) (D.CL.ν L b) (D.wrapEnvelope L b) := by
  rw [D.nu_eq L b]
  unfold wrapEnvelope
  apply bracket_add (D.GB.bracket L b)
  apply bracket_sum
  intro t _
  exact bracket_add (D.CL.bracket L b t .sym) (D.CL.bracket L b t .skew)

omit [DecidableEq P] in
/-- The price of `M − Ñ` is at most `S + A`. -/
theorem wrapEnvelope_price (L : ℕ) :
    ∑ b, ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew) ≤ D.CL.S + D.CL.A := by
  have h : ∑ b, ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew) =
      ∑ b, symTotal (D.CL.π L) b + ∑ b, skewTotal (D.CL.π L) b := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro b _
    rw [sum_add_distrib]
    rfl
  rw [h]
  exact add_le_add (D.CL.S_total L) (D.CL.A_total L)

/-! ## Stage 3: the fixed-interval envelope energies give the wrapping-term bound -/

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- `V'_L(𝒮)`: the single-half random-inclusion energy under `⊗_𝔟 M_𝔟` of the fixed-interval
source half-function of `𝒮`. -/
noncomputable def wrapInclusionEnergyL (S : Finset E) (L : ℕ) (A : Finset ℤ) : ℝ :=
  wrapInclusionEnergy m₀ blk p pr h L D.S.index.t (D.wrapEnvelope L)
    (wrapSourceHalf m₀ blk p pr h hcop D.S.Q.u L A S)

/-- `V'_R(𝒮)`: the same for the fixed-interval target half-function. -/
noncomputable def wrapInclusionEnergyR (S : Finset E) (L : ℕ) (A : Finset ℤ) : ℝ :=
  wrapInclusionEnergy m₀ blk p pr h L D.S.index.t (D.wrapEnvelope L)
    (wrapTargetHalf m₀ blk p pr h hcop D.S.Q.w L A S)

/-- The fixed-interval factor `κ_e^{2θ/d} R_I = K^{2θ/d} R_I` of one active query
(`lem:envelope-energy` with `κ_e = K`, `d = 72`). -/
noncomputable def fixedIntervalFactor : ℝ :=
  (blockScale : ℝ) ^ (2 * densityExponent / 72) * D.S.index.R_I

/-- **`lem:envelope-energy` at fixed intervals** (`κ_e = K`) for `M_𝔟 = Ñ_𝔟 + Q_𝔟`,
`Q_𝔟 = ∑_t (π̃^s D^s + π̃^a D^a)` of total price `T_Q ≤ S + A` (`wrapEnvelope_price`), robustly:
for every nonempty `𝒮`, `V'_L(𝒮), V'_R(𝒮) ≤ (B e^{S+A} (K^{2θ/d} R_I)^{|𝒮|} + o(1)) Y`. -/
def FixedIntervalEnvelopeEnergies : Prop :=
  ∃ εf : ℕ → ℝ, (∀ L, 0 ≤ εf L) ∧ Tendsto εf atTop (𝓝 0) ∧ ∃ cf : ℝ, 0 ≤ cf ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      D.wrapInclusionEnergyL hcop S L A ≤
          (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A ∧
      D.wrapInclusionEnergyR hcop S L A ≤
          (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A)

omit [DecidableEq P] in
/-- `K^{-1} · K^{2θ/d} R_I = R_I K^{2θ/d − 1}`, the ratio of `W`. -/
theorem inv_card_mul_fixedIntervalFactor :
    (Fintype.card (ZMod blockScale) : ℝ)⁻¹ * D.fixedIntervalFactor = D.wrapRatio := by
  have hK : (blockScale : ℝ) ≠ 0 := by norm_num [blockScale]
  unfold fixedIntervalFactor wrapRatio
  rw [ZMod.card, Real.rpow_sub_one hK]
  field_simp

/-- **The wrapping terms from the fixed-interval envelope energies**:
`lem:record:common-mean`(b) (`abs_wrapForm_le`), the bracket of `M_𝔟` (`wrapEnvelope_bracket`)
and `lem:envelope-energy` at fixed intervals give the hypothesis `WrappingTerms` of Theorem C,
with the same relative error and remainder constant. -/
theorem wrappingTerms_of_envelope (hf : D.FixedIntervalEnvelopeEnergies hcop) :
    D.WrappingTerms hcop := by
  obtain ⟨εf, hεf0, hεf, cf, hcf, hV⟩ := hf
  refine ⟨εf, hεf0, hεf, cf, hcf, ?_⟩
  filter_upwards [hV] with L hL
  intro C hC hind A hA hcounter S hS
  obtain ⟨hVL, hVR⟩ := hL C hC hind A hA hcounter S hS
  have hY0 : 0 ≤ D.Y L A := TheoremCParam.nonneg_of_counterexample hC hcounter
  have hF0 : 0 ≤ D.fixedIntervalFactor :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) D.S.index.hR_I
  have hr0 : 0 ≤ remainder cf L A := remainder_nonneg' hcf L A
  have hBd0 : 0 ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) *
      D.Y L A + remainder cf L A := by
    have := D.B_nonneg
    have := hεf0 L
    positivity
  have hab := abs_wrapForm_le m₀ blk p pr h hcop D.S.index.μ D.S.index.hμ D.S.index.hμ1 D.S.index.t
    D.S.index.hnorm D.S.Q.u D.S.Q.w D.CL.ν D.wrapEnvelope D.wrapEnvelope_bracket L A S
  have hsq : Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
      Real.sqrt (D.wrapInclusionEnergyR hcop S L A) ≤
      (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
        remainder cf L A := by
    calc Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
          Real.sqrt (D.wrapInclusionEnergyR hcop S L A)
        ≤ Real.sqrt ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) *
              D.Y L A + remainder cf L A) *
            Real.sqrt ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card +
              εf L) * D.Y L A + remainder cf L A) :=
          mul_le_mul (Real.sqrt_le_sqrt hVL) (Real.sqrt_le_sqrt hVR) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hBd0
  have hk0 : 0 ≤ (Fintype.card (ZMod blockScale) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hk1 : (Fintype.card (ZMod blockScale) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Fintype.card_pos
  have hkS : ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card ≤ 1 := pow_le_one₀ hk0 hk1
  have hkS0 : 0 ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card := pow_nonneg hk0 _
  calc |blockWrapForm m₀ blk p pr h hcop D.S.index.μ D.S.Q.u D.S.Q.w D.CL.ν L A S S|
      ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
          (Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
            Real.sqrt (D.wrapInclusionEnergyR hcop S L A)) := hab
    _ ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
          ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A) := mul_le_mul_of_nonneg_left hsq hkS0
    _ = D.B * Real.exp (D.CL.S + D.CL.A) *
            ((Fintype.card (ZMod blockScale) : ℝ)⁻¹ * D.fixedIntervalFactor) ^ S.card * D.Y L A +
          ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
              (εf L * D.Y L A + remainder cf L A) := by
        rw [mul_pow]
        ring
    _ ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.wrapRatio ^ S.card + εf L) * D.Y L A +
          remainder cf L A := by
        rw [D.inv_card_mul_fixedIntervalFactor]
        have h1 : ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
            (εf L * D.Y L A + remainder cf L A) ≤ εf L * D.Y L A + remainder cf L A :=
          mul_le_of_le_one_left (add_nonneg (mul_nonneg (hεf0 L) hY0) hr0) hkS
        linarith

end ComparisonData

end Sarkozy.TheoremCBlock

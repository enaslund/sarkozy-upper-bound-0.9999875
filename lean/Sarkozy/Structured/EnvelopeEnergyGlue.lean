module

public import Sarkozy.Structured.SharpFirstGlue
public import Sarkozy.TheoremC.WrapTerms

/-!
# Theorem C glue: `EnvelopeEnergies` from per-term bounds (`lem:envelope-energy`)

WP-FI's `Sarkozy.TheoremC.ComparisonData.EnvelopeEnergies` (`Sarkozy/TheoremC/Main.lean`)
asks for `V_L, V_R ≤ (B e^T R_I^k + o(1)) Y + c L^{-1/825} α` at the counterexamples, where
`V_s = E_𝒥 E_ω Q_{⊗M_s}(Z^𝒥_ω, Z^𝒥_ω)` is the random-inclusion energy of the matching
envelope `M_{s,𝔟} = Ñ_𝔟 + ∑_i c_{s,𝔟,i} κ_{s,𝔟,i}` (CP6). The paper's proof of
`lem:envelope-energy` expands `⊗(Ñ + Q)` into subsets. It bounds each term by (E1) under the
bracket, with the conductor price `Π_{𝒥,ω}` of the index, and averages with
`E Π = R_I^k` (`lem:hyb:moment`).

* `form_tensorLaw_add_eq_sum`: the cut form of `⊗(N + Q)` is the sum over the subsets of
  the cut forms of the subset terms.
* `inclusion_energy_le_of_terms`: the abstract summation. If every subset term satisfies
  `|Q_f| ≤ (B+z) Π Y ∏_{𝔟∈f} u_𝔟 + r_f`, `∑_𝔟 u_𝔟 ≤ T`, `E Π ≤ Π̄` and `E ∑_f r_f ≤ c'`, then
  `E E Q_{⊗(N+Q)}(Z, Z) ≤ (B+z) e^T Π̄ Y + c'`. Unlike `envelope_energy_le_paper`, remainders
  are allowed in the terms.
* **`envelopeEnergies_of_terms`**: `D.EnvelopeEnergies hcop` from the per-term bounds and the
  moment, for both envelopes, at the counterexamples.
-/

@[expose] public section

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.Structured

open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.IndexSupport

section Abstract

variable {Jb : Type*} [Fintype Jb] [DecidableEq Jb] {X : Jb → Type*} [∀ b, Fintype (X b)]
  [∀ b, DecidableEq (X b)]

/-- The cut form of `⊗(N + Q)` is the sum over the subsets of the cut forms of the terms. -/
theorem form_tensorLaw_add_eq_sum (N Qr : ∀ b, ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ)
    (F G : (reservedCut.Half → ∀ b, X b) → ℝ) :
    reservedCut.form (tensorLaw fun b => N b + Qr b) F G =
      ∑ f : Jb → Bool, reservedCut.form (tensorLaw fun b => if f b then Qr b else N b) F G := by
  unfold ReflectionCut.form
  rw [tensorLaw_add_eq_sum, LinearMap.sum_apply]

/-- **The summed envelope energy with remainders** (`lem:envelope-energy`, steps 2–3): if every
subset term satisfies `|Q_f(Z, Z)| ≤ (B+z) Π Y ∏_{𝔟∈f} u_𝔟 + r_f`, then
`E E Q_{⊗(N+Q)}(Z, Z) ≤ (B+z) e^T Π̄ Y + c'`, for `∑ u ≤ T`, `E Π ≤ Π̄` and `E ∑_f r_f ≤ c'`. -/
theorem inclusion_energy_le_of_terms {Ωq Ωi : Type*} [Fintype Ωq] [Fintype Ωi]
    (PJ : FiniteLaw Ωq) (PΩ : FiniteLaw Ωi) (N Qr : ∀ b, ((Slot → X b) → ℝ) →ₗ[ℝ] ℝ)
    (Zr : Ωq → Ωi → (reservedCut.Half → ∀ b, X b) → ℝ) (u : Jb → ℝ) (hu : ∀ b, 0 ≤ u b)
    {Bz Y TQ Pbar c' : ℝ} (hBz : 0 ≤ Bz) (hY : 0 ≤ Y) (hTQ : ∑ b, u b ≤ TQ)
    (Pj : Ωq → Ωi → ℝ) (r : Ωq → Ωi → (Jb → Bool) → ℝ)
    (hterm : ∀ J ω (f : Jb → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then Qr b else N b) (Zr J ω) (Zr J ω)| ≤
        Bz * Pj J ω * Y * ∏ b, (if f b then u b else 1) + r J ω f)
    (hPj : ∀ J ω, 0 ≤ Pj J ω)
    (hmoment : PJ.expect (fun J => PΩ.expect (fun ω => Pj J ω)) ≤ Pbar)
    (hrem : PJ.expect (fun J => PΩ.expect (fun ω => ∑ f, r J ω f)) ≤ c') :
    PJ.expect (fun J => PΩ.expect (fun ω =>
      reservedCut.form (tensorLaw fun b => N b + Qr b) (Zr J ω) (Zr J ω))) ≤
      Bz * Real.exp TQ * Pbar * Y + c' := by
  have hprod : ∏ b, (1 + u b) = ∑ f : Jb → Bool, ∏ b, (if f b then u b else 1) := by
    rw [← Fintype.prod_sum (fun b (i : Bool) => if i then u b else 1)]
    apply Finset.prod_congr rfl
    intro b _
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true]
    exact add_comm _ _
  have hexp : ∏ b, (1 + u b) ≤ Real.exp TQ :=
    (prod_one_add_le_exp u hu).trans (Real.exp_le_exp.mpr hTQ)
  -- the pointwise bound
  have hpt : ∀ J ω, reservedCut.form (tensorLaw fun b => N b + Qr b) (Zr J ω) (Zr J ω) ≤
      Bz * Real.exp TQ * Y * Pj J ω + ∑ f, r J ω f := by
    intro J ω
    rw [form_tensorLaw_add_eq_sum]
    have hK : 0 ≤ Bz * Pj J ω * Y := mul_nonneg (mul_nonneg hBz (hPj J ω)) hY
    calc ∑ f : Jb → Bool,
          reservedCut.form (tensorLaw fun b => if f b then Qr b else N b) (Zr J ω) (Zr J ω)
        ≤ ∑ f : Jb → Bool,
          |reservedCut.form (tensorLaw fun b => if f b then Qr b else N b) (Zr J ω) (Zr J ω)| :=
          sum_le_sum fun f _ => le_abs_self _
      _ ≤ ∑ f : Jb → Bool, (Bz * Pj J ω * Y * ∏ b, (if f b then u b else 1) + r J ω f) :=
          sum_le_sum fun f _ => hterm J ω f
      _ = Bz * Pj J ω * Y * ∏ b, (1 + u b) + ∑ f, r J ω f := by
          rw [sum_add_distrib, ← mul_sum, hprod]
      _ ≤ Bz * Pj J ω * Y * Real.exp TQ + ∑ f, r J ω f := by
          have := mul_le_mul_of_nonneg_left hexp hK
          linarith
      _ = Bz * Real.exp TQ * Y * Pj J ω + ∑ f, r J ω f := by ring
  have hK0 : 0 ≤ Bz * Real.exp TQ * Y := mul_nonneg (mul_nonneg hBz (Real.exp_pos _).le) hY
  calc PJ.expect (fun J => PΩ.expect (fun ω =>
        reservedCut.form (tensorLaw fun b => N b + Qr b) (Zr J ω) (Zr J ω)))
      ≤ PJ.expect (fun J => PΩ.expect (fun ω =>
          Bz * Real.exp TQ * Y * Pj J ω + ∑ f, r J ω f)) :=
        PJ.expect_mono fun J => PΩ.expect_mono fun ω => hpt J ω
    _ = Bz * Real.exp TQ * Y * PJ.expect (fun J => PΩ.expect (fun ω => Pj J ω)) +
        PJ.expect (fun J => PΩ.expect (fun ω => ∑ f, r J ω f)) := by
        have h1 : ∀ J, PΩ.expect (fun ω => Bz * Real.exp TQ * Y * Pj J ω + ∑ f, r J ω f) =
            Bz * Real.exp TQ * Y * PΩ.expect (fun ω => Pj J ω) +
              PΩ.expect (fun ω => ∑ f, r J ω f) := by
          intro J
          rw [PΩ.expect_add, PΩ.expect_const_mul]
        rw [PJ.expect_congr h1, PJ.expect_add, PJ.expect_const_mul]
    _ ≤ Bz * Real.exp TQ * Y * Pbar + c' := by
        have := mul_le_mul_of_nonneg_left hmoment hK0
        linarith
    _ = Bz * Real.exp TQ * Pbar * Y + c' := by ring

end Abstract

section TheoremC

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The left matching-envelope increment `Q_{L,𝔟} = ∑_i c_{L,𝔟,i} κ_{L,𝔟,i}` (CP6). -/
noncomputable def envIncL (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    AtomMeasure m₀ p L b :=
  ∑ i, D.ME.cL L b i • D.ME.κL L b i

/-- The right matching-envelope increment `Q_{R,𝔟}`. -/
noncomputable def envIncR (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    AtomMeasure m₀ p L b :=
  ∑ i, D.ME.cR L b i • D.ME.κR L b i

/-- The price `u_{L,𝔟} = ∑_i c_{L,𝔟,i} κ_{L,𝔟,i}(1) q_𝔟^{2a}` of the left increment. -/
noncomputable def envPriceL (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) : ℝ :=
  ∑ i, D.ME.cL L b i * mass (D.ME.κL L b i) * selectionFactor p D.S.selPre L b

/-- The price `u_{R,𝔟}` of the right increment. -/
noncomputable def envPriceR (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) : ℝ :=
  ∑ i, D.ME.cR L b i * mass (D.ME.κR L b i) * selectionFactor p D.S.selPre L b

omit [DecidableEq P] in
theorem envPriceL_nonneg (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    0 ≤ envPriceL D L b :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (D.ME.cL_nonneg L b i)
    (ComparisonData.mass_nonneg_of_nonneg (D.ME.κL_pos L b i).1)) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem envPriceR_nonneg (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    0 ≤ envPriceR D L b :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (D.ME.cR_nonneg L b i)
    (ComparisonData.mass_nonneg_of_nonneg (D.ME.κR_pos L b i).1)) (D.selectionFactor_nonneg L b)

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The revealed source half-function `Z^𝒥_ω` of the left inclusion energy. -/
noncomputable def revealL (D : ComparisonData m₀ p pr h E) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) :
    (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ :=
  queryReveal D.index.C Jq (productHalf D.index.u (fun e => atomInput m₀ p pr h hcop L A e)
    (atomLift m₀ p L A)) ω

/-- The revealed target half-function of the right inclusion energy. -/
noncomputable def revealR (D : ComparisonData m₀ p pr h E) (L : ℕ) (A : Finset ℤ)
    (Jq : ∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1))
    (ω : ∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) :
    (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ :=
  queryReveal D.index.C Jq (productHalf D.index.w (fun e => atomInput m₀ p pr h hcop L A e)
    (atomLift m₀ p L A)) ω

/-- **`EnvelopeEnergies` from the per-term bounds** (`lem:envelope-energy`). Suppose that at
every least counterexample, for both envelopes `s ∈ {L, R}`, every query depth `𝒥`, every
index `ω` and every subset `f` of atoms carrying the increment `Q_s`:
* `|Q_{⊗(f ? Q_s : Ñ)}(Z^𝒥_ω, Z^𝒥_ω)| ≤ (B + z_L) Π_{𝒥,ω} Y ∏_{𝔟∈f} u_{s,𝔟} + r_{s,𝒥,ω,f}`.
  This is (E1) under the bracket with the conductor price `Π` of the index: `envelopeBound`
  type bounds, the `_theta` layers at `ϑ`.
* `E_𝒥 E_ω Π_{𝒥,ω} ≤ R_I^k`, which is `lem:hyb:moment`.
* `E_𝒥 E_ω ∑_f r_{s,𝒥,ω,f} ≤ c L^{-1/825} α`.

Then `EnvelopeEnergies` holds with `o(1) = z_L e^T R_I^k`; the totals `TL_total`,
`TR_total` give `∑_𝔟 u_{s,𝔟} ≤ T`. -/
theorem envelopeEnergies_of_terms (D : ComparisonData m₀ p pr h E)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (Pj : ℕ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → ℝ)
    (hPj : ∀ L Jq ω, 0 ≤ Pj L Jq ω)
    (hmom : ∀ L, (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => Pj L Jq ω)) ≤ D.S.index.R_I ^ Fintype.card E)
    (rL rR : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
      (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ)
    (htermL : AtCounterexamples D.Y (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then envIncL D L b else D.GB.N L b)
          (revealL hcop D L A Jq ω) (revealL hcop D L A Jq ω)| ≤
        (D.B + z L) * Pj L Jq ω * D.Y L A * ∏ b, (if f b then envPriceL D L b else 1) +
          rL L A Jq ω f))
    (htermR : AtCounterexamples D.Y (fun L A => ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then envIncR D L b else D.GB.N L b)
          (revealR hcop D L A Jq ω) (revealR hcop D L A Jq ω)| ≤
        (D.B + z L) * Pj L Jq ω * D.Y L A * ∏ b, (if f b then envPriceR D L b else 1) +
          rR L A Jq ω f))
    (hremL : AtCounterexamples D.Y (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rL L A Jq ω f)) ≤ remainder c L A))
    (hremR : AtCounterexamples D.Y (fun L A => (queryLaw D.index.C D.index.t).expect (fun Jq =>
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j)).expect
        (fun ω => ∑ f, rR L A Jq ω f)) ≤ remainder c L A)) :
    D.EnvelopeEnergies hcop := by
  have hB := B_nonneg D
  refine ⟨fun L => z L * Real.exp D.ME.T * D.S.index.R_I ^ Fintype.card E, ?_, c, hc, ?_, ?_⟩
  · have := (hzt.mul_const (Real.exp D.ME.T)).mul_const (D.S.index.R_I ^ Fintype.card E)
    simpa using this
  · filter_upwards [htermL, hremL] with L hL hr
    intro C hC hk A hA hY
    have hY0 : 0 ≤ D.Y L A := by
      have : 0 ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hTQ : ∑ b, envPriceL D L b ≤ D.ME.T := D.ME.TL_total L
    have h := inclusion_energy_le_of_terms (queryLaw D.index.C D.index.t)
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j))
      (D.GB.N L) (envIncL D L) (revealL hcop D L A) (envPriceL D L) (envPriceL_nonneg D L)
      (add_nonneg hB (hz0 L)) hY0 hTQ (Pj L) (rL L A) (hL C hC hk A hA hY) (hPj L) (hmom L)
      (hr C hC hk A hA hY)
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · rfl
    · ring
  · filter_upwards [htermR, hremR] with L hL hr
    intro C hC hk A hA hY
    have hY0 : 0 ≤ D.Y L A := by
      have : 0 ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hTQ : ∑ b, envPriceR D L b ≤ D.ME.T := D.ME.TR_total L
    have h := inclusion_energy_le_of_terms (queryLaw D.index.C D.index.t)
      (FiniteLaw.uniform (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j))
      (D.GB.N L) (envIncR D L) (revealR hcop D L A) (envPriceR D L) (envPriceR_nonneg D L)
      (add_nonneg hB (hz0 L)) hY0 hTQ (Pj L) (rR L A) (hL C hC hk A hA hY) (hPj L) (hmom L)
      (hr C hC hk A hA hY)
    refine le_trans (le_of_eq ?_) (h.trans (le_of_eq ?_))
    · rfl
    · ring

/-- The wrapping increment `Q_𝔟 = ∑_t (π̃^s D^s + π̃^a D^a)` of `wrapEnvelope` (CP4). -/
noncomputable def wrapInc (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    AtomMeasure m₀ p L b :=
  ∑ t, (D.CL.πt L b t .sym • D.CL.D L b t .sym + D.CL.πt L b t .skew • D.CL.D L b t .skew)

/-- The price `∑_t (π^s + π^a)` of the wrapping increment. -/
noncomputable def wrapPrice (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) : ℝ :=
  ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew)

omit [DecidableEq P] in
theorem wrapPrice_nonneg (D : ComparisonData m₀ p pr h E) (L : ℕ) (b : PaperAtom J L) :
    0 ≤ wrapPrice D L b := by
  unfold wrapPrice ComparisonLaw.π
  exact sum_nonneg fun t _ => add_nonneg
    (mul_nonneg (D.CL.πt_nonneg L b t _) (D.selectionFactor_nonneg L b))
    (mul_nonneg (D.CL.πt_nonneg L b t _) (D.selectionFactor_nonneg L b))

/-- **`FixedIntervalEnvelopeEnergies` from the per-term bounds** (`lem:envelope-energy` at
fixed intervals, `κ_e = K`). The inputs are as in `envelopeEnergies_of_terms`, for every
nonempty set `𝒮` of active queries:
* the per-term bounds for the subsets of `wrapEnvelope = Ñ + ∑_t (π̃^s D^s + π̃^a D^a)`;
* the moment `E Π_𝒮 ≤ (K^{2θ/d} R_I)^{|𝒮|}`;
* the remainder summation.

The prices total at most `S + A` (`wrapEnvelope_price`). The relative error is
`z_L e^{S+A} (1 + K^{2θ/d} R_I)^k`; `R_I ≥ 0` is the field `hR_I` of WP-FI's `IndexLaw`. -/
theorem fixedIntervalEnvelopeEnergies_of_terms (D : ComparisonData m₀ p pr h E)
    (z : ℕ → ℝ) (hz0 : ∀ L, 0 ≤ z L) (hzt : Tendsto z atTop (𝓝 0)) {c : ℝ} (hc : 0 ≤ c)
    (Pj : ℕ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → ℝ)
    (hPj : ∀ L S Jq ω, 0 ≤ Pj L S Jq ω)
    (hmom : ∀ L S, (queryLaw (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => Pj L S Jq ω)) ≤ D.fixedIntervalFactor ^ S.card)
    (rL rR : ∀ L, Finset ℤ → Finset E →
      (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
      (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (PaperAtom J L → Bool) → ℝ)
    (htermL : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then wrapInc D L b else D.GB.N L b)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapSourceHalf m₀ p pr h hcop D.S.Q.u L A S) ω)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapSourceHalf m₀ p pr h hcop D.S.Q.u L A S) ω)| ≤
        (D.B + z L) * Pj L S Jq ω * D.Y L A * ∏ b, (if f b then wrapPrice D L b else 1) +
          rL L A S Jq ω f))
    (htermR : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      ∀ Jq ω (f : PaperAtom J L → Bool),
      |reservedCut.form (tensorLaw fun b => if f b then wrapInc D L b else D.GB.N L b)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapTargetHalf m₀ p pr h hcop D.S.Q.w L A S) ω)
          (queryReveal (fun (_ : E) => coordChain blockScale pr h) Jq
            (wrapTargetHalf m₀ p pr h hcop D.S.Q.w L A S) ω)| ≤
        (D.B + z L) * Pj L S Jq ω * D.Y L A * ∏ b, (if f b then wrapPrice D L b else 1) +
          rR L A S Jq ω f))
    (hremL : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rL L A S Jq ω f)) ≤ remainder c L A))
    (hremR : AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      (queryLaw (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (D.S.index.t e))).expect (fun Jq =>
        (FiniteLaw.uniform (E → ∀ j : Option P, CoordSpace blockScale pr h j)).expect
          (fun ω => ∑ f, rR L A S Jq ω f)) ≤ remainder c L A)) :
    D.FixedIntervalEnvelopeEnergies hcop := by
  have hB := B_nonneg D
  have hF : 0 ≤ D.fixedIntervalFactor := by
    unfold ComparisonData.fixedIntervalFactor
    exact mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) D.S.index.hR_I
  have hpowS : ∀ S : Finset E, D.fixedIntervalFactor ^ S.card ≤
      (1 + D.fixedIntervalFactor) ^ Fintype.card E := by
    intro S
    calc D.fixedIntervalFactor ^ S.card ≤ (1 + D.fixedIntervalFactor) ^ S.card :=
          pow_le_pow_left₀ hF (by linarith) _
      _ ≤ (1 + D.fixedIntervalFactor) ^ Fintype.card E :=
          pow_le_pow_right₀ (by linarith) (card_le_univ S)
  refine ⟨fun L => z L * Real.exp (D.CL.S + D.CL.A) * (1 + D.fixedIntervalFactor) ^ Fintype.card E,
    fun L => mul_nonneg (mul_nonneg (hz0 L) (Real.exp_pos _).le)
      (pow_nonneg (by linarith) _), ?_, c, hc, ?_⟩
  · have := (hzt.mul_const (Real.exp (D.CL.S + D.CL.A))).mul_const
      ((1 + D.fixedIntervalFactor) ^ Fintype.card E)
    simpa using this
  · filter_upwards [htermL, htermR, hremL, hremR] with L hL hR hrL hrR
    intro C hC hk A hA hY S hS
    have hY0 : 0 ≤ D.Y L A := by
      have : 0 ≤ C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hTQ : ∑ b, wrapPrice D L b ≤ D.CL.S + D.CL.A := D.wrapEnvelope_price L
    have hfin : ∀ x : ℝ, x ≤ (D.B + z L) * Real.exp (D.CL.S + D.CL.A) *
        D.fixedIntervalFactor ^ S.card * D.Y L A + remainder c L A →
        x ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card +
          z L * Real.exp (D.CL.S + D.CL.A) * (1 + D.fixedIntervalFactor) ^ Fintype.card E) *
            D.Y L A + remainder c L A := by
      intro x hx
      have h1 : z L * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card ≤
          z L * Real.exp (D.CL.S + D.CL.A) * (1 + D.fixedIntervalFactor) ^ Fintype.card E :=
        mul_le_mul_of_nonneg_left (hpowS S) (mul_nonneg (hz0 L) (Real.exp_pos _).le)
      have h2 := mul_le_mul_of_nonneg_right h1 hY0
      nlinarith
    constructor
    · apply hfin
      exact inclusion_energy_le_of_terms _ _ (D.GB.N L) (wrapInc D L) _ (wrapPrice D L)
        (wrapPrice_nonneg D L) (add_nonneg hB (hz0 L)) hY0 hTQ (Pj L S) (rL L A S)
        (hL C hC hk A hA hY S hS) (hPj L S) (hmom L S) (hrL C hC hk A hA hY S hS)
    · apply hfin
      exact inclusion_energy_le_of_terms _ _ (D.GB.N L) (wrapInc D L) _ (wrapPrice D L)
        (wrapPrice_nonneg D L) (add_nonneg hB (hz0 L)) hY0 hTQ (Pj L S) (rR L A S)
        (hR C hC hk A hA hY S hS) (hPj L S) (hmom L S) (hrR C hC hk A hA hY S hS)

end TheoremC

end Sarkozy.Structured

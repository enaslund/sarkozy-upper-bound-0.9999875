module

public import Sarkozy.OpsCore.StarForm

@[expose] public section

/-!
# The record operators at the comparison data, from the brackets of (CP3) (OPS-L)

`paper/sections/09_comparison_theorem.tex`, (CP3) (`(π̃ D ζ; ζ* π̃ D) ⪰_ι 0` with a
reserved-diagonal probability law `D^ε_{𝔟,t}`); `paper/sections/23_envelopes.tex`,
`subsec:envelope-tools`.

The comparison data carry, for every block `𝔟`, record `t` and type `ε`, a bracket of the change
`ζ^ε_{𝔟,t}` by `π̃^ε_{𝔟,t} D^ε_{𝔟,t}`, where `D^ε_{𝔟,t}` is diagonal at the reserved cut
(`TheoremCBlock.ComparisonLaw.bracket`, `D_diag`, `D_prob`). Let `d` be the half marginal of
`D^ε_{𝔟,t}` (`dHalf`; for the middle records it is the actual half marginal `m_t` of the record,
since B8's charged sides are `Diag_ι(m_t)`). Then:

* **`form_diag`**: the cut form of a diagonal law is `∑_x d(x) F(x) G(x)`;
* **`formBound_of_bracket`**: B8's `FormBound c d ζ π̃`, i.e. `‖recOp_d ζ‖ ≤ π̃` in `L²(d)`;
* **`plusIn_of_formBound`**: `ζ` charges no plus half outside the support of `d` (`PlusIn`);
* **`dHalf_diagonalLaw`**, **`selMarg_eq_of_diag`**: where `D^ε = Diag_ι(m)` (the middle blocks:
  `envT`), `selMarg = m`, the actual half marginal (B8's `mOf`);
* **`diagonalLaw_dHalf`**: a diagonal law is `Diag_ι` of its half marginal; hence **`hD_sel`**:
  at the star objects, `Diag_ι(m_𝔟) = D^ε_{𝔟,t}` (OPS-S's input `hD` of `paperDegreeOpsS`);
* at the comparison data: **`selMarg`** (the marginal `d` of the selected record at each block of
  a selection), **`plusIn_sel`**, **`selMarg_nonneg`**, **`formLE_sel`**
  (`‖recOp ζ_{ω(𝔅),𝔅}‖ ≤ π̃_{ω(𝔅)}`). So the hypotheses `hplus` and `hm` of `StarOK` hold for
  every selection at `mB := selMarg` (**`StarData.ofSel`**, **`starOK_of`**), and the only
  remaining per-record inputs of the star form are `w`, `L_𝔅` and its two norm bounds, and the
  signs.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps Sarkozy.SignedComponents Sarkozy.TheoremC

section Generic

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  {c : ReflectionCut V}

/-- The half marginal of a law that is diagonal at the cut: `d(x) = κ(join(x, x))`. -/
noncomputable def dHalf (c : ReflectionCut V) (κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (x : c.Half → X) : ℝ :=
  lawDensity κ (c.join x x)

/-- The cut form as a double sum over the halves. -/
theorem form_eq_density (κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (F G : (c.Half → X) → ℝ) :
    c.form κ F G = ∑ x, ∑ y, lawDensity κ (c.join x y) * F x * G y := by
  unfold ReflectionCut.form
  rw [cut_form_eq_sum]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  rw [← ReflectionCut.matrix_eq_density_join]
  rfl

/-- **The cut form of a diagonal law** is `∑_x d(x) F(x) G(x)`. -/
theorem form_diag {κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hD : ∀ z, lawDensity κ z ≠ 0 → ∀ v, z (c.flip v) = z v) (F G : (c.Half → X) → ℝ) :
    c.form κ F G = ∑ x, dHalf c κ x * (F x * G x) := by
  rw [form_eq_density]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_eq_single x]
  · unfold dHalf
    ring
  · intro y hy
    have : lawDensity κ (c.join x y) = 0 := by
      by_contra hne
      apply hy
      funext v
      have h := hD _ hne v.1
      rw [ReflectionCut.join_minus, ReflectionCut.join_plus] at h
      exact h
    rw [this]
    ring

/-- `hsq` is the form of the diagonal law. -/
theorem form_diag_self {κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hD : ∀ z, lawDensity κ z ≠ 0 → ∀ v, z (c.flip v) = z v) (F : (c.Half → X) → ℝ) :
    c.form κ F F = hsq c (dHalf c κ) F := by
  rw [form_diag hD]
  rfl

/-- **(CP3) as an operator norm bound**: a bracket of `ζ` by `π̃ D` with `D` diagonal gives B8's
`FormBound c d ζ π̃` relative to the half marginal `d` of `D`. -/
theorem formBound_of_bracket {κ ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ} {πt : ℝ} (hπ : 0 ≤ πt)
    (hD : ∀ z, lawDensity κ z ≠ 0 → ∀ v, z (c.flip v) = z v)
    (hB : c.Bracket (πt • κ) ζ (πt • κ)) : FormBound c (dHalf c κ) ζ πt := by
  refine ⟨hπ, fun F G => ?_⟩
  have h := hB.cauchy_schwarz_sq F G
  have hF := hB.left_positive.nonneg F
  have hG := hB.right_positive.nonneg G
  have eF : c.form (πt • κ) F F = πt * hsq c (dHalf c κ) F := by
    rw [← form_diag_self hD]
    rfl
  have eG : c.form (πt • κ) G G = πt * hsq c (dHalf c κ) G := by
    rw [← form_diag_self hD]
    rfl
  rw [eF] at h hF
  rw [eG] at h hG
  rcases hπ.eq_or_lt with h0 | hpos
  · rw [← h0] at h ⊢
    have : |c.form ζ F G| ^ 2 ≤ 0 := by simpa using h
    have h2 : |c.form ζ F G| = 0 := by nlinarith [abs_nonneg (c.form ζ F G)]
    rw [h2]
    simp
  · have hA : 0 ≤ hsq c (dHalf c κ) F := nonneg_of_mul_nonneg_right (by linarith) hpos
    have hB' : 0 ≤ hsq c (dHalf c κ) G := nonneg_of_mul_nonneg_right (by linarith) hpos
    have h3 : |c.form ζ F G| ≤
        Real.sqrt ((πt * hsq c (dHalf c κ) F) * (πt * hsq c (dHalf c κ) G)) :=
      Real.abs_le_sqrt (by rwa [sq_abs] at h)
    have e : Real.sqrt ((πt * hsq c (dHalf c κ) F) * (πt * hsq c (dHalf c κ) G)) =
        πt * Real.sqrt (hsq c (dHalf c κ) F) * Real.sqrt (hsq c (dHalf c κ) G) := by
      rw [show (πt * hsq c (dHalf c κ) F) * (πt * hsq c (dHalf c κ) G) =
          πt ^ 2 * (hsq c (dHalf c κ) F * hsq c (dHalf c κ) G) by ring,
        Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpos.le, Real.sqrt_mul hA, mul_assoc]
    rw [e] at h3
    exact h3

/-- **A diagonal law is the diagonal law of its half marginal**: `κ = Diag_ι(d)`. -/
theorem diagonalLaw_dHalf {κ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hD : ∀ z, lawDensity κ z ≠ 0 → ∀ v, z (c.flip v) = z v) :
    c.diagonalLaw (dHalf c κ) = κ := by
  refine LinearMap.ext fun Φ => ?_
  change ∑ x, dHalf c κ x * Φ (c.join x x) = κ Φ
  rw [linearFunctional_density κ Φ]
  change _ = ∑ z, lawDensity κ z * Φ z
  rw [← Fintype.sum_equiv c.configurationEquiv.symm (fun q => lawDensity κ (c.join q.1 q.2) *
    Φ (c.join q.1 q.2)) (fun z => lawDensity κ z * Φ z) (fun _ => rfl), Fintype.sum_prod_type]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_eq_single x]
  · rfl
  · intro y hy
    have : lawDensity κ (c.join x y) = 0 := by
      by_contra hne
      apply hy
      funext v
      have h := hD _ hne v.1
      rw [ReflectionCut.join_minus, ReflectionCut.join_plus] at h
      exact h
    rw [this, zero_mul]

/-- **The half marginal of `Diag_ι(m)` is `m`.** -/
theorem dHalf_diagonalLaw (m : (c.Half → X) → ℝ) : dHalf c (c.diagonalLaw m) = m := by
  funext x
  unfold dHalf lawDensity
  change ∑ y, m y * (if c.join y y = c.join x x then (1 : ℝ) else 0) = m x
  rw [Fintype.sum_eq_single x]
  · simp
  · intro y hy
    have : c.join y y ≠ c.join x x := by
      intro h
      apply hy
      funext v
      have := congrFun h v.1
      rwa [ReflectionCut.join_plus, ReflectionCut.join_plus] at this
    simp [this]

/-- **A form bound relative to `m` forces the support condition** `PlusIn`. -/
theorem plusIn_of_formBound {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ} {C : ℝ}
    (h : FormBound c m ζ C) : PlusIn c m ζ := by
  intro x y hx
  have h1 := h.2 (EnvelopeSteps.delta x) (EnvelopeSteps.delta y)
  have e1 : hsq c m (EnvelopeSteps.delta x) = 0 := by
    unfold hsq EnvelopeSteps.delta
    rw [Fintype.sum_eq_single x]
    · simp [hx]
    · intro z hz
      simp [hz]
  have e2 : c.form ζ (EnvelopeSteps.delta x) (EnvelopeSteps.delta y) =
      lawDensity ζ (c.join x y) := by
    rw [form_eq_density, Fintype.sum_eq_single x, Fintype.sum_eq_single y]
    · simp [EnvelopeSteps.delta]
    · intro z hz
      simp [EnvelopeSteps.delta, hz]
    · intro z hz
      refine sum_eq_zero fun w _ => ?_
      simp [EnvelopeSteps.delta, hz]
  rw [e1, e2, Real.sqrt_zero, mul_zero, zero_mul] at h1
  exact abs_nonpos_iff.mp h1

end Generic

section Paper

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The half marginal of the selected record** at a block: that of the diagonal law
`D^ε_{𝔟,t}` of the bracket of (CP3), for `ω(𝔟) = (t, ε)` (`0` off the support). -/
noncomputable def selMarg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) :
    (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ :=
  match ω b with
  | some (t, e) => dHalf reservedCut (D.CL.D L b t e)
  | none => fun _ => 0

/-- The price `π̃` of the selected record at a block (`0` off the support). -/
noncomputable def selPrice (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) : ℝ :=
  match ω b with
  | some (t, e) => D.CL.πt L b t e
  | none => 0

omit [DecidableEq P] in
/-- **The record operator of a selected factor is bounded by its price** (CP3):
`‖recOp ζ_{ω(𝔟),𝔟}‖ ≤ π̃_{ω(𝔟)}` in `L²(d)`. -/
theorem formBound_sel (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (hb : b ∈ Choice.support ω) :
    FormBound reservedCut (selMarg D L ω b) (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b))
      (selPrice D L ω b) := by
  have hs : (ω b).isSome := (mem_filter.mp hb).2
  unfold selMarg selPrice
  obtain ⟨⟨t, e⟩, he⟩ := Option.isSome_iff_exists.mp hs
  rw [he]
  exact formBound_of_bracket (D.CL.πt_nonneg L b t e) (D.CL.D_diag L b t e) (D.CL.bracket L b t e)

omit [DecidableEq P] in
/-- `PlusIn` for every selected factor, relative to `selMarg`. -/
theorem plusIn_sel (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (hb : b ∈ Choice.support ω) :
    PlusIn reservedCut (selMarg D L ω b) (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)) :=
  plusIn_of_formBound (formBound_sel D L ω b hb)

omit [DecidableEq P] in
/-- The selected marginals are nonnegative (`D^ε` is a probability law). -/
theorem selMarg_nonneg (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L)
    (x : reservedCut.Half → BlockLabel m₀ blk p L b) :
    0 ≤ selMarg D L ω b x := by
  unfold selMarg
  rcases ω b with _ | ⟨t, e⟩
  · exact le_rfl
  · exact (D.CL.D_prob L b t e).1 _ fun z => by split_ifs <;> norm_num

omit [DecidableEq P] in
/-- **The operator norm of the record operator** (`FormLE`) at a block of the support. -/
theorem formLE_sel (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (hb : b ∈ Choice.support ω) :
    FormLE (selMarg D L ω b)
      (recOp reservedCut (selMarg D L ω b) (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)))
      (selPrice D L ω b) :=
  formLE_of_formBound (plusIn_sel D L ω b hb) (formBound_sel D L ω b hb)

omit [DecidableEq P] in
/-- **The norm envelopes are the diagonal laws of the selected marginals**: at the star objects
(`φ = id`), `Diag_ι(push m_𝔟 id) = D^ε_{𝔟,t}` for `ω(𝔟) = (t, ε)`. This is OPS-S's input `hD`
of `paperDegreeOpsS` (`def:cp4`(b)), proved here from `D_diag`. -/
theorem hD_sel (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (t : D.CL.T L b) (e : ChangeType)
    (he : ω b = some (t, e)) :
    reservedCut.diagonalLaw (push (selMarg D L ω b) id) = D.CL.D L b t e := by
  have hp : push (selMarg D L ω b) id = selMarg D L ω b := by
    funext x
    unfold push
    rw [show univ.filter (fun y => id y = x) = {x} by ext y; simp]
    simp
  rw [hp]
  unfold selMarg
  rw [he]
  exact diagonalLaw_dHalf (D.CL.D_diag L b t e)

omit [DecidableEq P] in
/-- **The selected marginal is the actual half marginal** wherever the norm envelope is
`Diag_ι(m)`: at the middle blocks the atom comparison sets `D^ε_{𝔟,t} = envT = Diag_ι(m_+(Π_t))`
(`MiddleComparison.toAtom`), so there `selMarg` is B8's `mOf`, the marginal of the 24 norm
bounds. -/
theorem selMarg_eq_of_diag (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (t : D.CL.T L b) (e : ChangeType)
    (he : ω b = some (t, e)) (m : (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hD : D.CL.D L b t e = reservedCut.diagonalLaw m) : selMarg D L ω b = m := by
  unfold selMarg
  rw [he]
  change dHalf reservedCut (D.CL.D L b t e) = m
  rw [hD, dHalf_diagonalLaw]

/-- **The star data at the selected marginals**: `m_𝔅 := selMarg`, with the raw-arm
coefficients `w`, the leading stars `L_𝔅`, their bounds and the signs as arguments. -/
noncomputable def StarData.ofSel {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (w : {b // b ∈ Choice.support ω} → ℝ)
    (Lb : ∀ b : {b // b ∈ Choice.support ω},
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
        (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ))
    (ℓ ρ ε : {b // b ∈ Choice.support ω} → ℝ) : StarData D L ω where
  mB b := selMarg D L ω b.1
  w := w
  Lb := Lb
  ℓ := ℓ
  ρ := ρ
  ε := ε

omit [DecidableEq P] in
/-- **`StarOK` at the selected marginals**: `hplus` and `hm` are proved (`plusIn_sel`,
`selMarg_nonneg`); the inputs are `w > 0`, the two norm bounds of (N1)–(N3), the signs and the
symmetry of the kernels. -/
theorem starOK_of {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} {w : {b // b ∈ Choice.support ω} → ℝ}
    {Lb : ∀ b : {b // b ∈ Choice.support ω},
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
        (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ)}
    {ℓ ρ ε : {b // b ∈ Choice.support ω} → ℝ}
    (hw : ∀ b, 0 < w b)
    (hL : ∀ b, OpNormLE ((StarData.ofSel (D := D) w Lb ℓ ρ ε).mB b) (Lb b) (ℓ b))
    (hE : ∀ b, OpNormLE ((StarData.ofSel (D := D) w Lb ℓ ρ ε).mB b)
      ((StarData.ofSel (D := D) w Lb ℓ ρ ε).Δhat b - Lb b) (ρ b))
    (hε : ∏ b, ε b = 1)
    (hLs : ∀ b x y, kern ((StarData.ofSel (D := D) w Lb ℓ ρ ε).mB b) (Lb b) y x =
      ε b * kern ((StarData.ofSel (D := D) w Lb ℓ ρ ε).mB b) (Lb b) x y)
    (hΔs : ∀ b x y, kern ((StarData.ofSel (D := D) w Lb ℓ ρ ε).mB b)
        ((StarData.ofSel (D := D) w Lb ℓ ρ ε).Δhat b) y x =
      ε b * kern ((StarData.ofSel (D := D) w Lb ℓ ρ ε).mB b)
        ((StarData.ofSel (D := D) w Lb ℓ ρ ε).Δhat b) x y) :
    StarOK (StarData.ofSel (D := D) w Lb ℓ ρ ε) where
  hplus b := plusIn_sel D L ω b.1 b.2
  hm b x := selMarg_nonneg D L ω b.1 x
  hw := hw
  hL := hL
  hE := hE
  hε := hε
  hLs := hLs
  hΔs := hΔs

end Paper

end Sarkozy.OpsCore

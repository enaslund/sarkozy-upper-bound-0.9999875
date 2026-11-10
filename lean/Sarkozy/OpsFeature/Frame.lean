module

public import Sarkozy.OpsFeature.Block
public import Sarkozy.Envelopes.FeatureFrame
public import Sarkozy.EnvelopeSteps.Reflection
public import Mathlib.Analysis.InnerProductSpace.PiL2

@[expose] public section

/-!
# The actual feature frame at a block (`lem:oct24:feature-block`(a), (b))

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`. With the five fold features
`𝓗₀, 𝓗₁, 𝓗₂, 𝒦₁₂, 𝒦₀₁` of `Sarkozy.OpsFeature.Block` in the actual block law `m_{0,𝔅}`:

* **the singleton edges** `01`, `12`, `02` (`edge01`, `edge12`, `edge02`): B11's `corr01_actual`,
  `corr12_actual`, `corr02_actual` and `norm_actual_x*`, read in `L²(m_{0,𝔅})`, with the constants
  `ϱ₀₁(b)`, `ϱ₀₂(b)` at the least prime (`r01sq_b`, `r02sq_b`);
* **the vanishing correlations** `04`, `13`, `14`, `23` (`vanish04`, …): the definitions,
  `𝒦₁₂ ⊥ 𝓗₁ + 𝓗₂`, `𝒦₀₁ ⊥ 𝓗₀ + 𝓗₁`;
* **the edge `24` from the edge `03`** (`edge24_of_edge03`): the transport by the involution
  `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)`, which preserves `m_{0,𝔅}` (B11's `oldW_varsigma`) and
  exchanges `𝓗₀ ↔ 𝓗₂`, `𝒦₁₂ ↔ 𝒦₀₁` (the paper: "the pair `𝓗₂, 𝒦₀₁` is the same with `0` and `2`
  interchanged");
* **the edge `34`**: `edge34_block_b` (`Block`).

The edge `03` (Step 3 of the paper's proof) enters here as the named `Prop` `Edge03Block`; it is
proved in `Sarkozy.OpsFeature.Edge03` (block assembly) and `Sarkozy.OpsFeature.ExplicitT` (the
prime inputs), `edge03_block_proved`, and the unconditional forms of the two theorems below are
`actual_hcor_proved`, `actual_feature_frame_proved`.

**W2's hypothesis.** `feature_frame_middle` (`lem:oct24:feature-block`(b)) takes vectors
`h : Fin 5 → H` of a real inner product space with the correlation bounds `hcor`. Here
`H = EuclideanSpace ℝ (Tri F)` and the features are embedded by `h ↦ (√m_{0,𝔅}(x) h(x))_x`
(`emb`, an isometry of `L²(m_{0,𝔅})` into `H`). **`actual_hcor`** is exactly W2's `hcor` for the
embedded features, and **`actual_feature_frame`** is the frame bound
`‖∑_v h_v‖² ≤ Γ_F ∑_v ‖h_v‖²` in `L²(m_{0,𝔅})`, `Γ_F = 500111979555137707696357560603/(5·10²⁹)`,
at every block of primes `p ≡ 3 (mod 4)` whose least prime `b` is at least `Q₃ = 19951586`.
-/

open Finset
open scoped BigOperators RealInnerProductSpace

namespace Sarkozy.OpsFeature

open Sarkozy.MiddleRecords Sarkozy.Mixing Sarkozy.EnvelopeSteps Sarkozy.Envelopes

section Frame

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

/-! ## The inner product -/

theorem ipm_comm (h k : Tri F → ℝ) : ipm h k = ipm k h := by
  unfold ipm; exact sum_congr rfl fun x _ => by ring

theorem ipm_self (h : Tri F → ℝ) : ipm h h = ∑ x, m0B x * h x ^ 2 := by
  unfold ipm; exact sum_congr rfl fun x _ => by ring

theorem ipm_congr {h h' k k' : Tri F → ℝ} (hh : ∀ x, h x = h' x) (hk : ∀ x, k x = k' x) :
    ipm h k = ipm h' k' := by
  unfold ipm; simp only [hh, hk]

/-! ## The singleton edges (B11) -/

/-- `ϱ₀₁(p)² ≤ ϱ₀₁(b)²` for the primes `p ≥ b ≥ 7`, with `ϱ₀₁(b) = rho01 (1/b)`. -/
theorem r01sq_b {x b : ℝ} (hb : 7 ≤ b) (hx : b ≤ x) : r01sq x ≤ rho01 (1 / b) ^ 2 := by
  refine (r01sq_anti hb hx).trans (le_of_eq ?_)
  have hb4 : b - 4 ≠ 0 := by intro h; linarith
  have hb1 : b - 1 ≠ 0 := by intro h; linarith
  have hb0 : b ≠ 0 := by intro h; linarith
  have h14 : 1 - 4 * (1 / b) ≠ 0 := by
    rw [show 1 - 4 * (1 / b) = (b - 4) / b by field_simp]; exact div_ne_zero hb4 hb0
  have h1 : 1 - 1 / b ≠ 0 := by
    rw [show 1 - 1 / b = (b - 1) / b by field_simp]; exact div_ne_zero hb1 hb0
  have hpos : 0 ≤ 1 + 4 * (1 / b) / (1 - 4 * (1 / b)) ^ 2 := by
    have : 0 ≤ 4 * (1 / b) / (1 - 4 * (1 / b)) ^ 2 := by
      apply div_nonneg _ (sq_nonneg _); have : 0 < b := by linarith
      positivity
    linarith
  unfold rho01 r01sq
  rw [mul_pow, Real.sq_sqrt hpos]
  field_simp
  ring

/-- `ϱ₀₂(p)² ≤ ϱ₀₂(b)²` for the primes `p ≥ b ≥ 7`, with `ϱ₀₂(b) = rho02 (1/b) (b^{-1/2})`. -/
theorem r02sq_b {x b : ℝ} (hb : 7 ≤ b) (hx : b ≤ x) :
    r02sq x ≤ rho02 (1 / b) (1 / Real.sqrt b) ^ 2 := by
  refine (r02sq_anti hb hx).trans (le_of_eq ?_)
  have hb0 : 0 < b := by linarith
  have e1 : (1 / Real.sqrt b) ^ 2 = 1 / b := by rw [div_pow, one_pow, Real.sq_sqrt hb0.le]
  have e2 : Real.sqrt (1 + 1 / b) ^ 2 = 1 + 1 / b := Real.sq_sqrt (by positivity)
  unfold rho02 r02sq
  rw [div_pow, mul_pow, e1, e2]

theorem rho01_b_le {b : ℝ} (hb : 19951586 ≤ b) : 0 ≤ rho01 (1 / b) ∧ rho01 (1 / b) ≤ 1 := by
  have hb0 : 0 < b := by linarith
  have hq : 1 / b ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨?_, by have := (feature_table hb).2.1; linarith⟩
  unfold rho01
  exact mul_nonneg (div_nonneg (by positivity) (by linarith)) (Real.sqrt_nonneg _)

theorem rho02_b_le {b : ℝ} (hb : 19951586 ≤ b) :
    0 ≤ rho02 (1 / b) (1 / Real.sqrt b) ∧ rho02 (1 / b) (1 / Real.sqrt b) ≤ 1 := by
  have hb0 : 0 < b := by linarith
  have hq : 1 / b ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  refine ⟨?_, by have := (feature_table hb).1; linarith⟩
  unfold rho02
  exact div_nonneg (mul_nonneg (by positivity) (Real.sqrt_nonneg _)) (by linarith)

/-- The standing hypotheses on the block: primes `p ≡ 3 (mod 4)` (odd characteristic) with least
prime at least `b ≥ Q₃ = 19951586`. -/
structure MiddleBlock (F : P → Type*) [∀ p, Field (F p)] [∀ p, Fintype (F p)] (b : ℝ) : Prop where
  hF : ∀ p, ringChar (F p) ≠ 2
  h3 : ∀ p, Fintype.card (F p) % 4 = 3
  hb : 19951586 ≤ b
  hbp : ∀ p, b ≤ Fintype.card (F p)

omit [Fintype P] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem MiddleBlock.h7 {b : ℝ} (hB : MiddleBlock F b) (p : P) : (7 : ℝ) ≤ Fintype.card (F p) := by
  linarith [hB.hb, hB.hbp p]

/-- **The edge `01`** (B11's `corr01_actual`, in `L²(m_{0,𝔅})`). -/
theorem edge01 {b : ℝ} (hB : MiddleBlock F b) (h k : Tri F → ℝ) (hh : IsH c0 h) (hk : IsH c1 k) :
    |ipm h k| ≤ rho01 (1 / b) * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k)) := by
  obtain ⟨f, -, hf⟩ := hh
  obtain ⟨g, hg0, hg⟩ := hk
  obtain ⟨hc, hc1⟩ := rho01_b_le hB.hb
  have hb7 : (7 : ℝ) ≤ b := by linarith [hB.hb]
  have e1 : ipm h k = ∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.1) := by
    unfold ipm; simp only [hf, hg]; rfl
  have e2 : ipm h h = ∑ x, m0B x * f (fun p => (x p).1) ^ 2 := by
    rw [ipm_self]; simp only [hf]; rfl
  have e3 : ipm k k = ∑ x, m0B x * g (fun p => (x p).2.1) ^ 2 := by
    rw [ipm_self]; simp only [hg]; rfl
  rw [e1, e2, e3, norm_actual_x0 hB.hF hB.h3 hB.h7, norm_actual_x1 hB.hF hB.h3 hB.h7]
  exact corr01_actual hB.hF hB.h3 hB.h7 hc hc1 (fun p => r01sq_b hb7 (hB.hbp p)) f g hg0

/-- **The edge `12`** (B11's `corr12_actual`). -/
theorem edge12 {b : ℝ} (hB : MiddleBlock F b) (h k : Tri F → ℝ) (hh : IsH c1 h) (hk : IsH c2 k) :
    |ipm h k| ≤ rho01 (1 / b) * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k)) := by
  obtain ⟨f, -, hf⟩ := hh
  obtain ⟨g, hg0, hg⟩ := hk
  obtain ⟨hc, hc1⟩ := rho01_b_le hB.hb
  have hb7 : (7 : ℝ) ≤ b := by linarith [hB.hb]
  have e1 : ipm h k = ∑ x, m0B x * f (fun p => (x p).2.1) * g (fun p => (x p).2.2) := by
    unfold ipm; simp only [hf, hg]; rfl
  have e2 : ipm h h = ∑ x, m0B x * f (fun p => (x p).2.1) ^ 2 := by
    rw [ipm_self]; simp only [hf]; rfl
  have e3 : ipm k k = ∑ x, m0B x * g (fun p => (x p).2.2) ^ 2 := by
    rw [ipm_self]; simp only [hg]; rfl
  rw [e1, e2, e3, norm_actual_x1 hB.hF hB.h3 hB.h7, norm_actual_x2 hB.hF hB.h3 hB.h7]
  exact corr12_actual hB.hF hB.h3 hB.h7 hc hc1 (fun p => r01sq_b hb7 (hB.hbp p)) f g hg0

/-- **The edge `02`** (B11's `corr02_actual`). -/
theorem edge02 {b : ℝ} (hB : MiddleBlock F b) (h k : Tri F → ℝ) (hh : IsH c0 h) (hk : IsH c2 k) :
    |ipm h k| ≤ rho02 (1 / b) (1 / Real.sqrt b) * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k)) := by
  obtain ⟨f, -, hf⟩ := hh
  obtain ⟨g, hg0, hg⟩ := hk
  obtain ⟨hc, hc1⟩ := rho02_b_le hB.hb
  have hb7 : (7 : ℝ) ≤ b := by linarith [hB.hb]
  have e1 : ipm h k = ∑ x, m0B x * f (fun p => (x p).1) * g (fun p => (x p).2.2) := by
    unfold ipm; simp only [hf, hg]; rfl
  have e2 : ipm h h = ∑ x, m0B x * f (fun p => (x p).1) ^ 2 := by
    rw [ipm_self]; simp only [hf]; rfl
  have e3 : ipm k k = ∑ x, m0B x * g (fun p => (x p).2.2) ^ 2 := by
    rw [ipm_self]; simp only [hg]; rfl
  rw [e1, e2, e3, norm_actual_x0 hB.hF hB.h3 hB.h7, norm_actual_x2 hB.hF hB.h3 hB.h7]
  exact corr02_actual hB.hF hB.h3 hB.h7 hc hc1 (fun p => r02sq_b hb7 (hB.hbp p)) f g hg0

/-! ## The vanishing correlations (the definitions of `𝒦₁₂`, `𝒦₀₁`) -/

/-- A singleton feature of a coordinate on which `𝒦` is orthogonal: `⟨h, k⟩ = 0`. -/
theorem vanish_of_orth {π : Tri F → Lab F} {h k : Tri F → ℝ} (hh : IsH π h)
    (hk : ∀ g : Lab F → ℝ, ipm k (fun x => g (π x)) = 0) : ipm h k = 0 := by
  obtain ⟨f, -, hf⟩ := hh
  rw [ipm_comm, ← hk f]
  exact ipm_congr (fun _ => rfl) hf

theorem vanish04 (h k : Tri F → ℝ) (hh : IsH c0 h) (hk : IsK c0 c1 k) : ipm h k = 0 :=
  vanish_of_orth hh hk.2.1

theorem vanish13 (h k : Tri F → ℝ) (hh : IsH c1 h) (hk : IsK c1 c2 k) : ipm h k = 0 :=
  vanish_of_orth hh hk.2.1

theorem vanish14 (h k : Tri F → ℝ) (hh : IsH c1 h) (hk : IsK c0 c1 k) : ipm h k = 0 :=
  vanish_of_orth hh hk.2.2

theorem vanish23 (h k : Tri F → ℝ) (hh : IsH c2 h) (hk : IsK c1 c2 k) : ipm h k = 0 :=
  vanish_of_orth hh hk.2.2

/-! ## The edge `24` from the edge `03` (the involution `ς`) -/

/-- **The remaining input: the edge `03`** (`lem:oct24:feature-block`(a), proof Step 3; kind C):
`|⟨h, k⟩| ≤ c ‖h‖ ‖k‖` for `h ∈ 𝓗₀`, `k ∈ 𝒦₁₂` in `L²(m_{0,𝔅})`. -/
def Edge03Block (F : P → Type*) [∀ p, Field (F p)] [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]
    (c : ℝ) : Prop :=
  ∀ h k : Tri F → ℝ, IsH c0 h → IsK c1 c2 k →
    |ipm h k| ≤ c * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k))

/-- The involution `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)` of the object triples, prime by prime. -/
def sigT (x : Tri F) : Tri F := fun p => (-(x p).2.2, -(x p).2.1, -(x p).1)

omit [Fintype P] [∀ p, Fintype (F p)] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem sigT_invol (x : Tri F) : sigT (sigT x) = x := by
  funext p; simp [sigT]

omit [DecidableEq P] in
theorem m0B_sigT (x : Tri F) : m0B (sigT x) = m0B x := by
  unfold m0B sigT
  exact prod_congr rfl fun p _ => by rw [oldW_varsigma]

/-- The transport by `ς` preserves the inner product of `L²(m_{0,𝔅})`. -/
theorem ipm_sigT (h k : Tri F → ℝ) :
    ipm (fun x => h (sigT x)) (fun x => k (sigT x)) = ipm h k := by
  unfold ipm
  let e : Tri F ≃ Tri F := ⟨sigT, sigT, sigT_invol, sigT_invol⟩
  rw [← e.sum_comp (fun x => m0B x * h x * k x)]
  refine sum_congr rfl fun x _ => ?_
  change m0B x * h (sigT x) * k (sigT x) = m0B (sigT x) * h (sigT x) * k (sigT x)
  rw [m0B_sigT]

omit [Fintype P] [∀ p, Fintype (F p)] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem c0_sigT (x : Tri F) : c0 (sigT x) = -c2 x := rfl

omit [Fintype P] [∀ p, Fintype (F p)] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem c1_sigT (x : Tri F) : c1 (sigT x) = -c1 x := rfl

omit [Fintype P] [∀ p, Fintype (F p)] [DecidableEq P] [∀ p, DecidableEq (F p)] in
theorem c2_sigT (x : Tri F) : c2 (sigT x) = -c0 x := rfl

omit [∀ p, DecidableEq (F p)] in
/-- `ς` maps `𝓗₂` to `𝓗₀`. -/
theorem isH_sigT {h : Tri F → ℝ} (hh : IsH c2 h) : IsH c0 (fun x => h (sigT x)) := by
  obtain ⟨f, hf0, hf⟩ := hh
  refine ⟨fun u => f (-u), ?_, fun x => ?_⟩
  · have hc : ∀ u : Lab F, prodW unifB u = prodW unifB (-u) := fun u => rfl
    rw [← hf0]
    let e : Lab F ≃ Lab F := Equiv.neg _
    rw [← e.sum_comp (fun u => prodW unifB u * f u)]
    exact sum_congr rfl fun u _ => by rw [hc u]; rfl
  · show h (sigT x) = f (-(c0 x))
    rw [hf, c2_sigT]

/-- `ς` maps `𝒦₀₁` to `𝒦₁₂`. -/
theorem isK_sigT {k : Tri F → ℝ} (hk : IsK c0 c1 k) : IsK c1 c2 (fun x => k (sigT x)) := by
  obtain ⟨⟨K, hK⟩, h0, h1⟩ := hk
  refine ⟨⟨fun y z => K (-z) (-y), fun x => ?_⟩, fun g => ?_, fun g => ?_⟩
  · show k (sigT x) = K (-(c2 x)) (-(c1 x))
    rw [hK, c0_sigT, c1_sigT]
  · have e := ipm_sigT k (fun x => g (-c1 x))
    have e2 : (fun x => (fun x => g (-c1 x)) (sigT x)) = fun x => g (c1 x) := by
      funext x; simp only [c1_sigT, neg_neg]
    rw [e2] at e
    rw [e]
    exact h1 (fun u => g (-u))
  · have e := ipm_sigT k (fun x => g (-c0 x))
    have e2 : (fun x => (fun x => g (-c0 x)) (sigT x)) = fun x => g (c2 x) := by
      funext x; simp only [c0_sigT, neg_neg]
    rw [e2] at e
    rw [e]
    exact h0 (fun u => g (-u))

/-- **The edge `24` from the edge `03`** (`lem:oct24:feature-block`(a), proof Step 3, last
sentence): the transport by `ς`. -/
theorem edge24_of_edge03 {c : ℝ} (h03 : Edge03Block F c) (h k : Tri F → ℝ) (hh : IsH c2 h)
    (hk : IsK c0 c1 k) :
    |ipm h k| ≤ c * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k)) := by
  have := h03 _ _ (isH_sigT hh) (isK_sigT hk)
  rwa [ipm_sigT, ipm_sigT, ipm_sigT] at this

/-! ## The embedding into a real inner product space (W2's `feature_frame_middle`) -/

/-- The isometry `L²(m_{0,𝔅}) → EuclideanSpace`, `h ↦ (√m_{0,𝔅}(x) h(x))_x`. -/
noncomputable def emb (h : Tri F → ℝ) : EuclideanSpace ℝ (Tri F) :=
  WithLp.toLp 2 (fun x => Real.sqrt (m0B x) * h x)

theorem inner_emb (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (h k : Tri F → ℝ) :
    ⟪emb h, emb k⟫ = ipm h k := by
  rw [emb, emb, EuclideanSpace.inner_toLp_toLp]
  unfold ipm
  simp only [dotProduct, star_trivial]
  refine sum_congr rfl fun x _ => ?_
  have hm := Real.mul_self_sqrt (m0B_nonneg h7 hF h3 x)
  calc Real.sqrt (m0B x) * k x * (Real.sqrt (m0B x) * h x)
      = (Real.sqrt (m0B x) * Real.sqrt (m0B x)) * h x * k x := by ring
    _ = _ := by rw [hm]

theorem norm_emb (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (h : Tri F → ℝ) :
    ‖emb h‖ = Real.sqrt (ipm h h) := by
  rw [← inner_emb hF h3 h7, real_inner_self_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]

/-- **The five fold features in the actual block law**: `h₀ ∈ 𝓗₀`, `h₁ ∈ 𝓗₁`, `h₂ ∈ 𝓗₂`,
`h₃ ∈ 𝒦₁₂`, `h₄ ∈ 𝒦₀₁` (the labels `0, …, 4` of the paper). -/
def IsFoldFeat (h : Fin 5 → Tri F → ℝ) : Prop :=
  IsH c0 (h 0) ∧ IsH c1 (h 1) ∧ IsH c2 (h 2) ∧ IsK c1 c2 (h 3) ∧ IsK c0 c1 (h 4)

/-- **W2's `hcor` for the actual features**: the correlation bounds of
`lem:oct24:feature-block`(a), at every block with least prime `b ≥ Q₃`, for the embedded features,
in exactly the form of the hypothesis `hcor` of `Envelopes.feature_frame_middle`. The edges `01`,
`02`, `12`, `24`, `34` and the vanishing ones are proved; the edge `03` is the input `h03`. -/
theorem actual_hcor {b : ℝ} (hB : MiddleBlock F b)
    (h03 : Edge03Block F (rho03 (1 / b) (1 / Real.sqrt b))) (h : Fin 5 → Tri F → ℝ)
    (hf : IsFoldFeat h) :
    ∀ i j, i ≠ j → |⟪emb (h i), emb (h j)⟫| ≤ foldPattern (rho02 (1 / b) (1 / Real.sqrt b))
      (rho01 (1 / b)) (rho03 (1 / b) (1 / Real.sqrt b)) (rho34 (1 / b) (1 / Real.sqrt b)) i j *
        ‖emb (h i)‖ * ‖emb (h j)‖ := by
  obtain ⟨f0, f1, f2, f3, f4⟩ := hf
  have hF := hB.hF
  have h3 := hB.h3
  have h7 := hB.h7
  simp only [inner_emb hF h3 h7, norm_emb hF h3 h7]
  -- the symmetric form of an edge bound
  have sym : ∀ {c : ℝ} {u v : Tri F → ℝ},
      |ipm u v| ≤ c * (Real.sqrt (ipm u u) * Real.sqrt (ipm v v)) →
      |ipm v u| ≤ c * Real.sqrt (ipm v v) * Real.sqrt (ipm u u) := by
    intro c u v huv
    rw [ipm_comm]; linarith [huv]
  have dir : ∀ {c : ℝ} {u v : Tri F → ℝ},
      |ipm u v| ≤ c * (Real.sqrt (ipm u u) * Real.sqrt (ipm v v)) →
      |ipm u v| ≤ c * Real.sqrt (ipm u u) * Real.sqrt (ipm v v) := by
    intro c u v huv; linarith [huv]
  have zero : ∀ {u v : Tri F → ℝ}, ipm u v = 0 →
      |ipm u v| ≤ 0 * Real.sqrt (ipm u u) * Real.sqrt (ipm v v) := by
    intro u v huv; rw [huv]; simp
  have zero' : ∀ {u v : Tri F → ℝ}, ipm u v = 0 →
      |ipm v u| ≤ 0 * Real.sqrt (ipm v v) * Real.sqrt (ipm u u) := by
    intro u v huv; rw [ipm_comm, huv]; simp
  have e01 := edge01 hB _ _ f0 f1
  have e02 := edge02 hB _ _ f0 f2
  have e12 := edge12 hB _ _ f1 f2
  have e03 := h03 _ _ f0 f3
  have e24 := edge24_of_edge03 h03 _ _ f2 f4
  have e34 := edge34_block_b hF h3 hB.hb hB.hbp _ _ f3 f4
  have z04 := vanish04 _ _ f0 f4
  have z13 := vanish13 _ _ f1 f3
  have z14 := vanish14 _ _ f1 f4
  have z23 := vanish23 _ _ f2 f3
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp only [foldPattern, Fin.zero_eta, Fin.mk_one,
    Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one]
    <;> first
      | exact absurd rfl hij
      | exact dir e01 | exact dir e02 | exact dir e12 | exact dir e03 | exact dir e24
      | exact dir e34 | exact sym e01 | exact sym e02 | exact sym e12 | exact sym e03
      | exact sym e24 | exact sym e34 | exact zero z04 | exact zero z13 | exact zero z14
      | exact zero z23 | exact zero' z04 | exact zero' z13 | exact zero' z14 | exact zero' z23

/-- **`lem:oct24:feature-block`(b) in the actual block law**: at every block of primes
`p ≡ 3 (mod 4)` with least prime `b ≥ Q₃`, the five fold features satisfy
`‖h₀ + ⋯ + h₄‖² ≤ Γ_F ∑_v ‖h_v‖²` in `L²(m_{0,𝔅})`, given the edge `03`. -/
theorem actual_feature_frame {b : ℝ} (hB : MiddleBlock F b)
    (h03 : Edge03Block F (rho03 (1 / b) (1 / Real.sqrt b))) (h : Fin 5 → Tri F → ℝ)
    (hf : IsFoldFeat h) :
    ipm (fun x => ∑ i, h i x) (fun x => ∑ i, h i x) ≤ (gammaF : ℝ) * ∑ i, ipm (h i) (h i) := by
  have hF := hB.hF
  have h3 := hB.h3
  have h7 := hB.h7
  have hfr := feature_frame_middle hB.hb (fun i => emb (h i)) (actual_hcor hB h03 h hf)
  have esum : ∑ i, emb (h i) = emb (fun x => ∑ i, h i x) := by
    simp only [emb, ← WithLp.toLp_sum]
    congr 1
    funext x
    simp only [Finset.sum_apply, mul_sum]
  rw [esum, norm_emb hF h3 h7, Real.sq_sqrt (by
    rw [← inner_emb hF h3 h7]; exact real_inner_self_nonneg)] at hfr
  have en : ∀ i, ‖emb (h i)‖ ^ 2 = ipm (h i) (h i) := by
    intro i
    rw [norm_emb hF h3 h7,
      Real.sq_sqrt (by rw [← inner_emb hF h3 h7]; exact real_inner_self_nonneg)]
  simpa only [en] using hfr

end Frame

end Sarkozy.OpsFeature

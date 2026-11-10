module

public import Sarkozy.OpsFeature.Sector03
public import Sarkozy.EnvelopeSteps.FeatureCorr
public import Sarkozy.Envelopes.MatchingFrame

@[expose] public section

/-!
# The matching frame in the actual block law (`lem:oct24:feature-block`(c))

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`(c) and proof Step 6: in
`L²(m_{E,𝔅})`, `m_{E,𝔅}` uniform on the triples of labels distinct at every prime (`mEB`), the three
matching features `𝓗₀, 𝓗₁, 𝓗₂` (mean-zero functions of one whole label) satisfy
`‖h₀ + h₁ + h₂‖² ≤ (1 + 1/(b - 1)) ∑ ‖h_i‖² ≤ Γ_E ∑ ‖h_i‖²` (**`matching_frame_actual`**,
**`matching_frame_actual_Q3`**).

W2's `MatchingFrame` proves the bound on one sector; here the sectors are assembled. The pair law of
two coordinates is `⊗_p (uniform on distinct pairs)` (`fiberE01`, `fiberE02`, `fiberE12`), whose
conditional operator is `⊗_p (𝒥 - (I - 𝒥)/(p - 1)) = ∑_S c_S P_S`, `c_S = ∏_{p ∈ S} (-1/(p - 1))`
(`prodOp_matching`); so the cross Gram entries are `c_S ⟨f_S, g_S⟩` on every sector
(`cross_sectors`), and on a sector of size one `-1/(b-1) ≤ c_S < 0`, on larger ones
`|c_S| ≤ 1/(b-1)²` (`sector_bound`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.Mixing Sarkozy.IndexSupport Sarkozy.EnvelopeSteps Sarkozy.Envelopes

section Prime

variable {K : Type*} [Fintype K] [DecidableEq K]

local notation "qK" => (Fintype.card K : ℝ)

/-- The uniform law on the injective triples at one prime. -/
noncomputable def wE (t : K × K × K) : ℝ :=
  if t.1 ≠ t.2.1 ∧ t.1 ≠ t.2.2 ∧ t.2.1 ≠ t.2.2 then 1 / (qK * (qK - 1) * (qK - 2)) else 0

/-- The uniform law on the distinct pairs. -/
noncomputable def mpair (a b : K) : ℝ := if a = b then 0 else 1 / (qK * (qK - 1))

theorem sum_third (h3 : 3 ≤ qK) (a b : K) :
    ∑ z, (if a ≠ b ∧ a ≠ z ∧ b ≠ z then 1 / (qK * (qK - 1) * (qK - 2)) else (0 : ℝ)) =
      mpair a b := by
  unfold mpair
  by_cases hab : a = b
  · simp [hab]
  · rw [ite_eq_right hab]
    have e : ∀ z, (if a ≠ b ∧ a ≠ z ∧ b ≠ z then 1 / (qK * (qK - 1) * (qK - 2)) else (0 : ℝ)) =
        if z ≠ a ∧ z ≠ b then 1 / (qK * (qK - 1) * (qK - 2)) else 0 := by
      intro z
      by_cases h : z ≠ a ∧ z ≠ b
      · rw [ite_eq_left ⟨hab, Ne.symm h.1, Ne.symm h.2⟩, ite_eq_left h]
      · rw [ite_eq_right (fun h' => h ⟨Ne.symm h'.2.1, Ne.symm h'.2.2⟩), ite_eq_right h]
    simp only [e]
    rw [MiddleRecords.sum_ne_ne hab, sum_const, card_univ, nsmul_eq_mul]
    have h1 : qK - 1 ≠ 0 := by intro h; linarith
    have h2 : qK - 2 ≠ 0 := by intro h; linarith
    have h0 : qK ≠ 0 := by intro h; linarith
    field_simp
    ring

theorem fiberE01 (h3 : 3 ≤ qK) (a b : K) :
    ∑ t : K × K × K, (if t.1 = a ∧ t.2.1 = b then wE t else 0) = mpair a b := by
  rw [← sum_third h3 a b, Fintype.sum_prod_type, sum_eq_single a]
  · rw [Fintype.sum_prod_type, sum_eq_single b]
    · simp [wE]
    · intro y _ hy; exact sum_eq_zero fun z _ => by simp [hy]
    · simp
  · intro x _ hx; exact sum_eq_zero fun y _ => by simp [hx]
  · simp

theorem fiberE02 (h3 : 3 ≤ qK) (a b : K) :
    ∑ t : K × K × K, (if t.1 = a ∧ t.2.2 = b then wE t else 0) = mpair a b := by
  rw [Fintype.sum_prod_type, sum_eq_single a]
  · rw [Fintype.sum_prod_type, ← sum_third h3 a b]
    refine sum_congr rfl fun y _ => ?_
    rw [sum_eq_single b]
    · simp only [wE, and_self, ↓reduceIte]
      by_cases h : a ≠ y ∧ a ≠ b ∧ y ≠ b
      · rw [ite_eq_left h, ite_eq_left ⟨h.2.1, h.1, Ne.symm h.2.2⟩]
      · rw [ite_eq_right h, ite_eq_right (fun h' => h ⟨h'.2.1, h'.1, Ne.symm h'.2.2⟩)]
    · intro z _ hz; simp [hz]
    · simp
  · intro x _ hx; exact sum_eq_zero fun y _ => by simp [hx]
  · simp

theorem fiberE12 (h3 : 3 ≤ qK) (a b : K) :
    ∑ t : K × K × K, (if t.2.1 = a ∧ t.2.2 = b then wE t else 0) = mpair a b := by
  rw [Fintype.sum_prod_type, ← sum_third h3 a b]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.sum_prod_type, sum_eq_single a]
  · rw [sum_eq_single b]
    · simp only [wE, and_self, ↓reduceIte]
      by_cases h : a ≠ b ∧ a ≠ x ∧ b ≠ x
      · rw [ite_eq_left ⟨Ne.symm h.2.1, Ne.symm h.2.2, h.1⟩, ite_eq_left h]
      · rw [ite_eq_right (fun h' => h ⟨h'.2.2, Ne.symm h'.1, Ne.symm h'.2.1⟩), ite_eq_right h]
    · intro z _ hz; simp [hz]
    · simp
  · intro y _ hy; exact sum_eq_zero fun z _ => by simp [hy]
  · simp

theorem sum_mpair (h3 : 3 ≤ qK) (a : K) : ∑ b, mpair a b = 1 / qK := by
  have h1 : qK - 1 ≠ 0 := by intro h; linarith
  have h0 : qK ≠ 0 := by intro h; linarith
  have e : ∀ b, mpair a b = 1 / (qK * (qK - 1)) - (if a = b then 1 / (qK * (qK - 1)) else 0) := by
    intro b; unfold mpair; split_ifs <;> ring
  simp only [e, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, sum_ite_eq, mem_univ,
    ↓reduceIte]
  field_simp

theorem fiberE0 (h3 : 3 ≤ qK) (a : K) :
    ∑ t : K × K × K, (if t.1 = a then wE t else 0) = 1 / qK := by
  rw [← sum_mpair h3 a]
  have e : ∀ b, mpair a b = ∑ t : K × K × K, (if t.1 = a ∧ t.2.1 = b then wE t else 0) :=
    fun b => (fiberE01 h3 a b).symm
  simp only [e]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : t.1 = a
  · rw [sum_eq_single t.2.1]
    · simp [ht]
    · intro b _ hb; simp [ht, Ne.symm hb]
    · simp
  · simp [ht]

theorem fiberE1 (h3 : 3 ≤ qK) (a : K) :
    ∑ t : K × K × K, (if t.2.1 = a then wE t else 0) = 1 / qK := by
  rw [← sum_mpair h3 a]
  have e : ∀ b, mpair a b = ∑ t : K × K × K, (if t.2.1 = a ∧ t.2.2 = b then wE t else 0) :=
    fun b => (fiberE12 h3 a b).symm
  simp only [e]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : t.2.1 = a
  · rw [sum_eq_single t.2.2]
    · simp [ht]
    · intro b _ hb; simp [ht, Ne.symm hb]
    · simp
  · simp [ht]

theorem fiberE2 (h3 : 3 ≤ qK) (a : K) :
    ∑ t : K × K × K, (if t.2.2 = a then wE t else 0) = 1 / qK := by
  have hsym : ∀ b, mpair b a = mpair a b := fun b => by
    unfold mpair; by_cases h : a = b <;> simp [h, eq_comm]
  rw [← sum_mpair h3 a]
  have e : ∀ b, mpair a b = ∑ t : K × K × K, (if t.2.1 = b ∧ t.2.2 = a then wE t else 0) :=
    fun b => (hsym b).symm.trans (fiberE12 h3 b a).symm
  simp only [e]
  rw [sum_comm]
  refine sum_congr rfl fun t _ => ?_
  by_cases ht : t.2.2 = a
  · rw [sum_eq_single t.2.1]
    · simp [ht]
    · intro b _ hb; simp [ht, Ne.symm hb]
    · simp
  · simp [ht]

end Prime

section Block

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Fintype (F p)]
  [∀ p, DecidableEq (F p)]

/-- The actual matching law of the block: uniform on the triples distinct at every prime. -/
noncomputable def mEB (x : ∀ p, F p × F p × F p) : ℝ := ∏ p, wE (x p)

/-- The uniform law of one prime label. -/
noncomputable def unifL (p : P) (_ : F p) : ℝ := 1 / (Fintype.card (F p) : ℝ)

/-- The conditional operator of the distinct pairs at a prime: `M = 𝒥 - (I - 𝒥)/(p - 1)`. -/
noncomputable def mMat (p : P) : Matrix (F p) (F p) ℝ :=
  fun u v => (Fintype.card (F p) : ℝ) * mpair u v

/-- The sector constants `c_S = ∏_{p ∈ S} (-1/(p - 1))`. -/
noncomputable def cl (l : P → Bool) : ℝ :=
  ∏ p, (if l p then -(1 / ((Fintype.card (F p) : ℝ) - 1)) else 1)

omit [Fintype P] [DecidableEq P] in
theorem mMat_eq (h3 : ∀ p, (3 : ℝ) ≤ Fintype.card (F p)) (p : P) :
    mMat (F := F) p = wProj (unifL p) false false +
      (-(1 / ((Fintype.card (F p) : ℝ) - 1))) • wProj (unifL p) false true := by
  have hq := h3 p
  have h1 : (Fintype.card (F p) : ℝ) - 1 ≠ 0 := by intro h; linarith
  have h0 : (Fintype.card (F p) : ℝ) ≠ 0 := by intro h; linarith
  ext u v
  simp only [mMat, mpair, wProj, Bool.false_eq_true, ite_false, ite_true, avgMatrix, unifL,
    Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : u = v
  · rw [ite_eq_left h, ite_eq_left h]; field_simp; ring
  · rw [ite_eq_right h, ite_eq_right h]; field_simp; ring

/-- **The conditional operator of a pair of coordinates is `∑_S c_S P_S`.** -/
theorem prodOp_matching (h3 : ∀ p, (3 : ℝ) ≤ Fintype.card (F p)) :
    prodOp (fun p => mMat (F := F) p) =
      ∑ l : P → Bool, cl (F := F) l • wSectorProj (fun p => unifL (F := F) p) noSpec l := by
  have e : prodOp (fun p => mMat (F := F) p) = piKron (fun p => ∑ s : Bool,
      (if s then -(1 / ((Fintype.card (F p) : ℝ) - 1)) else 1) • wProj (unifL p) false s) := by
    show piKron _ = _
    congr 1
    funext p
    rw [mMat_eq h3 p, Fintype.sum_bool]
    simp only [ite_true, Bool.false_eq_true, ite_false, one_smul]
    abel
  rw [e, ← piKron_sum]
  refine sum_congr rfl fun l _ => ?_
  rw [piKron_smul]
  rfl

/-- **The cross terms on the sectors**: for two coordinates whose pair law is uniform on distinct
pairs at every prime, `⟨f(x_a), g(x_b)⟩_{m_E} = ∑_S c_S ⟨f_S, g_S⟩`. -/
theorem cross_sectors (h3 : ∀ p, (3 : ℝ) ≤ Fintype.card (F p))
    (πa πb : ∀ p, F p × F p × F p → F p)
    (hfib : ∀ p (u v : F p), ∑ t, (if πa p t = u ∧ πb p t = v then wE t else 0) = mpair u v)
    (f g : (∀ p, F p) → ℝ) :
    ∑ x, mEB x * f (fun p => πa p (x p)) * g (fun p => πb p (x p)) =
      ∑ l : P → Bool, cl (F := F) l * wip (fun p => unifL (F := F) p)
        (wSectorProj (fun p => unifL p) noSpec l *ᵥ f)
        (wSectorProj (fun p => unifL p) noSpec l *ᵥ g) := by
  have e1 := sum_prod_pair (fun p (t : F p × F p × F p) => wE t) πa πb (fun u v => f u * g v)
  simp only [hfib] at e1
  have e2 : ∑ x, mEB x * f (fun p => πa p (x p)) * g (fun p => πb p (x p)) =
      wip (fun p => unifL (F := F) p) f (prodOp (fun p => mMat (F := F) p) *ᵥ g) := by
    rw [show (∑ x, mEB x * f (fun p => πa p (x p)) * g (fun p => πb p (x p))) =
      ∑ x : ∀ p, F p × F p × F p, (∏ p, wE (x p)) *
        (f (fun p => πa p (x p)) * g (fun p => πb p (x p))) from
      sum_congr rfl fun x _ => by unfold mEB; ring, e1]
    unfold wip
    refine sum_congr rfl fun u _ => ?_
    simp only [mulVec, dotProduct, mul_sum]
    refine sum_congr rfl fun v _ => ?_
    have e : prodW (fun p => unifL (F := F) p) u * prodOp (fun p => mMat (F := F) p) u v =
        ∏ p, mpair (u p) (v p) := by
      simp only [prodW, prodOp, unifL, mMat, ← prod_mul_distrib]
      refine prod_congr rfl fun p _ => ?_
      have := h3 p
      have h0 : (Fintype.card (F p) : ℝ) ≠ 0 := by intro h; linarith
      field_simp
    rw [← e]
    ring
  rw [e2, prodOp_matching h3, Matrix.sum_mulVec]
  unfold wip
  simp only [Finset.sum_apply, Matrix.smul_mulVec, Pi.smul_apply, smul_eq_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun l _ => ?_
  have hsa := wip_sectorProj (fun p => unifL (F := F) p) l f
    (wSectorProj (fun p => unifL p) noSpec l *ᵥ g)
  have hid := sectorProj_idem (fun p => unifL (F := F) p) (fun p => by
    have := h3 p
    have h0 : (Fintype.card (F p) : ℝ) ≠ 0 := by intro h; linarith
    simp only [unifL, sum_const, card_univ, nsmul_eq_mul]; field_simp) l g
  rw [hid] at hsa
  unfold wip at hsa
  calc ∑ x, prodW (fun p => unifL (F := F) p) x * f x *
        (cl (F := F) l * (wSectorProj (fun p => unifL p) noSpec l *ᵥ g) x)
      = cl (F := F) l * ∑ x, prodW (fun p => unifL (F := F) p) x * f x *
          (wSectorProj (fun p => unifL p) noSpec l *ᵥ g) x := by
        rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    _ = _ := by rw [← hsa, mul_sum]

/-- The diagonal terms: every coordinate of `m_E` is uniform. -/
theorem diag_matching (π : ∀ p, F p × F p × F p → F p)
    (hfib : ∀ p (u : F p), ∑ t, (if π p t = u then wE t else 0) = 1 / (Fintype.card (F p) : ℝ))
    (f : (∀ p, F p) → ℝ) :
    ∑ x, mEB x * f (fun p => π p (x p)) ^ 2 =
      ∑ u, prodW (fun p => unifL (F := F) p) u * f u ^ 2 := by
  have e := sum_prod_single (fun p (t : F p × F p × F p) => wE t) π (fun u => f u ^ 2)
  simp only [hfib] at e
  exact e

omit [DecidableEq P] [∀ p, DecidableEq (F p)] in
/-- The bound of the sector constants: `-1/(b-1) ≤ c_S ≤ 1/(b-1)²` for `S ≠ ∅`. -/
theorem cl_bounds {b : ℝ} (hb : 3 ≤ b) (hbp : ∀ p, b ≤ Fintype.card (F p)) {l : P → Bool}
    (hl : ∃ p, l p = true) :
    -(1 / (b - 1)) ≤ cl (F := F) l ∧ cl (F := F) l ≤ 1 / (b - 1) ^ 2 := by
  set S := univ.filter (fun p => l p = true) with hS
  have hb1 : 0 < b - 1 := by linarith
  have hcl : cl (F := F) l = ∏ p ∈ S, (-(1 / ((Fintype.card (F p) : ℝ) - 1))) := by
    unfold cl; rw [Finset.prod_ite, prod_const_one, mul_one]
  have hq : ∀ p, 0 < (Fintype.card (F p) : ℝ) - 1 := fun p => by linarith [hbp p]
  have hle : ∀ p, 1 / ((Fintype.card (F p) : ℝ) - 1) ≤ 1 / (b - 1) := fun p =>
    one_div_le_one_div_of_le hb1 (by linarith [hbp p])
  have habs : |cl (F := F) l| ≤ (1 / (b - 1)) ^ S.card := by
    rw [hcl, abs_prod, ← prod_const]
    refine Finset.prod_le_prod₀ (fun p _ => abs_nonneg _) fun p _ => ?_
    rw [abs_neg, abs_of_pos (by have := hq p; positivity)]
    exact hle p
  obtain ⟨p₀, hp₀⟩ := hl
  have hne : S.card ≠ 0 := by
    rw [Finset.card_ne_zero]; exact ⟨p₀, by simp [hS, hp₀]⟩
  have hb2 : 1 / (b - 1) ≤ 1 := by rw [div_le_one hb1]; linarith
  have hb0 : 0 ≤ 1 / (b - 1) := by positivity
  by_cases h1 : S.card = 1
  · obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
    rw [hcl, hp, prod_singleton]
    constructor
    · exact neg_le_neg (hle p)
    · have : 0 ≤ 1 / ((Fintype.card (F p) : ℝ) - 1) := by have := hq p; positivity
      have : 0 ≤ 1 / (b - 1) ^ 2 := by positivity
      linarith
  · have h2 : 2 ≤ S.card := by omega
    have hpow : (1 / (b - 1)) ^ S.card ≤ (1 / (b - 1)) ^ 2 :=
      pow_le_pow_of_le_one hb0 hb2 h2
    have hsq : (1 / (b - 1)) ^ 2 ≤ 1 / (b - 1) := by
      rw [sq]; exact mul_le_of_le_one_left hb0 hb2
    have := abs_le.mp (habs.trans hpow)
    rw [_root_.one_div_pow] at this hsq
    constructor <;> linarith [this.1, this.2]

end Block

section Frame

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Fintype (F p)]
  [∀ p, DecidableEq (F p)]

/-- The per-sector bound `S + c(T - S) ≤ (1 + 1/(b-1)) S` for `0 ≤ T ≤ 3S`. -/
theorem sector_bound {b c S T : ℝ} (hb : 3 ≤ b) (hc : -(1 / (b - 1)) ≤ c ∧ c ≤ 1 / (b - 1) ^ 2)
    (hT0 : 0 ≤ T) (hT3 : T ≤ 3 * S) : S + c * (T - S) ≤ (1 + 1 / (b - 1)) * S := by
  have hb1 : 0 < b - 1 := by linarith
  have hS : 0 ≤ S := by linarith
  have h2 : 2 / (b - 1) ^ 2 ≤ 1 / (b - 1) := by
    rw [div_le_div_iff₀ (by positivity) hb1]; nlinarith
  rcases le_or_gt 0 c with hc0 | hc0
  · have a : c * (T - S) ≤ c * (2 * S) := mul_le_mul_of_nonneg_left (by linarith) hc0
    have b' : c * (2 * S) ≤ 1 / (b - 1) ^ 2 * (2 * S) :=
      mul_le_mul_of_nonneg_right hc.2 (by linarith)
    have : 1 / (b - 1) ^ 2 * (2 * S) = 2 / (b - 1) ^ 2 * S := by ring
    have d : 2 / (b - 1) ^ 2 * S ≤ 1 / (b - 1) * S := mul_le_mul_of_nonneg_right h2 hS
    nlinarith
  · have a : c * (T - S) ≤ c * (-S) := by
      have : -S ≤ T - S := by linarith
      nlinarith
    have b' : c * (-S) ≤ 1 / (b - 1) * S := by nlinarith [hc.1]
    nlinarith

/-- **`lem:oct24:feature-block`(c), the matching frame in the actual block law**: for mean-zero
`f₀, f₁, f₂` (uniform), `‖f₀(x₀) + f₁(x₁) + f₂(x₂)‖² ≤ (1 + 1/(b-1)) ∑ ‖f_i(x_i)‖²` in
`L²(m_{E,𝔅})`, at a block whose primes are at least `b ≥ 3`. -/
theorem matching_frame_actual (h3 : ∀ p, (3 : ℝ) ≤ Fintype.card (F p)) {b : ℝ} (hb : 3 ≤ b)
    (hbp : ∀ p, b ≤ Fintype.card (F p)) (f₀ f₁ f₂ : (∀ p, F p) → ℝ)
    (hf₀ : ∑ u, prodW (fun p => unifL (F := F) p) u * f₀ u = 0)
    (hf₁ : ∑ u, prodW (fun p => unifL (F := F) p) u * f₁ u = 0)
    (hf₂ : ∑ u, prodW (fun p => unifL (F := F) p) u * f₂ u = 0) :
    ∑ x, mEB x * (f₀ (fun p => (x p).1) + f₁ (fun p => (x p).2.1) + f₂ (fun p => (x p).2.2)) ^ 2 ≤
      (1 + 1 / (b - 1)) * (∑ x, mEB x * f₀ (fun p => (x p).1) ^ 2 +
        ∑ x, mEB x * f₁ (fun p => (x p).2.1) ^ 2 + ∑ x, mEB x * f₂ (fun p => (x p).2.2) ^ 2) := by
  set w : ∀ p, F p → ℝ := fun p => unifL (F := F) p with hw
  have hw0 : ∀ p a, 0 ≤ w p a := fun p a => by
    have := h3 p; simp only [hw, unifL]; positivity
  have hw1 : ∀ p, ∑ a, w p a = 1 := fun p => by
    have := h3 p
    have h0 : (Fintype.card (F p) : ℝ) ≠ 0 := by intro h; linarith
    simp only [hw, unifL, sum_const, card_univ, nsmul_eq_mul]; field_simp
  have hwP : ∀ a, 0 ≤ prodW w a := fun a => prod_nonneg fun p _ => hw0 p (a p)
  set PI : (P → Bool) → ((∀ p, F p) → ℝ) → (∀ p, F p) → ℝ :=
    fun l g => wSectorProj w noSpec l *ᵥ g with hPI
  -- the six terms
  have X01 := cross_sectors h3 (fun p t => t.1) (fun p t => t.2.1)
    (fun p u v => fiberE01 (h3 p) u v)
    f₀ f₁
  have X02 := cross_sectors h3 (fun p t => t.1) (fun p t => t.2.2)
    (fun p u v => fiberE02 (h3 p) u v)
    f₀ f₂
  have X12 := cross_sectors h3 (fun p t => t.2.1) (fun p t => t.2.2)
    (fun p u v => fiberE12 (h3 p) u v) f₁ f₂
  have D0 := diag_matching (fun p t => t.1) (fun p u => fiberE0 (h3 p) u) f₀
  have D1 := diag_matching (fun p t => t.2.1) (fun p u => fiberE1 (h3 p) u) f₁
  have D2 := diag_matching (fun p t => t.2.2) (fun p u => fiberE2 (h3 p) u) f₂
  have P0 := general_parseval w noSpec hw0 hw1 f₀
  have P1 := general_parseval w noSpec hw0 hw1 f₁
  have P2 := general_parseval w noSpec hw0 hw1 f₂
  -- the expansion of the square
  have hexp : ∑ x, mEB x * (f₀ (fun p => (x p).1) + f₁ (fun p => (x p).2.1) +
      f₂ (fun p => (x p).2.2)) ^ 2 =
      ∑ x, mEB x * f₀ (fun p => (x p).1) ^ 2 + ∑ x, mEB x * f₁ (fun p => (x p).2.1) ^ 2 +
      ∑ x, mEB x * f₂ (fun p => (x p).2.2) ^ 2 +
      2 * ∑ x, mEB x * f₀ (fun p => (x p).1) * f₁ (fun p => (x p).2.1) +
      2 * ∑ x, mEB x * f₀ (fun p => (x p).1) * f₂ (fun p => (x p).2.2) +
      2 * ∑ x, mEB x * f₁ (fun p => (x p).2.1) * f₂ (fun p => (x p).2.2) := by
    simp only [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun x _ => by ring
  rw [hexp, X01, X02, X12, D0, D1, D2, P0, P1, P2]
  -- one sector
  have hper : ∀ l : P → Bool,
      ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₀) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₁) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₂) a ^ 2 +
        2 * (cl (F := F) l * wip w (wSectorProj w noSpec l *ᵥ f₀) (wSectorProj w noSpec l *ᵥ f₁)) +
        2 * (cl (F := F) l * wip w (wSectorProj w noSpec l *ᵥ f₀) (wSectorProj w noSpec l *ᵥ f₂)) +
        2 * (cl (F := F) l * wip w (wSectorProj w noSpec l *ᵥ f₁) (wSectorProj w noSpec l *ᵥ f₂)) ≤
      (1 + 1 / (b - 1)) * (∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₀) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₁) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₂) a ^ 2) := by
    intro l
    set u₀ := wSectorProj w noSpec l *ᵥ f₀
    set u₁ := wSectorProj w noSpec l *ᵥ f₁
    set u₂ := wSectorProj w noSpec l *ᵥ f₂
    set S := ∑ a, prodW w a * u₀ a ^ 2 + ∑ a, prodW w a * u₁ a ^ 2 + ∑ a, prodW w a * u₂ a ^ 2
      with hS
    set T := ∑ a, prodW w a * (u₀ a + u₁ a + u₂ a) ^ 2 with hT
    have hTe : T = S + 2 * (wip w u₀ u₁ + wip w u₀ u₂ + wip w u₁ u₂) := by
      simp only [hT, hS, wip, mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun a _ => by ring
    have hT0 : 0 ≤ T := sum_nonneg fun a _ => mul_nonneg (hwP a) (sq_nonneg _)
    have hT3 : T ≤ 3 * S := by
      simp only [hT, hS, mul_sum, ← sum_add_distrib]
      refine sum_le_sum fun a _ => ?_
      have := hwP a
      nlinarith [sq_nonneg (u₀ a - u₁ a), sq_nonneg (u₀ a - u₂ a), sq_nonneg (u₁ a - u₂ a)]
    have hgoal : S + cl (F := F) l * (T - S) ≤ (1 + 1 / (b - 1)) * S := by
      by_cases hl : ∃ p, l p = true
      · exact sector_bound hb (cl_bounds hb hbp hl) hT0 hT3
      · have hl' : l = fun _ => false := by
          funext p
          cases h : l p
          · rfl
          · exact absurd ⟨p, h⟩ hl
        have z0 : u₀ = 0 := by simp only [u₀, hl']; exact sectorProj_empty w f₀ hf₀
        have z1 : u₁ = 0 := by simp only [u₁, hl']; exact sectorProj_empty w f₁ hf₁
        have z2 : u₂ = 0 := by simp only [u₂, hl']; exact sectorProj_empty w f₂ hf₂
        have hS0 : S = 0 := by simp [hS, z0, z1, z2]
        have hT00 : T = 0 := by simp [hT, z0, z1, z2]
        rw [hS0, hT00]; simp
    rw [hTe] at hgoal
    linarith [hgoal]
  calc _ = ∑ l : P → Bool, (∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₀) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₁) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₂) a ^ 2 +
        2 * (cl (F := F) l * wip w (wSectorProj w noSpec l *ᵥ f₀) (wSectorProj w noSpec l *ᵥ f₁)) +
        2 * (cl (F := F) l * wip w (wSectorProj w noSpec l *ᵥ f₀) (wSectorProj w noSpec l *ᵥ f₂)) +
        2 * (cl (F := F) l *
          wip w (wSectorProj w noSpec l *ᵥ f₁) (wSectorProj w noSpec l *ᵥ f₂))) := by
        rw [sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib, sum_add_distrib,
          ← mul_sum, ← mul_sum, ← mul_sum]
    _ ≤ ∑ l : P → Bool, (1 + 1 / (b - 1)) * (∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₀) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₁) a ^ 2 +
        ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ f₂) a ^ 2) := sum_le_sum fun l _ => hper l
    _ = _ := by rw [← mul_sum, sum_add_distrib, sum_add_distrib]

/-- **`lem:oct24:feature-block`(c) at every middle block**: `Γ_E = 19951586/19951585`. -/
theorem matching_frame_actual_Q3 (h3 : ∀ p, (3 : ℝ) ≤ Fintype.card (F p)) {b : ℝ}
    (hb : 19951586 ≤ b) (hbp : ∀ p, b ≤ Fintype.card (F p)) (f₀ f₁ f₂ : (∀ p, F p) → ℝ)
    (hf₀ : ∑ u, prodW (fun p => unifL (F := F) p) u * f₀ u = 0)
    (hf₁ : ∑ u, prodW (fun p => unifL (F := F) p) u * f₁ u = 0)
    (hf₂ : ∑ u, prodW (fun p => unifL (F := F) p) u * f₂ u = 0) :
    ∑ x, mEB x * (f₀ (fun p => (x p).1) + f₁ (fun p => (x p).2.1) + f₂ (fun p => (x p).2.2)) ^ 2 ≤
      (19951586 / 19951585 : ℝ) * (∑ x, mEB x * f₀ (fun p => (x p).1) ^ 2 +
        ∑ x, mEB x * f₁ (fun p => (x p).2.1) ^ 2 + ∑ x, mEB x * f₂ (fun p => (x p).2.2) ^ 2) := by
  refine (matching_frame_actual h3 (by linarith) hbp f₀ f₁ f₂ hf₀ hf₁ hf₂).trans ?_
  apply mul_le_mul_of_nonneg_right (matching_frame_constant hb)
  have h : ∀ (π : ∀ p, F p × F p × F p → F p) (g : (∀ p, F p) → ℝ),
      0 ≤ ∑ x, mEB x * g (fun p => π p (x p)) ^ 2 := fun π g =>
    sum_nonneg fun x _ => mul_nonneg (prod_nonneg fun p _ => by
      unfold wE; split_ifs
      · have := h3 p
        have : 0 < (Fintype.card (F p) : ℝ) - 2 := by linarith
        have : 0 < (Fintype.card (F p) : ℝ) - 1 := by linarith
        positivity
      · exact le_rfl) (sq_nonneg _)
  exact add_nonneg (add_nonneg (h (fun p t => t.1) f₀) (h (fun p t => t.2.1) f₁))
    (h (fun p t => t.2.2) f₂)

end Frame

end Sarkozy.OpsFeature

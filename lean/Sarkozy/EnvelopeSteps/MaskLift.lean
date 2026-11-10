module

public import Sarkozy.EnvelopeSteps.Placement
public import Mathlib.Analysis.Matrix.Order

@[expose] public section

/-!
# The lifting step of the matrix envelopes (`lem:oct24:mask-schur`(a))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a) and its proof. The tensor
`⊗_𝔅 L_𝔅` of the leading stars is the orthogonal sum, over the choices of one singleton sector
at every block, of `(∏ c) Ξ T Ξ^*`, and the proof shows `±⊗_𝔅 L_𝔅 ⪯ Lift(D)` in four moves:

1. **joint spectral decomposition**: `D ⊗ I ± T ⪰ 0` on every sector, from the conditions
   `eq:matrix-envelope` at every `ξ ∈ {±i}^X`;
2. **scaling**: `D ⪰ 0` and `0 ≤ ∏ c ≤ 1` give `D ⊗ I ± (∏ c) T ⪰ 0`;
3. **congruence and sum**: `Ξ (D ⊗ I) Ξ^* ± (∏ c) Ξ T Ξ^* ⪰ 0`, summed over the choices;
4. **positive enlargement**: `∑ Ξ (D ⊗ I) Ξ^* ⪯ Lift(D)`, by adding the positive congruences of
   the other sectors and replacing, one coordinate at a time, the factor `Z Z^*` by
   `Π_{𝒦₁₂} ⪯ Q₁₂` and `0` by `Q₀₁`.

Formalized here, for real matrices (the operators of the actual half spaces in a basis):

* **`scale_pm`** (move 2) and **`mask_lift_sum`** (moves 2–3, all sectors at once);
* **`mask_lift`**: moves 2–3 together with the enlargement (move 4) as a hypothesis give
  `Lift(D) ± ∑ c Ξ T Ξ^* ⪰ 0`;
* the tools of move 4: **`kron_mono`** ("replacing a factor of a tensor product of positive
  operators by a larger positive operator increases it": `A ⪰ 0`, `B ⪯ B'` give
  `A ⊗ B ⪯ A ⊗ B'`, and the same on the left, `kron_mono_left`) and **`contraction_le_proj`**
  (`Z Z^* ⪯ Π` for a contraction `Z` into the range of an orthogonal projection `Π`, the step
  `Z_𝔅 Z_𝔅^* ⪯ Π_{𝒦₁₂}`);
* **`opLE_of_feature_form`**: the domination `±L ⪯ D` in `L²(m)` from a bound
  `|∑⟪x_w, T_{wv} x_v⟫| ≤ ∑ d_v ‖x_v‖²` on the feature form (the conclusion of W2's `mask_schur`,
  `lem:oct24:mask-schur`(c), and of the five checked diagonal witnesses `F*_envelope`), given the
  feature representations of the forms of `L` and `D`; this bypasses move 1 for diagonal envelopes;
* **`opPos_conj`**, **`opLE_conj`**: the chart conjugation by a measure-preserving involution
  (the arithmetic transport `𝒰`, a name permutation `𝒫_β`) preserves the order of `L²(m)`;
* **`opPos_of_kern`** and **`opLE_of_mask`**: the bridge to the order of `L²(m)` of
  `Placement.lean`. If the kernels of `Lead` and `Lop` relative to `m` are the matrices
  `∑ c Ξ T Ξ^*` and `Lift(D)`, then `±Lead ⪯ Lop` in `L²(m)`, which is the hypothesis `hdom` of
  `envStepsOfOperators` (Step 2 of `thm:envelopes`).

**Used as hypotheses:** move 1 (`hspec`, the joint spectral decomposition of the commuting phases
`Φ̂_p`; it needs the complexification and is not formalized), and move 4 as an inequality
(`hLift`), whose ingredients `Π_{𝒦₁₂} ⪯ Q₁₂`, `0 ⪯ Q₀₁` are W2's
`Envelopes.pureSubstitute_loewner` (`lem:oct24:pure-pair-substitute`) in Mathlib's Loewner order.
The second and third assertions of (a) (annihilation of the constants, the coupling expansion and
the coupling mass) are not formalized here.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace Sarkozy.EnvelopeSteps

/-! ## Moves 2 and 3 -/

section Assembly

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] [DecidableEq W] in
/-- **Move 2**: `M ± T ⪰ 0` and `0 ≤ c ≤ 1` give `M ± c T ⪰ 0`. -/
theorem scale_pm {M T : Matrix W W ℝ} (hp : (M + T).PosSemidef) (hm : (M - T).PosSemidef)
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    (M + c • T).PosSemidef ∧ (M - c • T).PosSemidef := by
  have ha : 0 ≤ (1 + c) / 2 := by linarith
  have hb : 0 ≤ (1 - c) / 2 := by linarith
  have e1 : M + c • T = ((1 + c) / 2) • (M + T) + ((1 - c) / 2) • (M - T) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  have e2 : M - c • T = ((1 - c) / 2) • (M + T) + ((1 + c) / 2) • (M - T) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
    ring
  rw [e1, e2]
  exact ⟨(hp.smul ha).add (hm.smul hb), (hp.smul hb).add (hm.smul ha)⟩

variable {S : Type*} [Fintype S] {Z : S → Type*} [∀ s, Fintype (Z s)] [∀ s, DecidableEq (Z s)]
  {O : Type*} [Fintype O]

omit [DecidableEq W] in
/-- **Moves 2–3 of `lem:oct24:mask-schur`(a)**: if `D ⊗ I ± T_s ⪰ 0` on every sector `s`
(move 1) and `0 ≤ c_s ≤ 1`, then `∑_s Ξ_s (D ⊗ I) Ξ_s^* ± ∑_s c_s Ξ_s T_s Ξ_s^* ⪰ 0`. -/
theorem mask_lift_sum (D : Matrix W W ℝ) (T : ∀ s, Matrix (W × Z s) (W × Z s) ℝ) (c : S → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hc1 : ∀ s, c s ≤ 1)
    (hspec : ∀ s, (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) + T s).PosSemidef ∧
      (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) - T s).PosSemidef)
    (Ξ : ∀ s, Matrix O (W × Z s) ℝ) :
    (∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ +
        ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ)).PosSemidef ∧
    (∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ -
        ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ)).PosSemidef := by
  have hs := fun s => scale_pm (hspec s).1 (hspec s).2 (hc0 s) (hc1 s)
  have ep : ∀ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ +
      c s • (Ξ s * T s * (Ξ s)ᴴ) =
      Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) + c s • T s) * (Ξ s)ᴴ := by
    intro s
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  have em : ∀ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ -
      c s • (Ξ s * T s * (Ξ s)ᴴ) =
      Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) - c s • T s) * (Ξ s)ᴴ := by
    intro s
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [← sum_add_distrib, ← sum_sub_distrib]
  simp only [ep, em]
  exact ⟨posSemidef_sum univ fun s _ => (hs s).1.mul_mul_conjTranspose_same (Ξ s),
    posSemidef_sum univ fun s _ => (hs s).2.mul_mul_conjTranspose_same (Ξ s)⟩

omit [DecidableEq W] in
/-- **`lem:oct24:mask-schur`(a), `±⊗_𝔅 L_𝔅 ⪯ Lift(D)`**, from move 1 (`hspec`) and the
positive enlargement `∑ Ξ (D ⊗ I) Ξ^* ⪯ Lift(D)` (`hLift`, move 4), where
`L = ∑_s c_s Ξ_s T_s Ξ_s^*` is the tensor of the leading stars written as its orthogonal sum
over the singleton sectors. -/
theorem mask_lift (D : Matrix W W ℝ) (T : ∀ s, Matrix (W × Z s) (W × Z s) ℝ) (c : S → ℝ)
    (hc0 : ∀ s, 0 ≤ c s) (hc1 : ∀ s, c s ≤ 1)
    (hspec : ∀ s, (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) + T s).PosSemidef ∧
      (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ) - T s).PosSemidef)
    (Ξ : ∀ s, Matrix O (W × Z s) ℝ) (Lift : Matrix O O ℝ)
    (hLift : (Lift - ∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ).PosSemidef) :
    (Lift + ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ)).PosSemidef ∧
    (Lift - ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ)).PosSemidef := by
  obtain ⟨hp, hm⟩ := mask_lift_sum D T c hc0 hc1 hspec Ξ
  constructor
  · have e : Lift + ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ) =
        (Lift - ∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ) +
        (∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ +
          ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ)) := by abel
    rw [e]
    exact hLift.add hp
  · have e : Lift - ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ) =
        (Lift - ∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ) +
        (∑ s, Ξ s * (D ⊗ₖ (1 : Matrix (Z s) (Z s) ℝ)) * (Ξ s)ᴴ -
          ∑ s, c s • (Ξ s * T s * (Ξ s)ᴴ)) := by abel
    rw [e]
    exact hLift.add hm

end Assembly

/-! ## The tools of move 4 -/

section Enlargement

variable {n k : Type*} [Fintype n] [Fintype k] [DecidableEq n] [DecidableEq k]

omit [DecidableEq n] [DecidableEq k] in
/-- **Positive enlargement in a tensor factor**: `A ⪰ 0` and `B ⪯ B'` give `A ⊗ B ⪯ A ⊗ B'`. -/
theorem kron_mono {A : Matrix n n ℝ} {B B' : Matrix k k ℝ} (hA : A.PosSemidef)
    (hB : (B' - B).PosSemidef) : (A ⊗ₖ B' - A ⊗ₖ B).PosSemidef := by
  have e : A ⊗ₖ B' - A ⊗ₖ B = A ⊗ₖ (B' - B) := by
    ext i j
    simp only [Matrix.sub_apply, kroneckerMap_apply, mul_sub]
  rw [e]
  exact hA.kronecker hB

omit [DecidableEq n] [DecidableEq k] in
/-- The same in the left factor: `A ⪯ A'`, `B ⪰ 0` give `A ⊗ B ⪯ A' ⊗ B`. -/
theorem kron_mono_left {A A' : Matrix n n ℝ} {B : Matrix k k ℝ} (hA : (A' - A).PosSemidef)
    (hB : B.PosSemidef) : (A' ⊗ₖ B - A ⊗ₖ B).PosSemidef := by
  have e : A' ⊗ₖ B - A ⊗ₖ B = (A' - A) ⊗ₖ B := by
    ext i j
    simp only [Matrix.sub_apply, kroneckerMap_apply, sub_mul]
  rw [e]
  exact hA.kronecker hB

omit [DecidableEq k] in
/-- **`Z Z^* ⪯ Π`** for an orthogonal projection `Π` (`Π^* = Π`, `Π² = Π`) and a contraction `Z`
(`Z Z^* ⪯ I`) with range in that of `Π` (`Π Z = Z`): the step `Z_𝔅 Z_𝔅^* ⪯ Π_{𝒦₁₂}` of the proof
of `lem:oct24:mask-schur`(a). -/
theorem contraction_le_proj {Pi : Matrix n n ℝ} {Zm : Matrix n k ℝ} (hP : Piᴴ = Pi)
    (hPP : Pi * Pi = Pi) (hPZ : Pi * Zm = Zm) (hZ : (1 - Zm * Zmᴴ).PosSemidef) :
    (Pi - Zm * Zmᴴ).PosSemidef := by
  have h1 : Zmᴴ * Pi = Zmᴴ := by
    have := congrArg conjTranspose hPZ
    rwa [conjTranspose_mul, hP] at this
  have e : Pi * (1 - Zm * Zmᴴ) * Piᴴ = Pi - Zm * Zmᴴ := by
    rw [hP, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPP, ← Matrix.mul_assoc, hPZ,
      Matrix.mul_assoc, h1]
  rw [← e]
  exact hZ.mul_mul_conjTranspose_same Pi

end Enlargement

/-! ## The bridge to the order of `L²(m)` -/

section Bridge

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- A linear map whose kernel relative to `m` is positive semidefinite is positive in `L²(m)`. -/
theorem opPos_of_kern {m : O → ℝ} {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (hK : (Matrix.of fun x y => kern m K x y).PosSemidef) : OpPos m K := by
  have hsymm : ∀ x y, kern m K x y = kern m K y x := by
    intro x y
    have h := congrFun (congrFun hK.isHermitian x) y
    simpa only [conjTranspose_apply, star_trivial, of_apply] using h.symm
  constructor
  · intro f g
    rw [ip_eq_kern, ip_eq_kern, sum_comm]
    refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
    rw [hsymm]
    ring
  · intro f
    rw [ip_eq_kern]
    have hh := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hK).2 f
    simpa only [dotProduct, mulVec, star_trivial, of_apply, sum_mul, mul_sum, mul_left_comm,
      mul_comm, mul_assoc] using hh

omit [Fintype O] in
theorem kern_neg (m : O → ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) :
    kern m (-K) x y = -kern m K x y := by
  simp only [kern, LinearMap.neg_apply, Pi.neg_apply, mul_neg]

/-- **The domination hypothesis of Step 2 from the lifting step**: if the kernels of `Lead` and
`Lop` relative to `m` are the matrices `L` and `Lift` with `Lift ± L ⪰ 0` (`mask_lift`), then
`±Lead ⪯ Lop` in `L²(m)`. -/
theorem opLE_of_mask {m : O → ℝ} {Lead Lop : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {L Lift : Matrix O O ℝ}
    (hL : ∀ x y, kern m Lead x y = L x y) (hLift : ∀ x y, kern m Lop x y = Lift x y)
    (hp : (Lift + L).PosSemidef) (hm : (Lift - L).PosSemidef) :
    OpLE m Lead Lop ∧ OpLE m (-Lead) Lop := by
  constructor
  · apply opPos_of_kern
    have e : (Matrix.of fun x y => kern m (Lop - Lead) x y) = Lift - L := by
      ext x y
      simp only [of_apply, kern_sub, hL, hLift, Matrix.sub_apply]
    rw [e]
    exact hm
  · apply opPos_of_kern
    have e : (Matrix.of fun x y => kern m (Lop - -Lead) x y) = Lift + L := by
      ext x y
      simp only [of_apply, sub_neg_eq_add, kern_add, hL, hLift, Matrix.add_apply]
    rw [e]
    exact hp

end Bridge

/-! ## The chart conjugation -/

section Chart

variable {O : Type*} [Fintype O]

/-- The transport `𝒰 f = f ∘ σ` as a linear map. -/
def transportL (σ : O → O) : (O → ℝ) →ₗ[ℝ] (O → ℝ) where
  toFun f := fun x => f (σ x)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- **The chart conjugation preserves the order of `L²(m)`**: for an involution `σ` preserving
`m` (e.g. the arithmetic transport `ς` of `lem:reflection-averaging`(b), or a name permutation
`𝒫_β`), `K ⪰ 0` gives `𝒰 K 𝒰 ⪰ 0`. So `±𝒰^* L 𝒰 ⪯ Lift(D)` in the chart gives
`±L ⪯ 𝒰 Lift(D) 𝒰^*` (Step 2 of `thm:envelopes`, with `lem:reflection-averaging`(e)). -/
theorem opPos_conj {σ : O → O} (hσ : ∀ x, σ (σ x) = x) {m : O → ℝ} (hm : ∀ x, m (σ x) = m x)
    {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (hK : OpPos m K) :
    OpPos m (transportL σ ∘ₗ K ∘ₗ transportL σ) := by
  have hiso : ∀ f g : O → ℝ, ip m (transportL σ f) g = ip m f (transportL σ g) := by
    intro f g
    unfold ip transportL
    simp only [LinearMap.coe_mk, AddHom.coe_mk]
    rw [← Equiv.sum_comp ⟨σ, σ, hσ, hσ⟩]
    refine sum_congr rfl fun x _ => ?_
    change m (σ x) * (f (σ (σ x)) * g (σ x)) = m x * (f x * g (σ x))
    rw [hm, hσ]
  constructor
  · intro f g
    simp only [LinearMap.comp_apply]
    rw [← hiso, ← hiso, hK.symm]
  · intro f
    simp only [LinearMap.comp_apply]
    rw [← hiso]
    exact hK.nonneg _

/-- The chart conjugation of the domination: `±K ⪯ K'` gives `±𝒰K𝒰 ⪯ 𝒰K'𝒰`. -/
theorem opLE_conj {σ : O → O} (hσ : ∀ x, σ (σ x) = x) {m : O → ℝ} (hm : ∀ x, m (σ x) = m x)
    {K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (h : OpLE m K K') :
    OpLE m (transportL σ ∘ₗ K ∘ₗ transportL σ) (transportL σ ∘ₗ K' ∘ₗ transportL σ) := by
  have e : transportL σ ∘ₗ K' ∘ₗ transportL σ - transportL σ ∘ₗ K ∘ₗ transportL σ =
      transportL σ ∘ₗ (K' - K) ∘ₗ transportL σ := by
    rw [LinearMap.sub_comp, LinearMap.comp_sub]
  unfold OpLE
  rw [e]
  exact opPos_conj hσ hm h

end Chart

/-! ## The bridge from the mask Schur test (`lem:oct24:mask-schur`(c)) -/

section MaskSchurBridge

variable {O : Type*} [Fintype O] {Vf E : Type*} [Fintype Vf] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

/-- **The domination of Step 2 from a feature-form bound** (`lem:oct24:mask-schur`(c), whose
conclusion is W2's `mask_schur`, `checked_table_envelope` and `F*_envelope` for the five diagonal
witnesses): if the forms of `L` and `D` in `L²(m)` are, in feature coordinates `ι_v`,
`⟨f, L f⟩ = ∑_{v,w} ⟪ι_w f, T_{wv} ι_v f⟫` and `⟨f, D f⟩ = ∑_v d_v ‖ι_v f‖²`, both operators are
symmetric, and the feature form satisfies `|∑⟪x_w, T_{wv} x_v⟫| ≤ ∑ d_v ‖x_v‖²`, then
`±L ⪯ D` in `L²(m)`. -/
theorem opLE_of_feature_form {m : O → ℝ} {Lop Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ)}
    (T : Vf → Vf → E →ₗ[ℝ] E) (d : Vf → ℝ) (ι : Vf → (O → ℝ) →ₗ[ℝ] E)
    (hbound : ∀ x : Vf → E, |∑ v, ∑ w, inner ℝ (x w) (T w v (x v))| ≤ ∑ v, d v * ‖x v‖ ^ 2)
    (hL : ∀ f, ip m f (Lop f) = ∑ v, ∑ w, inner ℝ (ι w f) (T w v (ι v f)))
    (hD : ∀ f, ip m f (Dop f) = ∑ v, d v * ‖ι v f‖ ^ 2)
    (hLs : ∀ f g, ip m f (Lop g) = ip m g (Lop f)) (hDs : ∀ f g, ip m f (Dop g) = ip m g (Dop f)) :
    OpLE m Lop Dop ∧ OpLE m (-Lop) Dop := by
  have hb := fun f => abs_le.mp (hbound fun v => ι v f)
  refine ⟨⟨fun f g => ?_, fun f => ?_⟩, ⟨fun f g => ?_, fun f => ?_⟩⟩
  · simp only [LinearMap.sub_apply, ip_sub_right, hLs f g, hDs f g]
  · simp only [LinearMap.sub_apply, ip_sub_right, hL, hD]
    linarith [(hb f).2]
  · simp only [sub_neg_eq_add, LinearMap.add_apply, ip_add_right, hLs f g, hDs f g]
  · simp only [sub_neg_eq_add, LinearMap.add_apply, ip_add_right, hL, hD]
    linarith [(hb f).1]

end MaskSchurBridge

end Sarkozy.EnvelopeSteps

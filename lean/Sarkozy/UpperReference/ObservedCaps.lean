module

public import Sarkozy.Labellings.TwoLayer
public import Sarkozy.Cuts.Envelope
public import Sarkozy.Certificates.Majorant
public import Sarkozy.UpperReference.BlockCaps

/-!
# `prop:observed-caps`: observed merge and constant caps of EL22

`paper/sections/25_upper_reference.tex`, `prop:observed-caps`. A merge component of the upper
reference reads only the labels of the rows `0, 1` of its `E` coordinate, a constant component
only those of row `0`; at the layer cut `ι` only the compression `Op^O = Π_O Op Π_O` of the cut
operator of EL22 to functions of these *observed* labels matters.

**Geometry** (`Observed.crossD`, from the paper's graph `G_{EL,2}`, `Labellings.twoLayerEdge`):
* `crossD_eq`: the signed cross incidence of the layer cut is
  `D_{(a,b),(a',b')} = 1_{a≠a'}(1_{b'=rot b} - 1_{b=rot b'})`;
* `crossD_antisymm`, `crossD_degree`: `D` is antisymmetric and every cross degree is four;
  `internal_degree`: every internal degree is four;
* `supports_card`: there are `162` distinct supports of size at least two in the cross
  neighbourhoods; `merge_visible_card`, `const_visible_card`: `60` of them lie in the merge's
  observed labels and `6` in the constant's, so the merge has `12 + 60 = 72` visible and `108`
  hidden features, the constant `6 + 6 = 12` and `168`;
* `merge_singleton_gram`: on the merge's twelve singleton rows `B_⋆ B_⋆ᵀ = I` (the visible
  supports); `const_principal_D_zero`, `const_principal_B_zero`: the constant's principal star
  matrix is zero (no cross pair inside row `0`, and every visible support has a zero
  coefficient on the row `0`).

**The compression bound** (the proof's "Visible and hidden features" and "Lower bound"):
* `star_compression_bound`: with the synthesis split into a visible part (frame bound `Γ`) and
  a hidden part (`‖Π_O 𝓕_h‖ ≤ e_hid`), the visible principal block of `M` of norm `≤ k` and the
  three other blocks of norm `≤ k_M` (`= 6`), the compressed centred star form is at most
  `r{Γk + k_M(2√Γ e_hid + e_hid²)}`;
* `observed_lower`: **`Op^O ⪰ -(c + ε_ϱ²/(1+c)) I ⪰ -(c + ε_ϱ²) I`** on the functions of `x_O`,
  `c = R_Z[r{Γk + 6(2√Γ e_hid + e_hid²)} + N_ns + D_col]`, by `prop:matching:positive`(a′)
  (`Cuts.block_lower_scalar`), and `Op^O ⪯ 1 + B_top/p` from the full cut;
* `observed_numbers`: every bound after division by its power of `r` is admissible, so
  `(c + ε_ϱ²)/r` at `p ≥ p₀` is at most its value at `p₀` (the stated `g_G`, `g_C`);
* `observed_block`: the block caps `k_G = g_G exp(B_top L'/(X log X))`, `k_C` likewise
  (`matrix_block_cap`, for the compressions written in orthonormal bases).

**Hypotheses.** The decomposition of the doubly centred cut kernel into `r𝓕M(Φ̂)𝓕*`
(`cor:star-matrix`) and the nonstar and coincidence parts, the frame bound
(`lem:general-star`(f)), the hidden-feature bound (`lem:hidden-feature`), the nonstar,
coincidence, normalizer and constant-coupling bounds of the full cut (F6), and the norm bounds
`‖M(±i)‖ ≤ 6`, `‖M_vv(±i)‖ ≤ 2.188902` of the blocks enter as hypotheses on the forms. The two
Schur tests and the norm bounds of the explicit matrices are proved in `ObservedSchur.lean`,
`ObservedSchurTest.lean`, `ObservedGates.lean` and `ObservedNorm.lean`. The paper prints `g_G`, `g_C`
and `B_top` at `2⁴⁷`, `2⁴⁸`, but not the per-cut values they are computed from (`Γ`, `e_hid`,
`N_ns`, `D_col`, `R_Z`, `ε_ϱ` at `p₀`); that last numerical step is not checked here.
-/

@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.UpperReference.Observed

open Sarkozy Sarkozy.Labellings Sarkozy.Majorant

/-! ## Geometry of the layer cut of `G_{EL,2}` -/

/-- The labels `(a, b)`, `a ∈ O_E = {0, 1, 2}`, `b ∈ ℤ/6ℤ`, of a layer of `G_{EL,2}`. -/
abbrev Half := Fin 3 × ZMod 6

/-- The edge relation of `G_{EL,2}` between the slot `(u, ℓ)` and `(v, ℓ')`. -/
def edgeEL (u : Half) (ℓ : Fin 2) (v : Half) (ℓ' : Fin 2) : Bool :=
  twoLayerEdge typeE typeL ((u.1, u.2, ℓ) : Fin 3 × ZMod 6 × Fin 2) (v.1, v.2, ℓ')

/-- **The signed cross incidence of the layer cut `ι`** (plus half the layer `0`, minus half the
layer `1`, `ι` the layer swap): `+1` for an edge from `(u, 0)` to `(v, 1)`, `-1` for an edge from
`(v, 1)` to `(u, 0)`. -/
def crossD (u v : Half) : ℤ :=
  (if edgeEL u 0 v 1 then 1 else 0) - (if edgeEL v 1 u 0 then 1 else 0)

/-- **The cross incidence in closed form** (`prop:observed-caps`, proof): the edges are
`(a, b, ℓ) → (a', rot b, ℓ')` for `a ≠ a'`, so
`D_{(a,b),(a',b')} = 1_{a≠a'}(1_{b'=rot b} - 1_{b=rot b'})`. -/
theorem crossD_eq : ∀ u v : Half, crossD u v =
    if u.1 ≠ v.1 then (if v.2 = rot u.2 then 1 else 0) - (if u.2 = rot v.2 then 1 else 0)
    else 0 := by
  decide +kernel

/-- `D` is antisymmetric. -/
theorem crossD_antisymm : ∀ u v : Half, crossD v u = -crossD u v := by
  decide +kernel

/-- The cross neighbourhood of a label. -/
def nbr (u : Half) : Finset Half := univ.filter fun v => crossD u v ≠ 0

/-- Every cross degree is four. -/
theorem crossD_degree : ∀ u : Half, (nbr u).card = 4 := by
  decide +kernel

/-- Every internal degree (in the layer `0`, both orientations) is four. -/
theorem internal_degree : ∀ u : Half,
    (univ.filter fun v : Half => edgeEL u 0 v 0 = true ∨ edgeEL v 0 u 0 = true).card = 4 := by
  decide +kernel

/-- The entries of `D` are `0` or `±1`. -/
theorem crossD_range : ∀ u v : Half, crossD u v = 0 ∨ crossD u v = 1 ∨ crossD u v = -1 := by
  decide +kernel

/-- The supports of size at least two in the cross neighbourhoods. -/
def supports : Finset (Finset Half) :=
  univ.biUnion fun u => (nbr u).powerset.filter fun S => 2 ≤ S.card

/-- **There are `162` distinct supports of size at least two in the cross neighbourhoods.** -/
theorem supports_card : supports.card = 162 := by
  decide +kernel

/-- The merge's observed labels: the twelve labels of the rows `0, 1` of the `E` coordinate. -/
def mergeObs : Finset Half := univ.filter fun u => u.1 ≠ 2

/-- The constant's observed labels: the six labels of the row `0`. -/
def constObs : Finset Half := univ.filter fun u => u.1 = 0

theorem mergeObs_card : mergeObs.card = 12 := by
  decide +kernel

theorem constObs_card : constObs.card = 6 := by
  decide +kernel

/-- **`60` supports are visible to the merge** (contained in its observed labels), so the merge
has `12 + 60 = 72` visible and `18 + 162 - 72 = 108` hidden features. -/
theorem merge_visible_card : (supports.filter fun S => S ⊆ mergeObs).card = 60 := by
  decide +kernel

/-- **`6` supports are visible to the constant**, so it has `6 + 6 = 12` visible and `168`
hidden features. -/
theorem const_visible_card : (supports.filter fun S => S ⊆ constObs).card = 6 := by
  decide +kernel

/-- The star coefficients `(B_⋆)_{j,S} = (-1)^{|S|} ∏_{i∈S} D_{ji}`. -/
def starB (j : Half) (S : Finset Half) : ℤ := (-1) ^ S.card * ∏ i ∈ S, crossD j i

/-- **On the merge's singleton rows `B_⋆ B_⋆ᵀ = I`** (restricted to the visible supports). -/
theorem merge_singleton_gram : ∀ j ∈ mergeObs, ∀ j' ∈ mergeObs,
    ∑ S ∈ supports.filter (fun S => S ⊆ mergeObs), starB j S * starB j' S =
      if j = j' then 1 else 0 := by
  decide +kernel

/-- **The constant's principal star matrix is zero**, first half: `D` vanishes on the row `0`
(no cross pair inside one row of the `E` coordinate). -/
theorem const_principal_D_zero : ∀ j ∈ constObs, ∀ j' ∈ constObs, crossD j j' = 0 := by
  decide +kernel

/-- **The constant's principal star matrix is zero**, second half: every support visible to the
constant has a zero coefficient on the row `0`. -/
theorem const_principal_B_zero :
    ∀ j ∈ constObs, ∀ S ∈ supports.filter (fun S => S ⊆ constObs), starB j S = 0 := by
  intro j hj S hS
  rw [Finset.mem_filter] at hS
  have h2 : 2 ≤ S.card := by
    have h := hS.1
    unfold supports at h
    rw [Finset.mem_biUnion] at h
    obtain ⟨u, -, hu⟩ := h
    rw [Finset.mem_filter] at hu
    exact hu.2
  obtain ⟨i, hi⟩ := Finset.card_pos.mp (show 0 < S.card by omega)
  unfold starB
  rw [Finset.prod_eq_zero hi (const_principal_D_zero j hj i (hS.2 hi)), mul_zero]

/-! ## The compression bound -/

section Compression

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {Ev Eh : Type*} [NormedAddCommGroup Ev] [InnerProductSpace ℝ Ev]
  [NormedAddCommGroup Eh] [InnerProductSpace ℝ Eh]

/-- **`prop:observed-caps`, the compressed star part** ("Visible and hidden features"). Write
the centred star form through the synthesis, `⟨f, 𝒮 f⟩ = r ⟨𝓕*f, M 𝓕*f⟩`, with `𝓕* f` split
into its visible part `F_v f` and hidden part `F_h f`, and `M` into its visible principal block
`M_vv` (norm `≤ k`, the Schur test of the principal matrix) and the blocks `M_vh` and `M_hh`
(norm `≤ k_M`, the Schur test `‖M‖ ≤ 6` of the full matrix). If `‖F_v f‖² ≤ Γ ‖f‖²`
(`lem:general-star`(f)) and, for `f` a function of `x_O`, `‖F_h f‖ ≤ e ‖f‖` (`F_h f = F_h Π_O f`
and `‖Π_O 𝓕_h‖ ≤ e_hid`, `lem:hidden-feature` with Cauchy–Schwarz), then
`|⟨f, 𝒮 f⟩| ≤ r(Γk + k_M(2√Γ e + e²)) ‖f‖²`. -/
theorem star_compression_bound (S : H →ₗ[ℝ] H) (Fv : H →ₗ[ℝ] Ev) (Fh : H →ₗ[ℝ] Eh)
    (Mvv : Ev →ₗ[ℝ] Ev) (Mvh : Eh →ₗ[ℝ] Ev) (Mhh : Eh →ₗ[ℝ] Eh) {r k kM Γ e : ℝ}
    (hr : 0 ≤ r) (hk : 0 ≤ k) (hkM : 0 ≤ kM) (hΓ : 0 ≤ Γ)
    (hS : ∀ f, ⟪f, S f⟫_ℝ = r * (⟪Fv f, Mvv (Fv f)⟫_ℝ + 2 * ⟪Fv f, Mvh (Fh f)⟫_ℝ +
      ⟪Fh f, Mhh (Fh f)⟫_ℝ))
    (hMvv : ∀ x, ‖Mvv x‖ ≤ k * ‖x‖) (hMvh : ∀ x, ‖Mvh x‖ ≤ kM * ‖x‖)
    (hMhh : ∀ x, ‖Mhh x‖ ≤ kM * ‖x‖) (hFv : ∀ f, ‖Fv f‖ ^ 2 ≤ Γ * ‖f‖ ^ 2) (f : H)
    (hFh : ‖Fh f‖ ≤ e * ‖f‖) :
    |⟪f, S f⟫_ℝ| ≤ r * (Γ * k + kM * (2 * √Γ * e + e ^ 2)) * ‖f‖ ^ 2 := by
  set a := ‖Fv f‖
  set b := ‖Fh f‖
  have ha0 : 0 ≤ a := norm_nonneg _
  have hb0 : 0 ≤ b := norm_nonneg _
  have hf0 : 0 ≤ ‖f‖ := norm_nonneg _
  have ha : a ≤ √Γ * ‖f‖ := by
    have h := Real.sqrt_le_sqrt (hFv f)
    rwa [Real.sqrt_sq ha0, Real.sqrt_mul hΓ, Real.sqrt_sq hf0] at h
  have h1 : |⟪Fv f, Mvv (Fv f)⟫_ℝ| ≤ k * a ^ 2 := by
    calc |⟪Fv f, Mvv (Fv f)⟫_ℝ| ≤ a * ‖Mvv (Fv f)‖ := abs_real_inner_le_norm _ _
      _ ≤ a * (k * a) := mul_le_mul_of_nonneg_left (hMvv _) ha0
      _ = k * a ^ 2 := by ring
  have h2 : |⟪Fv f, Mvh (Fh f)⟫_ℝ| ≤ kM * a * b := by
    calc |⟪Fv f, Mvh (Fh f)⟫_ℝ| ≤ a * ‖Mvh (Fh f)‖ := abs_real_inner_le_norm _ _
      _ ≤ a * (kM * b) := mul_le_mul_of_nonneg_left (hMvh _) ha0
      _ = kM * a * b := by ring
  have h3 : |⟪Fh f, Mhh (Fh f)⟫_ℝ| ≤ kM * b ^ 2 := by
    calc |⟪Fh f, Mhh (Fh f)⟫_ℝ| ≤ b * ‖Mhh (Fh f)‖ := abs_real_inner_le_norm _ _
      _ ≤ b * (kM * b) := mul_le_mul_of_nonneg_left (hMhh _) hb0
      _ = kM * b ^ 2 := by ring
  have hsum : |⟪Fv f, Mvv (Fv f)⟫_ℝ + 2 * ⟪Fv f, Mvh (Fh f)⟫_ℝ + ⟪Fh f, Mhh (Fh f)⟫_ℝ| ≤
      k * a ^ 2 + 2 * (kM * a * b) + kM * b ^ 2 := by
    calc _ ≤ |⟪Fv f, Mvv (Fv f)⟫_ℝ| + |2 * ⟪Fv f, Mvh (Fh f)⟫_ℝ| + |⟪Fh f, Mhh (Fh f)⟫_ℝ| :=
          abs_add_three _ _ _
      _ ≤ k * a ^ 2 + 2 * (kM * a * b) + kM * b ^ 2 := by
          rw [abs_mul, abs_two]
          linarith
  have hbound : k * a ^ 2 + 2 * (kM * a * b) + kM * b ^ 2 ≤
      (Γ * k + kM * (2 * √Γ * e + e ^ 2)) * ‖f‖ ^ 2 := by
    have hsq : a ^ 2 ≤ Γ * ‖f‖ ^ 2 := hFv f
    have hab : a * b ≤ √Γ * ‖f‖ * (e * ‖f‖) := mul_le_mul ha hFh hb0 (by positivity)
    have hbb : b ^ 2 ≤ (e * ‖f‖) ^ 2 := pow_le_pow_left₀ hb0 hFh 2
    have t1 : k * a ^ 2 ≤ k * (Γ * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left hsq hk
    have t2 : kM * (a * b) ≤ kM * (√Γ * ‖f‖ * (e * ‖f‖)) := mul_le_mul_of_nonneg_left hab hkM
    have t3 : kM * b ^ 2 ≤ kM * (e * ‖f‖) ^ 2 := mul_le_mul_of_nonneg_left hbb hkM
    have e1 : (Γ * k + kM * (2 * √Γ * e + e ^ 2)) * ‖f‖ ^ 2 = k * (Γ * ‖f‖ ^ 2) +
        2 * (kM * (√Γ * ‖f‖ * (e * ‖f‖))) + kM * (e * ‖f‖) ^ 2 := by ring
    rw [e1]
    have e2 : 2 * (kM * a * b) = 2 * (kM * (a * b)) := by ring
    linarith
  rw [hS, abs_mul, abs_of_nonneg hr, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hsum.trans hbound) hr

/-- **`prop:observed-caps`, the lower and upper bounds of the compression.** Let `Op` be the
normalized cut operator of EL22 (symmetric, `⟨1, Op 1⟩ = 1`), `W` the functions of the observed
labels `x_O` (containing `1`), and let the doubly centred kernel split as
`⟨h, Op h⟩ = Z₀⁻¹(⟨h, 𝒮 h⟩ + ⟨h, T_ns h⟩ - ⟨h, T_coll h⟩)` for `h ⊥ 1` (`cor:star-matrix`),
with `Z₀ ≥ 1 - ε_Z > 0`, `‖T_ns‖ ≤ N_ns`, `‖T_coll‖ ≤ D_col`, the compressed star bound
`|⟨h, 𝒮 h⟩| ≤ r s ‖h‖²` on `W ∩ 1^⊥` (`star_compression_bound`, `s = Γk + 6(2√Γ e + e²)`), and
`‖Op 1 - 1‖ ≤ ε_ϱ`. Then on `W`, with `c = R_Z(r s + N_ns + D_col)`,
`Op^O ⪰ -(c + ε_ϱ²/(1 + c)) ⪰ -(c + ε_ϱ²)`; and `Op ⪯ 1 + B/p` gives `Op^O ⪯ 1 + B/p`. -/
theorem observed_lower (Op S Tns Tcoll : H →ₗ[ℝ] H) (one : H) (W : Submodule ℝ H)
    (hone : ‖one‖ = 1) (honeW : one ∈ W) (hsym : Op.IsSymmetric) (hmean : ⟪one, Op one⟫_ℝ = 1)
    {Z₀ εZ Nns Dcol ερ r s : ℝ} (hZ : 1 - εZ ≤ Z₀) (hεZ : εZ < 1) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hdec : ∀ h, ⟪one, h⟫_ℝ = 0 →
      ⟪h, Op h⟫_ℝ = Z₀⁻¹ * (⟪h, S h⟫_ℝ + ⟪h, Tns h⟫_ℝ - ⟪h, Tcoll h⟫_ℝ))
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    (hstar : ∀ h ∈ W, ⟪one, h⟫_ℝ = 0 → |⟪h, S h⟫_ℝ| ≤ r * s * ‖h‖ ^ 2)
    (hρ : ‖Op one - one‖ ≤ ερ) :
    ∀ f ∈ W, -((1 / (1 - εZ) * (r * s + Nns + Dcol)) +
        ερ ^ 2 / (1 + 1 / (1 - εZ) * (r * s + Nns + Dcol))) * ‖f‖ ^ 2 ≤ ⟪f, Op f⟫_ℝ ∧
      -((1 / (1 - εZ) * (r * s + Nns + Dcol)) + ερ ^ 2) * ‖f‖ ^ 2 ≤ ⟪f, Op f⟫_ℝ := by
  intro f hf
  have hden : 0 < 1 - εZ := by linarith
  have hZpos : 0 < Z₀ := lt_of_lt_of_le hden hZ
  have hNns : 0 ≤ Nns := by
    have := hns one
    rw [hone, mul_one] at this
    exact (norm_nonneg _).trans this
  have hDcol : 0 ≤ Dcol := by
    have := hcoll one
    rw [hone, mul_one] at this
    exact (norm_nonneg _).trans this
  set c := 1 / (1 - εZ) * (r * s + Nns + Dcol) with hc
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (by positivity)
  -- `f = α 1 + h`, `h ⊥ 1`, `h ∈ W`
  set α := ⟪one, f⟫_ℝ with hα
  set h := f - α • one with hh
  have hone1 : ⟪one, one⟫_ℝ = 1 := by rw [real_inner_self_eq_norm_sq, hone]; norm_num
  have hh1 : ⟪one, h⟫_ℝ = 0 := by
    rw [hh, inner_sub_right, real_inner_smul_right, hone1, mul_one, hα, sub_self]
  have hhW : h ∈ W := W.sub_mem hf (W.smul_mem α honeW)
  have hfe : f = α • one + h := by rw [hh]; abel
  -- the centred form
  have hcent : -c * ‖h‖ ^ 2 ≤ ⟪h, Op h⟫_ℝ := by
    rw [hdec h hh1]
    have h1 := hstar h hhW hh1
    have h2 : |⟪h, Tns h⟫_ℝ| ≤ Nns * ‖h‖ ^ 2 := by
      calc |⟪h, Tns h⟫_ℝ| ≤ ‖h‖ * ‖Tns h‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖h‖ * (Nns * ‖h‖) := mul_le_mul_of_nonneg_left (hns h) (norm_nonneg _)
        _ = Nns * ‖h‖ ^ 2 := by ring
    have h3 : |⟪h, Tcoll h⟫_ℝ| ≤ Dcol * ‖h‖ ^ 2 := by
      calc |⟪h, Tcoll h⟫_ℝ| ≤ ‖h‖ * ‖Tcoll h‖ := abs_real_inner_le_norm _ _
        _ ≤ ‖h‖ * (Dcol * ‖h‖) := mul_le_mul_of_nonneg_left (hcoll h) (norm_nonneg _)
        _ = Dcol * ‖h‖ ^ 2 := by ring
    have hlow : -((r * s + Nns + Dcol) * ‖h‖ ^ 2) ≤
        ⟪h, S h⟫_ℝ + ⟪h, Tns h⟫_ℝ - ⟪h, Tcoll h⟫_ℝ := by
      have := neg_abs_le ⟪h, S h⟫_ℝ
      have := neg_abs_le ⟪h, Tns h⟫_ℝ
      have := le_abs_self ⟪h, Tcoll h⟫_ℝ
      nlinarith
    have hq0 : 0 ≤ (r * s + Nns + Dcol) * ‖h‖ ^ 2 := by positivity
    have hZinv : Z₀⁻¹ ≤ 1 / (1 - εZ) := by
      rw [one_div]
      exact inv_anti₀ hden hZ
    have : -(Z₀⁻¹ * ((r * s + Nns + Dcol) * ‖h‖ ^ 2)) ≤
        Z₀⁻¹ * (⟪h, S h⟫_ℝ + ⟪h, Tns h⟫_ℝ - ⟪h, Tcoll h⟫_ℝ) := by
      have := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hZpos.le)
      linarith
    have hcmp : Z₀⁻¹ * ((r * s + Nns + Dcol) * ‖h‖ ^ 2) ≤ c * ‖h‖ ^ 2 := by
      rw [hc, mul_assoc]
      exact mul_le_mul_of_nonneg_right hZinv hq0
    linarith
  -- the coupling `⟨h, Op 1⟩ = ⟨h, Op 1 - 1⟩`
  have hcoup : |⟪h, Op one⟫_ℝ| ≤ ερ * ‖h‖ := by
    have e1 : ⟪h, Op one⟫_ℝ = ⟪h, Op one - one⟫_ℝ := by
      rw [inner_sub_right, real_inner_comm one h, hh1, sub_zero]
    rw [e1]
    calc |⟪h, Op one - one⟫_ℝ| ≤ ‖h‖ * ‖Op one - one‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖h‖ * ερ := mul_le_mul_of_nonneg_left hρ (norm_nonneg _)
      _ = ερ * ‖h‖ := by ring
  -- the expansions of the form and of the norm
  have hform : ⟪f, Op f⟫_ℝ = α ^ 2 + 2 * (α * ⟪h, Op one⟫_ℝ) + ⟪h, Op h⟫_ℝ := by
    have hsy : ⟪one, Op h⟫_ℝ = ⟪h, Op one⟫_ℝ := by
      rw [← hsym one h, real_inner_comm]
    rw [hfe, map_add, map_smul, inner_add_left, inner_add_right, inner_add_right,
      real_inner_smul_left, real_inner_smul_left, real_inner_smul_right, real_inner_smul_right,
      hmean, hsy]
    ring
  have hnorm : ‖f‖ ^ 2 = |α| ^ 2 + ‖h‖ ^ 2 := by
    rw [hfe, sq_abs, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_add_left,
      inner_add_right, inner_add_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, hone1, real_inner_comm one h, hh1]
    ring
  have hcα : |α * ⟪h, Op one⟫_ℝ| ≤ ερ * |α| * ‖h‖ := by
    rw [abs_mul]
    calc |α| * |⟪h, Op one⟫_ℝ| ≤ |α| * (ερ * ‖h‖) :=
          mul_le_mul_of_nonneg_left hcoup (abs_nonneg _)
      _ = ερ * |α| * ‖h‖ := by ring
  have key := Sarkozy.Cuts.block_lower_scalar (a := 1) (d := -c) (b := ερ) (X := |α|)
    (Y := ‖h‖) (qA := α ^ 2) (qD := ⟪h, Op h⟫_ℝ) (c := α * ⟪h, Op one⟫_ℝ) (by linarith)
    (by rw [sq_abs, one_mul]) hcent hcα
  have e1 : -c - ερ ^ 2 / (1 - -c) = -(c + ερ ^ 2 / (1 + c)) := by
    rw [show (1 : ℝ) - -c = 1 + c by ring]
    ring
  rw [e1, ← hnorm, ← hform] at key
  refine ⟨key, le_trans ?_ key⟩
  have h1 : ερ ^ 2 / (1 + c) ≤ ερ ^ 2 := div_le_self (sq_nonneg _) (by linarith)
  exact mul_le_mul_of_nonneg_right (by linarith) (sq_nonneg _)

/-- **`prop:observed-caps`, the upper bound**: the compression of the positive envelope
`Op ⪯ (1 + B_top/p) I` of the full cut (`thm:spectral-criterion`(d)) to the functions of `x_O`. -/
theorem observed_upper (Op : H →ₗ[ℝ] H) (W : Submodule ℝ H) {Bp : ℝ}
    (hup : ∀ v, ⟪v, Op v⟫_ℝ ≤ (1 + Bp) * ‖v‖ ^ 2) : ∀ f ∈ W, ⟪f, Op f⟫_ℝ ≤ (1 + Bp) * ‖f‖ ^ 2 :=
  fun f _ => hup f

end Compression

/-! ## All primes and blocks -/

/-- **`prop:observed-caps`, all primes** ("every error bound above, after division by its
indicated power of `r`, is admissible"): if `Γ`, `e_hid`, `N_ns/r`, `D_col/r`, `ε_Z` (with
`ε_Z < 1` at the endpoint) and `ε_ϱ²/r` are admissible on the box, then so is
`(c + ε_ϱ²)/r = R_Z(Γk + k_M(2√Γ e_hid + e_hid²) + N_ns/r + D_col/r) + ε_ϱ²/r`; so at every point it
is at most its endpoint value (`g_G` or `g_C`). -/
theorem observed_numbers {Δ : Type*} [Preorder Δ] (Γ e nN nD εZ eρ2 : Δ → ℝ) {k kM : ℝ}
    (hk : 0 ≤ k) (hkM : 0 ≤ kM) (hΓ : Admissible Γ) (he : Admissible e) (hN : Admissible nN)
    (hD : Admissible nD) (hZ : Admissible εZ) (hρ : Admissible eρ2) (xp : Δ)
    (hxp : ∀ x, x ≤ xp) (hZ1 : εZ xp < 1) :
    Admissible (fun x => 1 / (1 - εZ x) *
      (Γ x * k + kM * (2 * √(Γ x) * e x + e x ^ 2) + nN x + nD x) + eρ2 x) := by
  have hlt : ∀ x, εZ x < 1 := fun x => lt_of_le_of_lt (endpoint_le hZ (hxp x)) hZ1
  have hRZ : Admissible (fun x => 1 / (1 - εZ x)) := admissible_one_div_one_sub hZ hlt
  have hin : Admissible (fun x => Γ x * k + kM * (2 * √(Γ x) * e x + e x ^ 2) + nN x + nD x) := by
    refine ⟨fun x y hxy => ?_, fun x => ?_⟩
    · have g1 := hΓ.1 hxy
      have e0 := he.2 x
      have e1 := he.1 hxy
      have s1 : √(Γ x) ≤ √(Γ y) := Real.sqrt_le_sqrt g1
      have t1 : Γ x * k ≤ Γ y * k := mul_le_mul_of_nonneg_right g1 hk
      have t2 : 2 * √(Γ x) * e x ≤ 2 * √(Γ y) * e y :=
        mul_le_mul (mul_le_mul_of_nonneg_left s1 (by norm_num)) e1 e0 (by positivity)
      have t3 : e x ^ 2 ≤ e y ^ 2 := pow_le_pow_left₀ e0 e1 2
      have t4 : kM * (2 * √(Γ x) * e x + e x ^ 2) ≤ kM * (2 * √(Γ y) * e y + e y ^ 2) :=
        mul_le_mul_of_nonneg_left (by linarith) hkM
      linarith [hN.1 hxy, hD.1 hxy]
    · have := hΓ.2 x
      have := he.2 x
      have := hN.2 x
      have := hD.2 x
      positivity
  exact admissible_add (admissible_mul hRZ hin) hρ

/-- **`prop:observed-caps`, the block caps**: if the compressions `A_j` (to the functions of the
observed labels, written in orthonormal bases) satisfy `-g p_j^{-1/2} ⪯ A_j ⪯ 1 + B/p_j` at the
primes `p_j ≥ b ≥ X > 1` of a block with `∑ log p_j ≤ L'`, then the compressed block operator is
at least `-k b^{-1/2}`, `k = g exp(B L'/(X log X))` (`lem:spec:tensorcomp`(b),(c)). With
`g = g_G` (`g_C`) this is the cap `k_G` (`k_C`) of the reserved states LR, RL (LC, CL). -/
theorem observed_block {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*}
    [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hA : ∀ j, (A j).transpose = A j) (p : K → ℝ)
    {g B L X b : ℝ} (hg0 : 0 ≤ g) (hB0 : 0 ≤ B) (hX : 1 < X) (hXb : X ≤ b)
    (hpb : ∀ j, b ≤ p j) (hL : ∑ j, Real.log (p j) ≤ L) (hgr : ∀ j, g / √(p j) ≤ 1)
    (hlow : ∀ j x, -(g / √(p j)) * (x ⬝ᵥ x) ≤ x ⬝ᵥ ((A j).mulVec x))
    (hup : ∀ j x, x ⬝ᵥ ((A j).mulVec x) ≤ (1 + B / p j) * (x ⬝ᵥ x)) (x : (∀ j, Ω j) → ℝ) :
    -(g * Real.exp (B * L / (X * Real.log X)) / √b) * (x ⬝ᵥ x) ≤
      x ⬝ᵥ ((Sarkozy.IndexSupport.piKron A).mulVec x) :=
  matrix_block_cap A hA p hg0 hB0 hX hXb hpb hL hgr hlow hup x

end Sarkozy.UpperReference.Observed

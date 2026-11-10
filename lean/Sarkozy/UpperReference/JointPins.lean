module

public import Sarkozy.JointRows.PotentialPaley
public import Sarkozy.Labellings.TwoLayer
public import Sarkozy.Labellings.GraphAutomorphism
public import Sarkozy.TraceMixing.Paley
public import Mathlib.Analysis.Matrix.Order

/-!
# `lem:joint-pins`: pin classes of the `L` rows

`paper/sections/25_upper_reference.tex`, `lem:joint-pins` (subsection `subsec:upper-joint-rows`),
with `𝒵` as in `lem:joint-rows` (`paper/sections/16_extraction.tex`) and the consequence through
`lem:joint-potential`. **All of (a), (b) and the consequence are proved**; the consequence keeps
the analytic hypotheses of `lem:joint-potential` (in its formal version) as hypotheses.

The conditional `L` rows: a chamber coordinate of field type `F` (the fold law) or `E` (the
matching law), whose other coordinate has type `L`, with `ℓ ∈ {1, 2}` layers. The labels of a
row are indexed by the six base coordinates `u ∈ ℤ/6ℤ` and, for `ℓ = 2`, their twins.

**The geometry, from the graphs.** Everything is read off V1's two-layer graphs
(`Sarkozy.Labellings.twoLayerEdge`, `typeF`, `typeE`, `typeL`), by `decide`:
* `signedCross_typeF`, `signedCross_typeE`: the signed singleton matrices between the outer rows
  `0` and `2` (`+1` for an edge from row `0` to row `2`, `-1` for the reverse) are the displayed
  `D_F` and `D_E`; `signedCross_layers`: with `ℓ` layers they are `D ⊗ J_ℓ` (edges carry no
  layer condition, `twoLayerEdge_layer`);
* `pin_out_edge`, `pin_in_edge`: the outer label of base coordinate `u` (row `0` or `2`) is joined
  to the middle row exactly by the edges `u → m_{rot u}` and `m_{rot⁻¹ u} → u`, in every layer,
  for both laws (the table of the proof).

**(a)** `𝒵₀ = [[D_E, D_F], [-D_Fᵀ, D_E]]` (`Z0`) is antisymmetric (`jointZ_transpose`) with
`(𝒵₀² + I)(𝒵₀² + 9I) = 0` (`Z0_minpoly`, by `decide`). For every real antisymmetric `Z` with this
identity, `T = (-Z² + 3I)/4` (`absMat`) is positive semidefinite, `T² = ZᵀZ`, and `T ± iZ ⪰ 0`
(`absMat_posSemidef`, `absMat_sq`, `absMat_sub_I_posSemidef`, `absMat_add_I_posSemidef`). The
proof is a sum of squares: with `Y = iZ` (Hermitian, `(Y² - 1)(Y² - 9) = 0`),
`Q₁ = (Y - 1)(Y - 3)` and `Q₂ = Q₁(Y + 3)`, `48 Q₁ - 2Q₁² - Q₂² = (Y² - 1)(Y² - 9)(-Y² + 2Y + 5)`
(`sos_identity`), so `T - iZ = Q₁/4 = Q₁ᴴQ₁/96 + Q₂ᴴQ₂/192`. For `𝒵₀` this is `absZ0_spec`.
For `ℓ = 2`, `𝒵 = 𝒵₀ ⊗ J₂ = E 𝒵₀ Eᵀ` for the twin embedding `E` (`jointZr_eq_twin`), and
`T₀ ⊗ J₂ + s𝒵 = E (T₀ + s𝒵₀) Eᵀ ⪰ 0` whenever `T₀ + s𝒵₀ ⪰ 0` (`twin_posSemidef`, the paper's
"for `ℓ = 2` it suffices that `T = T₀ ⊗ J₂` with `T₀ ± i𝒵₀ ⪰ 0`"); with `T₀ = |𝒵₀|`,
`absZ2 = |𝒵₀| ⊗ J₂ = (-𝒵² + 12Π)/8` is positive semidefinite with square `𝒵ᵀ𝒵` (`absZ2_spec`)
and `absZ2 ± i𝒵 ⪰ 0` (`absZ2_sub_I`). `cfc_abs_eq` identifies both with Mathlib's absolute value
`CFC.abs` (positive square root of `𝒵ᵀ𝒵`).

**(b)** `pinAdm_iff_edges`: `PinAdm m u t` is exactly the strict-square condition of the edges
between an outer label of base coordinate `u` with value `t` and the middle labels `m`.
`pinAdm_eq_of_parity`, `pin_classes`: at `|F| ≡ 3 (mod 4)`, whatever `m`, a label `t` admissible
for two base coordinates of the same parity forces them to be equal, since two such coordinates
share a pin with opposite orientations and the strict-square relation is a tournament. So the
coordinates whose allowed set contains `t` lie in one of the nine classes `pinClass e o` (one even
and one odd base coordinate, with all twins, in both copies): `pinSel_mem`, `mem_pinSel`.

**Consequence** (`joint_pins`): `lem:joint-potential` in the form
`Sarkozy.JointRows.Restrict.joint_potential_paley`, with `𝒵` the paper's matrix, `𝒮` the nine
classes and the selector `pinSel` of (b). The hypotheses `hSel` and `hdS` there are discharged by
(b) and by the vanishing of `D(t) = diag(√ρ_i(t))` where `t` violates the pins of `i` (`hD0`).
`hN` is the hypothesis `T - i𝒵 ⪰ 0`, discharged for `T = |𝒵|` by (a) (`absMat_Z0_sub_I` for
`ℓ = 1`, `absZ2_sub_I` for `ℓ = 2`). The analytic inputs of `joint_potential_paley` (the
expansions of the kernels, their norms, the decomposition of the pure part) remain hypotheses,
exactly as there.

**Non-vacuity**: `pinAdm_m11`, `not_pinAdm_m11`, `pinSel_m11` (an explicit admissible label at
`p = 11`, the tournament step, and the selector), `pinClasses_card` (nine classes for `ℓ = 1, 2`),
`gate_absZ0_nonvacuous` (the gates are satisfiable with `T = |𝒵₀|`).

Not formalized: `hD0` from the definition of the allowed-set laws (their densities vanish off the
allowed sets by definition; the paper's allowed sets also exclude the middle and fixed labels,
which only shrinks them).
-/
@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix Finset

namespace Sarkozy.UpperReference

namespace JointPins

open Sarkozy.Labellings

/-! ## The signed singleton matrices and the pins, from the graphs -/

/-- **`D_F`** of `lem:joint-pins`, as displayed. -/
def DF : Matrix (ZMod 6) (ZMod 6) ℤ :=
  Matrix.of ![![0, 1, 1, 0, 0, 1], ![1, 0, 1, 0, 0, 1], ![0, 1, 0, 1, 1, 0],
    ![0, 1, 1, 0, 1, 0], ![1, 0, 0, 1, 0, 1], ![1, 0, 0, 1, 1, 0]]

/-- **`D_E`** of `lem:joint-pins`, as displayed. -/
def DE : Matrix (ZMod 6) (ZMod 6) ℤ :=
  Matrix.of ![![0, 0, 1, 0, -1, 0], ![0, 0, 0, -1, 0, 1], ![-1, 0, 0, 0, 1, 0],
    ![0, 1, 0, 0, 0, -1], ![1, 0, -1, 0, 0, 0], ![0, -1, 0, 1, 0, 0]]

/-- The signed singleton matrix between the outer rows `0` and `2` of a chamber coordinate of
field type `c` whose other coordinate has type `L`: `+1` for an edge `(0, u) → (2, v)`, `-1` for an
edge `(2, v) → (0, u)` (one layer; edges carry no layer condition, `twoLayerEdge_layer`). -/
def signedCross (c : FieldType (Fin 3)) : Matrix (ZMod 6) (ZMod 6) ℤ :=
  Matrix.of fun u v =>
    (if twoLayerEdge (Λ := Fin 1) c typeL ((0 : Fin 3), u, 0) (2, v, 0) then 1 else 0) -
      (if twoLayerEdge (Λ := Fin 1) c typeL ((2 : Fin 3), v, 0) (0, u, 0) then 1 else 0)

/-- **The fold rows** (`lem:joint-pins`, proof): the signed singleton matrix of `G_{FL}` is `D_F`.
-/
theorem signedCross_typeF : signedCross typeF = DF := by decide +kernel

/-- **The matching rows** (`lem:joint-pins`, proof): the signed singleton matrix of `G_{EL}` is
`D_E`. -/
theorem signedCross_typeE : signedCross typeE = DE := by decide +kernel

/-- Edges of the two-layer graphs carry no layer condition (`subsec:push:layer72spectral`). -/
theorem twoLayerEdge_layer {O₀ O₁ Λ Λ' : Type*} (c₀ : FieldType O₀) (c₁ : FieldType O₁)
    (a b : O₀ × O₁ × Λ) (l l' : Λ') :
    twoLayerEdge c₀ c₁ a b = twoLayerEdge c₀ c₁ (a.1, a.2.1, l) (b.1, b.2.1, l') := rfl

theorem pin_out_edge₁ {c : FieldType (Fin 3)} (hc : c = typeF ∨ c = typeE) :
    ∀ (a : Fin 3), a ≠ 1 → ∀ (u v : ZMod 6),
      (twoLayerEdge (Λ := Fin 1) c typeL (a, u, 0) (1, v, 0) = true ↔ v = rot u) := by
  rcases hc with rfl | rfl <;> decide +kernel

theorem pin_in_edge₁ {c : FieldType (Fin 3)} (hc : c = typeF ∨ c = typeE) :
    ∀ (a : Fin 3), a ≠ 1 → ∀ (u v : ZMod 6),
      (twoLayerEdge (Λ := Fin 1) c typeL (1, v, 0) (a, u, 0) = true ↔ v = rot (rot u)) := by
  rcases hc with rfl | rfl <;> decide +kernel

/-- **The factor `J_ℓ`** (`lem:joint-pins`): with `ℓ` layers the signed singleton matrix between
the labels `(0, u, l)` and `(2, v, l')` is `signedCross c u v` for all layers `l, l'`, i.e.
`D ⊗ J_ℓ`. -/
theorem signedCross_layers {Λ : Type*} (c : FieldType (Fin 3)) (u v : ZMod 6) (l l' : Λ) :
    (if twoLayerEdge c typeL ((0 : Fin 3), u, l) (2, v, l') then (1 : ℤ) else 0) -
      (if twoLayerEdge c typeL ((2 : Fin 3), v, l') (0, u, l) then 1 else 0) =
        signedCross c u v := rfl

/-- **Out-pins** (`lem:joint-pins`(b), proof): in `G_{FL}` and `G_{EL}`, the outer label of base
coordinate `u` (row `a ≠ 1`) has an edge to the middle label of base coordinate `v` iff
`v = rot u`, in every layer. -/
theorem pin_out_edge {Λ : Type*} {c : FieldType (Fin 3)} (hc : c = typeF ∨ c = typeE)
    (a : Fin 3) (ha : a ≠ 1) (u v : ZMod 6) (l l' : Λ) :
    twoLayerEdge c typeL (a, u, l) (1, v, l') = true ↔ v = rot u :=
  pin_out_edge₁ hc a ha u v

/-- **In-pins** (`lem:joint-pins`(b), proof): in `G_{FL}` and `G_{EL}`, the middle label of base
coordinate `v` has an edge to the outer label of base coordinate `u` iff `v = rot⁻¹ u =
rot (rot u)`, in every layer. -/
theorem pin_in_edge {Λ : Type*} {c : FieldType (Fin 3)} (hc : c = typeF ∨ c = typeE)
    (a : Fin 3) (ha : a ≠ 1) (u v : ZMod 6) (l l' : Λ) :
    twoLayerEdge c typeL (1, v, l') (a, u, l) = true ↔ v = rot (rot u) :=
  pin_in_edge₁ hc a ha u v

/-! ## (a): the matrix `𝒵` and `|𝒵|` -/

/-- The four blocks of `𝒵 = [[D_E, D_F], [-D_Fᵀ, D_E]]` (`lem:joint-rows`). -/
def zBase : Fin 2 → Fin 2 → Matrix (ZMod 6) (ZMod 6) ℤ :=
  ![![DE, DF], ![-DFᵀ, DE]]

/-- **`𝒵` for `ℓ` layers** (`lem:joint-rows`, `lem:joint-pins`), indexed by (copy, base
coordinate, twin): `𝒵₀ ⊗ J_ℓ`, `ℓ = |Λ|`. -/
def jointZ (Λ : Type*) : Matrix (Fin 2 × ZMod 6 × Λ) (Fin 2 × ZMod 6 × Λ) ℤ :=
  Matrix.of fun i j => zBase i.1 j.1 i.2.1 j.2.1

/-- `𝒵₀`, the matrix `𝒵` for `ℓ = 1` (`12 × 12`). -/
abbrev Z0 : Matrix (Fin 2 × ZMod 6 × Fin 1) (Fin 2 × ZMod 6 × Fin 1) ℤ := jointZ (Fin 1)

theorem zBase_antisymm :
    ∀ x : Fin 2 × Fin 2 × ZMod 6 × ZMod 6, zBase x.2.1 x.1 x.2.2.2 x.2.2.1 =
      -zBase x.1 x.2.1 x.2.2.1 x.2.2.2 := by
  decide +kernel

/-- `𝒵` is antisymmetric (`D_Eᵀ = -D_E`). -/
theorem jointZ_transpose (Λ : Type*) : (jointZ Λ)ᵀ = -jointZ Λ := by
  ext i j
  simp only [transpose_apply, jointZ, of_apply, neg_apply]
  exact zBase_antisymm (i.1, j.1, i.2.1, j.2.1)

/-- **`lem:joint-pins`(a), the identity of the proof**: `(𝒵₀² + I)(𝒵₀² + 9I) = 0`, by exact
integer arithmetic. -/
theorem Z0_minpoly : (Z0 * Z0 + 1) * (Z0 * Z0 + 9) = 0 := by decide +kernel

/-- The real matrix of an integer matrix. -/
abbrev toReal {m : Type*} (M : Matrix m m ℤ) : Matrix m m ℝ := M.map (Int.cast : ℤ → ℝ)

/-- `𝒵` as a real matrix. -/
abbrev jointZr (Λ : Type*) : Matrix (Fin 2 × ZMod 6 × Λ) (Fin 2 × ZMod 6 × Λ) ℝ :=
  toReal (jointZ Λ)

theorem jointZr_transpose (Λ : Type*) : (jointZr Λ)ᵀ = -jointZr Λ := by
  ext i j
  have h := congrFun (congrFun (jointZ_transpose Λ) i) j
  simp only [transpose_apply, neg_apply] at h
  simp [h]

theorem Z0r_minpoly : (jointZr (Fin 1) * jointZr (Fin 1) + 1) *
    (jointZr (Fin 1) * jointZr (Fin 1) + 9 • 1) = 0 := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix Z0_minpoly
  rw [map_zero, map_mul, map_add, map_add, map_mul, map_one, map_ofNat] at h
  rw [nsmul_one, Nat.cast_ofNat]
  exact h

section Abs

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **`|Z| = (-Z² + 3I)/4`** (`lem:joint-pins`(a), `ℓ = 1`), as a definition. -/
noncomputable def absMat (Z : Matrix n n ℝ) : Matrix n n ℝ :=
  (1 / 4 : ℝ) • (3 • (1 : Matrix n n ℝ) - Z * Z)

/-- The sum-of-squares identity behind `T ± iZ ⪰ 0`, in any ring: with `Q₁ = Y² - 4Y + 3` and
`Q₂ = Q₁(Y + 3)`, `48 Q₁ = 2Q₁² + Q₂²` whenever `(Y² - 1)(Y² - 9) = 0`. -/
theorem sos_identity {R : Type*} [Ring R] (Y : R) (hm : (Y * Y - 1) * (Y * Y - 9 • 1) = 0) :
    48 • (Y * Y - 4 • Y + 3 • 1) =
      2 • ((Y * Y - 4 • Y + 3 • 1) * (Y * Y - 4 • Y + 3 • 1)) +
        ((Y * Y - 4 • Y + 3 • 1) * (Y + 3 • 1)) * ((Y * Y - 4 • Y + 3 • 1) * (Y + 3 • 1)) := by
  have h : 48 • (Y * Y - 4 • Y + 3 • 1) -
      (2 • ((Y * Y - 4 • Y + 3 • 1) * (Y * Y - 4 • Y + 3 • 1)) +
        ((Y * Y - 4 • Y + 3 • 1) * (Y + 3 • 1)) * ((Y * Y - 4 • Y + 3 • 1) * (Y + 3 • 1))) =
      (Y * Y - 1) * (Y * Y - 9 • 1) * (-(Y * Y) + 2 • Y + 5 • 1) := by
    noncomm_ring
  rw [hm, zero_mul, sub_eq_zero] at h
  exact h

theorem cplx_eq (A : Matrix n n ℝ) :
    JointRows.RowsA.cplx A = Complex.ofRealHom.mapMatrix A := rfl

omit [Fintype n] [DecidableEq n] in
theorem cplx_smul (r : ℝ) (A : Matrix n n ℝ) :
    JointRows.RowsA.cplx (r • A) = (r : ℂ) • JointRows.RowsA.cplx A := by
  ext i j
  simp [JointRows.RowsA.cplx]

omit [Fintype n] [DecidableEq n] in
theorem cplx_conjTranspose {a : Type*} (A : Matrix n a ℝ) :
    (JointRows.RowsA.cplx A)ᴴ = JointRows.RowsA.cplx Aᵀ := by
  ext i j
  simp [JointRows.RowsA.cplx]

omit [DecidableEq n] in
theorem cplx_mul' {a b : Type*} (A : Matrix a n ℝ) (B : Matrix n b ℝ) :
    JointRows.RowsA.cplx (A * B) = JointRows.RowsA.cplx A * JointRows.RowsA.cplx B := by
  ext i j
  simp [JointRows.RowsA.cplx, Matrix.mul_apply]

theorem cplx_absMat (Z : Matrix n n ℝ) :
    JointRows.RowsA.cplx (absMat Z) =
      (1 / 4 : ℂ) • (3 • (1 : Matrix n n ℂ) -
        JointRows.RowsA.cplx Z * JointRows.RowsA.cplx Z) := by
  rw [absMat, cplx_smul, cplx_eq, cplx_eq, map_sub, map_nsmul, map_one, map_mul]
  norm_num

/-- **`lem:joint-pins`(a): `|Z| - iZ ⪰ 0`** for every real antisymmetric `Z` with
`(Z² + I)(Z² + 9I) = 0`, in the form `hN` of `joint_potential_paley`. -/
theorem absMat_sub_I_posSemidef (Z : Matrix n n ℝ) (hZ : Zᵀ = -Z)
    (hm : (Z * Z + 1) * (Z * Z + 9 • 1) = 0) :
    (JointRows.RowsA.cplx (absMat Z) - Complex.I • JointRows.RowsA.cplx Z).PosSemidef := by
  set Zc := JointRows.RowsA.cplx Z with hZc
  set Y : Matrix n n ℂ := Complex.I • Zc with hYdef
  have hZcH : Zcᴴ = -Zc := by
    rw [hZc, cplx_conjTranspose, hZ]
    ext i j
    simp [JointRows.RowsA.cplx]
  have hYH : Yᴴ = Y := by
    rw [hYdef, conjTranspose_smul, hZcH, Complex.star_def, Complex.conj_I, smul_neg, neg_smul,
      neg_neg]
  have hYY : Y * Y = -(Zc * Zc) := by
    rw [hYdef, smul_mul_smul_comm, Complex.I_mul_I, neg_one_smul]
  have hmc : (Zc * Zc + 1) * (Zc * Zc + 9 • 1) = 0 := by
    have h := congrArg Complex.ofRealHom.mapMatrix hm
    rw [map_zero, map_mul, map_add, map_add, map_mul, map_one, map_nsmul, map_one] at h
    rw [hZc, cplx_eq]
    exact h
  have hmY : (Y * Y - 1) * (Y * Y - 9 • 1) = 0 := by
    rw [hYY]
    have : (-(Zc * Zc) - 1) * (-(Zc * Zc) - 9 • 1) = (Zc * Zc + 1) * (Zc * Zc + 9 • 1) := by
      noncomm_ring
    rw [this, hmc]
  set Q₁ : Matrix n n ℂ := Y * Y - 4 • Y + 3 • 1 with hQ₁
  set Q₂ : Matrix n n ℂ := Q₁ * (Y + 3 • 1) with hQ₂
  have hQ₁H : Q₁ᴴ = Q₁ := by
    rw [hQ₁, conjTranspose_add, conjTranspose_sub, conjTranspose_mul, conjTranspose_nsmul,
      conjTranspose_nsmul, conjTranspose_one, hYH]
  have hQ₂H : Q₂ᴴ = Q₂ := by
    rw [hQ₂, conjTranspose_mul, hQ₁H, conjTranspose_add, conjTranspose_nsmul, conjTranspose_one,
      hYH, hQ₁]
    noncomm_ring
  have hsos := sos_identity Y hmY
  rw [← hQ₁, ← hQ₂] at hsos
  have hT : JointRows.RowsA.cplx (absMat Z) - Complex.I • Zc =
      (1 / 96 : ℂ) • (Q₁ᴴ * Q₁) + (1 / 192 : ℂ) • (Q₂ᴴ * Q₂) := by
    rw [hQ₁H, hQ₂H]
    have h1 : (1 / 96 : ℂ) • (Q₁ * Q₁) + (1 / 192 : ℂ) • (Q₂ * Q₂) =
        (1 / 192 : ℂ) • (2 • (Q₁ * Q₁) + Q₂ * Q₂) := by
      module
    rw [h1, ← hsos, cplx_absMat, ← hZc, hQ₁, hYY]
    module
  have h96 : (0 : ℂ) ≤ 1 / 96 := by simp
  have h192 : (0 : ℂ) ≤ 1 / 192 := by simp
  rw [hT]
  exact ((posSemidef_conjTranspose_mul_self Q₁).smul h96).add
    ((posSemidef_conjTranspose_mul_self Q₂).smul h192)

/-- **`lem:joint-pins`(a): `|Z| + iZ ⪰ 0`** (the other sign, by transposition). -/
theorem absMat_add_I_posSemidef (Z : Matrix n n ℝ) (hZ : Zᵀ = -Z)
    (hm : (Z * Z + 1) * (Z * Z + 9 • 1) = 0) :
    (JointRows.RowsA.cplx (absMat Z) + Complex.I • JointRows.RowsA.cplx Z).PosSemidef := by
  have h := (absMat_sub_I_posSemidef Z hZ hm).transpose
  have hT : (absMat Z)ᵀ = absMat Z := by
    rw [absMat, transpose_smul, transpose_sub, transpose_mul, hZ, transpose_smul, transpose_one]
    simp
  have e : (JointRows.RowsA.cplx (absMat Z) - Complex.I • JointRows.RowsA.cplx Z)ᵀ =
      JointRows.RowsA.cplx (absMat Z) + Complex.I • JointRows.RowsA.cplx Z := by
    rw [transpose_sub, transpose_smul]
    have h1 : (JointRows.RowsA.cplx (absMat Z))ᵀ = JointRows.RowsA.cplx (absMat Z) := by
      conv_rhs => rw [← hT]
      ext i j; simp [JointRows.RowsA.cplx]
    have h2 : (JointRows.RowsA.cplx Z)ᵀ = -JointRows.RowsA.cplx Z := by
      ext i j
      have := congrFun (congrFun hZ i) j
      simp only [transpose_apply] at this
      simp [JointRows.RowsA.cplx, this]
    rw [h1, h2, smul_neg, sub_neg_eq_add]
  rw [e] at h
  exact h

/-- **`|Z|` is positive semidefinite** (`lem:joint-pins`(a)). -/
theorem absMat_posSemidef (Z : Matrix n n ℝ) (hZ : Zᵀ = -Z) : (absMat Z).PosSemidef := by
  have e : absMat Z = (1 / 4 : ℝ) • (3 • (1 : Matrix n n ℝ) + Zᴴ * Z) := by
    rw [absMat, conjTranspose_eq_transpose_of_trivial, hZ, neg_mul, sub_eq_add_neg]
  have h3 : (3 • (1 : Matrix n n ℝ)).PosSemidef := by
    rw [nsmul_one]
    exact PosSemidef.natCast 3
  rw [e]
  exact (h3.add (posSemidef_conjTranspose_mul_self Z)).smul (by norm_num)

/-- **`|Z|² = ZᵀZ`** (`lem:joint-pins`(a)): `absMat Z` is the positive square root of `ZᵀZ`. -/
theorem absMat_sq (Z : Matrix n n ℝ) (hZ : Zᵀ = -Z) (hm : (Z * Z + 1) * (Z * Z + 9 • 1) = 0) :
    absMat Z * absMat Z = Zᵀ * Z := by
  have h : (3 • (1 : Matrix n n ℝ) - Z * Z) * (3 • (1 : Matrix n n ℝ) - Z * Z) =
      (Z * Z + 1) * (Z * Z + 9 • 1) - 16 • (Z * Z) := by
    noncomm_ring
  rw [absMat, smul_mul_smul_comm, h, hm, hZ, neg_mul]
  module

end Abs



/-! ### `ℓ = 1`: `|𝒵₀|` -/

/-- **`|𝒵₀| = (-𝒵₀² + 3I)/4`** for the `L` rows with one layer. -/
noncomputable abbrev absZ0 : Matrix (Fin 2 × ZMod 6 × Fin 1) (Fin 2 × ZMod 6 × Fin 1) ℝ :=
  absMat (jointZr (Fin 1))

/-- **`lem:joint-pins`(a), `ℓ = 1`**: `|𝒵₀| ⪰ 0`, `|𝒵₀|² = 𝒵₀ᵀ𝒵₀`, and `|𝒵₀| ± i𝒵₀ ⪰ 0`. -/
theorem absZ0_spec : absZ0.PosSemidef ∧ absZ0 * absZ0 = (jointZr (Fin 1))ᵀ * jointZr (Fin 1) ∧
    (JointRows.RowsA.cplx absZ0 - Complex.I • JointRows.RowsA.cplx (jointZr (Fin 1))).PosSemidef ∧
    (JointRows.RowsA.cplx absZ0 + Complex.I • JointRows.RowsA.cplx (jointZr (Fin 1))).PosSemidef :=
  ⟨absMat_posSemidef _ (jointZr_transpose _), absMat_sq _ (jointZr_transpose _) Z0r_minpoly,
    absMat_sub_I_posSemidef _ (jointZr_transpose _) Z0r_minpoly,
    absMat_add_I_posSemidef _ (jointZr_transpose _) Z0r_minpoly⟩

/-- **`hN` of `joint_pins` for `ℓ = 1`, `T = |𝒵₀|`.** -/
theorem absMat_Z0_sub_I :
    (JointRows.RowsA.cplx absZ0 - Complex.I • JointRows.RowsA.cplx (jointZr (Fin 1))).PosSemidef :=
  absZ0_spec.2.2.1

/-! ### `ℓ = 2`: `𝒵 = 𝒵₀ ⊗ J₂` and the twin embedding -/

/-- **The twin embedding** `E`: `E((c, u, l), (c', u', 0)) = [(c, u) = (c', u')]`, so that
`E Eᵀ = I ⊗ J_ℓ` and `E M Eᵀ = M ⊗ J_ℓ`. -/
def twinE (Λ : Type*) : Matrix (Fin 2 × ZMod 6 × Λ) (Fin 2 × ZMod 6 × Fin 1) ℤ :=
  Matrix.of fun i j => if j = (i.1, i.2.1, 0) then 1 else 0

/-- `𝒵 = 𝒵₀ ⊗ J_ℓ = E 𝒵₀ Eᵀ` (the factor `J_ℓ` of `lem:joint-pins`: edges carry no layer
condition). -/
theorem jointZ_eq_twin (Λ : Type*) [Fintype Λ] : jointZ Λ = twinE Λ * Z0 * (twinE Λ)ᵀ := by
  ext i j
  simp [Matrix.mul_apply, twinE, jointZ, ite_mul, mul_ite]

/-- The real twin embedding. -/
abbrev twinEr (Λ : Type*) : Matrix (Fin 2 × ZMod 6 × Λ) (Fin 2 × ZMod 6 × Fin 1) ℝ :=
  (twinE Λ).map (Int.cast : ℤ → ℝ)

theorem jointZr_eq_twin (Λ : Type*) [Fintype Λ] :
    jointZr Λ = twinEr Λ * jointZr (Fin 1) * (twinEr Λ)ᵀ := by
  rw [jointZr, toReal, jointZ_eq_twin]
  have h1 := Matrix.map_mul (L := twinE Λ * Z0) (M := (twinE Λ)ᵀ) (f := Int.castRingHom ℝ)
  have h2 := Matrix.map_mul (L := twinE Λ) (M := Z0) (f := Int.castRingHom ℝ)
  simp only [Int.coe_castRingHom] at h1 h2
  rw [h1, h2, transpose_map]

/-- **`lem:joint-pins`(a), `ℓ = 2` (and every `ℓ`)**: if `T₀ + s𝒵₀ ⪰ 0` then
`T₀ ⊗ J_ℓ + s𝒵 = E (T₀ + s𝒵₀) Eᴴ ⪰ 0`; with `s = ∓i` this is the paper's "for `ℓ = 2` it suffices
that `T = T₀ ⊗ J₂` with `T₀ ± i𝒵₀ ⪰ 0`". -/
theorem twin_posSemidef (Λ : Type*) [Fintype Λ] [DecidableEq Λ]
    (T0 : Matrix (Fin 2 × ZMod 6 × Fin 1) (Fin 2 × ZMod 6 × Fin 1) ℝ) (s : ℂ)
    (h : (JointRows.RowsA.cplx T0 + s • JointRows.RowsA.cplx (jointZr (Fin 1))).PosSemidef) :
    (JointRows.RowsA.cplx (twinEr Λ * T0 * (twinEr Λ)ᵀ) +
      s • JointRows.RowsA.cplx (jointZr Λ)).PosSemidef := by
  have e : JointRows.RowsA.cplx (twinEr Λ * T0 * (twinEr Λ)ᵀ) +
      s • JointRows.RowsA.cplx (jointZr Λ) = JointRows.RowsA.cplx (twinEr Λ) *
        (JointRows.RowsA.cplx T0 + s • JointRows.RowsA.cplx (jointZr (Fin 1))) *
          (JointRows.RowsA.cplx (twinEr Λ))ᴴ := by
    rw [jointZr_eq_twin Λ, cplx_conjTranspose, cplx_mul', cplx_mul', cplx_mul', cplx_mul',
      Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
  rw [e]
  exact h.mul_mul_conjTranspose_same _

/-- **`|𝒵| = |𝒵₀| ⊗ J₂`** for the `L` rows with two layers. -/
noncomputable abbrev absZ2 : Matrix (Fin 2 × ZMod 6 × Fin 2) (Fin 2 × ZMod 6 × Fin 2) ℝ :=
  twinEr (Fin 2) * absZ0 * (twinEr (Fin 2))ᵀ

/-- **`hN` of `joint_pins` for `ℓ = 2`, `T = |𝒵₀| ⊗ J₂`**, and the other sign. -/
theorem absZ2_sub_I :
    (JointRows.RowsA.cplx absZ2 - Complex.I • JointRows.RowsA.cplx (jointZr (Fin 2))).PosSemidef ∧
    (JointRows.RowsA.cplx absZ2 +
      Complex.I • JointRows.RowsA.cplx (jointZr (Fin 2))).PosSemidef := by
  constructor
  · have h := twin_posSemidef (Fin 2) absZ0 (-Complex.I) (by
      rw [neg_smul, ← sub_eq_add_neg]
      exact absZ0_spec.2.2.1)
    rwa [neg_smul, ← sub_eq_add_neg] at h
  · exact twin_posSemidef (Fin 2) absZ0 Complex.I absZ0_spec.2.2.2


/-- `EᵀE = ℓ I` for `ℓ = 2`. -/
theorem twinE_transpose_mul : (twinE (Fin 2))ᵀ * twinE (Fin 2) = 2 := by decide +kernel

theorem twinEr_transpose_mul : (twinEr (Fin 2))ᵀ * twinEr (Fin 2) = (2 : ℝ) • 1 := by
  have h := congrArg (Int.castRingHom ℝ).mapMatrix twinE_transpose_mul
  rw [map_ofNat, RingHom.mapMatrix_apply, Matrix.map_mul, transpose_map] at h
  simp only [Int.coe_castRingHom] at h
  rw [h, two_smul, one_add_one_eq_two]

/-- Products of twin images: `(E A Eᵀ)(E B Eᵀ) = 2 E(AB)Eᵀ`. -/
theorem twin_mul (A B : Matrix (Fin 2 × ZMod 6 × Fin 1) (Fin 2 × ZMod 6 × Fin 1) ℝ) :
    (twinEr (Fin 2) * A * (twinEr (Fin 2))ᵀ) * (twinEr (Fin 2) * B * (twinEr (Fin 2))ᵀ) =
      (2 : ℝ) • (twinEr (Fin 2) * (A * B) * (twinEr (Fin 2))ᵀ) := by
  have e : (twinEr (Fin 2) * A * (twinEr (Fin 2))ᵀ) * (twinEr (Fin 2) * B * (twinEr (Fin 2))ᵀ) =
      twinEr (Fin 2) * A * ((twinEr (Fin 2))ᵀ * twinEr (Fin 2)) * B * (twinEr (Fin 2))ᵀ := by
    simp only [Matrix.mul_assoc]
  rw [e, twinEr_transpose_mul, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.mul_assoc (twinEr (Fin 2)) A B]

/-- **`lem:joint-pins`(a), `ℓ = 2`**: `|𝒵| = |𝒵₀| ⊗ J₂` is positive semidefinite, its square is
`𝒵ᵀ𝒵`, and `|𝒵| = (-𝒵² + 12Π)/8` with `Π = EEᵀ/2 = I ⊗ J₂/2` the projection onto the vectors
constant on each twin class. -/
theorem absZ2_spec : absZ2.PosSemidef ∧ absZ2 * absZ2 = (jointZr (Fin 2))ᵀ * jointZr (Fin 2) ∧
    absZ2 = (1 / 8 : ℝ) • (-(jointZr (Fin 2) * jointZr (Fin 2)) +
      (12 : ℝ) • ((1 / 2 : ℝ) • (twinEr (Fin 2) * (twinEr (Fin 2))ᵀ))) := by
  refine ⟨?_, ?_, ?_⟩
  · have h := absZ0_spec.1.mul_mul_conjTranspose_same (twinEr (Fin 2))
    rwa [conjTranspose_eq_transpose_of_trivial] at h
  · have hZ : (jointZr (Fin 2))ᵀ = twinEr (Fin 2) * (jointZr (Fin 1))ᵀ * (twinEr (Fin 2))ᵀ := by
      rw [jointZr_eq_twin (Fin 2), transpose_mul, transpose_mul, transpose_transpose,
        Matrix.mul_assoc]
    rw [twin_mul, absZ0_spec.2.1, hZ, jointZr_eq_twin (Fin 2), twin_mul]
  · rw [jointZr_eq_twin (Fin 2), twin_mul, absZ2, absZ0, absMat]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    module

open scoped MatrixOrder in
/-- **`|𝒵|` is the matrix absolute value** (`lem:joint-pins`(a)): `CFC.abs 𝒵₀ = (-𝒵₀² + 3I)/4`
and `CFC.abs 𝒵 = (-𝒵² + 12Π)/8` for two layers, by uniqueness of positive square roots. -/
theorem cfc_abs_eq : CFC.abs (jointZr (Fin 1)) = absZ0 ∧ CFC.abs (jointZr (Fin 2)) = absZ2 := by
  have key : ∀ {m : Type} [Fintype m] [DecidableEq m] (A T : Matrix m m ℝ), T.PosSemidef →
      T * T = Aᵀ * A → CFC.abs A = T := by
    intro m _ _ A T hT h
    rw [CFC.abs, CFC.sqrt_eq_iff _ _ ?_ hT.nonneg]
    · rw [h, star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]
    · rw [star_eq_conjTranspose]
      exact (posSemidef_conjTranspose_mul_self A).nonneg
  exact ⟨key _ _ absZ0_spec.1 absZ0_spec.2.1, key _ _ absZ2_spec.1 absZ2_spec.2.1⟩

/-! ## (b): the pin classes -/

theorem rot_rot_rot (u : ZMod 6) : rot (rot (rot u)) = u := by revert u; decide

/-- Two distinct base coordinates of the same parity lie on one rotation triangle, so one is the
rotation of the other. -/
theorem rot_cases : ∀ u u' : ZMod 6, u.val % 2 = u'.val % 2 → u = u' ∨ u' = rot u ∨ u = rot u' := by
  decide

section Pins

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {Λ : Type*}

/-- **The pins of a base coordinate** (`lem:joint-pins`(b)): the label `t` satisfies the signed
conditions of the base coordinate `u` towards the middle labels `m`, `t → m(rot u, l)` and
`m(rot⁻¹ u, l) → t` for every layer `l`, where `x → y` is the strict-square relation
`χ(y - x) = 1` (`Sarkozy.Labellings.Feasible`). By `pinAdm_iff_edges` these are exactly the edge
conditions of `G_{FL}` and of `G_{EL}` between an outer label of base coordinate `u` and the middle
row. The allowed set of `u` in the paper is contained in `{t | PinAdm m u t}` (it also excludes
the middle and the other fixed labels). -/
def PinAdm (m : ZMod 6 × Λ → F) (u : ZMod 6) (t : F) : Prop :=
  ∀ l, quadraticChar F (m (rot u, l) - t) = 1 ∧ quadraticChar F (t - m (rot (rot u), l)) = 1

/-- **`PinAdm` is the edge condition of the graphs**: for `G_{FL}` or `G_{EL}`, an outer label
`(a, u, l)` (`a ≠ 1`) with value `t` satisfies the strict-square conditions of all its edges to and
from the middle row (labels `m`) iff `PinAdm m u t`. -/
theorem pinAdm_iff_edges {c : FieldType (Fin 3)} (hc : c = typeF ∨ c = typeE) (a : Fin 3)
    (ha : a ≠ 1) (u : ZMod 6) (l : Λ) (m : ZMod 6 × Λ → F) (t : F) :
    ((∀ (v : ZMod 6) (l' : Λ), twoLayerEdge c typeL (a, u, l) (1, v, l') = true →
        quadraticChar F (m (v, l') - t) = 1) ∧
      (∀ (v : ZMod 6) (l' : Λ), twoLayerEdge c typeL (1, v, l') (a, u, l) = true →
        quadraticChar F (t - m (v, l')) = 1)) ↔ PinAdm m u t := by
  constructor
  · rintro ⟨hout, hin⟩ l'
    exact ⟨hout _ l' ((pin_out_edge hc a ha u _ l l').2 rfl),
      hin _ l' ((pin_in_edge hc a ha u _ l l').2 rfl)⟩
  · intro h
    refine ⟨fun v l' he => ?_, fun v l' he => ?_⟩
    · rw [(pin_out_edge hc a ha u v l l').1 he]
      exact (h l').1
    · rw [(pin_in_edge hc a ha u v l l').1 he]
      exact (h l').2

/-- **The tournament step** (`lem:joint-pins`(b), proof): at `|F| ≡ 3 (mod 4)` no label is
admissible both for `u` and for `rot u`, since the in-pin of `u` is the out-pin of `rot u`. -/
theorem pinAdm_rot (h3 : Fintype.card F % 4 = 3) [Nonempty Λ] {m : ZMod 6 × Λ → F} {u : ZMod 6}
    {t : F} (hu : PinAdm m u t) : ¬ PinAdm m (rot u) t := by
  intro hr
  obtain ⟨l⟩ := ‹Nonempty Λ›
  have h1 := (hu l).2
  have h2 := (hr l).1
  rw [TraceMixing.chi_swap h3, h1] at h2
  norm_num at h2

/-- **`lem:joint-pins`(b), core**: two base coordinates of the same parity that both admit `t`
are equal. -/
theorem pinAdm_eq_of_parity (h3 : Fintype.card F % 4 = 3) [Nonempty Λ]
    {m : ZMod 6 × Λ → F} {u u' : ZMod 6} {t : F} (hu : PinAdm m u t) (hu' : PinAdm m u' t)
    (hp : u.val % 2 = u'.val % 2) : u = u' := by
  rcases rot_cases u u' hp with h | h | h
  · exact h
  · exact absurd (h ▸ hu') (pinAdm_rot h3 hu)
  · exact absurd (h ▸ hu) (pinAdm_rot h3 hu')

/-- The even base coordinate admitting `t`, or `0` if there is none. -/
noncomputable def pinEven (m : ZMod 6 × Λ → F) (t : F) : ZMod 6 := by
  classical exact if h : ∃ e : ZMod 6, e.val % 2 = 0 ∧ PinAdm m e t then h.choose else 0

/-- The odd base coordinate admitting `t`, or `1` if there is none. -/
noncomputable def pinOdd (m : ZMod 6 × Λ → F) (t : F) : ZMod 6 := by
  classical exact if h : ∃ o : ZMod 6, o.val % 2 = 1 ∧ PinAdm m o t then h.choose else 1

theorem pinEven_even (m : ZMod 6 × Λ → F) (t : F) : (pinEven m t).val % 2 = 0 := by
  classical
  unfold pinEven
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

theorem pinOdd_odd (m : ZMod 6 × Λ → F) (t : F) : (pinOdd m t).val % 2 = 1 := by
  classical
  unfold pinOdd
  split_ifs with h
  · exact h.choose_spec.1
  · rfl

/-- Every base coordinate admitting `t` is `pinEven m t` or `pinOdd m t`. -/
theorem pinAdm_eq_sel (h3 : Fintype.card F % 4 = 3) [Nonempty Λ] {m : ZMod 6 × Λ → F}
    {u : ZMod 6} {t : F} (hu : PinAdm m u t) : u = pinEven m t ∨ u = pinOdd m t := by
  classical
  rcases Nat.mod_two_eq_zero_or_one u.val with h0 | h1
  · left
    have hex : ∃ e : ZMod 6, e.val % 2 = 0 ∧ PinAdm m e t := ⟨u, h0, hu⟩
    have he : pinEven m t = hex.choose := by
      unfold pinEven
      simp only [hex, ↓reduceDIte]
    rw [he]
    exact pinAdm_eq_of_parity h3 hu hex.choose_spec.2 (by rw [h0, hex.choose_spec.1])
  · right
    have hex : ∃ o : ZMod 6, o.val % 2 = 1 ∧ PinAdm m o t := ⟨u, h1, hu⟩
    have ho : pinOdd m t = hex.choose := by
      unfold pinOdd
      simp only [hex, ↓reduceDIte]
    rw [ho]
    exact pinAdm_eq_of_parity h3 hu hex.choose_spec.2 (by rw [h1, hex.choose_spec.1])

/-- **`lem:joint-pins`(b)**: at `|F| ≡ 3 (mod 4)`, for all middle labels `m` and every label `t`,
the base coordinates whose pins `t` satisfies are among one even and one odd base coordinate. -/
theorem pin_classes (h3 : Fintype.card F % 4 = 3) [Nonempty Λ] (m : ZMod 6 × Λ → F) (t : F) :
    ∃ e o : ZMod 6, e.val % 2 = 0 ∧ o.val % 2 = 1 ∧ ∀ u, PinAdm m u t → u = e ∨ u = o :=
  ⟨pinEven m t, pinOdd m t, pinEven_even m t, pinOdd_odd m t, fun _ hu => pinAdm_eq_sel h3 hu⟩

end Pins

section Classes

variable (Λ : Type*) [Fintype Λ] [DecidableEq Λ]

/-- The class of an even base coordinate `e` and an odd one `o`: the coordinates `(c, u, l)` of the
joint block with `u ∈ {e, o}`, in both copies `c` and with all twins `l`. -/
def pinClass (e o : ZMod 6) : Finset (Fin 2 × ZMod 6 × Λ) :=
  univ.filter fun i => i.2.1 = e ∨ i.2.1 = o

/-- **The nine pin classes `𝒮`** of `lem:joint-pins`(b). -/
def pinClasses : Finset (Finset (Fin 2 × ZMod 6 × Λ)) :=
  ((univ.filter fun e : ZMod 6 => e.val % 2 = 0) ×ˢ
    (univ.filter fun o : ZMod 6 => o.val % 2 = 1)).image
    fun eo => pinClass Λ eo.1 eo.2

/-- There are nine classes, for one and for two layers. -/
theorem pinClasses_card : (pinClasses (Fin 1)).card = 9 ∧ (pinClasses (Fin 2)).card = 9 := by
  decide +kernel

end Classes

section Selector

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {Λ : Type*} [Fintype Λ] [DecidableEq Λ]

/-- **The selector**: the class containing all coordinates whose pins `t` satisfies. -/
noncomputable def pinSel (m : ZMod 6 × Λ → F) (t : F) : Finset (Fin 2 × ZMod 6 × Λ) :=
  pinClass Λ (pinEven m t) (pinOdd m t)

theorem pinSel_mem (m : ZMod 6 × Λ → F) (t : F) : pinSel m t ∈ pinClasses Λ := by
  unfold pinSel pinClasses
  rw [Finset.mem_image]
  exact ⟨(pinEven m t, pinOdd m t), Finset.mem_product.2 ⟨Finset.mem_filter.2 ⟨mem_univ _,
    pinEven_even m t⟩, Finset.mem_filter.2 ⟨mem_univ _, pinOdd_odd m t⟩⟩, rfl⟩

omit [DecidableEq Λ] in
/-- **`lem:joint-pins`(b), the hypothesis of `lem:joint-potential`**: every coordinate whose pins
`t` satisfies lies in the class `pinSel m t ∈ 𝒮`. -/
theorem mem_pinSel (h3 : Fintype.card F % 4 = 3) [Nonempty Λ] {m : ZMod 6 × Λ → F} {t : F}
    {i : Fin 2 × ZMod 6 × Λ} (hi : PinAdm m i.2.1 t) : i ∈ pinSel m t := by
  unfold pinSel pinClass
  rw [Finset.mem_filter]
  exact ⟨mem_univ _, pinAdm_eq_sel h3 hi⟩

end Selector

/-! ## Consequence: `lem:joint-potential` with the pin classes -/

open Sarkozy.JointRows Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {Ω : Type*} [Fintype Ω]

/-- **`lem:joint-pins`, consequence.** Let `p ≡ 3 (mod 4)`, let `𝒵` be the matrix of the `L` rows
with `ℓ = |Λ|` layers (`jointZr Λ`), `𝒮` the nine pin classes and `m` the middle labels. Let `T` be
a
real matrix with `T - i𝒵 ⪰ 0` (`hN`; for `T = |𝒵|` this is `absMat_Z0_sub_I` for `ℓ = 1` and
`absZ2_sub_I` for `ℓ = 2`), and let `D(t) = diag(√ρ_i(t))` vanish where `t` violates the pins of the
base coordinate of `i` (`hD0`). If `𝗄 > 0` and the gates `𝗄²I_S - 𝗄κ₀T_S - κ₀²𝒢_S ⪰ 0` hold for all
`S ∈ 𝒮` (`hgate`), then `r𝗄` is a joint pure-star coefficient: the lower bound of
`lem:joint-rows`(a) holds with `r𝗄/I₀` in place of `κ₀r𝗄/I₀`. This is
`Sarkozy.JointRows.Restrict.joint_potential_paley` with `𝒵`, `𝒮` and the selector of (b) fixed and
its hypotheses `hSel`, `hdS` discharged by `pinSel_mem` and `mem_pinSel`; its other hypotheses (the
kernel expansions, their bounds and the structure of the pure part) are kept as hypotheses. -/
theorem joint_pins {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3)
    {Λ : Type*} [Fintype Λ] [DecidableEq Λ] [Nonempty Λ] {Hs : Type*} [NormedAddCommGroup Hs]
    (lam : FiniteLaw Ω) (I : Ω → Prop) (hPpos : 0 < Peyre.prob lam I)
    (ν : FiniteLaw Ω) (g : Ω → ℝ) (ℓ : ℝ)
    (hν : ∀ x, ν.weight x = g x * (Peyre.condLaw lam I hPpos).weight x)
    (hg : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 → Real.exp (-ℓ) ≤ g x)
    (KE KF KstE KstF TnsE TnsF TcollE TcollF : Ω → Ω → ℝ)
    (hg1 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens1 (Peyre.condLaw lam I hPpos) KE x)
    (hg2 : ∀ x, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      g x = RowsA.dens2 (Peyre.condLaw lam I hPpos) KE x)
    (hexpE : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 → KE x y = 1 + KstE x y + TnsE x y - TcollE x y)
    (hexpF : ∀ x y, (Peyre.condLaw lam I hPpos).weight x ≠ 0 →
      (Peyre.condLaw lam I hPpos).weight y ≠ 0 → KF x y = 1 + KstF x y + TnsF x y - TcollF x y)
    {εE SE NE nE nE' mE εF SF NF nF nF' mF : ℝ}
    (hεE : |RowsA.mass (Peyre.condLaw lam I hPpos) KE - 1| ≤ εE) (hεE1 : εE < 1)
    (hSE0 : 0 ≤ SE) (hSE : PerpBound (Peyre.condLaw lam I hPpos) KstE SE)
    (hnsE : FormBound (Peyre.condLaw lam I hPpos) TnsE nE)
    (hcollE : FormBound (Peyre.condLaw lam I hPpos) TcollE nE') (hNE : nE + nE' ≤ NE)
    (hmE1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) KE)) ≤ mE)
    (hmE2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) KE)) ≤ mE)
    (hεF : |RowsA.mass (Peyre.condLaw lam I hPpos) KF - 1| ≤ εF) (hεF1 : εF < 1)
    (hSF0 : 0 ≤ SF) (hSF : PerpBound (Peyre.condLaw lam I hPpos) KstF SF)
    (hnsF : FormBound (Peyre.condLaw lam I hPpos) TnsF nF)
    (hcollF : FormBound (Peyre.condLaw lam I hPpos) TcollF nF') (hNF : nF + nF' ≤ NF)
    (hmF1 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone (Peyre.condLaw lam I hPpos) KF)) ≤ mF)
    (hmF2 : nrm (Peyre.condLaw lam I hPpos) (cen (Peyre.condLaw lam I hPpos)
      (kone' (Peyre.condLaw lam I hPpos) KF)) ≤ mF)
    (qPure qmean : EuclideanSpace ℝ (Ω ⊕ Ω) → ℝ) {I₀ κ₀ r k eF eE : ℝ}
    (hI₀ : 0 < I₀) (hP : I₀ ≤ Peyre.prob lam I) (hκ₀ : 0 < κ₀) (hr : 0 ≤ r) (hk : 0 < k)
    (heF : 0 ≤ eF) (heE : 0 ≤ eE)
    (hdec : ∀ x, Restrict.qTc lam KstE KstF x = qPure x + qmean x)
    (hmean : ∀ x, |qmean x| ≤ κ₀ * r * (eF + eE) * ‖x‖ ^ 2)
    (T G : Matrix (Fin 2 × ZMod 6 × Λ) (Fin 2 × ZMod 6 × Λ) ℝ)
    (hgate : ∀ S ∈ pinClasses Λ,
      ((k ^ 2 • (1 : Matrix (Fin 2 × ZMod 6 × Λ) (Fin 2 × ZMod 6 × Λ) ℝ) - (k * κ₀) • T -
        κ₀ ^ 2 • G).submatrix (fun i : S => (i : Fin 2 × ZMod 6 × Λ))
          (fun i : S => (i : Fin 2 × ZMod 6 × Λ))).PosSemidef)
    (D : ZMod p → (Fin 2 × ZMod 6 × Λ) → ℝ) (m : ZMod 6 × Λ → ZMod p)
    (hdκ : ∀ t i, D t i ^ 2 ≤ κ₀) (hD0 : ∀ t i, ¬ PinAdm m i.2.1 t → D t i = 0)
    (hGpos : ∀ y : (Fin 2 × ZMod 6 × Λ) → ℝ, 0 ≤ y ⬝ᵥ (G *ᵥ y))
    (qS : (ZMod p → (Fin 2 × ZMod 6 × Λ) → ℝ) → Hs → ℝ)
    (uc : EuclideanSpace ℝ (Ω ⊕ Ω) → ZMod p → (Fin 2 × ZMod 6 × Λ) → ℝ)
    (vc : EuclideanSpace ℝ (Ω ⊕ Ω) → Hs)
    (hcomp : ∀ x, qPure x = qS (uc x) (vc x) ∧
      (FiniteLaw.uniform (ZMod p)).expect (fun t => uc x t ⬝ᵥ uc x t) + ‖vc x‖ ^ 2 ≤ ‖x‖ ^ 2)
    (hN : (RowsA.cplx T - Complex.I • RowsA.cplx (jointZr Λ)).PosSemidef)
    (Bq : (ZMod p → (Fin 2 × ZMod 6 × Λ) → ℝ) → Hs → ℝ)
    (hS : ∀ u v, qS u v = r * Eig.zqForm (FiniteLaw.uniform (ZMod p)) (PaleyGauss.paley p)
      (jointZr Λ)
      (fun t i => D t i * u t i) + 2 * Real.sqrt κ₀ * r * Bq (fun t i => D t i * u t i) v)
    (hcouple : ∀ y v, |Bq y v| ≤
      Real.sqrt ((FiniteLaw.uniform (ZMod p)).expect (fun t => y t ⬝ᵥ (G *ᵥ y t))) * ‖v‖) :
    JointBlockLower ν (matchCov (RowsA.relDensity (Peyre.condLaw lam I hPpos) KE g))
      (foldCov ν (RowsA.relDensity (Peyre.condLaw lam I hPpos) KF g))
      (Real.exp ℓ * ((r * k + κ₀ * r * (eF + eE)) / I₀ + RowsA.cconst εF SF NF mF +
        RowsA.cconst εE SE NE mE)) :=
  Restrict.joint_potential_paley hp lam I hPpos ν g ℓ hν hg KE KF KstE KstF TnsE TnsF TcollE TcollF
    hg1 hg2 hexpE hexpF hεE hεE1 hSE0 hSE hnsE hcollE hNE hmE1 hmE2 hεF hεF1 hSF0 hSF hnsF hcollF
    hNF hmF1 hmF2 qPure qmean hI₀ hP hκ₀ hr hk heF heE hdec hmean T G (jointZr Λ) (pinClasses Λ)
    hgate D (pinSel m) (pinSel_mem m) hdκ
    (fun t i hi => hD0 t i fun h => hi (mem_pinSel (by rw [ZMod.card]; exact hp) h))
    hGpos qS uc vc hcomp hN Bq hS hcouple


/-! ## Non-vacuity -/

section NonVacuity

local instance factPrime11 : Fact (Nat.Prime 11) := ⟨by decide⟩

/-- Middle labels `m(v, 0) = v` at the prime `p = 11 ≡ 3 (mod 4)`, one layer. -/
def m11 : ZMod 6 × Fin 1 → ZMod 11 := fun x => (x.1.val : ZMod 11)

theorem card_zmod11 : Fintype.card (ZMod 11) % 4 = 3 := by rw [ZMod.card]

/-- **Non-vacuity of `PinAdm`**: at `p = 11` the label `8` satisfies the pins of the base
coordinate `0` (`χ(2 - 8) = χ(5) = 1`, `χ(8 - 4) = 1`). -/
theorem pinAdm_m11 : PinAdm m11 0 8 := by
  unfold PinAdm
  decide +kernel

/-- ... and not those of `rot 0 = 2` (the tournament step). -/
theorem not_pinAdm_m11 : ¬ PinAdm m11 (rot 0) 8 := pinAdm_rot card_zmod11 pinAdm_m11

/-- **Non-vacuity of the selector**: the coordinate `(copy 0, base 0, twin 0)` lies in the selected
class at the label `8`, and the selected class is one of the nine. -/
theorem pinSel_m11 : ((0 : Fin 2), (0 : ZMod 6), (0 : Fin 1)) ∈ pinSel m11 8 ∧
    pinSel m11 8 ∈ pinClasses (Fin 1) :=
  ⟨mem_pinSel card_zmod11 pinAdm_m11, pinSel_mem m11 8⟩


/-- **Non-vacuity of the gates for `T = |Z|`**: for every real antisymmetric `Z` with
`(Z² + I)(Z² + 9I) = 0`, `𝒢 = 0` and `𝗄 = 3κ₀`, the matrix `𝗄²I - 𝗄κ₀T - κ₀²𝒢` is
`(3κ₀²/4)(9I + Z²) ⪰ 0` (since `(9I + Z²)² = 8(9I + Z²)`), so every principal submatrix gate of
`lem:joint-potential` holds. -/
theorem gate_absMat_nonvacuous {n : Type*} [Fintype n] [DecidableEq n] (Z : Matrix n n ℝ)
    (hZ : Zᵀ = -Z) (hm : (Z * Z + 1) * (Z * Z + 9 • 1) = 0) (κ₀ : ℝ) {m : Type*}
    (e : m → n) :
    (((3 * κ₀) ^ 2 • (1 : Matrix n n ℝ) - (3 * κ₀ * κ₀) • absMat Z -
      κ₀ ^ 2 • (0 : Matrix n n ℝ)).submatrix e e).PosSemidef := by
  have hsym : (9 • (1 : Matrix n n ℝ) + Z * Z)ᴴ = 9 • 1 + Z * Z := by
    rw [conjTranspose_eq_transpose_of_trivial, transpose_add, transpose_smul, transpose_one,
      transpose_mul, hZ, neg_mul_neg]
  have hid : (9 • (1 : Matrix n n ℝ) + Z * Z) * (9 • 1 + Z * Z) = 8 • (9 • 1 + Z * Z) := by
    have h : (9 • (1 : Matrix n n ℝ) + Z * Z) * (9 • 1 + Z * Z) - 8 • (9 • 1 + Z * Z) =
        (Z * Z + 1) * (Z * Z + 9 • 1) := by
      noncomm_ring
    rw [hm] at h
    exact sub_eq_zero.mp h
  have hpsd : (9 • (1 : Matrix n n ℝ) + Z * Z).PosSemidef := by
    have h := (posSemidef_conjTranspose_mul_self (9 • (1 : Matrix n n ℝ) + Z * Z)).smul
      (by norm_num : (0 : ℝ) ≤ 1 / 8)
    rw [hsym, hid] at h
    convert h using 1
    module
  have e' : (3 * κ₀) ^ 2 • (1 : Matrix n n ℝ) - (3 * κ₀ * κ₀) • absMat Z -
      κ₀ ^ 2 • (0 : Matrix n n ℝ) = (3 * κ₀ ^ 2 / 4) • (9 • (1 : Matrix n n ℝ) + Z * Z) := by
    rw [absMat, smul_zero, sub_zero]
    module
  rw [e']
  exact (hpsd.smul (by positivity)).submatrix e

/-- The gates of `joint_pins` are satisfiable for `T = |𝒵₀|` (`𝒢 = 0`, `𝗄 = 3κ₀`). -/
theorem gate_absZ0_nonvacuous (κ₀ : ℝ) : ∀ S ∈ pinClasses (Fin 1),
    (((3 * κ₀) ^ 2 • (1 : Matrix (Fin 2 × ZMod 6 × Fin 1) (Fin 2 × ZMod 6 × Fin 1) ℝ) -
      (3 * κ₀ * κ₀) • absZ0 - κ₀ ^ 2 • (0 : Matrix _ _ ℝ)).submatrix
        (fun i : S => (i : Fin 2 × ZMod 6 × Fin 1))
        (fun i : S => (i : Fin 2 × ZMod 6 × Fin 1))).PosSemidef :=
  fun _ _ => gate_absMat_nonvacuous _ (jointZr_transpose _) Z0r_minpoly κ₀ _

end NonVacuity

end JointPins

end Sarkozy.UpperReference

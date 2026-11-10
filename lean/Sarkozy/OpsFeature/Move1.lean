module

public import Sarkozy.OpsFeature.Lift
public import Sarkozy.OpsFeature.PaleyStars

@[expose] public section

/-!
# Move 1 at one complex structure: the complex test gives the real operator inequality

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`, `eq:matrix-envelope` and the proof of
(a) (move 1): the envelope condition is stated for the complex matrices `𝖥(ξ)`, `𝖤(ξ)` at
`ξ ∈ {i, −i}^X`, and the operators `Φ̂_p` (skew, `Φ̂_p² = −I` on `L²₀`) are reduced to `±i` by the
joint spectral decomposition.

The core step, on one joint spectral sector where the operator is `N₀ ⊗ I + N₁ ⊗ X` with `X`
skew (in the paper `X` is the common complex structure, `X² = −I`), is a real statement:

* **`move1_core`**, **`move1_core_proj`** (on the range of a projection): if the realification
  `[[N₀, −N₁], [N₁, N₀]]` of the Hermitian matrix
  `N₀ + i N₁` is positive semidefinite (the finite complex test `N₀ + i N₁ ⪰ 0`), and `X` is a skew
  contraction (`Xᵀ = −X`, `XᵀX ⪯ I`), then `N₀ ⊗ I + N₁ ⊗ X ⪰ 0`.

The proof: `[[N₀, −N₁], [N₁, N₀]] = G Gᵀ` gives `N₀ = G_α G_αᵀ = G_β G_βᵀ`, `N₁ = G_β G_αᵀ`, and
`N₀ ⊗ I + N₁ ⊗ X = ½(ℬ + 𝒜𝒳ᵀ)(ℬ + 𝒜𝒳ᵀ)ᵀ + ½𝒜(I − 𝒳ᵀ𝒳)𝒜ᵀ` with `𝒜 = G_α ⊗ I`, `ℬ = G_β ⊗ I`,
`𝒳 = I ⊗ X`. No complexification is needed, and only `‖X‖ ≤ 1` is used.

* **`move1_two`**: two commuting complex structures `X`, `Y` (the Paley operators of two blocks on
  `L²₀ ⊗ L²₀`): the joint sectors `P_± = (I ± XY)/2`, on which `Y = ∓X`, reduce
  `M₀ ⊗ I + M₁ ⊗ X + M₂ ⊗ Y + M₃ ⊗ XY ⪰ 0` to the two complex tests `(M₀ ± M₃) + i(M₁ ∓ M₂) ⪰ 0`;
* **`hspec_two`**: B11's `hspec` (`D ⊗ I ± T ⪰ 0`) for the two-factor classes FF and FE, from the
  four finite tests of (d).

Not covered: classes with three or more factors (the `2^{|X|−1}` joint sectors), and the
realization of `𝖥(Φ̂_p)` on a basis of `L²₀` (`Φ̂_p² = −I` there; on the constants `Φ̂_p = 0`).
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace Sarkozy.OpsFeature

section Move1

variable {L V : Type*} [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V]

omit [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V] in
theorem neg_kron {L' V' : Type*} (A : Matrix L L' ℝ) (B : Matrix V V' ℝ) :
    (-A) ⊗ₖ B = -(A ⊗ₖ B) := by
  ext i j
  simp [kroneckerMap_apply, neg_mul]

omit [Fintype L] [DecidableEq L] [Fintype V] [DecidableEq V] in
theorem kron_neg {L' V' : Type*} (A : Matrix L L' ℝ) (B : Matrix V V' ℝ) :
    A ⊗ₖ (-B) = -(A ⊗ₖ B) := by
  ext i j
  simp [kroneckerMap_apply, mul_neg]

/-- **Move 1 at one complex structure.** -/
theorem move1_core (N0 N1 : Matrix L L ℝ) (X : Matrix V V ℝ)
    (hR : (fromBlocks N0 (-N1) N1 N0).PosSemidef) (hX : Xᴴ = -X)
    (hXc : (1 - Xᴴ * X).PosSemidef) :
    (N0 ⊗ₖ (1 : Matrix V V ℝ) + N1 ⊗ₖ X).PosSemidef := by
  obtain ⟨G, hG⟩ := exists_mul_transpose_of_posSemidef hR
  set Ga : Matrix L (L ⊕ L) ℝ := Matrix.of fun a k => G (Sum.inl a) k with hGa
  set Gb : Matrix L (L ⊕ L) ℝ := Matrix.of fun a k => G (Sum.inr a) k with hGb
  have h00 : N0 = Ga * Gaᴴ := by
    ext a b
    have := hG (Sum.inl a) (Sum.inl b)
    simp only [fromBlocks_apply₁₁] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGa, Matrix.of_apply]
  have h11 : N0 = Gb * Gbᴴ := by
    ext a b
    have := hG (Sum.inr a) (Sum.inr b)
    simp only [fromBlocks_apply₂₂] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGb, Matrix.of_apply]
  have h10 : N1 = Gb * Gaᴴ := by
    ext a b
    have := hG (Sum.inr a) (Sum.inl b)
    simp only [fromBlocks_apply₂₁] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGa, hGb, Matrix.of_apply]
  have h01 : -N1 = Ga * Gbᴴ := by
    ext a b
    have := hG (Sum.inl a) (Sum.inr b)
    simp only [fromBlocks_apply₁₂] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGa, hGb, Matrix.of_apply]
  set A := Ga ⊗ₖ (1 : Matrix V V ℝ) with hA
  set B := Gb ⊗ₖ (1 : Matrix V V ℝ) with hB
  set Xk := (1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) ⊗ₖ X with hXk
  have eBB : B * Bᴴ = N0 ⊗ₖ (1 : Matrix V V ℝ) := by
    rw [hB, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.mul_one,
      ← h11]
  have eAA : A * Aᴴ = N0 ⊗ₖ (1 : Matrix V V ℝ) := by
    rw [hA, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.mul_one,
      ← h00]
  have eBXA : B * Xk * Aᴴ = N1 ⊗ₖ X := by
    rw [hB, hXk, hA, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, ← h10]
  have eAXB : A * Xkᴴ * Bᴴ = N1 ⊗ₖ X := by
    simp only [hA, hB, hXk, conjTranspose_kronecker, conjTranspose_one, hX]
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one,
      ← h01, neg_kron, kron_neg, neg_neg]
  have eXX : (1 : Matrix ((L ⊕ L) × V) ((L ⊕ L) × V) ℝ) - Xkᴴ * Xk =
      (1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) ⊗ₖ (1 - Xᴴ * X) := by
    rw [hXk, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul, Matrix.mul_one,
      sub_eq_add_neg, sub_eq_add_neg, kronecker_add, kron_neg, one_kronecker_one]
  have key : N0 ⊗ₖ (1 : Matrix V V ℝ) + N1 ⊗ₖ X =
      (1 / 2 : ℝ) • ((B + A * Xkᴴ) * (B + A * Xkᴴ)ᴴ) +
        (1 / 2 : ℝ) • (A * (1 - Xkᴴ * Xk) * Aᴴ) := by
    have e1 : (B + A * Xkᴴ) * (B + A * Xkᴴ)ᴴ =
        B * Bᴴ + B * Xk * Aᴴ + A * Xkᴴ * Bᴴ + A * (Xkᴴ * Xk) * Aᴴ := by
      simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    have e2 : A * (1 - Xkᴴ * Xk) * Aᴴ = A * Aᴴ - A * (Xkᴴ * Xk) * Aᴴ := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one]
    rw [e1, e2, eBB, eAA, eBXA, eAXB]
    module
  rw [key]
  have p1 : ((B + A * Xkᴴ) * (B + A * Xkᴴ)ᴴ).PosSemidef :=
    posSemidef_self_mul_conjTranspose _
  have p2 : (A * (1 - Xkᴴ * Xk) * Aᴴ).PosSemidef := by
    rw [eXX]
    exact (PosSemidef.one.kronecker hXc).mul_mul_conjTranspose_same A
  exact (p1.smul (by norm_num)).add (p2.smul (by norm_num))

/-- **Move 1 on a sector**: the same with a projection `P` (`Pᵀ = P = P²`) in place of `I` and a
skew `X` living on `ran P` (`XP = X`, `XᵀX ⪯ P`): `N₀ ⊗ P + N₁ ⊗ X ⪰ 0`. -/
theorem move1_core_proj (N0 N1 : Matrix L L ℝ) (P X : Matrix V V ℝ)
    (hR : (fromBlocks N0 (-N1) N1 N0).PosSemidef) (hP : Pᴴ = P) (hPP : P * P = P)
    (hX : Xᴴ = -X) (hXP : X * P = X) (hXc : (P - Xᴴ * X).PosSemidef) :
    (N0 ⊗ₖ P + N1 ⊗ₖ X).PosSemidef := by
  have hPX : P * X = X := by
    have h := congrArg conjTranspose hXP
    rw [conjTranspose_mul, hP, hX] at h
    have h2 := congrArg Neg.neg h
    simpa only [Matrix.mul_neg, neg_neg] using h2
  obtain ⟨G, hG⟩ := exists_mul_transpose_of_posSemidef hR
  set Ga : Matrix L (L ⊕ L) ℝ := Matrix.of fun a k => G (Sum.inl a) k with hGa
  set Gb : Matrix L (L ⊕ L) ℝ := Matrix.of fun a k => G (Sum.inr a) k with hGb
  have h00 : N0 = Ga * Gaᴴ := by
    ext a b
    have := hG (Sum.inl a) (Sum.inl b)
    simp only [fromBlocks_apply₁₁] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGa, Matrix.of_apply]
  have h11 : N0 = Gb * Gbᴴ := by
    ext a b
    have := hG (Sum.inr a) (Sum.inr b)
    simp only [fromBlocks_apply₂₂] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGb, Matrix.of_apply]
  have h10 : N1 = Gb * Gaᴴ := by
    ext a b
    have := hG (Sum.inr a) (Sum.inl b)
    simp only [fromBlocks_apply₂₁] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGa, hGb, Matrix.of_apply]
  have h01 : -N1 = Ga * Gbᴴ := by
    ext a b
    have := hG (Sum.inl a) (Sum.inr b)
    simp only [fromBlocks_apply₁₂] at this
    rw [this, Matrix.mul_apply]
    simp only [conjTranspose_apply, star_trivial, hGa, hGb, Matrix.of_apply]
  set A := Ga ⊗ₖ P with hA
  set B := Gb ⊗ₖ P with hB
  set Xk := (1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) ⊗ₖ X with hXk
  set A1 := Ga ⊗ₖ (1 : Matrix V V ℝ) with hA1
  have eBB : B * Bᴴ = N0 ⊗ₖ P := by
    rw [hB, conjTranspose_kronecker, hP, ← mul_kronecker_mul, hPP, ← h11]
  have eBXA : B * Xk * Aᴴ = N1 ⊗ₖ X := by
    rw [hB, hXk, hA, conjTranspose_kronecker, hP, ← mul_kronecker_mul, ← mul_kronecker_mul,
      Matrix.mul_one, hPX, hXP, ← h10]
  have eAXB : A * Xkᴴ * Bᴴ = N1 ⊗ₖ X := by
    simp only [hA, hB, hXk, conjTranspose_kronecker, conjTranspose_one, hX, hP]
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one, Matrix.mul_neg, Matrix.neg_mul,
      hPX, hXP, ← h01, neg_kron, kron_neg, neg_neg]
  have eAXXA : A * Xkᴴ * Xk * Aᴴ = N0 ⊗ₖ (Xᴴ * X) := by
    have hXhP : P * Xᴴ = Xᴴ := by rw [hX, Matrix.mul_neg, hPX]
    simp only [hA, hXk, conjTranspose_kronecker, conjTranspose_one, hP]
    rw [← mul_kronecker_mul, ← mul_kronecker_mul, ← mul_kronecker_mul, Matrix.mul_one,
      Matrix.mul_one, hXhP, Matrix.mul_assoc, hXP, ← h00]
  have eA1 : A1 * ((1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) ⊗ₖ (P - Xᴴ * X)) * A1ᴴ =
      N0 ⊗ₖ P - N0 ⊗ₖ (Xᴴ * X) := by
    rw [hA1, conjTranspose_kronecker, conjTranspose_one, ← mul_kronecker_mul,
      ← mul_kronecker_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_one, ← h00,
      sub_eq_add_neg, kronecker_add, kron_neg, ← sub_eq_add_neg]
  have key : N0 ⊗ₖ P + N1 ⊗ₖ X =
      (1 / 2 : ℝ) • ((B + A * Xkᴴ) * (B + A * Xkᴴ)ᴴ) +
        (1 / 2 : ℝ) • (A1 * ((1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) ⊗ₖ (P - Xᴴ * X)) * A1ᴴ) := by
    have e1 : (B + A * Xkᴴ) * (B + A * Xkᴴ)ᴴ =
        B * Bᴴ + B * Xk * Aᴴ + A * Xkᴴ * Bᴴ + A * Xkᴴ * Xk * Aᴴ := by
      simp only [conjTranspose_add, conjTranspose_mul, conjTranspose_conjTranspose,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
    rw [e1, eA1, eBB, eBXA, eAXB, eAXXA]
    module
  rw [key]
  have p1 : ((B + A * Xkᴴ) * (B + A * Xkᴴ)ᴴ).PosSemidef :=
    posSemidef_self_mul_conjTranspose _
  have p2 : (A1 * ((1 : Matrix (L ⊕ L) (L ⊕ L) ℝ) ⊗ₖ (P - Xᴴ * X)) * A1ᴴ).PosSemidef :=
    (PosSemidef.one.kronecker hXc).mul_mul_conjTranspose_same A1
  exact (p1.smul (by norm_num)).add (p2.smul (by norm_num))

/-- **Move 1 for two commuting complex structures** (the two-factor classes FF, FE, with `X`, `Y`
the two Paley operators on `L²₀ ⊗ L²₀`): if `X`, `Y` are skew, commute and square to `−I`, and the
two complex tests `(M₀ ± M₃) + i(M₁ ∓ M₂) ⪰ 0` hold (as realifications), then
`M₀ ⊗ I + M₁ ⊗ X + M₂ ⊗ Y + M₃ ⊗ XY ⪰ 0`. The joint spectral sectors are the ranges of
`P_± = (I ± XY)/2`, on which `Y = ∓X`. -/
theorem move1_two (M0 M1 M2 M3 : Matrix L L ℝ) (X Y : Matrix V V ℝ) (hX : Xᴴ = -X)
    (hY : Yᴴ = -Y) (hXX : X * X = -1) (hYY : Y * Y = -1) (hXY : X * Y = Y * X)
    (hRp : (fromBlocks (M0 + M3) (-(M1 - M2)) (M1 - M2) (M0 + M3)).PosSemidef)
    (hRm : (fromBlocks (M0 - M3) (-(M1 + M2)) (M1 + M2) (M0 - M3)).PosSemidef) :
    (M0 ⊗ₖ (1 : Matrix V V ℝ) + M1 ⊗ₖ X + M2 ⊗ₖ Y + M3 ⊗ₖ (X * Y)).PosSemidef := by
  have hc : Y * X = X * Y := hXY.symm
  have hZh : (X * Y)ᴴ = X * Y := by
    rw [conjTranspose_mul, hX, hY, Matrix.neg_mul, Matrix.mul_neg, neg_neg, hc]
  have hZZ : X * Y * (X * Y) = 1 := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Y X Y, hc, Matrix.mul_assoc X Y Y,
      ← Matrix.mul_assoc X X, hXX, hYY]
    simp
  have hXZ : X * (X * Y) = -Y := by
    rw [← Matrix.mul_assoc, hXX, Matrix.neg_mul, Matrix.one_mul]
  have hZX : X * Y * X = -Y := by
    rw [Matrix.mul_assoc, hc, ← Matrix.mul_assoc, hXX, Matrix.neg_mul, Matrix.one_mul]
  set Z := X * Y with hZ
  set Pp : Matrix V V ℝ := (2 : ℝ)⁻¹ • (1 + Z) with hPp
  set Pm : Matrix V V ℝ := (2 : ℝ)⁻¹ • (1 - Z) with hPm
  have hPph : Ppᴴ = Pp := by
    rw [hPp, conjTranspose_smul, conjTranspose_add, conjTranspose_one, hZh, star_trivial]
  have hPmh : Pmᴴ = Pm := by
    rw [hPm, conjTranspose_smul, conjTranspose_sub, conjTranspose_one, hZh, star_trivial]
  have hPpP : Pp * Pp = Pp := by
    rw [hPp, smul_mul_smul_comm, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, hZZ]
    simp only [Matrix.one_mul, Matrix.mul_one]
    module
  have hPmP : Pm * Pm = Pm := by
    rw [hPm, smul_mul_smul_comm, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hZZ]
    simp only [Matrix.one_mul, Matrix.mul_one]
    module
  -- the sector pieces `X P_±`
  have hXPp : X * Pp * Pp = X * Pp := by rw [Matrix.mul_assoc, hPpP]
  have hXPm : X * Pm * Pm = X * Pm := by rw [Matrix.mul_assoc, hPmP]
  have hXPpX : X * Pp = Pp * X := by
    rw [hPp, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_add, Matrix.add_mul, hXZ, hZX]
    simp only [Matrix.one_mul, Matrix.mul_one]
  have hXPmX : X * Pm = Pm * X := by
    rw [hPm, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sub, Matrix.sub_mul, hXZ, hZX]
    simp only [Matrix.one_mul, Matrix.mul_one]
  have hskp : (X * Pp)ᴴ = -(X * Pp) := by
    rw [conjTranspose_mul, hPph, hX, Matrix.mul_neg, ← hXPpX]
  have hskm : (X * Pm)ᴴ = -(X * Pm) := by
    rw [conjTranspose_mul, hPmh, hX, Matrix.mul_neg, ← hXPmX]
  have hXhX : Xᴴ * X = 1 := by rw [hX, Matrix.neg_mul, hXX, neg_neg]
  have hcp : (Pp - (X * Pp)ᴴ * (X * Pp)).PosSemidef := by
    have : (X * Pp)ᴴ * (X * Pp) = Pp := by
      rw [conjTranspose_mul, hPph, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hXhX, Matrix.one_mul,
        hPpP]
    rw [this, sub_self]
    exact PosSemidef.zero
  have hcm : (Pm - (X * Pm)ᴴ * (X * Pm)).PosSemidef := by
    have : (X * Pm)ᴴ * (X * Pm) = Pm := by
      rw [conjTranspose_mul, hPmh, Matrix.mul_assoc, ← Matrix.mul_assoc Xᴴ, hXhX, Matrix.one_mul,
        hPmP]
    rw [this, sub_self]
    exact PosSemidef.zero
  have Sp := move1_core_proj (M0 + M3) (M1 - M2) Pp (X * Pp) hRp hPph hPpP hskp hXPp hcp
  have Sm := move1_core_proj (M0 - M3) (M1 + M2) Pm (X * Pm) hRm hPmh hPmP hskm hXPm hcm
  -- reassemble
  have i1 : Pp + Pm = 1 := by rw [hPp, hPm]; module
  have i2 : Pp - Pm = Z := by rw [hPp, hPm]; module
  have i3 : X * Pp + X * Pm = X := by rw [← Matrix.mul_add, i1, Matrix.mul_one]
  have i4 : X * Pm - X * Pp = Y := by
    rw [← Matrix.mul_sub, ← neg_sub, i2, Matrix.mul_neg, hXZ, neg_neg]
  have e : M0 ⊗ₖ (1 : Matrix V V ℝ) + M1 ⊗ₖ X + M2 ⊗ₖ Y + M3 ⊗ₖ Z =
      ((M0 + M3) ⊗ₖ Pp + (M1 - M2) ⊗ₖ (X * Pp)) +
        ((M0 - M3) ⊗ₖ Pm + (M1 + M2) ⊗ₖ (X * Pm)) := by
    ext ⟨a, v⟩ ⟨b, u⟩
    have j1 := congrFun (congrFun i1 v) u
    have j2 := congrFun (congrFun i2 v) u
    have j3 := congrFun (congrFun i3 v) u
    have j4 := congrFun (congrFun i4 v) u
    simp only [Matrix.add_apply, Matrix.sub_apply] at j1 j2 j3 j4
    simp only [Matrix.add_apply, Matrix.sub_apply, kroneckerMap_apply]
    rw [← j1, ← j2, ← j3, ← j4]
    ring
  rw [e]
  exact Sp.add Sm

/-- **B11's `hspec` for a two-factor class** (`lem:oct24:mask-schur`(d), FF and FE): for
`T = M₁ ⊗ X + M₂ ⊗ Y + M₃ ⊗ XY` (`𝖥(Φ̂_p) ⊗ 𝖥(Φ̂_q)` or `𝖥(Φ̂_p) ⊗ 𝖤(Φ̂_q)` on `L²₀ ⊗ L²₀`, with
`𝖥(Φ̂) = F_r ⊗ I + F_i ⊗ Φ̂`), `D ⊗ I ± T ⪰ 0` follows from the four finite complex tests
`(D ± M₃) + i(M₁ ∓ M₂) ⪰ 0`, `(D ∓ M₃) + i(−M₁ ± M₂) ⪰ 0` (as realifications `h1`–`h4`); for FE
(`M₁ = 0`, `M₂ = F_r ⊗ E_i`, `M₃ = F_i ⊗ E_i`) these are the paper's `D ± 𝖥(i) ⊗ 𝖤(±i) ⪰ 0`. -/
theorem hspec_two (D M1 M2 M3 : Matrix L L ℝ) (X Y : Matrix V V ℝ) (hX : Xᴴ = -X)
    (hY : Yᴴ = -Y) (hXX : X * X = -1) (hYY : Y * Y = -1) (hXY : X * Y = Y * X)
    (h1 : (fromBlocks (D + M3) (-(M1 - M2)) (M1 - M2) (D + M3)).PosSemidef)
    (h2 : (fromBlocks (D - M3) (-(M1 + M2)) (M1 + M2) (D - M3)).PosSemidef)
    (h3 : (fromBlocks (D + -M3) (-(-M1 - -M2)) (-M1 - -M2) (D + -M3)).PosSemidef)
    (h4 : (fromBlocks (D - -M3) (-(-M1 + -M2)) (-M1 + -M2) (D - -M3)).PosSemidef) :
    (D ⊗ₖ (1 : Matrix V V ℝ) + (M1 ⊗ₖ X + M2 ⊗ₖ Y + M3 ⊗ₖ (X * Y))).PosSemidef ∧
      (D ⊗ₖ (1 : Matrix V V ℝ) - (M1 ⊗ₖ X + M2 ⊗ₖ Y + M3 ⊗ₖ (X * Y))).PosSemidef := by
  constructor
  · have := move1_two D M1 M2 M3 X Y hX hY hXX hYY hXY h1 h2
    convert this using 1
    abel
  · have := move1_two D (-M1) (-M2) (-M3) X Y hX hY hXX hYY hXY h3 h4
    convert this using 1
    simp only [neg_kron]
    abel

end Move1

/-! ## `Φ̂` is a complex structure on `L²₀` -/

section Paley

open Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`Φ̂² = −Π₀`** (`lem:paley-triple`: `Φ̂` is skew with `Φ̂² = −I` on `L²₀`), with
`Π₀ = I − p⁻¹ 𝟙𝟙ᵀ`: `Φ̂_p` is a complex structure on `L²₀` and vanishes on the constants; with
`phiHat_antisymm` (`Φ̂ᵀ = −Φ̂`) these are the hypotheses on `X`, `Y` of `move1_two` on `L²₀`. -/
theorem phiHat_sq (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) :
    phiHat (F := F) * phiHat =
      -(1 - (Fintype.card F : ℝ)⁻¹ • Matrix.of fun _ _ : F => (1 : ℝ)) := by
  have hq : 0 < (Fintype.card F : ℝ) := by exact_mod_cast Fintype.card_pos
  have hs : Real.sqrt (Fintype.card F) * Real.sqrt (Fintype.card F) = (Fintype.card F : ℝ) :=
    Real.mul_self_sqrt hq.le
  ext z z''
  simp only [Matrix.mul_apply, phiHat, Matrix.neg_apply, Matrix.sub_apply, Matrix.one_apply,
    Matrix.smul_apply, Matrix.of_apply, smul_eq_mul, mul_one]
  have e : ∀ z', (quadraticChar F (z' - z) : ℝ) / Real.sqrt (Fintype.card F) *
      ((quadraticChar F (z'' - z') : ℝ) / Real.sqrt (Fintype.card F)) =
      -((Fintype.card F : ℝ)⁻¹ * ((quadraticChar F (z - z') : ℝ) *
        (quadraticChar F (z'' - z') : ℝ))) := by
    intro z'
    rw [chi_swap h3 z' z, div_mul_div_comm, hs]
    push_cast
    ring
  rw [sum_congr rfl fun z' _ => e z', sum_neg_distrib, ← mul_sum, sum_chi_mul_chi_R hF h3]
  split_ifs with h
  · field_simp
  · simp

end Paley

end Sarkozy.OpsFeature

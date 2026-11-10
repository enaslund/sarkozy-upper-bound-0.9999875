module

public import Sarkozy.BlockAdapter.UpperMain

/-!
# The six upper root caps of a band, and their anchor certificates

`paper/sections/25_upper_reference.tex`: (V1) of `lem:upper-reference-rp`;
`lem:record:monotone-endpoint`, `cert:upper-root-caps` (LL20 below `2⁵²`);
`lem:upper-completed-root`, `cert:upper-completed-root` (LL20 from `2⁵²`);
`26_upper_comparison.tex`, `lem:record:domain`(i),(ii) with formula (F6) and
`cert:upper-band-inputs`(a) (the five class-three nonroot chamber cuts).

B6's field `PC.hUC : ∀ k, UpperRootCaps k` asks, on each of the 310 upper bands, for six chamber
cut certificates (`BlockAdapter.UpperBandRootCap`): the two-layer chamber cuts of `G_{Lf}` for
`f = L, F, E` (the paper's LL20, FL21, EL21) at the ordinary caps, and the one-layer ones (LL10,
FL11, EL11) at the reserved caps.

* `Cap`: the six cuts; `Cap.field`, `capD k c` (the record cap `d`, `UpperRecords.bandOrd`,
  `bandRes`).
* `CapPrime c g B p`: B6's per-prime bound `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` (`ChamberCutCap`) for the
  cut `c`.
* **`AnchorCap c p₀ g B`**: this bound at **every** class-three prime `p ≥ p₀`. This is the form of
  the conclusions of `lem:record:monotone-endpoint`, `lem:upper-completed-root` and
  `lem:record:domain`(i) at an evaluation point `p₀`: one statement, uniform in the prime.
* `CapBand k c d`: B6's `UpperBandRootCap` for the cut `c` on band `k`.

Proved here:
* `chamberCutCap_mono`, `AnchorCap.mono`: the bound is monotone in `g`, `B` and in the anchor;
* **`capBand_of_anchor`**: an anchor certificate at `p₀ ≤ X_k`, with `0 ≤ g`, `0 ≤ B`, `g² < X_k`
  and the inflation `g exp(B L_k/(X_k log X_k)) ≤ d`, gives the band certificate. This is the use
  of `lem:record:domain`(ii) (and of the block statements of `lem:record:monotone-endpoint`,
  `lem:upper-completed-root`) that B6's field encodes: the block cap is assembled from the
  per-prime bounds by `BlockAdapter.upperBandLemma_of_rest`;
* **`upperRootCaps_of_capBands`**: the six band certificates give `UpperRootCaps k`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.PartV Sarkozy.FiveType.TwoCoord Sarkozy.PartVLaws.FieldGraphs
  Sarkozy.BlockAdapter

/-! ## The six caps -/

/-- **The six chamber cuts of a band** (`subsec:upper-nonroot`, `cert:upper-root-caps`): LL20,
FL21, EL21 (two layers, the ordinary inputs `d_L`, `d_F`, `d_E`) and LL10, FL11, EL11 (one layer,
the reserved inputs). -/
inductive Cap
  | LL20 | FL21 | EL21 | LL10 | FL11 | EL11
  deriving DecidableEq

instance : Fintype Cap where
  elems := {.LL20, .FL21, .EL21, .LL10, .FL11, .EL11}
  complete c := by cases c <;> decide

/-- The field type `f` of the chamber cut of `G_{Lf}`. -/
def Cap.field : Cap → FieldTy
  | .LL20 => .L | .FL21 => .F | .EL21 => .E | .LL10 => .L | .FL11 => .F | .EL11 => .E

/-- The record cap `d` of the cut on band `k`: `bandOrd k f` for the two-layer cuts, `bandRes k f`
for the one-layer cuts (`upper_dense_refined.json`, `inputs`, `reserved_inputs`). -/
def capD (k : Fin 310) : Cap → ℚ
  | .LL20 => (UpperRecords.bandOrd k .L).d
  | .FL21 => (UpperRecords.bandOrd k .F).d
  | .EL21 => (UpperRecords.bandOrd k .E).d
  | .LL10 => (UpperRecords.bandRes k .L).d
  | .FL11 => (UpperRecords.bandRes k .F).d
  | .EL11 => (UpperRecords.bandRes k .E).d

/-- A row of a cap table: the evaluation point `p₀` and the constants `(g, B_top)`. -/
structure CapRow where
  anchor : ℚ
  g : ℚ
  B : ℚ

/-- **B6's per-prime bound for the cut `c`** (`ChamberCutCap`): `-g p^{-1/2} ⪯ A_p ⪯ 1 + B/p` for
the chamber cut operator `A_p` of `G_{Lf}` at `p` (two layers `Λ = ℤ/2`, or one layer
`Λ = Unit`). -/
def CapPrime : Cap → ℝ → ℝ → (p : ℕ) → [Fact p.Prime] → Prop
  | .LL20, g, B, p, _ => ChamberCutCap .L (ZMod 2) g B p
  | .FL21, g, B, p, _ => ChamberCutCap .F (ZMod 2) g B p
  | .EL21, g, B, p, _ => ChamberCutCap .E (ZMod 2) g B p
  | .LL10, g, B, p, _ => ChamberCutCap .L Unit g B p
  | .FL11, g, B, p, _ => ChamberCutCap .F Unit g B p
  | .EL11, g, B, p, _ => ChamberCutCap .E Unit g B p

/-- **B6's band certificate for the cut `c`** (`UpperBandRootCap`). -/
def CapBand (k : Fin 310) : Cap → ℝ → Prop
  | .LL20, d => UpperBandRootCap k .L (ZMod 2) d
  | .FL21, d => UpperBandRootCap k .F (ZMod 2) d
  | .EL21, d => UpperBandRootCap k .E (ZMod 2) d
  | .LL10, d => UpperBandRootCap k .L Unit d
  | .FL11, d => UpperBandRootCap k .F Unit d
  | .EL11, d => UpperBandRootCap k .E Unit d

/-- **An anchor certificate** (the conclusion of `lem:record:monotone-endpoint`,
`lem:upper-completed-root` or `lem:record:domain`(i) at the evaluation point `p₀`): the per-prime
bound with the constants `(g, B)` at every class-three prime `p ≥ p₀`. Uniform in the prime. -/
def AnchorCap (c : Cap) (p₀ g B : ℝ) : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → p₀ ≤ p → CapPrime c g B p

/-! ## Monotonicity -/

/-- `ChamberCutCap` is monotone in `g` and in `B`. -/
theorem chamberCutCap_mono {f : FieldTy} {Λ : Type} [Fintype Λ] [DecidableEq Λ] {g B g' B' : ℝ}
    {p : ℕ} [Fact p.Prime] (hg : g ≤ g') (hB : B ≤ B') (h : ChamberCutCap f Λ g B p) :
    ChamberCutCap f Λ g' B' p := by
  intro hne v
  obtain ⟨h1, h2⟩ := h hne v
  have hr : 0 ≤ (√(p : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hv : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have hp : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  constructor
  · have : -(g' * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤ -(g * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (neg_le_neg (mul_le_mul_of_nonneg_right hg hr)) hv
    linarith
  · have : (1 + B / p) * ‖v‖ ^ 2 ≤ (1 + B' / p) * ‖v‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (add_le_add_right (div_le_div_of_nonneg_right hB hp) 1) hv
    linarith

/-- `CapPrime` is monotone in `g` and in `B`. -/
theorem CapPrime.mono {c : Cap} {g B g' B' : ℝ} {p : ℕ} [Fact p.Prime] (hg : g ≤ g') (hB : B ≤ B')
    (h : CapPrime c g B p) : CapPrime c g' B' p := by
  cases c <;> exact chamberCutCap_mono hg hB h

/-- **An anchor certificate serves every later anchor, with larger constants** (the monotone use of
`lem:record:domain`: a certificate at `p₀` holds at every evaluation point `p₁ ≥ p₀`). -/
theorem AnchorCap.mono {c : Cap} {p₀ g B p₁ g' B' : ℝ} (h : AnchorCap c p₀ g B) (hp : p₀ ≤ p₁)
    (hg : g ≤ g') (hB : B ≤ B') : AnchorCap c p₁ g' B' := fun p _ h3 hp₁ =>
  (h p h3 (hp.trans hp₁)).mono hg hB

/-! ## From anchors to bands -/

/-- The band certificate of B6 for one chamber cut, from the per-prime bounds at the band's primes
and the band arithmetic, with `X = X_k`. -/
theorem upperBandRootCap_of {k : Fin 310} {f : FieldTy} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {d g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < ((bandOf k).1 : ℝ))
    (hgX : g * (√((bandOf k).1 : ℝ))⁻¹ < 1)
    (hinf : g * Real.exp (B * (UpperRecords.CompletionData.record k).budget /
      (((bandOf k).1 : ℝ) * Real.log ((bandOf k).1 : ℝ))) ≤ d)
    (hp : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → ((bandOf k).1 : ℝ) ≤ p → ChamberCutCap f Λ g B p) :
    UpperBandRootCap k f Λ d :=
  ⟨g, B, (bandOf k).1, hg, hB, hX, le_rfl, hgX, hinf,
    fun p _ h3 h1 _ => hp p h3 (by exact_mod_cast h1)⟩

/-- `g X^{-1/2} < 1` from `g² < X` (a rational check). -/
theorem mul_inv_sqrt_lt_one {g X : ℝ} (hg : 0 ≤ g) (hX : 0 < X) (h : g ^ 2 < X) :
    g * (√X)⁻¹ < 1 := by
  have hs : 0 < √X := Real.sqrt_pos.mpr hX
  rw [← div_eq_mul_inv, div_lt_one hs]
  calc g = √(g ^ 2) := (Real.sqrt_sq hg).symm
    _ < √X := Real.sqrt_lt_sqrt (sq_nonneg g) h

/-- **The band certificate from an anchor certificate** (`lem:record:domain`(ii) with
`lem:record:monotone-endpoint` / `lem:upper-completed-root`, block cap assembled by B6): if the
cut has an anchor certificate `(g, B)` at `p₀ ≤ X_k`, with `0 ≤ g`, `0 ≤ B`, `g² < X_k` and the
inflation `g exp(B L_k/(X_k log X_k)) ≤ d`, then B6's band certificate holds at the cap `d`. -/
theorem capBand_of_anchor {k : Fin 310} {c : Cap} {p₀ g B d : ℝ} (h : AnchorCap c p₀ g B)
    (hp₀ : p₀ ≤ (bandOf k).1) (hg : 0 ≤ g) (hB : 0 ≤ B) (hX : 1 < ((bandOf k).1 : ℝ))
    (hgX : g ^ 2 < (bandOf k).1)
    (hinf : g * Real.exp (B * (UpperRecords.CompletionData.record k).budget /
      (((bandOf k).1 : ℝ) * Real.log ((bandOf k).1 : ℝ))) ≤ d) :
    CapBand k c d := by
  have hgX' := mul_inv_sqrt_lt_one hg (by linarith) hgX
  have hp : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → ((bandOf k).1 : ℝ) ≤ p → CapPrime c g B p :=
    fun p _ h3 h1 => h p h3 (hp₀.trans h1)
  cases c
  · exact upperBandRootCap_of hg hB hX hgX' hinf hp
  · exact upperBandRootCap_of hg hB hX hgX' hinf hp
  · exact upperBandRootCap_of hg hB hX hgX' hinf hp
  · exact upperBandRootCap_of hg hB hX hgX' hinf hp
  · exact upperBandRootCap_of hg hB hX hgX' hinf hp
  · exact upperBandRootCap_of hg hB hX hgX' hinf hp

/-- **B6's `UpperRootCaps k` from the six band certificates** at the record caps. -/
theorem upperRootCaps_of_capBands {k : Fin 310} (h : ∀ c, CapBand k c (capD k c)) :
    UpperRootCaps k := by
  intro f
  cases f
  · exact ⟨h .LL20, h .LL10⟩
  · exact ⟨h .FL21, h .FL11⟩
  · exact ⟨h .EL21, h .EL11⟩

end Sarkozy.UpperCapsPaper

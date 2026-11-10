module

public import Sarkozy.EnvelopeSteps.PaperAveraging
public import Sarkozy.Envelopes.OrbitCoupon

@[expose] public section

/-!
# Step 3 of `thm:envelopes`(i) with the orbit coupon, at the paper's data (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 3 ("`[D_ω]_ω = ∑_C c(C)[C]_ω`
with placed couplings … By `lem:orbit-coupon`,
`Y^Ñ[[D_ω]_ω] ≤ Y^{Ñ₀}[[D_ω]_ω] + (M(D_{(ω)}) R_err − M_ω e^{tU} tδ_s + o(1)) C_X Y`");
`lem:orbit-coupon`(i), (ii) and their proofs.

B11's `step3_paper` has the coupling expansion and the per-coupling bounds as inputs, but not the
orbit improvement; W2's `orbit_coupon` has the improvement on an abstract vector space, without
remainders. Here they are joined at the paper's energies `Y^Ñ = paperEN`, `Y^{Ñ₀} = paperEN0`:

* `place_eq_of_kern`, `place_expand`: the placement depends only on the kernel, so a kernel
  expansion `kern(D) = ∑ c(C) kern(C)` (the coupling expansion of `lem:oct24:mask-schur`(a), see
  `Coupling.lean`) gives `[D]_ω = ∑ c(C) [C]_ω`;
* **`orbit_coupon_rem`**: W2's `orbit_coupon` with per-coupling remainders `r_C ≥ 0`:
  `|Δ K| ≤ M R − M_h(K) s + ∑ |c(C)| r_C`;
* `orbitAvg_invariant`: if `R_{h*}[C]_ω = [hC]_ω` (`lem:reflection-averaging`(f), (g), as stated in
  `lem:orbit-coupon`), the orbit averages `½([C]_ω + [hC]_ω)` are `R_h`-invariant;
* **`step3_orbit`**: the field `step3` of B11's `DegreeOps` / `paperDegreeOps` for one selection, in
  exactly its form `Y^Ñ[[D]] ≤ Y^{Ñ₀}[[D]] + (M_ω R_err − M_{h,ω} e^{tU} tδ + z) C_X Y + r₃`, with
  `M_ω = M(D)` (`couplingMass`), `M_{h,ω} = M_h(K)` (`orbitMass`), `r₃ = ∑ |c(C)| r_C`, from:
  - the kernel expansion of `D_ω`;
  - the per-coupling bound `|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ (R_err + z') C_X Y + r_C`
    (`lem:bracket-energy`, (E1), last bound, for the admissible probability law `[C]_ω`);
  - the improved bound `≤ (R_err − e^{tU} tδ + z') C_X Y + r_C` for the `R_h`-invariant orbit
    averages (the category `e_s` of the proof of `lem:orbit-coupon`(i));
  - `R_{h*}[C]_ω = [hC]_ω`, and `M(D) z' ≤ z`;
* **`step3_orbit_two`**: the same with `lem:orbit-coupon`(ii) (no fold record: both reflections
  `R₁`, `R₃` on the disjoint categories `e₀`, `e₁`), `M_{h,ω} = M₁(K) + M₃(K)`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.Envelopes Sarkozy.EnvelopeSteps Sarkozy.RecordExpansion

/-! ## The orbit coupon with remainders -/

section Orbit

variable {ι : Type*} [Fintype ι]

/-- **`lem:orbit-coupon`(i) with remainders.** For an involution `h` of the couplings, a linear
error `Δ`, `|Δ [C]| ≤ R + r_C` for every coupling and `|Δ(½([C] + [hC]))| ≤ R − s + r_C` for every
orbit average: `|Δ K| ≤ M R − M_h(K) s + ∑_C |c(C)| r_C` for `K = ∑ c(C) [C]`. -/
theorem orbit_coupon_rem {V : Type*} [AddCommGroup V] [Module ℝ V] {h : ι → ι}
    (hh : ∀ C, h (h C) = C) (c : ι → ℝ) (e : ι → V) (Δ : V →ₗ[ℝ] ℝ) {R s : ℝ} (r : ι → ℝ)
    (hR : ∀ C, |Δ (e C)| ≤ R + r C) (hs : ∀ C, |Δ ((1 / 2 : ℝ) • (e C + e (h C)))| ≤ R - s + r C) :
    |Δ (∑ C, c C • e C)| ≤ couplingMass c * R - orbitMass h c * s + ∑ C, |c C| * r C := by
  set b := orbitPart h c
  have hsplit : ∑ C, c C • e C =
      ∑ C, b C • ((1 / 2 : ℝ) • (e C + e (h C))) + ∑ C, (c C - b C) • e C := by
    rw [← sum_orbitPart_avg hh c e, ← sum_add_distrib]
    refine sum_congr rfl fun C _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [hsplit, map_add, map_sum, map_sum]
  have hb : ∀ C, |b C| ≤ |c C| := fun C => by
    have := abs_sub_orbitPart h c C
    have h0 := abs_nonneg (c C - b C)
    linarith
  have h1 : |∑ C, Δ (b C • ((1 / 2 : ℝ) • (e C + e (h C))))| ≤ ∑ C, |b C| * (R - s + r C) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun C _ => ?_)
    rw [map_smul, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hs C) (abs_nonneg _)
  have h2 : |∑ C, Δ ((c C - b C) • e C)| ≤ ∑ C, (|c C| - |b C|) * (R + r C) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun C _ => ?_)
    rw [map_smul, smul_eq_mul, abs_mul, abs_sub_orbitPart]
    have : 0 ≤ |c C| - |b C| := by linarith [hb C]
    exact mul_le_mul_of_nonneg_left (hR C) this
  have e3 : ∑ C, |b C| * (R - s + r C) + ∑ C, (|c C| - |b C|) * (R + r C) =
      couplingMass c * R - orbitMass h c * s + ∑ C, |c C| * r C := by
    have e4 : ∑ C, |b C| * (R - s + r C) + ∑ C, (|c C| - |b C|) * (R + r C) =
        ∑ C, (|c C| * R - |b C| * s + |c C| * r C) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun C _ => by ring
    rw [e4, sum_add_distrib, sum_sub_distrib, ← sum_mul, ← sum_mul, sum_abs_orbitPart]
    rfl
  calc _ ≤ |∑ C, Δ (b C • ((1 / 2 : ℝ) • (e C + e (h C))))| +
        |∑ C, Δ ((c C - b C) • e C)| := abs_add_le _ _
    _ ≤ ∑ C, |b C| * (R - s + r C) + ∑ C, (|c C| - |b C|) * (R + r C) := add_le_add h1 h2
    _ = _ := e3

/-- A linear error bounded by `R + r_C` on every coupling is bounded by `M R + ∑ |c| r` on `K`. -/
theorem abs_le_couplingMass_rem {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ι → ℝ)
    (e : ι → V) (Δ : V →ₗ[ℝ] ℝ) {R : ℝ} (r : ι → ℝ) (hR : ∀ C, |Δ (e C)| ≤ R + r C) :
    |Δ (∑ C, c C • e C)| ≤ couplingMass c * R + ∑ C, |c C| * r C := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [couplingMass, sum_mul, ← sum_add_distrib]
  refine sum_le_sum fun C _ => ?_
  rw [abs_mul, ← mul_add]
  exact mul_le_mul_of_nonneg_left (hR C) (abs_nonneg _)

/-- **`lem:orbit-coupon`(ii) with remainders.** Two reflections `h₁`, `h₃` on the disjoint
categories `Δ₀`, `Δ₁` of the error, the other categories `Δ_r` unchanged:
`|(Δ₀ + Δ₁ + Δ_r) K| ≤ M (R₀ + R₁ + R_r) − (M₁(K) + M₃(K)) s + ∑ |c| (r₀ + r₁ + r_r)`. -/
theorem orbit_coupon_two_rem {V : Type*} [AddCommGroup V] [Module ℝ V] {h₁ h₃ : ι → ι}
    (hh₁ : ∀ C, h₁ (h₁ C) = C) (hh₃ : ∀ C, h₃ (h₃ C) = C) (c : ι → ℝ) (e : ι → V)
    (Δ₀ Δ₁ Δr : V →ₗ[ℝ] ℝ) {R₀ R₁ Rr s : ℝ} (r₀ r₁ rr : ι → ℝ)
    (hR₀ : ∀ C, |Δ₀ (e C)| ≤ R₀ + r₀ C)
    (hs₀ : ∀ C, |Δ₀ ((1 / 2 : ℝ) • (e C + e (h₁ C)))| ≤ R₀ - s + r₀ C)
    (hR₁ : ∀ C, |Δ₁ (e C)| ≤ R₁ + r₁ C)
    (hs₁ : ∀ C, |Δ₁ ((1 / 2 : ℝ) • (e C + e (h₃ C)))| ≤ R₁ - s + r₁ C)
    (hRr : ∀ C, |Δr (e C)| ≤ Rr + rr C) :
    |(Δ₀ + Δ₁ + Δr) (∑ C, c C • e C)| ≤
      couplingMass c * (R₀ + R₁ + Rr) - (orbitMass h₁ c + orbitMass h₃ c) * s +
        ∑ C, |c C| * (r₀ C + r₁ C + rr C) := by
  have h0 := orbit_coupon_rem hh₁ c e Δ₀ r₀ hR₀ hs₀
  have h1 := orbit_coupon_rem hh₃ c e Δ₁ r₁ hR₁ hs₁
  have h2 := abs_le_couplingMass_rem c e Δr rr hRr
  have e5 : ∑ C, |c C| * (r₀ C + r₁ C + rr C) =
      ∑ C, |c C| * r₀ C + ∑ C, |c C| * r₁ C + ∑ C, |c C| * rr C := by
    rw [← sum_add_distrib, ← sum_add_distrib]; exact sum_congr rfl fun C _ => by ring
  rw [LinearMap.add_apply, LinearMap.add_apply, e5]
  calc _ ≤ |Δ₀ (∑ C, c C • e C)| + |Δ₁ (∑ C, c C • e C)| + |Δr (∑ C, c C • e C)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ _ := by linarith

omit [Fintype ι] in
/-- **The orbit averages are `R_h`-invariant** when `R_{h*}[C] = [hC]` for an involution `h` of
the couplings (`lem:orbit-coupon`, "then `R_{h*}[C]_ω = [hC]_ω` for a permutation `C ↦ hC`"). -/
theorem orbitAvg_invariant {V X : Type*} [DecidableEq V] {α : V ≃ V} {h : ι → ι}
    (hh : ∀ C, h (h C) = C) (e : ι → ((V → X) → ℝ) →ₗ[ℝ] ℝ)
    (hpush : ∀ C, slotPush α (e C) = e (h C)) (C : ι) :
    slotPush α ((1 / 2 : ℝ) • (e C + e (h C))) = (1 / 2 : ℝ) • (e C + e (h C)) := by
  unfold slotPush
  rw [LinearMap.smul_comp, LinearMap.add_comp]
  change (1 / 2 : ℝ) • (slotPush α (e C) + slotPush α (e (h C))) = _
  rw [hpush, hpush, hh, add_comm]

end Orbit

/-! ## The placement depends only on the kernel -/

section Kernel

variable {O : Type*} [Fintype O] [DecidableEq O] {V X : Type*} [Fintype V] [DecidableEq V]

/-- **The placement depends only on the kernel** relative to `m`. -/
theorem place_eq_of_kern (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X))
    {K K' : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (h : ∀ x y, kern m K x y = kern m K' x y) :
    place c m φ K = place c m φ K' := by
  unfold place
  congr 1
  funext q
  exact h q.1 q.2

/-- **A kernel expansion is placed term by term**: `kern(D) = ∑ c(C) kern(C)` gives
`[D]_ω = ∑ c(C) [C]_ω`. -/
theorem place_expand (c : ReflectionCut V) (m : O → ℝ) (φ : O → (c.Half → X)) {ι : Type*}
    [Fintype ι] (coef : ι → ℝ) (Cop : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (hD : ∀ x y, kern m Dop x y = ∑ i, coef i * kern m (Cop i) x y) :
    place c m φ Dop = ∑ i, coef i • place c m φ (Cop i) := by
  have hk : ∀ x y, kern m Dop x y = kern m (∑ i, coef i • Cop i) x y := by
    intro x y
    rw [hD]
    unfold kern
    rw [LinearMap.sum_apply, Finset.sum_apply, mul_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [place_eq_of_kern c m φ hk]
  change placeL c m φ (∑ i, coef i • Cop i) = _
  rw [map_sum]
  exact sum_congr rfl fun i _ => map_smul _ _ _

end Kernel

/-! ## Step 3 at the paper's data -/

section Paper

open Sarkozy.TheoremCBlock Sarkozy.BlockFrame

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

/-- The error `κ ↦ Y^Ñ[κ] − Y^{Ñ₀}[κ]` of the outside bracket, as a linear functional. -/
noncomputable def errN (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) :
    (((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ :=
  paperEN D L A S - paperEN0 D L A S

omit [DecidableEq P] in
/-- **Step 3 of `thm:envelopes` at the paper's data, with the orbit coupon**
(`lem:orbit-coupon`(i)): the field `step3` of B11's `DegreeOps` for one selection. Inputs:

* `hD`: the coupling expansion `kern(D_ω) = ∑_C c(C) kern(C)` of the envelope relative to `m_ω`
  (`lem:oct24:mask-schur`(a); `Coupling.lean`);
* `herr`: `|Y^Ñ[[C]] − Y^{Ñ₀}[[C]]| ≤ (R_err + z') C_X Y + r_C` for every placed coupling
  (`lem:bracket-energy`, (E1) last bound);
* `hpush`: `R_{h*}[C]_ω = [hC]_ω` for the involution `C ↦ hC` (`lem:reflection-averaging`(f), (g));
* `hsym`: the improved bound `≤ (R_err − e^{tU} tδ + z') C_X Y + r_C` for every `R_h`-invariant
  orbit average (the category `e_s` in the proof of `lem:orbit-coupon`(i));
* `M(D) z' ≤ z`, `C_X Y ≥ 0`.

Then `Y^Ñ[[D]] ≤ Y^{Ñ₀}[[D]] + (M(D) R_err − M_h(D) e^{tU} tδ + z) C_X Y + ∑ |c(C)| r_C`. -/
theorem step3_orbit (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) {O : Type}
    [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    {ι : Type*} [Fintype ι] (coef : ι → ℝ) (Cop : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hD : ∀ x y, kern m Dop x y = ∑ i, coef i * kern m (Cop i) x y)
    (hR : ZMod 6) (hC : ι → ι) (hh : ∀ i, hC (hC i) = i)
    (hpush : ∀ i, slotPush (slotREquiv hR) (place reservedCut m φ (Cop i)) =
      place reservedCut m φ (Cop (hC i)))
    {Rerr z' z tU tδ CX Y : ℝ} (r : ι → ℝ)
    (herr : ∀ i, |paperEN D L A S (place reservedCut m φ (Cop i)) -
      paperEN0 D L A S (place reservedCut m φ (Cop i))| ≤ (Rerr + z') * CX * Y + r i)
    (hsym : ∀ κ, slotPush (slotREquiv hR) κ = κ →
      ∀ i, κ = (1 / 2 : ℝ) • (place reservedCut m φ (Cop i) + place reservedCut m φ (Cop (hC i))) →
      |paperEN D L A S κ - paperEN0 D L A S κ| ≤
        (Rerr - Real.exp tU * tδ + z') * CX * Y + r i)
    (hz : couplingMass coef * z' ≤ z) (hCY : 0 ≤ CX * Y) :
    paperEN D L A S (place reservedCut m φ Dop) ≤
      paperEN0 D L A S (place reservedCut m φ Dop) +
        (couplingMass coef * Rerr - orbitMass hC coef * Real.exp tU * tδ + z) * CX * Y +
          ∑ i, |coef i| * r i := by
  set e : ι → _ := fun i => place reservedCut m φ (Cop i) with he
  have hK : place reservedCut m φ Dop = ∑ i, coef i • e i := place_expand reservedCut m φ coef Cop
    Dop hD
  have hb := orbit_coupon_rem (R := (Rerr + z') * CX * Y) (s := Real.exp tU * tδ * (CX * Y)) hh
    coef e (errN D L A S) r (fun i => herr i) (fun i => by
      have h1 := hsym _ (orbitAvg_invariant hh e hpush i) i rfl
      change |(paperEN D L A S - paperEN0 D L A S) _| ≤ _
      rw [LinearMap.sub_apply]
      calc _ ≤ (Rerr - Real.exp tU * tδ + z') * CX * Y + r i := h1
        _ = (Rerr + z') * CX * Y - Real.exp tU * tδ * (CX * Y) + r i := by ring)
  have hM0 : 0 ≤ couplingMass coef := sum_nonneg fun i _ => abs_nonneg _
  have hdiff : paperEN D L A S (place reservedCut m φ Dop) -
      paperEN0 D L A S (place reservedCut m φ Dop) = errN D L A S (∑ i, coef i • e i) := by
    rw [← hK]
    rfl
  have hle := (le_abs_self _).trans hb
  rw [← hdiff] at hle
  have hzz : couplingMass coef * z' * (CX * Y) ≤ z * (CX * Y) := mul_le_mul_of_nonneg_right hz hCY
  nlinarith

omit [DecidableEq P] in
/-- **Step 3 with `lem:orbit-coupon`(ii)** (a selection without fold records: both reflections
`R₁`, `R₃` fix its placements, and they are used on the disjoint categories `e₀`, `e₁` of the
error). The error `Y^Ñ − Y^{Ñ₀}` is split as `Δ₀ + Δ₁ + Δ_r` (the categories `e₀`, `e₁` and the
rest, `lem:sharp-first`); per coupling `|Δ_j[C]| ≤ R_j C_X Y + r_j(C)`, with the improved bound
`(R_j − e^{tU} tδ) C_X Y + r_j(C)` on the `R_{2j+1}`-invariant orbit averages. Then
`Y^Ñ[[D]] ≤ Y^{Ñ₀}[[D]] + (M(D) R_err − (M₁ + M₃) e^{tU} tδ + z) C_X Y + r₃` with
`R_err = R₀ + R₁ + R_r` and `M(D) z' ≤ z` for the error weights `z'`. -/
theorem step3_orbit_two (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) {O : Type}
    [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    {ι : Type*} [Fintype ι] (coef : ι → ℝ) (Cop : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ))
    (Dop : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hD : ∀ x y, kern m Dop x y = ∑ i, coef i * kern m (Cop i) x y)
    (h₁ h₃ : ι → ι) (hh₁ : ∀ i, h₁ (h₁ i) = i) (hh₃ : ∀ i, h₃ (h₃ i) = i)
    (hpush₁ : ∀ i, slotPush (slotREquiv 1) (place reservedCut m φ (Cop i)) =
      place reservedCut m φ (Cop (h₁ i)))
    (hpush₃ : ∀ i, slotPush (slotREquiv 3) (place reservedCut m φ (Cop i)) =
      place reservedCut m φ (Cop (h₃ i)))
    (Δ₀ Δ₁ Δr : (((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ)
    (hsplit : paperEN D L A S - paperEN0 D L A S = Δ₀ + Δ₁ + Δr)
    {R₀ R₁ Rr z' z tU tδ CX Y : ℝ} (r₀ r₁ rr : ι → ℝ)
    (hR₀ : ∀ i, |Δ₀ (place reservedCut m φ (Cop i))| ≤ (R₀ + z') * CX * Y + r₀ i)
    (hs₀ : ∀ κ, slotPush (slotREquiv 1) κ = κ →
      ∀ i, κ = (1 / 2 : ℝ) • (place reservedCut m φ (Cop i) + place reservedCut m φ (Cop (h₁ i))) →
      |Δ₀ κ| ≤ (R₀ - Real.exp tU * tδ + z') * CX * Y + r₀ i)
    (hR₁ : ∀ i, |Δ₁ (place reservedCut m φ (Cop i))| ≤ R₁ * CX * Y + r₁ i)
    (hs₁ : ∀ κ, slotPush (slotREquiv 3) κ = κ →
      ∀ i, κ = (1 / 2 : ℝ) • (place reservedCut m φ (Cop i) + place reservedCut m φ (Cop (h₃ i))) →
      |Δ₁ κ| ≤ (R₁ - Real.exp tU * tδ) * CX * Y + r₁ i)
    (hRr : ∀ i, |Δr (place reservedCut m φ (Cop i))| ≤ Rr * CX * Y + rr i)
    (hz : couplingMass coef * z' ≤ z) (hCY : 0 ≤ CX * Y) :
    paperEN D L A S (place reservedCut m φ Dop) ≤
      paperEN0 D L A S (place reservedCut m φ Dop) +
        (couplingMass coef * (R₀ + R₁ + Rr) -
          (orbitMass h₁ coef + orbitMass h₃ coef) * Real.exp tU * tδ + z) * CX * Y +
          ∑ i, |coef i| * (r₀ i + r₁ i + rr i) := by
  set e : ι → _ := fun i => place reservedCut m φ (Cop i) with he
  have hK : place reservedCut m φ Dop = ∑ i, coef i • e i := place_expand reservedCut m φ coef Cop
    Dop hD
  have hb := orbit_coupon_two_rem (R₀ := (R₀ + z') * CX * Y) (R₁ := R₁ * CX * Y)
    (Rr := Rr * CX * Y) (s := Real.exp tU * tδ * (CX * Y)) hh₁ hh₃ coef e Δ₀ Δ₁ Δr r₀ r₁ rr
    hR₀ (fun i => by
      have h1 := hs₀ _ (orbitAvg_invariant hh₁ e hpush₁ i) i rfl
      calc _ ≤ (R₀ - Real.exp tU * tδ + z') * CX * Y + r₀ i := h1
        _ = (R₀ + z') * CX * Y - Real.exp tU * tδ * (CX * Y) + r₀ i := by ring)
    hR₁ (fun i => by
      have h1 := hs₁ _ (orbitAvg_invariant hh₃ e hpush₃ i) i rfl
      calc _ ≤ (R₁ - Real.exp tU * tδ) * CX * Y + r₁ i := h1
        _ = R₁ * CX * Y - Real.exp tU * tδ * (CX * Y) + r₁ i := by ring) hRr
  have hdiff : paperEN D L A S (place reservedCut m φ Dop) -
      paperEN0 D L A S (place reservedCut m φ Dop) = (Δ₀ + Δ₁ + Δr) (∑ i, coef i • e i) := by
    rw [← hK, ← hsplit]
    rfl
  have hle := (le_abs_self _).trans hb
  rw [← hdiff] at hle
  have hzz : couplingMass coef * z' * (CX * Y) ≤ z * (CX * Y) := mul_le_mul_of_nonneg_right hz hCY
  nlinarith

end Paper

end Sarkozy.OpsSteps

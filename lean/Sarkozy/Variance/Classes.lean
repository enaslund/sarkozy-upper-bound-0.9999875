module

public import Sarkozy.Variance.Gain
public import Sarkozy.Variance.Matching
public import Sarkozy.Variance.Restoration

/-!
# The eligible variance classes (`cor:var-classes`(i)–(iii))

`paper/sections/22_variance.tex`, `cor:var-classes`: `lem:var-gain` applies to the aligned
fold assignments with the restoration bound `l₀` and `κ_F`, to the two aligned matching
assignments with `l₀ - C ε_X` and `κ_E`, and to the `2^k` matching embeddings with
`2^{1-k} l₀ - C ε_X` and `κ_E`. These are the compositions of the earlier results:

* `var_classes_fold`: **(i)**: `lem:record:restoration` (`restoration`, at the fold chamber
  `ϑ`) gives (Res) for the fold product `Π_X = Diag_ϑ(λ)`; with (Cen) at `ι`
  (`lem:record:old-f-marginal`(d), hypothesis) `lem:var-gain`(a) gives
  `Y[J_ι(m_F)] ≥ (l̄_F - z) C_X Y`, `l̄_F = (l₀/C - κ_F)/(1 - κ_F)`.
* `var_classes_aligned_matching`: **(ii)**: `lem:record:paired-e-joint`(b)
  (`paired_e_joint_b_aligned`, at `ϑ₀`) gives (Res) for the two aligned matching assignments with
  `l₀ - C ε_X`; with (Cen) at `ι` (`lem:record:paired-e-bridge`(b), hypothesis),
  `½(Y[J_0] + Y[J_1]) ≥ (l̄_E^al - z) C_X Y`, `l̄_E^al = (l₀/C - ε_X - κ_E)/(1 - κ_E)`.
* `var_classes_embeddings`: **(iii)**: the same with `paired_e_joint_b_all` over the `2^k`
  embeddings, `l̄_E = (2^{1-k} l₀/C - ε_X - κ_E)/(1 - κ_E)`.

The gain formulas and the comparison `[l̄_E^al - R]_+ ≥ 2^{k-1}[l̄_E - R]_+` are in `Gain.lean`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion

namespace Sarkozy.Variance

section Classes

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`cor:var-classes`(ii)**: the two aligned matching assignments. (Res) is
`lem:record:paired-e-joint`(b) at the chamber cut `ϑ₀` (its hypotheses: the polarization order,
(E1) for the merge products, the restoration bounds `≥ (l₀ - z₁) Y` of the two fold products);
(Cen) is the centred norm `κ_E` of the aligned embeddings at `ι`
(`lem:record:paired-e-bridge`(b)); (E1) bounds their selected diagonals. Conclusion:
`½(Y[J_ι(m_0)] + Y[J_ι(m_1)]) ≥ (l̄_E^al - z) C_X Y` with
`l̄_E^al = (l₀/C - ε_X - κ_E)/(1 - κ_E)` and `z = (z₁ + z ε_X C + κ_E z₂)/(1 - κ_E)`. -/
theorem var_classes_aligned_matching (ϑ₀ ι : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO₀ : ∀ j, j ≠ j₀ → ϑ₀.Positive (O j)) (hOι : ∀ j, j ≠ j₀ → ι.Positive (O j))
    (F : (∀ b, X b) → ℝ) {E0 E1 Mg0 Mg1 F1 F2 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ}
    (horder : ϑ₀.Below (F1 + F2) ((E0 + Mg0) + (E1 + Mg1)))
    {Yμ CX C ε l₀ z₁ z z₂ κ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C) (hε : 0 ≤ ε)
    (hz : 0 ≤ z) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hF1 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F1 F) (hF2 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F2 F)
    (hMg0 : energyAt O j₀ Mg0 F ≤ (1 + z) * ε * CX * Yμ)
    (hMg1 : energyAt O j₀ Mg1 F ≤ (1 + z) * ε * CX * Yμ)
    {m0 m1 : (ι.Half → X j₀) → ℝ} (hm0 : ∀ x, 0 ≤ m0 x) (hm1 : ∀ x, 0 ≤ m1 x)
    (hm0p : 0 < ∑ x, m0 x) (hm1p : 0 < ∑ x, m1 x)
    (hs0 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E0 G H = ι.form E0 H G)
    (hs1 : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form E1 G H = ι.form E1 H G)
    (hp0 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E0 G 1 = ∑ x, m0 x * G x)
    (hp1 : ∀ G : (ι.Half → X j₀) → ℝ, ι.form E1 G 1 = ∑ x, m1 x * G x)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hcen0 : CentredNormLe ι E0 m0 κ)
    (hcen1 : CentredNormLe ι E1 m1 κ)
    (hD0 : energyAt O j₀ (ι.diagonalLaw m0) F ≤ (1 + z₂) * CX * Yμ)
    (hD1 : energyAt O j₀ (ι.diagonalLaw m1) F ≤ (1 + z₂) * CX * Yμ) :
    ((l₀ / C - ε - κ) / (1 - κ) - (z₁ + z * ε * C + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      (energyAt O j₀ (indepLaw ι m0) F + energyAt O j₀ (indepLaw ι m1) F) / 2 := by
  have hCpos : 0 < C := by linarith
  have hb := paired_e_joint_b_aligned ϑ₀ O j₀ hO₀ F horder hY hC hε hz hF1 hF2 hMg0 hMg1
  -- `lem:var-gain`(a) on the two aligned assignments, indexed by `Bool`
  let P : Bool → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ := fun s => if s then E1 else E0
  let m : Bool → (ι.Half → X j₀) → ℝ := fun s => if s then m1 else m0
  have hsumE : (∑ s ∈ (univ : Finset Bool), energyAt O j₀ (P s) F) / (univ : Finset Bool).card =
      (energyAt O j₀ E0 F + energyAt O j₀ E1 F) / 2 := by
    simp [P, add_comm]
  have hsumJ : (∑ s ∈ (univ : Finset Bool), energyAt O j₀ (indepLaw ι (m s)) F) /
      (univ : Finset Bool).card =
      (energyAt O j₀ (indepLaw ι m0) F + energyAt O j₀ (indepLaw ι m1) F) / 2 := by
    simp [m, add_comm]
  have ha := var_gain_a ι O j₀ hOι F univ univ_nonempty P m
    (fun s _ => by cases s <;> simp [m, hm0, hm1])
    (fun s _ => by cases s <;> simp [m, hm0p, hm1p])
    (fun s _ => by cases s <;> simp [P, hs0, hs1])
    (fun s _ => by cases s <;> simp [P, m, hp0, hp1])
    hκ0 hκ1 (fun s _ => by cases s <;> simp [P, m, hcen0, hcen1])
    (l₀ := l₀ - C * ε) (z₁ := z₁ + z * ε * C) hY hCX hC (by positivity) hz₂
    (by rw [hsumE]; linarith [hb])
    (fun s _ => by cases s <;> simp [m, hD0, hD1])
  rw [hsumJ, var_classes_aligned_gain hCpos.ne'] at ha
  exact ha

/-- **`cor:var-classes`(i)**: an aligned fold assignment `(F_j)_{𝔅∈X}`. (Res) is the
restoration bound `Y[Π_X] ≥ (l₀ - z₁) Y` of `lem:record:restoration` (the conclusion of
`restoration`, with `l₀` its `restorationL0` value; the maximum with `0` is allowed since
`Y[Π_X] ≥ 0`); (Cen) is the centred norm `κ_F` of `Π_X` at `ι` relative to its actual half
marginal `m_F` (`lem:record:old-f-marginal`(d), hypothesis); (E1) bounds `Y[Diag_ι(m_F)]`.
Conclusion: `Y[J_ι(m_F)] ≥ (l̄_F - (z₁ + κ_F z₂)/(1 - κ_F)) C_X Y`. -/
theorem var_classes_fold (ι : ReflectionCut V) (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hOι : ∀ j, j ≠ j₀ → ι.Positive (O j)) (F : (∀ b, X b) → ℝ)
    {Pfold : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ} {mF : (ι.Half → X j₀) → ℝ} (hm : ∀ x, 0 ≤ mF x)
    (hmp : 0 < ∑ x, mF x) (hs : ∀ G H : (ι.Half → X j₀) → ℝ, ι.form Pfold G H = ι.form Pfold H G)
    (hp : ∀ G : (ι.Half → X j₀) → ℝ, ι.form Pfold G 1 = ∑ x, mF x * G x)
    {κ : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hcen : CentredNormLe ι Pfold mF κ)
    {Yμ CX C l₀ z₁ z₂ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C) (hz₁ : 0 ≤ z₁)
    (hz₂ : 0 ≤ z₂) (hRes : (l₀ - z₁) * Yμ ≤ energyAt O j₀ Pfold F)
    (hD : energyAt O j₀ (ι.diagonalLaw mF) F ≤ (1 + z₂) * CX * Yμ) :
    (gainBar l₀ C κ - (z₁ + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      energyAt O j₀ (indepLaw ι mF) F := by
  have ha := var_gain_a ι O j₀ hOι F (univ : Finset Unit) univ_nonempty (fun _ => Pfold)
    (fun _ => mF) (fun _ _ => hm) (fun _ _ => hmp) (fun _ _ => hs) (fun _ _ => hp) hκ0 hκ1
    (fun _ _ => hcen) hY hCX hC hz₁ hz₂ (by simpa using hRes) (fun _ _ => hD)
  simpa using ha

/-- **`cor:var-classes`(iii)**: the `2^k` matching embeddings `E_s`, `s ∈ S`. (Res) is
`lem:record:paired-e-joint`(b), second bound (`paired_e_joint_b_all`, at `ϑ₀`), with
`2^{1-k} l₀ - C ε_X`; (Cen) is the centred norm `κ_E` of every embedding at `ι`
(`lem:record:paired-e-bridge`(b), hypothesis). Conclusion:
`avg_s Y[J_ι(m_s)] ≥ (l̄_E - z) C_X Y` with `l̄_E = (2^{1-k} l₀/C - ε_X - κ_E)/(1 - κ_E)`. -/
theorem var_classes_embeddings {σ : Type*} (ϑ₀ ι : ReflectionCut V)
    (O : ∀ j, ((V → X j) → ℝ) →ₗ[ℝ] ℝ) (j₀ : J)
    (hO₀ : ∀ j, j ≠ j₀ → ϑ₀.Positive (O j)) (hOι : ∀ j, j ≠ j₀ → ι.Positive (O j))
    (F : (∀ b, X b) → ℝ) (S : Finset σ) (hSne : S.Nonempty) (k : ℕ) (hS : S.card = 2 ^ k)
    (E : σ → ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ) {Mg F1 F2 : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ}
    (horder : ϑ₀.Below (F1 + F2) (∑ s ∈ S, E s + Mg))
    {Yμ CX C ε l₀ z₁ z z₂ κ : ℝ} (hY : 0 ≤ Yμ) (hCX : 1 ≤ CX) (hC : CX ≤ C) (hε : 0 ≤ ε)
    (hz : 0 ≤ z) (hz₁ : 0 ≤ z₁) (hz₂ : 0 ≤ z₂)
    (hF1 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F1 F) (hF2 : (l₀ - z₁) * Yμ ≤ energyAt O j₀ F2 F)
    (hMg : energyAt O j₀ Mg F ≤ (1 + z) * (2 ^ k * ε) * CX * Yμ)
    (m : σ → (ι.Half → X j₀) → ℝ) (hm : ∀ s ∈ S, ∀ x, 0 ≤ m s x)
    (hmp : ∀ s ∈ S, 0 < ∑ x, m s x)
    (hs : ∀ s ∈ S, ∀ G H : (ι.Half → X j₀) → ℝ, ι.form (E s) G H = ι.form (E s) H G)
    (hp : ∀ s ∈ S, ∀ G : (ι.Half → X j₀) → ℝ, ι.form (E s) G 1 = ∑ x, m s x * G x)
    (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (hcen : ∀ s ∈ S, CentredNormLe ι (E s) (m s) κ)
    (hD : ∀ s ∈ S, energyAt O j₀ (ι.diagonalLaw (m s)) F ≤ (1 + z₂) * CX * Yμ) :
    ((2 * (2 : ℝ)⁻¹ ^ k * l₀ / C - ε - κ) / (1 - κ) -
        (2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C + κ * z₂) / (1 - κ)) * CX * Yμ ≤
      (∑ s ∈ S, energyAt O j₀ (indepLaw ι (m s)) F) / S.card := by
  have hCpos : 0 < C := by linarith
  have hb := paired_e_joint_b_all ϑ₀ O j₀ hO₀ F S k E horder hY hC hε hz hF1 hF2 hMg
  have hcard : (S.card : ℝ) = 2 ^ k := by rw [hS]; push_cast; rfl
  have hz' : 0 ≤ 2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C := by positivity
  have ha := var_gain_a ι O j₀ hOι F S hSne E m hm hmp hs hp hκ0 hκ1 hcen
    (l₀ := 2 * (2 : ℝ)⁻¹ ^ k * l₀ - C * ε) (z₁ := 2 * (2 : ℝ)⁻¹ ^ k * z₁ + z * ε * C)
    hY hCX hC hz' hz₂ (by rw [hcard]; linarith [hb]) hD
  rw [var_classes_aligned_gain hCpos.ne'] at ha
  exact ha

end Classes

end Sarkozy.Variance

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The constants of `eq:signed-constants` as polynomials in nonnegative atoms (SD2)

`paper/sections/21_middle_records.tex`, `eq:signed-constants` (with `lem:actual-features`(d) for
`Γ_A`).

Every constant of `eq:signed-constants` that enters the gates of the signed record
(`c_col`, `e_o`, `e_sg`, `c_+`, and `Γ_A`) is a polynomial with nonnegative coefficients in the
nonnegative **atoms** (`Atoms`):
* `q`, `r`, `e = e₀`, `u = e₀/q`, `Γ` (the frame constant), the square roots `s₁ = √(1 + q)`,
  `s₃ = √3`, `s_a = √(3 + 2t²)`;
* the reciprocals `j₁ = 1/(1 - q)`, `j₂ = 1/(1 - 2q)`, `j_e = 1/(1 - e₀)`, `j₁₀ = 1/(1 - 10q)`
  (`= 1/h_c`), `j₁₄ = 1/(1 - 14q)` (`= 1/h₀`), and `k₃ = 1/√(1 - e₀)`.

This is `lem:majorant` made concrete: every remainder carrying `q` is written as an admissible
coefficient (`c_g/q = e₀ u j_e²`, `D_g/q = (2 + e₀) u j_e²`, `M_c/q = (20 + (1 + 10q) u) j₁₀ j_e`),
and the result is **monotone in every atom** (`Atoms.Le`, `eoPoly_mono`, `esgPoly_mono`,
`cpPoly_mono`, `ccolPoly_mono`, `gamPoly_mono`). The forms are stated over any field, so that the
same expressions are evaluated exactly in `ℚ` (`Numbers.lean`) and used in `ℝ` (`cast` lemmas).

The identification with the paper's literal formulas is in `Paper.lean`.
-/

namespace Sarkozy.SignedDecomp

/-- **The atoms** of the constants of `eq:signed-constants` (see the module docstring). -/
structure Atoms (K : Type) where
  q : K
  r : K
  e : K
  u : K
  Γ : K
  s1 : K
  s3 : K
  sa : K
  j1 : K
  j2 : K
  je : K
  j10 : K
  j14 : K
  k3 : K

section Forms

variable {K : Type} [Field K] (A : Atoms K)

/-- `c_g/q = e₀²/((1 - e₀)² q) = e₀ u j_e²`. -/
def cgq : K := A.e * A.u * A.je ^ 2

/-- `D_g/q = (2e₀ + e₀²)/((1 - e₀)² q) = (2 + e₀) u j_e²`. -/
def dgq : K := (2 + A.e) * A.u * A.je ^ 2

/-- **`c_col`** (`eq:signed-constants`):
`c^ν_col/(1 - e₀) + 17[2e₀/(1 - e₀)^{3/2} + e₀²/(1 - e₀)²]`, with
`c^ν_col = (56119/10000) Γ₅ + (2/Z)(12r + q) + 288q/(1 - q)`,
`Γ₅ = 1 + 2(r + q)/(1 - q) + 2q(1 + r)/((1 - q)(1 - 2q))`. -/
def ccolPoly : K :=
  (56119 / 10000 * (1 + 2 * (A.r + A.q) * A.j1 + 2 * A.q * (1 + A.r) * (A.j1 * A.j2)) +
      2 * (A.j1 * A.j2) * (12 * A.r + A.q) + 288 * A.q * A.j1) * A.je +
    17 * (2 * A.e * (A.je * A.k3) + A.e ^ 2 * A.je ^ 2)

/-- `r_o = 2/(Z(1 - e₀)) + c_col + c_g/q + (D_g/q) Γ r`. -/
def roPoly (c : K) : K := 2 * (A.j1 * A.j2 * A.je) + c + cgq A + dgq A * A.Γ * A.r

/-- **`e_o = r_o + n_o`**, `n_o = (14/h₀)(Γ + r_o r) r`. -/
def eoPoly (c : K) : K := roPoly A c + 14 * A.j14 * (A.Γ + roPoly A c * A.r) * A.r

/-- `n_c = (18/Z + 3)/(1 - e₀) + (1 + 2q) c_g/q`. -/
def ncPoly : K := (18 * (A.j1 * A.j2) + 3) * A.je + (1 + 2 * A.q) * cgq A

/-- `c_c = √3 Γ + (n_c + (D_g/q) √3 Γ r) r`. -/
def ccPoly : K := A.s3 * A.Γ + (ncPoly A + dgq A * A.s3 * A.Γ * A.r) * A.r

/-- `M_c/q = (2η_c + (1 + η_c) e₀)/(q h_c (1 - e₀)) = (20 + (1 + 10q) u) j₁₀ j_e`. -/
def mcqPoly : K := (20 + (1 + 10 * A.q) * A.u) * (A.j10 * A.je)

/-- `E_c = 10 c_c r/h_c + (2M_c/q)(c_c r/h_c + 2ϱ₀₂)`, `ϱ₀₂ = r√(1 + q)/(1 - q)`. -/
def ecPoly : K :=
  10 * ccPoly A * A.r * A.j10 + 2 * mcqPoly A * (ccPoly A * A.r * A.j10 + 2 * (A.r * A.s1 * A.j1))

/-- **`c_+ = √3 Γ + (n_c + (D_g/q) √3 Γ r + E_c) r`**. -/
def cpPoly : K := A.s3 * A.Γ + (ncPoly A + dgq A * A.s3 * A.Γ * A.r + ecPoly A) * A.r

/-- **`e_sg`** at `t = 127/500`, `k_col = 9/4`:
`((18 - 12t)/Z + k_col)/(1 - e₀) + (1 + 2q) c_g/q + (D_g/q) √(3 + 2t²) Γ r + (1 + t) E_c`, with
`18 - 12t = 1869/125` and `1 + t = 627/500`. -/
def esgPoly : K :=
  (1869 / 125 * (A.j1 * A.j2) + 9 / 4) * A.je + (1 + 2 * A.q) * cgq A +
    dgq A * A.sa * A.Γ * A.r + 627 / 500 * ecPoly A

/-- **`Γ_A`** (`lem:actual-features`(d)) with `s₁ = √(1 + q)`, `s₂ = √(1 + 4q/(1 - 4q)²)`,
`j₁ = 1/(1 - q)`, `j₄ = 1/(1 - 4q)`:
`1 + r s₁ j₁ + 2 q j₁ s₂ + qr(1 + 4q) j₁ j₄ + 2qr j₁ + 4q² j₁ j₄`. -/
def gamPoly (q r s1 s2 j1 j4 : K) : K :=
  1 + r * s1 * j1 + 2 * (q * j1 * s2) + q * r * (1 + 4 * q) * (j1 * j4) + 2 * q * r * j1 +
    4 * q ^ 2 * (j1 * j4)

end Forms

/-! ## Monotonicity in the atoms -/

/-- `A ≤ B` atomwise, with `A` nonnegative. -/
def Atoms.Le (A B : Atoms ℝ) : Prop :=
  (0 ≤ A.q ∧ A.q ≤ B.q) ∧ (0 ≤ A.r ∧ A.r ≤ B.r) ∧ (0 ≤ A.e ∧ A.e ≤ B.e) ∧
    (0 ≤ A.u ∧ A.u ≤ B.u) ∧ (0 ≤ A.Γ ∧ A.Γ ≤ B.Γ) ∧ (0 ≤ A.s1 ∧ A.s1 ≤ B.s1) ∧
    (0 ≤ A.s3 ∧ A.s3 ≤ B.s3) ∧ (0 ≤ A.sa ∧ A.sa ≤ B.sa) ∧ (0 ≤ A.j1 ∧ A.j1 ≤ B.j1) ∧
    (0 ≤ A.j2 ∧ A.j2 ≤ B.j2) ∧ (0 ≤ A.je ∧ A.je ≤ B.je) ∧ (0 ≤ A.j10 ∧ A.j10 ≤ B.j10) ∧
    (0 ≤ A.j14 ∧ A.j14 ≤ B.j14) ∧ (0 ≤ A.k3 ∧ A.k3 ≤ B.k3)

section Mono

variable {A B : Atoms ℝ}

theorem Atoms.Le.self (h : A.Le B) : B.Le B := by
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  exact ⟨⟨hq0.trans hq, le_rfl⟩, ⟨hr0.trans hr, le_rfl⟩, ⟨he0.trans he, le_rfl⟩,
    ⟨hu0.trans hu, le_rfl⟩,
    ⟨hΓ0.trans hΓ, le_rfl⟩, ⟨hs10.trans hs1, le_rfl⟩, ⟨hs30.trans hs3, le_rfl⟩,
    ⟨hsa0.trans hsa, le_rfl⟩, ⟨hj10.trans hj1, le_rfl⟩, ⟨hj20.trans hj2, le_rfl⟩,
    ⟨hje0.trans hje, le_rfl⟩, ⟨hj100.trans hj10', le_rfl⟩, ⟨hj140.trans hj14, le_rfl⟩,
    ⟨hk30.trans hk3, le_rfl⟩⟩

theorem cgq_mono (h : A.Le B) : cgq A ≤ cgq B := by
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold cgq; gcongr

theorem dgq_mono (h : A.Le B) : dgq A ≤ dgq B := by
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold dgq; gcongr

theorem cgq_nonneg (h : A.Le B) : 0 ≤ cgq A := by
  obtain ⟨-, -, ⟨he0, -⟩, ⟨hu0, -⟩, -⟩ := h
  unfold cgq; positivity

theorem dgq_nonneg (h : A.Le B) : 0 ≤ dgq A := by
  obtain ⟨-, -, ⟨he0, -⟩, ⟨hu0, -⟩, -⟩ := h
  unfold dgq; positivity

theorem ccolPoly_mono (h : A.Le B) : ccolPoly A ≤ ccolPoly B := by
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold ccolPoly; gcongr

theorem ccolPoly_nonneg (h : A.Le B) : 0 ≤ ccolPoly A := by
  obtain ⟨⟨hq0, -⟩, ⟨hr0, -⟩, ⟨he0, -⟩, -, -, -, -, -, ⟨h10, -⟩, ⟨h20, -⟩, ⟨hje0, -⟩, -, -,
    ⟨hk0, -⟩⟩ := h
  unfold ccolPoly; positivity

theorem roPoly_mono (h : A.Le B) {c c' : ℝ} (hc : c ≤ c') : roPoly A c ≤ roPoly B c' := by
  have := dgq_nonneg h.self
  have h1 := cgq_mono h
  have h2 := dgq_mono h
  have h3 := dgq_nonneg h
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold roPoly; gcongr

theorem roPoly_nonneg (h : A.Le B) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ roPoly A c := by
  have h1 := cgq_nonneg h
  have h3 := dgq_nonneg h
  obtain ⟨-, ⟨hr0, -⟩, -, -, ⟨hΓ0, -⟩, -, -, -, ⟨h10, -⟩, ⟨h20, -⟩, ⟨hje0, -⟩, -⟩ := h
  unfold roPoly; positivity

theorem eoPoly_mono (h : A.Le B) {c c' : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ c') :
    eoPoly A c ≤ eoPoly B c' := by
  have := roPoly_nonneg h.self (hc0.trans hc)
  have h1 := roPoly_mono h hc
  have h2 := roPoly_nonneg h hc0
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold eoPoly; gcongr

theorem eoPoly_nonneg (h : A.Le B) {c : ℝ} (hc : 0 ≤ c) : 0 ≤ eoPoly A c := by
  have h2 := roPoly_nonneg h hc
  obtain ⟨-, ⟨hr0, -⟩, -, -, ⟨hΓ0, -⟩, -, -, -, -, -, -, -, ⟨h140, -⟩, -⟩ := h
  unfold eoPoly; positivity

theorem ncPoly_mono (h : A.Le B) : ncPoly A ≤ ncPoly B := by
  have h1 := cgq_mono h
  have h3 := cgq_nonneg h
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold ncPoly; gcongr

theorem ncPoly_nonneg (h : A.Le B) : 0 ≤ ncPoly A := by
  have h3 := cgq_nonneg h
  obtain ⟨⟨hq0, -⟩, -, -, -, -, -, -, -, ⟨h10, -⟩, ⟨h20, -⟩, ⟨hje0, -⟩, -⟩ := h
  unfold ncPoly; positivity

theorem ccPoly_mono (h : A.Le B) : ccPoly A ≤ ccPoly B := by
  have := dgq_nonneg h.self
  have := ncPoly_nonneg h.self
  have h1 := ncPoly_mono h
  have h2 := dgq_mono h
  have h3 := dgq_nonneg h
  have h4 := ncPoly_nonneg h
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold ccPoly; gcongr

theorem ccPoly_nonneg (h : A.Le B) : 0 ≤ ccPoly A := by
  have h3 := dgq_nonneg h
  have h4 := ncPoly_nonneg h
  obtain ⟨-, ⟨hr0, -⟩, -, -, ⟨hΓ0, -⟩, -, ⟨hs0, -⟩, -⟩ := h
  unfold ccPoly; positivity

theorem mcqPoly_mono (h : A.Le B) : mcqPoly A ≤ mcqPoly B := by
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold mcqPoly; gcongr

theorem mcqPoly_nonneg (h : A.Le B) : 0 ≤ mcqPoly A := by
  obtain ⟨⟨hq0, -⟩, -, -, ⟨hu0, -⟩, -, -, -, -, -, -, ⟨hje0, -⟩, ⟨h100, -⟩, -⟩ := h
  unfold mcqPoly; positivity

theorem ecPoly_mono (h : A.Le B) : ecPoly A ≤ ecPoly B := by
  have := ccPoly_nonneg h.self
  have := mcqPoly_nonneg h.self
  have h1 := ccPoly_mono h
  have h2 := ccPoly_nonneg h
  have h3 := mcqPoly_mono h
  have h4 := mcqPoly_nonneg h
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold ecPoly; gcongr

theorem ecPoly_nonneg (h : A.Le B) : 0 ≤ ecPoly A := by
  have h2 := ccPoly_nonneg h
  have h4 := mcqPoly_nonneg h
  obtain ⟨-, ⟨hr0, -⟩, -, -, -, ⟨hs0, -⟩, -, -, ⟨h10, -⟩, -, -, ⟨h100, -⟩, -⟩ := h
  unfold ecPoly; positivity

theorem cpPoly_mono (h : A.Le B) : cpPoly A ≤ cpPoly B := by
  have := dgq_nonneg h.self
  have := ncPoly_nonneg h.self
  have := ecPoly_nonneg h.self
  have h1 := ncPoly_mono h
  have h2 := dgq_mono h
  have h3 := dgq_nonneg h
  have h4 := ncPoly_nonneg h
  have h5 := ecPoly_mono h
  have h6 := ecPoly_nonneg h
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold cpPoly; gcongr

theorem cpPoly_nonneg (h : A.Le B) : 0 ≤ cpPoly A := by
  have h3 := dgq_nonneg h
  have h4 := ncPoly_nonneg h
  have h6 := ecPoly_nonneg h
  obtain ⟨-, ⟨hr0, -⟩, -, -, ⟨hΓ0, -⟩, -, ⟨hs0, -⟩, -⟩ := h
  unfold cpPoly; positivity

theorem esgPoly_mono (h : A.Le B) : esgPoly A ≤ esgPoly B := by
  have := dgq_nonneg h.self
  have h1 := cgq_mono h
  have h2 := dgq_mono h
  have h3 := dgq_nonneg h
  have h4 := cgq_nonneg h
  have h5 := ecPoly_mono h
  have h6 := ecPoly_nonneg h
  obtain ⟨⟨hq0, hq⟩, ⟨hr0, hr⟩, ⟨he0, he⟩, ⟨hu0, hu⟩, ⟨hΓ0, hΓ⟩, ⟨hs10, hs1⟩, ⟨hs30, hs3⟩,
    ⟨hsa0, hsa⟩, ⟨hj10, hj1⟩, ⟨hj20, hj2⟩, ⟨hje0, hje⟩, ⟨hj100, hj10'⟩, ⟨hj140, hj14⟩,
    ⟨hk30, hk3⟩⟩ := h
  have := hq0.trans hq; have := hr0.trans hr; have := he0.trans he; have := hu0.trans hu
  have := hΓ0.trans hΓ; have := hs10.trans hs1; have := hs30.trans hs3; have := hsa0.trans hsa
  have := hj10.trans hj1; have := hj20.trans hj2; have := hje0.trans hje
  have := hj100.trans hj10'; have := hj140.trans hj14; have := hk30.trans hk3
  unfold esgPoly; gcongr

theorem esgPoly_nonneg (h : A.Le B) : 0 ≤ esgPoly A := by
  have h3 := dgq_nonneg h
  have h4 := cgq_nonneg h
  have h6 := ecPoly_nonneg h
  obtain ⟨⟨hq0, -⟩, ⟨hr0, -⟩, -, -, ⟨hΓ0, -⟩, -, -, ⟨hs0, -⟩, ⟨h10, -⟩, ⟨h20, -⟩, ⟨hje0, -⟩, -⟩ := h
  unfold esgPoly; positivity

end Mono

theorem gamPoly_mono {q r s1 s2 j1 j4 q' r' s1' s2' j1' j4' : ℝ} (hq0 : 0 ≤ q) (hq : q ≤ q')
    (hr0 : 0 ≤ r) (hr : r ≤ r') (hs10 : 0 ≤ s1) (hs1 : s1 ≤ s1') (hs20 : 0 ≤ s2) (hs2 : s2 ≤ s2')
    (hj10 : 0 ≤ j1) (hj1 : j1 ≤ j1') (hj40 : 0 ≤ j4) (hj4 : j4 ≤ j4') :
    gamPoly q r s1 s2 j1 j4 ≤ gamPoly q' r' s1' s2' j1' j4' := by
  have := hq0.trans hq; have := hr0.trans hr; have := hs10.trans hs1; have := hs20.trans hs2
  have := hj10.trans hj1; have := hj40.trans hj4
  unfold gamPoly; gcongr

/-! ## Casting from `ℚ` -/

/-- The atoms of `ℚ` as atoms of `ℝ`. -/
def Atoms.cast (A : Atoms ℚ) : Atoms ℝ :=
  ⟨A.q, A.r, A.e, A.u, A.Γ, A.s1, A.s3, A.sa, A.j1, A.j2, A.je, A.j10, A.j14, A.k3⟩

theorem ccolPoly_cast (A : Atoms ℚ) : ((ccolPoly A : ℚ) : ℝ) = ccolPoly A.cast := by
  simp only [ccolPoly, Atoms.cast]; push_cast; ring

theorem eoPoly_cast (A : Atoms ℚ) (c : ℚ) : ((eoPoly A c : ℚ) : ℝ) = eoPoly A.cast c := by
  simp only [eoPoly, roPoly, cgq, dgq, Atoms.cast]; push_cast; ring

theorem esgPoly_cast (A : Atoms ℚ) : ((esgPoly A : ℚ) : ℝ) = esgPoly A.cast := by
  simp only [esgPoly, ecPoly, ccPoly, ncPoly, mcqPoly, cgq, dgq, Atoms.cast]; push_cast; ring

theorem cpPoly_cast (A : Atoms ℚ) : ((cpPoly A : ℚ) : ℝ) = cpPoly A.cast := by
  simp only [cpPoly, ecPoly, ccPoly, ncPoly, mcqPoly, cgq, dgq, Atoms.cast]; push_cast; ring

theorem gamPoly_cast (q r s1 s2 j1 j4 : ℚ) :
    ((gamPoly q r s1 s2 j1 j4 : ℚ) : ℝ) = gamPoly (q : ℝ) r s1 s2 j1 j4 := by
  simp only [gamPoly]; push_cast; ring

end Sarkozy.SignedDecomp

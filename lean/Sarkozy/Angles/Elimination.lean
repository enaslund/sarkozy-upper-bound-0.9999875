module

public import Sarkozy.Angles.Kassabov

/-!
# Kassabov–Schur elimination: the abstract claim of `lem:mid:allpin`

`lem:mid:allpin` (`paper/sections/13_cuts_correlations.tex`) bounds the cosines of a family of
subspaces `V[𝒴]`, indexed by sets `𝒴` of parts, with `V[𝒴] ∩ V[𝒴'] = V[𝒴 ∪ 𝒴']`. It puts
`c_𝒴(β, β') = cos∠(V[𝒴 ∪ {β}], V[𝒴 ∪ {β'}])` and compares it with numbers `e_𝒴(β, β')`
obtained by Gaussian elimination, which satisfy
`e_{𝒴 ∪ {γ}}(β, β') = F(e_𝒴(β, β'), e_𝒴(β, γ), e_𝒴(β', γ))` with Kassabov's right side
`F(a, b, c) = (a + b c) / √((1 - b²)(1 - c²))` (`kassabovBound`).

* `kassabovBound_mono`: `F` is nondecreasing in each argument on `[0, 1)`;
  `kassabovBound_nonneg`.
* `normalized_schur_step`: the normalized Schur-complement step. For a symmetric matrix `N`
  with unit diagonal, eliminating `γ` and normalizing gives the entry `-F(-N_{ββ'}, -N_{βγ},
  -N_{β'γ})`; the same holds for a matrix with positive diagonal, normalized first
  (`normalized_schur_step'`, conjugation by a positive diagonal matrix).
* `allpin_claim`: the Claim, by induction on `𝒴`, for abstract subspaces `V[𝒴]` and abstract
  numbers `e_𝒴(β, β') < 1` that bound the cosines at `𝒴 = ∅` and dominate the recursion.
  The Claim's induction step is `kassabov_inf`, used in its form with upper bounds, so the
  monotonicity of `F` is not needed in it.
* `allpin_claim_pair`: the case `𝒴 = 𝒫 ∖ {β, β'}` used at the end of the proof.

The numbers `e` of the paper (Gaussian elimination of `I - Ē`, realized here through
Gram–Schmidt residuals) are constructed in `Sarkozy.Angles.Gram`. `Sarkozy.Angles.AllPin`,
`Sarkozy.Angles.AllPinNorm` and `Sarkozy.Angles.AllPinSub` complete the lemma.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

/-- The right side of Kassabov's inequality: `F(a, b, c) = (a + b c) / √((1 - b²)(1 - c²))`. -/
noncomputable def kassabovBound (a b c : ℝ) : ℝ := (a + b * c) / √((1 - b ^ 2) * (1 - c ^ 2))

theorem kassabovBound_nonneg {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    0 ≤ kassabovBound a b c :=
  div_nonneg (by positivity) (Real.sqrt_nonneg _)

/-- **Monotonicity of the right side** on `[0, 1)`: `F` is nondecreasing in each argument. -/
theorem kassabovBound_mono {a b c a' b' c' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (haa : a ≤ a') (hbb : b ≤ b') (hcc : c ≤ c') (hb' : b' < 1) (hc' : c' < 1) :
    kassabovBound a b c ≤ kassabovBound a' b' c' := by
  unfold kassabovBound
  have hb'0 : 0 ≤ b' := hb.trans hbb
  have hc'0 : 0 ≤ c' := hc.trans hcc
  have hd' : 0 < (1 - b' ^ 2) * (1 - c' ^ 2) := mul_pos (by nlinarith) (by nlinarith)
  have hdd : (1 - b' ^ 2) * (1 - c' ^ 2) ≤ (1 - b ^ 2) * (1 - c ^ 2) := by
    have h1 : 1 - b' ^ 2 ≤ 1 - b ^ 2 := by nlinarith
    have h2 : 1 - c' ^ 2 ≤ 1 - c ^ 2 := by nlinarith
    exact mul_le_mul h1 h2 (by nlinarith) (by nlinarith)
  have hnum : a + b * c ≤ a' + b' * c' := by nlinarith [mul_le_mul hbb hcc hc hb'0]
  exact div_le_div₀ (add_nonneg (ha.trans haa) (mul_nonneg hb'0 hc'0)) hnum
    (Real.sqrt_pos.mpr hd') (Real.sqrt_le_sqrt hdd)

/-- **The normalized Schur-complement step**, for a symmetric matrix with unit diagonal:
eliminating `γ` gives `N'_{xy} = N_{xy} - N_{xγ} N_{γy}`, so `N'_{xx} = 1 - N_{xγ}²`, and the
normalized entry `N'_{xy} / √(N'_{xx} N'_{yy})` is `-F(-N_{xy}, -N_{xγ}, -N_{yγ})`. With
`e = -N` this is the recursion `e' = F(e_{xy}, e_{xγ}, e_{yγ})` of `lem:mid:allpin`. -/
theorem normalized_schur_step {P : Type*} (N : Matrix P P ℝ) (hsymm : N.IsSymm)
    (hdiag : ∀ x, N x x = 1) (x y γ : P) :
    (N x y - N x γ * N γ y / N γ γ) /
        √((N x x - N x γ * N γ x / N γ γ) * (N y y - N y γ * N γ y / N γ γ)) =
      -kassabovBound (-N x y) (-N x γ) (-N y γ) := by
  have hs : ∀ a b, N a b = N b a := fun a b => by
    rw [← Matrix.transpose_apply N b a, hsymm.eq]
  unfold kassabovBound
  rw [hdiag x, hdiag y, hdiag γ, hs γ y, hs γ x]
  simp only [div_one]
  rw [show (1 - N x γ * N x γ) * (1 - N y γ * N y γ) = (1 - (-N x γ) ^ 2) * (1 - (-N y γ) ^ 2)
    by ring, ← neg_div]
  congr 1
  ring

/-- The real-number identity behind `normalized_schur_step'`: with `p, q, g > 0` the diagonal
entries, `(a - b c / g) / √((p - b² / g)(q - c² / g)) = -F(-a/√(pq), -b/√(pg), -c/√(qg))`. -/
theorem schur_normalize_aux {a b c p q g : ℝ} (hp : 0 < p) (hq : 0 < q) (hg : 0 < g)
    (hb : (b / √(p * g)) ^ 2 < 1) (hc : (c / √(q * g)) ^ 2 < 1) :
    (a - b * c / g) / √((p - b * b / g) * (q - c * c / g)) =
      -kassabovBound (-(a / √(p * q))) (-(b / √(p * g))) (-(c / √(q * g))) := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ p = s ^ 2 :=
    ⟨√p, Real.sqrt_pos.mpr hp, (Real.sq_sqrt hp.le).symm⟩
  obtain ⟨t, ht, rfl⟩ : ∃ t, 0 < t ∧ q = t ^ 2 :=
    ⟨√q, Real.sqrt_pos.mpr hq, (Real.sq_sqrt hq.le).symm⟩
  obtain ⟨u, hu, rfl⟩ : ∃ u, 0 < u ∧ g = u ^ 2 :=
    ⟨√g, Real.sqrt_pos.mpr hg, (Real.sq_sqrt hg.le).symm⟩
  have e1 : √(s ^ 2 * u ^ 2) = s * u := by rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have e2 : √(t ^ 2 * u ^ 2) = t * u := by rw [← mul_pow, Real.sqrt_sq (by positivity)]
  have e3 : √(s ^ 2 * t ^ 2) = s * t := by rw [← mul_pow, Real.sqrt_sq (by positivity)]
  rw [e1] at hb
  rw [e2] at hc
  rw [e1, e2, e3]
  unfold kassabovBound
  have hβ : 0 < 1 - (-(b / (s * u))) ^ 2 := by rw [neg_sq]; linarith
  have hγ : 0 < 1 - (-(c / (t * u))) ^ 2 := by rw [neg_sq]; linarith
  have key : (s ^ 2 - b * b / u ^ 2) * (t ^ 2 - c * c / u ^ 2) =
      (s * t) ^ 2 * ((1 - (-(b / (s * u))) ^ 2) * (1 - (-(c / (t * u))) ^ 2)) := by
    field_simp
  rw [key, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
  have hD : 0 < √((1 - (-(b / (s * u))) ^ 2) * (1 - (-(c / (t * u))) ^ 2)) :=
    Real.sqrt_pos.mpr (mul_pos hβ hγ)
  field_simp
  ring

/-- **The normalized Schur-complement step for a positive diagonal**: normalizing first
(conjugation by a positive diagonal matrix) does not change the normalized Schur
complement. For `A` symmetric with `A x x, A y y, A γ γ > 0`, write
`n_{uv} = A_{uv} / √(A_{uu} A_{vv})`; then the normalized entry of the Schur complement
eliminating `γ` is `-F(-n_{xy}, -n_{xγ}, -n_{yγ})`, provided `n_{xγ}², n_{yγ}² < 1`. -/
theorem normalized_schur_step' {P : Type*} (A : Matrix P P ℝ) (hsymm : A.IsSymm) (x y γ : P)
    (hx : 0 < A x x) (hy : 0 < A y y) (hγ : 0 < A γ γ)
    (hxγ : (A x γ / √(A x x * A γ γ)) ^ 2 < 1) (hyγ : (A y γ / √(A y y * A γ γ)) ^ 2 < 1) :
    (A x y - A x γ * A γ y / A γ γ) /
        √((A x x - A x γ * A γ x / A γ γ) * (A y y - A y γ * A γ y / A γ γ)) =
      -kassabovBound (-(A x y / √(A x x * A y y))) (-(A x γ / √(A x x * A γ γ)))
        (-(A y γ / √(A y y * A γ γ))) := by
  have hs : ∀ a b, A a b = A b a := fun a b => by
    rw [← Matrix.transpose_apply A b a, hsymm.eq]
  rw [hs γ y, hs γ x]
  exact schur_normalize_aux hx hy hγ hxγ hyγ

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable {P : Type*} [DecidableEq P]

/-- **The Claim of `lem:mid:allpin`**, for an abstract family of subspaces `V[𝒴]` (`𝒴` a finite
set of parts) with `V[𝒴] ⊓ V[𝒴'] = V[𝒴 ∪ 𝒴']`, and numbers `e 𝒴 β β'` that bound the
cosines at `𝒴 = ∅`, are `< 1`, and dominate Kassabov's recursion. Then for every `𝒴` and
distinct `β, β' ∉ 𝒴`,
`c_𝒴(β, β') = cos∠(V[𝒴 ∪ {β}], V[𝒴 ∪ {β'}]) ≤ e 𝒴 β β'`. -/
theorem allpin_claim (V : Finset P → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset P, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    (e : Finset P → P → P → ℝ)
    (hbase : ∀ β β', β ≠ β' → friedrichsCos (V {β}) (V {β'}) ≤ e ∅ β β')
    (hlt : ∀ 𝒴 β β', β ∉ 𝒴 → β' ∉ 𝒴 → β ≠ β' → e 𝒴 β β' < 1)
    (hrec : ∀ 𝒴 γ β β', γ ∉ 𝒴 → β ∉ insert γ 𝒴 → β' ∉ insert γ 𝒴 → β ≠ β' →
      kassabovBound (e 𝒴 β β') (e 𝒴 β γ) (e 𝒴 β' γ) ≤ e (insert γ 𝒴) β β') :
    ∀ 𝒴 β β', β ∉ 𝒴 → β' ∉ 𝒴 → β ≠ β' →
      friedrichsCos (V (insert β 𝒴)) (V (insert β' 𝒴)) ≤ e 𝒴 β β' := by
  intro 𝒴
  induction 𝒴 using Finset.induction_on with
  | empty =>
    intro β β' _ _ hne
    simpa using hbase β β' hne
  | insert γ 𝒴 hγ ih =>
    intro β β' hβ hβ' hne
    have hβ𝒴 : β ∉ 𝒴 := fun h => hβ (Finset.mem_insert_of_mem h)
    have hβ'𝒴 : β' ∉ 𝒴 := fun h => hβ' (Finset.mem_insert_of_mem h)
    have hβγ : β ≠ γ := fun h => hβ (h ▸ Finset.mem_insert_self γ 𝒴)
    have hβ'γ : β' ≠ γ := fun h => hβ' (h ▸ Finset.mem_insert_self γ 𝒴)
    have hu : ∀ δ, insert δ 𝒴 ∪ insert γ 𝒴 = insert δ (insert γ 𝒴) := fun δ => by
      ext z
      simp only [Finset.mem_union, Finset.mem_insert]
      tauto
    have hk := kassabov_inf (V₁ := V (insert β 𝒴)) (V₂ := V (insert β' 𝒴))
      (V₃ := V (insert γ 𝒴)) (ih β β' hβ𝒴 hβ'𝒴 hne) (ih β γ hβ𝒴 hγ hβγ)
      (ih β' γ hβ'𝒴 hγ hβ'γ) (hlt 𝒴 β γ hβ𝒴 hγ hβγ) (hlt 𝒴 β' γ hβ'𝒴 hγ hβ'γ)
    rw [hV, hV, hu, hu] at hk
    exact hk.trans (hrec 𝒴 γ β β' hγ hβ hβ' hne)

/-- The Claim at `𝒴 = 𝒫 ∖ {β, β'}`: `cos∠(V[𝒫 ∖ {β'}], V[𝒫 ∖ {β}]) ≤ e_𝒴(β, β')`. -/
theorem allpin_claim_pair [Fintype P] (V : Finset P → Submodule ℝ E)
    (hV : ∀ 𝒴 𝒴' : Finset P, V 𝒴 ⊓ V 𝒴' = V (𝒴 ∪ 𝒴'))
    (e : Finset P → P → P → ℝ)
    (hbase : ∀ β β', β ≠ β' → friedrichsCos (V {β}) (V {β'}) ≤ e ∅ β β')
    (hlt : ∀ 𝒴 β β', β ∉ 𝒴 → β' ∉ 𝒴 → β ≠ β' → e 𝒴 β β' < 1)
    (hrec : ∀ 𝒴 γ β β', γ ∉ 𝒴 → β ∉ insert γ 𝒴 → β' ∉ insert γ 𝒴 → β ≠ β' →
      kassabovBound (e 𝒴 β β') (e 𝒴 β γ) (e 𝒴 β' γ) ≤ e (insert γ 𝒴) β β')
    {β β' : P} (hne : β ≠ β') :
    friedrichsCos (V (Finset.univ \ {β'})) (V (Finset.univ \ {β})) ≤
      e (Finset.univ \ {β, β'}) β β' := by
  have h := allpin_claim V hV e hbase hlt hrec (Finset.univ \ {β, β'}) β β' (by simp)
    (by simp) hne
  have h1 : insert β (Finset.univ \ {β, β'}) = Finset.univ \ {β'} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro (rfl | h)
      · exact hne
      · exact fun h' => h (Or.inr h')
    · intro h
      by_cases hz : z = β
      · exact Or.inl hz
      · exact Or.inr fun h' => h'.elim hz h
  have h2 : insert β' (Finset.univ \ {β, β'}) = Finset.univ \ {β} := by
    ext z
    simp only [Finset.mem_insert, Finset.mem_sdiff, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    constructor
    · rintro (rfl | h)
      · exact fun h' => hne h'.symm
      · exact fun h' => h (Or.inl h')
    · intro h
      by_cases hz : z = β'
      · exact Or.inl hz
      · exact Or.inr fun h' => h'.elim h hz
  rwa [h1, h2] at h

end Sarkozy.Angles

module

public import Sarkozy.RecordExpansion.Completion
public import Sarkozy.RecordExpansion.Multinomial

/-!
# Degree-class replacement

`lem:record:record-expansion` (v) of the paper (Section 10), in evaluated form,
for a finite set of degree vectors.

## Setting

The skew records are divided into kinds `l ∈ L`: `kind : PriceVar T → Option L`
assigns a kind to (some of) the skew variables `x^a_{b,t}` (`hkind`: only skew
variables have a kind), so `ℛ_l = kindSet kind l`. Every variable carries the
auxiliary prices `y^arm`, `y^lead`, `y^rem ≥ 0` (only their values at the
variables of a kind enter), with kind totals `A^arm_l`, `A^lead_l`, `A^rem_l`
(`kindTotal`). For a degree vector `n` with `|n| ≥ 2` even, `degreeClass kind n`
is the class `𝒞_n` of the selections consisting of `n_l` skew records of kind
`l` for every `l` and of no other record: a selection is in `𝒞_n` iff its
monomial lies in `kindMonos kind n`. Its class bound is
`φ_ω = C_n ∏_{b ∈ X} y^arm_{b,t_b} + B'(∏_{b ∈ X}(y^lead + y^rem) - ∏_{b ∈ X} y^lead)`
(`replacementBound`), and `replacementSaving` is the subtracted polynomial
`(1/n!)[B' ∏ A_l^{n_l} - C_n ∏ (A^arm_l)^{n_l} - B'(∏ (A^lead_l + A^rem_l)^{n_l} - ∏ (A^lead_l)^{n_l})]`.

## Main results

* `replacement_le`: let `Ψ_0 = B'(e^{S(x)} cosh A(x) - 1) - 𝒟(x)` be a completed
  polynomial for the selections outside the classes `𝒞_n`, `n ∈ N` (the
  conditions of (iv): `0 ≤ d_m`, `d_m ≤ B' - c_ω` on the monomial of every such
  selection, `d_m ≤ B' c_m` on every non-selection monomial), whose coefficients on
  the monomials of the classes are those of `B'(e^{S(x)} cosh A(x) - 1)`
  (`d_m = 0` on `kindMonos kind n`). Then at nonnegative prices
  `∑_{ω outside} c_ω π_ω + ∑_{n ∈ N} ∑_{ω ∈ 𝒞_n} φ_ω ≤ Ψ_0(π) - ∑_{n ∈ N} saving_n(π, y)`.
  That is, `Ψ = Ψ_0 - ∑_n saving_n` dominates the bounds `b_ω` of all
  selections, evaluated at `(π, y)`; the replacements of several degree vectors
  add.
* `replacement_le_upper`: the same with the right side evaluated at upper
  prices `π̂ ≥ π` and upper auxiliary prices `ŷ ≥ y` (`lem:record:record-expansion`
  (iii)); the costs of the selections outside the classes are assumed
  nonnegative.
* `abs_energy_sub_le_replacement`: the reserved cost. If the terms satisfy
  `∑_ω |I_ω| ≤ ∑_ω ((b_ω + z π_ω) Y + r_ω)` with `b_ω = φ_ω` on the replaced classes
  and `b_ω = c_ω π_ω` elsewhere (`replacedBound`), then
  `|Y_ν - Y_λ| ≤ (Ψ(π̂, ŷ) + z (e^Ŝ cosh Â - 1)) Y + ∑_ω r_ω`.

`Ψ_0` is required to be of the completed form of (iv), which is the form used
in Part V (`Ψ_0 = B'(e^{S(x)} cosh A(x) - 1) - 𝒟_sym(x)`); the paper allows any
complete polynomial. The credits clause at the end of (v) is not formalized in
general; credits `γ_ω = g ∏_{b ∈ X} y^arm` on the raw-arm monomials with
`0 ≤ g ≤ C_n` amount to the class bound with `C_n - g` in place of `C_n`, which
is again covered by these theorems. The multinomial identity
`∏_l A_l^{n_l}/n! = ∑_{m ∈ kindMonos} x^m/m!` (`sum_kindMonos_mono_div`) replaces
the paper's coefficient comparison, and the inequality
`∑_{ω ∈ 𝒞_n} φ_ω ≤ (1/n!)[...]` ("dropping distinctness only adds nonnegative
terms") is `sum_replacementBound_le`.
-/

@[expose] public section

open Finset Filter
open scoped BigOperators Nat

namespace Sarkozy.RecordExpansion

open Choice

/-! ### Monotonicity of `∏ (a + b)^m - ∏ a^m` -/

theorem pow_add_sub_pow_mono {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (haa : a ≤ a')
    (hbb : b ≤ b') (k : ℕ) :
    0 ≤ (a + b) ^ k - a ^ k ∧ (a + b) ^ k - a ^ k ≤ (a' + b') ^ k - a' ^ k := by
  have e1 := geom_sum₂_mul (a + b) a k
  have e2 := geom_sum₂_mul (a' + b') a' k
  rw [add_sub_cancel_left] at e1 e2
  rw [← e1, ← e2]
  have hab : 0 ≤ a + b := add_nonneg ha hb
  have hs : ∑ i ∈ range k, (a + b) ^ i * a ^ (k - 1 - i) ≤
      ∑ i ∈ range k, (a' + b') ^ i * a' ^ (k - 1 - i) := by
    apply sum_le_sum
    intro i _
    exact mul_le_mul (pow_le_pow_left₀ hab (add_le_add haa hbb) i)
      (pow_le_pow_left₀ ha haa _) (pow_nonneg ha _)
      (pow_nonneg (le_trans hab (add_le_add haa hbb)) _)
  have hs0 : 0 ≤ ∑ i ∈ range k, (a + b) ^ i * a ^ (k - 1 - i) :=
    sum_nonneg fun i _ => mul_nonneg (pow_nonneg hab _) (pow_nonneg ha _)
  exact ⟨mul_nonneg hs0 hb, mul_le_mul hs hbb hb (hs0.trans hs)⟩

/-- `∏_i (a_i + b_i)^{m_i} - ∏_i a_i^{m_i}` is nonnegative and nondecreasing in
`a ≥ 0` and `b ≥ 0`: it is a polynomial with nonnegative coefficients. -/
theorem prod_add_pow_sub_mono {ι : Type*} [DecidableEq ι] (s : Finset ι) (m : ι → ℕ)
    {a b a' b' : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i) (haa : ∀ i, a i ≤ a' i)
    (hbb : ∀ i, b i ≤ b' i) :
    0 ≤ ∏ i ∈ s, (a i + b i) ^ m i - ∏ i ∈ s, a i ^ m i ∧
      ∏ i ∈ s, (a i + b i) ^ m i - ∏ i ∈ s, a i ^ m i ≤
        ∏ i ∈ s, (a' i + b' i) ^ m i - ∏ i ∈ s, a' i ^ m i := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert j s hj ih =>
    rw [prod_insert hj, prod_insert hj, prod_insert hj, prod_insert hj]
    obtain ⟨ih0, ih1⟩ := ih
    obtain ⟨h0, h1⟩ := pow_add_sub_pow_mono (ha j) (hb j) (haa j) (hbb j) (m j)
    have hPf : 0 ≤ ∏ i ∈ s, (a i + b i) ^ m i :=
      prod_nonneg fun i _ => pow_nonneg (add_nonneg (ha i) (hb i)) _
    have hPfle : ∏ i ∈ s, (a i + b i) ^ m i ≤ ∏ i ∈ s, (a' i + b' i) ^ m i :=
      Finset.prod_le_prod₀ (fun i _ => pow_nonneg (add_nonneg (ha i) (hb i)) _)
        (fun i _ => pow_le_pow_left₀ (add_nonneg (ha i) (hb i)) (add_le_add (haa i) (hbb i)) _)
    have hgj : 0 ≤ a j ^ m j := pow_nonneg (ha j) _
    have hgjle : a j ^ m j ≤ a' j ^ m j := pow_le_pow_left₀ (ha j) (haa j) _
    have e : ∀ (p q P Q : ℝ), p * P - q * Q = (p - q) * P + q * (P - Q) := by
      intros
      ring
    rw [e, e]
    constructor
    · exact add_nonneg (mul_nonneg h0 hPf) (mul_nonneg hgj ih0)
    · exact add_le_add (mul_le_mul h1 hPfle hPf (h0.trans h1))
        (mul_le_mul hgjle ih1 ih0 (hgj.trans hgjle))

/-! ### Degree classes -/

section Classes

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)] {L : Type*} [Fintype L] [DecidableEq L]

/-- The class `𝒞_n` of (v): the selections consisting of `n_l` skew records of kind
`l` for every `l` and of no other record. -/
def degreeClass (kind : PriceVar T → Option L) (n : L → ℕ) : Finset (Choice T) :=
  (univ.filter fun ω : Choice T => IsSelection ω).filter fun ω => selMono ω ∈ kindMonos kind n

/-- The total `∑_{v ∈ ℛ_l} z_v` of a kind. -/
def kindTotal (kind : PriceVar T → Option L) (z : PriceVar T → ℝ) (l : L) : ℝ :=
  ∑ v ∈ kindSet kind l, z v

/-- `n! = ∏_l n_l!` for a degree vector. -/
def degFact (n : L → ℕ) : ℕ := ∏ l, (n l)!

/-- The class bound
`φ_ω = C_n ∏_{b ∈ X} y^arm + B'(∏_{b ∈ X} (y^lead + y^rem) - ∏_{b ∈ X} y^lead)` of (v). -/
noncomputable def replacementBound (Cn B' : ℝ) (yarm ylead yrem : PriceVar T → ℝ)
    (ω : Choice T) : ℝ :=
  Cn * mono yarm (selMono ω) +
    B' * (mono (fun v => ylead v + yrem v) (selMono ω) - mono ylead (selMono ω))

/-- The subtracted polynomial of (v):
`(1/n!)[B' ∏ A_l^{n_l} - C_n ∏ (A^arm_l)^{n_l} - B'(∏ (A^lead_l + A^rem_l)^{n_l} - ∏ (A^lead_l)^{n_l})]`. -/
noncomputable def replacementSaving (kind : PriceVar T → Option L) (n : L → ℕ) (Cn B' : ℝ)
    (x yarm ylead yrem : PriceVar T → ℝ) : ℝ :=
  (B' * ∏ l, kindTotal kind x l ^ n l - Cn * ∏ l, kindTotal kind yarm l ^ n l -
    B' * (∏ l, (kindTotal kind ylead l + kindTotal kind yrem l) ^ n l -
      ∏ l, kindTotal kind ylead l ^ n l)) / (degFact n : ℝ)

/-- **The multinomial identity**: `∑_{m ∈ kindMonos kind n} x^m / m! = ∏_l A_l^{n_l} / n!`. -/
theorem sum_kindMonos_mono_div (kind : PriceVar T → Option L) (n : L → ℕ)
    (z : PriceVar T → ℝ) :
    ∑ m ∈ kindMonos kind n, mono z m / (mfact m : ℝ) =
      (∏ l, kindTotal kind z l ^ n l) / (degFact n : ℝ) := by
  have h := prod_kind_pow_div kind n z
  rw [Finset.prod_div_distrib] at h
  unfold kindTotal degFact
  rw [Nat.cast_prod, h]
  apply sum_congr rfl
  intro m _
  unfold mono mfact
  rw [Nat.cast_prod, Finset.prod_div_distrib]

theorem skewDeg_of_mem_kindMonos {kind : PriceVar T → Option L}
    (hkind : ∀ v l, kind v = some l → v.2.2 = .skew) {n : L → ℕ} {m : PriceVar T → ℕ}
    (hm : m ∈ kindMonos kind n) : skewDeg m = ∑ l, n l := by
  rw [mem_kindMonos] at hm
  have h1 : skewDeg m = ∑ v, m v := by
    unfold skewDeg
    apply sum_congr rfl
    intro v _
    split_ifs with h
    · rfl
    · rcases hv : kind v with _ | l
      · exact (hm.1 v hv).symm
      · exact absurd (hkind v l hv) h
  rw [h1, ← Finset.sum_fiberwise univ kind m, Fintype.sum_option]
  have h0 : ∑ v ∈ univ with kind v = none, m v = 0 := by
    apply sum_eq_zero
    intro v hv
    exact hm.1 v (mem_filter.mp hv).2
  rw [h0, zero_add]
  apply sum_congr rfl
  intro l _
  rw [← hm.2 l]
  apply sum_congr
  · ext v
    simp [kindSet]
  · intro v _
    rfl

theorem expCoeff_of_mem_kindMonos {kind : PriceVar T → Option L}
    (hkind : ∀ v l, kind v = some l → v.2.2 = .skew) {n : L → ℕ}
    (hn : n ≠ 0 ∧ Even (∑ l, n l)) {m : PriceVar T → ℕ} (hm : m ∈ kindMonos kind n) :
    expCoeff m = 1 / (mfact m : ℝ) := by
  have hne : m ≠ 0 := by
    rintro rfl
    apply hn.1
    funext l
    have := (mem_kindMonos.mp hm).2 l
    simp only [Pi.zero_apply, sum_const_zero] at this
    exact this.symm
  have hev : Even (skewDeg m) := by
    rw [skewDeg_of_mem_kindMonos hkind hm]
    exact hn.2
  unfold expCoeff
  simp only [ne_eq, hne, not_false_eq_true, hev, and_self, ↓reduceIte]

theorem kindMonos_disjoint {kind : PriceVar T → Option L} {n n' : L → ℕ} (h : n ≠ n') :
    Disjoint (kindMonos kind n) (kindMonos kind n') := by
  rw [Finset.disjoint_left]
  intro m hm hm'
  apply h
  funext l
  rw [← (mem_kindMonos.mp hm).2 l, ← (mem_kindMonos.mp hm').2 l]

/-- The sum over a class of a nonnegative function of the monomial is at most the
corresponding sum over all monomials of the degree, weighted by `1/m!`: the
monomials of the selections are distinct, squarefree, and lie in `kindMonos`. -/
theorem sum_degreeClass_le (kind : PriceVar T → Option L) (n : L → ℕ)
    (f : (PriceVar T → ℕ) → ℝ) (hf : ∀ m, 0 ≤ f m) :
    ∑ ω ∈ degreeClass kind n, f (selMono ω) ≤
      ∑ m ∈ kindMonos kind n, f m / (mfact m : ℝ) := by
  have hinj : Set.InjOn selMono (degreeClass kind n : Set (Choice T)) :=
    fun a _ b _ h => selMono_injective h
  rw [← sum_image (f := f) hinj]
  have h1 : ∑ m ∈ (degreeClass kind n).image selMono, f m =
      ∑ m ∈ (degreeClass kind n).image selMono, f m / (mfact m : ℝ) := by
    apply sum_congr rfl
    intro m hm
    obtain ⟨ω, _, rfl⟩ := mem_image.mp hm
    rw [mfact_selMono, Nat.cast_one, div_one]
  rw [h1]
  apply sum_le_sum_of_subset_of_nonneg
  · intro m hm
    obtain ⟨ω, hω, rfl⟩ := mem_image.mp hm
    exact (mem_filter.mp hω).2
  · intro m _ _
    exact div_nonneg (hf m) (Nat.cast_nonneg _)

omit [DecidableEq J] [∀ b, DecidableEq (T b)] [Fintype L] in
theorem kindTotal_add (kind : PriceVar T → Option L) (y y' : PriceVar T → ℝ) (l : L) :
    kindTotal kind (fun v => y v + y' v) l = kindTotal kind y l + kindTotal kind y' l := by
  unfold kindTotal
  rw [sum_add_distrib]

/-- **The class bounds of a degree class are dominated by the subtracted totals**
("dropping the distinctness only adds nonnegative terms"):
`∑_{ω ∈ 𝒞_n} φ_ω ≤ (1/n!)[C_n ∏ (A^arm_l)^{n_l} + B'(∏ (A^lead_l + A^rem_l)^{n_l} - ∏ (A^lead_l)^{n_l})]`. -/
theorem sum_replacementBound_le (kind : PriceVar T → Option L) (n : L → ℕ) {Cn B' : ℝ}
    (hC : 0 ≤ Cn) (hB' : 0 ≤ B') {yarm ylead yrem : PriceVar T → ℝ}
    (harm : ∀ v, 0 ≤ yarm v) (hlead : ∀ v, 0 ≤ ylead v) (hrem : ∀ v, 0 ≤ yrem v) :
    ∑ ω ∈ degreeClass kind n, replacementBound Cn B' yarm ylead yrem ω ≤
      (Cn * ∏ l, kindTotal kind yarm l ^ n l +
        B' * (∏ l, (kindTotal kind ylead l + kindTotal kind yrem l) ^ n l -
          ∏ l, kindTotal kind ylead l ^ n l)) / (degFact n : ℝ) := by
  have hsum := Finset.sum_add_distrib (s := degreeClass kind n)
    (f := fun ω => Cn * mono yarm (selMono ω))
    (g := fun ω => B' * (mono (fun v => ylead v + yrem v) (selMono ω) - mono ylead (selMono ω)))
  unfold replacementBound
  rw [hsum, ← mul_sum, ← mul_sum]
  have ha := sum_degreeClass_le kind n (fun m => mono yarm m) (fun m => mono_nonneg harm m)
  have hl := sum_degreeClass_le kind n
    (fun m => mono (fun v => ylead v + yrem v) m - mono ylead m)
    (fun m => sub_nonneg.mpr (mono_le_mono hlead (fun v => le_add_of_nonneg_right (hrem v)) m))
  rw [sum_kindMonos_mono_div] at ha
  have hl' : ∑ m ∈ kindMonos kind n,
      (mono (fun v => ylead v + yrem v) m - mono ylead m) / (mfact m : ℝ) =
      (∏ l, (kindTotal kind ylead l + kindTotal kind yrem l) ^ n l -
        ∏ l, kindTotal kind ylead l ^ n l) / (degFact n : ℝ) := by
    simp_rw [sub_div]
    rw [sum_sub_distrib, sum_kindMonos_mono_div, sum_kindMonos_mono_div]
    simp_rw [kindTotal_add]
  rw [hl'] at hl
  have h1 := mul_le_mul_of_nonneg_left ha hC
  have h2 := mul_le_mul_of_nonneg_left hl hB'
  rw [add_div, mul_div_assoc, mul_div_assoc]
  exact add_le_add h1 h2

end Classes

/-! ### The replacement -/

section Replacement

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)] {L : Type*} [Fintype L] [DecidableEq L]

/-- **Degree-class replacement at the actual prices** (`lem:record:record-expansion`
(v), for a finite set `N` of degree vectors; credits not included). -/
theorem replacement_le {π : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (kind : PriceVar T → Option L) (hkind : ∀ v l, kind v = some l → v.2.2 = .skew)
    (N : Finset (L → ℕ)) (hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l))
    (C : (L → ℕ) → ℝ) (hC : ∀ n ∈ N, 0 ≤ C n) {yarm ylead yrem : PriceVar T → ℝ}
    (harm : ∀ v, 0 ≤ yarm v) (hlead : ∀ v, 0 ≤ ylead v) (hrem : ∀ v, 0 ≤ yrem v)
    (cost : Choice T → ℝ) {B' : ℝ} (hB' : 0 ≤ B')
    (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ m, 0 ≤ d m)
    (hd0 : ∀ n ∈ N, ∀ m ∈ kindMonos kind n, d m = 0)
    (hsel : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) →
      d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ m, (∀ ω, IsSelection ω → selMono ω ≠ m) → d m ≤ B' * expCoeff m) :
    ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter
        (fun ω => ∀ n ∈ N, selMono ω ∉ kindMonos kind n), cost ω * monomial π ω +
      ∑ n ∈ N, ∑ ω ∈ degreeClass kind n, replacementBound (C n) B' yarm ylead yrem ω ≤
    B' * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) -
      ∑ m ∈ supp, d m * mono (priceVec π) m -
      ∑ n ∈ N, replacementSaving kind n (C n) B' (priceVec π) yarm ylead yrem := by
  classical
  set x := priceVec π with hxdef
  set U := N.biUnion (kindMonos kind) with hUdef
  have hU : ∀ m, m ∈ U ↔ ∃ n ∈ N, m ∈ kindMonos kind n := fun m => mem_biUnion
  have hdU : ∀ m ∈ U, d m = 0 := by
    intro m hm
    obtain ⟨n, hn, hmn⟩ := (hU m).mp hm
    exact hd0 n hn m hmn
  set d' : (PriceVar T → ℕ) → ℝ := fun m => d m + if m ∈ U then B' * expCoeff m else 0
    with hd'def
  set cost' : Choice T → ℝ := fun ω => if selMono ω ∈ U then 0 else cost ω with hcost'def
  have hd' : ∀ m, 0 ≤ d' m := by
    intro m
    simp only [hd'def]
    have := hd m
    split_ifs
    · exact add_nonneg this (mul_nonneg hB' (expCoeff_nonneg m))
    · linarith
  have hsel' : ∀ ω, IsSelection ω → d' (selMono ω) ≤ B' - cost' ω := by
    intro ω hω
    simp only [hd'def, hcost'def]
    by_cases hmem : selMono ω ∈ U
    · simp only [hmem, ↓reduceIte, hdU _ hmem, expCoeff_selMono hω, mul_one, zero_add,
        sub_zero, le_refl]
    · simp only [hmem, ↓reduceIte, add_zero]
      apply hsel ω hω
      intro n hn hmn
      exact hmem ((hU _).mpr ⟨n, hn, hmn⟩)
  have hoth' : ∀ m, (∀ ω, IsSelection ω → selMono ω ≠ m) → d' m ≤ B' * expCoeff m := by
    intro m hm
    simp only [hd'def]
    by_cases hmem : m ∈ U
    · simp only [hmem, ↓reduceIte, hdU _ hmem, zero_add, le_refl]
    · simp only [hmem, ↓reduceIte, add_zero]
      exact hoth m hm
  have hmain := sum_cost_add_poly_le hπ cost' hB' (supp ∪ U) d' hd' hsel' hoth'
  -- the selections outside the classes
  have h1 : ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), cost' ω * monomial π ω =
      ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter
        (fun ω => ∀ n ∈ N, selMono ω ∉ kindMonos kind n), cost ω * monomial π ω := by
    rw [Finset.sum_filter (fun ω : Choice T => ∀ n ∈ N, selMono ω ∉ kindMonos kind n)]
    apply sum_congr rfl
    intro ω _
    simp only [hcost'def]
    by_cases hmem : selMono ω ∈ U
    · have hn : ¬∀ n ∈ N, selMono ω ∉ kindMonos kind n := by
        intro h
        obtain ⟨n, hn, hmn⟩ := (hU _).mp hmem
        exact h n hn hmn
      rw [ite_eq_left hmem, ite_eq_right hn, zero_mul]
    · have hn : ∀ n ∈ N, selMono ω ∉ kindMonos kind n := by
        intro n hn hmn
        exact hmem ((hU _).mpr ⟨n, hn, hmn⟩)
      rw [ite_eq_right hmem, ite_eq_left hn]
  -- the completed polynomial
  have h2 : ∑ m ∈ supp ∪ U, d' m * mono x m =
      ∑ m ∈ supp, d m * mono x m + B' * ∑ n ∈ N, ∑ m ∈ kindMonos kind n,
        expCoeff m * mono x m := by
    simp only [hd'def, add_mul, sum_add_distrib]
    congr 1
    · symm
      apply sum_subset subset_union_left
      intro m hm hms
      have hmU : m ∈ U := by
        rcases mem_union.mp hm with h | h
        · exact absurd h hms
        · exact h
      rw [hdU m hmU, zero_mul]
    · have hdisj : (N : Set (L → ℕ)).PairwiseDisjoint (kindMonos kind) :=
        fun n _ n' _ h => kindMonos_disjoint h
      rw [← sum_biUnion hdisj, mul_sum, ← hUdef]
      have hU' : ∑ m ∈ U, B' * (expCoeff m * mono x m) =
          ∑ m ∈ U, (if m ∈ U then B' * expCoeff m else 0) * mono x m := by
        apply sum_congr rfl
        intro m hm
        rw [ite_eq_left hm]
        ring
      rw [hU']
      exact (sum_subset subset_union_right
        (fun m _ hmU => by rw [ite_eq_right hmU, zero_mul])).symm
  have h3 : ∀ n ∈ N, ∑ m ∈ kindMonos kind n, expCoeff m * mono x m =
      (∏ l, kindTotal kind x l ^ n l) / (degFact n : ℝ) := by
    intro n hn
    rw [← sum_kindMonos_mono_div]
    apply sum_congr rfl
    intro m hm
    rw [expCoeff_of_mem_kindMonos hkind (hN n hn) hm]
    ring
  rw [h1, h2, sum_congr rfl h3] at hmain
  -- the class bounds
  have h4 : ∑ n ∈ N, ∑ ω ∈ degreeClass kind n, replacementBound (C n) B' yarm ylead yrem ω ≤
      ∑ n ∈ N, (C n * ∏ l, kindTotal kind yarm l ^ n l +
        B' * (∏ l, (kindTotal kind ylead l + kindTotal kind yrem l) ^ n l -
          ∏ l, kindTotal kind ylead l ^ n l)) / (degFact n : ℝ) :=
    sum_le_sum fun n hn => sum_replacementBound_le kind n (hC n hn) hB' harm hlead hrem
  have h5 : ∑ n ∈ N, replacementSaving kind n (C n) B' x yarm ylead yrem =
      B' * ∑ n ∈ N, (∏ l, kindTotal kind x l ^ n l) / (degFact n : ℝ) -
        ∑ n ∈ N, (C n * ∏ l, kindTotal kind yarm l ^ n l +
          B' * (∏ l, (kindTotal kind ylead l + kindTotal kind yrem l) ^ n l -
            ∏ l, kindTotal kind ylead l ^ n l)) / (degFact n : ℝ) := by
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    unfold replacementSaving
    ring
  rw [h5]
  linarith

/-- The completed polynomial of the replacement:
`∑_{m ∈ supp ∪ U} (d_m + [m ∈ U] B' c_m) x^m = 𝒟(x) + B' ∑_{n ∈ N} ∏_l A_l(x)^{n_l} / n!`,
`U` the union of the monomial sets of the classes. -/
theorem replacement_poly_eq (kind : PriceVar T → Option L)
    (hkind : ∀ v l, kind v = some l → v.2.2 = .skew) (N : Finset (L → ℕ))
    (hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l)) (supp : Finset (PriceVar T → ℕ))
    (d : (PriceVar T → ℕ) → ℝ) (hd0 : ∀ n ∈ N, ∀ m ∈ kindMonos kind n, d m = 0) (B' : ℝ)
    (x : PriceVar T → ℝ) :
    ∑ m ∈ supp ∪ N.biUnion (kindMonos kind),
        (d m + if m ∈ N.biUnion (kindMonos kind) then B' * expCoeff m else 0) * mono x m =
      ∑ m ∈ supp, d m * mono x m +
        B' * ∑ n ∈ N, (∏ l, kindTotal kind x l ^ n l) / (degFact n : ℝ) := by
  set U := N.biUnion (kindMonos kind) with hUdef
  have hdU : ∀ m ∈ U, d m = 0 := by
    intro m hm
    obtain ⟨n, hn, hmn⟩ := mem_biUnion.mp hm
    exact hd0 n hn m hmn
  simp only [add_mul, sum_add_distrib]
  congr 1
  · symm
    apply sum_subset subset_union_left
    intro m hm hms
    have hmU : m ∈ U := by
      rcases mem_union.mp hm with h | h
      · exact absurd h hms
      · exact h
    rw [hdU m hmU, zero_mul]
  · have h3 : ∀ n ∈ N, ∑ m ∈ kindMonos kind n, expCoeff m * mono x m =
        (∏ l, kindTotal kind x l ^ n l) / (degFact n : ℝ) := by
      intro n hn
      rw [← sum_kindMonos_mono_div]
      apply sum_congr rfl
      intro m hm
      rw [expCoeff_of_mem_kindMonos hkind (hN n hn) hm]
      ring
    rw [← sum_congr rfl h3]
    have hdisj : (N : Set (L → ℕ)).PairwiseDisjoint (kindMonos kind) :=
      fun n _ n' _ h => kindMonos_disjoint h
    rw [← sum_biUnion hdisj, mul_sum, ← hUdef]
    have hU' : ∑ m ∈ U, B' * (expCoeff m * mono x m) =
        ∑ m ∈ U, (if m ∈ U then B' * expCoeff m else 0) * mono x m := by
      apply sum_congr rfl
      intro m hm
      rw [ite_eq_left hm]
      ring
    rw [hU']
    exact (sum_subset subset_union_right
      (fun m _ hmU => by rw [ite_eq_right hmU, zero_mul])).symm

omit [DecidableEq J] [∀ b, DecidableEq (T b)] in
/-- The added class totals of the replacement are nondecreasing in the auxiliary
prices (`lem:record:record-expansion` (iii)). -/
theorem replacement_classTotal_mono (kind : PriceVar T → Option L) (N : Finset (L → ℕ))
    (C : (L → ℕ) → ℝ) (hC : ∀ n ∈ N, 0 ≤ C n) {B' : ℝ} (hB' : 0 ≤ B')
    {yarm ylead yrem yarm' ylead' yrem' : PriceVar T → ℝ}
    (harm : ∀ v, 0 ≤ yarm v) (hlead : ∀ v, 0 ≤ ylead v) (hrem : ∀ v, 0 ≤ yrem v)
    (harm' : ∀ v, yarm v ≤ yarm' v) (hlead' : ∀ v, ylead v ≤ ylead' v)
    (hrem' : ∀ v, yrem v ≤ yrem' v) :
    ∑ n ∈ N, (C n * ∏ l, kindTotal kind yarm l ^ n l +
        B' * (∏ l, (kindTotal kind ylead l + kindTotal kind yrem l) ^ n l -
          ∏ l, kindTotal kind ylead l ^ n l)) / (degFact n : ℝ) ≤
      ∑ n ∈ N, (C n * ∏ l, kindTotal kind yarm' l ^ n l +
        B' * (∏ l, (kindTotal kind ylead' l + kindTotal kind yrem' l) ^ n l -
          ∏ l, kindTotal kind ylead' l ^ n l)) / (degFact n : ℝ) := by
  have htot : ∀ (y y' : PriceVar T → ℝ), (∀ v, 0 ≤ y v) → (∀ v, y v ≤ y' v) →
      ∀ l, 0 ≤ kindTotal kind y l ∧ kindTotal kind y l ≤ kindTotal kind y' l := by
    intro y y' hy hyy l
    exact ⟨sum_nonneg fun v _ => hy v, sum_le_sum fun v _ => hyy v⟩
  apply sum_le_sum
  intro n hn
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  apply add_le_add
  · apply mul_le_mul_of_nonneg_left _ (hC n hn)
    exact Finset.prod_le_prod₀ (fun l _ => pow_nonneg (htot yarm yarm' harm harm' l).1 _)
      (fun l _ => pow_le_pow_left₀ (htot yarm yarm' harm harm' l).1
        (htot yarm yarm' harm harm' l).2 _)
  · apply mul_le_mul_of_nonneg_left _ hB'
    exact (prod_add_pow_sub_mono univ n (fun l => (htot ylead ylead' hlead hlead' l).1)
      (fun l => (htot yrem yrem' hrem hrem' l).1) (fun l => (htot ylead ylead' hlead hlead' l).2)
      (fun l => (htot yrem yrem' hrem hrem' l).2)).2

/-- **Degree-class replacement at upper prices** (`lem:record:record-expansion` (v)
with (iii)): under the hypotheses of `replacement_le` and nonnegative costs of the
selections outside the classes, the bound holds with the right side evaluated at
upper prices `π̂ ≥ π` and upper auxiliary prices `ŷ ≥ y`. -/
theorem replacement_le_upper {π πu : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (hle : ∀ b t e, π b t e ≤ πu b t e)
    (kind : PriceVar T → Option L) (hkind : ∀ v l, kind v = some l → v.2.2 = .skew)
    (N : Finset (L → ℕ)) (hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l))
    (C : (L → ℕ) → ℝ) (hC : ∀ n ∈ N, 0 ≤ C n)
    {yarm ylead yrem yarmu yleadu yremu : PriceVar T → ℝ}
    (harm : ∀ v, 0 ≤ yarm v) (hlead : ∀ v, 0 ≤ ylead v) (hrem : ∀ v, 0 ≤ yrem v)
    (harmu : ∀ v, yarm v ≤ yarmu v) (hleadu : ∀ v, ylead v ≤ yleadu v)
    (hremu : ∀ v, yrem v ≤ yremu v)
    (cost : Choice T → ℝ)
    (hcost : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) → 0 ≤ cost ω)
    {B' : ℝ} (hB' : 0 ≤ B')
    (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ m, 0 ≤ d m)
    (hd0 : ∀ n ∈ N, ∀ m ∈ kindMonos kind n, d m = 0)
    (hsel : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) →
      d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ m, (∀ ω, IsSelection ω → selMono ω ≠ m) → d m ≤ B' * expCoeff m) :
    ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter
        (fun ω => ∀ n ∈ N, selMono ω ∉ kindMonos kind n), cost ω * monomial π ω +
      ∑ n ∈ N, ∑ ω ∈ degreeClass kind n, replacementBound (C n) B' yarm ylead yrem ω ≤
    B' * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) -
      ∑ m ∈ supp, d m * mono (priceVec πu) m -
      ∑ n ∈ N, replacementSaving kind n (C n) B' (priceVec πu) yarmu yleadu yremu := by
  classical
  have h := replacement_le hπ kind hkind N hN C hC harm hlead hrem cost hB' supp d hd hd0
    hsel hoth
  set U := N.biUnion (kindMonos kind) with hUdef
  set d' : (PriceVar T → ℕ) → ℝ := fun m => d m + if m ∈ U then B' * expCoeff m else 0
    with hd'def
  have hd' : ∀ m, 0 ≤ d' m := by
    intro m
    simp only [hd'def]
    have := hd m
    split_ifs
    · exact add_nonneg this (mul_nonneg hB' (expCoeff_nonneg m))
    · linarith
  have hcoeff' : ∀ m, d' m ≤ B' * expCoeff m := by
    intro m
    simp only [hd'def]
    by_cases hmU : m ∈ U
    · obtain ⟨n, hn, hmn⟩ := mem_biUnion.mp hmU
      rw [ite_eq_left hmU, hd0 n hn m hmn, zero_add]
    · rw [ite_eq_right hmU, add_zero]
      by_cases hsm : ∃ ω, IsSelection ω ∧ selMono ω = m
      · obtain ⟨ω, hω, rfl⟩ := hsm
        have hout : ∀ n ∈ N, selMono ω ∉ kindMonos kind n := fun n hn hmn =>
          hmU (mem_biUnion.mpr ⟨n, hn, hmn⟩)
        rw [expCoeff_selMono hω, mul_one]
        linarith [hsel ω hω hout, hcost ω hω hout]
      · simp only [not_exists, not_and] at hsm
        exact hoth m hsm
  have hmono := completion_mono (supp ∪ U) d' hd' hcoeff' (x := priceVec π) (y := priceVec πu)
    (fun v => hπ _ _ _) (fun v => hle _ _ _)
  rw [symSum_priceVec, skewSum_priceVec, symSum_priceVec, skewSum_priceVec] at hmono
  simp only [hd'def] at hmono
  rw [replacement_poly_eq kind hkind N hN supp d hd0 B' (priceVec π),
    replacement_poly_eq kind hkind N hN supp d hd0 B' (priceVec πu)] at hmono
  have hy := replacement_classTotal_mono kind N C hC hB' harm hlead hrem harmu hleadu hremu
  have hs : ∀ (x ya yl yr : PriceVar T → ℝ),
      ∑ n ∈ N, replacementSaving kind n (C n) B' x ya yl yr =
        B' * ∑ n ∈ N, (∏ l, kindTotal kind x l ^ n l) / (degFact n : ℝ) -
          ∑ n ∈ N, (C n * ∏ l, kindTotal kind ya l ^ n l +
            B' * (∏ l, (kindTotal kind yl l + kindTotal kind yr l) ^ n l -
              ∏ l, kindTotal kind yl l ^ n l)) / (degFact n : ℝ) := by
    intro x ya yl yr
    rw [mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n _
    unfold replacementSaving
    ring
  rw [hs] at h ⊢
  linarith

end Replacement

/-! ### The reserved cost with replaced degree classes -/

section Energy

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]
  {T : J → Type*} [∀ b, Fintype (T b)] [∀ b, DecidableEq (T b)]
  {L : Type*} [Fintype L] [DecidableEq L]

/-- The degree vector of a monomial: its degree in the variables of each kind. -/
def degreeOf (kind : PriceVar T → Option L) (m : PriceVar T → ℕ) (l : L) : ℕ :=
  ∑ v ∈ kindSet kind l, m v

theorem degreeOf_of_mem {kind : PriceVar T → Option L} {n : L → ℕ} {m : PriceVar T → ℕ}
    (hm : m ∈ kindMonos kind n) : degreeOf kind m = n :=
  funext fun l => (mem_kindMonos.mp hm).2 l

/-- The bound `b_ω` of every selection after the replacement: the class bound `φ_ω`
of (v) on the replaced classes, `c_ω π_ω` on all other selections. -/
noncomputable def replacedBound (kind : PriceVar T → Option L) (N : Finset (L → ℕ))
    (C : (L → ℕ) → ℝ) (B' : ℝ) (yarm ylead yrem : PriceVar T → ℝ) (cost : Choice T → ℝ)
    (π : ∀ b, T b → ChangeType → ℝ) (ω : Choice T) : ℝ :=
  if selMono ω ∈ N.biUnion (kindMonos kind) then
    replacementBound (C (degreeOf kind (selMono ω))) B' yarm ylead yrem ω
  else cost ω * monomial π ω

/-- The sum of the bounds `b_ω` splits into the selections outside the replaced classes
and the classes `𝒞_n`, `n ∈ N`. -/
theorem sum_replacedBound (kind : PriceVar T → Option L) (N : Finset (L → ℕ))
    (C : (L → ℕ) → ℝ) (B' : ℝ) (yarm ylead yrem : PriceVar T → ℝ) (cost : Choice T → ℝ)
    (π : ∀ b, T b → ChangeType → ℝ) :
    ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω),
        replacedBound kind N C B' yarm ylead yrem cost π ω =
      ∑ ω ∈ (univ.filter fun ω : Choice T => IsSelection ω).filter
          (fun ω => ∀ n ∈ N, selMono ω ∉ kindMonos kind n), cost ω * monomial π ω +
        ∑ n ∈ N, ∑ ω ∈ degreeClass kind n, replacementBound (C n) B' yarm ylead yrem ω := by
  classical
  set U := N.biUnion (kindMonos kind) with hUdef
  set sel := univ.filter (fun ω : Choice T => IsSelection ω) with hseldef
  rw [← Finset.sum_filter_add_sum_filter_not sel (fun ω => selMono ω ∈ U), add_comm]
  congr 1
  · rw [Finset.filter_congr (q := fun ω => ∀ n ∈ N, selMono ω ∉ kindMonos kind n)]
    · apply sum_congr rfl
      intro ω hω
      rw [mem_filter] at hω
      unfold replacedBound
      have hnot : selMono ω ∉ U := by
        intro hU
        obtain ⟨n, hn, hmn⟩ := mem_biUnion.mp hU
        exact hω.2 n hn hmn
      rw [← hUdef, ite_eq_right hnot]
    · intro ω _
      constructor
      · intro h n hn hmn
        exact h (mem_biUnion.mpr ⟨n, hn, hmn⟩)
      · intro h hU
        obtain ⟨n, hn, hmn⟩ := mem_biUnion.mp hU
        exact h n hn hmn
  · have hset : sel.filter (fun ω => selMono ω ∈ U) = N.biUnion (degreeClass kind) := by
      ext ω
      simp only [mem_filter, mem_biUnion, degreeClass, hUdef, hseldef]
      constructor
      · rintro ⟨h1, n, hn, hmn⟩
        exact ⟨n, hn, h1, hmn⟩
      · rintro ⟨n, hn, h1, hmn⟩
        exact ⟨h1, n, hn, hmn⟩
    have hdisj : (N : Set (L → ℕ)).PairwiseDisjoint (degreeClass kind) := by
      intro n _ n' _ h
      rw [Function.onFun, Finset.disjoint_left]
      intro ω hω hω'
      exact Finset.disjoint_left.mp (kindMonos_disjoint (kind := kind) h)
        (mem_filter.mp hω).2 (mem_filter.mp hω').2
    rw [hset, sum_biUnion hdisj]
    apply sum_congr rfl
    intro n _
    apply sum_congr rfl
    intro ω hω
    have hmn : selMono ω ∈ kindMonos kind n := (mem_filter.mp hω).2
    unfold replacedBound
    rw [degreeOf_of_mem hmn]
    have hU : selMono ω ∈ U := mem_biUnion.mpr ⟨n, by assumption, hmn⟩
    rw [← hUdef, ite_eq_left hU]

/-- **Reserved cost with replaced degree classes** (`lem:record:record-expansion`
(ii), (iii), (v)): if every selection satisfies the summed bound
`∑_ω |I_ω| ≤ ∑_ω ((b_ω + z π_ω) Y + r_ω)` with `b_ω` the class bound of (v) on the
replaced classes and `c_ω π_ω` elsewhere (`replacedBound`; for instance from
`sum_abs_le_of_classes`), then with upper prices and upper auxiliary prices
`|Y_ν - Y_λ| ≤ (Ψ(π̂, ŷ) + z(e^Ŝ cosh Â - 1)) Y + ∑_ω r_ω`,
`Ψ = B'(e^{S(x)} cosh A(x) - 1) - 𝒟(x) - ∑_{n ∈ N} saving_n(x, y)`. -/
theorem abs_energy_sub_le_replacement (c : ReflectionCut V)
    {ν lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    {ζ : ∀ b, T b → ChangeType → ((V → X b) → ℝ) →ₗ[ℝ] ℝ}
    (hν : ∀ b, ν b = lam b + ∑ t, (ζ b t .sym + ζ b t .skew))
    (hlam : ∀ b, IsSymmetricAt c (lam b)) (hs : ∀ b t, IsSymmetricAt c (ζ b t .sym))
    (ha : ∀ b t, IsSkewAt c (ζ b t .skew)) (F : (∀ b, X b) → ℝ)
    {π πu : ∀ b, T b → ChangeType → ℝ} (hπ : ∀ b t e, 0 ≤ π b t e)
    (hle : ∀ b t e, π b t e ≤ πu b t e)
    (kind : PriceVar T → Option L) (hkind : ∀ v l, kind v = some l → v.2.2 = .skew)
    (N : Finset (L → ℕ)) (hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l))
    (C : (L → ℕ) → ℝ) (hC : ∀ n ∈ N, 0 ≤ C n)
    {yarm ylead yrem yarmu yleadu yremu : PriceVar T → ℝ}
    (harm : ∀ v, 0 ≤ yarm v) (hlead : ∀ v, 0 ≤ ylead v) (hrem : ∀ v, 0 ≤ yrem v)
    (harmu : ∀ v, yarm v ≤ yarmu v) (hleadu : ∀ v, ylead v ≤ yleadu v)
    (hremu : ∀ v, yrem v ≤ yremu v)
    (cost : Choice T → ℝ)
    (hcost : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) → 0 ≤ cost ω)
    {B' : ℝ} (hB' : 0 ≤ B')
    (supp : Finset (PriceVar T → ℕ)) (d : (PriceVar T → ℕ) → ℝ) (hd : ∀ m, 0 ≤ d m)
    (hd0 : ∀ n ∈ N, ∀ m ∈ kindMonos kind n, d m = 0)
    (hsel : ∀ ω, IsSelection ω → (∀ n ∈ N, selMono ω ∉ kindMonos kind n) →
      d (selMono ω) ≤ B' - cost ω)
    (hoth : ∀ m, (∀ ω, IsSelection ω → selMono ω ≠ m) → d m ≤ B' * expCoeff m)
    {z Y : ℝ} (hz : 0 ≤ z) (hY : 0 ≤ Y) (r : Choice T → ℝ)
    (hsum : ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), |term lam ζ F ω| ≤
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω),
        ((replacedBound kind N C B' yarm ylead yrem cost π ω + z * monomial π ω) * Y + r ω)) :
    |diagonalIntegral (tensorLaw ν) F - diagonalIntegral (tensorLaw lam) F| ≤
      (B' * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) -
          ∑ m ∈ supp, d m * mono (priceVec πu) m -
          ∑ n ∈ N, replacementSaving kind n (C n) B' (priceVec πu) yarmu yleadu yremu +
        z * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1)) * Y +
      ∑ ω ∈ univ.filter (fun ω : Choice T => IsSelection ω), r ω := by
  have hrep := replacement_le_upper hπ hle kind hkind N hN C hC harm hlead hrem harmu hleadu
    hremu cost hcost hB' supp d hd hd0 hsel hoth
  rw [← sum_replacedBound] at hrep
  have hmain := abs_energy_sub_le_of_complete c hν hlam hs ha F hπ hz hY
    (replacedBound kind N C B' yarm ylead yrem cost π) r hsum hrep
  have hmono := exp_cosh_mono hπ hle
  have h3 : z * (Real.exp (∑ b, symTotal π b) * Real.cosh (∑ b, skewTotal π b) - 1) * Y ≤
      z * (Real.exp (∑ b, symTotal πu b) * Real.cosh (∑ b, skewTotal πu b) - 1) * Y := by
    apply mul_le_mul_of_nonneg_right _ hY
    apply mul_le_mul_of_nonneg_left _ hz
    linarith
  nlinarith

end Energy

end Sarkozy.RecordExpansion

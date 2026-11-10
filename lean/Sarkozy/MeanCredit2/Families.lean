module

public import Sarkozy.MeanCredit.All

@[expose] public section






open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.MeanCredit

theorem hasSum_exp_series (z : ℝ) : HasSum (fun n : ℕ => z ^ n / n.factorial) (Real.exp z) := by
  have h := NormedSpace.expSeries_div_hasSum_exp (𝔸 := ℝ) z
  rwa [← Real.exp_eq_exp_ℝ] at h

/-- The outside-background coefficient: `a_j` on a pure invariant background (`k = 0` generic
factors) of invariant degree `j ≤ J`, `a₀` otherwise. -/
def bg (a : ℕ → ℝ) (a0 : ℝ) (J j k : ℕ) : ℝ := if k = 0 ∧ j ≤ J then a j else a0

/-- **The completed outside background** (`prop:joint-middle-mean`: `F_η`, `F_ζ`, `B_ρ`): with
invariant total `V` and generic total `G`,
`∑_{j,k} bg(j,k) V^j/j! G^k/k! = a₀ e^{V+G} + ∑_{j ≤ J} (a_j − a₀) V^j/j!`. -/
theorem hasSum_bg (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (V G : ℝ) :
    HasSum (fun p : ℕ × ℕ => bg a a0 J p.1 p.2 * (V ^ p.1 / p.1.factorial *
        (G ^ p.2 / p.2.factorial)))
      (a0 * Real.exp (V + G) + ∑ j ∈ range (J + 1), (a j - a0) * (V ^ j / j.factorial)) := by
  have hV' := hasSum_exp_series V
  have hG' := hasSum_exp_series G
  have hsum : Summable fun p : ℕ × ℕ => V ^ p.1 / p.1.factorial * (G ^ p.2 / p.2.factorial) :=
    summable_mul_of_summable_norm (f := fun n : ℕ => V ^ n / (n.factorial : ℝ))
      (g := fun n : ℕ => G ^ n / (n.factorial : ℝ)) (summable_norm_iff.mpr hV'.summable)
      (summable_norm_iff.mpr hG'.summable)
  have h1 := (hV'.mul hG' hsum).mul_left a0
  set f : ℕ × ℕ → ℝ := fun p => if p.2 = 0 ∧ p.1 ≤ J then
    (a p.1 - a0) * (V ^ p.1 / p.1.factorial * (G ^ p.2 / p.2.factorial)) else 0 with hf
  have h2 : HasSum f (∑ j ∈ range (J + 1), (a j - a0) * (V ^ j / j.factorial)) := by
    have h : HasSum f (∑ p ∈ range (J + 1) ×ˢ {0}, f p) :=
      hasSum_sum_of_ne_finset_zero (fun p hp => by
      have hc : ¬ (p.2 = 0 ∧ p.1 ≤ J) := by
        intro hc
        apply hp
        rw [mem_product, mem_range, mem_singleton]
        exact ⟨by omega, hc.1⟩
      simp only [hf, hc, ↓reduceIte])
    convert h using 1
    rw [sum_product]
    refine sum_congr rfl fun j hj => ?_
    rw [sum_singleton]
    have hj' : j ≤ J := by rw [mem_range] at hj; omega
    simp [hf, hj']
  convert h1.add h2 using 1
  · funext p
    simp only [bg, hf]
    split_ifs <;> ring
  · rw [Real.exp_add]

/-! ## The letters of the joint middle mean -/

/-- The letters of the joint middle mean (`prop:joint-middle-mean`): a fold arm `F` (raw coordinate,
total `x`), an outside `𝖤` factor `O` (total `w`), a matching arm `E` (total `x`), a `K_s` factor
`K` (total `y = σx`), an invariant outside factor `I` (total `V`), a generic outside factor `G`
(total `U − V`). -/
inductive MLetter
  | F | O | E | K | I | G
  deriving DecidableEq

instance : Fintype MLetter where
  elems := {.F, .O, .E, .K, .I, .G}
  complete x := by cases x <;> simp

theorem prod_mletter {M : Type*} [CommMonoid M] (h : MLetter → M) :
    ∏ l, h l = h .F * h .O * h .E * h .K * h .I * h .G := by
  change ∏ l ∈ {MLetter.F, .O, .E, .K, .I, .G}, h l = _
  rw [prod_insert (by decide), prod_insert (by decide), prod_insert (by decide),
    prod_insert (by decide), prod_pair (by decide)]
  simp only [mul_assoc]

/-- The letter degree with the given counts. -/
def mdeg (f o e k i g : ℕ) : MLetter → ℕ
  | .F => f
  | .O => o
  | .E => e
  | .K => k
  | .I => i
  | .G => g

/-- The letter totals. -/
def mTot (x w y V Gt : ℝ) : MLetter → ℝ
  | .F => x
  | .O => w
  | .E => x
  | .K => y
  | .I => V
  | .G => Gt

theorem prod_mdeg (x w y V Gt : ℝ) (f o e k i g : ℕ) :
    ∏ l, mTot x w y V Gt l ^ mdeg f o e k i g l / (mdeg f o e k i g l).factorial =
      x ^ f / f.factorial * (w ^ o / o.factorial) * (x ^ e / e.factorial) *
        (y ^ k / k.factorial) * (V ^ i / i.factorial * (Gt ^ g / g.factorial)) := by
  rw [prod_mletter]
  simp only [mTot, mdeg]
  ring

/-- **A family's mean coefficient on the letter degrees**: on the degrees
`f F + o O + e E + k K + j I + g G` the background coefficient `bg a a₀ J j g`, `0` elsewhere. -/
noncomputable def famCoef (f o e k : ℕ) (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (d : MLetter → ℕ) : ℝ :=
  if d = mdeg f o e k (d .I) (d .G) then bg a a0 J (d .I) (d .G) else 0

theorem mdeg_injective (f o e k : ℕ) :
    Function.Injective fun p : ℕ × ℕ => mdeg f o e k p.1 p.2 := by
  intro p q h
  have h1 := congrFun h .I
  have h2 := congrFun h .G
  simp only [mdeg] at h1 h2
  exact Prod.ext h1 h2

/-- **A family, completed**: `∑_d famCoef(d) X^d/d! = (x^f/f!)(w^o/o!)(x^e/e!)(y^k/k!) ·
(a₀ e^{V + G} + ∑_{j ≤ J} (a_j − a₀) V^j/j!)`. -/
theorem hasSum_fam (f o e k : ℕ) (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (x w y V Gt : ℝ) :
    HasSum (fun d => famCoef f o e k a a0 J d *
        ∏ l, mTot x w y V Gt l ^ d l / (d l).factorial)
      (x ^ f / f.factorial * (w ^ o / o.factorial) * (x ^ e / e.factorial) *
        (y ^ k / k.factorial) *
        (a0 * Real.exp (V + Gt) + ∑ j ∈ range (J + 1), (a j - a0) * (V ^ j / j.factorial))) := by
  have h := (hasSum_bg a a0 J V Gt).mul_left (x ^ f / f.factorial * (w ^ o / o.factorial) *
    (x ^ e / e.factorial) * (y ^ k / k.factorial))
  rw [← (mdeg_injective f o e k).hasSum_iff]
  · convert h using 1
    funext p
    have e1 : mdeg f o e k p.1 p.2 .I = p.1 := rfl
    have e2 : mdeg f o e k p.1 p.2 .G = p.2 := rfl
    simp only [Function.comp, famCoef, e1, e2, ↓reduceIte, prod_mdeg]
    ring
  · intro d hd
    have hne : d ≠ mdeg f o e k (d .I) (d .G) := fun h' => hd ⟨(d .I, d .G), h'.symm⟩
    simp [famCoef, hne]

/-! ## The paper's middle mean coefficient and its completion -/

open Sarkozy.ClassData

/-- The family-(ii) background coefficients `η_{j+2}` (`j ≤ 8`), `η₀`. -/
noncomputable def aEta (j : ℕ) : ℝ := (etaQ (j + 2) : ℝ)
/-- The family-(iii) background coefficients `ζ_{j+1}` (`j ≤ 8`), `ζ₀`. -/
noncomputable def aZeta (j : ℕ) : ℝ := (zetaQ (j + 1) : ℝ)
/-- The family-(iv) background coefficients `ρ^j` (`j ≤ 10`), `1`. -/
noncomputable def aRho (j : ℕ) : ℝ := (rhoQ : ℝ) ^ j

/-- **The four families with separate letters** (a series identity only; the booking uses `mPaper`,
which letters every entry once): family (i) `4/(H_*² C(j+2,2))` on `2F + jO`; family (ii) `η` on
`2E + jI + kG`;
family (iii) `ζ` on `nK + E + jI + kG`, `n = 1, 3, 5`; family (iv) `ρ^j` on `nK + jI + kG`,
`n = 2, 4, 6` (the finite improvements on pure invariant backgrounds, the uniform constants
`η₀`, `ζ₀`, `1` otherwise). The supports are disjoint. -/
noncomputable def mPaperSep (d : MLetter → ℕ) : ℝ :=
  meanFI (hStar : ℝ) MLetter.F MLetter.O d +
  famCoef 0 0 2 0 aEta (eta0 : ℝ) 8 d +
  (famCoef 0 0 1 1 aZeta (zeta0 : ℝ) 8 d + famCoef 0 0 1 3 aZeta (zeta0 : ℝ) 8 d +
    famCoef 0 0 1 5 aZeta (zeta0 : ℝ) 8 d) +
  (famCoef 0 0 0 2 aRho 1 10 d + famCoef 0 0 0 4 aRho 1 10 d + famCoef 0 0 0 6 aRho 1 10 d)

/-- The value of a background family: `core · (a₀ e^U + ∑_{j ≤ J} (a_j − a₀) V^j/j!)`. -/
noncomputable def bgVal (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (U V : ℝ) : ℝ :=
  a0 * Real.exp U + ∑ j ∈ range (J + 1), (a j - a0) * (V ^ j / j.factorial)

/-- **The completed middle mean** `64 (Δ_α + Δ_M + Δ_O + Δ_K)` (`eq:joint-alpha`,
`eq:joint-middle`), as a function of the totals `x`, `w`, `y`, `U`, `V`. -/
noncomputable def meanValue (x w y U V : ℝ) : ℝ :=
  64 * (x ^ 2 / (16 * (hStar : ℝ) ^ 2) * ((Real.exp w - 1 - w) / w ^ 2)) +
  x ^ 2 / 2 * bgVal aEta (eta0 : ℝ) 8 U V +
  (x * y + x * (y ^ 3 / 6) + x * (y ^ 5 / 120)) * bgVal aZeta (zeta0 : ℝ) 8 U V +
  (y ^ 2 / 2 + y ^ 4 / 24 + y ^ 6 / 720) * bgVal aRho 1 10 U V

/-- **The four families with separate letters, completed**: with the letter totals
`x, w, x, y, V, U − V`, `∑_d mPaperSep(d) X^d/d! = 64 (Δ_α + Δ_M + Δ_O + Δ_K)`. This counts the
outside mass twice (`O` and `I + G`) and the fold mass twice (`F` and `K`), so it is a series
identity only. -/
theorem hasSum_mPaperSep (x w y U V : ℝ) (hw : w ≠ 0) :
    HasSum (fun d => mPaperSep d * ∏ l, mTot x w y V (U - V) l ^ d l / (d l).factorial)
      (meanValue x w y U V) := by
  have hH : (hStar : ℝ) ≠ 0 := by norm_num [hStar]
  have h1 := hasSum_meanFI (hStar : ℝ) hH (F := MLetter.F) (O := MLetter.O) (by decide)
    (mTot x w y V (U - V)) hw
  have hU : V + (U - V) = U := by ring
  have h2 := hasSum_fam 0 0 2 0 aEta (eta0 : ℝ) 8 x w y V (U - V)
  have h31 := hasSum_fam 0 0 1 1 aZeta (zeta0 : ℝ) 8 x w y V (U - V)
  have h33 := hasSum_fam 0 0 1 3 aZeta (zeta0 : ℝ) 8 x w y V (U - V)
  have h35 := hasSum_fam 0 0 1 5 aZeta (zeta0 : ℝ) 8 x w y V (U - V)
  have h42 := hasSum_fam 0 0 0 2 aRho 1 10 x w y V (U - V)
  have h44 := hasSum_fam 0 0 0 4 aRho 1 10 x w y V (U - V)
  have h46 := hasSum_fam 0 0 0 6 aRho 1 10 x w y V (U - V)
  rw [hU] at h2 h31 h33 h35 h42 h44 h46
  have h := h1.add (h2.add ((h31.add (h33.add h35)).add (h42.add (h44.add h46))))
  convert h using 1
  · funext d
    simp only [mPaperSep]
    ring
  · simp only [meanValue, bgVal, mTot, Nat.factorial]
    norm_num
    ring

/-- `ℕ × ℕ` as the antidiagonals. -/
def antiEquiv : (Σ n : ℕ, Fin (n + 1)) ≃ ℕ × ℕ where
  toFun p := (p.2.val, p.1 - p.2.val)
  invFun q := ⟨q.1 + q.2, ⟨q.1, by omega⟩⟩
  left_inv p := by
    obtain ⟨n, j, hj⟩ := p
    simp only
    have h : j + (n - j) = n := by omega
    ext
    · exact h
    · exact (Fin.heq_ext_iff (by dsimp only; omega)).mpr rfl
  right_inv q := by
    obtain ⟨j, k⟩ := q
    simp

/-- The binomial theorem with factorials: `∑_{j ≤ n} V^j/j! G^{n−j}/(n−j)! = (V+G)^n/n!`. -/
theorem sum_fin_binom (V G : ℝ) (n : ℕ) :
    ∑ j : Fin (n + 1), V ^ (j : ℕ) / (j : ℕ).factorial * (G ^ (n - j) / (n - j).factorial) =
      (V + G) ^ n / n.factorial := by
  rw [Fin.sum_univ_eq_sum_range (fun j => V ^ j / j.factorial * (G ^ (n - j) /
    (n - j).factorial)), add_pow, sum_div]
  refine sum_congr rfl fun j hj => ?_
  have hjn : j ≤ n := by rw [mem_range] at hj; omega
  have h := Nat.choose_mul_factorial_mul_factorial hjn
  have hf : (n.factorial : ℝ) = (n.choose j : ℝ) * j.factorial * (n - j).factorial := by
    exact_mod_cast h.symm
  have h1 : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos j).ne'
  have h2 : ((n - j).factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
  have h3 : (n.choose j : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hjn).ne'
  rw [hf]
  field_simp

/-- **Completion over two outside letters of a coefficient of the total outside degree**:
`∑_{j,k} a_{j+k} V^j/j! G^k/k! = ∑_n a_n (V+G)^n/n!`, for `a ≥ 0`, `V, G ≥ 0`. -/
theorem hasSum_antidiag (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (V G : ℝ) (hV : 0 ≤ V) (hG : 0 ≤ G)
    (s : ℝ) (h : HasSum (fun n => a n * ((V + G) ^ n / n.factorial)) s) :
    HasSum (fun p : ℕ × ℕ => a (p.1 + p.2) * (V ^ p.1 / p.1.factorial *
      (G ^ p.2 / p.2.factorial))) s := by
  set f : (Σ n : ℕ, Fin (n + 1)) → ℝ := fun p => a p.1 * (V ^ (p.2 : ℕ) /
    (p.2 : ℕ).factorial * (G ^ (p.1 - p.2) / (p.1 - p.2).factorial)) with hf
  have hfib : ∀ n, HasSum (fun j : Fin (n + 1) => f ⟨n, j⟩)
      (a n * ((V + G) ^ n / n.factorial)) := by
    intro n
    have := hasSum_fintype (fun j : Fin (n + 1) => f ⟨n, j⟩)
    have e : ∑ j : Fin (n + 1), f ⟨n, j⟩ = a n * ((V + G) ^ n / n.factorial) := by
      simp only [hf]
      rw [← mul_sum, sum_fin_binom]
    rwa [e] at this
  have hf0 : ∀ p, 0 ≤ f p := fun p => mul_nonneg (ha _) (by positivity)
  have hsum : Summable f := by
    rw [summable_sigma_of_nonneg hf0]
    refine ⟨fun n => (hfib n).summable, ?_⟩
    have e : (fun n => ∑' j : Fin (n + 1), f ⟨n, j⟩) =
        fun n => a n * ((V + G) ^ n / n.factorial) := funext fun n => (hfib n).tsum_eq
    rw [e]
    exact h.summable
  have hs : HasSum f s := HasSum.sigma_of_hasSum h hfib hsum
  rw [← antiEquiv.hasSum_iff]
  convert hs using 1
  funext p
  obtain ⟨n, j, hj⟩ := p
  simp only [Function.comp, antiEquiv, Equiv.coe_fn_mk, hf]
  have : j + (n - j) = n := by omega
  rw [this]

/-! ## The paper's lettering: every entry has one letter -/

/-- **Family (i) on the comparison's letters** (`prop:joint-middle-mean`, family (i)): on
`2F + jI + kG`, the per-pair coefficient `4/(H_*² C(j+k+2,2))` times `r^{j+k}`, the share of the
outside mass assigned to `𝖤` (`r = 1/(1+ρ_H)`: "an `𝖤` assignment at least `U/(1+ρ_H)`"). -/
noncomputable def famI (r : ℝ) (d : MLetter → ℕ) : ℝ :=
  if d = mdeg 2 0 0 0 (d .I) (d .G) then
    4 / ((hStar : ℝ) ^ 2 * (Nat.choose (d .I + d .G + 2) 2 : ℝ)) * r ^ (d .I + d .G) else 0

theorem hasSum_famI (r : ℝ) (hr : 0 ≤ r) (x V Gt : ℝ) (hV : 0 ≤ V) (hG : 0 ≤ Gt)
    (hw : r * (V + Gt) ≠ 0) :
    HasSum (fun d => famI r d * ∏ l, mTot x 0 0 V Gt l ^ d l / (d l).factorial)
      (64 * (x ^ 2 / (16 * (hStar : ℝ) ^ 2) *
        ((Real.exp (r * (V + Gt)) - 1 - r * (V + Gt)) / (r * (V + Gt)) ^ 2))) := by
  have hH : (hStar : ℝ) ≠ 0 := by norm_num [hStar]
  set a : ℕ → ℝ := fun n => 4 / ((hStar : ℝ) ^ 2 * (Nat.choose (n + 2) 2 : ℝ)) * r ^ n *
    (x ^ 2 / 2) with ha
  have ha0 : ∀ n, 0 ≤ a n := fun n => by
    have : (0 : ℝ) < Nat.choose (n + 2) 2 := by exact_mod_cast Nat.choose_pos (by omega)
    simp only [ha]
    positivity
  have h1 := hasSum_familyI (hStar : ℝ) x (r * (V + Gt)) hH hw
  have h2 : HasSum (fun n => a n * ((V + Gt) ^ n / n.factorial))
      (64 * (x ^ 2 / (16 * (hStar : ℝ) ^ 2) *
        ((Real.exp (r * (V + Gt)) - 1 - r * (V + Gt)) / (r * (V + Gt)) ^ 2))) := by
    convert h1 using 1
    funext n
    simp only [ha]
    rw [mul_pow]
    ring
  have h3 := hasSum_antidiag a ha0 V Gt hV hG _ h2
  rw [← (mdeg_injective 2 0 0 0).hasSum_iff]
  · convert h3 using 1
    funext p
    have e1 : mdeg 2 0 0 0 p.1 p.2 .I = p.1 := rfl
    have e2 : mdeg 2 0 0 0 p.1 p.2 .G = p.2 := rfl
    simp only [Function.comp, famI, e1, e2, ↓reduceIte, prod_mdeg, ha]
    simp
    ring
  · intro d hd
    have hne : d ≠ mdeg 2 0 0 0 (d .I) (d .G) := fun h' => hd ⟨(d .I, d .G), h'.symm⟩
    simp [famI, hne]

theorem bgVal_smul (c : ℝ) (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (U V : ℝ) :
    bgVal (fun j => c * a j) (c * a0) J U V = c * bgVal a a0 J U V := by
  unfold bgVal
  rw [mul_add, mul_sum]
  congr 1
  · ring
  · exact sum_congr rfl fun j _ => by ring

/-- **The paper's middle mean coefficient on the comparison's letters** (`prop:joint-middle-mean`,
families (i)–(iv) and the residual table): every entry has one letter: fold arm `F`, matching arm
`E` (raw-arm total `x` each), invariant outside `I` (`V`), generic outside `G` (`U − V`).
* family (i): `famI r` on `2F + jI + kG`;
* family (ii): `η` on `2E + jI + kG`;
* family (iii): `σ^f ζ` on `fF + E + jI + kG`, `f = 1, 3, 5`;
* family (iv): `σ^f ρ^j` on `fF + jI + kG`, `f = 2, 4, 6`.
The `F²` degrees carry families (i) and (iv) together, as in the table ("The `F²` entries are
added"). The letters `O`, `K` are not used (total `0`). -/
noncomputable def mPaper (r : ℝ) (d : MLetter → ℕ) : ℝ :=
  famI r d +
  famCoef 0 0 2 0 aEta (eta0 : ℝ) 8 d +
  (famCoef 1 0 1 0 (fun j => (sigmaQ : ℝ) * aZeta j) ((sigmaQ : ℝ) * zeta0) 8 d +
    famCoef 3 0 1 0 (fun j => (sigmaQ : ℝ) ^ 3 * aZeta j) ((sigmaQ : ℝ) ^ 3 * zeta0) 8 d +
    famCoef 5 0 1 0 (fun j => (sigmaQ : ℝ) ^ 5 * aZeta j) ((sigmaQ : ℝ) ^ 5 * zeta0) 8 d) +
  (famCoef 2 0 0 0 (fun j => (sigmaQ : ℝ) ^ 2 * aRho j) ((sigmaQ : ℝ) ^ 2 * 1) 10 d +
    famCoef 4 0 0 0 (fun j => (sigmaQ : ℝ) ^ 4 * aRho j) ((sigmaQ : ℝ) ^ 4 * 1) 10 d +
    famCoef 6 0 0 0 (fun j => (sigmaQ : ℝ) ^ 6 * aRho j) ((sigmaQ : ℝ) ^ 6 * 1) 10 d)

/-- **The completion of the paper's middle mean coefficient** (`prop:joint-middle-mean`): with the
letter totals `x` (`F`, `E`), `V` (`I`), `U − V` (`G`) and `0` (`O`, `K`),
`∑_d mPaper(d) X^d/d! = 64 (Δ_α + Δ_M + Δ_O + Δ_K)` at `w = rU`, `y = σx`. -/
theorem hasSum_mPaper (r : ℝ) (hr : 0 ≤ r) (x U V : ℝ) (hV : 0 ≤ V) (hVU : V ≤ U)
    (hw : r * U ≠ 0) :
    HasSum (fun d => mPaper r d * ∏ l, mTot x 0 0 V (U - V) l ^ d l / (d l).factorial)
      (meanValue x (r * U) ((sigmaQ : ℝ) * x) U V) := by
  have hU : V + (U - V) = U := by ring
  have h1 := hasSum_famI r hr x V (U - V) hV (by linarith) (by rw [hU]; exact hw)
  have h2 := hasSum_fam 0 0 2 0 aEta (eta0 : ℝ) 8 x 0 0 V (U - V)
  have h31 := hasSum_fam 1 0 1 0 (fun j => (sigmaQ : ℝ) * aZeta j) ((sigmaQ : ℝ) * zeta0) 8
    x 0 0 V (U - V)
  have h33 := hasSum_fam 3 0 1 0 (fun j => (sigmaQ : ℝ) ^ 3 * aZeta j) ((sigmaQ : ℝ) ^ 3 * zeta0)
    8 x 0 0 V (U - V)
  have h35 := hasSum_fam 5 0 1 0 (fun j => (sigmaQ : ℝ) ^ 5 * aZeta j) ((sigmaQ : ℝ) ^ 5 * zeta0)
    8 x 0 0 V (U - V)
  have h42 := hasSum_fam 2 0 0 0 (fun j => (sigmaQ : ℝ) ^ 2 * aRho j) ((sigmaQ : ℝ) ^ 2 * 1) 10
    x 0 0 V (U - V)
  have h44 := hasSum_fam 4 0 0 0 (fun j => (sigmaQ : ℝ) ^ 4 * aRho j) ((sigmaQ : ℝ) ^ 4 * 1) 10
    x 0 0 V (U - V)
  have h46 := hasSum_fam 6 0 0 0 (fun j => (sigmaQ : ℝ) ^ 6 * aRho j) ((sigmaQ : ℝ) ^ 6 * 1) 10
    x 0 0 V (U - V)
  rw [hU] at h1 h2 h31 h33 h35 h42 h44 h46
  have h := h1.add (h2.add ((h31.add (h33.add h35)).add (h42.add (h44.add h46))))
  convert h using 1
  · funext d
    simp only [mPaper]
    ring
  · have e : ∀ (c : ℝ) (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ),
        c * a0 * Real.exp U + ∑ j ∈ range (J + 1), (c * a j - c * a0) * (V ^ j / j.factorial) =
          c * bgVal a a0 J U V := fun c a a0 J => by
      rw [← bgVal_smul]
      rfl
    simp only [e]
    simp only [meanValue, bgVal, Nat.factorial]
    norm_num
    ring

end Sarkozy.MeanCredit2

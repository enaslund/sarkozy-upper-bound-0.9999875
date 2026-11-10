module

public import Sarkozy.Moments.Holder
public import Sarkozy.Moments.Grouping
public import Sarkozy.Moments.Energy
public import Sarkozy.Moments.TensorMixed
public import Sarkozy.ProbabilityProducts
public import Sarkozy.Slots

/-!
# At most two copies per clique draw (`lem:density:clique-copies`)

`paper/sections/30_density_moment_upgrade.tex`. A random pair of labels `(A, B)` in a finite
alphabet `X` is given by a law `μ` on an index space `Ω` and two maps `a b : Ω → X`.
Conditional on it, labels are drawn independently and uniformly from `{A, B}`, one fair coin per
draw (`drawLaw`).

* `lem:density:clique36` says that 36 such draws have unit mixed `L^{600/17}` norm. It is a
  finite numeric certificate over 31 dyadic bands, and is a hypothesis here.
* `lem:density:clique-copies` says that if the 72 slots are filled from independent draws, each
  draw used at most twice (`copyLaw`), the slot law has unit mixed `L^{1200/17}` norm. The same
  holds after tensoring independent digit pairs and after a common random permutation of the
  alphabet.

The proof is the paper's:
1. conditional on `(A, B)` the draws are independent, so the slot product factorizes over draws
   (`expect_copyLaw_prod`);
2. Cauchy–Schwarz in each group of one or two slots (`abs_expect_prod_le_of_card_le_two`);
3. Hölder over `(A, B)` with `72` equal exponents;
4. the 36-draw bound, applied with every input equal to `|f_v|²`.

The general form, `mixedLpBound_copyLaw`, takes any number `d ≥ 1` of draws in the hypothesis,
`2d` slots and any exponent `R > 0`, and gives exponent `2R`. The paper's form is
`clique_copies_slots`.

For the tensor statement, `clique_copies_tensor` specializes `MixedLpBound.tensor`
(`Moments/TensorMixed.lean`). The permutation statement, `MixedLpBound.random_perm`, is proved
for any law on the permutations of the alphabet; the paper's square-affine maps are a special
case. The paper identifies `(ℤ/p²ℤ)^m` with `ℤ/p^{2m}ℤ`, which is a bijection of alphabets, and
mixed bounds transfer along any bijection (`MixedLpBound.map_equiv`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

namespace CliqueCopies

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]

/-- The label of a draw with coin `c`: `a ω` for `true`, `b ω` for `false`. -/
def label (a b : Ω → X) (ω : Ω) (c : Bool) : X := cond c (a ω) (b ω)

/-- The fair coin. -/
noncomputable abbrev coin : FiniteLaw Bool := FiniteLaw.uniform Bool

/-- The conditional average over one draw, `ν_ω g = (g (a ω) + g (b ω)) / 2`. -/
noncomputable def pairAvg (a b : Ω → X) (ω : Ω) (g : X → ℝ) : ℝ :=
  coin.expect (fun c => g (label a b ω c))

/-- Independent fair coins indexed by `T`. -/
noncomputable def coins (T : Type*) [Fintype T] [DecidableEq T] : FiniteLaw (T → Bool) :=
  FiniteLaw.pi (fun _ : T => coin)

/-- The law of draws indexed by `T`: draw `ω` from `μ` and independent fair coins `c`; draw
`t` is `label a b ω (c t)`. -/
noncomputable def drawLaw (μ : FiniteLaw Ω) (a b : Ω → X) (T : Type*) [Fintype T]
    [DecidableEq T] : FiniteLaw (T → X) :=
  (μ.product (coins T)).map (fun q t => label a b q.1 (q.2 t))

/-- The slot law: slot `v` receives draw `σ v`. -/
noncomputable def copyLaw (μ : FiniteLaw Ω) (a b : Ω → X) {T V : Type*} [Fintype T]
    [DecidableEq T] [Fintype V] [DecidableEq V] (σ : V → T) : FiniteLaw (V → X) :=
  (drawLaw μ a b T).map (fun y v => y (σ v))

/-- The conditional second moment of `f v` given `ω`. -/
noncomputable def condSecond {V : Type*} (a b : Ω → X) (f : V → X → ℝ) (v : V) (ω : Ω) : ℝ :=
  pairAvg a b ω (fun x => f v x ^ 2)

omit [Fintype Ω] [Fintype X] [DecidableEq X] in
theorem condSecond_nonneg {V : Type*} (a b : Ω → X) (f : V → X → ℝ) (v : V) (ω : Ω) :
    0 ≤ condSecond a b f v ω := by
  unfold condSecond pairAvg
  exact coin.expect_nonneg (fun _ => sq_nonneg _)

variable (μ : FiniteLaw Ω) (a b : Ω → X)

theorem expect_drawLaw {T : Type*} [Fintype T] [DecidableEq T] (F : (T → X) → ℝ) :
    (drawLaw μ a b T).expect F =
      μ.expect (fun ω => (coins T).expect (fun c => F (fun t => label a b ω (c t)))) := by
  rw [drawLaw, FiniteLaw.expect_map, FiniteLaw.expect_product]
  rfl

/-- Conditional independence of the draws. -/
theorem expect_drawLaw_prod {T : Type*} [Fintype T] [DecidableEq T] (g : T → X → ℝ) :
    (drawLaw μ a b T).expect (fun y => ∏ t, g t (y t)) =
      μ.expect (fun ω => ∏ t, pairAvg a b ω (g t)) := by
  rw [expect_drawLaw]
  apply μ.expect_congr
  intro ω
  exact FiniteLaw.expect_pi_product (fun _ : T => coin) (fun t c => g t (label a b ω c))

/-- The slot product, grouped by draw. -/
theorem expect_copyLaw_prod {T V : Type*} [Fintype T] [DecidableEq T] [Fintype V]
    [DecidableEq V] (σ : V → T) (f : V → X → ℝ) :
    (copyLaw μ a b σ).expect (fun z => ∏ v, f v (z v)) =
      μ.expect (fun ω => ∏ t, pairAvg a b ω
        (fun x => ∏ v ∈ univ.filter (fun v => σ v = t), f v x)) := by
  have h := expect_drawLaw_prod μ a b
    (fun t x => ∏ v ∈ univ.filter (fun v => σ v = t), f v x)
  rw [← h, copyLaw, FiniteLaw.expect_map]
  apply FiniteLaw.expect_congr
  intro y
  symm
  calc ∏ t, ∏ v ∈ univ.filter (fun v => σ v = t), f v (y t)
      = ∏ t, ∏ v ∈ univ.filter (fun v => σ v = t), f v (y (σ v)) := by
        refine prod_congr rfl fun t _ => prod_congr rfl fun v hv => ?_
        rw [(mem_filter.mp hv).2]
    _ = ∏ v, f v (y (σ v)) := prod_fiberwise univ σ (fun v => f v (y (σ v)))

end CliqueCopies

/-- **Cauchy–Schwarz in a group of at most two slots.** -/
theorem abs_expect_prod_le_of_card_le_two {Ξ V : Type*} [Fintype Ξ] (ν : FiniteLaw Ξ)
    (F : Finset V) (hF : F.card ≤ 2) (g : V → Ξ → ℝ) :
    |ν.expect (fun c => ∏ v ∈ F, g v c)| ≤
      ∏ v ∈ F, Real.sqrt (ν.expect (fun c => g v c ^ 2)) := by
  classical
  rcases Nat.lt_or_ge F.card 1 with h0 | h1
  · have hF0 : F = ∅ := card_eq_zero.mp (by omega : F.card = 0)
    subst hF0
    simp
  rcases Nat.lt_or_ge F.card 2 with h1' | h2
  · obtain ⟨v, rfl⟩ := card_eq_one.mp (by omega : F.card = 1)
    simp only [prod_singleton]
    have h := ν.abs_expect_mul_le (g v) (fun _ => 1)
    simpa using h
  · obtain ⟨v, w, hvw, rfl⟩ := card_eq_two.mp (by omega : F.card = 2)
    simp only [prod_pair hvw]
    exact ν.abs_expect_mul_le (g v) (g w)

/-- The `L^R` norm of a square is the square of the `L^{2R}` norm. -/
theorem uniform_lpNorm_sq {X : Type*} [Fintype X] [Nonempty X] {R : ℝ} (hR : 0 < R)
    (f : X → ℝ) :
    (FiniteLaw.uniform X).lpNorm R (fun x => f x ^ 2) =
      (FiniteLaw.uniform X).lpNorm (2 * R) f ^ 2 := by
  set ν := FiniteLaw.uniform X
  have hfun : (fun x => f x ^ 2) = (fun x => |f x| ^ (2 : ℝ)) := by
    funext x
    rw [Real.rpow_two, sq_abs]
  have hmom : ν.moment R (fun x => f x ^ 2) = ν.moment (2 * R) f := by
    rw [hfun, ν.moment_rpow_of_nonneg R 2 (fun x => abs_nonneg (f x))]
    unfold FiniteLaw.moment
    simp only [abs_abs]
  unfold FiniteLaw.lpNorm
  rw [hmom, ← Real.rpow_natCast, ← Real.rpow_mul (ν.moment_nonneg _ _)]
  congr 1
  push_cast
  field_simp

namespace CliqueCopies

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X] (μ : FiniteLaw Ω) (a b : Ω → X)

/-- **At most two copies per draw** (`lem:density:clique-copies`, general form). If `d ≥ 1`
draws have unit mixed `L^R` norm, then any filling of `2d` slots from independent draws, each
draw used at most twice, has unit mixed `L^{2R}` norm. -/
theorem mixedLpBound_copyLaw [Nonempty X] {D T V : Type*} [Fintype D] [DecidableEq D]
    [Nonempty D] [Fintype T] [DecidableEq T] [Fintype V] [DecidableEq V] {R : ℝ} (hR : 0 < R)
    (hdraw : MixedLpBound (drawLaw μ a b D) R 1)
    (hV : Fintype.card V = 2 * Fintype.card D)
    (σ : V → T) (hσ : ∀ t, (univ.filter (fun v => σ v = t)).card ≤ 2) :
    MixedLpBound (copyLaw μ a b σ) (2 * R) 1 := by
  intro f
  have hd : 0 < Fintype.card D := Fintype.card_pos
  have hnR : (0 : ℝ) < Fintype.card V := by exact_mod_cast (show 0 < Fintype.card V by omega)
  -- conditional factorization and Cauchy–Schwarz in each group
  have hB : |(copyLaw μ a b σ).expect (fun z => ∏ v, f v (z v))| ≤
      μ.expect (fun ω => ∏ v, Real.sqrt (condSecond a b f v ω)) := by
    rw [expect_copyLaw_prod]
    refine (μ.abs_expect_le _).trans (μ.expect_mono fun ω => ?_)
    rw [Finset.abs_prod]
    calc ∏ t, |pairAvg a b ω (fun x => ∏ v ∈ univ.filter (fun v => σ v = t), f v x)|
        ≤ ∏ t, ∏ v ∈ univ.filter (fun v => σ v = t), Real.sqrt (condSecond a b f v ω) := by
          apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
          intro t _
          exact abs_expect_prod_le_of_card_le_two coin _ (hσ t)
            (fun v c => f v (label a b ω c))
      _ = ∏ v, Real.sqrt (condSecond a b f v ω) :=
          prod_fiberwise univ σ (fun v => Real.sqrt (condSecond a b f v ω))
  -- Hölder over `ω` with `|V|` equal exponents
  have hsum : ∑ _v : V, 1 / (Fintype.card V : ℝ) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one_div_cancel hnR.ne']
  have hC : μ.expect (fun ω => ∏ v, Real.sqrt (condSecond a b f v ω)) ≤
      ∏ v, μ.lpNorm (Fintype.card V) (fun ω => Real.sqrt (condSecond a b f v ω)) :=
    (le_abs_self _).trans (μ.abs_expect_prod_le_lpNorm (fun _ : V => (Fintype.card V : ℝ))
      (fun _ => hnR) hsum (fun v ω => Real.sqrt (condSecond a b f v ω)))
  -- each factor, by the draw bound with input `|f_v|²`
  have hD : ∀ v, μ.lpNorm (Fintype.card V) (fun ω => Real.sqrt (condSecond a b f v ω)) ≤
      (FiniteLaw.uniform X).lpNorm (2 * R) (f v) := by
    intro v
    have hL0 : 0 ≤ (FiniteLaw.uniform X).lpNorm (2 * R) (f v) :=
      (FiniteLaw.uniform X).lpNorm_nonneg _ _
    have hmom : μ.moment (Fintype.card V) (fun ω => Real.sqrt (condSecond a b f v ω)) =
        (drawLaw μ a b D).expect (fun y => ∏ _t : D, f v (y _t) ^ 2) := by
      rw [expect_drawLaw_prod μ a b (fun _ x => f v x ^ 2)]
      unfold FiniteLaw.moment
      apply μ.expect_congr
      intro ω
      rw [abs_of_nonneg (Real.sqrt_nonneg _), Real.rpow_natCast, hV, pow_mul,
        Real.sq_sqrt (condSecond_nonneg a b f v ω), prod_const, card_univ]
      rfl
    have hle : (drawLaw μ a b D).expect (fun y => ∏ _t : D, f v (y _t) ^ 2) ≤
        (FiniteLaw.uniform X).lpNorm (2 * R) (f v) ^ Fintype.card V := by
      have h := hdraw (fun _ x => f v x ^ 2)
      rw [prod_const, card_univ, uniform_lpNorm_sq hR, one_mul, ← pow_mul, ← hV] at h
      exact (le_abs_self _).trans h
    have hnn : 0 ≤ (drawLaw μ a b D).expect (fun y => ∏ _t : D, f v (y _t) ^ 2) :=
      FiniteLaw.expect_nonneg _ (fun y => prod_nonneg fun _ _ => sq_nonneg _)
    unfold FiniteLaw.lpNorm
    rw [hmom]
    calc (drawLaw μ a b D).expect (fun y => ∏ _t : D, f v (y _t) ^ 2) ^
          (1 / (Fintype.card V : ℝ))
        ≤ ((FiniteLaw.uniform X).lpNorm (2 * R) (f v) ^ Fintype.card V) ^
            (1 / (Fintype.card V : ℝ)) :=
          Real.rpow_le_rpow hnn hle (by positivity)
      _ = (FiniteLaw.uniform X).lpNorm (2 * R) (f v) := by
          rw [one_div, Real.pow_rpow_inv_natCast hL0 (by omega)]
  calc |(copyLaw μ a b σ).expect (fun z => ∏ v, f v (z v))|
      ≤ ∏ v, μ.lpNorm (Fintype.card V) (fun ω => Real.sqrt (condSecond a b f v ω)) :=
        hB.trans hC
    _ ≤ ∏ v, (FiniteLaw.uniform X).lpNorm (2 * R) (f v) :=
        prod_le_prod₀ (fun v _ => μ.lpNorm_nonneg _ _) (fun v _ => hD v)
    _ = 1 * ∏ v, (FiniteLaw.uniform X).lpNorm (2 * R) (f v) := (one_mul _).symm

/-- **`lem:density:clique-copies`, the paper's form.** From unit mixed `L^{600/17}` for 36 draws
(`lem:density:clique36`), any filling of the 72 slots from independent draws, each used at most
twice, has unit mixed `L^{1200/17}` norm. -/
theorem clique_copies_slots [Nonempty X]
    (h36 : MixedLpBound (drawLaw μ a b (Fin 36)) (600 / 17) 1)
    {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T)
    (hσ : ∀ t, (univ.filter (fun v => σ v = t)).card ≤ 2) :
    MixedLpBound (copyLaw μ a b σ) (1200 / 17) 1 := by
  have h := mixedLpBound_copyLaw μ a b (by norm_num : (0 : ℝ) < 600 / 17) h36
    (by rw [card_slot, Fintype.card_fin]) σ hσ
  have he : (1200 / 17 : ℝ) = 2 * (600 / 17) := by norm_num
  rw [he]
  exact h

end CliqueCopies

/-- Uniform norms are preserved by a bijection of alphabets. -/
theorem uniform_lpNorm_comp_equiv {X Y : Type*} [Fintype X] [Fintype Y] [Nonempty X]
    [Nonempty Y] (e : X ≃ Y) (p : ℝ) (g : Y → ℝ) :
    (FiniteLaw.uniform X).lpNorm p (fun x => g (e x)) = (FiniteLaw.uniform Y).lpNorm p g := by
  unfold FiniteLaw.lpNorm FiniteLaw.moment
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, Fintype.card_congr e,
    e.sum_comp (fun y => |g y| ^ p)]

/-- **Mixed bounds transfer along a bijection of the alphabet**, applied in every slot. -/
theorem MixedLpBound.map_equiv {V X Y : Type*} [Fintype V] [DecidableEq V] [Fintype X]
    [Nonempty X] [Fintype Y] [DecidableEq Y] [Nonempty Y] {μ : FiniteLaw (V → X)} {p C : ℝ}
    (h : MixedLpBound μ p C) (e : X ≃ Y) :
    MixedLpBound (μ.map (fun z v => e (z v))) p C := by
  intro f
  rw [FiniteLaw.expect_map]
  have hf := h (fun v x => f v (e x))
  simp only [uniform_lpNorm_comp_equiv] at hf
  exact hf

/-- **A common random permutation of the alphabet preserves mixed bounds.** The permutation
`π` is drawn from any law `ρ`, independently of the labelling, and applied in every slot. -/
theorem MixedLpBound.random_perm {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X]
    [DecidableEq X] [Nonempty X] {μ : FiniteLaw (V → X)} {p C : ℝ} (h : MixedLpBound μ p C)
    (ρ : FiniteLaw (Equiv.Perm X)) :
    MixedLpBound ((ρ.product μ).map (fun q v => q.1 (q.2 v))) p C := by
  intro f
  rw [FiniteLaw.expect_map, FiniteLaw.expect_product]
  refine (ρ.abs_expect_le _).trans (ρ.expect_le_const fun π => ?_)
  have hπ := (h.map_equiv π) f
  rw [FiniteLaw.expect_map] at hπ
  exact hπ

/-- **Tensoring digit pairs** (`lem:density:clique-copies`, second assertion): unit mixed bounds
for independent digit pairs give a unit mixed bound for the tensor law on the full digit
vector, for arbitrary functions of it. -/
theorem clique_copies_tensor {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V]
    [DecidableEq V] {Y : J → Type*} [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)]
    [∀ j, Nonempty (Y j)] (ν : ∀ j, FiniteLaw (V → Y j)) {p : ℝ} (hp : 0 < p)
    (h : ∀ j, MixedLpBound (ν j) p 1) :
    MixedLpBound (FiniteLaw.tensor ν) p 1 := by
  simpa using MixedLpBound.tensor ν hp (fun _ => 1) (fun _ => zero_le_one) h

end Sarkozy

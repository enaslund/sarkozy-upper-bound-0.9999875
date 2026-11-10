module

public import Sarkozy.MiddleRecords.Channels
public import Sarkozy.MiddleRecords.TwoFeature

/-!
# Mirror pairing (`lem:mirror`)

`paper/sections/21_middle_records.tex`, `subsec:mirror`, `lem:mirror`. With the channels
`𝖠, 𝖡, 𝖢, 𝖣` of `Sarkozy.MiddleRecords.Channels` and `|F| ≡ 3 (mod 4)`:

* **(a)** `Sym Φ = Φ_s = (1+𝖠)(1+𝖡)𝖢𝖣`, `Skew Φ = Φ_a = (1+𝖠)(1+𝖡)(𝖢+𝖣)`, `Skew Φ' = 0` and
  `Sym Φ' = (1+𝖠)(1+𝖡)(𝖢-𝖣-𝖢𝖣)` (`mirror_a_sym`, `mirror_a_skew`, `mirror_a_skew'`,
  `mirror_a_sym'`), as identities of kernels at every pair of halves.
* **(b)** The monomial classification (`Chan`, `Chan.edge`, `starX`, `starY`, `IsStarMono`,
  `IsNonstar`): the stars are the channels at `x₀` and at `y₀` (`starX_eq`, `starY_eq`), with no
  common label (`stars_disjoint`); there are exactly nine nonstars, those of
  `lem:record:projected-nonstar` (`nonstars_eq`); the four monomials of `Φ_s` are nonstars
  containing the matching `{𝖢, 𝖣}` (`PhiS_monomials`, `matching_CD`); the split
  `Φ_a = L_p + Φ_{a,ns}` (`mirror_b_split`) with star part `L_p = 𝖢+𝖣+𝖠𝖣+𝖡𝖢`
  (`Lp_monomials_star`) and nonstar part `Φ_{a,ns} = 𝖠𝖢+𝖡𝖣+𝖠𝖡𝖢+𝖠𝖡𝖣` (`PhiAns_monomials`); and
  the expansion of `Φ_s` into its four monomials (`PhiS_expand`).
* **(c)**, the norm: the scalar part. Given the Gram data `V_0^* A_⋆ = λ I + β P`,
  `A_⋆^* A_⋆ = γ I` of `lem:paley-triple`(e) as a `TwoFeature` bundle (with `V = V_0`,
  `A = A_⋆`, so that `L_p = A_⋆ V_0^* - V_0 A_⋆^*` is `TwoFeature.skewOp`),
  `‖L_p‖ = |β| r + (γ - λ²)^{1/2}` is `TwoFeature.opNorm_skewOp`, and
  `|β| r + (γ - λ²)^{1/2} ≤ l` (`mirror_c_scalar`), hence `‖L_p w‖ ≤ l ‖w‖` (`mirror_c`).
  The kernel identity `L_p = A_⋆ V_0^* - V_0 A_⋆^*` on `L²(ν_F)` is
  `Sarkozy.MiddleRecords.Lt_form` (with `Lt_zero`). **Not formalized in (c):** the Gram data
  themselves as a `TwoFeature` bundle (they are in WP-S's `Sarkozy.TraceMixing.PaleyFeatures*` in
  weak form, but are not transported to an inner product space here), the annihilation of the
  constants, and the limit `l/r → √2`.
* **(d)** The signed pairing: `Φ_0 = Φ` (`PhiT_zero`), `Φ_t = (1+𝖡) x̃_t + (1+𝖠) ỹ_t + x̃_t ỹ_t`
  (`PhiT_eq`), `x̃_t^⊤ = -ỹ_t`, `ỹ_t^⊤ = -x̃_t` (`kerT_xt`, `kerT_yt`),
  `Sym Φ_t = x̃_t ỹ_t` (`mirror_d_sym`), `Skew Φ_t = L_{t,p} + K_t - K_t^⊤` (`mirror_d_skew`) with
  `L_{t,p} = x̃_t + ỹ_t` (`Lt_eq`); `x̃_t`, `ỹ_t` are the stated rectangular stars
  (`xt_rect`, `yt_rect`); `K_t` does not depend on `y₁` (`Kt_indep_y1`), and of its factors only
  `𝖢` depends on `x₁` (`Kt_eq`, `chA_indep_x1`, `chB_indep_x1`). The operator identity
  `L_{t,p} = A_t V_0^* - V_0 A_t^*` on `L²(ν_F)` is `Sarkozy.MiddleRecords.Lt_form`
  (`Sarkozy.MiddleRecords.MirrorKernel`).

All identities of (a), (b), (d) are proved for every `t : ℝ`; the paper's `0 ≤ t ≤ 1` is not
needed.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Kernels that are functions of the channels -/

/-- The kernel `(x, y) ↦ f(𝖠, 𝖡, 𝖢, 𝖣)`. -/
def chanKer (f : ℝ → ℝ → ℝ → ℝ → ℝ) : Ker F :=
  fun x y => f (chA x y) (chB x y) (chC x y) (chD x y)

/-- The transpose of a channel kernel: substitute `(𝖡, 𝖠, -𝖣, -𝖢)` (`eq:middle:transpose`). -/
theorem chanKer_swap (h3 : Fintype.card F % 4 = 3) (f : ℝ → ℝ → ℝ → ℝ → ℝ) (x y : Half F) :
    chanKer f y x = f (chB x y) (chA x y) (-chD x y) (-chC x y) := by
  simp only [chanKer]
  rw [chA_swap x y, chB_swap x y, chC_swap h3 x y, chD_swap h3 x y]

theorem kerT_chanKer (h3 : Fintype.card F % 4 = 3) (f : ℝ → ℝ → ℝ → ℝ → ℝ) :
    kerT (chanKer (F := F) f) = chanKer (fun a b c d => f b a (-d) (-c)) := by
  funext x y
  rw [kerT_apply, chanKer_swap h3 f x y]
  rfl

theorem kSym_chanKer (h3 : Fintype.card F % 4 = 3) {f g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (h : ∀ a b c d, (f a b c d + f b a (-d) (-c)) / 2 = g a b c d) :
    kSym (chanKer (F := F) f) = chanKer g := by
  funext x y
  rw [kSym_apply, chanKer_swap h3 f x y]
  exact h _ _ _ _

theorem kSkew_chanKer (h3 : Fintype.card F % 4 = 3) {f g : ℝ → ℝ → ℝ → ℝ → ℝ}
    (h : ∀ a b c d, (f a b c d - f b a (-d) (-c)) / 2 = g a b c d) :
    kSkew (chanKer (F := F) f) = chanKer g := by
  funext x y
  rw [kSkew_apply, chanKer_swap h3 f x y]
  exact h _ _ _ _

/-! ## (a) -/

/-- `Φ = (1+𝖠)(1+𝖡)[(1+𝖢)(1+𝖣) - 1]`. -/
def Phi : Ker F := (1 + chA) * (1 + chB) * ((1 + chC) * (1 + chD) - 1)

/-- `Φ' = (1+𝖠)(1+𝖡)[(1+𝖢)(1-𝖣) - 1]`. -/
def Phi' : Ker F := (1 + chA) * (1 + chB) * ((1 + chC) * (1 - chD) - 1)

/-- `Φ_s = (1+𝖠)(1+𝖡)𝖢𝖣`. -/
def PhiS : Ker F := (1 + chA) * (1 + chB) * (chC * chD)

/-- `Φ_a = (1+𝖠)(1+𝖡)(𝖢+𝖣)`. -/
def PhiA : Ker F := (1 + chA) * (1 + chB) * (chC + chD)

theorem Phi_eq :
    (Phi : Ker F) = chanKer fun a b c d => (1 + a) * (1 + b) * ((1 + c) * (1 + d) - 1) :=
  rfl

theorem Phi'_eq :
    (Phi' : Ker F) = chanKer fun a b c d => (1 + a) * (1 + b) * ((1 + c) * (1 - d) - 1) := rfl

theorem PhiS_eq : (PhiS : Ker F) = chanKer fun a b c d => (1 + a) * (1 + b) * (c * d) := rfl

theorem PhiA_eq : (PhiA : Ker F) = chanKer fun a b c d => (1 + a) * (1 + b) * (c + d) := rfl

/-- **`lem:mirror`(a): `Sym Φ = Φ_s`.** -/
theorem mirror_a_sym (h3 : Fintype.card F % 4 = 3) : kSym (Phi : Ker F) = PhiS := by
  rw [Phi_eq, PhiS_eq]
  exact kSym_chanKer h3 fun a b c d => by ring

/-- **`lem:mirror`(a): `Skew Φ = Φ_a`.** -/
theorem mirror_a_skew (h3 : Fintype.card F % 4 = 3) : kSkew (Phi : Ker F) = PhiA := by
  rw [Phi_eq, PhiA_eq]
  exact kSkew_chanKer h3 fun a b c d => by ring

/-- **`lem:mirror`(a): `Skew Φ' = 0`.** -/
theorem mirror_a_skew' (h3 : Fintype.card F % 4 = 3) : kSkew (Phi' : Ker F) = 0 := by
  rw [Phi'_eq, show (0 : Ker F) = chanKer fun _ _ _ _ => 0 from rfl]
  exact kSkew_chanKer h3 fun a b c d => by ring

/-- **`lem:mirror`(a): `Sym Φ' = (1+𝖠)(1+𝖡)(𝖢 - 𝖣 - 𝖢𝖣)`.** -/
theorem mirror_a_sym' (h3 : Fintype.card F % 4 = 3) :
    kSym (Phi' : Ker F) = (1 + chA) * (1 + chB) * (chC - chD - chC * chD) := by
  rw [Phi'_eq, show ((1 + chA) * (1 + chB) * (chC - chD - chC * chD) : Ker F) =
    chanKer fun a b c d => (1 + a) * (1 + b) * (c - d - c * d) from rfl]
  exact kSym_chanKer h3 fun a b c d => by ring

/-! ## (b) The monomial classification -/

/-- The four channels, as letters. -/
inductive Chan where
  | A | B | C | D
  deriving DecidableEq

instance : Fintype Chan where
  elems := {.A, .B, .C, .D}
  complete := by intro x; cases x <;> decide

/-- The labels of a pair of halves: `(false, i)` is `x_i`, `(true, i)` is `y_i`. -/
abbrev Lbl : Type := Bool × Fin 3

/-- The edge of a channel, as (tail, head) of the arrow that the value `+1` asserts
(`eq:middle:channels`): `𝖠 : x₀ → y₂`, `𝖡 : y₀ → x₂`, `𝖢 : x₁ → y₀`, `𝖣 : x₀ → y₁`. -/
def Chan.edge : Chan → Lbl × Lbl
  | .A => ((false, 0), (true, 2))
  | .B => ((true, 0), (false, 2))
  | .C => ((false, 1), (true, 0))
  | .D => ((false, 0), (true, 1))

/-- The two endpoints of the edge of a channel. -/
def Chan.ends (c : Chan) : Finset Lbl := {c.edge.1, c.edge.2}

/-- The star at `x₀`: the channels whose edge contains `x₀`. -/
def starX : Finset Chan := Finset.univ.filter fun c => ((false, 0) : Lbl) ∈ c.ends

/-- The star at `y₀`: the channels whose edge contains `y₀`. -/
def starY : Finset Chan := Finset.univ.filter fun c => ((true, 0) : Lbl) ∈ c.ends

theorem starX_eq : starX = {Chan.A, Chan.D} := by decide

theorem starY_eq : starY = {Chan.B, Chan.C} := by decide

/-- **The two stars have no common label.** -/
theorem stars_disjoint : ∀ c ∈ starX, ∀ c' ∈ starY, Disjoint c.ends c'.ends := by decide

/-- A monomial (a set of channels) is a **star monomial** if all its edges lie in one star. -/
def IsStarMono (m : Finset Chan) : Prop := m.Nonempty ∧ (m ⊆ starX ∨ m ⊆ starY)

/-- A **nonstar**: a nonempty monomial that is not a star monomial. -/
def IsNonstar (m : Finset Chan) : Prop := m.Nonempty ∧ ¬ (m ⊆ starX ∨ m ⊆ starY)

instance : DecidablePred IsStarMono := fun m => by unfold IsStarMono; infer_instance

instance : DecidablePred IsNonstar := fun m => by unfold IsNonstar; infer_instance

/-- **The six star monomials** `𝖠, 𝖡, 𝖢, 𝖣, 𝖠𝖣, 𝖡𝖢`. -/
theorem stars_eq : Finset.univ.filter IsStarMono =
    {{Chan.A}, {Chan.B}, {Chan.C}, {Chan.D}, {Chan.A, Chan.D}, {Chan.B, Chan.C}} := by
  decide

/-- **The nine nonstars** listed in `lem:record:projected-nonstar`: `𝖠𝖡, 𝖠𝖢, 𝖡𝖣, 𝖢𝖣, 𝖠𝖡𝖢,
𝖠𝖡𝖣, 𝖠𝖢𝖣, 𝖡𝖢𝖣, 𝖠𝖡𝖢𝖣`. A nonstar contains one channel of each star, hence two disjoint cross
edges. -/
theorem nonstars_eq : Finset.univ.filter IsNonstar =
    {{Chan.A, Chan.B}, {Chan.A, Chan.C}, {Chan.B, Chan.D}, {Chan.C, Chan.D},
      {Chan.A, Chan.B, Chan.C}, {Chan.A, Chan.B, Chan.D}, {Chan.A, Chan.C, Chan.D},
      {Chan.B, Chan.C, Chan.D}, {Chan.A, Chan.B, Chan.C, Chan.D}} := by
  decide

theorem nonstar_meets_both (m : Finset Chan) (hm : IsNonstar m) :
    (m ∩ starX).Nonempty ∧ (m ∩ starY).Nonempty := by
  revert m
  decide

/-- **The matching `{𝖢, 𝖣}`**: the edges `x₁ — y₀` and `x₀ — y₁` have disjoint endpoints. -/
theorem matching_CD : Disjoint Chan.C.ends Chan.D.ends := by decide

/-- **`lem:mirror`(b), first claim**: the four monomials `𝖢𝖣, 𝖠𝖢𝖣, 𝖡𝖢𝖣, 𝖠𝖡𝖢𝖣` of `Φ_s` are
nonstars and contain the matching `{𝖢, 𝖣}`. -/
theorem PhiS_monomials : ∀ m ∈ ({{Chan.C, Chan.D}, {Chan.A, Chan.C, Chan.D},
    {Chan.B, Chan.C, Chan.D}, {Chan.A, Chan.B, Chan.C, Chan.D}} : Finset (Finset Chan)),
    IsNonstar m ∧ ({Chan.C, Chan.D} : Finset Chan) ⊆ m := by
  decide

/-- **`lem:mirror`(b)**: the monomials `𝖢, 𝖣, 𝖠𝖣, 𝖡𝖢` of `L_p` are star monomials. -/
theorem Lp_monomials_star : ∀ m ∈ ({{Chan.C}, {Chan.D}, {Chan.A, Chan.D}, {Chan.B, Chan.C}} :
    Finset (Finset Chan)), IsStarMono m := by
  decide

/-- **`lem:mirror`(b)**: the monomials `𝖠𝖢, 𝖡𝖣, 𝖠𝖡𝖢, 𝖠𝖡𝖣` of `Φ_{a,ns}` are nonstars. -/
theorem PhiAns_monomials : ∀ m ∈ ({{Chan.A, Chan.C}, {Chan.B, Chan.D}, {Chan.A, Chan.B, Chan.C},
    {Chan.A, Chan.B, Chan.D}} : Finset (Finset Chan)), IsNonstar m := by
  decide

/-- The star part `L_p = 𝖢 + 𝖣 + 𝖠𝖣 + 𝖡𝖢`. -/
def Lp : Ker F := chC + chD + chA * chD + chB * chC

/-- The nonstar part `Φ_{a,ns} = 𝖠𝖢 + 𝖡𝖣 + 𝖠𝖡𝖢 + 𝖠𝖡𝖣`. -/
def PhiAns : Ker F := chA * chC + chB * chD + chA * chB * chC + chA * chB * chD

/-- **`lem:mirror`(b): `Φ_a = L_p + Φ_{a,ns}`.** -/
theorem mirror_b_split : (PhiA : Ker F) = Lp + PhiAns := by
  unfold PhiA Lp PhiAns
  ring

/-- **`lem:mirror`(b): `Φ_s = 𝖢𝖣 + 𝖠𝖢𝖣 + 𝖡𝖢𝖣 + 𝖠𝖡𝖢𝖣`.** -/
theorem PhiS_expand :
    (PhiS : Ker F) = chC * chD + chA * chC * chD + chB * chC * chD + chA * chB * chC * chD := by
  unfold PhiS
  ring

/-! ## (c) The scalar part of the norm -/

/-- `λ = (p + 2)/(p (p - 1)(p - 2))` of `lem:mirror`(c). -/
noncomputable def lamM (p : ℝ) : ℝ := (p + 2) / (p * (p - 1) * (p - 2))

/-- `β = -1/(p - 1)` of `lem:mirror`(c). -/
noncomputable def betaM (p : ℝ) : ℝ := -1 / (p - 1)

/-- `γ = q + (1 - 2q - q²)/(p - 1) + 2q/((p - 1)(p - 2))`, `q = 1/p`, of `lem:mirror`(c). -/
noncomputable def gamM (p : ℝ) : ℝ :=
  1 / p + (1 - 2 / p - (1 / p) ^ 2) / (p - 1) + 2 * (1 / p) / ((p - 1) * (p - 2))

/-- `l = r [((2 + 2q²/(1 - 2q))/(1 - q))^{1/2} + q/(1 - q)]` of `lem:mirror`(c). -/
noncomputable def ellM (q r : ℝ) : ℝ :=
  r * (Real.sqrt ((2 + 2 * q ^ 2 / (1 - 2 * q)) / (1 - q)) + q / (1 - q))

/-- `γ/q = (2 - 3q - q²)/(1 - q) + 2q²/((1 - q)(1 - 2q))` (the proof of `lem:mirror`(c)). -/
theorem gamM_eq {p : ℝ} (hp : 3 ≤ p) :
    gamM p = (1 / p) * ((2 - 3 * (1 / p) - (1 / p) ^ 2) / (1 - 1 / p) +
      2 * (1 / p) ^ 2 / ((1 - 1 / p) * (1 - 2 * (1 / p)))) := by
  have h0 : p ≠ 0 := by positivity
  have h1 : p - 1 ≠ 0 := by intro h; linarith
  have h2 : p - 2 ≠ 0 := by intro h; linarith
  have h1' : 1 - 1 / p ≠ 0 := by
    rw [one_sub_div h0]; exact div_ne_zero h1 h0
  have h2' : 1 - 2 * (1 / p) ≠ 0 := by
    rw [mul_one_div, one_sub_div h0]; exact div_ne_zero h2 h0
  unfold gamM
  field_simp
  ring

/-- **`lem:mirror`(c), the scalar inequality**: `|β| r + (γ - λ²)^{1/2} ≤ l` at `q = 1/p`,
`r = q^{1/2}`, for every `p ≥ 3` (the paper's middle primes are `≥ 19`). -/
theorem mirror_c_scalar {p : ℝ} (hp : 3 ≤ p) :
    |betaM p| * Real.sqrt (1 / p) + Real.sqrt (gamM p - lamM p ^ 2) ≤
      ellM (1 / p) (Real.sqrt (1 / p)) := by
  set q : ℝ := 1 / p with hq
  have hp0 : 0 < p := by linarith
  have hq0 : 0 < q := by positivity
  have hqs : q ≤ 1 / 3 := by
    rw [hq]; exact div_le_div_of_nonneg_left (by norm_num) (by norm_num) hp
  have h1q : 0 < 1 - q := by linarith
  have h2q : 0 < 1 - 2 * q := by linarith
  set X : ℝ := (2 + 2 * q ^ 2 / (1 - 2 * q)) / (1 - q) with hX
  have hX0 : 0 ≤ X := by positivity
  -- `|β| = q/(1 - q)`
  have hbeta : |betaM p| = q / (1 - q) := by
    unfold betaM
    have hpm : 0 < p - 1 := by linarith
    rw [abs_div, abs_neg, abs_one, abs_of_pos hpm, hq]
    field_simp
  -- `γ ≤ q X`
  have hgam : gamM p ≤ q * X := by
    rw [gamM_eq hp, ← hq, hX]
    have : (2 - 3 * q - q ^ 2) / (1 - q) ≤ 2 / (1 - q) := by
      apply div_le_div_of_nonneg_right _ h1q.le
      nlinarith
    have e : (2 + 2 * q ^ 2 / (1 - 2 * q)) / (1 - q) =
        2 / (1 - q) + 2 * q ^ 2 / ((1 - q) * (1 - 2 * q)) := by
      field_simp
    rw [e]
    have := mul_le_mul_of_nonneg_left
      (add_le_add_right this (2 * q ^ 2 / ((1 - q) * (1 - 2 * q)))) hq0.le
    linarith
  have hsq : Real.sqrt (gamM p - lamM p ^ 2) ≤ Real.sqrt q * Real.sqrt X := by
    rw [← Real.sqrt_mul hq0.le]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg (lamM p)]
  unfold ellM
  rw [hbeta, ← hX]
  nlinarith [Real.sqrt_nonneg q]

/-- **`lem:mirror`(c)**: if the Gram data of `L_p = A_⋆ V_0^* - V_0 A_⋆^*` are those of
`lem:paley-triple`(e), `V_0^* A_⋆ = λ I + β P`, `A_⋆^* A_⋆ = γ I`, `P^* P = q I` with `q = 1/p`
(a `TwoFeature` bundle with `a = λ`, `b = β`, `c = γ`), then `‖L_p w‖ ≤ l ‖w‖`; by
`TwoFeature.skew_attained` the norm is exactly `|β| r + (γ - λ²)^{1/2}`. The Gram data are a
hypothesis here. -/
theorem mirror_c {H₀ H : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [Nontrivial H₀] (D : TwoFeature H₀ H)
    {p : ℝ} (hp : 3 ≤ p) (ha : D.a = lamM p) (hb : D.b = betaM p) (hc : D.c = gamM p)
    (hq : D.q = 1 / p) (w : H) :
    ‖D.skewOp w‖ ≤ ellM (1 / p) (Real.sqrt (1 / p)) * ‖w‖ := by
  refine (D.skew_norm_le w).trans ?_
  rw [ha, hb, hc, hq]
  exact mul_le_mul_of_nonneg_right (mirror_c_scalar hp) (norm_nonneg _)

/-! ## (d) The signed pairing -/

/-- `x̃_t = 𝖣 + t𝖠 + (1 - t)𝖠𝖣`. -/
def xt (t : ℝ) : Ker F := chD + t • chA + (1 - t) • (chA * chD)

/-- `ỹ_t = 𝖢 - t𝖡 + (1 - t)𝖡𝖢`. -/
def yt (t : ℝ) : Ker F := chC - t • chB + (1 - t) • (chB * chC)

/-- `Φ_t = (1+𝖢)(1+(1-t)𝖡)[1 + 𝖣 + (1+t)𝖠 + (1-t)𝖠𝖣] - (1+𝖠)(1+𝖡)`. -/
def PhiT (t : ℝ) : Ker F :=
  (1 + chC) * (1 + (1 - t) • chB) * (1 + chD + (1 + t) • chA + (1 - t) • (chA * chD)) -
    (1 + chA) * (1 + chB)

/-- `K_t = 𝖠𝖢(1 + (1 - t)𝖡)`. -/
def Kt (t : ℝ) : Ker F := chA * chC * (1 + (1 - t) • chB)

/-- `L_{t,p} = 𝖢 + 𝖣 + t(𝖠 - 𝖡) + (1 - t)(𝖠𝖣 + 𝖡𝖢)`. -/
def Lt (t : ℝ) : Ker F := chC + chD + t • (chA - chB) + (1 - t) • (chA * chD + chB * chC)

theorem xt_eq (t : ℝ) : (xt t : Ker F) = chanKer fun a _ _ d => d + t * a + (1 - t) * (a * d) :=
  rfl

theorem yt_eq (t : ℝ) : (yt t : Ker F) = chanKer fun _ b c _ => c - t * b + (1 - t) * (b * c) :=
  rfl

theorem PhiT_eq' (t : ℝ) : (PhiT t : Ker F) = chanKer fun a b c d =>
    (1 + c) * (1 + (1 - t) * b) * (1 + d + (1 + t) * a + (1 - t) * (a * d)) -
      (1 + a) * (1 + b) := rfl

theorem Kt_eq' (t : ℝ) : (Kt t : Ker F) = chanKer fun a b c _ => a * c * (1 + (1 - t) * b) := rfl

theorem Lt_eq' (t : ℝ) : (Lt t : Ker F) = chanKer fun a b c d =>
    c + d + t * (a - b) + (1 - t) * (a * d + b * c) := rfl

/-- **`lem:mirror`(d): `Φ_0 = Φ`.** -/
theorem PhiT_zero : (PhiT 0 : Ker F) = Phi := by
  rw [PhiT_eq', Phi_eq]
  funext x y
  simp only [chanKer]
  ring

/-- **`lem:mirror`(d), the factorization**: `Φ_t = (1+𝖡) x̃_t + (1+𝖠) ỹ_t + x̃_t ỹ_t`. -/
theorem PhiT_eq (t : ℝ) : (PhiT t : Ker F) = (1 + chB) * xt t + (1 + chA) * yt t + xt t * yt t := by
  rw [PhiT_eq']
  funext x y
  simp only [chanKer, xt, yt, Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply,
    Pi.one_apply, smul_eq_mul]
  ring

/-- **`lem:mirror`(d): `x̃_t^⊤ = -ỹ_t`.** -/
theorem kerT_xt (h3 : Fintype.card F % 4 = 3) (t : ℝ) : kerT (xt t : Ker F) = -yt t := by
  rw [xt_eq, kerT_chanKer h3, yt_eq]
  funext x y
  simp only [chanKer, Pi.neg_apply]
  ring

/-- **`lem:mirror`(d): `ỹ_t^⊤ = -x̃_t`.** -/
theorem kerT_yt (h3 : Fintype.card F % 4 = 3) (t : ℝ) : kerT (yt t : Ker F) = -xt t := by
  rw [yt_eq, kerT_chanKer h3, xt_eq]
  funext x y
  simp only [chanKer, Pi.neg_apply]
  ring

/-- **`lem:mirror`(d): `Sym Φ_t = x̃_t ỹ_t`.** -/
theorem mirror_d_sym (h3 : Fintype.card F % 4 = 3) (t : ℝ) :
    kSym (PhiT t : Ker F) = xt t * yt t := by
  rw [PhiT_eq', show (xt t * yt t : Ker F) = chanKer fun a b c d =>
    (d + t * a + (1 - t) * (a * d)) * (c - t * b + (1 - t) * (b * c)) from rfl]
  exact kSym_chanKer h3 fun a b c d => by ring

/-- **`lem:mirror`(d): `Skew Φ_t = L_{t,p} + K_t - K_t^⊤`.** -/
theorem mirror_d_skew (h3 : Fintype.card F % 4 = 3) (t : ℝ) :
    kSkew (PhiT t : Ker F) = Lt t + Kt t - kerT (Kt t) := by
  rw [PhiT_eq', Kt_eq', kerT_chanKer h3, Lt_eq']
  rw [show ((chanKer fun a b c d => c + d + t * (a - b) + (1 - t) * (a * d + b * c)) +
      (chanKer fun a b c _ => a * c * (1 + (1 - t) * b)) -
      chanKer fun a b c d => b * -d * (1 + (1 - t) * a) : Ker F) =
      chanKer fun a b c d => c + d + t * (a - b) + (1 - t) * (a * d + b * c) +
        a * c * (1 + (1 - t) * b) - b * -d * (1 + (1 - t) * a) from rfl]
  exact kSkew_chanKer h3 fun a b c d => by ring

/-- **`lem:mirror`(d): `L_{t,p} = x̃_t + ỹ_t`.** -/
theorem Lt_eq (t : ℝ) : (Lt t : Ker F) = xt t + yt t := by
  unfold Lt xt yt
  funext x y
  simp only [Pi.add_apply, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The rectangular star `a₁ χ(u - z) + a₂ χ(v - z) + a₃ χ(u - z) χ(v - z)`
(`lem:record:projected-nonstar`(b)). -/
def rectStar (a₁ a₂ a₃ : ℝ) (z u v : F) : ℝ :=
  a₁ * (quadraticChar F (u - z) : ℝ) + a₂ * (quadraticChar F (v - z) : ℝ) +
    a₃ * ((quadraticChar F (u - z) : ℝ) * (quadraticChar F (v - z) : ℝ))

/-- **`lem:mirror`(d)**: `x̃_t` is the rectangular star with centre `x₀`, leaves `y₁, y₂` and
coefficients `(1, t, 1 - t)`. -/
theorem xt_rect (t : ℝ) (x y : Half F) : xt t x y = rectStar 1 t (1 - t) (x 0) (y 1) (y 2) := by
  simp only [xt, rectStar, chA, chD, Pi.add_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- **`lem:mirror`(d)**: `ỹ_t` is the rectangular star with centre `y₀`, leaves `x₁, x₂` and
coefficients `-(1, t, 1 - t)`. -/
theorem yt_rect (h3 : Fintype.card F % 4 = 3) (t : ℝ) (x y : Half F) :
    yt t x y = -rectStar 1 t (1 - t) (y 0) (x 1) (x 2) := by
  simp only [yt, rectStar, chB, chC, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply,
    smul_eq_mul, chi_swap h3 (y 0) (x 1), Int.cast_neg]
  ring

/-- `K_t = 𝖠 · 𝖢 · (1 + (1 - t)𝖡)`, as a product of its factors. -/
theorem Kt_eq (t : ℝ) (x y : Half F) :
    Kt t x y = chA x y * chC x y * (1 + (1 - t) * chB x y) := rfl

/-- **`lem:mirror`(d): `K_t` does not depend on `y₁`.** -/
theorem Kt_indep_y1 (t : ℝ) (x y y' : Half F) (h0 : y 0 = y' 0) (h2 : y 2 = y' 2) :
    Kt t x y = Kt t x y' := by
  simp only [Kt_eq, chA, chB, chC, h0, h2]

/-- `𝖠` does not depend on `x₁`. -/
theorem chA_indep_x1 (x x' y : Half F) (h0 : x 0 = x' 0) : chA x y = chA x' y := by
  simp only [chA, h0]

/-- `𝖡` does not depend on `x₁`. -/
theorem chB_indep_x1 (x x' y : Half F) (h2 : x 2 = x' 2) : chB x y = chB x' y := by
  simp only [chB, h2]

end Sarkozy.MiddleRecords

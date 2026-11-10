module

public import Sarkozy.Variance.CharacterGraphLaw
public import Sarkozy.L20Cap.Mellin

/-! Character-graph moments, relabeling, and odd-edge cancellation. -/

@[expose] public section

namespace Sarkozy.Variance.CharacterGraph

open Finset Sarkozy.L20Cap

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable (F : Type*) [Field F] [Fintype F] [DecidableEq F]

noncomputable def edgeProd : List (ι × ι) → (ι → F) → ℝ
  | [], _ => 1
  | e :: es, x => chi (x e.2 - x e.1) * edgeProd es x

noncomputable def moment (G : List (ι × ι)) : ℝ := (labelLaw ι F).expect (edgeProd F G)

theorem moment_nil : moment F ([] : List (ι × ι)) = 1 := by
  simp only [moment, edgeProd, FiniteLaw.expect_const]

theorem moment_pointwise (G H : List (ι × ι)) (s : ℝ)
    (h : ∀ x, edgeProd F G x = s * edgeProd F H x) : moment F G = s * moment F H := by
  unfold moment
  rw [← FiniteLaw.expect_const_mul]
  exact (labelLaw ι F).expect_congr h

theorem moment_relabel (G H : List (ι × ι)) (e : Equiv.Perm ι) (s : ℝ)
    (h : ∀ x, edgeProd F G (x ∘ e) = s * edgeProd F H x) :
    moment F G = s * moment F H := by
  unfold moment
  rw [← label_expect_permute e, ← FiniteLaw.expect_const_mul]
  exact (labelLaw ι F).expect_congr h

omit [Fintype ι] [DecidableEq ι] in
theorem edgeProd_neg (hm1 : quadraticChar F (-1) = -1) (G : List (ι × ι)) (x : ι → F) :
    edgeProd F G (fun i => -x i) = (-1 : ℝ) ^ G.length * edgeProd F G x := by
  induction G with
  | nil => simp only [edgeProd, List.length_nil, pow_zero, mul_one]
  | cons e es ih =>
    simp only [edgeProd, List.length_cons, pow_succ]
    rw [show -x e.2 - -x e.1 = -(x e.2 - x e.1) by ring, chi_neg hm1, ih]
    ring

theorem moment_odd (hm1 : quadraticChar F (-1) = -1) (G : List (ι × ι))
    (hodd : Odd G.length) : moment F G = 0 := by
  have h := label_expect_equiv (Equiv.arrowCongr (Equiv.refl ι) (Equiv.neg F)) (edgeProd F G)
  change (labelLaw ι F).expect (fun x => edgeProd F G (fun i => -x i)) = moment F G at h
  simp_rw [edgeProd_neg F hm1 G, hodd.neg_one_pow] at h
  rw [FiniteLaw.expect_const_mul] at h
  change -1 * moment F G = moment F G at h
  linarith

def Avoids (G : List (ι × ι)) (v : ι) : Prop := ∀ e ∈ G, e.1 ≠ v ∧ e.2 ≠ v

instance (G : List (ι × ι)) (v : ι) : Decidable (Avoids G v) := by
  unfold Avoids
  infer_instance

omit [Fintype ι] in
theorem edgeProd_update (G : List (ι × ι)) (v : ι) (hv : Avoids G v) (x : ι → F) (t : F) :
    edgeProd F G (Function.update x v t) = edgeProd F G x := by
  induction G with
  | nil => rfl
  | cons e es ih =>
    obtain ⟨h1, h2⟩ := hv e (by simp)
    have hrest : Avoids es v := fun d hd => hv d (by simp only [List.mem_cons]; exact Or.inr hd)
    simp only [edgeProd, Function.update_of_ne h1, Function.update_of_ne h2, ih hrest]

def identify (a b : ι) (G : List (ι × ι)) : List (ι × ι) :=
  G.map (fun e => (if e.1 = b then a else e.1, if e.2 = b then a else e.2))

omit [Fintype ι] in
theorem edgeProd_identify (a b : ι) (G : List (ι × ι)) (x : ι → F) :
    edgeProd F (identify a b G) x = edgeProd F G (Function.update x b (x a)) := by
  induction G with
  | nil => rfl
  | cons e es ih =>
    simp only [identify, List.map_cons, edgeProd] at *
    rw [ih]
    by_cases h1 : e.1 = b <;> by_cases h2 : e.2 = b <;>
      simp [h1, h2, Function.update_of_ne]

theorem moment_loop (v : ι) (G : List (ι × ι)) : moment F ((v, v) :: G) = 0 := by
  simp only [moment, edgeProd, sub_self, chi_zero, zero_mul, FiniteLaw.expect_const]

end Sarkozy.Variance.CharacterGraph

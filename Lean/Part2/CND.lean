import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
Finite conditional negative definiteness and the simplex objective. The Gaussian/Schoenberg and Bernstein closure steps are
not assumptions of a claimed end-to-end radius construction in this file.
-/

namespace Part2.CND

open scoped BigOperators

variable {ι : Type*} [Fintype ι]

def quadratic (D : ι → ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, x i * x j * D i j

/-- The quadratic inequality on the zero-mass subspace. -/
def ConditionallyNegative (D : ι → ι → ℝ) : Prop :=
  ∀ x : ι → ℝ, (∑ i, x i) = 0 → quadratic D x ≤ 0

/-- The symmetric, zero-diagonal finite CND convention used in the paper. -/
def IsCND (D : ι → ι → ℝ) : Prop :=
  (∀ i j, D i j = D j i) ∧ (∀ i, D i i = 0) ∧ ConditionallyNegative D

def simplex : Set (ι → ℝ) :=
  {p | (∀ i, 0 ≤ p i) ∧ (∑ i, p i) = 1}

def massOne : Set (ι → ℝ) := {p | (∑ i, p i) = 1}

/-- P6's objective; its convexity is only asserted on a fixed-mass set. -/
noncomputable def potential (θ : ι → ℝ) (D : ι → ι → ℝ) (p : ι → ℝ) : ℝ :=
  (∑ i, θ i * p i) - (1 / 2 : ℝ) * quadratic D p

theorem convex_massOne : Convex ℝ (massOne : Set (ι → ℝ)) := by
  intro x hx y hy a b _ha _hb hab
  change (∑ i, (a * x i + b * y i)) = 1
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  change a * (∑ i, x i) + b * (∑ i, y i) = 1
  rw [show (∑ i, x i) = 1 from hx, show (∑ i, y i) = 1 from hy]
  simpa using hab

theorem convex_simplex : Convex ℝ (simplex : Set (ι → ℝ)) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · exact convex_massOne hx.2 hy.2 ha hb hab

/-- This algebraic identity needs no symmetry of `D`. -/
theorem quadratic_mix_identity (D : ι → ι → ℝ) (x y : ι → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    quadratic D (a • x + b • y) =
      a * quadratic D x + b * quadratic D y - a * b * quadratic D (x - y) := by
  have hb : b = 1 - a := by linarith
  have hterm (i j : ι) :
      (a * x i + b * y i) * (a * x j + b * y j) * D i j =
        a * (x i * x j * D i j) + b * (y i * y j * D i j) -
          a * b * ((x i - y i) * (x j - y j) * D i j) := by
    rw [hb]
    ring
  unfold quadratic
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply]
  simp_rw [hterm]
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]

theorem linear_mix_identity (θ x y : ι → ℝ) (a b : ℝ) :
    (∑ i, θ i * (a * x i + b * y i)) =
      a * (∑ i, θ i * x i) + b * (∑ i, θ i * y i) := by
  simp only [mul_add, Finset.sum_add_distrib]
  congr 1 <;> rw [Finset.mul_sum] <;> apply Finset.sum_congr rfl <;> intro i _ <;> ring

/-- Exact Jensen gap. CND controls the difference vector because its mass is zero. -/
theorem potential_mix_identity (θ : ι → ℝ) (D : ι → ι → ℝ) (x y : ι → ℝ)
    (a b : ℝ) (hab : a + b = 1) :
    potential θ D (a • x + b • y) =
      a * potential θ D x + b * potential θ D y +
        (1 / 2 : ℝ) * (a * b) * quadratic D (x - y) := by
  unfold potential
  rw [quadratic_mix_identity D x y a b hab]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [linear_mix_identity]
  ring

theorem potential_convexOn_massOne (θ : ι → ℝ) (D : ι → ι → ℝ)
    (hD : ConditionallyNegative D) :
    ConvexOn ℝ massOne (potential θ D) := by
  refine ⟨convex_massOne, ?_⟩
  intro x hx y hy a b ha hb hab
  have hmass : (∑ i, (x - y) i) = 0 := by
    simp only [Pi.sub_apply, Finset.sum_sub_distrib]
    rw [show (∑ i, x i) = 1 from hx, show (∑ i, y i) = 1 from hy]
    ring
  have hquad := hD (x - y) hmass
  have hgap : (1 / 2 : ℝ) * (a * b) * quadratic D (x - y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg (by norm_num) (mul_nonneg ha hb)) hquad
  rw [potential_mix_identity θ D x y a b hab]
  simpa only [smul_eq_mul] using add_le_of_nonpos_right hgap

/-- P6: finite CND radii imply a convex objective on the probability simplex. -/
theorem potential_convexOn_simplex (θ : ι → ℝ) (D : ι → ι → ℝ)
    (hD : IsCND D) : ConvexOn ℝ simplex (potential θ D) := by
  exact (potential_convexOn_massOne θ D hD.2.2).subset (fun _ hp => hp.2) convex_simplex

/-- The squared-distance kernel represented by a Gram matrix. -/
def gramDistance (B : ι → ι → ℝ) (i j : ι) : ℝ :=
  B i i + B j j - 2 * B i j

/-- The zero-mass cancellation behind the effective-resistance CND argument. -/
theorem gramDistance_quadratic (B : ι → ι → ℝ) (x : ι → ℝ)
    (hx : (∑ i, x i) = 0) :
    quadratic (gramDistance B) x = -2 * quadratic B x := by
  have hleft : (∑ i, ∑ j, x i * x j * B i i) = 0 := by
    have hterm (i j : ι) : x i * x j * B i i = (x i * B i i) * x j := by ring
    simp_rw [hterm, ← Finset.mul_sum, hx, mul_zero, Finset.sum_const_zero]
  have hright : (∑ i, ∑ j, x i * x j * B j j) = 0 := by
    calc
      _ = ∑ i, x i * (∑ j, x j * B j j) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = (∑ i, x i) * (∑ j, x j * B j j) := (Finset.sum_mul _ _ _).symm
      _ = 0 := by rw [hx, zero_mul]
  have hcross : (∑ i, ∑ j, x i * x j * (2 * B i j)) = 2 * quadratic B x := by
    have hterm (i j : ι) : x i * x j * (2 * B i j) = 2 * (x i * x j * B i j) := by
      ring
    simp_rw [hterm, ← Finset.mul_sum]
    rfl
  unfold quadratic at hcross
  unfold quadratic gramDistance
  simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hleft, hright, hcross]
  ring

/-- A symmetric PSD Gram matrix yields a genuine symmetric zero-diagonal CND kernel.
For resistance distances, supplying the PSD pseudoinverse is a separate obligation. -/
theorem gramDistance_isCND (B : ι → ι → ℝ)
    (hsym : ∀ i j, B i j = B j i)
    (hpsd : ∀ x : ι → ℝ, 0 ≤ quadratic B x) : IsCND (gramDistance B) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    unfold gramDistance
    rw [hsym i j]
    ring
  · intro i
    unfold gramDistance
    ring
  · intro x hx
    rw [gramDistance_quadratic B x hx]
    exact mul_nonpos_of_nonpos_of_nonneg (by norm_num) (hpsd x)

variable {κ : Type*} [Fintype κ]

def coordinateGram (v : ι → κ → ℝ) (i j : ι) : ℝ := ∑ k, v i k * v j k

def squaredDistance (v : ι → κ → ℝ) (i j : ι) : ℝ := ∑ k, (v i k - v j k) ^ 2

theorem coordinateGram_quadratic (v : ι → κ → ℝ) (x : ι → ℝ) :
    quadratic (coordinateGram v) x = ∑ k, (∑ i, x i * v i k) ^ 2 := by
  unfold quadratic coordinateGram
  calc
    _ = ∑ i, ∑ j, ∑ k, (x i * v i k) * (x j * v j k) := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i, ∑ k, ∑ j, (x i * v i k) * (x j * v j k) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ k, ∑ i, ∑ j, (x i * v i k) * (x j * v j k) := Finset.sum_comm
    _ = ∑ k, (∑ i, x i * v i k) * (∑ j, x j * v j k) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = _ := by simp only [pow_two]

theorem squaredDistance_eq_gramDistance (v : ι → κ → ℝ) :
    squaredDistance v = gramDistance (coordinateGram v) := by
  funext i j
  unfold squaredDistance gramDistance coordinateGram
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Finite Euclidean squared distances are CND, with no kernel-positivity assumption. -/
theorem squaredDistance_isCND (v : ι → κ → ℝ) : IsCND (squaredDistance v) := by
  rw [squaredDistance_eq_gramDistance]
  apply gramDistance_isCND
  · intro i j
    unfold coordinateGram
    apply Finset.sum_congr rfl
    intro k _
    ring
  · intro x
    rw [coordinateGram_quadratic]
    exact Finset.sum_nonneg (fun k _ => sq_nonneg _)

/-- A concrete end-to-end geometry result with arbitrary finite Euclidean coordinates. -/
theorem squaredDistance_potential_convexOn_simplex (θ : ι → ℝ) (v : ι → κ → ℝ) :
    ConvexOn ℝ simplex (potential θ (squaredDistance v)) :=
  potential_convexOn_simplex θ (squaredDistance v) (squaredDistance_isCND v)

end Part2.CND

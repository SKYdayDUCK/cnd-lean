import SqrtClosure

/-! The original CND-MAIN radius, connected to the computed inverse covariance. -/

noncomputable section
namespace Part2.CNDSaturation
open scoped BigOperators
open Part2.CND
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def originalRadius (D : ι → ι → ℝ) (H L R : ℝ) (i j : ι) : ℝ :=
  (2 * R / Part2.CNDPhysical.c0) *
    (1 - Real.exp (-(2 * H * Real.sqrt (L * D i j) +
      (4 * H * L + R * Fintype.card ι) * D i j) / R))

theorem originalRadius_isCND (D : ι → ι → ℝ) (hD : IsCND D)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    IsCND (originalRadius D H L R) := by
  have h := sqrt_linear_saturation_isCND D hD
    (2 * H * Real.sqrt L / R) ((4 * H * L + R * Fintype.card ι) / R)
    (2 * R / Part2.CNDPhysical.c0) (by positivity) (by positivity)
    (div_nonneg (by positivity) Part2.CNDPhysical.c0_pos.le)
  convert h using 1
  funext i j
  unfold originalRadius
  rw [Real.sqrt_mul hL]
  congr 2
  ring

theorem originalRadius_nonneg (D : ι → ι → ℝ) (hD : IsCND D)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (i j : ι) :
    0 ≤ originalRadius D H L R i j :=
  cnd_nonneg _ (originalRadius_isCND D hD H L R hH hL hR) i j

/-- R=0 is the exact zero-radius branch of the original protocol. -/
theorem originalRadius_isCND_nonnegR (D : ι → ι → ℝ) (hD : IsCND D)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    IsCND (originalRadius D H L R) := by
  by_cases h : R = 0
  · subst R
    have hz : originalRadius D H L 0 = fun _ _ => 0 := by
      funext i j
      simp [originalRadius]
    rw [hz]
    simpa only [zero_mul] using cnd_scale D hD 0 (le_refl 0)
  · exact originalRadius_isCND D hD H L R hH hL (lt_of_le_of_ne hR (Ne.symm h))

theorem originalRadius_gram_isCND (B : ι → ι → ℝ) (hB : IsPSD B)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    IsCND (originalRadius (gramDistance B) H L R) :=
  originalRadius_isCND _ (gramDistance_isCND B hB.1 hB.2) H L R hH hL hR

/-- The radius is CND for the actual inverse information matrix of the protocol. -/
theorem actual_resistance_radius_isCND (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ simplex) (n : ℕ)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    IsCND (originalRadius (Part2.CNDPhysical.resistance p n) H L R) :=
  originalRadius_isCND _ (Part2.CNDPhysical.actual_resistance_isCND p hp n)
    H L R hH hL hR

/-- End-to-end convexity for the original saturated radius, including its sqrt term. -/
theorem actual_resistance_radius_potential_convex (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ simplex) (n : ℕ) (θ : ι → ℝ)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    ConvexOn ℝ simplex
      (potential θ (originalRadius (Part2.CNDPhysical.resistance p n) H L R)) :=
  potential_convexOn_simplex θ _ (actual_resistance_radius_isCND p hp n H L R hH hL hR)

end Part2.CNDSaturation

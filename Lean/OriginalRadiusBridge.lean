import ActualRadius

/-! Equality and closure for the pre-existing, actual protocol radius function. -/

noncomputable section
namespace Part2.CNDSaturation
open Part2.CND
set_option linter.unusedSectionVars false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two real expressions agree for every R, including its totalized R=0 branch. -/
theorem actualSaturatedRadius_eq_originalRadius (p : ℕ → ι → ℝ) (n : ℕ)
    (H L R : ℝ) :
    Part2.CNDPhysical.actualSaturatedRadius p n H L R =
      originalRadius (Part2.CNDPhysical.resistance p n) H L R := by
  funext i j
  unfold Part2.CNDPhysical.actualSaturatedRadius Part2.CNDPhysical.saturatedRadius
    Part2.CNDPhysical.pairRadius originalRadius
  rw [neg_div]

/-- Full closure for the exact pre-existing protocol function, including R=0. -/
theorem actualSaturatedRadius_isCND (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ simplex) (n : ℕ)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    IsCND (Part2.CNDPhysical.actualSaturatedRadius p n H L R) := by
  rw [actualSaturatedRadius_eq_originalRadius]
  exact originalRadius_isCND_nonnegR _ (Part2.CNDPhysical.actual_resistance_isCND p hp n)
    H L R hH hL hR

theorem actualSaturatedRadius_nonneg (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ simplex) (n : ℕ)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (i j : ι) :
    0 ≤ Part2.CNDPhysical.actualSaturatedRadius p n H L R i j :=
  cnd_nonneg _ (actualSaturatedRadius_isCND p hp n H L R hH hL hR) i j

theorem actualSaturatedRadius_potential_convex (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ simplex) (n : ℕ) (θ : ι → ℝ)
    (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    ConvexOn ℝ simplex (potential θ (Part2.CNDPhysical.actualSaturatedRadius p n H L R)) :=
  potential_convexOn_simplex θ _ (actualSaturatedRadius_isCND p hp n H L R hH hL hR)

end Part2.CNDSaturation

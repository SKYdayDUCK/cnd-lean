import Part2.CNDPhysical
import staging.closure20261024.WeightedGraphMaximum

/-!
The original CND information operator is identified with the killed graph
operator before invoking the frozen maximum principle.  No graph equation,
oscillation identity, or maximum-principle conclusion is an input assumption.
-/

noncomputable section

namespace Part2.CNDGraphBridge

open Finset Matrix
open scoped BigOperators Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

def edgeWeight (p : ℕ → ι → ℝ) (n : ℕ) (i j : ι) : ℝ :=
  ∑ t ∈ Finset.range n, p t i * p t j

def inverseContrast (p : ℕ → ι → ℝ) (n : ℕ) (a b : ι) : ι → ℝ :=
  Part2.CNDPhysical.inverseInformation p n *ᵥ Part2.CNDPhysical.contrast a b

def osc (w : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty w - Finset.univ.inf' Finset.univ_nonempty w

theorem edgeWeight_nonneg (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (i j : ι) :
    0 ≤ edgeWeight p n i j := by
  exact Finset.sum_nonneg (fun t _ => mul_nonneg ((hp t).1 i) ((hp t).1 j))

theorem edgeWeight_symmetric (p : ℕ → ι → ℝ) (n : ℕ) (i j : ι) :
    edgeWeight p n i j = edgeWeight p n j i := by
  unfold edgeWeight
  apply Finset.sum_congr rfl
  intro t _
  ring

theorem covariance_graph_action (p w : ι → ℝ) (hs : ∑ j, p j = 1) (i : ι) :
    (Part2.CNDPhysical.covariance p *ᵥ w) i =
      ∑ j, p i * p j * (w i - w j) := by
  have hd : (∑ j, (if i = j then p i else 0) * w j) = p i * w i := by
    simp [ite_mul, eq_comm]
  have hfirst : (∑ j, p i * p j * w i) = p i * w i := by
    calc
      _ = (p i * w i) * (∑ j, p j) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hs, mul_one]
  simp only [Matrix.mulVec, dotProduct, Part2.CNDPhysical.covariance,
    sub_mul, Finset.sum_sub_distrib, mul_sub]
  rw [hd, hfirst]

/-- Exact I+sum(C) identity on all vectors, not only zero-sum contrasts. -/
theorem information_graph_action (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (w : ι → ℝ) (i : ι) :
    (Part2.CNDPhysical.information p n *ᵥ w) i =
      Part2.WeightedGraphMaximum.graphOperator 1 (fun _ => 1) (edgeWeight p n) w i := by
  have hsum : ((∑ t ∈ Finset.range n, Part2.CNDPhysical.covariance (p t)) *ᵥ w) i =
      ∑ j, edgeWeight p n i j * (w i - w j) := by
    rw [Matrix.sum_mulVec]
    simp only [Finset.sum_apply]
    simp_rw [covariance_graph_action _ w ((hp _).2) i]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    exact (Finset.sum_mul _ _ _).symm
  simp only [Part2.CNDPhysical.information, Matrix.add_mulVec, Matrix.one_mulVec,
    Pi.add_apply, Part2.WeightedGraphMaximum.graphOperator, one_mul]
  rw [hsum]

theorem inverseContrast_zero_sum (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    (∑ i, inverseContrast p n a b i) = 0 := by
  exact Part2.CNDPhysical.inverseInformation_preserves_zero_sum p hp n _
    (Part2.CNDPhysical.contrast_sum a b)

/-- The heq needed by the graph theorem is derived from the computed inverse. -/
theorem inverseContrast_graph_equation (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    ∀ i, Part2.WeightedGraphMaximum.graphOperator 1 (fun _ => 1)
      (edgeWeight p n) (inverseContrast p n a b) i =
        Part2.WeightedGraphMaximum.dipole a b i := by
  have h := (Part2.CNDPhysical.actual_resistance_contrast_equation p hp n a b).2.1
  change Part2.CNDPhysical.tangentInformation p n (inverseContrast p n a b) =
    Part2.CNDPhysical.contrast a b at h
  rw [Part2.CNDPhysical.tangentInformation_on_zero_sum p n _
    (inverseContrast_zero_sum p hp n a b)] at h
  intro i
  rw [← information_graph_action p hp n _ i]
  have hi := congr_fun h i
  exact hi

theorem inverseContrast_self (p : ℕ → ι → ℝ) (n : ℕ) (a : ι) :
    inverseContrast p n a a = 0 := by
  have hz : Part2.CNDPhysical.contrast a a = (0 : ι → ℝ) := by
    ext i
    simp [Part2.CNDPhysical.contrast]
  simp [inverseContrast, hz]

/-- Includes identical endpoints and the K=1 case without a dipole assumption. -/
theorem actual_graph_maximum_principle (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    ∀ i, inverseContrast p n a b b ≤ inverseContrast p n a b i ∧
      inverseContrast p n a b i ≤ inverseContrast p n a b a := by
  by_cases hab : a = b
  · subst b
    simp [inverseContrast_self]
  · exact Part2.WeightedGraphMaximum.weighted_graph_maximum_principle
      1 (fun _ => 1) (edgeWeight p n) (inverseContrast p n a b) a b
      (by norm_num) (fun _ => by norm_num) (edgeWeight_nonneg p hp n)
      (edgeWeight_symmetric p n) hab (inverseContrast_graph_equation p hp n a b)

theorem resistance_endpoint_difference (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    Part2.CNDPhysical.resistance p n a b =
      inverseContrast p n a b a - inverseContrast p n a b b := by
  have h := (Part2.CNDPhysical.actual_resistance_contrast_equation p hp n a b).2.2
  rw [h]
  simp [dotProduct, Part2.CNDPhysical.contrast, sub_mul, ite_mul, Finset.sum_sub_distrib,
    inverseContrast]

theorem osc_eq_of_extrema (w : ι → ℝ) (a b : ι)
    (h : ∀ i, w b ≤ w i ∧ w i ≤ w a) : osc w = w a - w b := by
  have hsup : Finset.univ.sup' Finset.univ_nonempty w = w a := by
    apply le_antisymm
    · exact Finset.sup'_le _ _ (fun i _ => (h i).2)
    · exact Finset.le_sup' _ (Finset.mem_univ a)
  have hinf : Finset.univ.inf' Finset.univ_nonempty w = w b := by
    apply le_antisymm
    · exact Finset.inf'_le _ (Finset.mem_univ b)
    · exact Finset.le_inf' _ _ (fun i _ => (h i).1)
  simp only [osc, hsup, hinf]

/-- Original CND equation (12), for the actual regularized information inverse. -/
theorem actual_inverse_osc_eq_resistance (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    osc (inverseContrast p n a b) = Part2.CNDPhysical.resistance p n a b := by
  rw [osc_eq_of_extrema _ a b (actual_graph_maximum_principle p hp n a b),
    resistance_endpoint_difference p hp n a b]

theorem actual_inverse_l1_bound (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    (∑ i, |inverseContrast p n a b i|) ≤
      (Fintype.card ι : ℝ) * Part2.CNDPhysical.resistance p n a b := by
  by_cases hab : a = b
  · subst b
    rw [resistance_endpoint_difference p hp n a a]
    simp [inverseContrast_self]
  · have h := Part2.WeightedGraphMaximum.weighted_graph_l1_bound
      1 (fun _ => 1) (edgeWeight p n) (inverseContrast p n a b) a b
      (by norm_num) (fun _ => by norm_num) (edgeWeight_nonneg p hp n)
      (edgeWeight_symmetric p n) hab (inverseContrast_graph_equation p hp n a b)
    simpa [resistance_endpoint_difference p hp n a b] using h

theorem actual_endpoint_signs (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    0 ≤ inverseContrast p n a b a ∧ inverseContrast p n a b b ≤ 0 := by
  by_cases hab : a = b
  · subst b
    simp [inverseContrast_self]
  · obtain ⟨⟨i, hi⟩, ⟨j, hj⟩⟩ := Part2.WeightedGraphMaximum.dipole_solution_signs
      1 (fun _ => 1) (edgeWeight p n) (inverseContrast p n a b) a b
      (by norm_num) (fun _ => by norm_num) (edgeWeight_symmetric p n) hab
      (inverseContrast_graph_equation p hp n a b)
    have hext := actual_graph_maximum_principle p hp n a b
    exact ⟨(hi.trans_le (hext i).2).le, ((hext j).1.trans_lt hj).le⟩

theorem actual_inverse_coordinate_bound (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b i : ι) :
    |inverseContrast p n a b i| ≤ Part2.CNDPhysical.resistance p n a b := by
  have hs := actual_endpoint_signs p hp n a b
  have he := actual_graph_maximum_principle p hp n a b i
  rw [resistance_endpoint_difference p hp n a b, abs_le]
  constructor <;> linarith [hs.1, hs.2, he.1, he.2]

theorem actual_inverse_pairwise_bound (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b i j : ι) :
    |inverseContrast p n a b i - inverseContrast p n a b j| ≤
      Part2.CNDPhysical.resistance p n a b := by
  have hi := actual_graph_maximum_principle p hp n a b i
  have hj := actual_graph_maximum_principle p hp n a b j
  rw [resistance_endpoint_difference p hp n a b, abs_le]
  constructor <;> linarith [hi.1, hi.2, hj.1, hj.2]

theorem actual_inverse_l2_squared_bound (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    (∑ i, (inverseContrast p n a b i) ^ 2) ≤
      (Fintype.card ι : ℝ) * (Part2.CNDPhysical.resistance p n a b) ^ 2 := by
  have hd := Part2.CNDPhysical.actual_resistance_nonneg p hp n a b
  calc
    _ ≤ ∑ _i : ι, (Part2.CNDPhysical.resistance p n a b) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      have h := actual_inverse_coordinate_bound p hp n a b i
      nlinarith [sq_abs (inverseContrast p n a b i),
        mul_nonneg (sub_nonneg.mpr h)
          (add_nonneg hd (abs_nonneg (inverseContrast p n a b i)))]
    _ = _ := by simp

theorem actual_inverse_l2_bound (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    Real.sqrt (∑ i, (inverseContrast p n a b i) ^ 2) ≤
      Real.sqrt (Fintype.card ι : ℝ) * Part2.CNDPhysical.resistance p n a b := by
  have h := Real.sqrt_le_sqrt (actual_inverse_l2_squared_bound p hp n a b)
  rw [Real.sqrt_mul (Nat.cast_nonneg _), Real.sqrt_sq
    (Part2.CNDPhysical.actual_resistance_nonneg p hp n a b)] at h
  exact h

/-- The original regularization bias is sharpened by centering theta at R/2. -/
theorem actual_regularization_bias (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι)
    (θ : ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R) :
    |∑ i, inverseContrast p n a b i * θ i| ≤
      (R / 2) * (Fintype.card ι : ℝ) * Part2.CNDPhysical.resistance p n a b := by
  have hzero := inverseContrast_zero_sum p hp n a b
  have hcenter : (∑ i, inverseContrast p n a b i * θ i) =
      ∑ i, inverseContrast p n a b i * (θ i - R / 2) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
  rw [hcenter]
  calc
    _ ≤ ∑ i, |inverseContrast p n a b i * (θ i - R / 2)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, |inverseContrast p n a b i| * (R / 2) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul]
      have hr : |θ i - R / 2| ≤ R / 2 := by
        rw [abs_le]
        constructor <;> linarith [(hθ i).1, (hθ i).2]
      exact mul_le_mul_of_nonneg_left hr (abs_nonneg _)
    _ = (R / 2) * (∑ i, |inverseContrast p n a b i|) := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (R / 2) * ((Fintype.card ι : ℝ) * Part2.CNDPhysical.resistance p n a b) :=
      mul_le_mul_of_nonneg_left (actual_inverse_l1_bound p hp n a b) (by positivity)
    _ = _ := by ring

theorem actual_regularization_bias_loose (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι)
    (θ : ι → ℝ) (R : ℝ) (hR : 0 ≤ R) (hθ : ∀ i, 0 ≤ θ i ∧ θ i ≤ R) :
    |∑ i, inverseContrast p n a b i * θ i| ≤
      R * (Fintype.card ι : ℝ) * Part2.CNDPhysical.resistance p n a b := by
  have h := actual_regularization_bias p hp n a b θ R hR hθ
  have hn : 0 ≤ R * (Fintype.card ι : ℝ) * Part2.CNDPhysical.resistance p n a b :=
    mul_nonneg (mul_nonneg hR (Nat.cast_nonneg _))
      (Part2.CNDPhysical.actual_resistance_nonneg p hp n a b)
  nlinarith

/-- The random-direction confidence term uses the same actual resistance energy. -/
theorem actual_inverse_energy_eq_resistance (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (a b : ι) :
    Part2.CND.quadratic (Part2.CNDPhysical.information p n) (inverseContrast p n a b) =
      Part2.CNDPhysical.resistance p n a b := by
  have ht := (Part2.CNDPhysical.actual_resistance_contrast_equation p hp n a b).2.1
  change Part2.CNDPhysical.tangentInformation p n (inverseContrast p n a b) =
    Part2.CNDPhysical.contrast a b at ht
  rw [Part2.CNDPhysical.tangentInformation_on_zero_sum p n _
    (inverseContrast_zero_sum p hp n a b)] at ht
  calc
    _ = (inverseContrast p n a b) ⬝ᵥ
        (Part2.CNDPhysical.information p n *ᵥ inverseContrast p n a b) := by
      rw [Part2.CNDPhysical.quadratic_eq_dot, star_trivial]
    _ = (inverseContrast p n a b) ⬝ᵥ Part2.CNDPhysical.contrast a b := by rw [ht]
    _ = Part2.CNDPhysical.contrast a b ⬝ᵥ inverseContrast p n a b := by
      simp only [dotProduct, mul_comm]
    _ = _ := (Part2.CNDPhysical.actual_resistance_contrast_equation p hp n a b).2.2.symm

end Part2.CNDGraphBridge

/-! Exhaustive public declaration axiom receipt. -/

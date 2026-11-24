import InformationBudget

/-! The exact actual saturated radius, Gamma, observable payment and Q(I). -/
noncomputable section
namespace Part2.CNDInformation
open Matrix Finset
open scoped Matrix BigOperators
variable {ι η : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [Fintype η] [DecidableEq η]

def actualGamma (p : ℕ → ι → ℝ) (t : ℕ) (H L R : ℝ) : ℝ :=
  2 * pairSum (fun i j => p t i * p t j * Part2.CNDPhysical.actualSaturatedRadius p t H L R i j)

def actualPayment (p : ℕ → ι → ℝ) (t : ℕ) (H L R : ℝ) (a : ι) : ℝ :=
  2 * ∑ j, Part2.CNDPhysical.actualSaturatedRadius p t H L R a j * p t j

def actualQ (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ) (u n : ℕ) (H L R : ℝ) : ℝ :=
  (4 * Real.sqrt 3 / Part2.CNDPhysical.c0) * H *
    Real.sqrt ((n : ℝ) * L * (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u)) +
  (6 / Part2.CNDPhysical.c0) * (4 * H * L + R * Fintype.card ι) *
    (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u)

theorem pairSum_mono (f g : ι → ι → ℝ) (h : ∀ i j, i < j → f i j ≤ g i j) :
    pairSum f ≤ pairSum g := by
  apply sum_le_sum
  intro i _
  apply sum_le_sum
  intro j _
  split_ifs with hij
  · exact h i j hij
  · exact le_rfl

theorem pairSum_linear (a b : ℝ) (f g : ι → ι → ℝ) :
    pairSum (fun i j => a * f i j + b * g i j) = a * pairSum f + b * pairSum g := by
  have ht (i j : ι) : (if i < j then a * f i j + b * g i j else 0) =
      a * (if i < j then f i j else 0) + b * (if i < j then g i j else 0) := by
    split_ifs <;> ring
  simp_rw [pairSum, ht, sum_add_distrib, ← mul_sum]

theorem actual_radius_bounds (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex)
    (t : ℕ) (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (i j : ι) :
    0 ≤ Part2.CNDPhysical.actualSaturatedRadius p t H L R i j ∧
      Part2.CNDPhysical.actualSaturatedRadius p t H L R i j ≤ 2 * R / Part2.CNDPhysical.c0 ∧
      Part2.CNDPhysical.actualSaturatedRadius p t H L R i j ≤
        2 * Part2.CNDPhysical.pairRadius p t H L R i j / Part2.CNDPhysical.c0 := by
  have hg := (Part2.CNDPhysical.actual_saturated_radius_geometry p hp t H L R hH hL hR).2.2 i j
  have hρ := Part2.CNDPhysical.pairRadius_nonneg p hp t H L R hH hL hR.le i j
  exact ⟨(le_min (by linarith) (by linarith)).trans hg.1,
    hg.2.trans (min_le_left _ _), hg.2.trans (min_le_right _ _)⟩

theorem actualPayment_bounds (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex)
    (t : ℕ) (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) (a : ι) :
    0 ≤ actualPayment p t H L R a ∧ actualPayment p t H L R a ≤ 4 * R / Part2.CNDPhysical.c0 := by
  constructor
  · exact mul_nonneg (by norm_num) (sum_nonneg (fun j _ => mul_nonneg
      (actual_radius_bounds p hp t H L R hH hL hR a j).1 ((hp t).1 j)))
  · have ht := sum_le_sum (s := (univ : Finset ι)) (fun j _ =>
      mul_le_mul_of_nonneg_right (actual_radius_bounds p hp t H L R hH hL hR a j).2.1 ((hp t).1 j))
    rw [← mul_sum, (hp t).2, mul_one] at ht
    unfold actualPayment
    convert mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring

theorem actualPayment_mean (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex)
    (t : ℕ) (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    (∑ i, p t i * actualPayment p t H L R i) = 2 * actualGamma p t H L R := by
  have hg := Part2.CNDPhysical.actual_saturated_radius_geometry p hp t H L R hH hL hR
  have hs := symmetric_pair_sum
    (fun i j => p t i * p t j * Part2.CNDPhysical.actualSaturatedRadius p t H L R i j)
    (by intro i j; dsimp only; rw [hg.1 i j]; ring)
    (by intro i; dsimp only; rw [hg.2.1 i]; ring)
  have he : (∑ i, p t i * actualPayment p t H L R i) =
      2 * ∑ i, ∑ j, p t i * p t j * Part2.CNDPhysical.actualSaturatedRadius p t H L R i j := by
    simp only [actualPayment, mul_sum]
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring
  rw [he, hs]
  unfold actualGamma
  ring

theorem actualGamma_le_linear_resistance (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (t : ℕ) (H L R : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    actualGamma p t H L R ≤
      (8 * H * Real.sqrt L / Part2.CNDPhysical.c0) * pairSum (fun i j =>
        p t i * p t j * Real.sqrt (Part2.CNDPhysical.resistance p t i j)) +
      (4 * (4 * H * L + R * Fintype.card ι) / Part2.CNDPhysical.c0) * pairSum (fun i j =>
        p t i * p t j * Part2.CNDPhysical.resistance p t i j) := by
  have ht := pairSum_mono
    (fun i j => p t i * p t j * Part2.CNDPhysical.actualSaturatedRadius p t H L R i j)
    (fun i j => (4 * H * Real.sqrt L / Part2.CNDPhysical.c0) *
      (p t i * p t j * Real.sqrt (Part2.CNDPhysical.resistance p t i j)) +
      (2 * (4 * H * L + R * Fintype.card ι) / Part2.CNDPhysical.c0) *
      (p t i * p t j * Part2.CNDPhysical.resistance p t i j)) (by
      intro i j _
      have hr := mul_le_mul_of_nonneg_left
        (actual_radius_bounds p hp t H L R hH hL hR i j).2.2
        (mul_nonneg ((hp t).1 i) ((hp t).1 j))
      unfold Part2.CNDPhysical.pairRadius at hr
      rw [Real.sqrt_mul hL] at hr
      convert hr using 1 <;> ring)
  rw [pairSum_linear] at ht
  unfold actualGamma
  convert mul_le_mul_of_nonneg_left ht (show (0 : ℝ) ≤ 2 by norm_num) using 1 <;> ring

theorem sqrt_information_constant (n L D : ℝ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hD : 0 ≤ D) :
    8 * Real.sqrt L * Real.sqrt (3 * n * D / 4) =
      4 * Real.sqrt 3 * Real.sqrt (n * L * D) := by
  have hnum : 0 ≤ 3 * n * D / 4 := by positivity
  have hprod : 0 ≤ n * L * D := by positivity
  apply (sq_eq_sq₀ (by positivity) (by positivity)).mp
  simp only [mul_pow, Real.sq_sqrt hL,
    Real.sq_sqrt hnum, Real.sq_sqrt hprod,
    Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  ring

theorem actualGamma_sum_le_actualQ (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) (H L R : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 < R) :
    (∑ s ∈ range n, actualGamma p (u + s) H L R) ≤ actualQ Q p u n H L R := by
  let D := coordinateLogdet Q p (u + n) - coordinateLogdet Q p u
  have hi := tangent_actual_resistance_information_budget Q hQ p hp u n
  have hs := tangent_actual_sqrt_resistance_information_budget Q hQ p hp u n
  have hres0 : 0 ≤ ∑ s ∈ range n, pairSum (fun i j =>
      p (u + s) i * p (u + s) j * Part2.CNDPhysical.resistance p (u + s) i j) := by
    apply sum_nonneg
    intro s _
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    split_ifs
    · exact mul_nonneg (mul_nonneg ((hp _).1 _) ((hp _).1 _))
        (Part2.CNDPhysical.actual_resistance_nonneg p hp _ _ _)
    · exact le_rfl
  have hD : 0 ≤ D := by dsimp [D]; linarith
  have hA : 0 ≤ 8 * H * Real.sqrt L / Part2.CNDPhysical.c0 :=
    div_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) (Real.sqrt_nonneg _)) Part2.CNDPhysical.c0_pos.le
  have hB : 0 ≤ 4 * (4 * H * L + R * Fintype.card ι) / Part2.CNDPhysical.c0 := by
    exact div_nonneg (mul_nonneg (by norm_num)
      (add_nonneg (mul_nonneg (mul_nonneg (by norm_num) hH) hL)
        (mul_nonneg hR.le (Nat.cast_nonneg _)))) Part2.CNDPhysical.c0_pos.le
  have ht := sum_le_sum (s := range n) (fun s _ => actualGamma_le_linear_resistance p hp (u+s) H L R hH hL hR)
  simp only [sum_add_distrib, ← mul_sum] at ht
  have hb := add_le_add (mul_le_mul_of_nonneg_left hs hA) (mul_le_mul_of_nonneg_left hi hB)
  have hc := sqrt_information_constant n L D (Nat.cast_nonneg n) hL hD
  have heq : 8 * H * Real.sqrt L / Part2.CNDPhysical.c0 * Real.sqrt (3 * n * D / 4) +
      4 * (4 * H * L + R * Fintype.card ι) / Part2.CNDPhysical.c0 * ((3 / 2 : ℝ) * D) =
      actualQ Q p u n H L R := by
    unfold actualQ
    calc
      _ = (H / Part2.CNDPhysical.c0) * (8 * Real.sqrt L * Real.sqrt (3 * n * D / 4)) +
          (6 / Part2.CNDPhysical.c0) * (4 * H * L + R * Fintype.card ι) * D := by ring
      _ = _ := by rw [hc]; dsimp [D]; ring
  exact ht.trans (hb.trans_eq heq)

theorem actualGamma_zeroR (p : ℕ → ι → ℝ) (t : ℕ) (H L : ℝ) :
    actualGamma p t H L 0 = 0 := by
  simp [actualGamma, pairSum, Part2.CNDPhysical.actualSaturatedRadius, Part2.CNDPhysical.saturatedRadius]

theorem actualPayment_zeroR (p : ℕ → ι → ℝ) (t : ℕ) (H L : ℝ) (a : ι) :
    actualPayment p t H L 0 a = 0 := by
  simp [actualPayment, Part2.CNDPhysical.actualSaturatedRadius, Part2.CNDPhysical.saturatedRadius]

theorem actualPayment_bounds_nonnegR (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex)
    (t : ℕ) (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (a : ι) :
    0 ≤ actualPayment p t H L R a ∧ actualPayment p t H L R a ≤ 4 * R / Part2.CNDPhysical.c0 := by
  by_cases hz : R = 0
  · subst R; simp [actualPayment_zeroR]
  · exact actualPayment_bounds p hp t H L R hH hL (lt_of_le_of_ne hR (Ne.symm hz)) a

theorem actualPayment_mean_nonnegR (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex)
    (t : ℕ) (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (∑ i, p t i * actualPayment p t H L R i) = 2 * actualGamma p t H L R := by
  by_cases hz : R = 0
  · subst R; simp [actualPayment_zeroR, actualGamma_zeroR]
  · exact actualPayment_mean p hp t H L R hH hL (lt_of_le_of_ne hR (Ne.symm hz))

def branchedQ (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ) (u n : ℕ) (H L R : ℝ) : ℝ :=
  if R = 0 then 0 else actualQ Q p u n H L R

theorem actualGamma_sum_le_branchedQ (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) (H L R : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (∑ s ∈ range n, actualGamma p (u + s) H L R) ≤ branchedQ Q p u n H L R := by
  by_cases hz : R = 0
  · subst R; simp [branchedQ, actualGamma_zeroR]
  · simpa only [branchedQ, if_neg hz] using
      actualGamma_sum_le_actualQ Q hQ p hp u n H L R hH hL (lt_of_le_of_ne hR (Ne.symm hz))

end Part2.CNDInformation

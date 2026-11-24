import staging.cnd20261024.prod.Dyadic

namespace Part2.CNDProd
open Finset
noncomputable section
variable {ι : Type*} [Fintype ι]

/-- Two actual probability averages of a common supported loss range. -/
theorem averages_sub_le (μ ν ℓ : ι → ℝ) (D : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1)
    (hdiff : ∀ i j, μ i ≠ 0 → ν j ≠ 0 → ℓ i - ℓ j ≤ D) :
    (∑ i, μ i * ℓ i) - (∑ j, ν j * ℓ j) ≤ D := by
  have hid : (∑ i, μ i * ℓ i) - (∑ j, ν j * ℓ j) =
      ∑ i, ∑ j, μ i * ν j * (ℓ i - ℓ j) := by
    simp_rw [mul_sub, sum_sub_distrib]
    have h₁ (i : ι) : (∑ j, μ i * ν j * ℓ i) = μ i * ℓ i := by
      rw [← sum_mul, ← mul_sum, hνsum, mul_one]
    have h₂ (i : ι) : (∑ j, μ i * ν j * ℓ j) = μ i * (∑ j, ν j * ℓ j) := by
      simp_rw [mul_assoc, ← mul_sum]
    simp_rw [h₁, h₂, ← sum_mul, hμsum, one_mul]
  rw [hid]
  calc
    _ ≤ ∑ i, ∑ j, μ i * ν j * D := by
      apply sum_le_sum; intro i _
      apply sum_le_sum; intro j _
      by_cases hi : μ i = 0
      · simp [hi]
      by_cases hj : ν j = 0
      · simp [hj]
      exact mul_le_mul_of_nonneg_left (hdiff i j hi hj) (mul_nonneg (hμ i) (hν j))
    _ = D := by
      have hh (i : ι) : (∑ j, μ i * ν j * D) = μ i * D := by
        rw [← sum_mul, ← mul_sum, hνsum, mul_one]
      simp_rw [hh]
      rw [← sum_mul, hμsum, one_mul]

theorem averages_abs_sub_le (μ ν ℓ : ι → ℝ) (D : ℝ)
    (hμ : ∀ i, 0 ≤ μ i) (hν : ∀ i, 0 ≤ ν i)
    (hμsum : ∑ i, μ i = 1) (hνsum : ∑ i, ν i = 1)
    (hdiff : ∀ i j, μ i ≠ 0 → ν j ≠ 0 → |ℓ i - ℓ j| ≤ D) :
    |(∑ i, μ i * ℓ i) - (∑ j, ν j * ℓ j)| ≤ D := by
  apply abs_le.mpr
  constructor
  · have h := averages_sub_le ν μ ℓ D hν hμ hνsum hμsum (by
      intro i j hi hj
      have hh := (abs_le.mp (hdiff j i hj hi)).1
      linarith)
    linarith
  · exact averages_sub_le μ ν ℓ D hμ hν hμsum hνsum
      (fun i j hi hj => (abs_le.mp (hdiff i j hi hj)).2)

/-- Coupling and positive source mass force every actual row destination into p's support. -/
theorem positive_destination (q p : ι → ℝ) (M : ι → ι → ℝ)
    (hq : ∀ i, 0 < q i) (hM : ∀ i j, 0 ≤ M i j)
    (hc : ∀ j, ∑ i, q i * M i j = p j) {k j : ι} (hkj : M k j ≠ 0) :
    0 < p j := by
  rw [← hc j]
  exact (mul_pos (hq k) (lt_of_le_of_ne (hM k j) (Ne.symm hkj))).trans_le
    (single_le_sum (fun i _ => mul_nonneg (hq i).le (hM i j)) (mem_univ k))

/-- Actual remapped row losses inherit the supported 2W span. -/
theorem transport_row_span (q p ℓ : ι → ℝ) (M : ι → ι → ℝ) (W : ℝ)
    (hq : ∀ i, 0 < q i) (hp : ∀ i, 0 ≤ p i) (hpsum : ∑ i, p i = 1)
    (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1)
    (hc : ∀ j, ∑ i, q i * M i j = p j)
    (hspan : ∀ i j, 0 < p i → 0 < p j → |ℓ i - ℓ j| ≤ 2 * W) (k : ι) :
    |(∑ j, p j * ℓ j) - (∑ j, M k j * ℓ j)| ≤ 2 * W := by
  apply averages_abs_sub_le p (M k) ℓ (2 * W) hp (hM k) hpsum (hrow k)
  intro i j hi hj
  exact hspan i j (lt_of_le_of_ne (hp i) (Ne.symm hi))
    (positive_destination q p M hq hM hc hj)

def rate (W A m : ℝ) : ℝ := min (1 / (4 * W)) (Real.sqrt A / (2 * W * Real.sqrt m))

/-- The actual safe remapping's destination constraints imply pairwise row
loss span, including its repaired zero-source rows. -/
theorem allowed_rows_span (M : ι → ι → ℝ) (g b : ι → ℝ) (m : ι) (W : ℝ)
    (hM : ∀ k j, 0 ≤ M k j) (hrow : ∀ k, ∑ j, M k j = 1)
    (hmin : ∀ j, g m ≤ g j)
    (hallowed : ∀ k j, M k j ≠ 0 → g j ≤ g m + W)
    (hb : ∀ i j, b j - b i ≤ W) (i k : ι) :
    |(∑ j, M i j * (g j + b j)) - (∑ j, M k j * (g j + b j))| ≤ 2 * W := by
  apply averages_abs_sub_le (M i) (M k) (fun j => g j + b j) (2 * W)
    (hM i) (hM k) (hrow i) (hrow k)
  intro a c ha hc
  have h₁ := hallowed i a ha
  have h₂ := hallowed k c hc
  have h₃ := hmin a
  have h₄ := hmin c
  have h₅ := hb a c
  have h₆ := hb c a
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem allowed_row_dominates (M : ι → ι → ℝ) (g b : ι → ℝ) (W : ℝ)
    (hM : ∀ k j, 0 ≤ M k j) (hrow : ∀ k, ∑ j, M k j = 1)
    (hgap : ∀ k j, M k j ≠ 0 → j = k ∨ W ≤ g k - g j)
    (hb : ∀ i j, b j - b i ≤ W) (k : ι) :
    (∑ j, M k j * (g j + b j)) ≤ g k + b k := by
  calc
    _ ≤ ∑ j, M k j * (g k + b k) := by
      apply sum_le_sum
      intro j _
      by_cases hz : M k j = 0
      · simp [hz]
      · have h : g j + b j ≤ g k + b k := by
          rcases hgap k j hz with rfl | h
          · exact le_rfl
          · linarith [hb k j]
        exact mul_le_mul_of_nonneg_left h (hM k j)
    _ = _ := by rw [← sum_mul, hrow, one_mul]

theorem rate_pos {W A m : ℝ} (hW : 0 < W) (hA : 0 < A) (hm : 0 < m) :
    0 < rate W A m := by unfold rate; exact lt_min (by positivity) (by positivity)

theorem rate_cap {W A m : ℝ} (hW : 0 < W) : rate W A m * (2 * W) ≤ 1 / 2 := by
  have h := mul_le_mul_of_nonneg_right (min_le_left (1 / (4 * W))
    (Real.sqrt A / (2 * W * Real.sqrt m))) (show 0 ≤ 2 * W by positivity)
  have hid : 1 / (4 * W) * (2 * W) = (1 : ℝ) / 2 := by field_simp; ring
  rw [hid] at h
  exact h

/-- The paper's exact long-block branch, with its prescribed min learning rate. -/
theorem long_block_tuning {W A m : ℝ} (hW : 0 < W) (hA : 0 < A) (hm : 0 < m)
    (hlong : 4 * A ≤ m) :
    A / rate W A m + 4 * rate W A m * W ^ 2 * m =
      4 * W * Real.sqrt A * Real.sqrt m := by
  have hsA := Real.sq_sqrt hA.le
  have hsm := Real.sq_sqrt hm.le
  have hA' := Real.sqrt_pos.mpr hA
  have hm' := Real.sqrt_pos.mpr hm
  have hroot : 2 * Real.sqrt A ≤ Real.sqrt m := by nlinarith
  have hle : Real.sqrt A / (2 * W * Real.sqrt m) ≤ 1 / (4 * W) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith
  rw [rate, min_eq_right hle]
  field_simp
  nlinarith

/-- Short blocks use the actual per-round bound, not the potential estimate. -/
theorem short_block_tuning {W A m : ℝ} (hW : 0 ≤ W) (hA : 0 ≤ A) (hm : 0 ≤ m)
    (hshort : m ≤ 4 * A) : 2 * W * m ≤ 4 * W * Real.sqrt A * Real.sqrt m := by
  have hsm := Real.sq_sqrt hm
  have hsA := Real.sq_sqrt hA
  have hroot : Real.sqrt m ≤ 2 * Real.sqrt A := by
    nlinarith [Real.sqrt_nonneg m, Real.sqrt_nonneg A]
  have hp := mul_le_mul_of_nonneg_left hroot (Real.sqrt_nonneg m)
  have hp' := mul_le_mul_of_nonneg_left hp (show 0 ≤ 2 * W by positivity)
  nlinarith

end
end Part2.CNDProd

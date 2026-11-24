import Part2.Intervals
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp

noncomputable section

namespace Part2.CNDRateAbsorption

theorem sqrt_product_bound (n a d K L : ℝ) (hn : 0 ≤ n)
    (hd : 0 ≤ d) (hK : 0 ≤ K) (hL : 0 ≤ L)
    (haU : a ≤ K * L) (hdU : d ≤ K * L) :
    Real.sqrt (n * a * d) ≤ Real.sqrt n * K * L := by
  have hKL : 0 ≤ K * L := mul_nonneg hK hL
  have hprod : n * a * d ≤ n * (K * L) * (K * L) :=
    mul_le_mul (mul_le_mul_of_nonneg_left haU hn) hdU hd (mul_nonneg hn hKL)
  calc
    _ ≤ Real.sqrt (n * (K * L) * (K * L)) := Real.sqrt_le_sqrt hprod
    _ = Real.sqrt n * K * L := by
      rw [mul_assoc, Real.sqrt_mul hn, Real.sqrt_mul_self hKL]
      ring

theorem absorb_two_branches (P H K n L A B C Λ : ℝ)
    (hH : 0 ≤ H) (hK : 1 ≤ K) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hΛ : Λ ≤ L)
    (hsmall : P ≤ C * H * n)
    (hlarge : P ≤ A * H * K * Real.sqrt n * L + B * H * K ^ 2 * L ^ 2 + C * H * Λ) :
    P ≤ (A + B + C) * H * K * Real.sqrt n * L ^ 2 := by
  have hn0 : 0 ≤ n := by linarith
  have hK0 : 0 ≤ K := by linarith
  have hx : 1 ≤ Real.sqrt n := by
    simpa using Real.sqrt_le_sqrt hn
  have hx0 : 0 ≤ Real.sqrt n := Real.sqrt_nonneg _
  have hL2 : 1 ≤ L ^ 2 := by nlinarith
  have hLL : L ≤ L ^ 2 := by nlinarith
  have hKx : 1 ≤ K * Real.sqrt n := by nlinarith
  have hbase : 0 ≤ H * K * Real.sqrt n * L ^ 2 := by positivity
  by_cases hcase : Real.sqrt n ≤ K
  · have hnK : n ≤ K * Real.sqrt n := by
      nlinarith [Real.sq_sqrt hn0, mul_nonneg hx0 (sub_nonneg.mpr hcase)]
    calc
      P ≤ C * H * n := hsmall
      _ ≤ C * H * (K * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hnK (mul_nonneg hC hH)
      _ ≤ C * H * (K * Real.sqrt n) * L ^ 2 :=
        le_mul_of_one_le_right (by positivity) hL2
      _ ≤ (A + B + C) * H * K * Real.sqrt n * L ^ 2 := by
        have hcoef : C ≤ A + B + C := by linarith
        have := mul_le_mul_of_nonneg_right hcoef hbase
        nlinarith only [this]
  · have hKsq : K ^ 2 ≤ K * Real.sqrt n := by
      nlinarith [mul_nonneg hK0 (sub_nonneg.mpr (le_of_not_ge hcase))]
    have ht1 : A * H * K * Real.sqrt n * L ≤
        A * H * K * Real.sqrt n * L ^ 2 :=
      mul_le_mul_of_nonneg_left hLL (by positivity)
    have ht2 : B * H * K ^ 2 * L ^ 2 ≤ B * H * (K * Real.sqrt n) * L ^ 2 := by
      gcongr
    have ht3 : C * H * Λ ≤ C * H * (K * Real.sqrt n) * L ^ 2 := by
      have hΛU : Λ ≤ (K * Real.sqrt n) * L ^ 2 :=
        hΛ.trans (hLL.trans (le_mul_of_one_le_left (sq_nonneg L) hKx))
      have := mul_le_mul_of_nonneg_left hΛU (mul_nonneg hC hH)
      nlinarith only [this]
    nlinarith only [hlarge, ht1, ht2, ht3]

theorem normalized_Q_bound (H R c K n L a d : ℝ)
    (hR : 0 ≤ R) (hRH : R ≤ H) (hc : 0 < c)
    (hK : 1 ≤ K) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (haU : a ≤ K * L) (hdU : d ≤ K * L) :
    c * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
      (6 / c) * (4 * H * a + R * K) * d) ≤
      8 * H * K * Real.sqrt n * L + 30 * H * K ^ 2 * L ^ 2 := by
  have hH : 0 ≤ H := hR.trans hRH
  have hK0 : 0 ≤ K := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hs3 : Real.sqrt 3 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hs := sqrt_product_bound n a d K L hn0 hd hK0 hL0 haU hdU
  have ht1 : 4 * Real.sqrt 3 * H * Real.sqrt (n * a * d) ≤
      8 * H * K * Real.sqrt n * L := by
    calc
      _ ≤ 4 * 2 * H * (Real.sqrt n * K * L) := by gcongr
      _ = _ := by ring
  have hrU : R * K ≤ H * K * L :=
    (mul_le_mul_of_nonneg_right hRH hK0).trans
      (le_mul_of_one_le_right (mul_nonneg hH hK0) hL)
  have hiU : 4 * H * a + R * K ≤ 5 * H * K * L := by
    have := mul_le_mul_of_nonneg_left haU (show 0 ≤ 4 * H by positivity)
    nlinarith only [this, hrU]
  have ht2 : 6 * (4 * H * a + R * K) * d ≤ 30 * H * K ^ 2 * L ^ 2 := by
    calc
      _ ≤ 6 * (5 * H * K * L) * (K * L) := by gcongr
      _ = _ := by ring
  have heq : c * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
      (6 / c) * (4 * H * a + R * K) * d) =
      4 * Real.sqrt 3 * H * Real.sqrt (n * a * d) + 6 * (4 * H * a + R * K) * d := by
    field_simp
    <;> ring
  rw [heq]
  linarith

theorem actual_budget_uniform_rate (P H R c K n L a d Λ : ℝ)
    (hR : 0 ≤ R) (hRH : R ≤ H) (hc : 0 < c)
    (hK : 1 ≤ K) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (haU : a ≤ K * L) (hdU : d ≤ K * L)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L)
    (hlinear : P ≤ (4 * R / c) * n)
    (hcurved : P ≤ 4 * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
      (6 / c) * (4 * H * a + R * K) * d) + (4 * R / c) * Λ) :
    P ≤ (156 / c) * H * K * Real.sqrt n * L ^ 2 := by
  have hH : 0 ≤ H := hR.trans hRH
  have hlin := mul_le_mul_of_nonneg_left hlinear (le_of_lt hc)
  have hcurve := mul_le_mul_of_nonneg_left hcurved (le_of_lt hc)
  have heqlin : c * ((4 * R / c) * n) = 4 * R * n := by field_simp
  have heqcurve : c * (4 * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
      (6 / c) * (4 * H * a + R * K) * d) + (4 * R / c) * Λ) =
      4 * (c * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
      (6 / c) * (4 * H * a + R * K) * d)) + 4 * R * Λ := by
    field_simp
    <;> ring
  rw [heqlin] at hlin
  rw [heqcurve] at hcurve
  have hQ := normalized_Q_bound H R c K n L a d hR hRH hc hK hn hL ha hd haU hdU
  have hsmall : c * P ≤ 4 * H * n := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRH) (show 0 ≤ n by linarith)]
  have hlarge : c * P ≤ 32 * H * K * Real.sqrt n * L +
      120 * H * K ^ 2 * L ^ 2 + 4 * H * Λ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hRH) hΛ0]
  have hfinal := absorb_two_branches (c * P) H K n L 32 120 4 Λ hH hK hn hL
    (by norm_num) (by norm_num) (by norm_num) hΛ hsmall hlarge
  have heqfinal : c * ((156 / c) * H * K * Real.sqrt n * L ^ 2) =
      (32 + 120 + 4) * H * K * Real.sqrt n * L ^ 2 := by field_simp <;> ring
  apply (mul_le_mul_left hc).mp
  rw [heqfinal]
  exact hfinal

/-- The sub-Gaussian confidence scale enlarges `a`, but does not enlarge the
information increment `d` or the logarithmic tail term `Λ`. -/
theorem actual_budget_sg_rate (P H R c K n L a d Λ : ℝ)
    (hR : 0 ≤ R) (hRH : R ≤ H) (hc : 0 < c)
    (hK : 1 ≤ K) (hn : 1 ≤ n) (hL : 1 ≤ L)
    (ha : 0 ≤ a) (hd : 0 ≤ d) (haU : a ≤ 4 * K * L) (hdU : d ≤ K * L)
    (hΛ0 : 0 ≤ Λ) (hΛ : Λ ≤ L)
    (hlinear : P ≤ (4 * R / c) * n)
    (hcurved : P ≤ 4 * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
      (6 / c) * (4 * H * a + R * K) * d) + (4 * R / c) * Λ) :
    P ≤ (468 / c) * H * K * Real.sqrt n * L ^ 2 := by
  have hH : 0 ≤ H := hR.trans hRH
  have hK0 : 0 ≤ K := by linarith
  have hn0 : 0 ≤ n := by linarith
  have hL0 : 0 ≤ L := by linarith
  have hs : Real.sqrt (n * a * d) ≤ 2 * (Real.sqrt n * K * L) := by
    have hs' := sqrt_product_bound n (a / 4) d K L hn0 hd hK0 hL0
      (by linarith) hdU
    calc
      _ = Real.sqrt (4 * (n * (a / 4) * d)) := by ring_nf
      _ = 2 * Real.sqrt (n * (a / 4) * d) := by
        have hs4 : Real.sqrt (4 : ℝ) = 2 := by
          rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
            Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]
        have hscaled : 0 ≤ n * (a / 4) * d :=
          mul_nonneg (mul_nonneg hn0 (div_nonneg ha (by norm_num))) hd
        rw [mul_comm (4 : ℝ), Real.sqrt_mul hscaled, hs4, mul_comm]
      _ ≤ _ := mul_le_mul_of_nonneg_left hs' (by norm_num)
  have hs3 : Real.sqrt 3 ≤ 7 / 4 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hrU : R * K ≤ H * K * L :=
    (mul_le_mul_of_nonneg_right hRH hK0).trans
      (le_mul_of_one_le_right (mul_nonneg hH hK0) hL)
  have hiU : 4 * H * a + R * K ≤ 17 * H * K * L := by
    have hterm := mul_le_mul_of_nonneg_left haU (show 0 ≤ 4 * H by positivity)
    nlinarith only [hterm, hrU]
  have hsmall : c * P ≤ 4 * H * n := by
    calc
      _ ≤ c * ((4 * R / c) * n) := mul_le_mul_of_nonneg_left hlinear hc.le
      _ = 4 * R * n := by field_simp
      _ ≤ _ := by gcongr
  have hlarge : c * P ≤ 56 * H * K * Real.sqrt n * L +
      408 * H * K ^ 2 * L ^ 2 + 4 * H * Λ := by
    calc
      _ ≤ c * (4 * ((4 * Real.sqrt 3 / c) * H * Real.sqrt (n * a * d) +
          (6 / c) * (4 * H * a + R * K) * d) + (4 * R / c) * Λ) :=
        mul_le_mul_of_nonneg_left hcurved hc.le
      _ = 4 * (4 * Real.sqrt 3 * H * Real.sqrt (n * a * d) +
          6 * (4 * H * a + R * K) * d) + 4 * R * Λ := by field_simp
      _ ≤ 4 * (4 * (7 / 4) * H * (2 * (Real.sqrt n * K * L)) +
          6 * (17 * H * K * L) * (K * L)) + 4 * H * Λ := by gcongr
      _ = _ := by ring
  have hfinal := absorb_two_branches (c * P) H K n L 56 408 4 Λ hH hK hn hL
    (by norm_num) (by norm_num) (by norm_num) hΛ hsmall hlarge
  apply (mul_le_mul_iff_right₀ hc).mp
  calc
    c * P ≤ (56 + 408 + 4) * H * K * Real.sqrt n * L ^ 2 := hfinal
    _ = c * ((468 / c) * H * K * Real.sqrt n * L ^ 2) := by
      field_simp
      ring

end Part2.CNDRateAbsorption

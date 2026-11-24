import Part2.ExponentialExperts
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Exact quadratic remainder for finite exponential experts

Companion to `ExponentialExperts`: E6 with the exact coefficient kappa,
and substitution in E7/E8. All assertions concern exact real arithmetic.
-/

namespace Part2.ExponentialRemainder

noncomputable section

open Finset
open Part2.ExponentialExperts

/-- Continuous-value convention at zero; only nonnegative arguments are used. -/
def kappa (b : ℝ) : ℝ := if b = 0 then 1 / 2 else psi b / b ^ 2

def remainderIntegral (z : ℝ) : ℝ :=
  ∫ s in (0 : ℝ)..1, (1 - s) * Real.exp (s * z)

theorem remainder_continuous (z : ℝ) :
    Continuous (fun s : ℝ => (1 - s) * Real.exp (s * z)) := by
  fun_prop

theorem remainder_identity (z : ℝ) :
    z ^ 2 * remainderIntegral z = psi z := by
  have hd (s : ℝ) : HasDerivAt
      (fun s : ℝ => ((1 - s) * z + 1) * Real.exp (s * z))
      (z ^ 2 * ((1 - s) * Real.exp (s * z))) s := by
    convert (((hasDerivAt_const s 1).sub (hasDerivAt_id s)).mul_const z |>.add_const 1).mul
      (((hasDerivAt_id s).mul_const z).exp) using 1 <;> simp <;> ring
  have hint : IntervalIntegrable
      (fun s : ℝ => z ^ 2 * ((1 - s) * Real.exp (s * z)))
      MeasureTheory.volume 0 1 := by
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (remainder_continuous z)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun s _ => hd s) hint
  rw [intervalIntegral.integral_const_mul] at h
  simpa [remainderIntegral, psi, sub_sub, add_comm] using h

theorem remainderIntegral_mono {z b : ℝ} (hzb : z ≤ b) :
    remainderIntegral z ≤ remainderIntegral b := by
  apply intervalIntegral.integral_mono_on (by norm_num)
    ((remainder_continuous z).intervalIntegrable 0 1)
    ((remainder_continuous b).intervalIntegrable 0 1)
  intro s hs
  apply mul_le_mul_of_nonneg_left _ (sub_nonneg.mpr hs.2)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hzb hs.1)

theorem remainderIntegral_eq_kappa {b : ℝ} (hb : 0 < b) :
    remainderIntegral b = kappa b := by
  rw [kappa, if_neg (ne_of_gt hb)]
  apply (eq_div_iff (pow_ne_zero 2 (ne_of_gt hb))).mpr
  nlinarith [remainder_identity b]

/-- E6 scalar inequality, including the degenerate radius zero. -/
theorem psi_le_kappa_sq {z b : ℝ} (hb : 0 ≤ b) (hz : |z| ≤ b) :
    psi z ≤ kappa b * z ^ 2 := by
  rcases eq_or_lt_of_le hb with h | h
  · have hb0 : b = 0 := h.symm
    have hz0 : z = 0 := abs_nonpos_iff.mp (by simpa [hb0] using hz)
    simp [hz0, psi]
  · rw [← remainder_identity z]
    have hi := remainderIntegral_mono ((le_abs_self z).trans hz)
    rw [remainderIntegral_eq_kappa h] at hi
    nlinarith [sq_nonneg z]

variable {E : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- E6's observable quadratic cost, with any common absolute bound `b`. -/
def quadraticCost (w z : E → ℝ) (b : ℝ) : ℝ :=
  kappa b * ∑ e, beta w e * (z e) ^ 2

/-- The all-virtual-expert cost equals the active-expert expression in E6. -/
theorem quadraticCost_eq_active (w z eta x : E → ℝ) (b : ℝ) (active : Finset E)
    (hz : ∀ e ∈ active, z e = eta e * x e)
    (hsleep : ∀ e ∉ active, z e = 0) :
    quadraticCost w z b =
      kappa b * ∑ e ∈ active, beta w e * (eta e) ^ 2 * (x e) ^ 2 := by
  unfold quadraticCost
  congr 1
  calc
    _ = ∑ e ∈ active, beta w e * (z e) ^ 2 := by
      symm
      apply Finset.sum_subset (Finset.subset_univ active)
      intro e _ he
      simp [hsleep e he]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e he
      rw [hz e he]
      ring

theorem remainder_mean_le_quadraticCost (w z : E → ℝ) (b : ℝ)
    (hw : ∀ e, 0 < w e) (hb : 0 ≤ b) (hz : ∀ e, |z e| ≤ b) :
    (∑ e, beta w e * psi (z e)) ≤ quadraticCost w z b := by
  unfold quadraticCost
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro e _
  have h := mul_le_mul_of_nonneg_left (psi_le_kappa_sq hb (hz e))
    (beta_pos w hw e).le
  convert h using 1 <;> ring

/-- E6, with no restriction on positive learning rates. -/
theorem increment_bounds (w z : E → ℝ) (b : ℝ)
    (hw : ∀ e, 0 < w e) (hb : 0 ≤ b) (hz : ∀ e, |z e| ≤ b)
    (hzero : (∑ e, w e * z e) = 0) :
    0 ≤ increment w z ∧ increment w z ≤ quadraticCost w z b := by
  exact ⟨(increment_identity_nonneg w z hw hzero).2,
    (increment_le_remainder w z hw hzero).trans
      (remainder_mean_le_quadraticCost w z b hw hb hz)⟩

theorem sum_increment_le_quadraticCost (n : ℕ) (w z : ℕ → E → ℝ)
    (b : ℕ → ℝ) (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hb : ∀ t < n, 0 ≤ b t) (hz : ∀ t < n, ∀ e, |z t e| ≤ b t)
    (hzero : ∀ t < n, (∑ e, w t e * z t e) = 0) :
    (∑ t ∈ range n, increment (w t) (z t)) ≤
      ∑ t ∈ range n, quadraticCost (w t) (z t) (b t) := by
  apply Finset.sum_le_sum
  intro t ht
  have ht' := mem_range.mp ht
  exact (increment_bounds (w t) (z t) (b t)
    (trajectory_pos n w z hinit hupdate t (by omega))
    (hb t ht') (hz t ht') (hzero t ht')).2

theorem normalized_log_mass_le_quadraticCost (n : ℕ) (w z : ℕ → E → ℝ)
    (b : ℕ → ℝ) (hinit : ∀ e, 0 < w 0 e) (hnorm : mass (w 0) = 1)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hb : ∀ t < n, 0 ≤ b t) (hz : ∀ t < n, ∀ e, |z t e| ≤ b t)
    (hzero : ∀ t < n, (∑ e, w t e * z t e) = 0) :
    Real.log (mass (w n)) ≤ ∑ t ∈ range n, quadraticCost (w t) (z t) (b t) := by
  rw [normalized_log_mass n w z hinit hnorm hupdate]
  exact sum_increment_le_quadraticCost n w z b hinit hupdate hb hz hzero

/-- E7 with the exact E6 quadratic costs on an arbitrary local segment. -/
theorem segment_regret_quadratic (n : ℕ) (w z : ℕ → E → ℝ)
    (b : ℕ → ℝ) (x r : ℕ → ℝ) (eta : ℝ) (heta : 0 < eta) (e : E)
    (hinit : ∀ i, 0 < w 0 i)
    (hupdate : ∀ t < n, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hb : ∀ t < n, 0 ≤ b t) (hbound : ∀ t < n, ∀ i, |z t i| ≤ b t)
    (hzero : ∀ t < n, (∑ i, w t i * z t i) = 0)
    (hz : ∀ t < n, z t e = eta * x t) (hr : ∀ t < n, r t ≤ x t) :
    (∑ t ∈ range n, r t) ≤
      (Real.log (1 / beta (w 0) e) +
        ∑ t ∈ range n, quadraticCost (w t) (z t) (b t)) / eta := by
  apply (segment_regret n w z x r eta heta e hinit hupdate hz hr).trans
  exact div_le_div_of_nonneg_right
    (add_le_add_left (sum_increment_le_quadraticCost n w z b hinit hupdate
      hb hbound hzero) _) heta.le

/-- E8 from a normalized initial virtual mass and a birth at time zero. -/
theorem birth_regret_quadratic (n : ℕ) (w z : ℕ → E → ℝ)
    (b : ℕ → ℝ) (x r : ℕ → ℝ) (eta pi : ℝ) (heta : 0 < eta) (e : E)
    (hinit : ∀ i, 0 < w 0 i) (hnorm : mass (w 0) = 1) (hbirth : w 0 e = pi)
    (hupdate : ∀ t < n, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hb : ∀ t < n, 0 ≤ b t) (hbound : ∀ t < n, ∀ i, |z t i| ≤ b t)
    (hzero : ∀ t < n, (∑ i, w t i * z t i) = 0)
    (hz : ∀ t < n, z t e = eta * x t) (hr : ∀ t < n, r t ≤ x t) :
    (∑ t ∈ range n, r t) ≤
      (Real.log (1 / pi) + ∑ t ∈ range n, quadraticCost (w t) (z t) (b t)) / eta := by
  apply (birth_regret n w z x r eta pi heta e hinit hbirth hupdate hz hr).trans
  exact div_le_div_of_nonneg_right
    (add_le_add_left (normalized_log_mass_le_quadraticCost n w z b hinit hnorm
      hupdate hb hbound hzero) _) heta.le

/-- E8 at an arbitrary birth time `m`: regret sums only the `n` rounds
after birth, while the quadratic cost sums all `m+n` rounds from the
normalized global origin. No normalization is imposed at birth. -/
theorem birth_segment_regret_quadratic (m n : ℕ) (w z : ℕ → E → ℝ)
    (b : ℕ → ℝ) (x r : ℕ → ℝ) (eta pi : ℝ) (heta : 0 < eta) (e : E)
    (hinit : ∀ i, 0 < w 0 i) (hnorm : mass (w 0) = 1) (hbirth : w m e = pi)
    (hupdate : ∀ t < m + n, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hb : ∀ t < m + n, 0 ≤ b t)
    (hbound : ∀ t < m + n, ∀ i, |z t i| ≤ b t)
    (hzero : ∀ t < m + n, (∑ i, w t i * z t i) = 0)
    (hz : ∀ t < n, z (m + t) e = eta * x t)
    (hr : ∀ t < n, r t ≤ x t) :
    (∑ t ∈ range n, r t) ≤
      (Real.log (1 / pi) +
        ∑ t ∈ range (m + n), quadraticCost (w t) (z t) (b t)) / eta := by
  have hp := trajectory_pos (m + n) w z hinit hupdate
  have hu : ∀ t < n, ∀ i,
      w (m + (t + 1)) i = step (w (m + t)) (z (m + t)) i := by
    intro t ht i
    simpa [Nat.add_assoc] using hupdate (m + t) (by omega) i
  have h := birth_regret n (fun t => w (m + t)) (fun t => z (m + t))
    x r eta pi heta e (by simpa using hp m (by omega))
    (by simpa using hbirth) hu hz hr
  apply h.trans
  exact div_le_div_of_nonneg_right
    (add_le_add_left (normalized_log_mass_le_quadraticCost (m + n) w z b
      hinit hnorm hupdate hb hbound hzero) _) heta.le

end

end Part2.ExponentialRemainder

import Part2.Prod
import Part2.Intervals

/-!
# Finite sleeping exponential experts: exact potential accounting

This is an independent deterministic companion to `Prod`, not a replacement
for its mass-conservation result. All experts, including future and retired
experts, remain in the finite virtual mass. Indices are zero based.

The exact kappa(b) quadratic remainder inequality (E6) is not asserted here.
No statistical confidence, transport, or floating-point property is asserted.
-/

namespace Part2.ExponentialExperts

noncomputable section

open Finset

variable {E K : Type*} [Fintype E] [DecidableEq E] [Nonempty E] [Fintype K]

def mass (w : E → ℝ) : ℝ := ∑ e, w e

def beta (w : E → ℝ) (e : E) : ℝ := w e / mass w

def psi (z : ℝ) : ℝ := Real.exp z - 1 - z

def step (w z : E → ℝ) (e : E) : ℝ := w e * Real.exp (z e)

def increment (w z : E → ℝ) : ℝ := Real.log (mass (step w z) / mass w)

theorem psi_nonneg (z : ℝ) : 0 ≤ psi z := by
  have h := Real.add_one_le_exp z
  dsimp [psi]
  linarith

theorem mass_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) : 0 < mass w := by
  exact Finset.sum_pos (fun e _ => hw e) Finset.univ_nonempty

theorem beta_pos (w : E → ℝ) (hw : ∀ e, 0 < w e) (e : E) : 0 < beta w e :=
  div_pos (hw e) (mass_pos w hw)

theorem beta_le_one (w : E → ℝ) (hw : ∀ e, 0 < w e) (e : E) : beta w e ≤ 1 := by
  apply (div_le_one (mass_pos w hw)).mpr
  exact Finset.single_le_sum (fun i _ => (hw i).le) (Finset.mem_univ e)

theorem beta_sum (w : E → ℝ) (hw : ∀ e, 0 < w e) : (∑ e, beta w e) = 1 := by
  simp only [beta, ← Finset.sum_div]
  exact div_self (ne_of_gt (mass_pos w hw))

theorem step_pos (w z : E → ℝ) (hw : ∀ e, 0 < w e) (e : E) :
    0 < step w z e := mul_pos (hw e) (Real.exp_pos _)

theorem sleeping_unchanged (w z : E → ℝ) (e : E) (hz : z e = 0) :
    step w z e = w e := by simp [step, hz]

/-- The existing advice construction supplies the zero first-order term even
when different experts use different fixed learning rates. -/
theorem advice_zero_first_order (active : Finset E) (eta w : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ)
    (hDen : (∑ e ∈ active, Part2.Prod.coefficient eta w e) ≠ 0) :
    (∑ e, w e * (eta e *
      Part2.Prod.excess active eta w advice loss e)) = 0 := by
  convert Part2.Prod.weighted_excess_zero active eta w advice loss hDen using 1
  apply Finset.sum_congr rfl
  intro e _
  dsimp [Part2.Prod.coefficient]
  ring

/-- E5 before taking logs: no linearized update or mass conservation is used. -/
theorem mass_identity (w z : E → ℝ)
    (hzero : (∑ e, w e * z e) = 0) :
    mass (step w z) = mass w + ∑ e, w e * psi (z e) := by
  have h : (∑ e, w e * psi (z e)) =
      mass (step w z) - mass w - ∑ e, w e * z e := by
    simp only [psi, mul_sub, mul_one, Finset.sum_sub_distrib, mass, step]
  linarith

theorem mass_ratio_identity (w z : E → ℝ) (hw : ∀ e, 0 < w e)
    (hzero : (∑ e, w e * z e) = 0) :
    mass (step w z) / mass w = 1 + ∑ e, beta w e * psi (z e) := by
  rw [mass_identity w z hzero]
  have hd : mass w ≠ 0 := ne_of_gt (mass_pos w hw)
  simp only [beta, div_mul_eq_mul_div, ← Finset.sum_div]
  rw [add_div, div_self hd]

theorem remainder_mean_nonneg (w z : E → ℝ) (hw : ∀ e, 0 < w e) :
    0 ≤ ∑ e, beta w e * psi (z e) := by
  apply Finset.sum_nonneg
  intro e _
  exact mul_nonneg (beta_pos w hw e).le (psi_nonneg _)

/-- E5's exact logarithmic increment, including its nonnegativity. -/
theorem increment_identity_nonneg (w z : E → ℝ) (hw : ∀ e, 0 < w e)
    (hzero : (∑ e, w e * z e) = 0) :
    increment w z = Real.log (1 + ∑ e, beta w e * psi (z e)) ∧
      0 ≤ increment w z := by
  have hi : increment w z = Real.log (1 + ∑ e, beta w e * psi (z e)) := by
    unfold increment
    rw [mass_ratio_identity w z hw hzero]
  refine ⟨hi, ?_⟩
  rw [hi]
  exact Real.log_nonneg (by linarith [remainder_mean_nonneg w z hw])

/-- A useful exact-remainder bound; this is deliberately not the kappa bound E6. -/
theorem increment_le_remainder (w z : E → ℝ) (hw : ∀ e, 0 < w e)
    (hzero : (∑ e, w e * z e) = 0) :
    increment w z ≤ ∑ e, beta w e * psi (z e) := by
  rw [(increment_identity_nonneg w z hw hzero).1]
  have h := Real.log_le_sub_one_of_pos
    (show 0 < 1 + ∑ e, beta w e * psi (z e) by
      linarith [remainder_mean_nonneg w z hw])
  linarith

theorem trajectory_pos (n : ℕ) (w z : ℕ → E → ℝ)
    (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e) :
    ∀ t ≤ n, ∀ e, 0 < w t e := by
  intro t ht
  induction t with
  | zero => exact hinit
  | succ t ih =>
    intro e
    rw [hupdate t (by omega) e]
    exact step_pos (w t) (z t) (ih (by omega)) e

/-- Exact telescope for any positive trajectory, independently of centering. -/
theorem sum_increment (n : ℕ) (w z : ℕ → E → ℝ)
    (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e) :
    (∑ t ∈ range n, increment (w t) (z t)) =
      Real.log (mass (w n)) - Real.log (mass (w 0)) := by
  have hp := trajectory_pos n w z hinit hupdate
  have hs : ∀ t < n, increment (w t) (z t) =
      Real.log (mass (w (t + 1))) - Real.log (mass (w t)) := by
    intro t ht
    have hu : w (t + 1) = step (w t) (z t) := funext (hupdate t ht)
    unfold increment
    rw [← hu, Real.log_div (ne_of_gt (mass_pos _ (hp _ (by omega))))
      (ne_of_gt (mass_pos _ (hp _ (by omega))))]
  calc
    _ = ∑ t ∈ range n, (Real.log (mass (w (t + 1))) - Real.log (mass (w t))) :=
      Finset.sum_congr rfl (fun t ht => hs t (mem_range.mp ht))
    _ = _ := by
      clear hinit hupdate hp hs
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ, ih]; ring

/-- E5 accumulated from a normalized positive prior. -/
theorem normalized_log_mass (n : ℕ) (w z : ℕ → E → ℝ)
    (hinit : ∀ e, 0 < w 0 e) (hnorm : mass (w 0) = 1)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e) :
    Real.log (mass (w n)) = ∑ t ∈ range n, increment (w t) (z t) := by
  have h := sum_increment n w z hinit hupdate
  simpa [hnorm] using h.symm

theorem trajectory_increment_nonneg (n : ℕ) (w z : ℕ → E → ℝ)
    (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hzero : ∀ t < n, (∑ e, w t e * z t e) = 0) :
    ∀ t < n, 0 ≤ increment (w t) (z t) := by
  intro t ht
  exact (increment_identity_nonneg (w t) (z t)
    (trajectory_pos n w z hinit hupdate t (by omega)) (hzero t ht)).2

theorem normalized_log_mass_nonneg (n : ℕ) (w z : ℕ → E → ℝ)
    (hinit : ∀ e, 0 < w 0 e) (hnorm : mass (w 0) = 1)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hzero : ∀ t < n, (∑ e, w t e * z t e) = 0) :
    0 ≤ Real.log (mass (w n)) := by
  rw [normalized_log_mass n w z hinit hnorm hupdate]
  exact Finset.sum_nonneg (fun t ht =>
    trajectory_increment_nonneg n w z hinit hupdate hzero t (mem_range.mp ht))

theorem log_weight_identity (n : ℕ) (w z : ℕ → E → ℝ)
    (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < n, ∀ e, w (t + 1) e = step (w t) (z t) e) (e : E) :
    (∑ t ∈ range n, z t e) = Real.log (w n e) - Real.log (w 0 e) := by
  have hp := trajectory_pos n w z hinit hupdate
  have hs : ∀ t < n, z t e = Real.log (w (t + 1) e) - Real.log (w t e) := by
    intro t ht
    rw [hupdate t ht e]
    simp only [step, Real.log_mul (ne_of_gt (hp t (by omega) e))
      (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    ring
  calc
    _ = ∑ t ∈ range n, (Real.log (w (t + 1) e) - Real.log (w t e)) :=
      Finset.sum_congr rfl (fun t ht => hs t (mem_range.mp ht))
    _ = _ := by
      clear hinit hupdate hp hs
      induction n with
      | zero => simp
      | succ n ih => rw [sum_range_succ, ih]; ring

/-- E7 on an arbitrary local segment. `w 0` is the positive virtual weight at
the segment start; it need not have total mass one. The loss gap `r` can be
any quantity dominated by the selected expert's excess `x`. -/
theorem segment_regret (n : ℕ) (w z : ℕ → E → ℝ) (x r : ℕ → ℝ)
    (eta : ℝ) (heta : 0 < eta) (e : E)
    (hinit : ∀ i, 0 < w 0 i)
    (hupdate : ∀ t < n, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hz : ∀ t < n, z t e = eta * x t)
    (hr : ∀ t < n, r t ≤ x t) :
    (∑ t ∈ range n, r t) ≤
      (Real.log (1 / beta (w 0) e) + ∑ t ∈ range n, increment (w t) (z t)) / eta := by
  have hp := trajectory_pos n w z hinit hupdate
  have hw : w n e ≤ mass (w n) :=
    Finset.single_le_sum (fun i _ => (hp n le_rfl i).le) (Finset.mem_univ e)
  have hl : Real.log (w n e) ≤ Real.log (mass (w n)) :=
    Real.log_le_log (hp n le_rfl e) hw
  have heq := log_weight_identity n w z hinit hupdate e
  have hzsum : (∑ t ∈ range n, z t e) = eta * ∑ t ∈ range n, x t := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun t ht => hz t (mem_range.mp ht))
  rw [hzsum] at heq
  have hbeta : Real.log (1 / beta (w 0) e) =
      Real.log (mass (w 0)) - Real.log (w 0 e) := by
    rw [one_div, Real.log_inv, beta, Real.log_div (ne_of_gt (hinit e))
      (ne_of_gt (mass_pos _ hinit))]
    ring
  rw [hbeta, sum_increment n w z hinit hupdate]
  apply (le_div_iff₀ heta).mpr
  have hrs := Finset.sum_le_sum (fun t ht => hr t (mem_range.mp ht))
  have hmul := mul_le_mul_of_nonneg_left hrs heta.le
  nlinarith

/-- E8 in a local segment beginning at an expert's birth. Future/retired mass
remains in `w`; the explicit equality identifies the selected birth prior. -/
theorem birth_regret (n : ℕ) (w z : ℕ → E → ℝ) (x r : ℕ → ℝ)
    (eta pi : ℝ) (heta : 0 < eta) (e : E)
    (hinit : ∀ i, 0 < w 0 i) (hbirth : w 0 e = pi)
    (hupdate : ∀ t < n, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hz : ∀ t < n, z t e = eta * x t)
    (hr : ∀ t < n, r t ≤ x t) :
    (∑ t ∈ range n, r t) ≤
      (Real.log (1 / pi) + Real.log (mass (w n))) / eta := by
  have h := segment_regret n w z x r eta heta e hinit hupdate hz hr
  have hb : Real.log (1 / beta (w 0) e) =
      Real.log (mass (w 0)) - Real.log pi := by
    rw [one_div, Real.log_inv, beta, Real.log_div (ne_of_gt (hinit e))
      (ne_of_gt (mass_pos _ hinit)), hbirth]
    ring
  rw [hb, sum_increment n w z hinit hupdate] at h
  convert h using 1 <;> simp only [one_div, Real.log_inv] <;> ring

/-- E10's finite disjoint-block reduction. Each `hlocal` is supplied by E7
for an expert covering that block. This reduction neither constructs a
covering expert family nor claims the original dyadic sqrt bound. -/
theorem partition_regret {H : Finset ℕ} (P : Part2.Intervals.Partition H)
    (r : ℕ → ℝ) (cost : ℕ → ℝ) (W : ℝ)
    (hlocal : ∀ j ∈ P.labels, (∑ t ∈ P.block j, r t) ≤ cost j)
    (hspan : ∀ t ∈ H, r t ≤ 2 * W) :
    (∑ t ∈ H, r t) ≤ min (2 * W * (H.card : ℝ)) (∑ j ∈ P.labels, cost j) := by
  apply le_min
  · calc
      _ ≤ ∑ _t ∈ H, 2 * W := Finset.sum_le_sum hspan
      _ = _ := by simp; ring
  · rw [← P.sum_blocks r]
    exact Finset.sum_le_sum hlocal

/-- E9/E10's infimum step over any nonempty collection of admissible finite
covers. The cover collection and its local E7 costs are explicit data. -/
theorem partition_infimum_regret {H : Finset ℕ} {C : Type*} [Nonempty C]
    (P : C → Part2.Intervals.Partition H) (r : ℕ → ℝ)
    (cost : C → ℕ → ℝ) (W : ℝ)
    (hlocal : ∀ c, ∀ j ∈ (P c).labels,
      (∑ t ∈ (P c).block j, r t) ≤ cost c j)
    (hspan : ∀ t ∈ H, r t ≤ 2 * W) :
    (∑ t ∈ H, r t) ≤ min (2 * W * (H.card : ℝ))
      (sInf (Set.range (fun c => ∑ j ∈ (P c).labels, cost c j))) := by
  apply le_min
  · exact (le_min_iff.mp (partition_regret (P (Classical.arbitrary C)) r
      (cost (Classical.arbitrary C)) W (hlocal _) hspan)).1
  · apply le_csInf (Set.range_nonempty _)
    rintro y ⟨c, rfl⟩
    exact (le_min_iff.mp (partition_regret (P c) r (cost c) W (hlocal c) hspan)).2

end

end Part2.ExponentialExperts

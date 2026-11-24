import Part2.ExponentialRemainder
import Mathlib.Data.Real.Sqrt

/-!
# A safe horizon-dependent rate band for the same exponential-excess update

Every virtual expert uses a fixed rate in [1/(2 B sqrt N),1/(B sqrt N)].
Sleeping coordinates have exponent zero. The potential includes every
virtual expert, regardless of current activity. The proof uses E5/E6/E8,
not a normalized-Hedge update or mass conservation.
-/

namespace Part2.ExponentialSafeRate

noncomputable section

open Finset Part2.ExponentialExperts Part2.ExponentialRemainder

variable {E K : Type*} [Fintype E] [DecidableEq E] [Nonempty E] [Fintype K]

def sleepingExponent (active : Finset E) (eta x : E → ℝ) (e : E) : ℝ :=
  if e ∈ active then eta e * x e else 0

def rateLower (N : ℕ) (B : ℝ) : ℝ := 1 / (2 * B * Real.sqrt (N : ℝ))

def rateUpper (N : ℕ) (B : ℝ) : ℝ := 1 / (B * Real.sqrt (N : ℝ))

/-- The virtual process preserves a future expert's actual initial weight
through every round before its birth. No separate birth-weight assumption. -/
theorem weight_unchanged_before_birth (m : ℕ) (active : ℕ → Finset E)
    (eta : E → ℝ) (w x : ℕ → E → ℝ) (e : E)
    (hupdate : ∀ t < m, ∀ i,
      w (t + 1) i = step (w t) (sleepingExponent (active t) eta (x t)) i)
    (hunborn : ∀ t < m, e ∉ active t) : w m e = w 0 e := by
  have hi : ∀ t ≤ m, w t e = w 0 e := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [hupdate t (by omega) e]
      rw [sleeping_unchanged (w t) (sleepingExponent (active t) eta (x t)) e
        (by simp [sleepingExponent, hunborn t (by omega)])]
      exact ih (by omega)
  exact hi m le_rfl

theorem sqrt_horizon_pos (N : ℕ) (hN : 0 < N) : 0 < Real.sqrt (N : ℝ) :=
  Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)

theorem rate_pos (N : ℕ) (B : ℝ) (hN : 0 < N) (hB : 0 < B)
    (eta : E → ℝ) (hlower : ∀ e, rateLower N B ≤ eta e) :
    ∀ e, 0 < eta e := by
  intro e
  have hs := sqrt_horizon_pos N hN
  exact lt_of_lt_of_le (by unfold rateLower; positivity) (hlower e)

/-- One explicit admissible choice is eta_e=1/(B sqrt N) for every expert.
The remaining theorems also allow unequal fixed rates throughout the band. -/
theorem canonical_rate_admissible (N : ℕ) (B : ℝ) (hN : 0 < N) (hB : 0 < B) :
    rateLower N B ≤ rateUpper N B ∧ 0 < rateUpper N B := by
  have hs := sqrt_horizon_pos N hN
  constructor
  · unfold rateLower rateUpper
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * B * Real.sqrt (N : ℝ))
      (by positivity : 0 < B * Real.sqrt (N : ℝ))).mpr
    nlinarith [mul_pos hB hs]
  · unfold rateUpper
    positivity

theorem kappa_one_nonneg : 0 ≤ kappa 1 := by
  simpa [kappa] using psi_nonneg 1

/-- The rate band and real span bound give a common exponent radius 1/sqrt N,
including zero exponents on every sleeping coordinate. -/
theorem exponent_bound (N : ℕ) (B : ℝ) (hN : 0 < N) (hB : 0 < B)
    (active : Finset E) (eta x : E → ℝ)
    (hlower : ∀ e, rateLower N B ≤ eta e)
    (hupper : ∀ e, eta e ≤ rateUpper N B)
    (hspan : ∀ e ∈ active, |x e| ≤ B) (e : E) :
    |sleepingExponent active eta x e| ≤ 1 / Real.sqrt (N : ℝ) := by
  have hs := sqrt_horizon_pos N hN
  by_cases he : e ∈ active
  · simp only [sleepingExponent, if_pos he, abs_mul,
      abs_of_pos (rate_pos N B hN hB eta hlower e)]
    calc
      _ ≤ eta e * B := mul_le_mul_of_nonneg_left (hspan e he)
        (rate_pos N B hN hB eta hlower e).le
      _ ≤ rateUpper N B * B := mul_le_mul_of_nonneg_right (hupper e) hB.le
      _ = _ := by unfold rateUpper; field_simp [ne_of_gt hB, ne_of_gt hs]
  · simp only [sleepingExponent, if_neg he, abs_zero]
    positivity

theorem exponent_square_bound (N : ℕ) (B : ℝ) (hN : 0 < N) (hB : 0 < B)
    (active : Finset E) (eta x : E → ℝ)
    (hlower : ∀ e, rateLower N B ≤ eta e)
    (hupper : ∀ e, eta e ≤ rateUpper N B)
    (hspan : ∀ e ∈ active, |x e| ≤ B) (e : E) :
    (sleepingExponent active eta x e) ^ 2 ≤ 1 / (N : ℝ) := by
  have hs := sqrt_horizon_pos N hN
  have hb := abs_le.mp (exponent_bound N B hN hB active eta x hlower hupper hspan e)
  have hp := mul_nonneg (sub_nonneg.mpr hb.2)
    (show 0 ≤ 1 / Real.sqrt (N : ℝ) + sleepingExponent active eta x e by linarith [hb.1])
  have heq : (1 / Real.sqrt (N : ℝ)) ^ 2 = 1 / (N : ℝ) := by
    rw [div_pow, one_pow, Real.sq_sqrt (Nat.cast_nonneg N)]
  nlinarith

theorem quadraticCost_le (N : ℕ) (B : ℝ) (hN : 0 < N) (hB : 0 < B)
    (active : Finset E) (eta w x : E → ℝ) (hw : ∀ e, 0 < w e)
    (hlower : ∀ e, rateLower N B ≤ eta e)
    (hupper : ∀ e, eta e ≤ rateUpper N B)
    (hspan : ∀ e ∈ active, |x e| ≤ B) :
    quadraticCost w (sleepingExponent active eta x) 1 ≤ kappa 1 / (N : ℝ) := by
  have hm : (∑ e, beta w e * (sleepingExponent active eta x e) ^ 2) ≤ 1 / (N : ℝ) := by
    calc
      _ ≤ ∑ e, beta w e * (1 / (N : ℝ)) := by
        apply Finset.sum_le_sum
        intro e _
        exact mul_le_mul_of_nonneg_left
          (exponent_square_bound N B hN hB active eta x hlower hupper hspan e)
          (beta_pos w hw e).le
      _ = _ := by rw [← Finset.sum_mul, beta_sum w hw]; ring
  unfold quadraticCost
  have h := mul_le_mul_of_nonneg_left hm kappa_one_nonneg
  convert h using 1 <;> ring

/-- A bound on the full virtual mass after any H<=N updates, including
future, active, and retired experts. No mass normalization after time zero. -/
theorem log_mass_le (N H : ℕ) (B : ℝ) (hN : 0 < N) (hH : H ≤ N) (hB : 0 < B)
    (active : ℕ → Finset E) (eta : E → ℝ) (w x : ℕ → E → ℝ)
    (hlower : ∀ e, rateLower N B ≤ eta e)
    (hupper : ∀ e, eta e ≤ rateUpper N B)
    (hinit : ∀ e, 0 < w 0 e) (hnorm : mass (w 0) = 1)
    (hupdate : ∀ t < H, ∀ e,
      w (t + 1) e = step (w t) (sleepingExponent (active t) eta (x t)) e)
    (hzero : ∀ t < H,
      (∑ e, w t e * sleepingExponent (active t) eta (x t) e) = 0)
    (hspan : ∀ t < H, ∀ e ∈ active t, |x t e| ≤ B) :
    Real.log (mass (w H)) ≤ kappa 1 := by
  let z : ℕ → E → ℝ := fun t => sleepingExponent (active t) eta (x t)
  have hp := trajectory_pos H w z hinit hupdate
  have hs := sqrt_horizon_pos N hN
  have hNreal : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hsone : 1 ≤ Real.sqrt (N : ℝ) := by
    apply Real.one_le_sqrt.mpr
    exact_mod_cast (show 1 ≤ N by omega)
  have hbound : ∀ t < H, ∀ e, |z t e| ≤ 1 := by
    intro t ht e
    have hb := exponent_bound N B hN hB (active t) eta (x t) hlower hupper (hspan t ht) e
    exact hb.trans ((div_le_iff₀ hs).mpr (by simpa using hsone))
  have hpot := normalized_log_mass_le_quadraticCost H w z (fun _ => 1)
    hinit hnorm hupdate (by intro _ _; norm_num) hbound hzero
  calc
    _ ≤ ∑ t ∈ range H, quadraticCost (w t) (z t) 1 := hpot
    _ ≤ ∑ _t ∈ range H, kappa 1 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro t ht
      exact quadraticCost_le N B hN hB (active t) eta (w t) (x t)
        (hp t (by have hh := Finset.mem_range.mp ht; omega)) hlower hupper
        (hspan t (Finset.mem_range.mp ht))
    _ = (H : ℝ) * (kappa 1 / (N : ℝ)) := by simp
    _ ≤ kappa 1 := by
      have hHr : (H : ℝ) ≤ (N : ℝ) := Nat.cast_le.mpr hH
      have hm := mul_le_mul_of_nonneg_right hHr kappa_one_nonneg
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hNreal).mpr
      nlinarith

/-- A newborn expert's actual segment regret has an explicit sqrt(N) cost.
All earlier virtual potential is charged: the segment is not restarted. -/
theorem birth_segment_regret (N m n : ℕ) (B : ℝ) (hN : 0 < N)
    (hwithin : m + n ≤ N) (hB : 0 < B)
    (active : ℕ → Finset E) (eta : E → ℝ) (w x : ℕ → E → ℝ)
    (r : ℕ → ℝ) (e : E)
    (hlower : ∀ i, rateLower N B ≤ eta i)
    (hupper : ∀ i, eta i ≤ rateUpper N B)
    (hinit : ∀ i, 0 < w 0 i) (hnorm : mass (w 0) = 1)
    (hbirth : w m e = w 0 e)
    (hupdate : ∀ t < m + n, ∀ i,
      w (t + 1) i = step (w t) (sleepingExponent (active t) eta (x t)) i)
    (hzero : ∀ t < m + n,
      (∑ i, w t i * sleepingExponent (active t) eta (x t) i) = 0)
    (hspan : ∀ t < m + n, ∀ i ∈ active t, |x t i| ≤ B)
    (hcover : ∀ t < n, e ∈ active (m + t))
    (hgap : ∀ t < n, r t ≤ x (m + t) e) :
    (∑ t ∈ range n, r t) ≤
      2 * B * Real.sqrt (N : ℝ) * (Real.log (1 / w 0 e) + kappa 1) := by
  let z : ℕ → E → ℝ := fun t => sleepingExponent (active t) eta (x t)
  have heta := rate_pos N B hN hB eta hlower e
  have hp := trajectory_pos (m + n) w z hinit hupdate
  have hu : ∀ t < n, ∀ i,
      w (m + (t + 1)) i = step (w (m + t)) (z (m + t)) i := by
    intro t ht i
    simpa [Nat.add_assoc] using hupdate (m + t) (by omega) i
  have hreg := Part2.ExponentialExperts.birth_regret n
    (fun t => w (m + t)) (fun t => z (m + t))
    (fun t => x (m + t) e) r (eta e) (w 0 e) heta e
    (by simpa using hp m (by omega)) (by simpa using hbirth) hu
    (by intro t ht; exact if_pos (hcover t ht)) hgap
  have hpot := log_mass_le N (m + n) B hN hwithin hB active eta w x
    hlower hupper hinit hnorm hupdate hzero hspan
  have hpi : w 0 e ≤ 1 := by
    simpa [beta, hnorm] using beta_le_one (w 0) hinit e
  have hlog : 0 ≤ Real.log (1 / w 0 e) :=
    Real.log_nonneg ((one_le_div (hinit e)).mpr hpi)
  have hnum : 0 ≤ Real.log (1 / w 0 e) + kappa 1 := add_nonneg hlog kappa_one_nonneg
  have hs := sqrt_horizon_pos N hN
  have hd : 0 < 2 * B * Real.sqrt (N : ℝ) := by positivity
  have hlow : 1 ≤ eta e * (2 * B * Real.sqrt (N : ℝ)) :=
    (div_le_iff₀ hd).mp (hlower e)
  calc
    _ ≤ (Real.log (1 / w 0 e) + Real.log (mass (w (m + n)))) / eta e := hreg
    _ ≤ (Real.log (1 / w 0 e) + kappa 1) / eta e := by
      exact div_le_div_of_nonneg_right (add_le_add_left hpot _) heta.le
    _ ≤ _ := by
      apply (div_le_iff₀ heta).mpr
      have hmul := mul_le_mul_of_nonneg_left hlow hnum
      convert hmul using 1 <;> ring

/-- For the actual learning-rate-weighted advice mixture, the moment
condition in `birth_segment_regret` follows from the existing E4 identity. -/
theorem sleeping_advice_zero (active : Finset E) (eta w : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ)
    (hden : (∑ e ∈ active, Part2.Prod.coefficient eta w e) ≠ 0) :
    (∑ e, w e * sleepingExponent active eta
      (Part2.Prod.excess active eta w advice loss) e) = 0 := by
  have hz : sleepingExponent active eta (Part2.Prod.excess active eta w advice loss) =
      (fun e => eta e * Part2.Prod.excess active eta w advice loss e) := by
    funext e
    by_cases he : e ∈ active
    · simp [sleepingExponent, he]
    · simp [sleepingExponent, Part2.Prod.excess, he]
  rw [hz]
  exact advice_zero_first_order active eta w advice loss hden

/-- The safe birth-segment bound for the actual learning-rate-weighted
mixture. In this theorem centering is proved, not supplied as a premise.
Advice losses and their excesses are exactly the existing E1/E4 definitions. -/
theorem advice_birth_segment_regret (N m n : ℕ) (B : ℝ) (hN : 0 < N)
    (hwithin : m + n ≤ N) (hB : 0 < B)
    (active : ℕ → Finset E) (eta : E → ℝ) (w : ℕ → E → ℝ)
    (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ)
    (r : ℕ → ℝ) (e : E)
    (hlower : ∀ i, rateLower N B ≤ eta i)
    (hupper : ∀ i, eta i ≤ rateUpper N B)
    (hinit : ∀ i, 0 < w 0 i) (hnorm : mass (w 0) = 1)
    (hunborn : ∀ t < m, e ∉ active t)
    (hactive : ∀ t < m + n, (active t).Nonempty)
    (hupdate : ∀ t < m + n, ∀ i,
      w (t + 1) i = step (w t) (sleepingExponent (active t) eta
        (Part2.Prod.excess (active t) eta (w t) (advice t) (loss t))) i)
    (hspan : ∀ t < m + n, ∀ i ∈ active t,
      |Part2.Prod.excess (active t) eta (w t) (advice t) (loss t) i| ≤ B)
    (hcover : ∀ t < n, e ∈ active (m + t))
    (hgap : ∀ t < n, r t ≤
      Part2.Prod.excess (active (m + t)) eta (w (m + t)) (advice (m + t)) (loss (m + t)) e) :
    (∑ t ∈ range n, r t) ≤
      2 * B * Real.sqrt (N : ℝ) * (Real.log (1 / w 0 e) + kappa 1) := by
  let x : ℕ → E → ℝ := fun t =>
    Part2.Prod.excess (active t) eta (w t) (advice t) (loss t)
  let z : ℕ → E → ℝ := fun t => sleepingExponent (active t) eta (x t)
  have hbirth : w m e = w 0 e := weight_unchanged_before_birth m active eta w x e
    (fun t ht => hupdate t (by omega)) hunborn
  have hp := trajectory_pos (m + n) w z hinit hupdate
  have hzero : ∀ t < m + n,
      (∑ i, w t i * sleepingExponent (active t) eta (x t) i) = 0 := by
    intro t ht
    have hd : (∑ i ∈ active t, Part2.Prod.coefficient eta (w t) i) ≠ 0 := by
      apply ne_of_gt
      exact Part2.Prod.denominator_pos (active t) eta (w t)
        (fun i _ => rate_pos N B hN hB eta hlower i)
        (fun i _ => hp t (by omega) i) (hactive t ht)
    exact sleeping_advice_zero (active t) eta (w t) (advice t) (loss t) hd
  exact birth_segment_regret N m n B hN hwithin hB active eta w x r e
    hlower hupper hinit hnorm hbirth hupdate hzero hspan hcover hgap

/-- A fully explicit safe configuration: uniform positive prior and the
fixed horizon-dependent rate 1/(B sqrt N), with the original exponential
excess update and its original learning-rate-weighted advice mixture.
The chosen full-horizon expert supplies a static sqrt(N) comparator bound. -/
theorem canonical_static_advice_regret (N : ℕ) (B : ℝ) (hN : 0 < N) (hB : 0 < B)
    (active : ℕ → Finset E) (w : ℕ → E → ℝ)
    (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ)
    (r : ℕ → ℝ) (e : E)
    (hinitial : ∀ i, w 0 i = 1 / (Fintype.card E : ℝ))
    (hactive : ∀ t < N, (active t).Nonempty)
    (hupdate : ∀ t < N, ∀ i,
      w (t + 1) i = step (w t) (sleepingExponent (active t) (fun _ => rateUpper N B)
        (Part2.Prod.excess (active t) (fun _ => rateUpper N B) (w t) (advice t) (loss t))) i)
    (hspan : ∀ t < N, ∀ i ∈ active t,
      |Part2.Prod.excess (active t) (fun _ => rateUpper N B) (w t) (advice t) (loss t) i| ≤ B)
    (hcover : ∀ t < N, e ∈ active t)
    (hgap : ∀ t < N, r t ≤
      Part2.Prod.excess (active t) (fun _ => rateUpper N B) (w t) (advice t) (loss t) e) :
    (∑ t ∈ range N, r t) ≤
      2 * B * Real.sqrt (N : ℝ) * (Real.log (Fintype.card E : ℝ) + kappa 1) := by
  have hc : 0 < (Fintype.card E : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hinit : ∀ i, 0 < w 0 i := by
    intro i
    rw [hinitial i]
    positivity
  have hnorm : mass (w 0) = 1 := by
    unfold mass
    simp_rw [hinitial]
    simp [nsmul_eq_mul, ne_of_gt hc]
  have h := advice_birth_segment_regret N 0 N B hN (by omega) hB active
    (fun _ => rateUpper N B) w advice loss r e
    (fun _ => (canonical_rate_admissible N B hN hB).1) (fun _ => le_rfl)
    hinit hnorm (by intro t ht; omega) (by simpa using hactive) (by simpa using hupdate)
    (by simpa using hspan) (by simpa using hcover) (by simpa using hgap)
  simpa [hinitial e] using h

end

end Part2.ExponentialSafeRate

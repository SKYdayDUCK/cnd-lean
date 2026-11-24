import Part2.ExponentialSafeRate
import Part2.ExponentialCovers

/-! # Cover cost for the horizon-dependent exponential update

Each piece uses an expert that is still at its original prior on the
first round of that piece. The cost charges the global mass at its end.
-/

namespace Part2.ExponentialSafeCover

noncomputable section

open Finset ExponentialCovers ExponentialExperts ExponentialRemainder ExponentialSafeRate

variable {E A : Type*} [Fintype E] [DecidableEq E] [Nonempty E]
  {N : ℕ} {active : ℕ → Finset E} {arm : E → A} {k : A} {H : Finset ℕ}

/-- A logarithmic-size covering bound can use this estimate once per piece.
Sleeping experts have zero exponent and remain at their prior until birth. -/
theorem cover_cost_le (C : Cover N active arm k H) (B : ℝ)
    (hN : 0 < N) (hB : 0 < B) (eta : E → ℝ) (w x : ℕ → E → ℝ)
    (hlower : ∀ i, rateLower N B ≤ eta i)
    (hupper : ∀ i, eta i ≤ rateUpper N B)
    (hinitial : ∀ i, w 0 i = 1 / (Fintype.card E : ℝ))
    (hupdate : ∀ t < N, ∀ i,
      w (t + 1) i = step (w t) (sleepingExponent (active t) eta (x t)) i)
    (hzero : ∀ t < N, (∑ i, w t i * sleepingExponent (active t) eta (x t) i) = 0)
    (hspan : ∀ t < N, ∀ i ∈ active t, |x t i| ≤ B)
    (hunborn : ∀ j ∈ C.partition.labels, ∀ t < C.start j, C.expert j ∉ active t) :
    C.totalCost w (fun t => sleepingExponent (active t) eta (x t)) eta ≤
      (C.partition.labels.card : ℝ) *
        (2 * B * Real.sqrt (N : ℝ) * (Real.log (Fintype.card E : ℝ) + kappa 1)) := by
  let z : ℕ → E → ℝ := fun t => sleepingExponent (active t) eta (x t)
  have hc : 0 < (Fintype.card E : ℝ) := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
  have hinit (i : E) : 0 < w 0 i := by
    rw [hinitial]
    positivity
  have hnorm : mass (w 0) = 1 := by
    unfold mass
    simp_rw [hinitial]
    simp [nsmul_eq_mul, ne_of_gt hc]
  have hp := trajectory_pos N w z hinit hupdate
  have hnum : 0 ≤ Real.log (Fintype.card E : ℝ) + kappa 1 := by
    have hc1 : 1 ≤ (Fintype.card E : ℝ) := by
      exact_mod_cast (Fintype.card_pos : 0 < Fintype.card E)
    exact add_nonneg (Real.log_nonneg hc1) kappa_one_nonneg
  change (∑ j ∈ C.partition.labels, C.localCost w z eta j) ≤ _
  calc
    _ ≤ ∑ _j ∈ C.partition.labels,
        2 * B * Real.sqrt (N : ℝ) * (Real.log (Fintype.card E : ℝ) + kappa 1) := by
      apply sum_le_sum
      intro j hj
      let u := C.start j
      let n := C.length j
      let e := C.expert j
      have hwithin : u + n ≤ N := C.within j hj
      have hbirth : w u e = w 0 e :=
        weight_unchanged_before_birth u active eta w x e
          (fun t ht => hupdate t (by omega)) (hunborn j hj)
      have hshift (t : ℕ) (ht : t < n) (i : E) :
          w (u + (t + 1)) i = step (w (u + t)) (z (u + t)) i := by
        simpa only [Nat.add_assoc] using hupdate (u + t) (by omega) i
      have hinc : (∑ t ∈ Ico u (u + n), increment (w t) (z t)) =
          Real.log (mass (w (u + n))) - Real.log (mass (w u)) := by
        rw [sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
        simpa only [Nat.add_zero] using
          sum_increment n (fun t => w (u + t)) (fun t => z (u + t))
            (fun i => hp u (by omega) i) hshift
      have hlogbeta : Real.log (1 / beta (w u) e) =
          Real.log (mass (w u)) + Real.log (Fintype.card E : ℝ) := by
        rw [one_div, Real.log_inv, beta,
          Real.log_div (ne_of_gt (hp u (by omega) e)) (ne_of_gt (mass_pos _ (hp u (by omega)))),
          hbirth, hinitial e, one_div, Real.log_inv]
        ring
      have hmass := log_mass_le N (u + n) B hN hwithin hB active eta w x
        hlower hupper hinit hnorm (fun t ht => hupdate t (by omega))
        (fun t ht => hzero t (by omega)) (fun t ht => hspan t (by omega))
      have heta := rate_pos N B hN hB eta hlower e
      have hd : 0 < 2 * B * Real.sqrt (N : ℝ) :=
        mul_pos (by positivity) (sqrt_horizon_pos N hN)
      have hlow : 1 ≤ eta e * (2 * B * Real.sqrt (N : ℝ)) :=
        (div_le_iff₀ hd).mp (hlower e)
      unfold Cover.localCost
      rw [C.block_eq j hj]
      change (Real.log (1 / beta (w u) e) +
        ∑ t ∈ Ico u (u + n), increment (w t) (z t)) / eta e ≤ _
      rw [hlogbeta, hinc]
      calc
        _ ≤ (Real.log (Fintype.card E : ℝ) + kappa 1) / eta e :=
          div_le_div_of_nonneg_right (by linarith) heta.le
        _ ≤ _ := by
          apply (div_le_iff₀ heta).mpr
          have hm := mul_le_mul_of_nonneg_right hlow hnum
          convert hm using 1 <;> ring
    _ = _ := by simp

end

end Part2.ExponentialSafeCover

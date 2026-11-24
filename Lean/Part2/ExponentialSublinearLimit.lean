import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas

/-! Asymptotic consequences of the finite-horizon ECND regret estimates.
Realized regret against an arbitrary path can be signed, so the conclusion
concerns its positive part. The bounds may hold on different events at
different horizons; the lemmas are deterministic and make no claim about a
common probability event. -/

noncomputable section
open Filter Asymptotics
open scoped Topology

namespace Part2.ExponentialSublinearLimit

private theorem positive_average_squeeze {regret upper : ℕ → ℝ}
    (bound : ∀ᶠ n in atTop, regret n ≤ upper n)
    (upperLimit : Tendsto (fun n => upper n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (regret n) / (n : ℝ)) atTop (𝓝 0) := by
  have hzero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0) := tendsto_const_nhds
  have hmax : Tendsto (fun n => max 0 (upper n / (n : ℝ))) atTop (𝓝 0) := by
    simpa using hzero.max upperLimit
  apply squeeze_zero' (Eventually.of_forall fun n => by positivity) _ hmax
  filter_upwards [bound] with n hn
  rw [← max_div_div_right (Nat.cast_nonneg n), zero_div]
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hn (Nat.cast_nonneg n))

/-- For the rate-controlled interval cover, divide the finite bound by the
horizon. The contribution of the cover is its weighted count divided by
`sqrt n`, while the concentration term has a factor `sqrt segments / sqrt n`.
The private learning term and the coverage correction are each charged once. -/
theorem positive_average_of_component_limits
    (regret noise payment gap : ℕ → ℝ) (pieces experts segments : ℕ → ℕ) (C κ : ℝ)
    (bound : ∀ᶠ n in atTop, regret n ≤
      C * Real.sqrt (n : ℝ) * (pieces n : ℝ) * (Real.log (experts n : ℝ) + κ) +
        noise n * Real.sqrt ((n : ℝ) * (segments n : ℝ)) + payment n + gap n)
    (coverLimit : Tendsto (fun n =>
      (pieces n : ℝ) * (Real.log (experts n : ℝ) + κ) / Real.sqrt (n : ℝ)) atTop (𝓝 0))
    (noiseLimit : Tendsto (fun n =>
      noise n * (Real.sqrt (segments n : ℝ) / Real.sqrt (n : ℝ))) atTop (𝓝 0))
    (paymentLimit : Tendsto (fun n => payment n / (n : ℝ)) atTop (𝓝 0))
    (gapLimit : Tendsto (fun n => gap n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (regret n) / (n : ℝ)) atTop (𝓝 0) := by
  refine positive_average_squeeze bound ?_
  have h := (((tendsto_const_nhds (x := C)).mul coverLimit).add noiseLimit).add
    paymentLimit |>.add gapLimit
  apply (show Tendsto (fun n =>
    C * ((pieces n : ℝ) * (Real.log (experts n : ℝ) + κ) / Real.sqrt (n : ℝ)) +
    noise n * (Real.sqrt (segments n : ℝ) / Real.sqrt (n : ℝ)) +
      payment n / (n : ℝ) + gap n / (n : ℝ)) atTop (𝓝 0) from by simpa using h).congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs := Real.sqrt_pos.2 hn'
  have hsquare := Real.sq_sqrt hn'.le
  rw [add_div, add_div, add_div, Real.sqrt_mul hn'.le]
  have hcancel : (Real.sqrt (n : ℝ)) / (n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
    field_simp [hn'.ne', hs.ne']
    nlinarith
  simp only [div_eq_mul_inv] at hcancel ⊢
  linear_combination
    (-C * (pieces n : ℝ) * (Real.log (experts n : ℝ) + κ) -
      noise n * Real.sqrt (segments n : ℝ)) * hcancel

/-- Any fixed power of `log n` is dominated by a positive power of `n`. -/
theorem normalized_polynomial_log (a p : ℝ) (ha : a < 1) :
    Tendsto (fun n : ℕ => (n : ℝ) ^ a * Real.log (n : ℝ) ^ p / (n : ℝ)) atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop p (sub_pos.mpr ha)).tendsto_div_nhds_zero.comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.2 hn
  change Real.log (n : ℝ) ^ p / (n : ℝ) ^ (1-a) = _
  rw [Real.rpow_sub hn', Real.rpow_one, div_div_eq_mul_div, mul_comm (Real.log (n : ℝ) ^ p)]

/-- A concrete sufficient regime. The expert-cover block has order
`n^(1/2+a) (log n)^p`; this includes the dyadic cover with polynomially many
experts and `O(n^a)` constant-comparator runs, by taking `p = 2`. The combined
sampling and private learning term may have any power `b < 1`, up to a fixed
power of `log n`. The coverage correction can vanish identically under the
canonical confidence construction. -/
theorem positive_average_of_polynomial_log_bound
    (regret gap : ℕ → ℝ) (A B a b p q : ℝ)
    (ha : a < 1 / 2) (hb : b < 1)
    (bound : ∀ᶠ n in atTop, regret n ≤
      A * ((n : ℝ) ^ (1 / 2 + a) * Real.log (n : ℝ) ^ p) +
      B * ((n : ℝ) ^ b * Real.log (n : ℝ) ^ q) + gap n)
    (gapLimit : Tendsto (fun n => gap n / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n => max 0 (regret n) / (n : ℝ)) atTop (𝓝 0) := by
  refine positive_average_squeeze bound ?_
  have hExpert := (tendsto_const_nhds (x := A)).mul
    (normalized_polynomial_log (1 / 2 + a) p (by linarith))
  have hOther := (tendsto_const_nhds (x := B)).mul (normalized_polynomial_log b q hb)
  simpa only [Pi.mul_apply, Pi.add_apply, mul_zero, add_zero, add_div, mul_div_assoc] using
    ((hExpert.add hOther).add gapLimit)

end Part2.ExponentialSublinearLimit

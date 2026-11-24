import Part2.ExponentialExperts

/-!
# E14: the actual two-arm alternating exponential-excess process

There are two always-awake experts with the same fixed positive rate, one
for each arm. The decision is the learning-rate-weighted distribution from
the paper. The recursive weights use excess-loss exponentials, including
the common played-loss term; they are not replaced by Hedge weights.
-/

namespace Part2.ExponentialAlternating

noncomputable section

open Finset

def firstLoss : Bool → ℝ
  | false => 1
  | true => 0

def secondLoss : Bool → ℝ
  | false => 0
  | true => 1

def loss (t : ℕ) : Bool → ℝ := if t % 2 = 0 then firstLoss else secondLoss

/-- The actual q in E1, specialized to equal rates and two experts. -/
def q (gamma : ℝ) (w : Bool → ℝ) (e : Bool) : ℝ :=
  gamma * w e / (gamma * w false + gamma * w true)

def played (gamma : ℝ) (w l : Bool → ℝ) : ℝ :=
  q gamma w false * l false + q gamma w true * l true

def update (gamma : ℝ) (w l : Bool → ℝ) (e : Bool) : ℝ :=
  w e * Real.exp (gamma * (played gamma w l - l e))

/-- A single actual E1 trajectory, initialized with the normalized prior. -/
def weight (gamma : ℝ) : ℕ → Bool → ℝ
  | 0 => fun _ => 1 / 2
  | t + 1 => update gamma (weight gamma t) (loss t)

def regret (gamma : ℝ) (t : ℕ) (e : Bool) : ℝ :=
  played gamma (weight gamma t) (loss t) - loss t e

def pairGap (gamma : ℝ) : ℝ := Real.exp gamma / (1 + Real.exp gamma) - 1 / 2

def identityAdvice (e k : Bool) : ℝ := if e = k then 1 else 0

/-- The displayed two-arm q is definitionally the original E1 mixture
after expanding the finite two-element sums and identity expert advice. -/
theorem q_eq_original_mixture (gamma : ℝ) (w : Bool → ℝ) (e : Bool) :
    q gamma w e = Part2.Prod.mixture Finset.univ (fun _ => gamma) w identityAdvice e := by
  cases e <;> simp [q, Part2.Prod.mixture, Part2.Prod.coefficient,
    identityAdvice, Fintype.sum_bool, add_comm]

theorem played_eq_original_mixtureLoss (gamma : ℝ) (w l : Bool → ℝ) :
    played gamma w l = Part2.Prod.mixtureLoss Finset.univ (fun _ => gamma) w identityAdvice l := by
  unfold Part2.Prod.mixtureLoss
  rw [Fintype.sum_bool]
  rw [← q_eq_original_mixture, ← q_eq_original_mixture]
  unfold played
  ring

theorem excess_eq_original_excess (gamma : ℝ) (w l : Bool → ℝ) (e : Bool) :
    Part2.Prod.excess Finset.univ (fun _ => gamma) w identityAdvice l e =
      played gamma w l - l e := by
  unfold Part2.Prod.excess
  rw [if_pos (Finset.mem_univ e), ← played_eq_original_mixtureLoss]
  cases e <;> simp [Part2.Prod.adviceLoss, identityAdvice, Fintype.sum_bool]

theorem loss_even (m : ℕ) : loss (2 * m) = firstLoss := by
  simp [loss, Nat.mul_mod]

theorem loss_odd (m : ℕ) : loss (2 * m + 1) = secondLoss := by
  simp [loss, Nat.add_mod, Nat.mul_mod]

theorem weight_pos (gamma : ℝ) (t : ℕ) (e : Bool) : 0 < weight gamma t e := by
  induction t with
  | zero => norm_num [weight]
  | succ t ih => exact mul_pos ih (Real.exp_pos _)

theorem initial_normalized (gamma : ℝ) :
    Part2.ExponentialExperts.mass (weight gamma 0) = 1 := by
  norm_num [Part2.ExponentialExperts.mass, weight, Fintype.sum_bool]

theorem q_eq_weight_fraction (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (e : Bool) :
    q gamma w e = w e / (w false + w true) := by
  have hd : w false + w true ≠ 0 := ne_of_gt (add_pos (hw false) (hw true))
  have hd' : gamma * w false + gamma * w true ≠ 0 :=
    ne_of_gt (add_pos (mul_pos hgamma (hw false)) (mul_pos hgamma (hw true)))
  unfold q
  field_simp [ne_of_gt hgamma, hd, hd']
  <;> ring

theorem q_pos (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (e : Bool) :
    0 < q gamma w e := by
  rw [q_eq_weight_fraction gamma w hgamma hw e]
  exact div_pos (hw e) (add_pos (hw false) (hw true))

theorem q_sum (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) :
    q gamma w false + q gamma w true = 1 := by
  rw [q_eq_weight_fraction gamma w hgamma hw false,
    q_eq_weight_fraction gamma w hgamma hw true, ← add_div]
  exact div_self (ne_of_gt (add_pos (hw false) (hw true)))

theorem update_is_excess_step (gamma : ℝ) (w l : Bool → ℝ) :
    update gamma w l = Part2.ExponentialExperts.step w
      (fun e => gamma * (played gamma w l - l e)) := rfl

theorem update_is_original_advice_step (gamma : ℝ) (w l : Bool → ℝ) :
    update gamma w l = Part2.ExponentialExperts.step w
      (fun e => gamma * Part2.Prod.excess Finset.univ (fun _ => gamma) w identityAdvice l e) := by
  funext e
  simp only [Part2.ExponentialExperts.step, update, excess_eq_original_excess]

theorem played_first_equal (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (heq : w false = w true) :
    played gamma w firstLoss = 1 / 2 := by
  simp only [played, firstLoss, mul_one, mul_zero, add_zero]
  rw [q_eq_weight_fraction gamma w hgamma hw false, ← heq]
  field_simp [ne_of_gt (hw false), ne_of_gt (add_pos (hw false) (hw false))]
  <;> ring

theorem first_update_false (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (heq : w false = w true) :
    update gamma w firstLoss false = w false * Real.exp (-gamma / 2) := by
  unfold update
  rw [played_first_equal gamma w hgamma hw heq]
  simp only [firstLoss]
  congr 1
  congr 1
  ring

theorem first_update_true (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (heq : w false = w true) :
    update gamma w firstLoss true = w false * Real.exp (gamma / 2) := by
  unfold update
  rw [played_first_equal gamma w hgamma hw heq, ← heq]
  simp only [firstLoss]
  congr 1
  congr 1
  ring

theorem played_second_after_first (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (heq : w false = w true) :
    played gamma (update gamma w firstLoss) secondLoss =
      Real.exp gamma / (1 + Real.exp gamma) := by
  have hw' : ∀ e, 0 < update gamma w firstLoss e :=
    fun e => mul_pos (hw e) (Real.exp_pos _)
  simp only [played, secondLoss, mul_zero, mul_one, zero_add]
  rw [q_eq_weight_fraction gamma _ hgamma hw' true,
    first_update_false gamma w hgamma hw heq,
    first_update_true gamma w hgamma hw heq]
  have hex : Real.exp (gamma / 2) = Real.exp (-gamma / 2) * Real.exp gamma := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hex]
  have ha : w false ≠ 0 := ne_of_gt (hw false)
  have hwfalse : 0 < w false := hw false
  have hb : Real.exp (-gamma / 2) ≠ 0 := ne_of_gt (Real.exp_pos _)
  have hc : 1 + Real.exp gamma ≠ 0 := by positivity
  have hd : w false * Real.exp (-gamma / 2) +
      w false * (Real.exp (-gamma / 2) * Real.exp gamma) ≠ 0 := by positivity
  field_simp [ha, hb, hc, hd]
  <;> ring

theorem two_updates_equal (gamma : ℝ) (w : Bool → ℝ)
    (hgamma : 0 < gamma) (hw : ∀ e, 0 < w e) (heq : w false = w true) :
    update gamma (update gamma w firstLoss) secondLoss false =
      update gamma (update gamma w firstLoss) secondLoss true := by
  change update gamma w firstLoss false *
      Real.exp (gamma * (played gamma (update gamma w firstLoss) secondLoss - 0)) =
    update gamma w firstLoss true *
      Real.exp (gamma * (played gamma (update gamma w firstLoss) secondLoss - 1))
  rw [first_update_false gamma w hgamma hw heq,
    first_update_true gamma w hgamma hw heq]
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add]
  congr 1
  congr 1
  ring

theorem weight_even_equal (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) :
    weight gamma (2 * m) false = weight gamma (2 * m) true := by
  induction m with
  | zero => rfl
  | succ m ih =>
    have hi : 2 * (m + 1) = (2 * m + 1) + 1 := by omega
    rw [hi]
    simp only [weight, loss_odd, loss_even]
    exact two_updates_equal gamma (weight gamma (2 * m)) hgamma
      (weight_pos gamma (2 * m)) ih

theorem played_even (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) :
    played gamma (weight gamma (2 * m)) (loss (2 * m)) = 1 / 2 := by
  rw [loss_even]
  exact played_first_equal gamma _ hgamma (weight_pos gamma _)
    (weight_even_equal gamma hgamma m)

theorem played_odd (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) :
    played gamma (weight gamma (2 * m + 1)) (loss (2 * m + 1)) =
      Real.exp gamma / (1 + Real.exp gamma) := by
  simp only [weight, loss_odd, loss_even]
  exact played_second_after_first gamma _ hgamma (weight_pos gamma _)
    (weight_even_equal gamma hgamma m)

theorem q_even (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) (e : Bool) :
    q gamma (weight gamma (2 * m)) e = 1 / 2 := by
  have hf : q gamma (weight gamma (2 * m)) false = 1 / 2 := by
    simpa [played, loss_even, firstLoss] using played_even gamma hgamma m
  have hs := q_sum gamma (weight gamma (2 * m)) hgamma (weight_pos gamma _)
  cases e
  · exact hf
  · linarith

theorem q_odd_true (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) :
    q gamma (weight gamma (2 * m + 1)) true =
      Real.exp gamma / (1 + Real.exp gamma) := by
  simpa [played, loss_odd, secondLoss] using played_odd gamma hgamma m

theorem q_odd_false (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) :
    q gamma (weight gamma (2 * m + 1)) false = 1 / (1 + Real.exp gamma) := by
  have hs := q_sum gamma (weight gamma (2 * m + 1)) hgamma (weight_pos gamma _)
  rw [q_odd_true gamma hgamma m] at hs
  have hd : 1 + Real.exp gamma ≠ 0 := by positivity
  field_simp [hd] at hs ⊢
  nlinarith

theorem weight_odd_ratio (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) :
    weight gamma (2 * m + 1) false / weight gamma (2 * m + 1) true =
      Real.exp (-gamma) := by
  simp only [weight, loss_even]
  rw [first_update_false gamma _ hgamma (weight_pos gamma _)
      (weight_even_equal gamma hgamma m),
    first_update_true gamma _ hgamma (weight_pos gamma _)
      (weight_even_equal gamma hgamma m)]
  calc
    _ = Real.exp (-gamma / 2) / Real.exp (gamma / 2) := by
      field_simp [ne_of_gt (weight_pos gamma (2 * m) false),
        ne_of_gt (Real.exp_pos (gamma / 2))]
      <;> ring
    _ = Real.exp ((-gamma / 2) - gamma / 2) := (Real.exp_sub _ _).symm
    _ = _ := by congr 1; ring

theorem pair_regret (gamma : ℝ) (hgamma : 0 < gamma) (m : ℕ) (e : Bool) :
    regret gamma (2 * m) e + regret gamma (2 * m + 1) e = pairGap gamma := by
  unfold regret
  rw [played_even gamma hgamma m, played_odd gamma hgamma m, loss_even, loss_odd]
  cases e <;> simp only [firstLoss, secondLoss, pairGap] <;> ring

theorem total_regret (gamma : ℝ) (hgamma : 0 < gamma) (n : ℕ) (e : Bool) :
    (∑ t ∈ range (2 * n), regret gamma t e) = (n : ℝ) * pairGap gamma := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hi : 2 * (n + 1) = (2 * n + 1) + 1 := by omega
    rw [hi, sum_range_succ, sum_range_succ, ih]
    have hp := pair_regret gamma hgamma n e
    push_cast
    nlinarith

/-- E14 in an exp-only form equivalent to the displayed tanh formula. -/
theorem total_regret_e14 (gamma : ℝ) (hgamma : 0 < gamma) (n : ℕ) (e : Bool) :
    (∑ t ∈ range (2 * n), regret gamma t e) =
      ((2 * n : ℕ) : ℝ) / 4 * ((Real.exp gamma - 1) / (Real.exp gamma + 1)) := by
  rw [total_regret gamma hgamma n e]
  unfold pairGap
  push_cast
  have hd : 1 + Real.exp gamma ≠ 0 := by positivity
  have hd' : Real.exp gamma + 1 ≠ 0 := by positivity
  field_simp [hd, hd']
  <;> ring

theorem pairGap_pos (gamma : ℝ) (hgamma : 0 < gamma) : 0 < pairGap gamma := by
  have he : 1 < Real.exp gamma := Real.one_lt_exp_iff.mpr hgamma
  unfold pairGap
  apply sub_pos.mpr
  apply (lt_div_iff₀ (show 0 < 1 + Real.exp gamma by positivity)).mpr
  nlinarith

/-- A strictly positive coefficient independent of the horizon: linear,
even when the fixed learning rate also satisfies an external small cap. -/
theorem positive_linear_regret (gamma : ℝ) (hgamma : 0 < gamma) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, ∀ e : Bool,
      (∑ t ∈ range (2 * n), regret gamma t e) = ((2 * n : ℕ) : ℝ) * c := by
  refine ⟨pairGap gamma / 2, div_pos (pairGap_pos gamma hgamma) (by norm_num), ?_⟩
  intro n e
  rw [total_regret gamma hgamma n e]
  push_cast
  ring

end

end Part2.ExponentialAlternating

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic

/-!
# Sleeping Prod with distribution-valued advice

The coefficients are exactly learning-rate times weight. The mixture is formed
before observing the loss vector; no measurability or probability assertion is
made here. Sleeping experts have zero excess and therefore keep their weight.
-/

namespace Part2.Prod

noncomputable section

open Finset

variable {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K]

def coefficient (eta weight : E → ℝ) (e : E) : ℝ := eta e * weight e

def adviceLoss (advice : E → K → ℝ) (loss : K → ℝ) (e : E) : ℝ :=
  ∑ k, advice e k * loss k

def mixture (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (k : K) : ℝ :=
  (∑ e ∈ active, coefficient eta weight e * advice e k) /
    ∑ e ∈ active, coefficient eta weight e

def mixtureLoss (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ) : ℝ :=
  ∑ k, mixture active eta weight advice k * loss k

def excess (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ) (e : E) : ℝ :=
  if e ∈ active then
    mixtureLoss active eta weight advice loss - adviceLoss advice loss e else 0

def step (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ) (e : E) : ℝ :=
  weight e * (1 + eta e * excess active eta weight advice loss e)

theorem denominator_pos (active : Finset E) (eta weight : E → ℝ)
    (hEta : ∀ e ∈ active, 0 < eta e)
    (hWeight : ∀ e ∈ active, 0 < weight e) (hActive : active.Nonempty) :
    0 < ∑ e ∈ active, coefficient eta weight e := by
  apply Finset.sum_pos
  · intro e he
    exact mul_pos (hEta e he) (hWeight e he)
  · exact hActive

theorem mixture_loss_identity (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ)
    (hDen : (∑ e ∈ active, coefficient eta weight e) ≠ 0) :
    (∑ e ∈ active, coefficient eta weight e) *
        mixtureLoss active eta weight advice loss =
      ∑ e ∈ active, coefficient eta weight e * adviceLoss advice loss e := by
  unfold mixtureLoss mixture adviceLoss
  rw [Finset.mul_sum]
  have hterm (k : K) :
      (∑ e ∈ active, coefficient eta weight e) *
        ((∑ e ∈ active, coefficient eta weight e * advice e k) /
          (∑ e ∈ active, coefficient eta weight e) * loss k) =
      ∑ e ∈ active, coefficient eta weight e * advice e k * loss k := by
    rw [← Finset.sum_mul]
    field_simp
  simp_rw [hterm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem weighted_excess_zero (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ)
    (hDen : (∑ e ∈ active, coefficient eta weight e) ≠ 0) :
    (∑ e, coefficient eta weight e * excess active eta weight advice loss e) = 0 := by
  have hMix := mixture_loss_identity active eta weight advice loss hDen
  simp only [excess, mul_ite, mul_zero, Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
  exact sub_eq_zero.mpr hMix

theorem mass_conserved (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ)
    (hDen : (∑ e ∈ active, coefficient eta weight e) ≠ 0) :
    (∑ e, step active eta weight advice loss e) = ∑ e, weight e := by
  have hZero := weighted_excess_zero active eta weight advice loss hDen
  unfold step
  simp_rw [mul_add, mul_one]
  rw [Finset.sum_add_distrib]
  have h : (∑ e, weight e * (eta e * excess active eta weight advice loss e)) = 0 := by
    convert hZero using 1
    apply Finset.sum_congr rfl
    intro e he
    unfold coefficient
    ring
  rw [h, add_zero]

theorem sleeping_unchanged (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ) (e : E) (he : e ∉ active) :
    step active eta weight advice loss e = weight e := by
  simp [step, excess, he]

theorem step_pos (active : Finset E) (eta weight : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ) (e : E)
    (hWeight : 0 < weight e)
    (hBound : |eta e * excess active eta weight advice loss e| ≤ 1 / 2) :
    0 < step active eta weight advice loss e := by
  unfold step
  apply mul_pos hWeight
  have h := (abs_le.mp hBound).1
  linarith

def logGap (x : ℝ) : ℝ := Real.log (1 + x) - x + x ^ 2

theorem logGap_deriv (x : ℝ) (hx : -(1 / 2 : ℝ) ≤ x) :
    HasDerivAt logGap (x * (1 + 2 * x) / (1 + x)) x := by
  have hx' : 1 + x ≠ 0 := by linarith
  have h := (((hasDerivAt_id x).const_add 1).log hx').sub
    (hasDerivAt_id x)
  have h' := h.add ((hasDerivAt_id x).pow 2)
  convert h' using 1 <;> dsimp [logGap]
  field_simp [hx']
  <;> ring

/-- The exact scalar inequality used by the paper, including the endpoint -1/2. -/
theorem log_one_add_lower (x : ℝ) (hx : -(1 / 2 : ℝ) ≤ x) :
    x - x ^ 2 ≤ Real.log (1 + x) := by
  have hcont : ContinuousOn logGap (Set.Ici (-(1 / 2 : ℝ))) := by
    intro y hy
    exact (logGap_deriv y hy).continuousAt.continuousWithinAt
  have hgap : 0 ≤ logGap x := by
    by_cases hx0 : 0 ≤ x
    · have hm : MonotoneOn logGap (Set.Ici (0 : ℝ)) := by
        apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici 0)
          (hcont.mono (by intro y hy; simp only [Set.mem_Ici] at *; linarith))
        · intro y hy
          have hy0 : 0 ≤ y := interior_subset hy
          exact (logGap_deriv y (by linarith)).hasDerivWithinAt
        · intro y hy
          have hy0 : 0 ≤ y := interior_subset hy
          exact div_nonneg (mul_nonneg hy0 (by linarith)) (by linarith)
      have hh := hm (by simp) hx0 hx0
      simpa [logGap] using hh
    · have hx0' : x ≤ 0 := le_of_not_ge hx0
      have hm : AntitoneOn logGap (Set.Icc (-(1 / 2 : ℝ)) 0) := by
        apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc _ _)
          (hcont.mono (by intro y hy; exact hy.1))
        · intro y hy
          have hy' : y ∈ Set.Icc (-(1 / 2 : ℝ)) 0 := interior_subset hy
          exact (logGap_deriv y hy'.1).hasDerivWithinAt
        · intro y hy
          have hy' : y ∈ Set.Icc (-(1 / 2 : ℝ)) 0 := interior_subset hy
          exact div_nonpos_of_nonpos_of_nonneg
            (mul_nonpos_of_nonpos_of_nonneg hy'.2 (by linarith [hy'.1]))
            (by linarith [hy'.1])
      have hh := hm ⟨hx, hx0'⟩ (by norm_num) hx0'
      simpa [logGap] using hh
  unfold logGap at hgap
  linarith

/-- Log potential for one specialist; zero excess represents its sleeping rounds. -/
theorem single_expert_potential (n : ℕ) (eta : ℝ) (r weight : ℕ → ℝ)
    (hWeight : 0 < weight 0)
    (hUpdate : ∀ t < n, weight (t + 1) = weight t * (1 + eta * r t))
    (hSmall : ∀ t < n, |eta * r t| ≤ 1 / 2) :
    eta * (∑ t ∈ range n, r t) - eta ^ 2 * (∑ t ∈ range n, (r t) ^ 2) ≤
      Real.log (weight n) - Real.log (weight 0) := by
  have hw : ∀ t ≤ n, 0 < weight t := by
    intro t ht
    induction t with
    | zero => exact hWeight
    | succ t ih =>
      rw [hUpdate t (by omega)]
      apply mul_pos (ih (by omega))
      have hh := (abs_le.mp (hSmall t (by omega))).1
      linarith
  have hlog : ∀ t < n,
      eta * r t - eta ^ 2 * (r t) ^ 2 ≤
        Real.log (weight (t + 1)) - Real.log (weight t) := by
    intro t ht
    have hs := log_one_add_lower (eta * r t) (abs_le.mp (hSmall t ht)).1
    have hp : 0 < 1 + eta * r t := by
      have hh := (abs_le.mp (hSmall t ht)).1
      linarith
    rw [hUpdate t ht, Real.log_mul (ne_of_gt (hw t (by omega))) (ne_of_gt hp)]
    nlinarith
  have hsum := Finset.sum_le_sum (s := range n) (fun t ht => hlog t (mem_range.mp ht))
  have htel : (∑ t ∈ range n,
      (Real.log (weight (t + 1)) - Real.log (weight t))) =
        Real.log (weight n) - Real.log (weight 0) := by
    clear hUpdate hSmall hw hlog hsum
    induction n with
    | zero => simp
    | succ n ih => rw [sum_range_succ, ih]; ring
  rw [htel] at hsum
  simpa only [Finset.sum_sub_distrib, ← Finset.mul_sum] using hsum

/-- The second-order deterministic regret bound, before replacing squared excess. -/
theorem single_expert_regret (n : ℕ) (eta N : ℝ) (r weight : ℕ → ℝ)
    (hEta : 0 < eta) (hN : 0 < N) (hInit : weight 0 = 1 / N)
    (hUpdate : ∀ t < n, weight (t + 1) = weight t * (1 + eta * r t))
    (hSmall : ∀ t < n, |eta * r t| ≤ 1 / 2) (hFinal : weight n ≤ 1) :
    (∑ t ∈ range n, r t) ≤ Real.log N / eta +
      eta * (∑ t ∈ range n, (r t) ^ 2) := by
  have hInitPos : 0 < weight 0 := by rw [hInit]; positivity
  have hp := single_expert_potential n eta r weight hInitPos hUpdate hSmall
  have hnpos : 0 < weight n := by
    have hw : ∀ t ≤ n, 0 < weight t := by
      intro t ht
      induction t with
      | zero => exact hInitPos
      | succ t ih =>
        rw [hUpdate t (by omega)]
        apply mul_pos (ih (by omega))
        have hh := (abs_le.mp (hSmall t (by omega))).1
        linarith
    exact hw n le_rfl
  have hln : Real.log (weight n) ≤ 0 := Real.log_nonpos hnpos.le hFinal
  have hli : Real.log (weight 0) = -Real.log N := by simp [hInit, Real.log_div]
  rw [hli] at hp
  have hid : (Real.log N / eta + eta * (∑ t ∈ range n, (r t) ^ 2)) * eta =
      Real.log N + eta ^ 2 * (∑ t ∈ range n, (r t) ^ 2) := by
    field_simp
    <;> ring
  apply (mul_le_mul_right hEta).mp
  rw [hid]
  nlinarith

/-- Positivity and normalized total mass are consequences of the actual updates. -/
theorem trajectory_invariant (n : ℕ) (active : ℕ → Finset E) (eta : E → ℝ)
    (weight : ℕ → E → ℝ) (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ)
    (hEta : ∀ e, 0 < eta e) (hActive : ∀ t < n, (active t).Nonempty)
    (hInitPos : ∀ e, 0 < weight 0 e) (hInitMass : (∑ e, weight 0 e) = 1)
    (hUpdate : ∀ t < n, ∀ e,
      weight (t + 1) e = step (active t) eta (weight t) (advice t) (loss t) e)
    (hSmall : ∀ t < n, ∀ e,
      |eta e * excess (active t) eta (weight t) (advice t) (loss t) e| ≤ 1 / 2) :
    (∀ e, 0 < weight n e) ∧ (∑ e, weight n e) = 1 := by
  have hInv : ∀ m ≤ n, (∀ e, 0 < weight m e) ∧ (∑ e, weight m e) = 1 := by
    intro m hm
    induction m with
    | zero => exact ⟨hInitPos, hInitMass⟩
    | succ m ih =>
      have hi := ih (by omega)
      have hd : (∑ e ∈ active m, coefficient eta (weight m) e) ≠ 0 := by
        apply ne_of_gt
        exact denominator_pos (active m) eta (weight m)
          (fun e _ => hEta e) (fun e _ => hi.1 e) (hActive m (by omega))
      constructor
      · intro e
        rw [hUpdate m (by omega) e]
        exact step_pos (active m) eta (weight m) (advice m) (loss m) e
          (hi.1 e) (hSmall m (by omega) e)
      · simp_rw [hUpdate m (by omega)]
        rw [mass_conserved (active m) eta (weight m) (advice m) (loss m) hd]
        exact hi.2
  exact hInv n le_rfl

/-- Specialist regret from normalized sleeping Prod, without assuming a final weight bound. -/
theorem sleeping_prod_regret (n : ℕ) (active : ℕ → Finset E) (eta : E → ℝ)
    (weight : ℕ → E → ℝ) (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ)
    (hEta : ∀ e, 0 < eta e) (hActive : ∀ t < n, (active t).Nonempty)
    (hInitPos : ∀ e, 0 < weight 0 e) (hInitMass : (∑ e, weight 0 e) = 1)
    (hUpdate : ∀ t < n, ∀ e,
      weight (t + 1) e = step (active t) eta (weight t) (advice t) (loss t) e)
    (hSmall : ∀ t < n, ∀ e,
      |eta e * excess (active t) eta (weight t) (advice t) (loss t) e| ≤ 1 / 2)
    (e : E) :
    (∑ t ∈ range n, excess (active t) eta (weight t) (advice t) (loss t) e) ≤
      Real.log (1 / weight 0 e) / eta e + eta e *
      (∑ t ∈ range n, (excess (active t) eta (weight t) (advice t) (loss t) e) ^ 2) := by
  have hi := trajectory_invariant n active eta weight advice loss hEta hActive
    hInitPos hInitMass hUpdate hSmall
  have hInitial : 0 < weight 0 e := hInitPos e
  have hFinal : weight n e ≤ 1 := by
    rw [← hi.2]
    exact Finset.single_le_sum (fun i _ => (hi.1 i).le) (Finset.mem_univ e)
  apply single_expert_regret n (eta e) (1 / weight 0 e)
    (fun t => excess (active t) eta (weight t) (advice t) (loss t) e)
    (fun t => weight t e) (hEta e) (by positivity)
  · simp
  · intro t ht
    exact hUpdate t ht e
  · intro t ht
    exact hSmall t ht e
  · exact hFinal

/-- The paper's block bound; only active rounds contribute to the quadratic term. -/
theorem sleeping_prod_span_regret (n : ℕ) (active : ℕ → Finset E) (eta : E → ℝ)
    (weight : ℕ → E → ℝ) (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ)
    (W : ℝ) (hW : 0 ≤ W)
    (hEta : ∀ e, 0 < eta e) (hCap : ∀ e, eta e * (2 * W) ≤ 1 / 2)
    (hActive : ∀ t < n, (active t).Nonempty)
    (hInitPos : ∀ e, 0 < weight 0 e) (hInitMass : (∑ e, weight 0 e) = 1)
    (hUpdate : ∀ t < n, ∀ e,
      weight (t + 1) e = step (active t) eta (weight t) (advice t) (loss t) e)
    (hSpan : ∀ t < n, ∀ e ∈ active t,
      |mixtureLoss (active t) eta (weight t) (advice t) (loss t) -
        adviceLoss (advice t) (loss t) e| ≤ 2 * W)
    (e : E) :
    (∑ t ∈ range n, excess (active t) eta (weight t) (advice t) (loss t) e) ≤
      Real.log (1 / weight 0 e) / eta e + 4 * eta e * W ^ 2 *
        (((range n).filter (fun t => e ∈ active t)).card : ℝ) := by
  have hr : ∀ t < n, ∀ i,
      |excess (active t) eta (weight t) (advice t) (loss t) i| ≤ 2 * W := by
    intro t ht i
    by_cases hi : i ∈ active t
    · simpa [excess, hi] using hSpan t ht i hi
    · simp [excess, hi, hW]
  have hs : ∀ t < n, ∀ i,
      |eta i * excess (active t) eta (weight t) (advice t) (loss t) i| ≤ 1 / 2 := by
    intro t ht i
    rw [abs_mul, abs_of_pos (hEta i)]
    exact (mul_le_mul_of_nonneg_left (hr t ht i) (hEta i).le).trans (hCap i)
  have hbase := sleeping_prod_regret n active eta weight advice loss hEta hActive
    hInitPos hInitMass hUpdate hs e
  have hq : (∑ t ∈ range n,
      (excess (active t) eta (weight t) (advice t) (loss t) e) ^ 2) ≤
      4 * W ^ 2 * (((range n).filter (fun t => e ∈ active t)).card : ℝ) := by
    calc
      _ ≤ ∑ t ∈ range n, if e ∈ active t then 4 * W ^ 2 else 0 := by
        apply Finset.sum_le_sum
        intro t ht
        by_cases he : e ∈ active t
        · rw [if_pos he]
          have hh := abs_le.mp (hr t (mem_range.mp ht) e)
          have hp := mul_nonneg (sub_nonneg.mpr hh.2)
            (show 0 ≤ 2 * W + excess (active t) eta (weight t) (advice t) (loss t) e by
              linarith [hh.1])
          nlinarith
        · simp [excess, he]
      _ = _ := by rw [← Finset.sum_filter]; simp; ring
  have hq' := mul_le_mul_of_nonneg_left hq (hEta e).le
  nlinarith

end

end Part2.Prod

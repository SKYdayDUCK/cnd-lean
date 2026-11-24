import staging.cnd20261024.prod.Transport

namespace Part2.CNDProd
open Finset
noncomputable section
variable {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K]

/-- The actual numerical sleeping-Prod recursion, including frozen sleeping weights. -/
def evolution (active : ℕ → Finset E) (eta init : E → ℝ)
    (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ) : ℕ → E → ℝ
  | 0 => init
  | t + 1 => Part2.Prod.step (active t) eta (evolution active eta init advice loss t)
      (advice t) (loss t)

/-- A state-machine implementation with these exact updates is the same
trajectory, rather than a second independently quantified run. -/
theorem evolution_unique (active : ℕ → Finset E) (eta init : E → ℝ)
    (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ) (w : ℕ → E → ℝ)
    (hzero : w 0 = init)
    (hstep : ∀ t, w (t + 1) = Part2.Prod.step (active t) eta (w t) (advice t) (loss t)) :
    w = evolution active eta init advice loss := by
  funext t
  induction t with
  | zero => exact hzero
  | succ t ih => rw [hstep, ih]; rfl

/-- Pairwise transported row ranges imply the actual weighted mixture range. -/
theorem mixture_span (active : Finset E) (eta w : E → ℝ)
    (advice : E → K → ℝ) (loss : K → ℝ) (D : ℝ)
    (he : active.Nonempty) (heta : ∀ i, 0 < eta i) (hw : ∀ i, 0 < w i)
    (hpair : ∀ i ∈ active, ∀ j ∈ active,
      |Part2.Prod.adviceLoss advice loss i - Part2.Prod.adviceLoss advice loss j| ≤ D)
    (e : E) (he' : e ∈ active) :
    |Part2.Prod.mixtureLoss active eta w advice loss - Part2.Prod.adviceLoss advice loss e| ≤ D := by
  let den := ∑ i ∈ active, Part2.Prod.coefficient eta w i
  have hd : 0 < den := Part2.Prod.denominator_pos active eta w
    (fun i _ => heta i) (fun i _ => hw i) he
  have hid := Part2.Prod.mixture_loss_identity active eta w advice loss (ne_of_gt hd)
  have hc : ∀ i, 0 ≤ Part2.Prod.coefficient eta w i := fun i => (mul_pos (heta i) (hw i)).le
  have hcenter : den * (Part2.Prod.mixtureLoss active eta w advice loss - Part2.Prod.adviceLoss advice loss e) =
      ∑ i ∈ active, Part2.Prod.coefficient eta w i *
        (Part2.Prod.adviceLoss advice loss i - Part2.Prod.adviceLoss advice loss e) := by
    dsimp [den]
    rw [mul_sub, hid]
    simp_rw [mul_sub, sum_sub_distrib, ← sum_mul]
  have hup : den * (Part2.Prod.mixtureLoss active eta w advice loss - Part2.Prod.adviceLoss advice loss e) ≤ den * D := by
    calc
      _ = ∑ i ∈ active, Part2.Prod.coefficient eta w i *
          (Part2.Prod.adviceLoss advice loss i - Part2.Prod.adviceLoss advice loss e) := by
        exact hcenter
      _ ≤ ∑ i ∈ active, Part2.Prod.coefficient eta w i * D := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hpair i hi e he')).2 (hc i)
      _ = den * D := (sum_mul ..).symm
  have hlo : den * (-D) ≤ den * (Part2.Prod.mixtureLoss active eta w advice loss - Part2.Prod.adviceLoss advice loss e) := by
    calc
      _ = ∑ i ∈ active, Part2.Prod.coefficient eta w i * (-D) := sum_mul ..
      _ ≤ ∑ i ∈ active, Part2.Prod.coefficient eta w i *
          (Part2.Prod.adviceLoss advice loss i - Part2.Prod.adviceLoss advice loss e) := by
        apply sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_left (abs_le.mp (hpair i hi e he')).1 (hc i)
      _ = _ := hcenter.symm
  exact abs_le.mpr ⟨(mul_le_mul_left hd).mp hlo, (mul_le_mul_left hd).mp hup⟩

/-- Positivity, normalization and the per-round span are consequences of the
actual recursion and primitive pairwise row ranges. No regret input is used. -/
theorem evolution_invariant (T : ℕ) (active : ℕ → Finset E) (eta init : E → ℝ)
    (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (heta : ∀ e, 0 < eta e) (hcap : ∀ e, eta e * (2 * W) ≤ 1 / 2)
    (hactive : ∀ t < T, (active t).Nonempty)
    (hinit : ∀ e, 0 < init e) (hmass : ∑ e, init e = 1)
    (hpair : ∀ t < T, ∀ i ∈ active t, ∀ j ∈ active t,
      |Part2.Prod.adviceLoss (advice t) (loss t) i - Part2.Prod.adviceLoss (advice t) (loss t) j| ≤ 2 * W) :
    ∀ t ≤ T, (∀ e, 0 < evolution active eta init advice loss t e) ∧
      (∑ e, evolution active eta init advice loss t e) = 1 := by
  intro t ht
  induction t with
  | zero => exact ⟨hinit, hmass⟩
  | succ t ih =>
    have hi := ih (by omega)
    have hspan := mixture_span (active t) eta (evolution active eta init advice loss t)
      (advice t) (loss t) (2 * W) (hactive t (by omega)) heta hi.1 (hpair t (by omega))
    have hs : ∀ e, |eta e * Part2.Prod.excess (active t) eta
        (evolution active eta init advice loss t) (advice t) (loss t) e| ≤ 1 / 2 := by
      intro e
      rw [abs_mul, abs_of_pos (heta e)]
      by_cases he : e ∈ active t
      · exact (mul_le_mul_of_nonneg_left (by simpa [Part2.Prod.excess, he] using hspan e he) (heta e).le).trans (hcap e)
      · simp [Part2.Prod.excess, he]
    constructor
    · intro e
      exact Part2.Prod.step_pos _ _ _ _ _ e (hi.1 e) (hs e)
    · change (∑ e, Part2.Prod.step _ _ _ _ _ e) = 1
      rw [Part2.Prod.mass_conserved]
      · exact hi.2
      · exact ne_of_gt (Part2.Prod.denominator_pos _ _ _ (fun e _ => heta e)
          (fun e _ => hi.1 e) (hactive t (by omega)))

/-- The cumulative specialist guarantee for the explicitly defined recursion. -/
theorem evolution_regret (T : ℕ) (active : ℕ → Finset E) (eta init : E → ℝ)
    (advice : ℕ → E → K → ℝ) (loss : ℕ → K → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (heta : ∀ e, 0 < eta e) (hcap : ∀ e, eta e * (2 * W) ≤ 1 / 2)
    (hactive : ∀ t < T, (active t).Nonempty)
    (hinit : ∀ e, 0 < init e) (hmass : ∑ e, init e = 1)
    (hpair : ∀ t < T, ∀ i ∈ active t, ∀ j ∈ active t,
      |Part2.Prod.adviceLoss (advice t) (loss t) i - Part2.Prod.adviceLoss (advice t) (loss t) j| ≤ 2 * W)
    (e : E) :
    (∑ t ∈ range T, Part2.Prod.excess (active t) eta
      (evolution active eta init advice loss t) (advice t) (loss t) e) ≤
      Real.log (1 / init e) / eta e + 4 * eta e * W ^ 2 *
        (((range T).filter (fun t => e ∈ active t)).card : ℝ) := by
  have hi := evolution_invariant T active eta init advice loss W hW heta hcap hactive hinit hmass hpair
  apply Part2.Prod.sleeping_prod_span_regret T active eta (evolution active eta init advice loss)
    advice loss W hW heta hcap hactive hinit hmass (fun _ _ _ => rfl)
  intro t ht e he
  exact mixture_span _ _ _ _ _ _ (hactive t ht) heta (hi t (by omega)).1 (hpair t ht) e he

end
end Part2.CNDProd

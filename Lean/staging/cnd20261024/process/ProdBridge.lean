import staging.cnd20261024.process.CNDProcess
import Part2.Prod

/-! Exact algebra identifying the process's actual sleeping-Prod update with
the existing Prod recursion. No update/span/regret premise is assumed. -/

noncomputable section
open Finset
open scoped BigOperators

namespace Part2.CNDProcess

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

def activeSet (d : ExpertData ι E) (n : ℕ) : Finset E := univ.filter (fun e ↦ d.active n e)
def processAdvice (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (s : State ι E) (e : E) : Vec ι :=
  transport o d n s (d.arm e)
def processLoss (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (s : State ι E) (b : Vec ι) (i : ι) : ℝ :=
  proxy o d n s i + b i
def pureAdvice (d : ExpertData ι E) (e : E) (i : ι) : ℝ := if d.arm e = i then 1 else 0

theorem denominator_eq_prod (d : ExpertData ι E) (n : ℕ) (s : State ι E) :
    denominator d n s = ∑ e ∈ activeSet d n, Prod.coefficient d.eta s.2 e := by
  simp [denominator, activeSet, Prod.coefficient, Finset.sum_filter]

theorem alpha_weighted_sum (d : ExpertData ι E) (n : ℕ) (s : State ι E) (f : E → ℝ) :
    (∑ e, alpha d n s e * f e) =
      (∑ e ∈ activeSet d n, Prod.coefficient d.eta s.2 e * f e) / denominator d n s := by
  simp only [alpha, activeSet, Prod.coefficient, Finset.sum_filter]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  split_ifs <;> simp [div_mul_eq_mul_div]

theorem suggestion_eq_pure_mixture (d : ExpertData ι E) (hW : d.W ≠ 0)
    (n : ℕ) (s : State ι E) :
    suggestion d n s = Prod.mixture (activeSet d n) d.eta s.2 (pureAdvice d) := by
  funext i
  calc
    suggestion d n s i = ∑ e, alpha d n s e * pureAdvice d e i := by
      unfold suggestion pureAdvice
      rw [if_neg hW]
      apply Finset.sum_congr rfl
      intro e _
      split_ifs <;> simp
    _ = _ := by rw [alpha_weighted_sum, denominator_eq_prod]; rfl

theorem expertLoss_eq_adviceLoss (o : DecisionMaps ι) (d : ExpertData ι E)
    (n : ℕ) (s : State ι E) (b : Vec ι) (e : E) :
    expertLoss o d n s b e = Prod.adviceLoss (processAdvice o d n s) (processLoss o d n s b) e := rfl

theorem mixtureLoss_eq_ratio (active : Finset E) (eta weight : E → ℝ)
    (advice : E → ι → ℝ) (loss : ι → ℝ) :
    Prod.mixtureLoss active eta weight advice loss =
      (∑ e ∈ active, Prod.coefficient eta weight e * Prod.adviceLoss advice loss e) /
        (∑ e ∈ active, Prod.coefficient eta weight e) := by
  unfold Prod.mixtureLoss Prod.mixture Prod.adviceLoss
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem meanExpertLoss_eq_mixtureLoss (o : DecisionMaps ι) (d : ExpertData ι E)
    (n : ℕ) (s : State ι E) (b : Vec ι) :
    meanExpertLoss o d n s b =
      Prod.mixtureLoss (activeSet d n) d.eta s.2 (processAdvice o d n s) (processLoss o d n s b) := by
  unfold meanExpertLoss
  simp_rw [expertLoss_eq_adviceLoss]
  rw [alpha_weighted_sum, mixtureLoss_eq_ratio, denominator_eq_prod]

theorem step_weights_eq_prod (o : DecisionMaps ι) (d : ExpertData ι E) (hW : d.W ≠ 0)
    (n : ℕ) (s : State ι E) (A : ι) (Y : ℝ) (b : Vec ι) :
    (step o d n s A Y b).2 =
      Prod.step (activeSet d n) d.eta s.2 (processAdvice o d n s) (processLoss o d n s b) := by
  funext e
  unfold step Prod.step Prod.excess
  simp only [hW, ↓reduceIte]
  rw [meanExpertLoss_eq_mixtureLoss, expertLoss_eq_adviceLoss]
  by_cases ha : d.active n e = true
  · simp [activeSet, ha]
  · simp [activeSet, ha]

end Part2.CNDProcess

end

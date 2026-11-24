import staging.cnd20261024.probability.ModelBridge
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum

/-!
# Actual causal CND state recursion: a compositional measurable interface

The four finite-dimensional decision maps are the confidence selection,
radius, canonical matrix prox and prescribed transport. Their Borel interfaces
are explicit cross-module inputs. The distribution is computed from the
actual previous state, never supplied as a free predictable process.

No confidence event, confidence probability, tail or payment bound is a field.
The original-space raw M1 laws are kept separate from the deterministic maps.
-/

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory

namespace Part2.CNDProcess

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [Fintype E] [DecidableEq E]

abbrev Vec (ι : Type*) := ι → ℝ
abbrev Mat (ι : Type*) := ι → ι → ℝ
abbrev Stats (ι : Type*) := Mat ι × Vec ι
abbrev State (ι E : Type*) := Stats ι × (E → ℝ)
abbrev ProxInput (ι : Type*) := Vec ι × (Mat ι × Vec ι)
abbrev TransportInput (ι : Type*) := Vec ι × (Vec ι × Vec ι)

/-- Exact selected functions are supplied by the choice/geometry modules.
`prox_simplex` is a deterministic codomain property, not a confidence claim.
This interface by itself does not identify an arbitrary map with the paper's
canonical map; that identification is a separate integration obligation. -/
structure DecisionMaps (ι : Type*) [Fintype ι] where
  confidence : Stats ι → Vec ι
  radius : Stats ι → Mat ι
  prox : ProxInput ι → Vec ι
  transport : TransportInput ι → Mat ι
  confidence_measurable : Measurable confidence
  radius_measurable : Measurable radius
  prox_measurable : Measurable prox
  transport_measurable : Measurable transport
  prox_simplex : ∀ x, prox x ∈ CND.simplex

structure ExpertData (ι E : Type*) where
  active : ℕ → E → Bool
  arm : E → ι
  eta : E → ℝ
  W : ℝ
  R : ℝ

def initialState : State ι E :=
  ((fun i j ↦ (if i = j then 1 else 0) - (Fintype.card ι : ℝ)⁻¹, fun _ ↦ 0),
    fun _ ↦ (Fintype.card E : ℝ)⁻¹)

def denominator (d : ExpertData ι E) (n : ℕ) (s : State ι E) : ℝ :=
  ∑ e, if d.active n e then d.eta e * s.2 e else 0

def alpha (d : ExpertData ι E) (n : ℕ) (s : State ι E) (e : E) : ℝ :=
  if d.active n e then d.eta e * s.2 e / denominator d n s else 0

def suggestion (d : ExpertData ι E) (n : ℕ) (s : State ι E) (i : ι) : ℝ :=
  if d.W = 0 then (Fintype.card ι : ℝ)⁻¹
  else ∑ e, if d.arm e = i then alpha d n s e else 0

def confidence (o : DecisionMaps ι) (d : ExpertData ι E) (s : State ι E) : Vec ι :=
  if d.R = 0 then fun _ ↦ 0 else o.confidence s.1

def radius (o : DecisionMaps ι) (d : ExpertData ι E) (s : State ι E) : Mat ι :=
  if d.R = 0 then fun _ _ ↦ 0 else o.radius s.1

def probability (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (s : State ι E) : Vec ι :=
  o.prox (confidence o d s, (radius o d s, suggestion d n s))

def gradient (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (s : State ι E) (i : ι) : ℝ :=
  confidence o d s i - ∑ j, radius o d s i j * probability o d n s j

def transport (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (s : State ι E) : Mat ι :=
  o.transport (suggestion d n s, (probability o d n s, gradient o d n s))

def proxy (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (s : State ι E) (i : ι) : ℝ :=
  gradient o d n s i - ∑ j, probability o d n s j * confidence o d s j

def expertLoss (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ)
    (s : State ι E) (b : Vec ι) (e : E) : ℝ :=
  ∑ j, transport o d n s (d.arm e) j * (proxy o d n s j + b j)

def meanExpertLoss (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ)
    (s : State ι E) (b : Vec ι) : ℝ :=
  ∑ e, alpha d n s e * expertLoss o d n s b e

/-- One original update, using exactly one selected residual and one potential
public vector. R=0 skips statistics; W=0 skips sleeping-Prod. -/
def step (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ)
    (s : State ι E) (A : ι) (Y : ℝ) (b : Vec ι) : State ι E :=
  ((fun i j ↦ if d.R = 0 then s.1.1 i j else
      s.1.1 i j + CNDPhysical.covariance (probability o d n s) i j,
    fun i ↦ if d.R = 0 then s.1.2 i else
      s.1.2 i + ((if A = i then 1 else 0) - probability o d n s i) * Y),
    fun e ↦ if d.W = 0 then s.2 e else if d.active n e then
      s.2 e * (1 + d.eta e * (meanExpertLoss o d n s b - expertLoss o d n s b e))
      else s.2 e)

section MeasurableMaps
variable {Ω : Type*} [m : MeasurableSpace Ω] {s : Ω → State ι E}
  (hs : Measurable s) (o : DecisionMaps ι) (d : ExpertData ι E)

include hs

theorem denominator_measurable (n : ℕ) : Measurable (fun ω ↦ denominator d n (s ω)) := by
  apply Finset.measurable_fun_sum
  intro e _
  by_cases h : d.active n e = true
  · simpa [denominator, h] using ((measurable_pi_apply e).comp (measurable_snd.comp hs)).const_mul (d.eta e)
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem alpha_measurable (n : ℕ) (e : E) : Measurable (fun ω ↦ alpha d n (s ω) e) := by
  unfold alpha
  split_ifs
  · exact (((measurable_pi_apply e).comp (measurable_snd.comp hs)).const_mul _).div
      (denominator_measurable hs d n)
  · exact measurable_const

theorem suggestion_measurable (n : ℕ) : Measurable (fun ω ↦ suggestion d n (s ω)) := by
  apply measurable_pi_lambda
  intro i
  unfold suggestion
  split_ifs
  · exact measurable_const
  · apply Finset.measurable_fun_sum
    intro e _
    split_ifs
    · exact alpha_measurable hs d n e
    · exact measurable_const

theorem confidence_measurable : Measurable (fun ω ↦ confidence o d (s ω)) := by
  unfold confidence
  split_ifs
  · exact measurable_const
  · exact o.confidence_measurable.comp (measurable_fst.comp hs)

theorem radius_measurable : Measurable (fun ω ↦ radius o d (s ω)) := by
  unfold radius
  split_ifs
  · exact measurable_const
  · exact o.radius_measurable.comp (measurable_fst.comp hs)

theorem probability_measurable (n : ℕ) : Measurable (fun ω ↦ probability o d n (s ω)) :=
  o.prox_measurable.comp ((confidence_measurable hs o d).prodMk
    ((radius_measurable hs o d).prodMk (suggestion_measurable hs d n)))

theorem gradient_measurable (n : ℕ) : Measurable (fun ω ↦ gradient o d n (s ω)) := by
  apply measurable_pi_lambda
  intro i
  apply ((measurable_pi_apply i).comp (confidence_measurable hs o d)).sub
  apply Finset.measurable_fun_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp (radius_measurable hs o d))).mul
    ((measurable_pi_apply j).comp (probability_measurable hs o d n))

theorem transport_measurable (n : ℕ) : Measurable (fun ω ↦ transport o d n (s ω)) :=
  o.transport_measurable.comp ((suggestion_measurable hs d n).prodMk
    ((probability_measurable hs o d n).prodMk (gradient_measurable hs o d n)))

theorem proxy_measurable (n : ℕ) (i : ι) : Measurable (fun ω ↦ proxy o d n (s ω) i) := by
  apply ((measurable_pi_apply i).comp (gradient_measurable hs o d n)).sub
  apply Finset.measurable_fun_sum
  intro j _
  exact ((measurable_pi_apply j).comp (probability_measurable hs o d n)).mul
    ((measurable_pi_apply j).comp (confidence_measurable hs o d))

theorem expertLoss_measurable (n : ℕ) {b : Ω → Vec ι} (hb : Measurable b) (e : E) :
    Measurable (fun ω ↦ expertLoss o d n (s ω) (b ω) e) := by
  apply Finset.measurable_fun_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply (d.arm e)).comp
    (transport_measurable hs o d n))).mul
    ((proxy_measurable hs o d n j).add ((measurable_pi_apply j).comp hb))

theorem meanExpertLoss_measurable (n : ℕ) {b : Ω → Vec ι} (hb : Measurable b) :
    Measurable (fun ω ↦ meanExpertLoss o d n (s ω) (b ω)) := by
  apply Finset.measurable_fun_sum
  intro e _
  exact (alpha_measurable hs d n e).mul (expertLoss_measurable hs o d n hb e)

variable [MeasurableSpace ι] [MeasurableSingletonClass ι]

theorem step_measurable (n : ℕ) {A : Ω → ι} (hA : Measurable A)
    {Y : Ω → ℝ} (hY : Measurable Y) {b : Ω → Vec ι} (hb : Measurable b) :
    Measurable (fun ω ↦ step o d n (s ω) (A ω) (Y ω) (b ω)) := by
  refine Measurable.prodMk (Measurable.prodMk ?_ ?_) ?_
  · apply measurable_pi_lambda
    intro i
    apply measurable_pi_lambda
    intro j
    have hv := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
      (measurable_fst.comp (measurable_fst.comp hs)))
    split_ifs
    · exact hv
    · apply hv.add
      unfold CNDPhysical.covariance
      have hdiag : Measurable (fun ω ↦ if i = j then probability o d n (s ω) i else 0) := by
        split_ifs
        · exact (measurable_pi_apply i).comp (probability_measurable hs o d n)
        · exact measurable_const
      exact hdiag.sub
        (((measurable_pi_apply i).comp (probability_measurable hs o d n)).mul
          ((measurable_pi_apply j).comp (probability_measurable hs o d n)))
  · apply measurable_pi_lambda
    intro i
    have hv := (measurable_pi_apply i).comp (measurable_snd.comp (measurable_fst.comp hs))
    split_ifs
    · exact hv
    · exact hv.add (((PairConfidence.actionIndicator_measurable hA i).sub
        ((measurable_pi_apply i).comp (probability_measurable hs o d n))).mul hY)
  · apply measurable_pi_lambda
    intro e
    have hw := (measurable_pi_apply e).comp (measurable_snd.comp hs)
    split_ifs
    · exact hw
    · exact hw.mul (measurable_const.add (((meanExpertLoss_measurable hs o d n hb).sub
        (expertLoss_measurable hs o d n hb e)).const_mul _))
    · exact hw

end MeasurableMaps

section Run
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] [MeasurableSpace ι] [MeasurableSingletonClass ι]

structure Feedback (ℱ : Filtration ℕ m₀) where
  action : ℕ → Ω → ι
  residual : ℕ → Ω → ℝ
  broadcast : ℕ → Ω → Vec ι
  action_measurable : ∀ n, Measurable[ℱ (n + 1)] (action n)
  residual_measurable : ∀ n, Measurable[ℱ (n + 1)] (residual n)
  broadcast_measurable : ∀ n, Measurable[ℱ (n + 1)] (broadcast n)

def run (o : DecisionMaps ι) (d : ExpertData ι E) {ℱ : Filtration ℕ m₀} (f : Feedback (ι := ι) ℱ) :
    ℕ → Ω → State ι E
  | 0, _ => initialState
  | n + 1, ω => step o d n (run o d f n ω) (f.action n ω) (f.residual n ω) (f.broadcast n ω)

theorem run_measurable (o : DecisionMaps ι) (d : ExpertData ι E) {ℱ : Filtration ℕ m₀}
    (f : Feedback (ι := ι) ℱ) (n : ℕ) : Measurable[ℱ n] (run o d f n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
    exact step_measurable (m := ℱ (n + 1)) (ih.mono (ℱ.mono (Nat.le_succ n)) le_rfl) o d n
      (f.action_measurable n) (f.residual_measurable n) (f.broadcast_measurable n)

def runProbability (o : DecisionMaps ι) (d : ExpertData ι E) {ℱ : Filtration ℕ m₀}
    (f : Feedback (ι := ι) ℱ) (n : ℕ) (i : ι) (ω : Ω) : ℝ := probability o d n (run o d f n ω) i

theorem runProbability_measurable (o : DecisionMaps ι) (d : ExpertData ι E)
    {ℱ : Filtration ℕ m₀} (f : Feedback (ι := ι) ℱ) (n : ℕ) (i : ι) :
    Measurable[ℱ n] (runProbability o d f n i) :=
  (measurable_pi_apply i).comp (probability_measurable (m := ℱ n) (run_measurable o d f n) o d n)

theorem runProbability_simplex (o : DecisionMaps ι) (d : ExpertData ι E)
    {ℱ : Filtration ℕ m₀} (f : Feedback (ι := ι) ℱ) (n : ℕ) (ω : Ω) :
    (fun i ↦ runProbability o d f n i ω) ∈ CND.simplex := o.prox_simplex _

end Run
end Part2.CNDProcess

end

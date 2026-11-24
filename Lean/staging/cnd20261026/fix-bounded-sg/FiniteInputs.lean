import staging.cnd20261026.«fix-bounded-sg».StoppedKernel
import staging.cnd20261024.process.SGActual

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
namespace Part2.CNDHorizon
open CNDProcess
variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ} {T : ℕ}

def root : ι := Classical.choice inferInstance

/-- The original recursion, without measurability premises or tail laws. -/
def rawRun (o : DecisionMaps ι) (d : ExpertData ι E)
    (A : ℕ → Ω → ι) (Y : ℕ → Ω → ℝ) (b : ℕ → Ω → Vec ι) : ℕ → Ω → State ι E
  | 0, _ => initialState
  | n+1, ω => step o d n (rawRun o d A Y b n ω) (A n ω) (Y n ω) (b n ω)

theorem rawRun_prefix (o : DecisionMaps ι) (d : ExpertData ι E)
    (A A' : ℕ → Ω → ι) (Y Y' : ℕ → Ω → ℝ) (b b' : ℕ → Ω → Vec ι)
    (hA : ∀ t<T, A t=A' t) (hY : ∀ t<T, Y t=Y' t) (hb : ∀ t<T, b t=b' t)
    (n : ℕ) (hn : n≤T) : rawRun o d A Y b n=rawRun o d A' Y' b' n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    funext ω
    simp only [rawRun, congrFun (ih (by omega)) ω, hA n (by omega), hY n (by omega), hb n (by omega)]

structure BoundedInputs (ℱ : Filtration ℕ m₀) (θ : ι → ℝ) (R M D : ℝ) (T : ℕ) where
  R_nonneg : 0 ≤ R
  M_nonneg : 0 ≤ M
  D_nonneg : 0 ≤ D
  theta_range : ∀ a, 0 ≤ θ a ∧ θ a ≤ R
  pre : ℕ → MeasurableSpace Ω
  past_le_pre : ∀ n, n < T → ℱ n ≤ pre n
  pre_le_next : ∀ n, n < T → pre n ≤ ℱ (n + 1)
  action : ℕ → Ω → ι
  seed : ℕ → Ω → (ι → ℝ)
  publicCost : ℕ → ι → Ω → ℝ
  drift : ℕ → Ω → ℝ
  error : ℕ → ι → Ω → ℝ
  action_measurable : ∀ n, n < T → Measurable[ℱ (n + 1)] (action n)
  seed_measurable : ∀ n, n < T → Measurable[ℱ (n + 1)] (seed n)
  public_measurable : ∀ n, n < T → ∀ a, Measurable[pre n] (publicCost n a)
  drift_measurable : ∀ n, n < T → Measurable[pre n] (drift n)
  drift_range : ∀ n, n < T → ∀ ω, 0 ≤ drift n ω ∧ drift n ω ≤ M
  error_encoded : ∀ n, n < T → ∀ a, Measurable[pre n ⊔ MeasurableSpace.comap (seed n) inferInstance] (error n a)
  error_bound : ∀ n, n < T → ∀ a ω, |error n a ω| ≤ D

namespace BoundedInputs
variable (h : BoundedInputs ℱ θ R M D T)
def physical (n : ℕ) (i : ι) (ω : Ω) : ℝ := h.publicCost n i ω + θ i + h.drift n ω
def broadcast (n : ℕ) (ω : Ω) (i : ι) : ℝ := h.publicCost n i ω+h.error n i ω
def residual (n : ℕ) (ω : Ω) : ℝ := h.physical n (h.action n ω) ω-h.broadcast n ω (h.action n ω)
def extend : CNDProcess.PotentialInputs ℱ θ R M D where
  R_nonneg := h.R_nonneg
  M_nonneg := h.M_nonneg
  D_nonneg := h.D_nonneg
  theta_range := h.theta_range
  pre n := if n<T then h.pre n else ℱ n
  past_le_pre n := by split_ifs with hn; exact h.past_le_pre n hn; exact le_rfl
  pre_le_next n := by split_ifs with hn; exact h.pre_le_next n hn; exact ℱ.mono (Nat.le_succ n)
  action n := if n<T then h.action n else fun _ => root
  seed n := if n<T then h.seed n else fun _ _ => 0
  publicCost n i := if n<T then h.publicCost n i else fun _ => 0
  drift n := if n<T then h.drift n else fun _ => 0
  error n i := if n<T then h.error n i else fun _ => 0
  action_measurable n := by split_ifs with hn; exact h.action_measurable n hn; exact measurable_const
  seed_measurable n := by split_ifs with hn; exact h.seed_measurable n hn; exact measurable_const
  drift_measurable n := by split_ifs with hn; exact h.drift_measurable n hn; exact measurable_const
  public_measurable n i := by split_ifs with hn; exact h.public_measurable n hn i; exact measurable_const
  drift_range n ω := by split_ifs with hn; exact h.drift_range n hn ω; exact ⟨le_rfl,h.M_nonneg⟩
  error_encoded n i := by split_ifs with hn; exact h.error_encoded n hn i; exact measurable_const
  error_bound n i ω := by split_ifs with hn; exact h.error_bound n hn i ω; simpa using h.D_nonneg

theorem extend_action {n : ℕ} (hn : n<T) : h.extend.action n=h.action n := by simp [extend,hn]
theorem extend_public {n : ℕ} (hn : n<T) : h.extend.publicCost n=h.publicCost n := by simp [extend,hn]
theorem extend_physical {n : ℕ} (hn : n<T) : h.extend.physical n=h.physical n := by
  funext i ω; simp [CNDProcess.PotentialInputs.physical,physical,extend,hn]
theorem extend_broadcast {n : ℕ} (hn : n<T) : h.extend.broadcast n=h.broadcast n := by
  funext ω i; simp [CNDProcess.PotentialInputs.broadcast,broadcast,extend,hn]
theorem extend_residual {n : ℕ} (hn : n<T) : h.extend.residual n=h.residual n := by
  funext ω
  simp only [CNDProcess.PotentialInputs.residual,residual,h.extend_physical hn,h.extend_action hn,h.extend_broadcast hn]

theorem extend_run (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (hn : n≤T) :
    run o d h.extend.feedback n=rawRun o d h.action h.residual h.broadcast n := by
  have he : ∀ n, run o d h.extend.feedback n = rawRun o d h.extend.action h.extend.residual h.extend.broadcast n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => funext ω; simp only [run,rawRun,ih]; rfl
  rw [he]
  exact rawRun_prefix o d _ _ _ _ _ _ (fun t ht => h.extend_action ht)
    (fun t ht => h.extend_residual ht) (fun t ht => h.extend_broadcast ht) n hn
end BoundedInputs

structure SGInputs (ℱ : Filtration ℕ m₀) (θ : ι → ℝ) (R M D : ℝ) (T : ℕ) where
  R_nonneg : 0 ≤ R
  M_nonneg : 0 ≤ M
  D_nonneg : 0 ≤ D
  theta_range : ∀ i, 0 ≤ θ i ∧ θ i ≤ R
  pre : ℕ → MeasurableSpace Ω
  past_le_pre : ∀ n, n < T → ℱ n ≤ pre n
  pre_le_next : ∀ n, n < T → pre n ≤ ℱ (n + 1)
  action : ℕ → Ω → ι
  noise : ℕ → Ω → Vec ι
  encodingSeed : ℕ → Ω → Vec ι
  publicCost : ℕ → ι → Ω → ℝ
  drift : ℕ → Ω → ℝ
  error : ℕ → ι → Ω → ℝ
  action_measurable : ∀ n, n < T → Measurable[ℱ (n + 1)] (action n)
  noise_measurable : ∀ n, n < T → Measurable[ℱ (n + 1)] (noise n)
  seed_measurable : ∀ n, n < T → Measurable[ℱ (n + 1)] (encodingSeed n)
  public_measurable : ∀ n, n < T → ∀ i, Measurable[pre n] (publicCost n i)
  drift_measurable : ∀ n, n < T → Measurable[pre n] (drift n)
  drift_range : ∀ n, n < T → ∀ ω, 0 ≤ drift n ω ∧ drift n ω ≤ M
  error_encoded : ∀ n, n < T → ∀ i, Measurable[pre n ⊔
    (MeasurableSpace.comap (noise n) inferInstance ⊔
      MeasurableSpace.comap (encodingSeed n) inferInstance)] (error n i)
  error_bound : ∀ n, n < T → ∀ i ω, |error n i ω| ≤ D

namespace SGInputs
variable (h : SGInputs ℱ θ R M D T)
def physical (n : ℕ) (i : ι) (ω : Ω) : ℝ := h.publicCost n i ω + θ i + h.drift n ω + h.noise n ω i
def broadcast (n : ℕ) (ω : Ω) (i : ι) : ℝ := h.publicCost n i ω+h.error n i ω
def residual (n : ℕ) (ω : Ω) : ℝ := h.physical n (h.action n ω) ω-h.broadcast n ω (h.action n ω)
def extend : CNDProcess.SG.Inputs ℱ θ R M D where
  R_nonneg := h.R_nonneg
  M_nonneg := h.M_nonneg
  D_nonneg := h.D_nonneg
  theta_range := h.theta_range
  pre n := if n<T then h.pre n else ℱ n
  past_le_pre n := by split_ifs with hn; exact h.past_le_pre n hn; exact le_rfl
  pre_le_next n := by split_ifs with hn; exact h.pre_le_next n hn; exact ℱ.mono (Nat.le_succ n)
  action n := if n<T then h.action n else fun _ => root
  noise n := if n<T then h.noise n else fun _ _ => 0
  encodingSeed n := if n<T then h.encodingSeed n else fun _ _ => 0
  publicCost n i := if n<T then h.publicCost n i else fun _ => 0
  drift n := if n<T then h.drift n else fun _ => 0
  error n i := if n<T then h.error n i else fun _ => 0
  action_measurable n := by split_ifs with hn; exact h.action_measurable n hn; exact measurable_const
  noise_measurable n := by split_ifs with hn; exact h.noise_measurable n hn; exact measurable_const
  seed_measurable n := by split_ifs with hn; exact h.seed_measurable n hn; exact measurable_const
  drift_measurable n := by split_ifs with hn; exact h.drift_measurable n hn; exact measurable_const
  public_measurable n i := by split_ifs with hn; exact h.public_measurable n hn i; exact measurable_const
  drift_range n ω := by split_ifs with hn; exact h.drift_range n hn ω; exact ⟨le_rfl,h.M_nonneg⟩
  error_encoded n i := by split_ifs with hn; exact h.error_encoded n hn i; exact measurable_const
  error_bound n i ω := by split_ifs with hn; exact h.error_bound n hn i ω; simpa using h.D_nonneg

theorem extend_action {n : ℕ} (hn : n<T) : h.extend.action n=h.action n := by simp [extend,hn]
theorem extend_public {n : ℕ} (hn : n<T) : h.extend.publicCost n=h.publicCost n := by simp [extend,hn]
theorem extend_physical {n : ℕ} (hn : n<T) : h.extend.physical n=h.physical n := by
  funext i ω; simp [CNDProcess.SG.Inputs.physical,physical,extend,hn]
theorem extend_broadcast {n : ℕ} (hn : n<T) : h.extend.broadcast n=h.broadcast n := by
  funext ω i; simp [CNDProcess.SG.Inputs.broadcast,broadcast,extend,hn]
theorem extend_residual {n : ℕ} (hn : n<T) : h.extend.residual n=h.residual n := by
  funext ω
  simp only [CNDProcess.SG.Inputs.residual,residual,h.extend_physical hn,h.extend_action hn,h.extend_broadcast hn]

theorem extend_run (o : DecisionMaps ι) (d : ExpertData ι E) (n : ℕ) (hn : n≤T) :
    run o d h.extend.feedback n=rawRun o d h.action h.residual h.broadcast n := by
  have he : ∀ n, run o d h.extend.feedback n = rawRun o d h.extend.action h.extend.residual h.extend.broadcast n := by
    intro n; induction n with
    | zero => rfl
    | succ n ih => funext ω; simp only [run,rawRun,ih]; rfl
  rw [he]
  exact rawRun_prefix o d _ _ _ _ _ _ (fun t ht => h.extend_action ht)
    (fun t ht => h.extend_residual ht) (fun t ht => h.extend_broadcast ht) n hn
end SGInputs

end Part2.CNDHorizon

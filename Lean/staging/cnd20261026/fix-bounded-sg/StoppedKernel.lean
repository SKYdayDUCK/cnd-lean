import staging.cnd20261024.process.SGOriginal

/-! Same-space stopping of primitive M1 data. No tail sampling law is assumed. -/
noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory
namespace Part2.CNDHorizon
variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]

def stop {α : Type*} (T : ℕ) (a : α) (x : ℕ → Ω → α) (n : ℕ) : Ω → α :=
  if n < T then x n else fun _ => a

def stopP (T : ℕ) (root : ι) (p : ℕ → ι → Ω → ℝ) (n : ℕ) (i : ι) : Ω → ℝ :=
  if n < T then p n i else fun _ => if root = i then 1 else 0

theorem stop_measurable {α : Type*} [MeasurableSpace α] (T : ℕ) (a : α)
    (x : ℕ → Ω → α) (m : ℕ → MeasurableSpace Ω)
    (hx : ∀ n < T, Measurable[m n] (x n)) (n : ℕ) : Measurable[m n] (stop T a x n) := by
  by_cases hn : n < T
  · simpa only [stop, if_pos hn] using hx n hn
  · simp only [stop, if_neg hn]; exact measurable_const

/-- This record has only deterministic and measurability specifications.
The two probability laws below are required only in executed slots. -/
structure Primitive (ℱ : Filtration ℕ m₀) (θ : ι → ℝ) (R M D : ℝ) where
  R_nonneg : 0 ≤ R
  M_nonneg : 0 ≤ M
  D_nonneg : 0 ≤ D
  theta_range : ∀ i, 0 ≤ θ i ∧ θ i ≤ R
  pre : ℕ → MeasurableSpace Ω
  afterAction : ℕ → MeasurableSpace Ω
  encoded : ℕ → MeasurableSpace Ω
  past_le_pre : ∀ n, ℱ n ≤ pre n
  pre_le_action : ∀ n, pre n ≤ afterAction n
  action_le_next : ∀ n, afterAction n ≤ ℱ (n+1)
  pre_le_encoded : ∀ n, pre n ≤ encoded n
  encoded_le_next : ∀ n, encoded n ≤ ℱ (n+1)
  p : ℕ → ι → Ω → ℝ
  action : ℕ → Ω → ι
  publicCost : ℕ → ι → Ω → ℝ
  drift : ℕ → Ω → ℝ
  error : ℕ → ι → Ω → ℝ
  p_measurable : ∀ n i, Measurable[ℱ n] (p n i)
  p_nonneg : ∀ n ω i, 0 ≤ p n i ω
  p_sum : ∀ n ω, ∑ i, p n i ω = 1
  action_measurable : ∀ n, Measurable[afterAction n] (action n)
  public_measurable : ∀ n i, Measurable[pre n] (publicCost n i)
  drift_measurable : ∀ n, Measurable[pre n] (drift n)
  drift_range : ∀ n ω, 0 ≤ drift n ω ∧ drift n ω ≤ M
  error_encoded : ∀ n i, Measurable[encoded n] (error n i)
  error_bound : ∀ n i ω, |error n i ω| ≤ D

namespace Primitive
variable (a : Primitive ℱ θ R M D) (T : ℕ) (root : ι)
  (hcat : ∀ n < T, ∀ i, μ[PairConfidence.actionIndicator (a.action n) i | a.encoded n] =ᵐ[μ] a.p n i)
  (hcenter : ∀ n < T, ∀ i, μ[a.error n i | a.afterAction n] =ᵐ[μ] fun _ => 0)

def stopped : CNDProbability.M1Model ℱ μ θ R M D where
  R_nonneg := a.R_nonneg
  M_nonneg := a.M_nonneg
  D_nonneg := a.D_nonneg
  theta_range := a.theta_range
  pre n := if n < T then a.pre n else ℱ n
  afterAction n := if n < T then a.afterAction n else ℱ n
  encoded n := if n < T then a.encoded n else ℱ n
  past_le_pre n := by split_ifs with hn; exact a.past_le_pre n; exact le_rfl
  pre_le_action n := by split_ifs; exact a.pre_le_action n; exact le_rfl
  action_le_next n := by split_ifs; exact a.action_le_next n; exact ℱ.mono (Nat.le_succ n)
  pre_le_encoded n := by split_ifs; exact a.pre_le_encoded n; exact le_rfl
  encoded_le_next n := by split_ifs; exact a.encoded_le_next n; exact ℱ.mono (Nat.le_succ n)
  p := stopP T root a.p
  action := stop T root a.action
  publicCost n i ω := if n < T then a.publicCost n i ω else 0
  drift := stop T 0 a.drift
  error n i ω := if n < T then a.error n i ω else 0
  p_measurable n i := by
    by_cases hn : n < T
    · simpa only [stopP, if_pos hn] using a.p_measurable n i
    · simp only [stopP, if_neg hn]; exact measurable_const
  p_nonneg n ω i := by
    by_cases hn : n < T
    · simpa only [stopP, if_pos hn] using a.p_nonneg n ω i
    · simp only [stopP, if_neg hn]; split_ifs <;> norm_num
  p_sum n ω := by
    by_cases hn : n < T
    · simpa only [stopP, if_pos hn] using a.p_sum n ω
    · simp [stopP, hn]
  action_measurable n := by
    by_cases hn : n < T
    · simpa only [stop, if_pos hn] using a.action_measurable n
    · simp only [stop, if_neg hn]; exact measurable_const
  public_measurable n i := by split_ifs; exact a.public_measurable n i; exact measurable_const
  drift_measurable n := by
    by_cases hn : n < T
    · simpa only [stop, if_pos hn] using a.drift_measurable n
    · simp only [stop, if_neg hn]; exact measurable_const
  drift_range n ω := by
    by_cases hn : n < T
    · simpa only [stop, if_pos hn] using a.drift_range n ω
    · simp only [stop, if_neg hn]; exact ⟨le_rfl, a.M_nonneg⟩
  error_measurable n i := by
    split_ifs
    · exact (a.error_encoded n i).mono (a.encoded_le_next n) le_rfl
    · exact measurable_const
  error_encoded n i := by split_ifs; exact a.error_encoded n i; exact measurable_const
  error_bound n i ω := by split_ifs; exact a.error_bound n i ω; simpa using a.D_nonneg
  strong_categorical n i := by
    by_cases hn : n < T
    · simpa only [stop, stopP, if_pos hn] using hcat n hn i
    · simp only [stop, stopP, if_neg hn, PairConfidence.actionIndicator]
      change μ[fun _ : Ω => (if root=i then (1:ℝ) else 0) | ℱ n] =ᵐ[μ] _
      rw [condExp_const (ℱ.le n)]
  encoder_centered n i := by
    by_cases hn : n < T
    · simpa only [if_pos hn] using hcenter n hn i
    · simp only [if_neg hn]
      rw [condExp_const (ℱ.le n)]
  categorical n i := by
    by_cases hn : n < T
    · simp only [stop, stopP, if_pos hn]
      apply PairConfidence.conditional_down (m₁ := a.pre n) (m₂ := a.encoded n)
        (a.pre_le_encoded n) ((a.encoded_le_next n).trans (ℱ.le (n+1))) (hcat n hn i)
        ((a.p_measurable n i).stronglyMeasurable.mono (a.past_le_pre n))
      apply PairConfidence.bounded_integrable ((a.p_measurable n i).mono (ℱ.le n) le_rfl)
      intro ω
      rw [abs_of_nonneg (a.p_nonneg n ω i)]
      simpa only [a.p_sum n ω] using single_le_sum (fun j _ => a.p_nonneg n ω j) (mem_univ i)
    · simp only [stop, stopP, if_neg hn, PairConfidence.actionIndicator]
      change μ[fun _ : Ω => (if root=i then (1:ℝ) else 0) | ℱ n] =ᵐ[μ] _
      rw [condExp_const (ℱ.le n)]

theorem stopped_p_before {n : ℕ} (hn : n < T) :
    (a.stopped T root hcat hcenter).p n = a.p n := by
  funext i ω; simp only [stopped, stopP, if_pos hn]

theorem stopped_p_after {n : ℕ} (hn : T ≤ n) :
    (a.stopped T root hcat hcenter).p n = fun i _ => if root=i then 1 else 0 := by
  funext i ω; simp only [stopped, stopP, if_neg (not_lt.mpr hn)]
end Primitive
end Part2.CNDHorizon

import staging.cnd20261024.process.OriginalM1

/-! The actual V/S recursion, finite-sum identities and unconditional L1 bounds.
No bound on the unbounded common public offset is required: it cancels once
in the observed residual before any integrability argument is used. -/

noncomputable section
open MeasureTheory Filter Finset
open scoped BigOperators ProbabilityTheory

namespace Part2.CNDProcess

variable {ι E Ω : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
  [Fintype E] [DecidableEq E] [MeasurableSpace ι] [MeasurableSingletonClass ι]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}

def runV (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i j : ι) (ω : Ω) : ℝ := (run o d f n ω).1.1 i j

def runS (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i : ι) (ω : Ω) : ℝ := (run o d f n ω).1.2 i

theorem runV_measurable (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i j : ι) : Measurable[ℱ n] (runV o d f n i j) :=
  (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_fst.comp (measurable_fst.comp (run_measurable o d f n))))

theorem runS_measurable (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i : ι) : Measurable[ℱ n] (runS o d f n i) :=
  (measurable_pi_apply i).comp (measurable_snd.comp (measurable_fst.comp (run_measurable o d f n)))

theorem runV_succ (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i j : ι) (ω : Ω) :
    runV o d f (n + 1) i j ω = if d.R = 0 then runV o d f n i j ω else
      runV o d f n i j ω + CNDPhysical.covariance (fun a ↦ runProbability o d f n a ω) i j := rfl

theorem runS_succ (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i : ι) (ω : Ω) :
    runS o d f (n + 1) i ω = if d.R = 0 then runS o d f n i ω else
      runS o d f n i ω + ((if f.action n ω = i then 1 else 0) - runProbability o d f n i ω) * f.residual n ω := rfl

theorem actual_information_identity (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (i j : ι) (ω : Ω) :
    runV o d f n i j ω = (if i = j then 1 else 0) - (Fintype.card ι : ℝ)⁻¹ +
      ∑ t ∈ Finset.range n, CNDPhysical.covariance (fun a ↦ runProbability o d f t a ω) i j := by
  induction n with
  | zero => simp [runV, run, initialState]
  | succ n ih => rw [runV_succ, if_neg hR, ih, Finset.sum_range_succ]; ring

theorem actual_statistic_identity (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (hR : d.R ≠ 0) (n : ℕ) (i : ι) (ω : Ω) :
    runS o d f n i ω = ∑ t ∈ Finset.range n,
      ((if f.action t ω = i then 1 else 0) - runProbability o d f t i ω) * f.residual t ω := by
  induction n with
  | zero => simp [runS, run, initialState]
  | succ n ih => rw [runS_succ, if_neg hR, ih, Finset.sum_range_succ]

theorem runProbability_bounds (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (n : ℕ) (i : ι) (ω : Ω) :
    0 ≤ runProbability o d f n i ω ∧ runProbability o d f n i ω ≤ 1 := by
  have hp := runProbability_simplex o d f n ω
  refine ⟨hp.1 i, ?_⟩
  calc
    _ ≤ ∑ j, runProbability o d f n j ω :=
      Finset.single_le_sum (fun j _ ↦ hp.1 j) (Finset.mem_univ i)
    _ = 1 := hp.2

theorem centeredIndicator_bound (o : DecisionMaps ι) (d : ExpertData ι E)
    (f : Feedback (ι := ι) ℱ) (n : ℕ) (i : ι) (ω : Ω) :
    |(if f.action n ω = i then 1 else 0) - runProbability o d f n i ω| ≤ 1 := by
  have hp := runProbability_bounds o d f n i ω
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

theorem covariance_entry_bound (p : ι → ℝ) (hp : p ∈ CND.simplex) (i j : ι) :
    |CNDPhysical.covariance p i j| ≤ 2 := by
  have hbound (k : ι) : 0 ≤ p k ∧ p k ≤ 1 := by
    refine ⟨hp.1 k, ?_⟩
    calc
      _ ≤ ∑ l, p l := Finset.single_le_sum (fun l _ ↦ hp.1 l) (Finset.mem_univ k)
      _ = 1 := hp.2
  have hprod : |p i * p j| ≤ 1 := by
    rw [abs_mul, abs_of_nonneg (hbound i).1, abs_of_nonneg (hbound j).1]
    exact (mul_le_mul_of_nonneg_right (hbound i).2 (hbound j).1).trans (by simpa using (hbound j).2)
  have hdiag : |(if i = j then p i else 0)| ≤ 1 := by
    split_ifs
    · simpa [abs_of_nonneg (hbound i).1] using (hbound i).2
    · norm_num
  exact (abs_sub _ _).trans (by linarith)

theorem initial_information_bound (i j : ι) :
    |(if i = j then (1 : ℝ) else 0) - (Fintype.card ι : ℝ)⁻¹| ≤ 2 := by
  have hk : (1 : ℝ) ≤ Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hi : (Fintype.card ι : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
  have hn : (0 : ℝ) ≤ (Fintype.card ι : ℝ)⁻¹ := by positivity
  rw [abs_le]
  split_ifs <;> constructor <;> linarith

theorem runV_bound (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i j : ι) (ω : Ω) : |runV o d f n i j ω| ≤ 2 + 2 * n := by
  induction n with
  | zero => simpa [runV, run, initialState] using initial_information_bound i j
  | succ n ih =>
    rw [runV_succ]
    split_ifs
    · exact ih.trans (by norm_num)
    · have hc := covariance_entry_bound _ (runProbability_simplex o d f n ω) i j
      have hh := abs_add_le (runV o d f n i j ω)
        (CNDPhysical.covariance (fun a ↦ runProbability o d f n a ω) i j)
      norm_num at *
      linarith

theorem runS_bound (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (H : ℝ) (hH : 0 ≤ H) (hY : ∀ n ω, |f.residual n ω| ≤ H)
    (n : ℕ) (i : ι) (ω : Ω) : |runS o d f n i ω| ≤ n * H := by
  induction n with
  | zero => simp [runS, run, initialState]
  | succ n ih =>
    rw [runS_succ]
    by_cases hz : d.R = 0
    · rw [if_pos hz]
      norm_num at *
      nlinarith
    · rw [if_neg hz]
      have hb := centeredIndicator_bound o d f n i ω
      have hm : |((if f.action n ω = i then 1 else 0) - runProbability o d f n i ω) * f.residual n ω| ≤ H := by
        rw [abs_mul]
        exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (by simpa using hY n ω)
      have ha := abs_add_le (runS o d f n i ω)
        (((if f.action n ω = i then 1 else 0) - runProbability o d f n i ω) * f.residual n ω)
      norm_num at *
      nlinarith

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem runV_integrable (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (n : ℕ) (i j : ι) : Integrable (runV o d f n i j) μ :=
  PairConfidence.bounded_integrable ((runV_measurable o d f n i j).mono (ℱ.le n) le_rfl)
    (runV_bound o d f n i j)

theorem runS_integrable (o : DecisionMaps ι) (d : ExpertData ι E) (f : Feedback (ι := ι) ℱ)
    (H : ℝ) (hH : 0 ≤ H) (hY : ∀ n ω, |f.residual n ω| ≤ H)
    (n : ℕ) (i : ι) : Integrable (runS o d f n i) μ :=
  PairConfidence.bounded_integrable ((runS_measurable o d f n i).mono (ℱ.le n) le_rfl)
    (runS_bound o d f H hH hY n i)

end Part2.CNDProcess

end

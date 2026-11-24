import staging.cnd20261024.probability.FiniteVille

/-! Generic restricted-MGF process tools for unbounded increments.
These are tools, not a replacement for deriving CND's one-step MGF.
All cumulative integrability is derived from primitive all-parameter
exponential integrability of individual increments. -/

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators
set_option maxHeartbeats 1000000

namespace Part2.CNDProbability.SGRestricted
section Integrability
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

lemma integrable_exp_add {X Y : Ω → ℝ}
    (hX : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * X ω)) μ)
    (hY : ∀ t : ℝ, Integrable (fun ω => Real.exp (t * Y ω)) μ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * (X ω + Y ω))) μ := by
  have hm := (hX t).aestronglyMeasurable.mul (hY t).aestronglyMeasurable
  have heq : (fun ω => Real.exp (t * (X ω + Y ω))) =
      (fun ω => Real.exp (t * X ω) * Real.exp (t * Y ω)) := by
    funext ω
    rw [mul_add, Real.exp_add]
  rw [heq]
  apply ((hX (2 * t)).add (hY (2 * t))).mono' hm
  apply Eventually.of_forall
  intro ω
  change ‖Real.exp (t * X ω) * Real.exp (t * Y ω)‖ ≤ Real.exp ((2 * t) * X ω) + Real.exp ((2 * t) * Y ω)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]
  have hx : Real.exp (t * X ω) ^ 2 = Real.exp ((2 * t) * X ω) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hy : Real.exp (t * Y ω) ^ 2 = Real.exp ((2 * t) * Y ω) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  nlinarith [sq_nonneg (Real.exp (t * X ω) - Real.exp (t * Y ω)),
    sq_nonneg (Real.exp (t * X ω)), sq_nonneg (Real.exp (t * Y ω))]

lemma exp_sum_integrable (X : ℕ → Ω → ℝ)
    (hX : ∀ n t, Integrable (fun ω => Real.exp (t * X n ω)) μ) :
    ∀ n t, Integrable (fun ω => Real.exp (t * Bernstein.sumProcess X n ω)) μ := by
  intro n
  induction n with
  | zero => intro t; simpa only [Bernstein.sumProcess, Finset.sum_range_zero, mul_zero, Real.exp_zero] using integrable_const (1 : ℝ)
  | succ n ih =>
    intro t
    simpa only [Bernstein.sumProcess, Finset.sum_range_succ] using
      integrable_exp_add ih (hX n) t

end Integrability

section Process
variable {Ω : Type*} [m₀ : MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m₀} {X q : ℕ → Ω → ℝ} {a t : ℝ}

noncomputable def process (X q : ℕ → Ω → ℝ) (a t : ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  Real.exp (t * Bernstein.sumProcess X n ω - a * t ^ 2 * Bernstein.sumProcess q n ω)

lemma process_zero : process X q a t 0 = fun _ => 1 := by
  funext ω
  simp [process, Bernstein.sumProcess]

lemma process_succ (n : ℕ) (ω : Ω) : process X q a t (n + 1) ω =
    process X q a t n ω * Real.exp (t * X n ω - a * t ^ 2 * q n ω) := by
  simp only [process, Bernstein.sumProcess, Finset.sum_range_succ, ← Real.exp_add]
  congr 1
  ring

lemma process_adapted
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hqm : ∀ n, StronglyMeasurable[ℱ n] (q n)) : Adapted ℱ (process X q a t) := by
  intro n
  have hxs : StronglyMeasurable[ℱ n] (Bernstein.sumProcess X n) :=
    (Finset.range n).stronglyMeasurable_fun_sum fun i hi =>
      (hXm i).mono (ℱ.mono (Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)))
  have hqs : StronglyMeasurable[ℱ n] (Bernstein.sumProcess q n) :=
    (Finset.range n).stronglyMeasurable_fun_sum fun i hi =>
      (hqm i).mono (ℱ.mono (Finset.mem_range.mp hi).le)
  exact Real.continuous_exp.comp_stronglyMeasurable ((hxs.const_mul t).sub (hqs.const_mul (a * t ^ 2)))

lemma process_integrable (ha : 0 ≤ a)
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hqm : ∀ n, StronglyMeasurable[ℱ n] (q n)) (hq0 : ∀ n ω, 0 ≤ q n ω)
    (hXi : ∀ n s, Integrable (fun ω => Real.exp (s * X n ω)) μ) (n : ℕ) :
    Integrable (process X q a t n) μ := by
  apply (exp_sum_integrable X hXi n t).mono'
    (((process_adapted hXm hqm n).mono (ℱ.le n)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro ω
  change ‖Real.exp (t * Bernstein.sumProcess X n ω - a * t ^ 2 * Bernstein.sumProcess q n ω)‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  apply sub_le_self
  exact mul_nonneg (mul_nonneg ha (sq_nonneg t)) (Finset.sum_nonneg fun i _ => hq0 i ω)

/-- Genuine exponential supermartingale after a separately proved one-step
conditional MGF. No cumulative integrability or supermartingale target is
assumed. This generic tool does not claim to discharge SG-M1's random
predictable-parameter step. -/
theorem supermartingale_of_conditional_mgf (ha : 0 ≤ a)
    (hXm : ∀ n, StronglyMeasurable[ℱ (n + 1)] (X n))
    (hqm : ∀ n, StronglyMeasurable[ℱ n] (q n)) (hq0 : ∀ n ω, 0 ≤ q n ω)
    (hXi : ∀ n s, Integrable (fun ω => Real.exp (s * X n ω)) μ)
    (hmgf : ∀ n, μ[fun ω => Real.exp (t * X n ω) | ℱ n] ≤ᵐ[μ]
      fun ω => Real.exp (a * t ^ 2 * q n ω)) :
    Supermartingale (process X q a t) ℱ μ := by
  apply supermartingale_nat (process_adapted hXm hqm)
    (process_integrable ha hXm hqm hq0 hXi)
  intro n
  let D : Ω → ℝ := fun ω => process X q a t n ω * Real.exp (-(a * t ^ 2 * q n ω))
  have hDm : StronglyMeasurable[ℱ n] D :=
    (process_adapted hXm hqm n).mul
      (Real.continuous_exp.comp_stronglyMeasurable ((hqm n).const_mul (a * t ^ 2)).neg)
  have heq : (fun ω => D ω * Real.exp (t * X n ω)) = process X q a t (n + 1) := by
    funext ω
    rw [process_succ]
    dsimp [D]
    rw [mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hp := condExp_mul_of_stronglyMeasurable_left hDm
    (by
      change Integrable (fun ω => D ω * Real.exp (t * X n ω)) μ
      rw [heq]
      exact process_integrable ha hXm hqm hq0 hXi (n + 1)) (hXi n t)
  filter_upwards [hp, hmgf n] with ω hp hm
  rw [← heq]
  calc
    _ = D ω * (μ[fun ω => Real.exp (t * X n ω) | ℱ n]) ω := hp
    _ ≤ D ω * Real.exp (a * t ^ 2 * q n ω) :=
      mul_le_mul_of_nonneg_left hm (mul_nonneg (Real.exp_nonneg _) (Real.exp_nonneg _))
    _ = process X q a t n ω := by
      dsimp [D]
      rw [mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end Process

lemma restricted_parameter {a v L cap : ℝ} (ha : 0 ≤ a) (hv : 0 ≤ v) (hL : 0 < L) (hcap : 0 < cap) :
    let t := L / (Real.sqrt (a * v * L) + L / cap)
    0 ≤ t ∧ t ≤ cap ∧ a * t ^ 2 * v - t * (2 * Real.sqrt (a * v * L) + L / cap) ≤ -L := by
  let b := Real.sqrt (a * v * L)
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb2 : b ^ 2 = a * v * L := Real.sq_sqrt (by positivity)
  have hd : 0 < b + L / cap := by positivity
  let t := L / (b + L / cap)
  change 0 ≤ t ∧ t ≤ cap ∧ a * t ^ 2 * v - t * (2 * b + L / cap) ≤ -L
  have ht : 0 ≤ t := div_nonneg hL.le hd.le
  have hprod : t * (b + L / cap) = L := div_mul_cancel₀ L hd.ne'
  have htc : t ≤ cap := by
    dsimp [t]
    apply (div_le_iff₀ hd).2
    have hid : cap * (L / cap) = L := mul_div_cancel₀ L hcap.ne'
    nlinarith [mul_nonneg hcap.le hb]
  have htb : 0 ≤ t * b := mul_nonneg ht hb
  have htble : t * b ≤ L := by nlinarith [mul_nonneg ht (div_nonneg hL.le hcap.le)]
  have hsq : (t * b) ^ 2 ≤ L * (t * b) := by nlinarith [mul_nonneg htb (sub_nonneg.mpr htble)]
  have hid : (t * b) ^ 2 = (a * t ^ 2 * v) * L := by rw [mul_pow, hb2]; ring
  have hvar : a * t ^ 2 * v ≤ t * b := by nlinarith
  exact ⟨ht, htc, by nlinarith [hprod]⟩

end Part2.CNDProbability.SGRestricted

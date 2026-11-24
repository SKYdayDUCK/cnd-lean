import Part2.Pairwise
import Part2.Bernstein
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator

/-!
# Original-space categorical sampling to pairwise confidence

The primitive stochastic hypotheses below are the categorical action law and
coordinate-wise centering of the encoder after revealing the action. Pairwise
conditional moments are derived, not assumed. No success event restricts μ.
-/

open MeasureTheory Filter Finset
open scoped ProbabilityTheory BigOperators

namespace Part2.PairConfidence

section Elementary

variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsFiniteMeasure μ]

def actionIndicator (A : Ω → ι) (a : ι) (ω : Ω) : ℝ := if A ω = a then 1 else 0

lemma actionIndicator_measurable {m : MeasurableSpace Ω} {A : Ω → ι}
    (hA : Measurable[m] A) (a : ι) : Measurable[m] (actionIndicator A a) :=
  measurable_const.ite ((measurableSet_singleton a).preimage hA) measurable_const

lemma selected_eq_sum (A : Ω → ι) (f : ι → Ω → ℝ) (ω : Ω) :
    f (A ω) ω = ∑ a, f a ω * actionIndicator A a ω := by
  classical
  simp [actionIndicator, mul_ite, eq_comm]

lemma bounded_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hbound : ∀ ω, |f ω| ≤ B) : Integrable f μ :=
  (integrable_const B).mono' hf.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)

lemma selected_measurable {m : MeasurableSpace Ω} {A : Ω → ι} (hA : Measurable[m] A)
    {f : ι → Ω → ℝ} (hf : ∀ a, Measurable[m] (f a)) :
    Measurable[m] (fun ω => f (A ω) ω) := by
  have heq : (fun ω => f (A ω) ω) = fun ω => ∑ a, f a ω * actionIndicator A a ω :=
    funext (selected_eq_sum A f)
  rw [heq]
  exact Finset.measurable_fun_sum _ fun a _ => (hf a).mul (actionIndicator_measurable hA a)

lemma selected_integrable {A : Ω → ι} (hA : Measurable A)
    {f : ι → Ω → ℝ} (hf : ∀ a, Integrable (f a) μ) :
    Integrable (fun ω => f (A ω) ω) μ := by
  have hprod (a : ι) : Integrable (fun ω => f a ω * actionIndicator A a ω) μ := by
    have heq : (fun ω => f a ω * actionIndicator A a ω) =
        Set.indicator {ω | A ω = a} (f a) := by
      funext ω
      by_cases h : A ω = a <;> simp [actionIndicator, Set.indicator, h]
    rw [heq]
    exact (hf a).indicator ((measurableSet_singleton a).preimage hA)
  have heq : (fun ω => f (A ω) ω) = fun ω => ∑ a, f a ω * actionIndicator A a ω :=
    funext (selected_eq_sum A f)
  rw [heq]
  exact integrable_finset_sum _ fun a _ => hprod a

/-- Conditional categorical integration with random predictable coefficients.
The primitive hypothesis concerns only action indicators, not score moments. -/
theorem conditional_selected {m : MeasurableSpace Ω} {A : Ω → ι} {p : ι → Ω → ℝ}
    (hA : Measurable[m₀] A)
    (hlaw : ∀ a, μ[actionIndicator A a | m] =ᵐ[μ] p a)
    (f : ι → Ω → ℝ) (hfm : ∀ a, StronglyMeasurable[m] (f a))
    (hfi : ∀ a, Integrable (f a) μ) :
    μ[fun ω => f (A ω) ω | m] =ᵐ[μ] fun ω => ∑ a, p a ω * f a ω := by
  letI : MeasurableSpace Ω := m₀
  have hprod (a : ι) : Integrable (fun ω => f a ω * actionIndicator A a ω) μ := by
    have heq : (fun ω => f a ω * actionIndicator A a ω) =
        Set.indicator {ω | A ω = a} (f a) := by
      funext ω
      by_cases h : A ω = a <;> simp [actionIndicator, Set.indicator, h]
    rw [heq]
    exact (hfi a).indicator ((measurableSet_singleton a).preimage hA)
  have hterm (a : ι) : μ[fun ω => f a ω * actionIndicator A a ω | m] =ᵐ[μ]
      fun ω => f a ω * p a ω := by
    have hIi : Integrable (actionIndicator A a) μ := bounded_integrable (B := (1 : ℝ))
      (actionIndicator_measurable hA a) (fun ω => by
        unfold actionIndicator
        split_ifs <;> norm_num)
    have hpull := condExp_mul_of_stronglyMeasurable_left (hfm a) (hprod a) hIi
    filter_upwards [hpull, hlaw a] with ω hp hl
    change (μ[fun ω => f a ω * actionIndicator A a ω | m]) ω =
      f a ω * (μ[actionIndicator A a | m]) ω at hp
    simpa only [hl] using hp
  have hsum := condExp_finset_sum (s := Finset.univ) (m := m) (fun a _ => hprod a)
  have heq : (fun ω => f (A ω) ω) = fun ω => ∑ a, f a ω * actionIndicator A a ω :=
    funext (selected_eq_sum A f)
  rw [heq]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with ω hs ht
  simp only [Finset.sum_fn, Finset.sum_apply] at hs
  change (μ[fun ω => ∑ a, f a ω * actionIndicator A a ω | m]) ω =
    ∑ a, (μ[fun ω => f a ω * actionIndicator A a ω | m]) ω at hs
  rw [hs]
  exact Finset.sum_congr rfl fun a _ => (ht a).trans (mul_comm _ _)

lemma conditional_zero_down {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ m₀)
    {f : Ω → ℝ} (hf : μ[f | m₂] =ᵐ[μ] fun _ => 0) :
    μ[f | m₁] =ᵐ[μ] fun _ => 0 := by
  have ht := condExp_condExp_of_le (μ := μ) (f := f) h12 h2
  have hz := condExp_congr_ae (m := m₁) hf
  have hzero : μ[fun _ : Ω => (0 : ℝ) | m₁] = fun _ => 0 := condExp_zero
  exact ht.symm.trans (hz.trans (EventuallyEq.of_eq hzero))

lemma conditional_down {m₁ m₂ : MeasurableSpace Ω} (h12 : m₁ ≤ m₂) (h2 : m₂ ≤ m₀)
    {f g : Ω → ℝ} (hf : μ[f | m₂] =ᵐ[μ] g)
    (hgm : StronglyMeasurable[m₁] g) (hgi : Integrable g μ) :
    μ[f | m₁] =ᵐ[μ] g := by
  have ht := condExp_condExp_of_le (μ := μ) (f := f) h12 h2
  have hg := condExp_congr_ae (m := m₁) hf
  exact ht.symm.trans (hg.trans (EventuallyEq.of_eq
    (condExp_of_stronglyMeasurable (h12.trans h2) hgm hgi)))

/-- A coordinate-wise centered encoder remains centered after selecting its
coordinate by an already-revealed action. No independence is postulated. -/
theorem conditional_selected_zero {m : MeasurableSpace Ω} (hm : m ≤ m₀)
    {A : Ω → ι} (hA : Measurable[m] A) (e : ι → Ω → ℝ)
    (hei : ∀ a, Integrable (e a) μ) (he0 : ∀ a, μ[e a | m] =ᵐ[μ] fun _ => 0) :
    μ[fun ω => e (A ω) ω | m] =ᵐ[μ] fun _ => 0 := by
  letI : MeasurableSpace Ω := m₀
  let f : ι → Ω → ℝ := fun a => Set.indicator {ω | A ω = a} (e a)
  have hfi (a : ι) : Integrable (f a) μ :=
    (hei a).indicator (hm _ ((measurableSet_singleton a).preimage hA))
  have hterm (a : ι) : μ[f a | m] =ᵐ[μ] fun _ => 0 := by
    have hset : MeasurableSet[m] {ω | A ω = a} := by
      have hs : {ω | A ω = a} = A ⁻¹' {a} := by ext ω; simp
      rw [hs]
      exact (measurableSet_singleton a).preimage hA
    have ht := condExp_indicator (s := {ω | A ω = a}) (hei a) hset
    filter_upwards [ht, he0 a] with ω ht hz
    change (μ[f a | m]) ω = 0
    simpa only [Set.indicator_apply, Set.mem_setOf_eq, hz, ite_self] using ht
  have hsum := condExp_finset_sum (s := Finset.univ) (m := m) (fun a _ => hfi a)
  have heq : (fun ω => e (A ω) ω) = fun ω => ∑ a, f a ω := by
    funext ω
    rw [selected_eq_sum A e ω]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : A ω = a <;> simp [f, Set.indicator, actionIndicator, ha]
  rw [heq]
  filter_upwards [hsum, ae_all_iff.mpr hterm] with ω hs ht
  simp only [Finset.sum_fn, Finset.sum_apply] at hs
  change (μ[fun ω => ∑ a, f a ω | m]) ω = 0
  rw [hs]
  exact Finset.sum_eq_zero fun a _ => ht a

lemma bounded_square_integrable {f : Ω → ℝ} {B : ℝ} (hf : Measurable f)
    (hbound : ∀ ω, |f ω| ≤ B) : Integrable (fun ω => (f ω) ^ 2) μ := by
  have hi := bounded_integrable (μ := μ) hf hbound
  have hp := hi.bdd_mul' hf.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun ω => by simpa only [Real.norm_eq_abs] using hbound ω)
  simpa only [pow_two] using hp

/-- Conditional variance reduction by the predictable conditional mean. The
integrability premises below are technical and derived from physical bounds
at the model call site. -/
lemma centered_square_le {m : MeasurableSpace Ω} (hm : m ≤ m₀) {W b : Ω → ℝ}
    (hbm : StronglyMeasurable[m] b) (hWi : Integrable W μ)
    (hW2i : Integrable (fun ω => (W ω) ^ 2) μ)
    (hbWi : Integrable (fun ω => b ω * W ω) μ)
    (hb2i : Integrable (fun ω => (b ω) ^ 2) μ)
    (hmean : μ[W | m] =ᵐ[μ] b) :
    μ[fun ω => (W ω - b ω) ^ 2 | m] ≤ᵐ[μ] μ[fun ω => (W ω) ^ 2 | m] := by
  letI : MeasurableSpace Ω := m₀
  have hs := condExp_sub hW2i (hbWi.const_mul 2) m
  have ha := condExp_add (hW2i.sub (hbWi.const_mul 2)) hb2i m
  have hm2 := condExp_smul (μ := μ) (2 : ℝ) (fun ω => b ω * W ω) m
  have hp := condExp_mul_of_stronglyMeasurable_left hbm hbWi hWi
  have hb := condExp_of_stronglyMeasurable hm (hbm.pow 2) hb2i
  change μ[fun ω => (b ω) ^ 2 | m] = (fun ω => (b ω) ^ 2) at hb
  have heq : (fun ω => (W ω - b ω) ^ 2) =
      (fun ω => (W ω) ^ 2 - 2 * (b ω * W ω)) + (fun ω => (b ω) ^ 2) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  rw [heq]
  filter_upwards [hs, ha, hm2, hp, hmean] with ω hs ha hm2 hp hmean
  change (μ[fun ω => (W ω) ^ 2 - 2 * (b ω * W ω) | m]) ω =
    (μ[fun ω => (W ω) ^ 2 | m]) ω - (μ[fun ω => 2 * (b ω * W ω) | m]) ω at hs
  change (μ[(fun ω => (W ω) ^ 2 - 2 * (b ω * W ω)) + (fun ω => (b ω) ^ 2) | m]) ω =
    (μ[fun ω => (W ω) ^ 2 - 2 * (b ω * W ω) | m]) ω + (μ[fun ω => (b ω) ^ 2 | m]) ω at ha
  change (μ[fun ω => 2 * (b ω * W ω) | m]) ω = 2 * (μ[fun ω => b ω * W ω | m]) ω at hm2
  change (μ[fun ω => b ω * W ω | m]) ω = b ω * (μ[W | m]) ω at hp
  rw [ha, hs, hm2, hp, hmean, hb]
  nlinarith [sq_nonneg (b ω)]

end Elementary

noncomputable def clip (R x : ℝ) : ℝ := max (-R) (min R x)

lemma clip_range {R x : ℝ} (hR : 0 ≤ R) : -R ≤ clip R x ∧ clip R x ≤ R := by
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

lemma clip_contract {R x g : ℝ} (hg : -R ≤ g ∧ g ≤ R) : |clip R x - g| ≤ |x - g| := by
  have hmin : |min R x - g| ≤ |x - g| := by
    simpa only [min_eq_right hg.2, sub_self, abs_zero, max_eq_right (abs_nonneg (x - g))] using
      abs_min_sub_min_le_max R x R g
  have hmax : |clip R x - g| ≤ |min R x - g| := by
    simpa only [clip, max_eq_right hg.1, sub_self, abs_zero,
      max_eq_right (abs_nonneg (min R x - g))] using
      abs_max_sub_max_le_max (-R) (min R x) (-R) g
  exact hmax.trans hmin

noncomputable def confidenceLog (m T : ℕ) (δ : ℝ) : ℝ :=
  Real.log (8 * (m : ℝ) * ((T + 1 : ℕ) : ℝ) ^ 2 / δ)

lemma confidenceLog_pos {m T : ℕ} {δ : ℝ} (hm : 0 < m) (hδ : 0 < δ) (hδ1 : δ < 1) :
    0 < confidenceLog m T δ := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hT : (1 : ℝ) ≤ ((T + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le T)
  have hTsq : 1 ≤ ((T + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
  have hmT : 1 ≤ (m : ℝ) * ((T + 1 : ℕ) : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hm1) (sub_nonneg.mpr hTsq)]
  exact Real.log_pos ((lt_div_iff₀ hδ).2 (by nlinarith))

/-- The upper-triangular index is exactly the paper's m_K, rather than the
ordered-pair count K(K-1). -/
lemma upper_pair_card {ι : Type*} [Fintype ι] [LinearOrder ι] :
    Fintype.card {ij : ι × ι // ij.1 < ij.2} =
      Fintype.card ι * (Fintype.card ι - 1) / 2 := by
  classical
  have hcNat : Fintype.card {ij : ι × ι // ij.1 < ij.2} =
      ∑ ij : ι × ι, if ij.1 < ij.2 then 1 else 0 := by
    rw [Fintype.card_subtype, Finset.card_eq_sum_ones, Finset.sum_filter]
  have hcReal : (Fintype.card {ij : ι × ι // ij.1 < ij.2} : ℝ) =
      ∑ i : ι, ∑ j : ι, if i < j then (1 : ℝ) else 0 := by
    have hp : (Fintype.card {ij : ι × ι // ij.1 < ij.2} : ℝ) =
        ∑ ij : ι × ι, if ij.1 < ij.2 then (1 : ℝ) else 0 := by exact_mod_cast hcNat
    simpa only [Fintype.sum_prod_type] using hp
  let r : ι → ι → ℝ := fun i j => if i = j then 0 else 1
  have hr : ∀ i j, r i j = r j i := by intro i j; simp [r, eq_comm]
  have hd : ∀ i, r i i = 0 := by intro i; simp [r]
  have ht := Pairwise.symmetric_sum_upper_triangle (fun _ : ι => (1 : ℝ)) r hr hd
  simp only [one_mul] at ht
  have hrow (i : ι) : (∑ j : ι, r i j) = (Fintype.card ι : ℝ) - 1 := by
    have heq (j : ι) : r i j = 1 - (if j = i then (1 : ℝ) else 0) := by
      by_cases hij : i = j <;> simp [r, hij, eq_comm]
    simp_rw [heq, Finset.sum_sub_distrib]
    simp
  have hleft : (∑ i : ι, ∑ j : ι, r i j) =
      (Fintype.card ι : ℝ) * ((Fintype.card ι : ℝ) - 1) := by simp_rw [hrow]; simp [mul_sub]
  have hright : (∑ i : ι, ∑ j : ι, if i < j then r i j else 0) =
      ∑ i : ι, ∑ j : ι, if i < j then (1 : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases hij : i < j <;> simp [r, hij, ne_of_lt]
  rw [hleft, hright, ← hcReal] at ht
  by_cases hK : Fintype.card ι = 0
  · have hm : Fintype.card {ij : ι × ι // ij.1 < ij.2} = 0 := by
      rw [hK] at ht
      norm_num at ht
      exact ht
    simp [hK, hm]
  have hK1 : 1 ≤ Fintype.card ι := Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hK)
  have hn : 2 * Fintype.card {ij : ι × ι // ij.1 < ij.2} =
      Fintype.card ι * (Fintype.card ι - 1) := by
    have hReal : (2 : ℝ) * (Fintype.card {ij : ι × ι // ij.1 < ij.2} : ℝ) =
        (Fintype.card ι : ℝ) * ((Fintype.card ι - 1 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hK1]
      norm_num
      linarith
    exact_mod_cast hReal
  exact (Nat.div_eq_of_eq_mul_right Nat.zero_lt_two hn.symm).symm

/-- The general pair score is exactly J-p in the original two-arm C1/C3
notation, since the two action masses sum to one. -/
lemma fin2_score_eq_centered_indicator (p : Fin 2 → ℝ) (hp : ∑ a, p a = 1) (a : Fin 2) :
    Pairwise.pairScore p 0 1 a = (if a = 0 then 1 else 0) - p 0 := by
  have hp01 : p 0 + p 1 = 1 := by simpa only [Fin.sum_univ_two] using hp
  have ha : a.val = 0 ∨ a.val = 1 :=
    Nat.le_one_iff_eq_zero_or_eq_one.mp (Nat.le_of_lt_succ a.isLt)
  rcases ha with ha | ha
  · have heq : a = 0 := Fin.ext ha
    subst a
    norm_num [Pairwise.pairScore, hp01] <;> linarith
  · have heq : a = 1 := Fin.ext ha
    subst a
    norm_num [Pairwise.pairScore, hp01]

lemma fin2_information_eq (p : Fin 2 → ℝ) (hp : ∑ a, p a = 1) :
    p 0 * p 1 / (p 0 + p 1) = p 0 * (1 - p 0) := by
  have hp01 : p 0 + p 1 = 1 := by simpa only [Fin.sum_univ_two] using hp
  rw [hp01, div_one]
  have hp1 : p 1 = 1 - p 0 := by linarith
  rw [hp1]

section Model

variable {Ω ι : Type*} [m₀ : MeasurableSpace Ω] [Fintype ι] [DecidableEq ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι]
  {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m₀}
  {θ : ι → ℝ} {R M D : ℝ}

/-- Original-space time ordering. `pre` contains the chosen current physical
state, `afterAction` additionally contains the action but precedes encoder
randomness. The only stochastic laws are categorical action indicators and
coordinate-wise encoder centering. -/
structure SamplingModel (ℱ : Filtration ℕ m₀) (μ : Measure Ω) (θ : ι → ℝ)
    (R M D : ℝ) where
  R_nonneg : 0 ≤ R
  M_nonneg : 0 ≤ M
  D_nonneg : 0 ≤ D
  theta_range : ∀ a, 0 ≤ θ a ∧ θ a ≤ R
  pre : ℕ → MeasurableSpace Ω
  afterAction : ℕ → MeasurableSpace Ω
  past_le_pre : ∀ n, ℱ n ≤ pre n
  pre_le_action : ∀ n, pre n ≤ afterAction n
  action_le_next : ∀ n, afterAction n ≤ ℱ (n + 1)
  p : ℕ → ι → Ω → ℝ
  action : ℕ → Ω → ι
  publicCost : ℕ → ι → Ω → ℝ
  drift : ℕ → Ω → ℝ
  error : ℕ → ι → Ω → ℝ
  p_measurable : ∀ n a, Measurable[ℱ n] (p n a)
  p_nonneg : ∀ n ω a, 0 ≤ p n a ω
  p_sum : ∀ n ω, ∑ a, p n a ω = 1
  action_measurable : ∀ n, Measurable[afterAction n] (action n)
  public_measurable : ∀ n a, Measurable[pre n] (publicCost n a)
  drift_measurable : ∀ n, Measurable[pre n] (drift n)
  drift_range : ∀ n ω, 0 ≤ drift n ω ∧ drift n ω ≤ M
  error_measurable : ∀ n a, Measurable[ℱ (n + 1)] (error n a)
  error_bound : ∀ n a ω, |error n a ω| ≤ D
  categorical : ∀ n a, μ[actionIndicator (action n) a | pre n] =ᵐ[μ] p n a
  encoder_centered : ∀ n a, μ[error n a | afterAction n] =ᵐ[μ] fun _ => 0

namespace SamplingModel

variable (h : SamplingModel ℱ μ θ R M D)

lemma pre_le (n : ℕ) : h.pre n ≤ m₀ :=
  (h.pre_le_action n).trans ((h.action_le_next n).trans (ℱ.le (n + 1)))

lemma action_le (n : ℕ) : h.afterAction n ≤ m₀ :=
  (h.action_le_next n).trans (ℱ.le (n + 1))

noncomputable def information (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.p n i ω * h.p n j ω / (h.p n i ω + h.p n j ω)

noncomputable def scoreAt (i j : ι) (n : ℕ) (a : ι) (ω : Ω) : ℝ :=
  Pairwise.pairScore (fun k => h.p n k ω) i j a

noncomputable def score (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.scoreAt i j n (h.action n ω) ω

/-- Actual physical observation minus reconstructed public observation. -/
def residual (n : ℕ) (ω : Ω) : ℝ :=
  (h.publicCost n (h.action n ω) ω + θ (h.action n ω) + h.drift n ω) -
    (h.publicCost n (h.action n ω) ω + h.error n (h.action n ω) ω)

lemma residual_eq (n : ℕ) (ω : Ω) :
    h.residual n ω = θ (h.action n ω) + h.drift n ω - h.error n (h.action n ω) ω := by
  unfold residual
  ring

noncomputable def statistic (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.score i j n ω * h.residual n ω

noncomputable def predictableMean (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  (θ i - θ j) * h.information i j n ω

noncomputable def increment (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.statistic i j n ω - h.predictableMean i j n ω

lemma scoreAt_measurable (i j : ι) (n : ℕ) (a : ι) :
    Measurable[ℱ n] (h.scoreAt i j n a) := by
  have h1 : Measurable[ℱ n] (fun ω => if a = i then h.p n j ω else 0) := by
    split_ifs <;> first | exact h.p_measurable n j | exact measurable_const
  have h2 : Measurable[ℱ n] (fun ω => if a = j then h.p n i ω else 0) := by
    split_ifs <;> first | exact h.p_measurable n i | exact measurable_const
  exact (h1.sub h2).div ((h.p_measurable n i).add (h.p_measurable n j))

lemma information_measurable (i j : ι) (n : ℕ) :
    Measurable[ℱ n] (h.information i j n) :=
  ((h.p_measurable n i).mul (h.p_measurable n j)).div
    ((h.p_measurable n i).add (h.p_measurable n j))

lemma information_bounds (i j : ι) (hij : i ≠ j) (n : ℕ) (ω : Ω) :
    0 ≤ h.information i j n ω ∧ h.information i j n ω ≤ 1 / 4 := by
  have hsum : h.p n i ω + h.p n j ω ≤ 1 := by
    have hs := Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.subset_univ ({i, j} : Finset ι)) (fun a _ _ => h.p_nonneg n ω a)
    simpa only [Finset.sum_pair hij, h.p_sum n ω] using hs
  by_cases hs : h.p n i ω + h.p n j ω = 0
  · simp [information, hs]
  have hpos : 0 < h.p n i ω + h.p n j ω :=
    lt_of_le_of_ne (add_nonneg (h.p_nonneg n ω i) (h.p_nonneg n ω j)) (Ne.symm hs)
  have hv := Pairwise.pair_variance_bounds (h.p n i ω) (h.p n j ω)
    (h.p_nonneg n ω i) (h.p_nonneg n ω j) hpos hsum
  exact ⟨hv.1, hv.2.1⟩

lemma scoreAt_bound (i j : ι) (n : ℕ) (a : ι) (ω : Ω) : |h.scoreAt i j n a ω| ≤ 1 :=
  Pairwise.pairScore_abs_le_one _ (h.p_nonneg n ω) i j a

include h in
lemma gap_bound (i j : ι) : |θ i - θ j| ≤ R := by
  rw [abs_le]
  constructor <;> linarith [(h.theta_range i).1, (h.theta_range i).2,
    (h.theta_range j).1, (h.theta_range j).2]

lemma residual_bound (n : ℕ) (ω : Ω) : |h.residual n ω| ≤ R + M + D := by
  rw [h.residual_eq, abs_le]
  have he := abs_le.mp (h.error_bound n (h.action n ω) ω)
  constructor <;> linarith [(h.theta_range (h.action n ω)).1,
    (h.theta_range (h.action n ω)).2, (h.drift_range n ω).1, (h.drift_range n ω).2]

lemma score_measurable (i j : ι) (n : ℕ) :
    Measurable[h.afterAction n] (h.score i j n) :=
  selected_measurable (h.action_measurable n) fun a =>
    (h.scoreAt_measurable i j n a).mono ((h.past_le_pre n).trans (h.pre_le_action n)) le_rfl

lemma residual_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (h.residual n) := by
  have hA := (h.action_measurable n).mono (h.action_le_next n) le_rfl
  have hθ : Measurable[ℱ (n + 1)] (fun ω => θ (h.action n ω)) :=
    selected_measurable hA fun a => measurable_const
  have he : Measurable[ℱ (n + 1)] (fun ω => h.error n (h.action n ω) ω) :=
    selected_measurable hA (h.error_measurable n)
  have hz := (h.drift_measurable n).mono ((h.pre_le_action n).trans (h.action_le_next n)) le_rfl
  have heq : h.residual n = fun ω => θ (h.action n ω) + h.drift n ω - h.error n (h.action n ω) ω :=
    funext (h.residual_eq n)
  rw [heq]
  exact (hθ.add hz).sub he

lemma statistic_measurable (i j : ι) (n : ℕ) :
    Measurable[ℱ (n + 1)] (h.statistic i j n) :=
  ((h.score_measurable i j n).mono (h.action_le_next n) le_rfl).mul (h.residual_measurable n)

lemma mean_measurable (i j : ι) (n : ℕ) :
    Measurable[ℱ n] (h.predictableMean i j n) :=
  (h.information_measurable i j n).const_mul _

lemma increment_measurable (i j : ι) (n : ℕ) :
    Measurable[ℱ (n + 1)] (h.increment i j n) :=
  (h.statistic_measurable i j n).sub ((h.mean_measurable i j n).mono
    (ℱ.mono (Nat.le_succ n)) le_rfl)

lemma statistic_bound (i j : ι) (n : ℕ) (ω : Ω) :
    |h.statistic i j n ω| ≤ R + M + D := by
  rw [statistic, abs_mul]
  have hs := h.scoreAt_bound i j n (h.action n ω) ω
  have hy := h.residual_bound n ω
  exact (mul_le_mul_of_nonneg_right hs (abs_nonneg _)).trans (by simpa using hy)

lemma mean_bound (i j : ι) (hij : i ≠ j) (n : ℕ) (ω : Ω) :
    |h.predictableMean i j n ω| ≤ R := by
  rw [predictableMean, abs_mul, abs_of_nonneg (h.information_bounds i j hij n ω).1]
  have hv : h.information i j n ω ≤ 1 := by linarith [(h.information_bounds i j hij n ω).2]
  simpa using mul_le_mul (h.gap_bound i j) hv (h.information_bounds i j hij n ω).1 h.R_nonneg

lemma increment_bound (i j : ι) (hij : i ≠ j) (n : ℕ) (ω : Ω) :
    |h.increment i j n ω| ≤ 2 * (R + M + D) := by
  exact (abs_sub _ _).trans (by
    have hs := h.statistic_bound i j n ω
    have hm := h.mean_bound i j hij n ω
    linarith [h.M_nonneg, h.D_nonneg])

lemma information_integrable (i j : ι) (hij : i ≠ j) (n : ℕ) :
    Integrable (h.information i j n) μ :=
  bounded_integrable ((h.information_measurable i j n).mono (ℱ.le n) le_rfl)
    (fun ω => by simpa only [abs_of_nonneg (h.information_bounds i j hij n ω).1]
      using (h.information_bounds i j hij n ω).2)

lemma mean_integrable (i j : ι) (hij : i ≠ j) (n : ℕ) :
    Integrable (h.predictableMean i j n) μ :=
  bounded_integrable ((h.mean_measurable i j n).mono (ℱ.le n) le_rfl) (h.mean_bound i j hij n)

lemma statistic_integrable (i j : ι) (n : ℕ) : Integrable (h.statistic i j n) μ :=
  bounded_integrable ((h.statistic_measurable i j n).mono (ℱ.le (n + 1)) le_rfl)
    (h.statistic_bound i j n)

/-- Original-space score centering from the categorical action law. -/
theorem score_conditional_mean (i j : ι) (n : ℕ) :
    μ[h.score i j n | ℱ n] =ᵐ[μ] fun _ => 0 := by
  have hI (a : ι) : Integrable (h.scoreAt i j n a) μ := bounded_integrable
    ((h.scoreAt_measurable i j n a).mono (ℱ.le n) le_rfl) (h.scoreAt_bound i j n a)
  have ht := conditional_selected ((h.action_measurable n).mono (h.action_le n) le_rfl)
    (h.categorical n) (h.scoreAt i j n)
    (fun a => ((h.scoreAt_measurable i j n a).stronglyMeasurable.mono (h.past_le_pre n))) hI
  have hp : μ[h.score i j n | h.pre n] =ᵐ[μ] fun _ => 0 := by
    filter_upwards [ht] with ω ht
    exact ht.trans (Pairwise.pairScore_mean_zero (fun a => h.p n a ω) i j)
  exact conditional_zero_down (h.past_le_pre n) (h.pre_le n) hp

/-- Original-space conditional second moment, including zero action masses. -/
theorem score_conditional_second (i j : ι) (hij : i ≠ j) (n : ℕ) :
    μ[fun ω => (h.score i j n ω) ^ 2 | ℱ n] =ᵐ[μ] h.information i j n := by
  let f : ι → Ω → ℝ := fun a ω => (h.scoreAt i j n a ω) ^ 2
  have hfbound (a : ι) (ω : Ω) : |f a ω| ≤ 1 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    have hs := h.scoreAt_bound i j n a ω
    simpa only [sq_abs, one_pow] using (sq_le_sq₀ (abs_nonneg _) zero_le_one).2 hs
  have hfm (a : ι) : Measurable[ℱ n] (f a) := (h.scoreAt_measurable i j n a).pow_const 2
  have ht := conditional_selected ((h.action_measurable n).mono (h.action_le n) le_rfl)
    (h.categorical n) f (fun a => (hfm a).stronglyMeasurable.mono (h.past_le_pre n))
    (fun a => bounded_integrable ((hfm a).mono (ℱ.le n) le_rfl) (hfbound a))
  have hp : μ[fun ω => (h.score i j n ω) ^ 2 | h.pre n] =ᵐ[μ] h.information i j n := by
    filter_upwards [ht] with ω ht
    exact ht.trans (Pairwise.pairScore_second_moment_nonneg _ (h.p_nonneg n ω) i j hij)
  exact conditional_down (h.past_le_pre n) (h.pre_le n) hp
    (h.information_measurable i j n).stronglyMeasurable (h.information_integrable i j hij n)

def selectedError (n : ℕ) (ω : Ω) : ℝ := h.error n (h.action n ω) ω

noncomputable def noiseStatistic (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.score i j n ω * h.selectedError n ω

noncomputable def signalStatistic (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  h.score i j n ω * (θ (h.action n ω) + h.drift n ω)

lemma selectedError_measurable (n : ℕ) : Measurable[ℱ (n + 1)] (h.selectedError n) :=
  selected_measurable ((h.action_measurable n).mono (h.action_le_next n) le_rfl)
    (h.error_measurable n)

lemma selectedError_integrable (n : ℕ) : Integrable (h.selectedError n) μ :=
  bounded_integrable ((h.selectedError_measurable n).mono (ℱ.le (n + 1)) le_rfl)
    (fun ω => h.error_bound n (h.action n ω) ω)

lemma noiseStatistic_integrable (i j : ι) (n : ℕ) : Integrable (h.noiseStatistic i j n) μ := by
  apply bounded_integrable
    ((((h.score_measurable i j n).mono (h.action_le_next n) le_rfl).mul
      (h.selectedError_measurable n)).mono (ℱ.le (n + 1)) le_rfl)
  intro ω
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (h.scoreAt_bound i j n (h.action n ω) ω)
    (abs_nonneg _)).trans (by simpa using h.error_bound n (h.action n ω) ω)

/-- Conditioning after the action centers the actual selected encoder error. -/
theorem selectedError_conditional_zero (n : ℕ) :
    μ[h.selectedError n | h.afterAction n] =ᵐ[μ] fun _ => 0 :=
  conditional_selected_zero (h.action_le n) (h.action_measurable n) (h.error n)
    (fun a => bounded_integrable ((h.error_measurable n a).mono (ℱ.le (n + 1)) le_rfl)
      (h.error_bound n a)) (h.encoder_centered n)

theorem noiseStatistic_conditional_zero (i j : ι) (n : ℕ) :
    μ[h.noiseStatistic i j n | h.pre n] =ᵐ[μ] fun _ => 0 := by
  have hpull := condExp_mul_of_stronglyMeasurable_left
    (h.score_measurable i j n).stronglyMeasurable
    (h.noiseStatistic_integrable i j n) (h.selectedError_integrable n)
  have hp : μ[h.noiseStatistic i j n | h.afterAction n] =ᵐ[μ] fun _ => 0 := by
    filter_upwards [hpull, h.selectedError_conditional_zero n] with ω hp hz
    change (μ[h.noiseStatistic i j n | h.afterAction n]) ω =
      h.score i j n ω * (μ[h.selectedError n | h.afterAction n]) ω at hp
    simpa only [hz, mul_zero] using hp
  exact conditional_zero_down (h.pre_le_action n) (h.action_le n) hp

lemma signalStatistic_integrable (i j : ι) (n : ℕ) :
    Integrable (h.signalStatistic i j n) μ := by
  let f : ι → Ω → ℝ := fun a ω => h.scoreAt i j n a ω * (θ a + h.drift n ω)
  have hfm (a : ι) : Measurable[h.pre n] (f a) :=
    ((h.scoreAt_measurable i j n a).mono (h.past_le_pre n) le_rfl).mul
      (measurable_const.add (h.drift_measurable n))
  have hfb (a : ι) (ω : Ω) : |f a ω| ≤ R + M := by
    change |h.scoreAt i j n a ω * (θ a + h.drift n ω)| ≤ R + M
    rw [abs_mul]
    have hz0 : 0 ≤ θ a + h.drift n ω := by
      linarith [(h.theta_range a).1, (h.drift_range n ω).1]
    have hzu : θ a + h.drift n ω ≤ R + M := by
      linarith [(h.theta_range a).2, (h.drift_range n ω).2]
    exact (mul_le_mul_of_nonneg_right (h.scoreAt_bound i j n a ω) (abs_nonneg (θ a + h.drift n ω))).trans
      (by simpa only [one_mul, abs_of_nonneg hz0] using hzu)
  exact selected_integrable ((h.action_measurable n).mono (h.action_le n) le_rfl)
    (fun a => bounded_integrable ((hfm a).mono (h.pre_le n) le_rfl) (hfb a))

/-- The action law eliminates the arbitrary adaptive common drift. -/
theorem signalStatistic_conditional_mean (i j : ι) (n : ℕ) :
    μ[h.signalStatistic i j n | h.pre n] =ᵐ[μ] h.predictableMean i j n := by
  let f : ι → Ω → ℝ := fun a ω => h.scoreAt i j n a ω * (θ a + h.drift n ω)
  have hfm (a : ι) : Measurable[h.pre n] (f a) :=
    ((h.scoreAt_measurable i j n a).mono (h.past_le_pre n) le_rfl).mul
      (measurable_const.add (h.drift_measurable n))
  have hfb (a : ι) (ω : Ω) : |f a ω| ≤ R + M := by
    change |h.scoreAt i j n a ω * (θ a + h.drift n ω)| ≤ R + M
    rw [abs_mul]
    have hz0 : 0 ≤ θ a + h.drift n ω := by
      linarith [(h.theta_range a).1, (h.drift_range n ω).1]
    have hzu : θ a + h.drift n ω ≤ R + M := by
      linarith [(h.theta_range a).2, (h.drift_range n ω).2]
    exact (mul_le_mul_of_nonneg_right (h.scoreAt_bound i j n a ω) (abs_nonneg (θ a + h.drift n ω))).trans
      (by simpa only [one_mul, abs_of_nonneg hz0] using hzu)
  have ht := conditional_selected ((h.action_measurable n).mono (h.action_le n) le_rfl)
    (h.categorical n) f (fun a => (hfm a).stronglyMeasurable)
    (fun a => bounded_integrable ((hfm a).mono (h.pre_le n) le_rfl) (hfb a))
  filter_upwards [ht] with ω ht
  calc
    _ = ∑ a, h.p n a ω * f a ω := ht
    _ = ∑ a, h.p n a ω * h.scoreAt i j n a ω * (θ a + h.drift n ω) := by
      apply Finset.sum_congr rfl
      intro a _
      dsimp [f]
      ring
    _ = h.information i j n ω * (θ i - θ j) :=
      Pairwise.pairScore_signal (fun a => h.p n a ω) θ (h.drift n ω) i j
    _ = h.predictableMean i j n ω := mul_comm _ _

/-- The actual observed statistic, including selected encoded error, has the
required original-space conditional mean. This is derived from the two raw
sampling/encoder laws, not stored in SamplingModel. -/
theorem statistic_conditional_mean (i j : ι) (hij : i ≠ j) (n : ℕ) :
    μ[h.statistic i j n | ℱ n] =ᵐ[μ] h.predictableMean i j n := by
  have heq : h.statistic i j n = h.signalStatistic i j n - h.noiseStatistic i j n := by
    funext ω
    dsimp [statistic, signalStatistic, noiseStatistic, selectedError]
    rw [h.residual_eq]
    ring
  have hs := condExp_sub (h.signalStatistic_integrable i j n)
    (h.noiseStatistic_integrable i j n) (h.pre n)
  have hp : μ[h.statistic i j n | h.pre n] =ᵐ[μ] h.predictableMean i j n := by
    rw [heq]
    filter_upwards [hs, h.signalStatistic_conditional_mean i j n,
      h.noiseStatistic_conditional_zero i j n] with ω hs hm hz
    change (μ[h.signalStatistic i j n - h.noiseStatistic i j n | h.pre n]) ω =
      (μ[h.signalStatistic i j n | h.pre n]) ω -
        (μ[h.noiseStatistic i j n | h.pre n]) ω at hs
    simpa only [hm, hz, sub_zero] using hs
  exact conditional_down (h.past_le_pre n) (h.pre_le n) hp
    (h.mean_measurable i j n).stronglyMeasurable (h.mean_integrable i j hij n)

theorem increment_conditional_zero (i j : ι) (hij : i ≠ j) (n : ℕ) :
    μ[h.increment i j n | ℱ n] =ᵐ[μ] fun _ => 0 := by
  have ht := condExp_sub (h.statistic_integrable i j n) (h.mean_integrable i j hij n) (ℱ n)
  have hm := condExp_of_stronglyMeasurable (ℱ.le n)
    (h.mean_measurable i j n).stronglyMeasurable (h.mean_integrable i j hij n)
  filter_upwards [ht, h.statistic_conditional_mean i j hij n] with ω ht hs
  change (μ[h.increment i j n | ℱ n]) ω =
    (μ[h.statistic i j n | ℱ n]) ω - (μ[h.predictableMean i j n | ℱ n]) ω at ht
  simpa only [hm, hs, sub_self] using ht

lemma statistic_conditional_second_le (i j : ι) (hij : i ≠ j) (n : ℕ) :
    μ[fun ω => (h.statistic i j n ω) ^ 2 | ℱ n] ≤ᵐ[μ]
      fun ω => (R + M + D) ^ 2 * h.information i j n ω := by
  have hsm : Measurable (h.score i j n) :=
    (h.score_measurable i j n).mono (h.action_le n) le_rfl
  have hwm : Measurable (h.statistic i j n) :=
    (h.statistic_measurable i j n).mono (ℱ.le (n + 1)) le_rfl
  have hSi := bounded_square_integrable (μ := μ) hsm
    (fun ω => h.scoreAt_bound i j n (h.action n ω) ω)
  have hWi := bounded_square_integrable (μ := μ) hwm (h.statistic_bound i j n)
  have hpoint (ω : Ω) : (h.statistic i j n ω) ^ 2 ≤
      (R + M + D) ^ 2 * (h.score i j n ω) ^ 2 := by
    have hH : 0 ≤ R + M + D := by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]
    have hy : (h.residual n ω) ^ 2 ≤ (R + M + D) ^ 2 := by
      simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) hH).2 (h.residual_bound n ω)
    dsimp [statistic]
    rw [mul_pow]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left hy (sq_nonneg (h.score i j n ω))
  have hmono := condExp_mono (m := ℱ n) hWi (hSi.const_mul ((R + M + D) ^ 2))
    (Eventually.of_forall hpoint)
  have hm := condExp_smul (μ := μ) ((R + M + D) ^ 2)
    (fun ω => (h.score i j n ω) ^ 2) (ℱ n)
  filter_upwards [hmono, hm, h.score_conditional_second i j hij n] with ω hl hm hs
  change (μ[fun ω => (R + M + D) ^ 2 * (h.score i j n ω) ^ 2 | ℱ n]) ω =
    (R + M + D) ^ 2 * (μ[fun ω => (h.score i j n ω) ^ 2 | ℱ n]) ω at hm
  simpa only [hm, hs] using hl

/-- The centered statistic's original-space variance bound is derived from
the categorical second moment and encoder amplitude, not a model field. -/
theorem increment_conditional_second_le (i j : ι) (hij : i ≠ j) (n : ℕ) :
    μ[fun ω => (h.increment i j n ω) ^ 2 | ℱ n] ≤ᵐ[μ]
      fun ω => (R + M + D) ^ 2 * h.information i j n ω := by
  have hwm : Measurable (h.statistic i j n) :=
    (h.statistic_measurable i j n).mono (ℱ.le (n + 1)) le_rfl
  have hmm : Measurable (h.predictableMean i j n) :=
    (h.mean_measurable i j n).mono (ℱ.le n) le_rfl
  have hWi := h.statistic_integrable i j n
  have hW2i := bounded_square_integrable (μ := μ) hwm (h.statistic_bound i j n)
  have hb2i := bounded_square_integrable (μ := μ) hmm (h.mean_bound i j hij n)
  have hbWi := hWi.bdd_mul' hmm.stronglyMeasurable.aestronglyMeasurable
    (Eventually.of_forall fun ω => by
      simpa only [Real.norm_eq_abs] using h.mean_bound i j hij n ω)
  exact (centered_square_le (ℱ.le n) (h.mean_measurable i j n).stronglyMeasurable
    hWi hW2i hbWi hb2i (h.statistic_conditional_mean i j hij n)).trans
      (h.statistic_conditional_second_le i j hij n)

/-- The full Bernstein interface is instantiated entirely from original
sampling and encoder assumptions. -/
theorem bernstein_data (i j : ι) (hij : i ≠ j) :
    Bernstein.BoundedIncrements ℱ μ (h.increment i j)
      (fun n ω => (R + M + D) ^ 2 * h.information i j n ω) (2 * (R + M + D)) := by
  refine ⟨by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg],
    fun n => (h.increment_measurable i j n).stronglyMeasurable,
    fun n => ((h.information_measurable i j n).const_mul _).stronglyMeasurable,
    h.increment_bound i j hij, ?_, h.increment_conditional_zero i j hij,
    h.increment_conditional_second_le i j hij⟩
  intro n ω
  exact mul_nonneg (sq_nonneg _) (h.information_bounds i j hij n ω).1

noncomputable def regularizedInformation (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  1 + Bernstein.sumProcess (h.information i j) n ω

noncomputable def estimate (i j : ι) (n : ℕ) (ω : Ω) : ℝ :=
  clip R (Bernstein.sumProcess (h.statistic i j) n ω / h.regularizedInformation i j n ω)

noncomputable def fluctuationRadius (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  2 * (R + M + D) * Real.sqrt (h.regularizedInformation i j n ω * L) +
    (4 / 3) * (R + M + D) * L

noncomputable def rawRadius (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  (R + h.fluctuationRadius i j n L ω) / h.regularizedInformation i j n ω

noncomputable def lower (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  max (-R) (h.estimate i j n ω - h.rawRadius i j n L ω)

noncomputable def upper (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  min R (h.estimate i j n ω + h.rawRadius i j n L ω)

noncomputable def midpoint (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  (h.lower i j n L ω + h.upper i j n L ω) / 2

noncomputable def radius (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  (h.upper i j n L ω - h.lower i j n L ω) / 2

def Coverage (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : Prop :=
  |h.estimate i j n ω - (θ i - θ j)| ≤ min (2 * R) (h.rawRadius i j n L ω) ∧
  |(θ i - θ j) - h.midpoint i j n L ω| ≤ h.radius i j n L ω ∧
  0 ≤ h.radius i j n L ω ∧ h.radius i j n L ω ≤ min R (h.rawRadius i j n L ω)

lemma regularizedInformation_pos (i j : ι) (hij : i ≠ j) (n : ℕ) (ω : Ω) :
    0 < h.regularizedInformation i j n ω := by
  have hv : 0 ≤ Bernstein.sumProcess (h.information i j) n ω :=
    Finset.sum_nonneg fun k _ => (h.information_bounds i j hij k ω).1
  dsimp [regularizedInformation]
  linarith

lemma rawRadius_nonneg (i j : ι) (hij : i ≠ j) (n : ℕ) {L : ℝ} (hL : 0 ≤ L) (ω : Ω) :
    0 ≤ h.rawRadius i j n L ω := by
  have hH : 0 ≤ R + M + D := by linarith [h.R_nonneg, h.M_nonneg, h.D_nonneg]
  have hR := h.R_nonneg
  dsimp [rawRadius, fluctuationRadius]
  apply div_nonneg _ (h.regularizedInformation_pos i j hij n ω).le
  positivity

lemma ridge_identity (i j : ι) (n : ℕ) (ω : Ω) :
    Bernstein.sumProcess (h.statistic i j) n ω - (θ i - θ j) * h.regularizedInformation i j n ω =
      Bernstein.sumProcess (h.increment i j) n ω - (θ i - θ j) := by
  simp only [Bernstein.sumProcess, increment, predictableMean, regularizedInformation,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

/-- Deterministic ridge bias, clipping, and intersection of the confidence
interval. This simultaneously supplies C3 and the M5/M6 midpoint-radius form. -/
theorem coverage_of_fluctuation (i j : ι) (hij : i ≠ j) (n : ℕ) {L : ℝ} (hL : 0 ≤ L)
    (ω : Ω) (hdev : |Bernstein.sumProcess (h.increment i j) n ω| ≤ h.fluctuationRadius i j n L ω) :
    h.Coverage i j n L ω := by
  let g := θ i - θ j
  let V := h.regularizedInformation i j n ω
  let S := Bernstein.sumProcess (h.statistic i j) n ω
  have hV : 0 < V := h.regularizedInformation_pos i j hij n ω
  have hg : -R ≤ g ∧ g ≤ R := abs_le.mp (h.gap_bound i j)
  have hcenter : |S - g * V| ≤ R + h.fluctuationRadius i j n L ω := by
    change |Bernstein.sumProcess (h.statistic i j) n ω - (θ i - θ j) *
      h.regularizedInformation i j n ω| ≤ _
    rw [h.ridge_identity]
    exact (abs_sub _ _).trans (by linarith [h.gap_bound i j])
  have hraw : |S / V - g| ≤ h.rawRadius i j n L ω := by
    have heq : S / V - g = (S - g * V) / V := by field_simp
    rw [heq, abs_div, abs_of_pos hV]
    exact div_le_div_of_nonneg_right hcenter hV.le
  have hclip : |h.estimate i j n ω - g| ≤ h.rawRadius i j n L ω :=
    clip_contract hg |>.trans hraw
  have hcliprange := clip_range (x := S / V) h.R_nonneg
  change -R ≤ h.estimate i j n ω ∧ h.estimate i j n ω ≤ R at hcliprange
  have hshort : |h.estimate i j n ω - g| ≤ 2 * R := by
    rw [abs_le]
    constructor <;> linarith [hcliprange.1, hcliprange.2, hg.1, hg.2]
  have hmid := Pairwise.clipped_midpoint_radius R (h.estimate i j n ω)
    (h.rawRadius i j n L ω) g hcliprange (h.rawRadius_nonneg i j hij n hL ω) hg
    (by simpa only [abs_sub_comm] using hclip)
  exact ⟨le_min hshort hclip, hmid.1, hmid.2.1, le_min hmid.2.2.1 hmid.2.2.2⟩

/-- R=0 is deterministically covered without dividing by H or applying a
positive-scale concentration theorem. In particular this covers H=0. -/
theorem coverage_zero_range (hR : R = 0) (i j : ι) (hij : i ≠ j) (n : ℕ)
    {L : ℝ} (hL : 0 ≤ L) (ω : Ω) : h.Coverage i j n L ω := by
  have hg : θ i - θ j = 0 := by
    have hb := h.gap_bound i j
    rw [hR] at hb
    exact abs_nonpos_iff.mp hb
  have hcRange := clip_range
    (x := Bernstein.sumProcess (h.statistic i j) n ω / h.regularizedInformation i j n ω) h.R_nonneg
  change -R ≤ h.estimate i j n ω ∧ h.estimate i j n ω ≤ R at hcRange
  have hc : h.estimate i j n ω = 0 := by linarith [hcRange.1, hcRange.2]
  have hrho := h.rawRadius_nonneg i j hij n hL ω
  have hl : h.lower i j n L ω = 0 := by
    dsimp [lower]
    have hnegR : -R = 0 := by linarith
    rw [hc, hnegR]
    exact max_eq_left (by linarith)
  have hu : h.upper i j n L ω = 0 := by
    dsimp [upper]
    rw [hc]
    exact (min_eq_left (by linarith)).trans hR
  dsimp [Coverage, midpoint, radius]
  rw [hc, hg, hl, hu]
  simp only [zero_sub, sub_zero, add_zero, zero_div, abs_zero]
  exact ⟨le_min (by linarith [h.R_nonneg]) hrho, le_refl 0, le_refl 0, le_min h.R_nonneg hrho⟩

/-- Full original-space C3/M6 confidence statement for a finite collection of
distinct arm pairs. All pair conditional moments are derived above from the
categorical and encoder laws. Empty collections and zero private range are
handled, rather than excluded by a positive-cardinality/positive-H premise. -/
theorem confidence_family {κ : Type*} [Fintype κ] (pairs : κ → ι × ι)
    (hpairs : ∀ a, (pairs a).1 ≠ (pairs a).2) (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := confidenceLog (Fintype.card κ) T δ
    μ.real {ω | ∃ a, ∃ n ≤ T, ¬h.Coverage (pairs a).1 (pairs a).2 n L ω} ≤ δ / 4 := by
  let L := confidenceLog (Fintype.card κ) T δ
  change μ.real {ω | ∃ a, ∃ n ≤ T, ¬h.Coverage (pairs a).1 (pairs a).2 n L ω} ≤ δ / 4
  by_cases hc : Fintype.card κ = 0
  · letI : IsEmpty κ := Fintype.card_eq_zero_iff.mp hc
    have he : {ω | ∃ a, ∃ n ≤ T, ¬h.Coverage (pairs a).1 (pairs a).2 n L ω} = ∅ := by
      ext ω
      simp
    rw [he]
    simp only [measureReal_empty]
    positivity
  have hcard : 0 < Fintype.card κ := Nat.pos_of_ne_zero hc
  have hL : 0 < L := confidenceLog_pos hcard hδ hδ1
  by_cases hR : R = 0
  · have he : {ω | ∃ a, ∃ n ≤ T, ¬h.Coverage (pairs a).1 (pairs a).2 n L ω} = ∅ := by
      ext ω
      constructor
      · rintro ⟨a, n, hn, hbad⟩
        exact False.elim (hbad (h.coverage_zero_range hR _ _ (hpairs a) n hL.le ω))
      · simp
    rw [he]
    simp only [measureReal_empty]
    positivity
  have hH : 0 < R + M + D := by
    have hRp : 0 < R := lt_of_le_of_ne h.R_nonneg (Ne.symm hR)
    linarith [h.M_nonneg, h.D_nonneg]
  let E : Set Ω := {ω | ∃ a, ∃ n ≤ T,
    h.fluctuationRadius (pairs a).1 (pairs a).2 n L ω ≤
      |Bernstein.sumProcess (h.increment (pairs a).1 (pairs a).2) n ω|}
  have htail : μ.real E ≤ δ / 4 := Bernstein.paper_confidence hcard hH
    (fun a => h.increment (pairs a).1 (pairs a).2)
    (fun a => h.information (pairs a).1 (pairs a).2)
    (fun a => h.bernstein_data _ _ (hpairs a))
    (fun a n ω => by linarith [(h.information_bounds _ _ (hpairs a) n ω).2]) T hδ hδ1
  have hsub : {ω | ∃ a, ∃ n ≤ T, ¬h.Coverage (pairs a).1 (pairs a).2 n L ω} ⊆ E := by
    intro ω hbad
    obtain ⟨a, n, hn, hbad⟩ := hbad
    refine ⟨a, n, hn, ?_⟩
    by_contra ht
    exact hbad (h.coverage_of_fluctuation _ _ (hpairs a) n hL.le ω (not_le.mp ht).le)
  exact (measureReal_mono hsub).trans htail

/-- All unordered arm pairs, including the K=1/empty-pair case. The logarithm
uses exactly the cardinality of the upper-triangular pair type. -/
theorem uniform_confidence [LinearOrder ι] (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := confidenceLog (Fintype.card {ij : ι × ι // ij.1 < ij.2}) T δ
    μ.real {ω | ∃ i j, i < j ∧ ∃ n ≤ T, ¬h.Coverage i j n L ω} ≤ δ / 4 := by
  let κ := {ij : ι × ι // ij.1 < ij.2}
  have hfamily := h.confidence_family (κ := κ) (fun a => a.val) (fun a => ne_of_lt a.property) T hδ hδ1
  apply (measureReal_mono (μ := μ) ?_).trans hfamily
  intro ω hbad
  obtain ⟨i, j, hij, n, hn, hbad⟩ := hbad
  exact ⟨⟨(i, j), hij⟩, n, hn, hbad⟩

/-- The C3 clipped-estimator statement for one pair, with exactly the
single-process logarithm and capped radius min(2R,rho). -/
theorem single_pair_confidence (i j : ι) (hij : i ≠ j) (T : ℕ)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := confidenceLog 1 T δ
    μ.real {ω | ∃ n ≤ T,
      ¬(|h.estimate i j n ω - (θ i - θ j)| ≤ min (2 * R) (h.rawRadius i j n L ω))} ≤ δ / 4 := by
  have hf := h.confidence_family (κ := Unit) (fun _ => (i, j)) (fun _ => hij) T hδ hδ1
  simp only [Fintype.card_unit] at hf
  apply (measureReal_mono (μ := μ) ?_).trans hf
  intro ω hbad
  obtain ⟨n, hn, hbad⟩ := hbad
  exact ⟨(), n, hn, fun hc => hbad hc.1⟩

section Directed

variable [LinearOrder ι]

/-- Exactly the paper's extension from upper-triangular confidence intervals:
reverse centers change sign, reverse radii are copied, and diagonals are zero. -/
noncomputable def directedMidpoint (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  if i < j then h.midpoint i j n L ω else if j < i then -h.midpoint j i n L ω else 0

noncomputable def directedRadius (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  if i < j then h.radius i j n L ω else if j < i then h.radius j i n L ω else 0

noncomputable def directedRawRadius (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : ℝ :=
  if i < j then h.rawRadius i j n L ω else if j < i then h.rawRadius j i n L ω else 0

def DirectedCoverage (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) : Prop :=
  |(θ i - θ j) - h.directedMidpoint i j n L ω| ≤ h.directedRadius i j n L ω ∧
  0 ≤ h.directedRadius i j n L ω ∧
  h.directedRadius i j n L ω ≤ min R (h.directedRawRadius i j n L ω)

lemma directedMidpoint_antisymmetric (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) :
    h.directedMidpoint i j n L ω = -h.directedMidpoint j i n L ω := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [directedMidpoint, hij, not_lt_of_gt hij]
  · subst j; simp [directedMidpoint]
  · simp [directedMidpoint, hij, not_lt_of_gt hij]

lemma directedRadius_symmetric (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) :
    h.directedRadius i j n L ω = h.directedRadius j i n L ω := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [directedRadius, hij, not_lt_of_gt hij]
  · subst j; simp [directedRadius]
  · simp [directedRadius, hij, not_lt_of_gt hij]

lemma directedRawRadius_symmetric (i j : ι) (n : ℕ) (L : ℝ) (ω : Ω) :
    h.directedRawRadius i j n L ω = h.directedRawRadius j i n L ω := by
  rcases lt_trichotomy i j with hij | hij | hij
  · simp [directedRawRadius, hij, not_lt_of_gt hij]
  · subst j; simp [directedRawRadius]
  · simp [directedRawRadius, hij, not_lt_of_gt hij]

lemma directed_coverage_forward (i j : ι) (hij : i < j) (n : ℕ) (L : ℝ) (ω : Ω)
    (hc : h.Coverage i j n L ω) : h.DirectedCoverage i j n L ω := by
  simpa only [DirectedCoverage, directedMidpoint, directedRadius, directedRawRadius,
    if_pos hij] using hc.2

lemma directed_coverage_reverse (i j : ι) (hji : j < i) (n : ℕ) (L : ℝ) (ω : Ω)
    (hc : h.Coverage j i n L ω) : h.DirectedCoverage i j n L ω := by
  have heq : (θ i - θ j) - -h.midpoint j i n L ω = -((θ j - θ i) - h.midpoint j i n L ω) := by ring
  simpa only [DirectedCoverage, directedMidpoint, directedRadius, directedRawRadius,
    if_neg (not_lt_of_gt hji), if_pos hji, heq, abs_neg] using hc.2

lemma directed_coverage_diagonal (i : ι) (n : ℕ) (L : ℝ) (ω : Ω) :
    h.DirectedCoverage i i n L ω := by
  simp [DirectedCoverage, directedMidpoint, directedRadius, directedRawRadius, h.R_nonneg]

/-- Full M6 statement for all ordered pairs. The log allocation is paid only
for K(K-1)/2 upper-triangular processes, with no second directional union. -/
theorem directed_confidence (T : ℕ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    let L := confidenceLog (Fintype.card ι * (Fintype.card ι - 1) / 2) T δ
    μ.real {ω | ∃ i j, ∃ n ≤ T, ¬h.DirectedCoverage i j n L ω} ≤ δ / 4 := by
  have hu := h.uniform_confidence T hδ hδ1
  rw [upper_pair_card] at hu
  apply (measureReal_mono (μ := μ) ?_).trans hu
  intro ω hbad
  obtain ⟨i, j, n, hn, hbad⟩ := hbad
  rcases lt_trichotomy i j with hij | hij | hij
  · exact ⟨i, j, hij, n, hn, fun hc => hbad (h.directed_coverage_forward i j hij n _ ω hc)⟩
  · subst j
    exact False.elim (hbad (h.directed_coverage_diagonal i n _ ω))
  · exact ⟨j, i, hij, n, hn, fun hc => hbad (h.directed_coverage_reverse i j hij n _ ω hc)⟩

end Directed

end SamplingModel

end Model

end Part2.PairConfidence

/- Kernel dependency audit for every proof declaration in this staging file. -/

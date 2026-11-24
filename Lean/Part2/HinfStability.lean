import Part2.HinfExpected
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-! The genuine one-dimensional Tsallis Taylor/stability bridge. -/
namespace Part2.HinfStability

open Finset Set
open Part2.HinfExpected

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Order-two Taylor's theorem on [0,1], proved by two actual applications of
Rolle's theorem. Derivative premises are instantiated below for the actual Fq. -/
theorem taylor_two (f f' f'' : ℝ → ℝ)
    (hf : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f (f' s) s)
    (hf' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt f' (f'' s) s) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, f 1 - f 0 - f' 0 = f'' θ / 2 := by
  let D : ℝ := f 1 - f 0 - f' 0
  let h : ℝ → ℝ := fun s => f s - f 0 - f' 0 * s - D * s ^ 2
  let h' : ℝ → ℝ := fun s => f' s - f' 0 - 2 * D * s
  have hh : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt h (h' s) s := by
    intro s hs
    convert (((hf s hs).sub_const (f 0)).sub
      ((hasDerivAt_id s).const_mul (f' 0))).sub
      (((hasDerivAt_id s).pow 2).const_mul D) using 1 <;> dsimp [h, h'] <;> ring
  have hh' : ∀ s ∈ Icc (0 : ℝ) 1, HasDerivAt h' (f'' s - 2 * D) s := by
    intro s hs
    convert ((hf' s hs).sub_const (f' 0)).sub
      ((hasDerivAt_id s).const_mul (2 * D)) using 1 <;> dsimp [h'] <;> ring
  have hcont : ContinuousOn h (Icc (0 : ℝ) 1) :=
    fun s hs => (hh s hs).continuousAt.continuousWithinAt
  have hend : h 0 = h 1 := by dsimp [h, D]; ring
  obtain ⟨c, hc, hcz⟩ := exists_hasDerivAt_eq_zero zero_lt_one hcont hend
    (fun s hs => hh s ⟨hs.1.le, hs.2.le⟩)
  have hcont' : ContinuousOn h' (Icc (0 : ℝ) c) := by
    intro s hs
    exact (hh' s ⟨hs.1, hs.2.trans hc.2.le⟩).continuousAt.continuousWithinAt
  have hends : h' 0 = h' c := by rw [hcz]; dsimp [h']; ring
  obtain ⟨θ, hθ, hθz⟩ := exists_hasDerivAt_eq_zero hc.1 hcont' hends
    (fun s hs => hh' s ⟨hs.1.le, hs.2.le.trans hc.2.le⟩)
  refine ⟨θ, ⟨hθ.1, hθ.2.trans hc.2⟩, ?_⟩
  dsimp [D] at hθz
  linarith

noncomputable def segment (p p' : ι → ℝ) (s : ℝ) (i : ι) : ℝ :=
  (1 - s) * p i + s * p' i

theorem segment_positive (p p' : ι → ℝ) (hp : ∀ i, 0 < p i)
    (hp' : ∀ i, 0 < p' i) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) (i : ι) :
    0 < segment p p' s i := by
  unfold segment
  have h1 : 0 ≤ (1 - s) * p i := mul_nonneg (by linarith [hs.2]) (hp i).le
  have h2 : 0 ≤ s * p' i := mul_nonneg hs.1 (hp' i).le
  by_cases hzero : s = 0
  · simpa [hzero] using hp i
  · exact add_pos_of_nonneg_of_pos h1 (mul_pos (lt_of_le_of_ne hs.1 (Ne.symm hzero)) (hp' i))

theorem segment_hasDerivAt (p p' : ι → ℝ) (s : ℝ) (i : ι) :
    HasDerivAt (fun t => segment p p' t i) (p' i - p i) s := by
  convert (((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).mul_const (p i)).add
    ((hasDerivAt_id s).mul_const (p' i)) using 1 <;> dsimp [segment] <;> ring

noncomputable def pathValue (q : ℝ) (p p' : ι → ℝ) (s : ℝ) : ℝ :=
  tsallis q (segment p p' s)

noncomputable def pathSlope (q : ℝ) (p p' : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ i, -(segment p p' s i ^ (-1 / q)) * (p' i - p i)

noncomputable def pathCurvature (q : ℝ) (p p' : ι → ℝ) (s : ℝ) : ℝ :=
  ∑ i, (1 / q) * (segment p p' s i ^ (-1 - 1 / q)) * (p' i - p i) ^ 2

/-- The actual first derivative of the Tsallis potential along a segment. -/
theorem pathValue_hasDerivAt (q : ℝ) (p p' : ι → ℝ) (hq : 1 < q)
    (hp : ∀ i, 0 < p i) (hp' : ∀ i, 0 < p' i)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (pathValue q p p') (pathSlope q p p' s) s := by
  have hα : 1 - 1 / q ≠ 0 := by
    have hq0 : 0 < q := by linarith
    have hh := (div_lt_one hq0).2 hq
    linarith
  apply HasDerivAt.congr_deriv (f' := ∑ i,
    -((p' i - p i) * (1 - 1 / q) *
      (segment p p' s i) ^ ((1 - 1 / q) - 1)) / (1 - 1 / q))
  · simpa only [pathValue, tsallis, Finset.sum_apply] using
      (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        (((segment_hasDerivAt p p' s i).rpow_const (p := 1 - 1 / q)
          (Or.inl (segment_positive p p' hp hp' s hs i).ne')).neg.div_const (1 - 1 / q)))
  · unfold pathSlope
    apply Finset.sum_congr rfl
    intro i _
    rw [show (1 - 1 / q) - 1 = -1 / q by ring]
    apply (div_eq_iff hα).2
    ring

/-- The actual second derivative; the diagonal Hessian is computed here rather
than supplied as an assumption. -/
theorem pathSlope_hasDerivAt (q : ℝ) (p p' : ι → ℝ)
    (hp : ∀ i, 0 < p i) (hp' : ∀ i, 0 < p' i)
    (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
    HasDerivAt (pathSlope q p p') (pathCurvature q p p' s) s := by
  apply HasDerivAt.congr_deriv (f' := ∑ i,
    -((p' i - p i) * (-1 / q) *
      (segment p p' s i) ^ ((-1 / q) - 1)) * (p' i - p i))
  · simpa only [pathSlope, Finset.sum_apply] using
      (HasDerivAt.fun_sum (u := Finset.univ) fun i _ =>
        (((segment_hasDerivAt p p' s i).rpow_const (p := -1 / q)
          (Or.inl (segment_positive p p' hp hp' s hs i).ne')).neg.mul_const (p' i - p i)))
  · unfold pathCurvature
    apply Finset.sum_congr rfl
    intro i _
    rw [show (-1 / q) - 1 = -1 - 1 / q by ring]
    ring

/-- A single genuine segment point realizes the complete Bregman quadratic
remainder. The same theta is used in every coordinate. -/
theorem bregman_taylor (q : ℝ) (p p' : ι → ℝ) (hq : 1 < q)
    (hp : ∀ i, 0 < p i) (hp' : ∀ i, 0 < p' i) :
    ∃ θ ∈ Ioo (0 : ℝ) 1, bregman q p' p = pathCurvature q p p' θ / 2 := by
  obtain ⟨θ, hθ, ht⟩ := taylor_two (pathValue q p p') (pathSlope q p p')
    (pathCurvature q p p')
    (pathValue_hasDerivAt q p p' hq hp hp')
    (pathSlope_hasDerivAt q p p' hp hp')
  refine ⟨θ, hθ, ?_⟩
  have hs0 : segment p p' 0 = p := by funext i; simp [segment]
  have hs1 : segment p p' 1 = p' := by funext i; simp [segment]
  simpa only [pathValue, pathSlope, hs0, hs1, bregman, dot,
    neg_mul, Finset.sum_neg_distrib, sub_neg_eq_add] using ht

/-- Exact weighted completion of squares; the numerical factor 1/2 is retained. -/
theorem quadratic_young (η w g h : ℝ) (hη : 0 < η) (hw : 0 < w) :
    -g * h - w * h ^ 2 / (2 * η) ≤ η * g ^ 2 / (2 * w) := by
  apply (le_div_iff₀ (by linarith : 0 < 2 * w)).2
  apply (mul_le_mul_right hη).mp
  calc
    (-g * h - w * h ^ 2 / (2 * η)) * (2 * w) * η =
        η ^ 2 * g ^ 2 - (w * h + η * g) ^ 2 := by
      field_simp
      <;> ring
    _ ≤ (η * g ^ 2) * η := by nlinarith [sq_nonneg (w * h + η * g)]

/-- Inverting the actual diagonal curvature gives q*z^(1+1/q), with no
matrix/Hessian equation supplied as a premise. -/
theorem inverse_curvature (q z : ℝ) (hq : 0 < q) (hz : 0 < z) :
    1 / ((1 / q) * z ^ (-1 - 1 / q)) = q * z ^ (1 + 1 / q) := by
  have hm : z ^ (-1 - 1 / q) * z ^ (1 + 1 / q) = 1 := by
    rw [← Real.rpow_add hz]
    rw [show (-1 - 1 / q) + (1 + 1 / q) = 0 by ring, Real.rpow_zero]
  apply (div_eq_iff (mul_ne_zero (one_div_ne_zero hq.ne')
    (Real.rpow_pos_of_pos hz (-1 - 1 / q)).ne')).2
  have hqinv : (1 / q) * q = 1 := one_div_mul_cancel hq.ne'
  calc
    1 = ((1 / q) * q) * (z ^ (-1 - 1 / q) * z ^ (1 + 1 / q)) := by rw [hqinv, hm]; norm_num
    _ = _ := by ring

/-- The complete genuine Taylor-to-stability bridge for arbitrary interior
points and arbitrary loss vectors. No curvature or stability bound is assumed. -/
theorem stability_le_segment_norm (q η : ℝ) (g p p' : ι → ℝ)
    (hq : 1 < q) (hη : 0 < η) (hp : ∀ i, 0 < p i) (hp' : ∀ i, 0 < p' i) :
    ∃ θ ∈ Ioo (0 : ℝ) 1,
      dot g (fun i => p i - p' i) - bregman q p' p / η ≤
        (η / 2) * (q * ∑ i, (segment p p' θ i) ^ (1 + 1 / q) * (g i) ^ 2) := by
  obtain ⟨θ, hθ, ht⟩ := bregman_taylor q p p' hq hp hp'
  refine ⟨θ, hθ, ?_⟩
  have hq0 : 0 < q := by linarith
  have hz (i : ι) : 0 < segment p p' θ i :=
    segment_positive p p' hp hp' θ ⟨hθ.1.le, hθ.2.le⟩ i
  have hterm (i : ι) :
      -(g i) * (p' i - p i) -
          ((1 / q) * (segment p p' θ i) ^ (-1 - 1 / q)) * (p' i - p i) ^ 2 / (2 * η) ≤
        (η / 2) * q * (segment p p' θ i) ^ (1 + 1 / q) * (g i) ^ 2 := by
    have hy := quadratic_young η ((1 / q) * (segment p p' θ i) ^ (-1 - 1 / q))
      (g i) (p' i - p i) hη
      (mul_pos (one_div_pos.mpr hq0) (Real.rpow_pos_of_pos (hz i) _))
    have hrhs : η * (g i) ^ 2 / (2 * ((1 / q) * (segment p p' θ i) ^ (-1 - 1 / q))) =
        (η / 2) * q * (segment p p' θ i) ^ (1 + 1 / q) * (g i) ^ 2 := by
      have hi := inverse_curvature q (segment p p' θ i) hq0 (hz i)
      calc
        _ = (η / 2) * (g i) ^ 2 * (1 / ((1 / q) * (segment p p' θ i) ^ (-1 - 1 / q))) := by ring
        _ = _ := by rw [hi]; ring
    exact hrhs ▸ hy
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hterm i
  rw [ht]
  unfold pathCurvature at hs ⊢
  simp only [Finset.sum_sub_distrib, ← Finset.sum_div] at hs
  have hrs : (∑ i, (η / 2) * q * (segment p p' θ i) ^ (1 + 1 / q) * (g i) ^ 2) =
      (η / 2) * (q * ∑ i, (segment p p' θ i) ^ (1 + 1 / q) * (g i) ^ 2) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hrs] at hs
  have hdot : dot g (fun i => p i - p' i) = ∑ i, -(g i) * (p' i - p i) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hdot]
  convert hs using 1 <;> ring

/-- Genuine analytic stability joined to the exact projection and the proved
composite current-point estimate, with the original constants. -/
theorem projection_composite_stability_le (q η B r : ℝ) (G p p' b : ι → ℝ)
    (x x' : ℝ) (a : ι) (hq : 1 < q) (hη : 0 < η) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hp : IsProjection q η G p x)
    (hp' : IsProjection q η (fun i => G i + composite b r a i) p' x')
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ B) :
    dot (composite b r a) (fun i => p i - p' i) - bregman q p' p / η ≤
      η * q * (2 * B ^ 2 + (p a) ^ (1 + 1 / q) * r ^ 2) := by
  have hp0 (i : ι) : 0 < p i := by rw [hp.2.1 i]; exact Real.rpow_pos_of_pos (hp.1 i) _
  have hp'0 (i : ι) : 0 < p' i := by rw [hp'.2.1 i]; exact Real.rpow_pos_of_pos (hp'.1 i) _
  obtain ⟨θ, hθ, hstab⟩ := stability_le_segment_norm q η (composite b r a) p p' hq hη hp0 hp'0
  have hnorm := projection_composite_norm_le q η B r G p p' (segment p p' θ) b
    x x' θ a hq hη hB hr hp hp' ⟨hθ.1.le, hθ.2.le⟩ (fun _ => rfl) hb
  exact hstab.trans (by nlinarith [mul_le_mul_of_nonneg_left hnorm (by linarith : 0 ≤ η / 2)])

/-- A common base shift changes only the normalizing multiplier of the exact
next projection. This is the actual projection identity used for span bounds. -/
theorem projection_center_base (q η m r : ℝ) (G p' b : ι → ℝ) (x' : ℝ) (a : ι)
    (hp' : IsProjection q η (fun i => G i + composite b r a i) p' x') :
    IsProjection q η (fun i => G i + composite (fun i => b i - m) r a i) p' (x' + m) := by
  have he (i : ι) : η * (G i + composite (fun i => b i - m) r a i + (x' + m)) =
      η * (G i + composite b r a i + x') := by unfold composite; ring
  refine ⟨?_, ?_, hp'.2.2⟩
  · intro i
    rw [he i]
    exact hp'.1 i
  · intro i
    rw [he i]
    exact hp'.2.1 i

/-- Common public shifts cancel from the simplex linear stability term. -/
theorem dot_center_base (m r : ℝ) (p p' b : ι → ℝ) (a : ι)
    (hp : ∑ i, p i = 1) (hp' : ∑ i, p' i = 1) :
    dot (composite b r a) (fun i => p i - p' i) =
      dot (composite (fun i => b i - m) r a) (fun i => p i - p' i) := by
  have he (i : ι) : composite (fun i => b i - m) r a i = composite b r a i - m := by
    unfold composite
    ring
  simp_rw [dot, he, sub_mul, mul_sub, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hp, hp']
  ring

/-- Span-sensitive one-step stability on the original uncentered fed loss.
Both the original exact projection and its Bregman stability are retained. -/
theorem projection_span_stability_le (q η B m r : ℝ) (G p p' b : ι → ℝ)
    (x x' : ℝ) (a : ι) (hq : 1 < q) (hη : 0 < η) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hp : IsProjection q η G p x)
    (hp' : IsProjection q η (fun i => G i + composite b r a i) p' x')
    (hb : ∀ i, m ≤ b i ∧ b i ≤ m + B) :
    dot (composite b r a) (fun i => p i - p' i) - bregman q p' p / η ≤
      η * q * (2 * B ^ 2 + (p a) ^ (1 + 1 / q) * r ^ 2) := by
  rw [dot_center_base m r p p' b a hp.2.2 hp'.2.2]
  exact projection_composite_stability_le q η B r G p p' (fun i => b i - m)
    x (x' + m) a hq hη hB hr hp (projection_center_base q η m r G p' b x' a hp')
    (fun i => ⟨by linarith [(hb i).1], by linarith [(hb i).2]⟩)

/-- Complete deterministic H-INF FTRL bound with actual raw IW feedback,
arbitrary real q>1, the original constants, and public-base spans.
This theorem supplies the remaining deterministic input to the probability
proof; no regret, curvature, or stability inequality occurs in its premises. -/
theorem ftrl_hybrid_regret_le_span (q η : ℝ) (L p b ρ : ℕ → ι → ℝ)
    (x B m : ℕ → ℝ) (A : ℕ → ι) (hq : 1 < q) (hη : 0 < η)
    (hproj : ∀ t, IsProjection q η (cumulative L t) (p t) (x t))
    (hL : ∀ t i, L t i = composite (b t) (ρ t (A t) / p t (A t)) (A t) i)
    (hB : ∀ t, 0 ≤ B t) (hρ : ∀ t i, 0 ≤ ρ t i)
    (hb : ∀ t i, m t ≤ b t i ∧ b t i ≤ m t + B t)
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1) (T : ℕ) :
    (∑ t ∈ Finset.range T, dot (L t) (fun i => p t i - u i)) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        q * η * ∑ t ∈ Finset.range T, (2 * (B t) ^ 2 + residualMoment q (p t) (ρ t) (A t)) := by
  have hstep (t : ℕ) : stability q η L p t ≤
      q * η * (2 * (B t) ^ 2 + residualMoment q (p t) (ρ t) (A t)) := by
    have hp0 (i : ι) : 0 < p t i := by
      rw [(hproj t).2.1 i]
      exact Real.rpow_pos_of_pos ((hproj t).1 i) _
    have hcum : cumulative L (t + 1) =
        fun i => cumulative L t i + composite (b t) (ρ t (A t) / p t (A t)) (A t) i := by
      funext i
      simp only [cumulative, Finset.sum_range_succ, hL]
    have hn : IsProjection q η
        (fun i => cumulative L t i + composite (b t) (ρ t (A t) / p t (A t)) (A t) i)
        (p (t + 1)) (x (t + 1)) := by rw [← hcum]; exact hproj (t + 1)
    have hst := projection_span_stability_le q η (B t) (m t) (ρ t (A t) / p t (A t))
      (cumulative L t) (p t) (p (t + 1)) (b t) (x t) (x (t + 1)) (A t)
      hq hη (hB t) (div_nonneg (hρ t (A t)) (hp0 (A t)).le) (hproj t) hn (hb t)
    have hLt : L t = composite (b t) (ρ t (A t) / p t (A t)) (A t) := funext (hL t)
    simpa only [stability, hLt, residualMoment, mul_comm η q] using hst
  have hs := Finset.sum_le_sum fun t (_ : t ∈ Finset.range T) => hstep t
  rw [← Finset.mul_sum] at hs
  exact (ftrl_regret_le_range q η L p x hq hη hproj u hu hsu T).trans (add_le_add_left hs _)

end Part2.HinfStability

-- Explicit kernel-dependency queries for this staging proof package.
#print axioms Part2.HinfStability.taylor_two
#print axioms Part2.HinfStability.segment_positive
#print axioms Part2.HinfStability.segment_hasDerivAt
#print axioms Part2.HinfStability.pathValue_hasDerivAt
#print axioms Part2.HinfStability.pathSlope_hasDerivAt
#print axioms Part2.HinfStability.bregman_taylor
#print axioms Part2.HinfStability.quadratic_young
#print axioms Part2.HinfStability.inverse_curvature
#print axioms Part2.HinfStability.stability_le_segment_norm
#print axioms Part2.HinfStability.projection_composite_stability_le
#print axioms Part2.HinfStability.projection_center_base
#print axioms Part2.HinfStability.dot_center_base
#print axioms Part2.HinfStability.projection_span_stability_le
#print axioms Part2.HinfStability.ftrl_hybrid_regret_le_span

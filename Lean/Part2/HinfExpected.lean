import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact INF projection and the composite local norm

The declarations below derive the actual Tsallis objective minimization and
the full deterministic FTRL regret inequality, prove H2'' and the explicit
composite sum in H2', and prove the finite categorical content of H3 for every
q > 1. They do not assert the complete expected-regret theorem. The genuine
Hessian/Taylor-to-stability bridge and conditional sampling remain separate
obligations; they are not replaced by assumptions carrying their conclusions.
-/
namespace Part2.HinfExpected

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exact power projection, with its normalizing multiplier supplied explicitly.
The domain condition is essential for negative real powers. -/
def IsProjection (q η : ℝ) (G p : ι → ℝ) (x : ℝ) : Prop :=
  (∀ i, 0 < η * (G i + x)) ∧
  (∀ i, p i = (η * (G i + x)) ^ (-q)) ∧ ∑ i, p i = 1

/-- Canonical H2'': the coordinate receiving a maximal increment cannot gain
probability. No existence or uniqueness of the projection is presumed proved. -/
theorem projection_max_increment (q η : ℝ) (G v p p' : ι → ℝ) (x x' : ℝ)
    (hq : 0 < q) (hη : 0 < η)
    (hp : IsProjection q η G p x)
    (hp' : IsProjection q η (fun i => G i + v i) p' x')
    (a : ι) (hmax : ∀ i, v i ≤ v a) : p' a ≤ p a := by
  by_contra hn
  have ha : p a < p' a := lt_of_not_ge hn
  rw [hp.2.1 a, hp'.2.1 a] at ha
  have harg := (Real.rpow_lt_rpow_iff_of_neg (hp.1 a) (hp'.1 a) (neg_neg_of_pos hq)).1 ha
  have hx : x' - x < -v a := by nlinarith
  have hall : ∀ i, p i < p' i := by
    intro i
    rw [hp.2.1 i, hp'.2.1 i]
    exact Real.rpow_lt_rpow_of_neg (hp'.1 i)
      (by nlinarith [hmax i]) (neg_neg_of_pos hq)
  have hs : ∑ i, p i < ∑ i, p' i :=
    Finset.sum_lt_sum (fun i _ => (hall i).le) ⟨a, Finset.mem_univ a, hall a⟩
  rw [hp.2.2, hp'.2.2] at hs
  exact (lt_irrefl (1 : ℝ)) hs

/-- A coordinate of a probability vector lies in [0,1]. -/
theorem coordinate_le_one (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i)
    (hs : ∑ i, p i = 1) (a : ι) : p a ≤ 1 := by
  rw [← hs]
  exact Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ a)

/-- The elementary power inequality used for the base at any simplex point. -/
theorem coordinate_rpow_le (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (r : ℝ) (hr : 1 ≤ r) : z ^ r ≤ z := by
  rcases eq_or_lt_of_le hz with hzero | hpos
  · subst z
    rw [Real.zero_rpow (by linarith : r ≠ 0)]
  · simpa using Real.rpow_le_rpow_of_exponent_ge hpos hz1 hr

/-- Composite fed vector after a common baseline has been removed. -/
def composite (b : ι → ℝ) (r : ℝ) (a j : ι) : ℝ :=
  b j + if j = a then r else 0

/-- H2' in the span-sensitive form used by v3 A.1.  The hypothesis `hmove`
is exactly the maximal-increment coordinate monotonicity, established for the
actual INF projection by `projection_composite_norm_le` below. -/
theorem composite_norm_le (q B r : ℝ) (p z b : ι → ℝ) (a : ι)
    (hq : 1 < q) (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hp : ∀ i, 0 ≤ p i) (hz : ∀ i, 0 ≤ z i)
    (hsz : ∑ i, z i = 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ B)
    (hmove : B ≤ r → z a ≤ p a) :
    q * ∑ i, (z i) ^ (1 + 1 / q) * (composite b r a i) ^ 2 ≤
      4 * q * B ^ 2 + 2 * q * (p a) ^ (1 + 1 / q) * r ^ 2 := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have he : 1 ≤ 1 + 1 / q := by linarith [one_div_pos.mpr hq0]
  have hzi (i : ι) : (z i) ^ (1 + 1 / q) ≤ z i :=
    coordinate_rpow_le _ (hz i) (coordinate_le_one z hz hsz i) _ he
  have hbase : ∑ i, (z i) ^ (1 + 1 / q) * (b i) ^ 2 ≤ B ^ 2 := by
    calc
      _ ≤ ∑ i, z i * B ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul (hzi i) (by nlinarith [hb i])
          (sq_nonneg _) (hz i)
      _ = B ^ 2 := by rw [← Finset.sum_mul, hsz, one_mul]
  have hres : (z a) ^ (1 + 1 / q) * r ^ 2 ≤
      (p a) ^ (1 + 1 / q) * r ^ 2 + B ^ 2 := by
    by_cases hlarge : B ≤ r
    · have hpow := Real.rpow_le_rpow (hz a) (hmove hlarge) (by linarith : 0 ≤ 1 + 1 / q)
      nlinarith [mul_le_mul_of_nonneg_right hpow (sq_nonneg r), sq_nonneg B]
    · have hsmall : r ≤ B := (lt_of_not_ge hlarge).le
      have hpow : (z a) ^ (1 + 1 / q) ≤ 1 :=
        (hzi a).trans (coordinate_le_one z hz hsz a)
      have hterm : (z a) ^ (1 + 1 / q) * r ^ 2 ≤ B ^ 2 := by
        have hsq : r ^ 2 ≤ B ^ 2 := by nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hpow (sq_nonneg r)]
      nlinarith [mul_nonneg (Real.rpow_nonneg (hp a) (1 + 1 / q)) (sq_nonneg r)]
  have hsplit : ∑ i, (z i) ^ (1 + 1 / q) * (composite b r a i) ^ 2 ≤
      2 * (∑ i, (z i) ^ (1 + 1 / q) * (b i) ^ 2) +
        2 * (z a) ^ (1 + 1 / q) * r ^ 2 := by
    calc
      _ ≤ ∑ i, (2 * (z i) ^ (1 + 1 / q) * (b i) ^ 2 +
          if i = a then 2 * (z a) ^ (1 + 1 / q) * r ^ 2 else 0) := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hia : i = a
        · subst i
          simp only [composite, ite_true]
          nlinarith [mul_nonneg (Real.rpow_nonneg (hz a) (1 + 1 / q))
            (sq_nonneg (b a - r))]
        · simp only [composite, if_neg hia, add_zero]
          nlinarith [mul_nonneg (Real.rpow_nonneg (hz i) (1 + 1 / q)) (sq_nonneg (b i))]
      _ = _ := by rw [Finset.sum_add_distrib]; simp [Finset.mul_sum, mul_assoc]
  have hm := mul_le_mul_of_nonneg_left hsplit hq0.le
  nlinarith

/-- Complete current-point reduction from exact INF projections. The point z
lies on the actual update segment, rather than being assumed close to p. -/
theorem projection_composite_norm_le (q η B r : ℝ) (G p p' z b : ι → ℝ)
    (x x' θ : ℝ) (a : ι) (hq : 1 < q) (hη : 0 < η)
    (hB : 0 ≤ B) (hr : 0 ≤ r)
    (hp : IsProjection q η G p x)
    (hp' : IsProjection q η (fun i => G i + composite b r a i) p' x')
    (hθ : 0 ≤ θ ∧ θ ≤ 1)
    (hz : ∀ i, z i = (1 - θ) * p i + θ * p' i)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ B) :
    q * ∑ i, (z i) ^ (1 + 1 / q) * (composite b r a i) ^ 2 ≤
      4 * q * B ^ 2 + 2 * q * (p a) ^ (1 + 1 / q) * r ^ 2 := by
  have hp0 (i : ι) : 0 ≤ p i := by rw [hp.2.1 i]; exact Real.rpow_nonneg (hp.1 i).le _
  have hp'0 (i : ι) : 0 ≤ p' i := by rw [hp'.2.1 i]; exact Real.rpow_nonneg (hp'.1 i).le _
  apply composite_norm_le q B r p z b a hq hB hr hp0
  · intro i
    rw [hz i]
    exact add_nonneg (mul_nonneg (by linarith [hθ.2]) (hp0 i))
      (mul_nonneg hθ.1 (hp'0 i))
  · simp only [hz, Finset.sum_add_distrib, ← Finset.mul_sum, hp.2.2, hp'.2.2]
    ring
  · exact hb
  · intro hlarge
    have hmax : ∀ i, composite b r a i ≤ composite b r a a := by
      intro i
      by_cases hia : i = a
      · subst i; exact le_rfl
      · simp only [composite, if_neg hia, ite_true, add_zero]
        linarith [hb i, hb a]
    have hpa := projection_max_increment q η G (composite b r a) p p' x x'
      (lt_trans zero_lt_one hq) hη hp hp' a hmax
    rw [hz a]
    nlinarith [mul_le_mul_of_nonneg_left hpa hθ.1]

/-- The exact dimension factor for all real q > 1, including the deployed q=3.
This is a probability-simplex consequence of Holder's inequality. -/
theorem sum_rpow_le_card (q : ℝ) (p : ι → ℝ) (hq : 1 < q)
    (hp : ∀ i, 0 ≤ p i) (hs : ∑ i, p i = 1) :
    ∑ i, (p i) ^ (1 / q) ≤ (Fintype.card ι : ℝ) ^ (1 - 1 / q) := by
  have hq0 : q ≠ 0 := ne_of_gt (lt_trans zero_lt_one hq)
  have hconj := Real.HolderConjugate.conjExponent hq
  have hpow (i : ι) : ((p i) ^ (1 / q)) ^ q = p i := by
    rw [← Real.rpow_mul (hp i), one_div_mul_cancel hq0, Real.rpow_one]
  have hc : 1 / Real.conjExponent q = 1 - 1 / q := by
    rw [Real.conjExponent]
    field_simp
    <;> ring
  have hh := Real.inner_le_Lp_mul_Lq_of_nonneg (s := Finset.univ)
    (f := fun i => (p i) ^ (1 / q)) (g := fun _i : ι => (1 : ℝ))
    hconj (fun i _ => Real.rpow_nonneg (hp i) _) (fun _ _ => zero_le_one)
  simpa only [mul_one, hpow, hs, Real.one_rpow, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul, mul_one, one_mul, hc] using hh

/-- The sampled raw-IW inverse-Hessian term; no IX denominator is introduced. -/
noncomputable def residualMoment (q : ℝ) (p ρ : ι → ℝ) (a : ι) : ℝ :=
  (p a) ^ (1 + 1 / q) * (ρ a / p a) ^ 2

/-- The full finite categorical identity in H3, with strictly positive sampling
weights and every would-be residual fixed before the draw. -/
theorem mean_residualMoment (q : ℝ) (p ρ : ι → ℝ)
    (hp : ∀ i, 0 < p i) :
    (∑ a, p a * residualMoment q p ρ a) =
      ∑ i, (p i) ^ (1 / q) * (ρ i) ^ 2 := by
  apply Finset.sum_congr rfl
  intro i _
  unfold residualMoment
  rw [Real.rpow_add (hp i), Real.rpow_one]
  field_simp [(hp i).ne']
  <;> ring

/-- Complete finite-categorical H3 moment bound for arbitrary real q > 1.
This is not labeled a conditional-expectation theorem. -/
theorem mean_residualMoment_le (q R : ℝ) (p ρ : ι → ℝ)
    (hq : 1 < q) (hp : ∀ i, 0 < p i) (hs : ∑ i, p i = 1)
    (hρ : ∀ i, 0 ≤ ρ i ∧ ρ i ≤ R) :
    (∑ a, p a * residualMoment q p ρ a) ≤
      R ^ 2 * (Fintype.card ι : ℝ) ^ (1 - 1 / q) := by
  rw [mean_residualMoment q p ρ hp]
  calc
    _ ≤ ∑ i, (p i) ^ (1 / q) * R ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left (by nlinarith [hρ i])
        (Real.rpow_nonneg (hp i).le _)
    _ = R ^ 2 * ∑ i, (p i) ^ (1 / q) := by rw [← Finset.sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (sum_rpow_le_card q p hq (fun i => (hp i).le) hs) (sq_nonneg R)

/-- The scalar convex supporting inequality for the actual Tsallis potential,
including boundary comparators u=0. -/
theorem tsallis_scalar_support (q p u : ℝ) (hq : 1 < q)
    (hp : 0 < p) (hu : 0 ≤ u) :
    -(p ^ (1 - 1 / q)) / (1 - 1 / q) -
      p ^ (-1 / q) * (u - p) ≤
      -(u ^ (1 - 1 / q)) / (1 - 1 / q) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hα : 0 < 1 - 1 / q := by
    have hh : 1 / q < 1 := (div_lt_one hq0).2 hq
    linarith
  have hα1 : 1 - 1 / q ≤ 1 := by linarith [one_div_pos.mpr hq0]
  have hratio : -1 ≤ u / p - 1 := by linarith [div_nonneg hu hp.le]
  have hber := rpow_one_add_le_one_add_mul_self hratio hα.le hα1
  rw [add_sub_cancel] at hber
  have hfactor : p ^ (1 - 1 / q) = p * p ^ (-1 / q) := by
    rw [show 1 - 1 / q = 1 + (-1 / q) by ring, Real.rpow_add hp, Real.rpow_one]
  have hprod : p ^ (1 - 1 / q) * (u / p) ^ (1 - 1 / q) =
      u ^ (1 - 1 / q) := by
    rw [← Real.mul_rpow hp.le (div_nonneg hu hp.le)]
    congr 1
    field_simp
  have hscaled := mul_le_mul_of_nonneg_left hber
    (Real.rpow_nonneg hp.le (1 - 1 / q))
  rw [hprod] at hscaled
  have hright : p ^ (1 - 1 / q) * (1 + (1 - 1 / q) * (u / p - 1)) =
      p ^ (1 - 1 / q) + (1 - 1 / q) * p ^ (-1 / q) * (u - p) := by
    rw [hfactor]
    field_simp
    <;> ring
  rw [hright] at hscaled
  apply (le_div_iff₀ hα).2
  have hdiv : (-(p ^ (1 - 1 / q)) / (1 - 1 / q)) * (1 - 1 / q) =
      -(p ^ (1 - 1 / q)) := div_mul_cancel₀ _ (ne_of_gt hα)
  nlinarith

/-- The actual regularizer from canonical H1 and v3 equation (9). -/
noncomputable def tsallis (q : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, -(p i ^ (1 - 1 / q)) / (1 - 1 / q)

/-- Finite scalar product, kept explicit to expose the simplex KKT algebra. -/
noncomputable def dot (f g : ι → ℝ) : ℝ := ∑ i, f i * g i

/-- Exact power projection implies the actual Tsallis gradient equation. -/
theorem projection_gradient (q η : ℝ) (G p : ι → ℝ) (x : ℝ)
    (hq : 1 < q) (hp : IsProjection q η G p x) (i : ι) :
    -(p i ^ (-1 / q)) = -η * (G i + x) := by
  rw [hp.2.1 i, ← Real.rpow_mul (hp.1 i).le]
  have he : -q * (-1 / q) = 1 := by field_simp
  rw [he, Real.rpow_one]
  ring

/-- Exact INF projections really minimize the FTRL objective on the closed
simplex. Minimization is derived from the power formula, never assumed. -/
theorem projection_minimizes (q η : ℝ) (G p u : ι → ℝ) (x : ℝ)
    (hq : 1 < q) (hp : IsProjection q η G p x)
    (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1) :
    tsallis q p + η * dot G p ≤ tsallis q u + η * dot G u := by
  have hp0 (i : ι) : 0 < p i := by
    rw [hp.2.1 i]
    exact Real.rpow_pos_of_pos (hp.1 i) _
  have hs := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) =>
    tsallis_scalar_support q (p i) (u i) hq (hp0 i) (hu i)
  have hgrad : ∑ i, (p i) ^ (-1 / q) * (u i - p i) =
      η * (dot G u - dot G p) := by
    have hg (i : ι) : (p i) ^ (-1 / q) = η * (G i + x) := by
      linarith [projection_gradient q η G p x hq hp i]
    simp_rw [hg, mul_add, add_mul, mul_sub, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [hp.2.2, hsu, mul_one, dot]
    simp_rw [Finset.mul_sum, mul_assoc]
    ring
  simp only [Finset.sum_sub_distrib] at hs
  change tsallis q p - _ ≤ tsallis q u at hs
  rw [hgrad] at hs
  linarith

/-- Gradient pairing, with the simplex multiplier eliminated exactly. -/
theorem projection_gradient_dot (q η : ℝ) (G p u : ι → ℝ) (x : ℝ)
    (hq : 1 < q) (hp : IsProjection q η G p x) (hsu : ∑ i, u i = 1) :
    dot (fun i => (p i) ^ (-1 / q)) (fun i => u i - p i) =
      η * (dot G u - dot G p) := by
  have hg (i : ι) : (p i) ^ (-1 / q) = η * (G i + x) := by
    linarith [projection_gradient q η G p x hq hp i]
  simp_rw [dot, hg, mul_add, add_mul, mul_sub, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [hp.2.2, hsu, mul_one]
  simp_rw [Finset.mul_sum, mul_assoc]
  ring

/-- Bregman divergence of the actual Tsallis regularizer, using its explicit
gradient rather than an abstract convexity oracle. -/
noncomputable def bregman (q : ℝ) (u p : ι → ℝ) : ℝ :=
  tsallis q u - tsallis q p +
    dot (fun i => (p i) ^ (-1 / q)) (fun i => u i - p i)

noncomputable def cumulative (L : ℕ → ι → ℝ) (t : ℕ) (i : ι) : ℝ :=
  ∑ s ∈ Finset.range t, L s i

noncomputable def potential (q η : ℝ) (L p : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  tsallis q (p t) + η * dot (cumulative L t) (p t)

noncomputable def stability (q η : ℝ) (L p : ℕ → ι → ℝ) (t : ℕ) : ℝ :=
  dot (L t) (fun i => p t i - p (t + 1) i) -
    bregman q (p (t + 1)) (p t) / η

/-- Exact potential increment for the real power-projection update. -/
theorem potential_increment (q η : ℝ) (L p : ℕ → ι → ℝ) (x : ℕ → ℝ)
    (hq : 1 < q) (hproj : ∀ t, IsProjection q η (cumulative L t) (p t) (x t))
    (t : ℕ) :
    potential q η L p (t + 1) - potential q η L p t =
      bregman q (p (t + 1)) (p t) + η * dot (L t) (p (t + 1)) := by
  have hg := projection_gradient_dot q η (cumulative L t) (p t) (p (t + 1))
    (x t) hq (hproj t) (hproj (t + 1)).2.2
  have hc : dot (cumulative L (t + 1)) (p (t + 1)) =
      dot (cumulative L t) (p (t + 1)) + dot (L t) (p (t + 1)) := by
    simp only [dot, cumulative, Finset.sum_range_succ, add_mul, Finset.sum_add_distrib]
  unfold potential bregman
  rw [hc, hg]
  ring

/-- The complete telescoping equality, before the final comparator minimum.
Its only algorithmic premises are the exact power projection and zero initial
cumulative loss contained in `cumulative`. -/
theorem ftrl_identity (q η : ℝ) (L p : ℕ → ι → ℝ) (x : ℕ → ℝ)
    (hq : 1 < q) (hη : 0 < η)
    (hproj : ∀ t, IsProjection q η (cumulative L t) (p t) (x t))
    (T : ℕ) :
    η * (∑ t ∈ Finset.range T, dot (L t) (p t)) =
      potential q η L p T - potential q η L p 0 +
        η * ∑ t ∈ Finset.range T, stability q η L p t := by
  have hstep (t : ℕ) : η * dot (L t) (p t) =
      potential q η L p (t + 1) - potential q η L p t + η * stability q η L p t := by
    rw [potential_increment q η L p x hq hproj t]
    unfold stability
    have hd : dot (L t) (fun i => p t i - p (t + 1) i) =
        dot (L t) (p t) - dot (L t) (p (t + 1)) := by
      simp only [dot, mul_sub, Finset.sum_sub_distrib]
    rw [hd]
    field_simp
    <;> ring
  calc
    _ = ∑ t ∈ Finset.range T, η * dot (L t) (p t) := Finset.mul_sum _ _ _
    _ = ∑ t ∈ Finset.range T,
        (potential q η L p (t + 1) - potential q η L p t + η * stability q η L p t) := by
      apply Finset.sum_congr rfl
      intro t _
      exact hstep t
    _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_range_sub, Finset.mul_sum]

/-- Canonical H2 / v3 A.1's entire deterministic FTRL regret inequality before
Taylor's local-norm bound, derived for the actual Tsallis power projections.
No regret inequality, objective-minimality, curvature, or stability bound is
assumed. -/
theorem ftrl_regret_le (q η : ℝ) (L p : ℕ → ι → ℝ) (x : ℕ → ℝ)
    (hq : 1 < q) (hη : 0 < η)
    (hproj : ∀ t, IsProjection q η (cumulative L t) (p t) (x t))
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1) (T : ℕ) :
    (∑ t ∈ Finset.range T, dot (L t) (fun i => p t i - u i)) ≤
      (tsallis q u - tsallis q (p 0)) / η +
        ∑ t ∈ Finset.range T, stability q η L p t := by
  have hid := ftrl_identity q η L p x hq hη hproj T
  have hmin := projection_minimizes q η (cumulative L T) (p T) u (x T)
    hq (hproj T) hu hsu
  have hz : potential q η L p 0 = tsallis q (p 0) := by
    simp [potential, cumulative, dot]
  have hcum : dot (cumulative L T) u = ∑ t ∈ Finset.range T, dot (L t) u := by
    unfold dot cumulative
    simp_rw [Finset.sum_mul]
    exact Finset.sum_comm
  have hsplit : (∑ t ∈ Finset.range T, dot (L t) (fun i => p t i - u i)) =
      (∑ t ∈ Finset.range T, dot (L t) (p t)) - ∑ t ∈ Finset.range T, dot (L t) u := by
    simp only [dot, mul_sub, Finset.sum_sub_distrib]
  rw [hsplit]
  rw [hz] at hid
  unfold potential at hid
  rw [hcum] at hmin
  apply (mul_le_mul_right hη).mp
  have halg : ((tsallis q u - tsallis q (p 0)) / η +
      ∑ t ∈ Finset.range T, stability q η L p t) * η =
      tsallis q u - tsallis q (p 0) + η * ∑ t ∈ Finset.range T, stability q η L p t := by
    field_simp
    <;> ring
  rw [halg]
  nlinarith

/-- The full Fq range bound on the closed simplex. This is the actual
q/(q-1)*(K^(1/q)-1) from H1 and v3 equation (9), for any real q>1. -/
theorem tsallis_range_le (q : ℝ) (p u : ι → ℝ) (hq : 1 < q)
    (hp : ∀ i, 0 ≤ p i) (hsp : ∑ i, p i = 1)
    (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1) :
    tsallis q u - tsallis q p ≤
      q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1) := by
  have hq0 : 0 < q := lt_trans zero_lt_one hq
  have hqm : 0 < q - 1 := by linarith
  have hα : 0 < 1 - 1 / q := by
    have hh := (div_lt_one hq0).2 hq
    linarith
  have hα1 : 1 - 1 / q ≤ 1 := by linarith [one_div_pos.mpr hq0]
  have hconj : 1 < q / (q - 1) := (lt_div_iff₀ hqm).2 (by linarith)
  have he1 : 1 / (q / (q - 1)) = 1 - 1 / q := by field_simp
  have hupper := sum_rpow_le_card (q / (q - 1)) p hconj hp hsp
  rw [he1] at hupper
  have hlower : 1 ≤ ∑ i, (u i) ^ (1 - 1 / q) := by
    calc
      1 = ∑ i, u i := hsu.symm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro i _
        simpa using Real.rpow_le_rpow_of_exponent_ge' (hu i)
          (coordinate_le_one u hu hsu i) hα.le hα1
  calc
    tsallis q u - tsallis q p =
        ((∑ i, (p i) ^ (1 - 1 / q)) - ∑ i, (u i) ^ (1 - 1 / q)) / (1 - 1 / q) := by
      simp only [tsallis, ← Finset.sum_div, Finset.sum_neg_distrib]
      ring
    _ ≤ ((Fintype.card ι : ℝ) ^ (1 / q) - 1) / (1 - 1 / q) := by
      apply div_le_div_of_nonneg_right _ hα.le
      have hexp : 1 - (1 - 1 / q) = 1 / q := by ring
      rw [hexp] at hupper
      linarith
    _ = _ := by field_simp

/-- The exact range-instantiated deterministic FTRL regret inequality from
H2. The Taylor/second-derivative stability inequality remains a separate task. -/
theorem ftrl_regret_le_range (q η : ℝ) (L p : ℕ → ι → ℝ) (x : ℕ → ℝ)
    (hq : 1 < q) (hη : 0 < η)
    (hproj : ∀ t, IsProjection q η (cumulative L t) (p t) (x t))
    (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) (hsu : ∑ i, u i = 1) (T : ℕ) :
    (∑ t ∈ Finset.range T, dot (L t) (fun i => p t i - u i)) ≤
      (q / (q - 1) * ((Fintype.card ι : ℝ) ^ (1 / q) - 1)) / η +
        ∑ t ∈ Finset.range T, stability q η L p t := by
  have hp0 (i : ι) : 0 ≤ p 0 i := by
    rw [(hproj 0).2.1 i]
    exact Real.rpow_nonneg ((hproj 0).1 i).le _
  exact (ftrl_regret_le q η L p x hq hη hproj u hu hsu T).trans
    (add_le_add_right (div_le_div_of_nonneg_right
      (tsallis_range_le q (p 0) u hq hp0 (hproj 0).2.2 hu hsu) hη.le) _)

end Part2.HinfExpected

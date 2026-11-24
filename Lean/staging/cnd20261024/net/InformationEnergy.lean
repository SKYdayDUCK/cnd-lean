import staging.cnd20261024.net.OscillationNet
import staging.cnd20261024.probability.CoordinateBridge
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Seminorm

noncomputable section
set_option maxHeartbeats 800000
open Finset
namespace Part2.CNDNet
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem oscillation_nonneg (x : ι → ℝ) : 0 ≤ oscillation x := norm_nonneg _

theorem pairwise_le_oscillation (x : ι → ℝ) (i j : ι) :
    |x i - x j| ≤ oscillation x := by
  exact norm_le_pi_norm (fun ij : ι × ι => x ij.1 - x ij.2) (i, j)

theorem oscillation_smul (c : ℝ) (x : ι → ℝ) :
    oscillation (c • x) = |c| * oscillation x := by
  unfold oscillation
  have he : (fun ij : ι × ι => (c • x) ij.1 - (c • x) ij.2) =
      c • (fun ij : ι × ι => x ij.1 - x ij.2) := by ext ij; simp; ring
  rw [he, norm_smul, Real.norm_eq_abs]

theorem coordinate_le_oscillation [Nonempty ι] (x : ι → ℝ)
    (hx : (∑ i, x i) = 0) (i : ι) : |x i| ≤ oscillation x := by
  have hc : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hupper := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    (abs_le.mp (pairwise_le_oscillation x i j)).2)
  have hlower := Finset.sum_le_sum (s := Finset.univ) (fun j _ =>
    (abs_le.mp (pairwise_le_oscillation x j i)).2)
  simp only [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, hx,
    Finset.card_univ] at hupper hlower
  apply abs_le.mpr
  constructor <;> nlinarith

theorem square_sum_upper [Nonempty ι] (x : ι → ℝ) (hx : (∑ i, x i) = 0) :
    (∑ i, (x i)^2) ≤ (Fintype.card ι : ℝ) * (oscillation x)^2 := by
  calc
    _ ≤ ∑ _i : ι, (oscillation x)^2 := by
      apply Finset.sum_le_sum
      intro i _
      have hh := coordinate_le_oscillation x hx i
      nlinarith [sq_abs (x i), abs_nonneg (x i), oscillation_nonneg x]
    _ = _ := by simp

theorem square_sum_lower (x : ι → ℝ) :
    (oscillation x)^2 ≤ 2 * (∑ i, (x i)^2) := by
  have hsum : 0 ≤ ∑ i, (x i)^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hnorm : oscillation x ≤ Real.sqrt (2 * ∑ i, (x i)^2) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2
    intro ij
    have hp : (x ij.1 - x ij.2)^2 ≤ 2 * ∑ i, (x i)^2 := by
      by_cases he : ij.1 = ij.2
      · simp [he]; positivity
      · have hh : (x ij.1)^2 + (x ij.2)^2 ≤ ∑ i, (x i)^2 := by
          have hh := Finset.sum_le_sum_of_subset_of_nonneg
            (f := fun i => (x i)^2) (Finset.subset_univ ({ij.1, ij.2} : Finset ι))
            (by intros; positivity)
          simpa only [Finset.sum_pair he] using hh
        nlinarith [sq_nonneg (x ij.1 + x ij.2)]
    rw [Real.norm_eq_abs]
    have hh := Real.sq_sqrt (by positivity : 0 ≤ 2 * ∑ i, (x i)^2)
    nlinarith [abs_nonneg (x ij.1 - x ij.2), sq_abs (x ij.1 - x ij.2), Real.sqrt_nonneg (2 * ∑ i, (x i)^2)]
  nlinarith [Real.sq_sqrt (by positivity : 0 ≤ 2 * ∑ i, (x i)^2), oscillation_nonneg x,
    Real.sqrt_nonneg (2 * ∑ i, (x i)^2)]

/-- An explicit Euclidean embedding of the actual regularized information energy. -/
def energyMap (p : ℕ → ι → ℝ) (n : ℕ) :
    (ι → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (Sum ι (Fin n × ι)) where
  toFun x := WithLp.toLp 2 (fun k => match k with
    | .inl i => x i
    | .inr ti => Real.sqrt (p ti.1 ti.2) *
        (x ti.2 - CNDPhysical.coordinateMean (p ti.1) x))
  map_add' x y := by
    apply PiLp.ext
    intro k
    cases k with
    | inl i => rfl
    | inr ti => simp [CNDPhysical.coordinateMean, mul_add, Finset.sum_add_distrib]; ring
  map_smul' c x := by
    apply PiLp.ext
    intro k
    cases k with
    | inl i => rfl
    | inr ti =>
      change Real.sqrt (p ti.1 ti.2) *
          (c * x ti.2 - ∑ j, p ti.1 j * (c * x j)) =
        c * (Real.sqrt (p ti.1 ti.2) * (x ti.2 - ∑ j, p ti.1 j * x j))
      have hs : (∑ j, p ti.1 j * (c * x j)) = c * ∑ j, p ti.1 j * x j := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        ring
      rw [hs]
      ring

def informationEnergy (p : ℕ → ι → ℝ) (n : ℕ) : Seminorm ℝ (ι → ℝ) :=
  (normSeminorm ℝ _).comp (energyMap p n)

theorem energy_square (p : ℕ → ι → ℝ) (hp : ∀ t i, 0 ≤ p t i) (n : ℕ) (x : ι → ℝ) :
    (informationEnergy p n x)^2 = (∑ i, (x i)^2) +
      ∑ t : Fin n, ∑ i, p t i * (x i - CNDPhysical.coordinateMean (p t) x)^2 := by
  change ‖energyMap p n x‖^2 = _
  rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sum_type]
  simp only [energyMap, LinearMap.coe_mk, AddHom.coe_mk, PiLp.toLp_apply,
    Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type, PiLp.toLp_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_pow, Real.sq_sqrt (hp t i)]

theorem direction_variance_upper (p x : ι → ℝ) (hp : p ∈ CND.simplex) :
    CNDProbability.directionVariance p x ≤ (oscillation x)^2 := by
  have hh (i : ι) : |x i - CNDPhysical.coordinateMean p x| ≤ oscillation x := by
    have he : x i - CNDPhysical.coordinateMean p x = ∑ j, p j * (x i - x j) := by
      simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hp.2, one_mul,
        CNDPhysical.coordinateMean]
    rw [he]
    calc
      _ ≤ ∑ j, |p j * (x i - x j)| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, p j * |x i - x j| := by simp_rw [abs_mul, abs_of_nonneg (hp.1 _)]
      _ ≤ ∑ j, p j * oscillation x := Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (pairwise_le_oscillation x i j) (hp.1 j)
      _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]
  unfold CNDProbability.directionVariance CNDProbability.directionScore CNDProbability.weighted
  calc
    _ ≤ ∑ i, p i * (oscillation x)^2 := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (hp.1 i)
      have hh' := hh i
      change |x i - (∑ j, p j * x j)| ≤ oscillation x at hh'
      nlinarith [sq_abs (x i - ∑ j, p j * x j), oscillation_nonneg x,
        abs_nonneg (x i - ∑ j, p j * x j)]
    _ = _ := by rw [← Finset.sum_mul, hp.2, one_mul]

theorem energy_square_variance (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ CND.simplex)
    (n : ℕ) (x : ι → ℝ) :
    (informationEnergy p n x)^2 = (∑ i, (x i)^2) +
      ∑ t ∈ Finset.range n, CNDProbability.directionVariance (p t) x := by
  rw [energy_square p (fun t i => (hp t).1 i)]
  simp only [CNDProbability.directionVariance, CNDProbability.directionScore,
    CNDProbability.weighted, CNDPhysical.coordinateMean]
  congr 1
  exact Fin.sum_univ_eq_sum_range
    (fun t => ∑ i, p t i * (x i - ∑ j, p t j * x j)^2) n

theorem quadratic_add (B C : Matrix ι ι ℝ) (x : ι → ℝ) :
    CND.quadratic (B + C) x = CND.quadratic B x + CND.quadratic C x := by
  simp only [CND.quadratic, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

theorem quadratic_identity (x : ι → ℝ) :
    CND.quadratic (1 : Matrix ι ι ℝ) x = ∑ i, (x i)^2 := by
  simp [CND.quadratic, Matrix.one_apply, mul_ite, pow_two]

theorem quadratic_covariance_sum (p : ℕ → ι → ℝ) (n : ℕ) (x : ι → ℝ) :
    CND.quadratic (∑ t ∈ Finset.range n, CNDPhysical.covariance (p t)) x =
      ∑ t ∈ Finset.range n, CND.quadratic (CNDPhysical.covariance (p t)) x := by
  induction n with
  | zero => simp [CND.quadratic]
  | succ n ih => rw [Finset.sum_range_succ, quadratic_add, ih, Finset.sum_range_succ]

/-- This is exactly xᵀ(I+ΣC)x, not an assumed abstract variance process. -/
theorem energy_actual_information (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ CND.simplex)
    (n : ℕ) (x : ι → ℝ) :
    (informationEnergy p n x)^2 = CND.quadratic (CNDPhysical.information p n) x := by
  rw [energy_square_variance p hp, CNDPhysical.information, quadratic_add,
    quadratic_identity, quadratic_covariance_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [CNDPhysical.covariance_variance (p t) x (hp t).2]
  rfl

theorem energy_upper [Nonempty ι] (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ CND.simplex) (n T : ℕ) (hn : n ≤ T)
    (hK : 2 ≤ Fintype.card ι) (x : ι → ℝ) (hx : (∑ i, x i) = 0) :
    informationEnergy p n x ≤ Real.sqrt ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2)) *
      oscillation x := by
  have hq : (∑ t ∈ Finset.range n, CNDProbability.directionVariance (p t) x) ≤
      (n : ℝ) * (oscillation x)^2 := by
    calc
      _ ≤ ∑ _t ∈ Finset.range n, (oscillation x)^2 :=
        Finset.sum_le_sum fun t _ => direction_variance_upper (p t) x (hp t)
      _ = _ := by simp
  have hs := square_sum_upper x hx
  have he := energy_square_variance p hp n x
  have hn' : (n : ℝ) ≤ T := by exact_mod_cast hn
  have hK' : (2 : ℝ) ≤ Fintype.card ι := by exact_mod_cast hK
  have ht : (0 : ℝ) ≤ T := by positivity
  have hbound : (informationEnergy p n x)^2 ≤
      ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2)) * (oscillation x)^2 := by
    nlinarith [sq_nonneg (oscillation x), mul_nonneg (by nlinarith : 0 ≤
      (Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2) - (Fintype.card ι + n))
      (sq_nonneg (oscillation x))]
  have hr := Real.sq_sqrt (by positivity : 0 ≤ (Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2))
  have hz := apply_nonneg (informationEnergy p n) x
  have ho := oscillation_nonneg x
  have hr0 := Real.sqrt_nonneg ((Fintype.card ι : ℝ) * (1 + (T : ℝ) / 2))
  apply (sq_le_sq₀ hz (mul_nonneg hr0 ho)).mp
  rw [mul_pow, hr]
  exact hbound

end Part2.CNDNet


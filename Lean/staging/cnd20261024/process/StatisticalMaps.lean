import staging.cnd20261024.process.CNDProcess
import CNDConfidenceSlabs
import Mathlib.Topology.Instances.Matrix

/-! Concrete Borel statistical coefficients for the original CND recursion.
The full-space inverse of V+11^T/K implements the inverse on contrasts;
subtracting 11^T/K gives the tangent inverse on valid information states.
No invertibility or confidence-success event is needed for measurability. -/

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix

namespace Part2.CNDProcess.StatisticalMaps

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

local instance : MeasurableSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (MeasurableSpace (ι → ι → ℝ))

local instance : BorelSpace (Matrix ι ι ℝ) :=
  inferInstanceAs (BorelSpace (ι → ι → ℝ))

def regularized (V : Mat ι) : Matrix ι ι ℝ := fun i j ↦ V i j + (Fintype.card ι : ℝ)⁻¹
def totalInverse (V : Mat ι) : Matrix ι ι ℝ := (regularized V)⁻¹
def tangentInverse (V : Mat ι) : Mat ι := fun i j ↦ totalInverse V i j - (Fintype.card ι : ℝ)⁻¹
def estimate (s : Stats ι) (i : ι) : ℝ := ∑ j, tangentInverse s.1 i j * s.2 j
def resistance (V : Mat ι) : Mat ι := CND.gramDistance (totalInverse V)

def rawPairRadius (H L R : ℝ) (s : Stats ι) (i j : ι) : ℝ :=
  2 * H * Real.sqrt (L * resistance s.1 i j) +
    (4 * H * L + R * Fintype.card ι) * resistance s.1 i j

def rawRadius (H L R : ℝ) (s : Stats ι) (i j : ι) : ℝ :=
  CNDPhysical.saturatedRadius R (rawPairRadius H L R s i j)

def actualConfidence (H L R : ℝ) (hR : 0 ≤ R) (s : Stats ι) : Vec ι :=
  CNDConfidenceSlabs.canonicalConfidence ι R hR (estimate s, rawPairRadius H L R s)

theorem measurable_matrix_inverse : Measurable (fun V : Matrix ι ι ℝ ↦ V⁻¹) := by
  have hd : Measurable (fun V : Matrix ι ι ℝ ↦ V.det) := continuous_id.matrix_det.measurable
  have ha : Measurable (fun V : Matrix ι ι ℝ ↦ V.adjugate) := continuous_id.matrix_adjugate.measurable
  have he : (fun V : Matrix ι ι ℝ ↦ V⁻¹) =
      fun V ↦ (V.det)⁻¹ • V.adjugate := by
    funext V
    rw [Matrix.inv_def, Ring.inverse_eq_inv]
  rw [he]
  exact hd.inv.smul ha

theorem measurable_regularized : Measurable (regularized (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (((measurable_pi_apply j).comp (measurable_pi_apply i)).add_const _)

theorem measurable_totalInverse : Measurable (totalInverse (ι := ι)) :=
  measurable_matrix_inverse.comp measurable_regularized

theorem measurable_tangentInverse : Measurable (tangentInverse (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_totalInverse)).sub_const _)

theorem measurable_estimate : Measurable (estimate (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  apply Finset.measurable_fun_sum
  intro j _
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_tangentInverse.comp measurable_fst))).mul ((measurable_pi_apply j).comp measurable_snd))

theorem measurable_resistance : Measurable (resistance (ι := ι)) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  unfold resistance CND.gramDistance
  exact (((measurable_pi_apply i).comp ((measurable_pi_apply i).comp measurable_totalInverse)).add
    ((measurable_pi_apply j).comp ((measurable_pi_apply j).comp measurable_totalInverse))).sub
    (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp measurable_totalInverse)).const_mul 2)

theorem measurable_rawPairRadius (H L R : ℝ) : Measurable (rawPairRadius (ι := ι) H L R) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hm : Measurable (fun s : Stats ι ↦ resistance s.1 i j) := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp
    (measurable_resistance.comp measurable_fst))
  exact (((hm.const_mul L).sqrt).const_mul (2 * H)).add (hm.const_mul _)

theorem measurable_rawRadius (H L R : ℝ) : Measurable (rawRadius (ι := ι) H L R) := by
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  have hm : Measurable (fun s : Stats ι ↦ rawPairRadius H L R s i j) := (measurable_pi_apply j).comp ((measurable_pi_apply i).comp (measurable_rawPairRadius (ι := ι) H L R))
  exact (measurable_const.sub (((hm.div_const R).neg).exp)).const_mul _

theorem measurable_actualConfidence (H L R : ℝ) (hR : 0 ≤ R) :
    Measurable (actualConfidence (ι := ι) H L R hR) :=
  (CNDConfidenceSlabs.measurable_canonicalConfidence ι R hR).comp
    (measurable_estimate.prodMk (measurable_rawPairRadius H L R))

theorem rawRadius_history_measurable {Ω : Type*} [MeasurableSpace Ω]
    (s : Ω → Stats ι) (hs : Measurable s) (H L R : ℝ) :
    Measurable (fun ω ↦ rawRadius H L R (s ω)) := (measurable_rawRadius H L R).comp hs

theorem rawRadius_zero_R (H L : ℝ) (s : Stats ι) : rawRadius H L 0 s = 0 := by
  funext i j
  simp [rawRadius, CNDPhysical.saturatedRadius]

end Part2.CNDProcess.StatisticalMaps

end

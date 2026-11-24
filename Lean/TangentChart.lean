import PrivateInformationBudget

/-! A fixed orthonormal chart is constructed for the actual zero-sum subspace. -/
noncomputable section
namespace Part2.CNDInformation
open Matrix Finset
open scoped Matrix BigOperators InnerProductSpace
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def commonVector (ι : Type*) [Fintype ι] : EuclideanSpace ℝ ι :=
  WithLp.toLp 2 (fun _ => 1)

def tangentSpace (ι : Type*) [Fintype ι] : Submodule ℝ (EuclideanSpace ℝ ι) :=
  (ℝ ∙ commonVector ι)ᗮ

theorem mem_tangentSpace (x : EuclideanSpace ℝ ι) :
    x ∈ tangentSpace ι ↔ (∑ i, x i) = 0 := by
  rw [tangentSpace, Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [commonVector, EuclideanSpace.inner_eq_star_dotProduct, dotProduct]

abbrev TangentIndex (ι : Type*) [Fintype ι] := Fin (Module.finrank ℝ (tangentSpace ι))

def tangentBasis (ι : Type*) [Fintype ι] :
    OrthonormalBasis (TangentIndex ι) ℝ (tangentSpace ι) := stdOrthonormalBasis ℝ (tangentSpace ι)

def canonicalChart (ι : Type*) [Fintype ι] : Matrix ι (TangentIndex ι) ℝ :=
  fun i a => ((tangentBasis ι a : tangentSpace ι) : EuclideanSpace ℝ ι) i

theorem canonicalChart_column_sum (a : TangentIndex ι) :
    (∑ i, canonicalChart ι i a) = 0 :=
  (mem_tangentSpace _).mp (tangentBasis ι a).property

theorem canonicalChart_orthonormal : (canonicalChart ι)ᴴ * canonicalChart ι = 1 := by
  ext a b
  have h := (tangentBasis ι).inner_eq_ite a b
  simpa [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct,
    Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    canonicalChart, dotProduct, mul_comm] using h

theorem canonicalChart_range_zero_sum (y : TangentIndex ι → ℝ) :
    (∑ i, (canonicalChart ι *ᵥ y) i) = 0 := by
  simp only [Matrix.mulVec, dotProduct]
  rw [sum_comm]
  simp_rw [← sum_mul, canonicalChart_column_sum, zero_mul]
  simp

theorem canonicalChart_spans_tangent (x : ι → ℝ) (hx : (∑ i, x i) = 0) :
    canonicalChart ι *ᵥ ((canonicalChart ι)ᴴ *ᵥ x) = x := by
  let xH : tangentSpace ι := ⟨WithLp.toLp 2 x, (mem_tangentSpace _).mpr hx⟩
  have he := congrArg (tangentSpace ι).subtype ((tangentBasis ι).sum_repr' xH)
  simp only [map_sum, map_smul] at he
  funext i
  let ev : EuclideanSpace ℝ ι →ₗ[ℝ] ℝ :=
    (LinearMap.proj i : (ι → ℝ) →ₗ[ℝ] ℝ).comp (WithLp.linearEquiv 2 ℝ (ι → ℝ)).toLinearMap
  have hi := congrArg ev he
  simp only [map_sum, map_smul, smul_eq_mul] at hi
  have hinner (a : TangentIndex ι) :
      ⟪tangentBasis ι a, xH⟫_ℝ = ((canonicalChart ι)ᴴ *ᵥ x) a := by
    simp [Submodule.coe_inner, EuclideanSpace.inner_eq_star_dotProduct,
      Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply, canonicalChart, xH, mul_comm]
  simp only [hinner] at hi
  change (∑ a, (((canonicalChart ι)ᴴ *ᵥ x) a) * canonicalChart ι i a) = x i at hi
  simpa only [Matrix.mulVec, dotProduct, mul_comm] using hi

theorem canonicalChart_is_tangentChart : TangentChart (canonicalChart ι) :=
  ⟨canonicalChart_orthonormal, canonicalChart_range_zero_sum, canonicalChart_spans_tangent⟩

theorem exists_tangentChart : ∃ Q : Matrix ι (TangentIndex ι) ℝ, TangentChart Q :=
  ⟨canonicalChart ι, canonicalChart_is_tangentChart⟩

theorem commonVector_ne_zero [Nonempty ι] : commonVector ι ≠ 0 := by
  intro h
  obtain ⟨i⟩ := ‹Nonempty ι›
  have he := congrArg (fun x : EuclideanSpace ℝ ι => x i) h
  simp [commonVector] at he

theorem tangentSpace_finrank [Nonempty ι] :
    Module.finrank ℝ (tangentSpace ι) = Fintype.card ι - 1 := by
  have hcard : 0 < Fintype.card ι := Fintype.card_pos
  letI : Fact (Module.finrank ℝ (EuclideanSpace ℝ ι) = (Fintype.card ι - 1) + 1) :=
    ⟨by rw [finrank_euclideanSpace]; omega⟩
  exact Submodule.finrank_orthogonal_span_singleton (commonVector_ne_zero (ι := ι))

/-- No free coordinate-chart assumption remains in this actual Q information bound. -/
theorem actualGamma_sum_le_canonicalQ [LinearOrder ι] (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) (H L R : ℝ)
    (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (∑ s ∈ range n, actualGamma p (u+s) H L R) ≤
      branchedQ (canonicalChart ι) p u n H L R :=
  actualGamma_sum_le_branchedQ _ canonicalChart_is_tangentChart p hp u n H L R hH hL hR

end Part2.CNDInformation

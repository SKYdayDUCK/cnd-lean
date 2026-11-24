import Part2.CNDPhysical
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-! Actual positive-semidefinite increments, inverse-design trace and log determinant. -/
noncomputable section
namespace Part2.CNDInformation
open Matrix Finset
open scoped Matrix BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem scalar_trace_log {x : ℝ} (hx : 0 ≤ x) (hhalf : x ≤ 1 / 2) :
    x ≤ (3 / 2 : ℝ) * Real.log (1 + x) := by
  have hpos : 0 < 1 + x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hpos
  have hlog0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have hmul := (mul_le_mul_of_nonneg_right hlog hpos.le)
  have hid : (1 - (1 + x)⁻¹) * (1 + x) = x := by field_simp; ring
  rw [hid] at hmul
  nlinarith

theorem eigenvector_norm_sq {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (i : ι) :
    (⇑(hA.eigenvectorBasis i)) ⬝ᵥ (⇑(hA.eigenvectorBasis i)) = 1 := by
  have hn := hA.eigenvectorBasis.orthonormal.1 i
  simpa only [real_inner_self_eq_norm_sq, hn, one_pow, star_trivial] using
    (EuclideanSpace.inner_eq_star_dotProduct (hA.eigenvectorBasis i)
      (hA.eigenvectorBasis i)).symm

/-- The actual PSD trace inequality; no log determinant inequality is a premise. -/
theorem psd_trace_le_logdet (A : Matrix ι ι ℝ) (hA : A.PosSemidef)
    (hupper : ((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) - A).PosSemidef) :
    A.trace ≤ (3 / 2 : ℝ) * Real.log ((1 + A).det) := by
  let M : Matrix ι ι ℝ := 1 + A
  have hM : M.PosDef := Matrix.PosDef.one.add_posSemidef hA
  have hlow (i : ι) : 1 ≤ hM.isHermitian.eigenvalues i := by
    have he := hM.isHermitian.eigenvalues_eq i
    have hp := hA.2 (⇑(hM.isHermitian.eigenvectorBasis i))
    simp only [M, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
      star_trivial, RCLike.re_to_real] at he
    rw [eigenvector_norm_sq hM.isHermitian i] at he
    simp only [star_trivial] at hp
    linarith
  have hupp (i : ι) : hM.isHermitian.eigenvalues i ≤ 3 / 2 := by
    have he := hM.isHermitian.eigenvalues_eq i
    have hp := hupper.2 (⇑(hM.isHermitian.eigenvectorBasis i))
    simp only [M, Matrix.add_mulVec, Matrix.one_mulVec, dotProduct_add,
      star_trivial, RCLike.re_to_real] at he
    simp only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
      star_trivial, dotProduct_sub, dotProduct_smul, smul_eq_mul,
      eigenvector_norm_sq hM.isHermitian i] at hp
    rw [eigenvector_norm_sq hM.isHermitian i] at he
    linarith
  have hsum := Finset.sum_le_sum (s := (univ : Finset ι)) (fun i _ =>
    scalar_trace_log (sub_nonneg.mpr (hlow i)) (by linarith [hupp i]))
  have htrace : A.trace = ∑ i, (hM.isHermitian.eigenvalues i - 1) := by
    have ht := hM.isHermitian.trace_eq_sum_eigenvalues
    simp only [M, Matrix.trace_add, Matrix.trace_one, RCLike.ofReal_real_eq_id,
      id_eq] at ht
    simp only [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, mul_one]
    linarith
  have hdet : Real.log M.det = ∑ i, Real.log (hM.isHermitian.eigenvalues i) := by
    rw [hM.isHermitian.det_eq_prod_eigenvalues]
    simpa using Real.log_prod (univ : Finset ι) hM.isHermitian.eigenvalues
      (fun i _ => (hM.eigenvalues_pos i).ne')
  rw [htrace]
  simpa only [add_sub_cancel, ← Finset.mul_sum, ← hdet, M] using hsum

/-- A symmetric square root is constructed from the actual spectral decomposition. -/
theorem exists_symmetric_sqrt (C : Matrix ι ι ℝ) (hC : C.PosSemidef) :
    ∃ R : Matrix ι ι ℝ, R.IsHermitian ∧ R * R = C := by
  let U := hC.isHermitian.eigenvectorUnitary
  let D : Matrix ι ι ℝ := Matrix.diagonal (fun i => Real.sqrt (hC.isHermitian.eigenvalues i))
  have hD : D.IsHermitian := Matrix.isHermitian_diagonal _
  have hDD : D * D = Matrix.diagonal hC.isHermitian.eigenvalues := by
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact Real.mul_self_sqrt (hC.eigenvalues_nonneg i)
  refine ⟨(U : Matrix ι ι ℝ) * D * star (U : Matrix ι ι ℝ), ?_, ?_⟩
  · simpa only [Matrix.star_eq_conjTranspose] using
      Matrix.isHermitian_mul_mul_conjTranspose (U : Matrix ι ι ℝ) hD
  · calc
      _ = (U : Matrix ι ι ℝ) * (D * D) * star (U : Matrix ι ι ℝ) := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc (star (U : Matrix ι ι ℝ)),
          unitary.coe_star_mul_self, Matrix.one_mul]
      _ = C := by
        rw [hDD]
        simpa only [U, RCLike.ofReal_real_eq_id, Function.comp_id, Function.id_comp] using
          hC.isHermitian.spectral_theorem.symm

/-- Inversion contracts quadratic forms when the actual design dominates identity. -/
theorem inverse_le_identity (V : Matrix ι ι ℝ) (hV : V.PosDef)
    (hbase : (V - 1).PosSemidef) :
    ((1 : Matrix ι ι ℝ) - V⁻¹).PosSemidef := by
  refine ⟨Matrix.isHermitian_one.sub hV.inv.isHermitian, ?_⟩
  intro x
  let y := V⁻¹ *ᵥ x
  have hsol : V *ᵥ y = x := by
    dsimp [y]
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv V
      ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit), Matrix.one_mulVec]
  have hpos := hbase.2 y
  have hsquare : 0 ≤ (x - y) ⬝ᵥ (x - y) :=
    Finset.sum_nonneg (fun i _ => mul_self_nonneg ((x - y) i))
  have hsym : x ⬝ᵥ y = y ⬝ᵥ x := dotProduct_comm x y
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.one_mulVec, dotProduct_sub,
    sub_dotProduct, hsol] at hpos hsquare ⊢
  change 0 ≤ x ⬝ᵥ x - x ⬝ᵥ y
  nlinarith

/-- A genuine one-step trace/logdet bound for a PSD matrix increment. -/
theorem actual_trace_logdet_step (V C : Matrix ι ι ℝ) (hV : V.PosDef)
    (hbase : (V - 1).PosSemidef) (hC : C.PosSemidef)
    (hupper : ((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) - C).PosSemidef) :
    (V⁻¹ * C).trace ≤ (3 / 2 : ℝ) *
      (Real.log ((V + C).det) - Real.log V.det) := by
  obtain ⟨R, hR, hRR⟩ := exists_symmetric_sqrt C hC
  let A := R * V⁻¹ * R
  have hA : A.PosSemidef := by
    simpa only [A, hR.eq] using hV.inv.posSemidef.mul_mul_conjTranspose_same R
  have hdiff : (C - A).PosSemidef := by
    have hp := (inverse_le_identity V hV hbase).mul_mul_conjTranspose_same R
    simpa only [hR.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      hRR, A] using hp
  have hAu : ((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) - A).PosSemidef := by
    convert hupper.add hdiff using 1 <;> abel
  have htr : A.trace = (V⁻¹ * C).trace := by
    dsimp [A]
    rw [Matrix.trace_mul_cycle, hRR]
    exact Matrix.trace_mul_comm _ _
  have hfactor : V * (1 + V⁻¹ * C) = V + C := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit),
      Matrix.one_mul]
  have hdetA : (1 + A).det = (1 + V⁻¹ * C).det := by
    dsimp [A]
    rw [Matrix.mul_assoc R V⁻¹ R]
    rw [Matrix.det_one_add_mul_comm R (V⁻¹ * R)]
    rw [Matrix.mul_assoc V⁻¹ R R, hRR]
  have hdet : Real.log ((1 + A).det) =
      Real.log ((V + C).det) - Real.log V.det := by
    have hd : V.det * (1 + A).det = (V + C).det := by
      rw [hdetA, ← Matrix.det_mul, hfactor]
    have hinc : 0 < (1 + A).det := (Matrix.PosDef.one.add_posSemidef hA).det_pos
    have he := Real.log_mul hV.det_pos.ne' hinc.ne'
    rw [hd] at he
    linarith
  have ht := psd_trace_le_logdet A hA hAu
  rwa [htr, hdet] at ht

theorem covariance_half_identity (p x : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    (1 / 2 : ℝ) * (∑ i, (x i) ^ 2) -
      Part2.CND.quadratic (Part2.CNDPhysical.covariance p) x =
    (1 / 2 : ℝ) * (∑ i, (2 * p i - 1) ^ 2 * (x i) ^ 2) +
    (1 / 2 : ℝ) * (∑ i, ∑ j, if i = j then 0 else
      p i * p j * (x i + x j) ^ 2) := by
  have hfull : (∑ i, ∑ j, p i * p j * (x i + x j) ^ 2) =
      2 * (∑ i, p i * (x i) ^ 2) + 2 * (Part2.CNDPhysical.coordinateMean p x) ^ 2 := by
    have hterm (i j : ι) : p i * p j * (x i + x j) ^ 2 =
        (p i * (x i) ^ 2) * p j + (p i * x i) * (2 * (p j * x j)) +
          p i * (p j * (x j) ^ 2) := by ring
    simp_rw [hterm, sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul]
    rw [hp.2]
    unfold Part2.CNDPhysical.coordinateMean
    ring
  have hoff : (∑ i, ∑ j, if i = j then 0 else p i * p j * (x i + x j) ^ 2) =
      (∑ i, ∑ j, p i * p j * (x i + x j) ^ 2) - ∑ i, 4 * (p i) ^ 2 * (x i) ^ 2 := by
    rw [← sum_sub_distrib]
    apply sum_congr rfl
    intro i _
    have he (j : ι) : (if i = j then 0 else p i * p j * (x i + x j) ^ 2) =
        p i * p j * (x i + x j) ^ 2 -
          (if i = j then p i * p j * (x i + x j) ^ 2 else 0) := by
      split_ifs <;> ring
    simp_rw [he, sum_sub_distrib]
    simp only [Finset.sum_ite_eq, mem_univ, if_true]
    congr 1
    ring
  have hgap : (∑ i, (2 * p i - 1) ^ 2 * (x i) ^ 2) =
      4 * (∑ i, (p i) ^ 2 * (x i) ^ 2) -
      4 * (∑ i, p i * (x i) ^ 2) + ∑ i, (x i) ^ 2 := by
    have he (i : ι) : (2 * p i - 1) ^ 2 * (x i) ^ 2 =
        4 * ((p i) ^ 2 * (x i) ^ 2) - 4 * (p i * (x i) ^ 2) + (x i) ^ 2 := by ring
    simp_rw [he, sum_add_distrib, sum_sub_distrib, ← mul_sum]
  rw [hoff, hfull, hgap, Part2.CNDPhysical.covariance_quadratic]
  simp only [← mul_sum, mul_assoc]
  ring

/-- Uniform spectral bound for the actual arbitrary-simplex categorical covariance. -/
theorem covariance_half_psd (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    ((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) - Part2.CNDPhysical.covariance p).PosSemidef := by
  refine ⟨(Matrix.PosSemidef.one.smul (show (0 : ℝ) ≤ 1 / 2 by norm_num)).isHermitian.sub
    (Part2.CNDPhysical.covariance_posSemidef p hp).isHermitian, ?_⟩
  intro x
  simp only [star_trivial, Matrix.sub_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_smul, smul_eq_mul]
  have hq := Part2.CNDPhysical.quadratic_eq_dot (Part2.CNDPhysical.covariance p) x
  simp only [star_trivial] at hq
  rw [← hq]
  change 0 ≤ (1 / 2 : ℝ) * (∑ i, x i * x i) -
    Part2.CND.quadratic (Part2.CNDPhysical.covariance p) x
  simp_rw [← pow_two]
  rw [covariance_half_identity p x hp]
  apply add_nonneg
  · exact mul_nonneg (by norm_num) (sum_nonneg (fun i _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
  · apply mul_nonneg (by norm_num)
    apply sum_nonneg
    intro i _
    apply sum_nonneg
    intro j _
    split_ifs
    · exact le_rfl
    · exact mul_nonneg (mul_nonneg (hp.1 i) (hp.1 j)) (sq_nonneg _)

theorem actual_information_base_psd (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) :
    (Part2.CNDPhysical.information p n - 1).PosSemidef := by
  induction n with
  | zero => simpa [Part2.CNDPhysical.information] using
      (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | succ n ih =>
    have he : Part2.CNDPhysical.information p (n + 1) - 1 =
        (Part2.CNDPhysical.information p n - 1) + Part2.CNDPhysical.covariance (p n) := by
      simp only [Part2.CNDPhysical.information, sum_range_succ]
      abel
    rw [he]
    exact ih.add (Part2.CNDPhysical.covariance_posSemidef (p n) (hp n))

def actualLogdet (p : ℕ → ι → ℝ) (n : ℕ) : ℝ :=
  Real.log (Part2.CNDPhysical.information p n).det

/-- Every actual time interval, with the past design retained at its left endpoint. -/
theorem actual_information_trace_budget (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, ((Part2.CNDPhysical.information p (u + s))⁻¹ *
      Part2.CNDPhysical.covariance (p (u + s))).trace) ≤
      (3 / 2 : ℝ) * (actualLogdet p (u + n) - actualLogdet p u) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have ht := actual_trace_logdet_step
      (Part2.CNDPhysical.information p (u + n))
      (Part2.CNDPhysical.covariance (p (u + n)))
      (Part2.CNDPhysical.information_posDef p hp (u + n))
      (actual_information_base_psd p hp (u + n))
      (Part2.CNDPhysical.covariance_posSemidef (p (u + n)) (hp (u + n)))
      (covariance_half_psd (p (u + n)) (hp (u + n)))
    have he : Part2.CNDPhysical.information p (u + n) +
        Part2.CNDPhysical.covariance (p (u + n)) =
        Part2.CNDPhysical.information p (u + (n + 1)) := by
      change Part2.CNDPhysical.information p (u + n) +
        Part2.CNDPhysical.covariance (p (u + n)) =
        Part2.CNDPhysical.information p ((u + n) + 1)
      simp only [Part2.CNDPhysical.information, sum_range_succ]
      abel
    rw [he] at ht
    unfold actualLogdet at ih ⊢
    linarith

def matrixDesign (C : ℕ → Matrix ι ι ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  1 + ∑ t ∈ range n, C t

theorem matrixDesign_base_psd (C : ℕ → Matrix ι ι ℝ)
    (hC : ∀ t, (C t).PosSemidef) (n : ℕ) : (matrixDesign C n - 1).PosSemidef := by
  induction n with
  | zero => simpa [matrixDesign] using (Matrix.PosSemidef.zero : (0 : Matrix ι ι ℝ).PosSemidef)
  | succ n ih =>
    have he : matrixDesign C (n + 1) - 1 = (matrixDesign C n - 1) + C n := by
      simp only [matrixDesign, sum_range_succ]; abel
    rw [he]
    exact ih.add (hC n)

theorem matrixDesign_posDef (C : ℕ → Matrix ι ι ℝ)
    (hC : ∀ t, (C t).PosSemidef) (n : ℕ) : (matrixDesign C n).PosDef := by
  convert Matrix.PosDef.one.add_posSemidef (matrixDesign_base_psd C hC n) using 1
  abel

theorem matrixDesign_trace_budget (C : ℕ → Matrix ι ι ℝ)
    (hC : ∀ t, (C t).PosSemidef)
    (hu : ∀ t, ((1 / 2 : ℝ) • (1 : Matrix ι ι ℝ) - C t).PosSemidef) (u n : ℕ) :
    (∑ s ∈ range n, ((matrixDesign C (u + s))⁻¹ * C (u + s)).trace) ≤
      (3 / 2 : ℝ) * (Real.log (matrixDesign C (u + n)).det - Real.log (matrixDesign C u).det) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ]
    have ht := actual_trace_logdet_step (matrixDesign C (u + n)) (C (u + n))
      (matrixDesign_posDef C hC _) (matrixDesign_base_psd C hC _) (hC _) (hu _)
    have he : matrixDesign C (u + n) + C (u + n) = matrixDesign C (u + (n + 1)) := by
      change matrixDesign C (u + n) + C (u + n) = matrixDesign C ((u + n) + 1)
      simp only [matrixDesign, sum_range_succ]; abel
    rw [he] at ht
    linarith

variable {η : Type*} [Fintype η] [DecidableEq η]

/-- A fixed finite orthonormal chart of the actual zero-sum tangent subspace. -/
def TangentChart (Q : Matrix ι η ℝ) : Prop :=
  Qᴴ * Q = 1 ∧
  (∀ y : η → ℝ, (∑ i, (Q *ᵥ y) i) = 0) ∧
  (∀ x : ι → ℝ, (∑ i, x i) = 0 → Q *ᵥ (Qᴴ *ᵥ x) = x)

/-- The actual categorical covariance in a fixed orthonormal coordinate chart. -/
def coordinateCovariance (Q : Matrix ι η ℝ) (p : ι → ℝ) : Matrix η η ℝ :=
  Qᴴ * Part2.CNDPhysical.covariance p * Q

theorem coordinateCovariance_psd (Q : Matrix ι η ℝ) (p : ι → ℝ)
    (hp : p ∈ Part2.CND.simplex) : (coordinateCovariance Q p).PosSemidef :=
  (Part2.CNDPhysical.covariance_posSemidef p hp).conjTranspose_mul_mul_same Q

theorem coordinateCovariance_half_psd (Q : Matrix ι η ℝ) (hQ : Qᴴ * Q = 1)
    (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    ((1 / 2 : ℝ) • (1 : Matrix η η ℝ) - coordinateCovariance Q p).PosSemidef := by
  have h := (covariance_half_psd p hp).conjTranspose_mul_mul_same Q
  simpa only [coordinateCovariance, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, hQ] using h

def coordinateDesign (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ) (n : ℕ) : Matrix η η ℝ :=
  matrixDesign (fun t => coordinateCovariance Q (p t)) n

def coordinateLogdet (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ) (n : ℕ) : ℝ :=
  Real.log (coordinateDesign Q p n).det

def coordinateInverseKernel (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ) (n : ℕ) : Matrix ι ι ℝ :=
  Q * (coordinateDesign Q p n)⁻¹ * Qᴴ

def coordinateResistance (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ) (n : ℕ) : ι → ι → ℝ :=
  Part2.CND.gramDistance (coordinateInverseKernel Q p n)

theorem coordinateDesign_posDef (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) : (coordinateDesign Q p n).PosDef :=
  matrixDesign_posDef _ (fun t => coordinateCovariance_psd Q (p t) (hp t)) n

theorem coordinateDesign_eq_compression (Q : Matrix ι η ℝ) (hQ : Qᴴ * Q = 1)
    (p : ℕ → ι → ℝ) (n : ℕ) :
    coordinateDesign Q p n = Qᴴ * Part2.CNDPhysical.information p n * Q := by
  simp only [coordinateDesign, matrixDesign, Part2.CNDPhysical.information,
    Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hQ,
    Matrix.mul_sum, Matrix.sum_mul, coordinateCovariance]

theorem coordinateInverseKernel_psd (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) : (coordinateInverseKernel Q p n).PosSemidef :=
  (coordinateDesign_posDef Q p hp n).inv.posSemidef.mul_mul_conjTranspose_same Q

theorem information_preserves_zero_sum (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ) (x : ι → ℝ)
    (hx : (∑ i, x i) = 0) : (∑ i, (Part2.CNDPhysical.information p n *ᵥ x) i) = 0 := by
  have hsym (i j : ι) : Part2.CNDPhysical.information p n i j =
      Part2.CNDPhysical.information p n j i := by
    simpa using (Part2.CNDPhysical.information_posDef p hp n).isHermitian.apply j i
  have hcol (j : ι) : (∑ i, Part2.CNDPhysical.information p n i j) = 1 := by
    calc
      _ = ∑ i, Part2.CNDPhysical.information p n j i := sum_congr rfl (fun i _ => hsym i j)
      _ = 1 := by
        simpa [Matrix.mulVec, dotProduct] using congr_fun
          (Part2.CNDPhysical.information_mul_ones p hp n) j
  change (∑ i, ∑ j, Part2.CNDPhysical.information p n i j * x j) = 0
  rw [sum_comm]
  simp_rw [← sum_mul, hcol, one_mul]
  exact hx

/-- The coordinate inverse solves precisely the original Pi+sum(C) equation on H. -/
theorem coordinate_inverse_on_tangent (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (n : ℕ)
    (b : ι → ℝ) (hb : (∑ i, b i) = 0) :
    coordinateInverseKernel Q p n *ᵥ b = Part2.CNDPhysical.inverseInformation p n *ᵥ b := by
  let y := (coordinateDesign Q p n)⁻¹ *ᵥ (Qᴴ *ᵥ b)
  let w := Q *ᵥ y
  have hw : (∑ i, w i) = 0 := hQ.2.1 y
  have hzero := information_preserves_zero_sum p hp n w hw
  have hcomp : Qᴴ *ᵥ (Part2.CNDPhysical.information p n *ᵥ w) = Qᴴ *ᵥ b := by
    calc
      _ = (Qᴴ * Part2.CNDPhysical.information p n * Q) *ᵥ y := by
        simp only [w, Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = coordinateDesign Q p n *ᵥ y := by rw [← coordinateDesign_eq_compression Q hQ.1]
      _ = _ := by
        dsimp [y]
        rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
          ((Matrix.isUnit_iff_isUnit_det _).mp (coordinateDesign_posDef Q p hp n).isUnit),
          Matrix.one_mulVec]
  have hsol : Part2.CNDPhysical.information p n *ᵥ w = b := by
    calc
      _ = Q *ᵥ (Qᴴ *ᵥ (Part2.CNDPhysical.information p n *ᵥ w)) := (hQ.2.2 _ hzero).symm
      _ = Q *ᵥ (Qᴴ *ᵥ b) := by rw [hcomp]
      _ = b := hQ.2.2 b hb
  have htan : Part2.CNDPhysical.tangentInformation p n w = b := by
    rw [Part2.CNDPhysical.tangentInformation_on_zero_sum p n w hw]
    exact hsol
  have he := (Part2.CNDPhysical.inverse_tangent_direction p hp n b hb).2.2 w hw htan
  simpa only [coordinateInverseKernel, w, y, Matrix.mulVec_mulVec, Matrix.mul_assoc] using he

theorem coordinate_trace_budget (Q : Matrix ι η ℝ) (hQ : Qᴴ * Q = 1)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, ((coordinateDesign Q p (u + s))⁻¹ *
      coordinateCovariance Q (p (u + s))).trace) ≤
      (3 / 2 : ℝ) * (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u) :=
  matrixDesign_trace_budget _ (fun t => coordinateCovariance_psd Q (p t) (hp t))
    (fun t => coordinateCovariance_half_psd Q hQ (p t) (hp t)) u n

theorem trace_covariance (B : Matrix ι ι ℝ) (p : ι → ℝ) :
    (B * Part2.CNDPhysical.covariance p).trace =
      (∑ i, p i * B i i) - ∑ i, ∑ j, p i * p j * B i j := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Part2.CNDPhysical.covariance,
    mul_sub, sum_sub_distrib]
  congr 1
  · apply sum_congr rfl
    intro i _
    simp [mul_ite, Finset.sum_ite_eq', mul_comm]
  · apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    ring

theorem resistance_double_trace (B : Matrix ι ι ℝ) (p : ι → ℝ)
    (hp : p ∈ Part2.CND.simplex) :
    (∑ i, ∑ j, p i * p j * Part2.CND.gramDistance B i j) =
      2 * (B * Part2.CNDPhysical.covariance p).trace := by
  have ht (i j : ι) : p i * p j * Part2.CND.gramDistance B i j =
      (p i * B i i) * p j + p i * (p j * B j j) - 2 * (p i * p j * B i j) := by
    unfold Part2.CND.gramDistance
    ring
  simp_rw [ht, sum_sub_distrib, sum_add_distrib,
    ← Finset.mul_sum, ← Finset.sum_mul]
  rw [hp.2, trace_covariance]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  ring

theorem weighted_sqrt_budget {α : Type*} (s : Finset α) (w d : α → ℝ)
    (hw : ∀ a ∈ s, 0 ≤ w a) (hd : ∀ a ∈ s, 0 ≤ d a)
    (n D : ℝ) (hn : 0 ≤ n)
    (hmass : (∑ a ∈ s, w a) ≤ n / 2)
    (hinfo : (∑ a ∈ s, w a * d a) ≤ (3 / 2 : ℝ) * D) :
    (∑ a ∈ s, w a * Real.sqrt (d a)) ≤ Real.sqrt (3 * n * D / 4) := by
  have hwd : ∀ a ∈ s, 0 ≤ w a * d a := fun a ha => mul_nonneg (hw a ha) (hd a ha)
  have hCS := Finset.sum_sq_le_sum_mul_sum_of_sq_eq_mul s hw hwd
    (r := fun a => w a * Real.sqrt (d a)) (fun a ha => by
      rw [mul_pow, Real.sq_sqrt (hd a ha)]; ring)
  apply Real.le_sqrt_of_sq_le
  calc
    _ ≤ (∑ a ∈ s, w a) * ∑ a ∈ s, w a * d a := hCS
    _ ≤ (n / 2) * ∑ a ∈ s, w a * d a :=
      mul_le_mul_of_nonneg_right hmass (sum_nonneg hwd)
    _ ≤ (n / 2) * ((3 / 2 : ℝ) * D) :=
      mul_le_mul_of_nonneg_left hinfo (div_nonneg hn (by norm_num))
    _ = _ := by ring

theorem sum_time_pairs (n : ℕ) (f : ℕ × (ι × ι) → ℝ) :
    (∑ z ∈ (range n).product (univ.product univ), f z) =
      ∑ s ∈ range n, ∑ i, ∑ j, f (s, i, j) := by
  exact (Finset.sum_product (range n) (univ.product univ) f).trans
    (Finset.sum_congr rfl (fun s _ => Finset.sum_product univ univ (fun z => f (s, z))))

section OrderedPairs
variable [LinearOrder ι]

def pairSum (f : ι → ι → ℝ) : ℝ := ∑ i, ∑ j, if i < j then f i j else 0

theorem symmetric_pair_sum (f : ι → ι → ℝ)
    (hsym : ∀ i j, f i j = f j i) (hdiag : ∀ i, f i i = 0) :
    (∑ i, ∑ j, f i j) = 2 * pairSum f := by
  have ht (i j : ι) : f i j =
      (if i < j then f i j else 0) + (if j < i then f j i else 0) := by
    rcases lt_trichotomy i j with h | h | h
    · simp [h, not_lt.mpr h.le]
    · subst j; simp [hdiag]
    · simp [h, not_lt.mpr h.le, hsym i j]
  calc
    _ = (∑ i, ∑ j, if i < j then f i j else 0) +
        (∑ i, ∑ j, if j < i then f j i else 0) := by
      calc
        _ = ∑ i, ∑ j, ((if i < j then f i j else 0) +
              (if j < i then f j i else 0)) :=
          sum_congr rfl (fun i _ => sum_congr rfl (fun j _ => ht i j))
        _ = _ := by simp only [sum_add_distrib]
    _ = 2 * pairSum f := by
      rw [Finset.sum_comm (f := fun i j => if j < i then f j i else 0)]
      unfold pairSum
      ring

theorem actual_resistance_trace (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (t : ℕ) :
    pairSum (fun i j => p t i * p t j * Part2.CNDPhysical.resistance p t i j) =
      ((Part2.CNDPhysical.information p t)⁻¹ * Part2.CNDPhysical.covariance (p t)).trace := by
  have hgeo := Part2.CNDPhysical.actual_resistance_isCND p hp t
  have hs := symmetric_pair_sum
    (fun i j => p t i * p t j * Part2.CNDPhysical.resistance p t i j)
    (by intro i j; dsimp only; rw [hgeo.1 i j]; ring)
    (by intro i; dsimp only; rw [hgeo.2.1 i]; ring)
  have ht := resistance_double_trace ((Part2.CNDPhysical.information p t)⁻¹) (p t) (hp t)
  change (∑ i, ∑ j, p t i * p t j * Part2.CNDPhysical.resistance p t i j) = _ at ht
  linarith

theorem coordinate_resistance_nonneg (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (t : ℕ) (i j : ι) :
    0 ≤ coordinateResistance Q p t i j := by
  have hB := coordinateInverseKernel_psd Q p hp t
  have hs (i j : ι) : coordinateInverseKernel Q p t i j = coordinateInverseKernel Q p t j i := by
    simpa using hB.isHermitian.apply j i
  rw [coordinateResistance, Part2.CNDPhysical.gramDistance_energy _ hs i j]
  exact hB.2 _

theorem coordinateResistance_eq_actual (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (t : ℕ) (i j : ι) :
    coordinateResistance Q p t i j = Part2.CNDPhysical.resistance p t i j := by
  have hB := coordinateInverseKernel_psd Q p hp t
  have hs (i j : ι) : coordinateInverseKernel Q p t i j = coordinateInverseKernel Q p t j i := by
    simpa using hB.isHermitian.apply j i
  rw [coordinateResistance, Part2.CNDPhysical.gramDistance_energy _ hs i j,
    coordinate_inverse_on_tangent Q hQ p hp t _ (Part2.CNDPhysical.contrast_sum i j)]
  simp only [star_trivial]
  exact (Part2.CNDPhysical.actual_resistance_contrast_equation p hp t i j).2.2.symm

theorem coordinate_resistance_trace (Q : Matrix ι η ℝ) (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (t : ℕ) :
    pairSum (fun i j => p t i * p t j * coordinateResistance Q p t i j) =
      ((coordinateDesign Q p t)⁻¹ * coordinateCovariance Q (p t)).trace := by
  have hB := coordinateInverseKernel_psd Q p hp t
  have hsym (i j : ι) : coordinateResistance Q p t i j = coordinateResistance Q p t j i := by
    have hs := hB.isHermitian.apply i j
    simp only [Matrix.conjTranspose_apply, star_trivial] at hs
    unfold coordinateResistance Part2.CND.gramDistance
    rw [hs]
    ring
  have hs := symmetric_pair_sum
    (fun i j => p t i * p t j * coordinateResistance Q p t i j)
    (by intro i j; dsimp only; rw [hsym i j]; ring)
    (by intro i; dsimp only [coordinateResistance, Part2.CND.gramDistance]; ring)
  have ht := resistance_double_trace (coordinateInverseKernel Q p t) (p t) (hp t)
  change (∑ i, ∑ j, p t i * p t j * coordinateResistance Q p t i j) = _ at ht
  have htr : (coordinateInverseKernel Q p t * Part2.CNDPhysical.covariance (p t)).trace =
      ((coordinateDesign Q p t)⁻¹ * coordinateCovariance Q (p t)).trace := by
    unfold coordinateInverseKernel coordinateCovariance
    rw [Matrix.mul_assoc Q, Matrix.mul_assoc Q, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [htr] at ht
  linarith

theorem coordinate_resistance_information_budget (Q : Matrix ι η ℝ) (hQ : Qᴴ * Q = 1)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      coordinateResistance Q p (u + s) i j)) ≤
      (3 / 2 : ℝ) * (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u) := by
  simp_rw [coordinate_resistance_trace Q p hp]
  exact coordinate_trace_budget Q hQ p hp u n

/-- The exact resistance information inequality from CND-MAIN section 9. -/
theorem actual_resistance_information_budget (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      Part2.CNDPhysical.resistance p (u + s) i j)) ≤
      (3 / 2 : ℝ) * (actualLogdet p (u + n) - actualLogdet p u) := by
  simp_rw [actual_resistance_trace p hp]
  exact actual_information_trace_budget p hp u n

theorem pair_mass_le_half (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    pairSum (fun i j => p i * p j) ≤ 1 / 2 := by
  let f : ι → ι → ℝ := fun i j => if i = j then 0 else p i * p j
  have hs := symmetric_pair_sum f
    (by
      intro i j
      dsimp [f]
      by_cases h : i = j
      · subst j; simp
      · simp [h, Ne.symm h, mul_comm])
    (by intro i; simp [f])
  have hf : (∑ i, ∑ j, f i j) = 1 - ∑ i, (p i) ^ 2 := by
    have ht (i j : ι) : f i j = p i * p j - if i = j then p i * p j else 0 := by
      dsimp [f]; split_ifs <;> ring
    simp_rw [ht, sum_sub_distrib, Finset.sum_ite_eq, mem_univ, if_true,
      ← Finset.mul_sum]
    rw [hp.2]
    simp only [mul_one, ← pow_two]
    rw [hp.2]
  have hpairs : pairSum f = pairSum (fun i j => p i * p j) := by
    unfold pairSum
    apply sum_congr rfl
    intro i _
    apply sum_congr rfl
    intro j _
    by_cases h : i < j
    · simp [h, f, ne_of_lt h]
    · simp [h]
  rw [hpairs, hf] at hs
  have hsq := sum_nonneg (s := (univ : Finset ι)) (fun i _ => sq_nonneg (p i))
  linarith

/-- Finite weighted Cauchy--Schwarz; the matrix information premise is discharged below. -/
theorem pair_sqrt_from_information (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (r : ℕ → ι → ι → ℝ)
    (hr : ∀ t i j, 0 ≤ r t i j) (u n : ℕ) (D : ℝ)
    (hinfo : (∑ s ∈ range n, pairSum (fun i j =>
      p (u + s) i * p (u + s) j * r (u + s) i j)) ≤ (3 / 2 : ℝ) * D) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      Real.sqrt (r (u + s) i j))) ≤ Real.sqrt (3 * n * D / 4) := by
  let S : Finset (ℕ × (ι × ι)) := (range n).product (univ.product univ)
  let w : ℕ × (ι × ι) → ℝ := fun z =>
    if z.2.1 < z.2.2 then p (u + z.1) z.2.1 * p (u + z.1) z.2.2 else 0
  let d : ℕ × (ι × ι) → ℝ := fun z =>
    r (u + z.1) z.2.1 z.2.2
  have hw : ∀ z ∈ S, 0 ≤ w z := by
    intro z _
    dsimp [w]
    split_ifs
    · exact mul_nonneg ((hp _).1 _) ((hp _).1 _)
    · exact le_rfl
  have hd : ∀ z ∈ S, 0 ≤ d z := fun z _ => hr _ _ _
  have hm : (∑ z ∈ S, w z) ≤ (n : ℝ) / 2 := by
    change (∑ z ∈ (range n).product (univ.product univ), w z) ≤ _
    rw [sum_time_pairs n w]
    calc
      _ ≤ ∑ s ∈ range n, (1 / 2 : ℝ) := by
        apply sum_le_sum
        intro s _
        exact pair_mass_le_half (p (u + s)) (hp _)
      _ = _ := by simp; ring
  have hi : (∑ z ∈ S, w z * d z) ≤
      (3 / 2 : ℝ) * D := by
    change (∑ z ∈ (range n).product (univ.product univ), w z * d z) ≤ _
    rw [sum_time_pairs n (fun z => w z * d z)]
    simpa only [w, d, pairSum, ite_mul, zero_mul] using
      hinfo
  have h := weighted_sqrt_budget S w d hw hd n D (Nat.cast_nonneg n) hm hi
  change (∑ z ∈ (range n).product (univ.product univ), w z * Real.sqrt (d z)) ≤ _ at h
  rw [sum_time_pairs n (fun z => w z * Real.sqrt (d z))] at h
  simpa only [w, d, pairSum, ite_mul, zero_mul] using h

/-- The original constant sqrt(3*n*D/4), for all actual intervals and simplex sequences. -/
theorem actual_sqrt_resistance_information_budget (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      Real.sqrt (Part2.CNDPhysical.resistance p (u + s) i j))) ≤
      Real.sqrt (3 * n * (actualLogdet p (u + n) - actualLogdet p u) / 4) :=
  pair_sqrt_from_information p hp (Part2.CNDPhysical.resistance p)
    (Part2.CNDPhysical.actual_resistance_nonneg p hp) u n _
    (actual_resistance_information_budget p hp u n)

theorem coordinate_sqrt_resistance_information_budget (Q : Matrix ι η ℝ) (hQ : Qᴴ * Q = 1)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      Real.sqrt (coordinateResistance Q p (u + s) i j))) ≤
      Real.sqrt (3 * n * (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u) / 4) :=
  pair_sqrt_from_information p hp (coordinateResistance Q p)
    (coordinate_resistance_nonneg Q p hp) u n _
    (coordinate_resistance_information_budget Q hQ p hp u n)

/-- The section-9 resistance budget with the genuine determinant restricted to H. -/
theorem tangent_actual_resistance_information_budget (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      Part2.CNDPhysical.resistance p (u + s) i j)) ≤
      (3 / 2 : ℝ) * (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u) := by
  have h := coordinate_resistance_information_budget Q hQ.1 p hp u n
  simpa only [coordinateResistance_eq_actual Q hQ p hp] using h

/-- The section-9 square-root budget with the genuine determinant restricted to H. -/
theorem tangent_actual_sqrt_resistance_information_budget (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ℕ → ι → ℝ) (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    (∑ s ∈ range n, pairSum (fun i j => p (u + s) i * p (u + s) j *
      Real.sqrt (Part2.CNDPhysical.resistance p (u + s) i j))) ≤
      Real.sqrt (3 * n * (coordinateLogdet Q p (u + n) - coordinateLogdet Q p u) / 4) := by
  have h := coordinate_sqrt_resistance_information_budget Q hQ.1 p hp u n
  simpa only [coordinateResistance_eq_actual Q hQ p hp] using h

end OrderedPairs
end Part2.CNDInformation

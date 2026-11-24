import TangentChart

/-! The true interval log determinant has the original K-1 dimensional upper bound. -/
noncomputable section
namespace Part2.CNDInformation
open Matrix Finset
open scoped Matrix BigOperators
variable {ι η : Type*} [Fintype ι] [DecidableEq ι] [Fintype η] [DecidableEq η]

theorem pd_logdet_tangent_bound (M : Matrix η η ℝ) (hM : M.PosDef)
    (a : ℝ) (ha : 0 < a) :
    Real.log M.det ≤ (Fintype.card η : ℝ) * Real.log a + M.trace / a - Fintype.card η := by
  have hlog (i : η) : Real.log (hM.isHermitian.eigenvalues i) ≤
      Real.log a + hM.isHermitian.eigenvalues i / a - 1 := by
    have h := Real.log_le_sub_one_of_pos (div_pos (hM.eigenvalues_pos i) ha)
    rw [Real.log_div (hM.eigenvalues_pos i).ne' ha.ne'] at h
    linarith
  have hd : Real.log M.det = ∑ i, Real.log (hM.isHermitian.eigenvalues i) := by
    rw [hM.isHermitian.det_eq_prod_eigenvalues]
    simpa using Real.log_prod (univ : Finset η) hM.isHermitian.eigenvalues
      (fun i _ => (hM.eigenvalues_pos i).ne')
  rw [hd, hM.isHermitian.trace_eq_sum_eigenvalues]
  simpa only [sum_add_distrib, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul,
    mul_one, ← sum_div, RCLike.ofReal_real_eq_id, id_eq] using
      sum_le_sum (s := (univ : Finset η)) (fun i _ => hlog i)

theorem normalized_increment_exists (V C : Matrix η η ℝ) (hV : V.PosDef)
    (hbase : (V - 1).PosSemidef) (hC : C.PosSemidef) :
    ∃ A : Matrix η η ℝ, A.PosSemidef ∧ A.trace ≤ C.trace ∧
      Real.log ((V+C).det) - Real.log V.det = Real.log ((1+A).det) := by
  obtain ⟨R, hR, hRR⟩ := exists_symmetric_sqrt C hC
  let A := R * V⁻¹ * R
  have hA : A.PosSemidef := by
    simpa only [A, hR.eq] using hV.inv.posSemidef.mul_mul_conjTranspose_same R
  have hdiff : (C-A).PosSemidef := by
    have h := (inverse_le_identity V hV hbase).mul_mul_conjTranspose_same R
    simpa only [hR.eq, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hRR, A] using h
  have htr := hdiff.trace_nonneg
  rw [Matrix.trace_sub] at htr
  have hfactor : V * (1 + V⁻¹ * C) = V+C := by
    rw [Matrix.mul_add, Matrix.mul_one, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv V ((Matrix.isUnit_iff_isUnit_det V).mp hV.isUnit), Matrix.one_mul]
  have hdetA : (1+A).det = (1 + V⁻¹ * C).det := by
    dsimp [A]
    rw [Matrix.mul_assoc R V⁻¹ R, Matrix.det_one_add_mul_comm R (V⁻¹ * R), Matrix.mul_assoc V⁻¹ R R, hRR]
  have hd : V.det * (1+A).det = (V+C).det := by
    rw [hdetA, ← Matrix.det_mul, hfactor]
  have hinc := (Matrix.PosDef.one.add_posSemidef hA).det_pos
  have he := Real.log_mul hV.det_pos.ne' hinc.ne'
  rw [hd] at he
  exact ⟨A, hA, by linarith, by linarith⟩

theorem actual_logdet_increment_le_trace_scale (V C : Matrix η η ℝ) (hV : V.PosDef)
    (hbase : (V-1).PosSemidef) (hC : C.PosSemidef) (q : ℝ) (hq : 0 ≤ q)
    (htr : C.trace ≤ (Fintype.card η : ℝ) * q) :
    Real.log ((V+C).det) - Real.log V.det ≤
      (Fintype.card η : ℝ) * Real.log (1+q) := by
  obtain ⟨A, hA, hAC, hdet⟩ := normalized_increment_exists V C hV hbase hC
  have hpos : 0 < 1+q := by linarith
  have hm := pd_logdet_tangent_bound (1+A) (Matrix.PosDef.one.add_posSemidef hA) (1+q) hpos
  have ht : (1+A).trace / (1+q) ≤ (Fintype.card η : ℝ) := by
    apply (div_le_iff₀ hpos).mpr
    rw [Matrix.trace_add, Matrix.trace_one]
    nlinarith
  rw [hdet]
  linarith

theorem covariance_trace (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    (Part2.CNDPhysical.covariance p).trace = 1 - ∑ i, (p i)^2 := by
  simp [Matrix.trace, Matrix.diag_apply, Part2.CNDPhysical.covariance,
    sum_sub_distrib, hp.2, pow_two]

theorem covariance_trace_le_dimension [Nonempty ι] (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    (Part2.CNDPhysical.covariance p).trace ≤ ((Fintype.card ι : ℝ)-1) / Fintype.card ι := by
  have hcs := sum_mul_sq_le_sq_mul_sq (univ : Finset ι) p (fun _ => (1 : ℝ))
  simp only [mul_one, one_pow, sum_const, card_univ, nsmul_eq_mul, mul_one, hp.2] at hcs
  have hK : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  rw [covariance_trace p hp]
  apply (le_div_iff₀ hK).mpr
  nlinarith

theorem tangent_compressed_covariance_trace (Q : Matrix ι η ℝ) (hQ : TangentChart Q)
    (p : ι → ℝ) (hp : p ∈ Part2.CND.simplex) :
    (coordinateCovariance Q p).trace = (Part2.CNDPhysical.covariance p).trace := by
  have hcol (j : ι) : (∑ i, Part2.CNDPhysical.covariance p i j) = 0 := by
    simp [Part2.CNDPhysical.covariance, sum_sub_distrib, ← sum_mul, hp.2]
  have hproj : Q * Qᴴ * Part2.CNDPhysical.covariance p = Part2.CNDPhysical.covariance p := by
    rw [Matrix.mul_assoc]
    ext i j
    have h := congr_fun (hQ.2.2 (fun k => Part2.CNDPhysical.covariance p k j) (hcol j)) i
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct] using h
  rw [coordinateCovariance, Matrix.trace_mul_cycle, hproj]

theorem canonical_logdet_interval_upper [Nonempty ι] (p : ℕ → ι → ℝ)
    (hp : ∀ t, p t ∈ Part2.CND.simplex) (u n : ℕ) :
    coordinateLogdet (canonicalChart ι) p (u+n) - coordinateLogdet (canonicalChart ι) p u ≤
      ((Fintype.card ι : ℝ)-1) * Real.log (1 + (n : ℝ) / Fintype.card ι) := by
  let Q := canonicalChart ι
  let C : Matrix (TangentIndex ι) (TangentIndex ι) ℝ :=
    ∑ s ∈ range n, coordinateCovariance Q (p (u+s))
  have hC : C.PosSemidef := by
    dsimp [C]
    apply Finset.sum_induction
    · intro a b ha hb; exact ha.add hb
    · exact Matrix.PosSemidef.zero
    · intro s _; exact coordinateCovariance_psd Q _ (hp _)
  have hV := coordinateDesign_posDef Q p hp u
  have hbase := matrixDesign_base_psd (fun t => coordinateCovariance Q (p t))
    (fun t => coordinateCovariance_psd Q _ (hp t)) u
  have hdim : (Fintype.card (TangentIndex ι) : ℝ) = (Fintype.card ι : ℝ)-1 := by
    simp only [TangentIndex, Fintype.card_fin, tangentSpace_finrank]
    have hNat : 1 ≤ Fintype.card ι := Nat.succ_le_of_lt (show 0 < Fintype.card ι from Fintype.card_pos)
    simpa only [Nat.cast_one] using (Nat.cast_sub (R := ℝ) hNat)
  have hK : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have htr : C.trace ≤ (Fintype.card (TangentIndex ι) : ℝ) * ((n : ℝ) / Fintype.card ι) := by
    dsimp [C]
    rw [Matrix.trace_sum]
    calc
      _ ≤ ∑ s ∈ range n, (((Fintype.card ι : ℝ)-1) / Fintype.card ι) := by
        apply sum_le_sum
        intro s _
        rw [tangent_compressed_covariance_trace Q canonicalChart_is_tangentChart (p (u+s)) (hp (u+s))]
        exact covariance_trace_le_dimension _ (hp _)
      _ = _ := by simp only [sum_const, card_range, nsmul_eq_mul, hdim]; ring
  have he : coordinateDesign Q p u + C = coordinateDesign Q p (u+n) := by
    simp [coordinateDesign, matrixDesign, C, sum_range_add, add_assoc]
  have ht := actual_logdet_increment_le_trace_scale _ C hV hbase hC
    ((n : ℝ)/Fintype.card ι) (div_nonneg (Nat.cast_nonneg _) hK.le) htr
  rw [he, hdim] at ht
  exact ht

end Part2.CNDInformation

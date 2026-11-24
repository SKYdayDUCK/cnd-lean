import Part2.CNDPhysical
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! Finite Schoenberg closure, proved from the actual CND quadratic inequality. -/

noncomputable section
namespace Part2.CNDSaturation
open scoped BigOperators Matrix Topology
open Filter
open Part2.CND
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def IsPSD (A : ι → ι → ℝ) : Prop :=
  (∀ i j, A i j = A j i) ∧ ∀ x, 0 ≤ quadratic A x

theorem isPSD_iff_matrix (A : ι → ι → ℝ) : IsPSD A ↔ Matrix.PosSemidef A := by
  constructor
  · rintro ⟨hs, hq⟩
    constructor
    · ext i j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using hs j i
    · intro x
      rw [← Part2.CNDPhysical.quadratic_eq_dot]
      exact hq x
  · rintro ⟨hs, hq⟩
    constructor
    · intro i j
      simpa only [Matrix.conjTranspose_apply, star_trivial] using
        (congr_fun (congr_fun hs j) i)
    · intro x
      rw [Part2.CNDPhysical.quadratic_eq_dot]
      exact hq x

theorem psd_coordinateGram (v : ι → ι → ℝ) : IsPSD (coordinateGram v) := by
  constructor
  · intro i j
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  · intro x
    rw [coordinateGram_quadratic]
    exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- The spectral theorem gives actual real coordinates, including singular PSD matrices. -/
theorem psd_gram_representation (A : ι → ι → ℝ) (hA : IsPSD A) :
    ∃ v : ι → ι → ℝ, A = coordinateGram v := by
  have hM := (isPSD_iff_matrix A).1 hA
  let U : Matrix ι ι ℝ := hM.1.eigenvectorUnitary
  let lam : ι → ℝ := hM.1.eigenvalues
  refine ⟨fun i k => U i k * Real.sqrt (lam k), ?_⟩
  funext i j
  have hspec := congr_fun (congr_fun hM.1.spectral_theorem i) j
  change A i j = ((U * Matrix.diagonal lam) * star U) i j at hspec
  rw [hspec, Matrix.mul_apply]
  unfold coordinateGram
  apply Finset.sum_congr rfl
  intro k _
  rw [Matrix.mul_diagonal, Matrix.star_apply, star_trivial]
  have hsq : Real.sqrt (lam k) ^ 2 = lam k := Real.sq_sqrt (hM.eigenvalues_nonneg k)
  dsimp only
  calc
    U i k * lam k * U j k = (U i k * U j k) * lam k := by ring
    _ = (U i k * U j k) * Real.sqrt (lam k) ^ 2 := by rw [hsq]
    _ = _ := by ring

theorem gram_product_quadratic (v : ι → ι → ℝ) (B : ι → ι → ℝ) (x : ι → ℝ) :
    quadratic (fun i j => coordinateGram v i j * B i j) x =
      ∑ k, quadratic B (fun i => x i * v i k) := by
  unfold quadratic coordinateGram
  calc
    _ = ∑ i, ∑ j, ∑ k, (x i * v i k) * (x j * v j k) * B i j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      dsimp only
      rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = ∑ i, ∑ k, ∑ j, (x i * v i k) * (x j * v j k) * B i j := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = _ := Finset.sum_comm

/-- Schur positivity is established here, rather than used as a kernel premise. -/
theorem psd_product (A B : ι → ι → ℝ) (hA : IsPSD A) (hB : IsPSD B) :
    IsPSD (fun i j => A i j * B i j) := by
  constructor
  · intro i j
    dsimp only
    rw [hA.1 i j, hB.1 i j]
  · intro x
    obtain ⟨v, hv⟩ := psd_gram_representation A hA
    rw [hv, gram_product_quadratic]
    exact Finset.sum_nonneg (fun k _ => hB.2 _)

theorem psd_one : IsPSD (fun (_ _ : ι) => 1) := by
  constructor
  · intros; rfl
  · intro x
    have h : quadratic (fun (_ _ : ι) => 1) x = (∑ i, x i) ^ 2 := by
      simp only [quadratic, mul_one, ← Finset.mul_sum, ← Finset.sum_mul, pow_two]
    rw [h]
    exact sq_nonneg _

theorem psd_scale (A : ι → ι → ℝ) (hA : IsPSD A) (a : ℝ) (ha : 0 ≤ a) :
    IsPSD (fun i j => a * A i j) := by
  constructor
  · intro i j; dsimp only; rw [hA.1 i j]
  · intro x
    have h : quadratic (fun i j => a * A i j) x = a * quadratic A x := by
      unfold quadratic
      simp_rw [show ∀ i j, x i * x j * (a * A i j) = a * (x i * x j * A i j) by
        intros; ring, ← Finset.mul_sum]
    rw [h]
    exact mul_nonneg ha (hA.2 x)

theorem psd_add (A B : ι → ι → ℝ) (hA : IsPSD A) (hB : IsPSD B) :
    IsPSD (fun i j => A i j + B i j) := by
  constructor
  · intro i j; dsimp only; rw [hA.1 i j, hB.1 i j]
  · intro x
    simp only [quadratic, mul_add, Finset.sum_add_distrib]
    exact add_nonneg (hA.2 x) (hB.2 x)

theorem psd_power (A : ι → ι → ℝ) (hA : IsPSD A) (n : ℕ) :
    IsPSD (fun i j => A i j ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (psd_one : IsPSD (fun (_ _ : ι) => 1))
  | succ n ih => simpa only [pow_succ] using psd_product _ _ ih hA

theorem quadratic_tendsto {α : Type*} {l : Filter α} (A : α → ι → ι → ℝ)
    (B : ι → ι → ℝ) (h : ∀ i j, Tendsto (fun n => A n i j) l (𝓝 (B i j)))
    (x : ι → ℝ) : Tendsto (fun n => quadratic (A n) x) l (𝓝 (quadratic B x)) := by
  exact tendsto_finset_sum _ (fun i _ => tendsto_finset_sum _
    (fun j _ => tendsto_const_nhds.mul (h i j)))

theorem psd_limit {α : Type*} {l : Filter α} [l.NeBot] (A : α → ι → ι → ℝ)
    (B : ι → ι → ℝ) (hA : ∀ n, IsPSD (A n))
    (h : ∀ i j, Tendsto (fun n => A n i j) l (𝓝 (B i j))) : IsPSD B := by
  constructor
  · intro i j
    exact tendsto_nhds_unique (h i j) ((h j i).congr (fun n => (hA n).1 j i))
  · intro x
    exact ge_of_tendsto (quadratic_tendsto A B h x) (Filter.Eventually.of_forall (fun n => (hA n).2 x))

/-- Entrywise exponentiation of a real PSD matrix is PSD. -/
theorem psd_exp (A : ι → ι → ℝ) (hA : IsPSD A) :
    IsPSD (fun i j => Real.exp (A i j)) := by
  let Q : ℕ → ι → ι → ℝ := fun n i j => (1 + A i j / (n : ℝ)) ^ n
  apply psd_limit (l := atTop) Q _
  · intro n
    apply psd_power
    have hs := psd_scale A hA ((n : ℝ)⁻¹) (inv_nonneg.mpr (Nat.cast_nonneg n))
    simpa only [div_eq_mul_inv, mul_comm] using psd_add _ _ psd_one hs
  · intro i j
    exact Real.tendsto_one_add_div_pow_exp _

def centeredGram (D : ι → ι → ℝ) (o i j : ι) : ℝ :=
  (D i o + D j o - D i j) / 2

theorem centeredGram_psd (D : ι → ι → ℝ) (hD : IsCND D) (o : ι) :
    IsPSD (centeredGram D o) := by
  constructor
  · intro i j
    dsimp [centeredGram]
    rw [hD.1 i j]
    ring
  · intro x
    let s : ℝ := ∑ i, x i
    let y : ι → ℝ := fun i => x i - if i = o then s else 0
    have hy : (∑ i, y i) = 0 := by simp [y, Finset.sum_sub_distrib, s]
    have hq := hD.2.2 y hy
    have hid : quadratic D y = -2 * quadratic (centeredGram D o) x := by
      have hd := hD.2.1 o
      unfold quadratic centeredGram
      dsimp [y]
      simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ite_mul, mul_ite, zero_mul, mul_zero]
      simp only [Finset.sum_ite_irrel, Finset.sum_const_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, hd, mul_zero]
      simp_rw [hD.1 o]
      have hterm (i j : ι) : x i * x j * ((D i o + D j o - D i j) / 2) =
          (x i * D i o) * x j / 2 + x i * (x j * D j o) / 2 -
            (x i * x j * D i j) / 2 := by ring
      simp_rw [hterm]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.sum_div, ← Finset.mul_sum, ← Finset.sum_mul]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, hd, mul_zero]
      simp only [sub_zero]
      have hlin : (∑ i, x i * s * D i o) = s * ∑ i, x i * D i o := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      rw [hlin]
      have hlin' : (∑ i, s * x i * D i o) = s * ∑ i, x i * D i o := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros
        ring
      rw [hlin']
      dsimp [s]
      ring
    rw [hid] at hq
    linarith

theorem centeredGram_distance (D : ι → ι → ℝ) (hD : IsCND D) (o : ι) :
    gramDistance (centeredGram D o) = D := by
  funext i j
  simp only [gramDistance, centeredGram, hD.2.1]
  ring

/-- Every finite symmetric zero-diagonal CND matrix has actual Euclidean coordinates. -/
theorem cnd_squaredDistance_representation (D : ι → ι → ℝ) (hD : IsCND D) :
    ∃ v : ι → ι → ℝ, D = squaredDistance v := by
  by_cases hn : Nonempty ι
  · let o : ι := Classical.choice hn
    obtain ⟨v, hv⟩ := psd_gram_representation _ (centeredGram_psd D hD o)
    refine ⟨v, ?_⟩
    rw [squaredDistance_eq_gramDistance, ← hv, centeredGram_distance D hD o]
  · refine ⟨fun _ _ => 0, ?_⟩
    funext i
    exact (hn ⟨i⟩).elim

theorem cnd_nonneg (D : ι → ι → ℝ) (hD : IsCND D) (i j : ι) : 0 ≤ D i j := by
  obtain ⟨v, rfl⟩ := cnd_squaredDistance_representation D hD
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem psd_diagonal_conjugate (A : ι → ι → ℝ) (hA : IsPSD A) (w : ι → ℝ) :
    IsPSD (fun i j => w i * w j * A i j) := by
  constructor
  · intro i j; dsimp only; rw [hA.1 i j]; ring
  · intro x
    convert hA.2 (fun i => x i * w i) using 1
    unfold quadratic
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring

/-- Gaussian PSD for the actual squared distance of an arbitrary PSD Gram matrix. -/
theorem gaussian_gram_psd (A : ι → ι → ℝ) (hA : IsPSD A) (t : ℝ) (ht : 0 ≤ t) :
    IsPSD (fun i j => Real.exp (-t * gramDistance A i j)) := by
  have he := psd_exp _ (psd_scale A hA (2 * t) (by positivity))
  have hc := psd_diagonal_conjugate _ he (fun i => Real.exp (-t * A i i))
  convert hc using 1
  funext i j
  simp only [← Real.exp_add]
  congr 1
  unfold gramDistance
  ring

/-- Finite Schoenberg theorem with no unproved Gaussian/embedding premise. -/
theorem gaussian_cnd_psd (D : ι → ι → ℝ) (hD : IsCND D) (t : ℝ) (ht : 0 ≤ t) :
    IsPSD (fun i j => Real.exp (-t * D i j)) := by
  obtain ⟨v, rfl⟩ := cnd_squaredDistance_representation D hD
  rw [squaredDistance_eq_gramDistance]
  exact gaussian_gram_psd _ (psd_coordinateGram v) t ht

theorem cnd_of_one_sub_psd (A : ι → ι → ℝ) (hA : IsPSD A)
    (hd : ∀ i, A i i = 1) : IsCND (fun i j => 1 - A i j) := by
  refine ⟨fun i j => by dsimp only; rw [hA.1 i j],
    fun i => by dsimp only; rw [hd i]; ring, ?_⟩
  intro x hx
  have hc : quadratic (fun (_ _ : ι) => 1) x = 0 := by
    simp only [quadratic, mul_one, ← Finset.mul_sum, hx, mul_zero, Finset.sum_const_zero]
  have hq : quadratic (fun i j => 1 - A i j) x = -quadratic A x := by
    simp only [quadratic, mul_sub, mul_one, Finset.sum_sub_distrib] at hc ⊢
    rw [hc]
    ring
  rw [hq]
  exact neg_nonpos.mpr (hA.2 x)

theorem cnd_scale (D : ι → ι → ℝ) (hD : IsCND D) (a : ℝ) (ha : 0 ≤ a) :
    IsCND (fun i j => a * D i j) := by
  refine ⟨fun i j => by dsimp only; rw [hD.1 i j],
    fun i => by dsimp only; rw [hD.2.1 i, mul_zero], ?_⟩
  intro x hx
  have hq : quadratic (fun i j => a * D i j) x = a * quadratic D x := by
    unfold quadratic
    simp_rw [show ∀ i j, x i * x j * (a * D i j) = a * (x i * x j * D i j) by
      intros; ring, ← Finset.mul_sum]
  rw [hq]
  exact mul_nonpos_of_nonneg_of_nonpos ha (hD.2.2 x hx)

theorem cnd_add (D E : ι → ι → ℝ) (hD : IsCND D) (hE : IsCND E) :
    IsCND (fun i j => D i j + E i j) := by
  refine ⟨fun i j => by dsimp only; rw [hD.1 i j, hE.1 i j],
    fun i => by dsimp only; rw [hD.2.1 i, hE.2.1 i, add_zero], ?_⟩
  intro x hx
  simp only [quadratic, mul_add, Finset.sum_add_distrib]
  exact add_nonpos (hD.2.2 x hx) (hE.2.2 x hx)

/-- Genuine exponential saturation closure for any finite CND input. -/
theorem exponential_saturation_isCND (D : ι → ι → ℝ) (hD : IsCND D)
    (C t : ℝ) (hC : 0 ≤ C) (ht : 0 ≤ t) :
    IsCND (fun i j => C * (1 - Real.exp (-t * D i j))) := by
  apply cnd_scale _ _ C hC
  apply cnd_of_one_sub_psd _ (gaussian_cnd_psd D hD t ht)
  intro i
  rw [hD.2.1 i, mul_zero, Real.exp_zero]

end Part2.CNDSaturation

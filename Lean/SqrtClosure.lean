import GaussianClosure
import Mathlib.Topology.Order.MonotoneConvergence

/-! Entrywise square-root closure via positive Schur iteration and a derivative limit. -/

noncomputable section
namespace Part2.CNDSaturation
open scoped BigOperators Matrix Topology
open Filter
open Part2.CND
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def rootIter : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, z => (z + rootIter n z ^ 2) / 2

theorem rootIter_bounds (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) (n : ℕ) :
    0 ≤ rootIter n z ∧ rootIter n z ≤ 1 := by
  induction n with
  | zero => simp [rootIter]
  | succ n ih =>
    simp only [rootIter]
    constructor
    · positivity
    · nlinarith [sq_nonneg (rootIter n z), mul_self_le_mul_self ih.1 ih.2]

theorem rootIter_mono (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Monotone (fun n => rootIter n z) := by
  apply monotone_nat_of_le_succ
  intro n
  induction n with
  | zero => simp only [rootIter]; positivity
  | succ n ih =>
    have hn := (rootIter_bounds z hz hz1 n).1
    have hn1 := (rootIter_bounds z hz hz1 (n + 1)).1
    change (z + rootIter n z ^ 2) / 2 ≤ (z + rootIter (n + 1) z ^ 2) / 2
    nlinarith [mul_self_le_mul_self hn ih]

/-- The PSD polynomial iteration selects the smaller fixed point, including z=0 and z=1. -/
theorem rootIter_tendsto (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    Tendsto (fun n => rootIter n z) atTop (𝓝 (1 - Real.sqrt (1 - z))) := by
  let L : ℝ := ⨆ n, rootIter n z
  have hb : BddAbove (Set.range (fun n => rootIter n z)) :=
    ⟨1, by rintro _ ⟨n, rfl⟩; exact (rootIter_bounds z hz hz1 n).2⟩
  have hlim : Tendsto (fun n => rootIter n z) atTop (𝓝 L) :=
    tendsto_atTop_ciSup (rootIter_mono z hz hz1) hb
  have hL0 : 0 ≤ L := by
    simpa only [L, rootIter] using le_ciSup hb 0
  have hL1 : L ≤ 1 := ciSup_le (fun n => (rootIter_bounds z hz hz1 n).2)
  have hlim' : Tendsto (fun n => rootIter (n + 1) z) atTop (𝓝 L) :=
    hlim.comp (tendsto_add_atTop_nat 1)
  have heq : L = (z + L ^ 2) / 2 := by
    apply tendsto_nhds_unique hlim'
    simpa only [rootIter] using (tendsto_const_nhds.add (hlim.pow 2)).div_const 2
  have hsq : (1 - L) ^ 2 = 1 - z := by nlinarith [heq]
  have hroot : Real.sqrt (1 - z) = 1 - L := by
    rw [← hsq, Real.sqrt_sq (by linarith)]
  have hL : L = 1 - Real.sqrt (1 - z) := by linarith
  rwa [← hL]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem psd_rootIter (A : ι → ι → ℝ) (hA : IsPSD A) (n : ℕ) :
    IsPSD (fun i j => rootIter n (A i j)) := by
  induction n with
  | zero =>
    simpa only [rootIter, zero_mul] using psd_scale A hA 0 (le_refl 0)
  | succ n ih =>
    have h := psd_scale _ (psd_add _ _ hA (psd_power _ ih 2)) (1 / 2) (by norm_num)
    simpa only [rootIter, div_eq_mul_inv, one_mul, mul_comm] using h

theorem psd_complement_sqrt (A : ι → ι → ℝ) (hA : IsPSD A)
    (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i j, A i j ≤ 1) :
    IsPSD (fun i j => 1 - Real.sqrt (1 - A i j)) := by
  apply psd_limit (l := atTop) (fun n i j => rootIter n (A i j)) _
  · exact psd_rootIter A hA
  · exact fun i j => rootIter_tendsto _ (h0 i j) (h1 i j)

theorem cnd_sqrt_one_sub (A : ι → ι → ℝ) (hA : IsPSD A)
    (h0 : ∀ i j, 0 ≤ A i j) (h1 : ∀ i j, A i j ≤ 1) (hd : ∀ i, A i i = 1) :
    IsCND (fun i j => Real.sqrt (1 - A i j)) := by
  have h := cnd_of_one_sub_psd _ (psd_complement_sqrt A hA h0 h1)
    (fun i => by rw [hd i, sub_self, Real.sqrt_zero, sub_zero])
  simpa only [sub_sub_cancel] using h

theorem cnd_limit {α : Type*} {l : Filter α} [l.NeBot] (A : α → ι → ι → ℝ)
    (B : ι → ι → ℝ) (hA : ∀ n, IsCND (A n))
    (h : ∀ i j, Tendsto (fun n => A n i j) l (𝓝 (B i j))) : IsCND B := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j
    exact tendsto_nhds_unique (h i j) ((h j i).congr (fun n => (hA n).1 j i))
  · intro i
    exact tendsto_nhds_unique (h i i)
      (tendsto_const_nhds.congr (fun n => ((hA n).2.1 i).symm))
  · intro x hx
    exact le_of_tendsto (quadratic_tendsto A B h x)
      (Filter.Eventually.of_forall (fun n => (hA n).2.2 x hx))

theorem cnd_sqrt_exp_difference (D : ι → ι → ℝ) (hD : IsCND D)
    (t : ℝ) (ht : 0 ≤ t) :
    IsCND (fun i j => Real.sqrt (1 - Real.exp (-t * D i j))) := by
  apply cnd_sqrt_one_sub _ (gaussian_cnd_psd D hD t ht)
  · exact fun i j => (Real.exp_pos _).le
  · intro i j
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht)
      (cnd_nonneg D hD i j))
  · intro i
    rw [hD.2.1 i, mul_zero, Real.exp_zero]

theorem scaled_exp_difference_tendsto (x : ℝ) :
    Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) *
      (1 - Real.exp (-(((n + 1 : ℕ) : ℝ)⁻¹) * x))) atTop (𝓝 x) := by
  have hd : HasDerivAt (fun t : ℝ => 1 - Real.exp (-t * x)) x 0 := by
    convert (hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub
      ((Real.hasDerivAt_exp (-(0 : ℝ) * x)).comp 0 ((hasDerivAt_id (0 : ℝ)).neg.mul_const x)) using 1
    simp
  have hnat : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hinv : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp hnat
  have hp : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝[≠] (0 : ℝ)) := by
    apply tendsto_nhdsWithin_iff.2
    refine ⟨hinv, Filter.Eventually.of_forall ?_⟩
    intro n
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, inv_eq_zero]
    positivity
  convert hd.tendsto_slope_zero.comp hp using 1
  funext n
  simp only [zero_add, neg_zero, zero_mul, Real.exp_zero, sub_self, sub_zero,
    smul_eq_mul, inv_inv, Function.comp_apply]

/-- Square-root closure for an arbitrary finite symmetric zero-diagonal CND matrix. -/
theorem cnd_sqrt (D : ι → ι → ℝ) (hD : IsCND D) :
    IsCND (fun i j => Real.sqrt (D i j)) := by
  let A : ℕ → ι → ι → ℝ := fun n i j => Real.sqrt (((n + 1 : ℕ) : ℝ)) *
    Real.sqrt (1 - Real.exp (-(((n + 1 : ℕ) : ℝ)⁻¹) * D i j))
  apply cnd_limit (l := atTop) A _
  · intro n
    exact cnd_scale _ (cnd_sqrt_exp_difference D hD _ (by positivity)) _ (Real.sqrt_nonneg _)
  · intro i j
    have hl := Real.continuous_sqrt.continuousAt.tendsto.comp
      (scaled_exp_difference_tendsto (D i j))
    convert hl using 1
    funext n
    exact (Real.sqrt_mul (by positivity) _).symm

/-- The exact two-term radius transform in CND-MAIN and SG4. -/
theorem sqrt_linear_isCND (D : ι → ι → ℝ) (hD : IsCND D)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    IsCND (fun i j => a * Real.sqrt (D i j) + b * D i j) :=
  cnd_add _ _ (cnd_scale _ (cnd_sqrt D hD) a ha) (cnd_scale D hD b hb)

/-- Full genuine saturation closure; no Gaussian, Schoenberg or sqrt premise is exposed. -/
theorem sqrt_linear_saturation_isCND (D : ι → ι → ℝ) (hD : IsCND D)
    (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) :
    IsCND (fun i j => C * (1 - Real.exp (-a * Real.sqrt (D i j) - b * D i j))) := by
  have h := exponential_saturation_isCND _ (sqrt_linear_isCND D hD a b ha hb)
    C 1 hC (by norm_num)
  convert h using 1
  funext i j
  congr 2
  ring

theorem sqrt_linear_saturation_nonneg (D : ι → ι → ℝ) (hD : IsCND D)
    (a b C : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hC : 0 ≤ C) (i j : ι) :
    0 ≤ C * (1 - Real.exp (-a * Real.sqrt (D i j) - b * D i j)) :=
  cnd_nonneg _ (sqrt_linear_saturation_isCND D hD a b C ha hb hC) i j

end Part2.CNDSaturation

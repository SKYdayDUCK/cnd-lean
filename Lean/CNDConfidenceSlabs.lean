import CNDConfidenceChoice

/-! Exact absolute contrast constraints from CND-MAIN section 2. -/

noncomputable section

namespace Part2.CNDConfidenceSlabs

open Set Topology
open scoped BigOperators
open CNDConfidenceChoice CNDMatrixProx

variable (ι : Type*) [Fintype ι] [DecidableEq ι]

abbrev SlabData := (ι → ℝ) × (ι → ι → ℝ)

def contrastRow (i j : ι) : ι → ℝ := Pi.single i 1 - Pi.single j 1

theorem contrastRow_dot (i j : ι) (p : ι → ℝ) :
    (∑ k, contrastRow ι i j k * p k) = p i - p j := by
  simp [contrastRow, Pi.single_apply, sub_mul, Finset.sum_sub_distrib, ite_mul]

def slabRows (d : SlabData ι) : AffineData ι ((ι × ι) × Bool) :=
  (fun k => if k.2 then contrastRow ι k.1.1 k.1.2 else -contrastRow ι k.1.1 k.1.2,
   fun k => if k.2 then (d.1 k.1.1 - d.1 k.1.2) + d.2 k.1.1 k.1.2
     else -(d.1 k.1.1 - d.1 k.1.2) + d.2 k.1.1 k.1.2)

theorem continuous_slabRows : Continuous (slabRows ι) := by
  unfold slabRows
  apply Continuous.prodMk continuous_const
  apply continuous_pi
  intro k
  split_ifs <;> fun_prop

theorem slabRows_iff (d : SlabData ι) (p : ι → ℝ) :
    (∀ k : (ι × ι) × Bool, (∑ i, (slabRows ι d).1 k i * p i) ≤ (slabRows ι d).2 k) ↔
      ∀ i j, |p i - p j - (d.1 i - d.1 j)| ≤ d.2 i j := by
  constructor
  · intro h i j
    have hp := h ((i, j), true)
    have hn := h ((i, j), false)
    simp [slabRows, contrastRow_dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] at hp hn
    rw [abs_le]
    constructor <;> linarith
  · intro h k
    rcases k with ⟨⟨i, j⟩, b⟩
    have ha := (abs_le.mp (h i j))
    cases b <;>
      simp [slabRows, contrastRow_dot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib] <;> linarith

def confidenceSet (R : ℝ) (d : SlabData ι) : Set (ι → ℝ) :=
  {p | p ∈ cube R ∧ ∀ i j, |p i - p j - (d.1 i - d.1 j)| ≤ d.2 i j}

def canonicalConfidence (R : ℝ) (hR : 0 ≤ R) (d : SlabData ι) : ι → ℝ :=
  affineConfidence R hR (slabRows ι d)

/-- The exact cube/slab confidence rule of CND-MAIN, with zero on the empty
branch, is Borel on all real estimate/radius coefficients. -/
theorem measurable_canonicalConfidence (R : ℝ) (hR : 0 ≤ R) :
    Measurable (canonicalConfidence ι R hR) :=
  (measurable_affineConfidence R hR).comp (continuous_slabRows ι).measurable

theorem confidenceSet_eq_zeroSet (R : ℝ) (d : SlabData ι) :
    confidenceSet ι R d = {p | p ∈ cube R ∧ affineViolation (slabRows ι d) p = 0} := by
  ext p
  simp only [confidenceSet, mem_setOf_eq, affineViolation_eq_zero, slabRows_iff]

theorem canonicalConfidence_spec (R : ℝ) (hR : 0 ≤ R) (d : SlabData ι)
    (hne : (confidenceSet ι R d).Nonempty) :
    canonicalConfidence ι R hR d ∈ confidenceSet ι R d ∧
      IsMinOn squaredNorm (confidenceSet ι R d) (canonicalConfidence ι R hR d) := by
  rw [confidenceSet_eq_zeroSet] at hne ⊢
  obtain ⟨z, hz⟩ := hne
  exact confidenceChoice_spec (cube R) (compact_cube R) (nonempty_cube R hR)
    (fun z => affineViolation z.1 z.2) continuous_affineViolation
    (fun d => convex_affineViolation (cube R) (convex_cube R) d)
    (fun d p _ => affineViolation_nonneg d p) (fun _ => 0) (slabRows ι d) ⟨z, hz⟩

theorem canonicalConfidence_empty (R : ℝ) (hR : 0 ≤ R) (d : SlabData ι)
    (hempty : confidenceSet ι R d = ∅) : canonicalConfidence ι R hR d = 0 := by
  have hnot : slabRows ι d ∉ feasibleDomain (cube R)
      (fun z => affineViolation z.1 z.2) := by
    rintro ⟨p, hp, hzero⟩
    have hmem : p ∈ confidenceSet ι R d := by
      rw [confidenceSet_eq_zeroSet]
      exact ⟨hp, hzero⟩
    rw [hempty] at hmem
    exact hmem
  simp only [canonicalConfidence, affineConfidence, confidenceChoice, if_neg hnot]

theorem measurable_canonicalConfidence_history {Ω : Type*} [MeasurableSpace Ω]
    (R : ℝ) (hR : 0 ≤ R) (d : Ω → SlabData ι) (hd : Measurable d) :
    Measurable (fun ω => canonicalConfidence ι R hR (d ω)) :=
  (measurable_canonicalConfidence ι R hR).comp hd

end Part2.CNDConfidenceSlabs

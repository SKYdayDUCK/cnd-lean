import CNDMinimumNormMeasurable
import Mathlib.Analysis.Convex.Mul

/-!
Concrete finite affine confidence sets in a fixed cube. Both an inequality and
its negative are permitted as separate rows; equalities and absolute slabs are
therefore included. The empty feasible set has an explicit Borel fallback.
-/

noncomputable section

namespace Part2.CNDConfidenceChoice

open Set Filter Topology
open scoped BigOperators
open CNDMatrixProx CNDMinimumNormMeasurable

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
variable {X : Type*} [TopologicalSpace X]

def feasibleDomain (S : Set (ι → ℝ)) (V : X × (ι → ℝ) → ℝ) : Set X :=
  {x | ∃ p ∈ S, V (x, p) = 0}

/-- Projection is closed because the point domain is fixed and compact. -/
theorem isClosed_feasibleDomain (S : Set (ι → ℝ)) (hS : IsCompact S)
    (V : X × (ι → ℝ) → ℝ) (hV : Continuous V) :
    IsClosed (feasibleDomain S V) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let A : Set (X × S) := {z | V (z.1, z.2.val) = 0}
  have hA : IsClosed A := isClosed_eq
    (hV.comp₂ continuous_fst (continuous_subtype_val.comp continuous_snd)) continuous_const
  have heq : feasibleDomain S V = Prod.fst '' A := by
    ext x
    constructor
    · rintro ⟨p, hp, hzero⟩
      exact ⟨(x, ⟨p, hp⟩), hzero, rfl⟩
    · rintro ⟨⟨x, p⟩, hzero, rfl⟩
      exact ⟨p.val, p.property, hzero⟩
  rw [heq]
  exact isClosedMap_fst_of_compactSpace A hA

def confidenceChoice (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (V : X × (ι → ℝ) → ℝ) (hV : Continuous V)
    (hconv : ∀ x, ConvexOn ℝ S (fun p => V (x, p)))
    (fallback : X → (ι → ℝ)) (x : X) : ι → ℝ := by
  classical
  exact if x ∈ feasibleDomain S V then
    minimumNorm S hS hne (fun p => V (x, p))
      (hV.comp₂ continuous_const continuous_id) (hconv x)
  else fallback x

theorem measurable_confidenceChoice [MeasurableSpace X] [BorelSpace X]
    (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (V : X × (ι → ℝ) → ℝ) (hV : Continuous V)
    (hconv : ∀ x, ConvexOn ℝ S (fun p => V (x, p)))
    (fallback : X → (ι → ℝ)) (hb : Measurable fallback) :
    Measurable (confidenceChoice S hS hne V hV hconv fallback) := by
  classical
  exact (measurable_minimumNorm S hS hne V hV hconv).piecewise
    (isClosed_feasibleDomain S hS V hV).measurableSet hb

theorem minSet_eq_zeroSet (S : Set (ι → ℝ)) (V : (ι → ℝ) → ℝ)
    (hVnonneg : ∀ p ∈ S, 0 ≤ V p) (hfeas : ∃ p ∈ S, V p = 0) :
    minSet S V = {p | p ∈ S ∧ V p = 0} := by
  obtain ⟨z, hz, hzero⟩ := hfeas
  ext p
  constructor
  · intro hp
    refine ⟨hp.1, le_antisymm ?_ (hVnonneg p hp.1)⟩
    have h := hp.2 hz
    change V p ≤ V z at h
    rw [hzero] at h
    exact h
  · intro hp
    refine ⟨hp.1, ?_⟩
    intro y hy
    rw [hp.2]
    exact hVnonneg y hy

/-- On the feasible branch the selected point is exactly the unique minimum
of the Euclidean square norm over the zero-violation confidence set. -/
theorem confidenceChoice_spec (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (V : X × (ι → ℝ) → ℝ) (hV : Continuous V)
    (hconv : ∀ x, ConvexOn ℝ S (fun p => V (x, p)))
    (hnonneg : ∀ x p, p ∈ S → 0 ≤ V (x, p))
    (fallback : X → (ι → ℝ)) (x : X) (hx : x ∈ feasibleDomain S V) :
    let p := confidenceChoice S hS hne V hV hconv fallback x
    (p ∈ S ∧ V (x, p) = 0) ∧
      IsMinOn squaredNorm {y | y ∈ S ∧ V (x, y) = 0} p := by
  have heq := minSet_eq_zeroSet S (fun p => V (x, p)) (hnonneg x) hx
  simp only [confidenceChoice, if_pos hx]
  have hs := minimumNorm_spec S hS hne (fun p => V (x, p))
    (hV.comp₂ continuous_const continuous_id) (hconv x)
  constructor
  · simpa only [heq] using hs.1
  · simpa only [heq] using hs.2

theorem confidenceChoice_unique (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (V : X × (ι → ℝ) → ℝ) (hV : Continuous V)
    (hconv : ∀ x, ConvexOn ℝ S (fun p => V (x, p)))
    (hnonneg : ∀ x p, p ∈ S → 0 ≤ V (x, p))
    (fallback : X → (ι → ℝ)) (x : X) (hx : x ∈ feasibleDomain S V)
    (p : ι → ℝ) (hp : (p ∈ S ∧ V (x, p) = 0) ∧
      IsMinOn squaredNorm {y | y ∈ S ∧ V (x, y) = 0} p) :
    p = confidenceChoice S hS hne V hV hconv fallback x := by
  have heq := minSet_eq_zeroSet S (fun p => V (x, p)) (hnonneg x) hx
  simp only [confidenceChoice, if_pos hx]
  apply (Classical.choose_spec (exists_unique_minimumNorm S hS hne (fun p => V (x, p))
    (hV.comp₂ continuous_const continuous_id) (hconv x))).2
  simpa only [heq] using hp

abbrev AffineData (ι κ : Type*) := (κ → ι → ℝ) × (κ → ℝ)

def affineValue (d : AffineData ι κ) (p : ι → ℝ) (k : κ) : ℝ :=
  (∑ i, d.1 k i * p i) - d.2 k

def affineViolation (d : AffineData ι κ) (p : ι → ℝ) : ℝ :=
  ∑ k, (max 0 (affineValue d p k)) ^ 2

theorem continuous_affineViolation :
    Continuous (fun z : AffineData ι κ × (ι → ℝ) => affineViolation z.1 z.2) := by
  unfold affineViolation affineValue
  fun_prop

theorem affineViolation_nonneg (d : AffineData ι κ) (p : ι → ℝ) :
    0 ≤ affineViolation d p := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem affineViolation_eq_zero (d : AffineData ι κ) (p : ι → ℝ) :
    affineViolation d p = 0 ↔ ∀ k, (∑ i, d.1 k i * p i) ≤ d.2 k := by
  rw [affineViolation, Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp only [Finset.mem_univ, true_implies, sq_eq_zero_iff, max_eq_left_iff, affineValue,
    sub_nonpos]

theorem convex_affineValue (S : Set (ι → ℝ)) (hS : Convex ℝ S)
    (d : AffineData ι κ) (k : κ) : ConvexOn ℝ S (fun p => affineValue d p k) := by
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [affineValue, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have hmix : (∑ i, d.1 k i * (a * x i + b * y i)) =
      a * (∑ i, d.1 k i * x i) + b * (∑ i, d.1 k i * y i) :=
    CND.linear_mix_identity (d.1 k) x y a b
  rw [hmix]
  have hb : b = 1 - a := by linarith
  rw [hb]
  exact le_of_eq (by ring)

theorem convex_affineViolation (S : Set (ι → ℝ)) (hS : Convex ℝ S)
    (d : AffineData ι κ) : ConvexOn ℝ S (affineViolation d) := by
  have hterm (k : κ) : ConvexOn ℝ S (fun p => (max 0 (affineValue d p k)) ^ 2) := by
    have hmax : ConvexOn ℝ S (fun p => max 0 (affineValue d p k)) :=
      (convexOn_const 0 hS).sup (convex_affineValue S hS d k)
    exact hmax.pow (fun _ _ => le_max_left _ _) 2
  refine ⟨hS, ?_⟩
  intro x hx y hy a b ha hb hab
  simp only [affineViolation, smul_eq_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun k _ => (hterm k).2 hx hy ha hb hab

def cube (R : ℝ) : Set (ι → ℝ) := Set.Icc (fun _ => 0) (fun _ => R)

theorem compact_cube (R : ℝ) : IsCompact (cube (ι := ι) R) := isCompact_Icc

theorem convex_cube (R : ℝ) : Convex ℝ (cube (ι := ι) R) := by
  intro x hx y hy a b ha hb hab
  constructor
  · intro i
    change 0 ≤ a * x i + b * y i
    exact add_nonneg (mul_nonneg ha (hx.1 i)) (mul_nonneg hb (hy.1 i))
  · intro i
    change a * x i + b * y i ≤ R
    have hax := mul_le_mul_of_nonneg_left (hx.2 i) ha
    have hby := mul_le_mul_of_nonneg_left (hy.2 i) hb
    calc
      _ ≤ a * R + b * R := add_le_add hax hby
      _ = R := by rw [← add_mul, hab, one_mul]

theorem nonempty_cube (R : ℝ) (hR : 0 ≤ R) : (cube (ι := ι) R).Nonempty :=
  ⟨0, (show (0 : ι → ℝ) ≤ 0 from le_refl _), fun _ => hR⟩

def affineConfidence (R : ℝ) (hR : 0 ≤ R) (d : AffineData ι κ) : ι → ℝ :=
  confidenceChoice (cube R) (compact_cube R) (nonempty_cube R hR)
    (fun z => affineViolation z.1 z.2) continuous_affineViolation
    (fun d => convex_affineViolation (cube R) (convex_cube R) d) (fun _ => 0) d

/-- Borel canonical cube confidence point for any finite list of affine rows,
including inconsistent histories (where the result is zero). -/
theorem measurable_affineConfidence (R : ℝ) (hR : 0 ≤ R) :
    Measurable (affineConfidence (ι := ι) (κ := κ) R hR) :=
  measurable_confidenceChoice (cube R) (compact_cube R) (nonempty_cube R hR)
    (fun z => affineViolation z.1 z.2) continuous_affineViolation
    (fun d => convex_affineViolation (cube R) (convex_cube R) d) (fun _ => 0) measurable_const

/-- Any finite Borel partition of the history may select among Borel maps. -/
theorem measurable_finite_history_choice {Ω J : Type*} [MeasurableSpace Ω]
    [Fintype J] [DecidableEq J] [MeasurableSpace J] [MeasurableSingletonClass J]
    (key : Ω → J) (hkey : Measurable key) (c : J → Ω → (ι → ℝ))
    (hc : ∀ j, Measurable (c j)) : Measurable (fun ω => c (key ω) ω) := by
  have hsum : Measurable (fun ω => ∑ j : J, if key ω = j then c j ω else 0) := by
    apply Finset.measurable_sum
    intro j _
    exact (hc j).piecewise (hkey (measurableSet_singleton j)) measurable_const
  have heq : (fun ω => ∑ j : J, if key ω = j then c j ω else 0) =
      fun ω => c (key ω) ω := by
    funext ω
    simp
  rwa [heq] at hsum

end Part2.CNDConfidenceChoice

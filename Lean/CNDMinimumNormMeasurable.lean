import CNDCompactSelection
import CNDMatrixProx

/-!
Borel minimum-Euclidean-norm minimization for continuous convex families on a
fixed nonempty compact convex subset of a finite real coordinate space.
The regularizer is the actual coordinate sum of squares, not the Pi sup norm.
-/

noncomputable section

namespace Part2.CNDMinimumNormMeasurable

open Set Filter Topology
open CNDMatrixProx

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def minSet (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ) : Set (ι → ℝ) :=
  {p | p ∈ S ∧ IsMinOn f S p}

theorem convex_minSet (S : Set (ι → ℝ)) (f : (ι → ℝ) → ℝ)
    (hf : ConvexOn ℝ S f) : Convex ℝ (minSet S f) := by
  intro x hx y hy a b ha hb hab
  refine ⟨hf.1 hx.1 hy.1 ha hb hab, ?_⟩
  intro z hz
  have hxy : f y = f x := le_antisymm (hy.2 hx.1) (hx.2 hy.1)
  have hmix := hf.2 hx.1 hy.1 ha hb hab
  simp only [smul_eq_mul] at hmix
  rw [hxy, ← add_mul, hab, one_mul] at hmix
  exact hmix.trans (hx.2 hz)

theorem compact_minSet (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) : IsCompact (minSet S f) := by
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne hf.continuousOn
  have heq : minSet S f = S ∩ {y | f y = f p} := by
    ext y
    constructor
    · intro hy
      exact ⟨hy.1, le_antisymm (hy.2 hp) (hmin hy.1)⟩
    · intro hy
      refine ⟨hy.1, ?_⟩
      intro z hz
      rw [hy.2]
      exact hmin hz
  rw [heq]
  exact hS.inter_right (isClosed_eq hf continuous_const)

theorem exists_unique_minimumNorm (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f) :
    ∃! p, p ∈ minSet S f ∧ IsMinOn squaredNorm (minSet S f) p := by
  obtain ⟨x, hx, hxmin⟩ := hS.exists_isMinOn hne hf.continuousOn
  obtain ⟨p, hp, hn⟩ := (compact_minSet S hS hne f hf).exists_isMinOn ⟨x, hx, hxmin⟩
    continuous_squaredNorm.continuousOn
  refine ⟨p, ⟨hp, hn⟩, ?_⟩
  intro y hy
  by_contra hyp
  have hmid := (convex_minSet S f hconv) hy.1 hp
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hn1 := hn hmid
  have hn2 := hy.2 hmid
  change squaredNorm p ≤ squaredNorm ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • p) at hn1
  change squaredNorm y ≤ squaredNorm ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • p) at hn2
  rw [squaredNorm_midpoint] at hn1 hn2
  have hpositive := squaredNorm_sub_pos hyp
  nlinarith

def minimumNorm (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f) : ι → ℝ :=
  Classical.choose (exists_unique_minimumNorm S hS hne f hf hconv)

theorem minimumNorm_spec (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f) :
    minimumNorm S hS hne f hf hconv ∈ minSet S f ∧
      IsMinOn squaredNorm (minSet S f) (minimumNorm S hS hne f hf hconv) :=
  (Classical.choose_spec (exists_unique_minimumNorm S hS hne f hf hconv)).1

theorem exists_unique_regularized (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f)
    (e : ℝ) (he : 0 < e) :
    ∃! p, p ∈ S ∧ IsMinOn (fun y => f y + e * squaredNorm y) S p := by
  obtain ⟨p, hp, hmin⟩ := hS.exists_isMinOn hne
    (hf.add (continuous_const.mul continuous_squaredNorm)).continuousOn
  refine ⟨p, ⟨hp, hmin⟩, ?_⟩
  intro y hy
  by_contra hyp
  let z := (1 / 2 : ℝ) • y + (1 / 2 : ℝ) • p
  have hz : z ∈ S := hconv.1 hy.1 hp
    (by norm_num) (by norm_num) (by norm_num)
  have hconvex := hconv.2 hy.1 hp
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  simp only [smul_eq_mul] at hconvex
  have hn1 := hmin hz
  have hn2 := hy.2 hz
  have hid : squaredNorm z = (squaredNorm y + squaredNorm p) / 2 - squaredNorm (y - p) / 4 :=
    squaredNorm_midpoint y p
  change f p + e * squaredNorm p ≤ f z + e * squaredNorm z at hn1
  change f y + e * squaredNorm y ≤ f z + e * squaredNorm z at hn2
  rw [hid] at hn1 hn2
  have hpositive := squaredNorm_sub_pos hyp
  change f z ≤ _ at hconvex
  nlinarith [mul_pos he hpositive]

def regularized (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f)
    (e : ℝ) (he : 0 < e) : ι → ℝ :=
  Classical.choose (exists_unique_regularized S hS hne f hf hconv e he)

theorem regularized_spec (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f)
    (e : ℝ) (he : 0 < e) :
    regularized S hS hne f hf hconv e he ∈ S ∧
      IsMinOn (fun y => f y + e * squaredNorm y) S (regularized S hS hne f hf hconv e he) :=
  (Classical.choose_spec (exists_unique_regularized S hS hne f hf hconv e he)).1

variable {X : Type*} [TopologicalSpace X]

theorem continuous_regularized (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : X × (ι → ℝ) → ℝ) (hf : Continuous f)
    (hconv : ∀ x, ConvexOn ℝ S (fun p => f (x, p))) (e : ℝ) (he : 0 < e) :
    Continuous (fun x => regularized S hS hne (fun p => f (x, p))
      (hf.comp₂ continuous_const continuous_id) (hconv x) e he) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let u : X → S := fun x => ⟨regularized S hS hne (fun p => f (x, p))
    (hf.comp₂ continuous_const continuous_id) (hconv x) e he,
    (regularized_spec S hS hne (fun p => f (x, p))
      (hf.comp₂ continuous_const continuous_id) (hconv x) e he).1⟩
  have hn : Continuous (fun z : X × S => squaredNorm z.2.val) :=
    (continuous_squaredNorm (ι := ι)).comp (continuous_subtype_val.comp continuous_snd)
  have hcont : Continuous (fun z : X × S => f (z.1, z.2.val) + e * squaredNorm z.2.val) :=
    (hf.comp₂ continuous_fst (continuous_subtype_val.comp continuous_snd)).add
      (continuous_const.mul hn)
  have hu : Continuous u := by
    apply CNDCompactSelection.continuous_unique_argmin _ hcont u
    · intro x y
      exact (regularized_spec S hS hne (fun p => f (x, p))
        (hf.comp₂ continuous_const continuous_id) (hconv x) e he).2 y.property
    · intro x y hy
      apply Subtype.ext
      apply (Classical.choose_spec (exists_unique_regularized S hS hne
        (fun p => f (x, p)) (hf.comp₂ continuous_const continuous_id) (hconv x) e he)).2
      refine ⟨y.property, ?_⟩
      intro z hz
      exact hy ⟨z, hz⟩
  exact continuous_subtype_val.comp hu

theorem regularized_tendsto_minimumNorm (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : (ι → ℝ) → ℝ) (hf : Continuous f) (hconv : ConvexOn ℝ S f) :
    Tendsto (fun n : ℕ => regularized S hS hne f hf hconv (1 / ((n : ℝ) + 1))
      (by positivity)) atTop (𝓝 (minimumNorm S hS hne f hf hconv)) := by
  letI : CompactSpace S := isCompact_iff_compactSpace.mp hS
  let u : ℕ → S := fun n => ⟨regularized S hS hne f hf hconv (1 / ((n : ℝ) + 1))
    (by positivity), (regularized_spec S hS hne f hf hconv _ (by positivity)).1⟩
  let p : S := ⟨minimumNorm S hS hne f hf hconv, (minimumNorm_spec S hS hne f hf hconv).1.1⟩
  have hgS : Continuous (fun y : S => squaredNorm y.val) :=
    (continuous_squaredNorm (ι := ι)).comp continuous_subtype_val
  have hlim : Tendsto u atTop (𝓝 p) := by
    apply CNDCompactSelection.tikhonov_tendsto (fun y : S => f y.val) (fun y : S => squaredNorm y.val)
      (hf.comp continuous_subtype_val) hgS
      (fun n : ℕ => 1 / ((n : ℝ) + 1)) (fun _ => by positivity)
      tendsto_one_div_add_atTop_nhds_zero_nat u
    · intro n y
      exact (regularized_spec S hS hne f hf hconv _ (by positivity)).2 y.property
    · intro y
      exact (minimumNorm_spec S hS hne f hf hconv).1.2 y.property
    · intro y hy hynorm
      apply Subtype.ext
      apply (Classical.choose_spec (exists_unique_minimumNorm S hS hne f hf hconv)).2
      refine ⟨⟨y.property, ?_⟩, ?_⟩
      · intro z hz
        exact hy ⟨z, hz⟩
      · intro z hz
        exact hynorm.trans ((minimumNorm_spec S hS hne f hf hconv).2 hz)
  exact (continuous_subtype_val.tendsto p).comp hlim

/-- The full canonical minimum-norm selector is Borel for every jointly
continuous convex family on a fixed compact convex feasible set. -/
theorem measurable_minimumNorm [MeasurableSpace X] [BorelSpace X]
    (S : Set (ι → ℝ)) (hS : IsCompact S) (hne : S.Nonempty)
    (f : X × (ι → ℝ) → ℝ) (hf : Continuous f)
    (hconv : ∀ x, ConvexOn ℝ S (fun p => f (x, p))) :
    Measurable (fun x => minimumNorm S hS hne (fun p => f (x, p))
      (hf.comp₂ continuous_const continuous_id) (hconv x)) := by
  apply measurable_of_tendsto_metrizable
    (fun n : ℕ => (continuous_regularized S hS hne f hf hconv
      (1 / ((n : ℝ) + 1)) (by positivity)).measurable)
  apply tendsto_pi_nhds.mpr
  intro x
  exact regularized_tendsto_minimumNorm S hS hne _ _ (hconv x)

end Part2.CNDMinimumNormMeasurable

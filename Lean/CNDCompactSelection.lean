import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Compact parameterized minimization. Neither continuity nor measurability of a
selector is an input: continuity follows from a closed graph and compact fibers;
the Tikhonov limit follows by passing actual minimizing inequalities to a limit.
-/

noncomputable section

namespace Part2.CNDCompactSelection

open Set Filter Topology

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A jointly continuous objective with a unique minimizer on a fixed compact
space has a continuous minimizer. No selection theorem is assumed. -/
theorem continuous_unique_argmin [CompactSpace Y]
    (f : X × Y → ℝ) (hf : Continuous f) (u : X → Y)
    (hu : ∀ x y, f (x, u x) ≤ f (x, y))
    (huniq : ∀ x y, (∀ z, f (x, y) ≤ f (x, z)) → y = u x) :
    Continuous u := by
  rw [continuous_iff_isClosed]
  intro C hC
  let A : Set (X × Y) := {z | z.2 ∈ C ∧ ∀ y, f z ≤ f (z.1, y)}
  have hA : IsClosed A := by
    have hB : IsClosed {z : X × Y | ∀ y, f z ≤ f (z.1, y)} := by
      simp only [setOf_forall]
      exact isClosed_iInter fun y => isClosed_le hf (hf.comp₂ continuous_fst continuous_const)
    exact (hC.preimage continuous_snd).inter hB
  have heq : u ⁻¹' C = Prod.fst '' A := by
    ext x
    constructor
    · intro hx
      exact ⟨(x, u x), ⟨hx, hu x⟩, rfl⟩
    · rintro ⟨⟨x', y⟩, ⟨hyC, hy⟩, rfl⟩
      change u x' ∈ C
      rw [← huniq x' y hy]
      exact hyC
  rw [heq]
  exact isClosedMap_fst_of_compactSpace A hA

/-- The primary minimizer set is nonempty compact. -/
theorem compact_argmin [CompactSpace Y] [Nonempty Y]
    (f : Y → ℝ) (hf : Continuous f) :
    IsCompact {y | ∀ z, f y ≤ f z} ∧ {y | ∀ z, f y ≤ f z}.Nonempty := by
  constructor
  · apply IsClosed.isCompact
    simp only [setOf_forall]
    exact isClosed_iInter fun z => isClosed_le hf continuous_const
  · obtain ⟨y, _, hy⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty : (univ : Set Y).Nonempty)
      hf.continuousOn
    exact ⟨y, fun z => hy (mem_univ z)⟩

/-- The secondary minimum exists, before any convexity or uniqueness is used. -/
theorem exists_secondary_argmin [CompactSpace Y] [Nonempty Y]
    (f g : Y → ℝ) (hf : Continuous f) (hg : Continuous g) :
    ∃ p, (∀ z, f p ≤ f z) ∧ ∀ y, (∀ z, f y ≤ f z) → g p ≤ g y := by
  obtain ⟨hK, hne⟩ := compact_argmin f hf
  obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hne hg.continuousOn
  exact ⟨p, hp, fun y hy => hpmin hy⟩

/-- Actual Tikhonov minimizers converge to the unique secondary minimizer.
The hypotheses are objective continuity, positive vanishing regularization,
minimizing inequalities, and variational uniqueness; no measurable selector,
convergence, or continuity of a selector is postulated. -/
theorem tikhonov_tendsto [CompactSpace Y]
    (f g : Y → ℝ) (hf : Continuous f) (hg : Continuous g)
    (e : ℕ → ℝ) (hepos : ∀ n, 0 < e n) (he : Tendsto e atTop (𝓝 0))
    (u : ℕ → Y) (hu : ∀ n y, f (u n) + e n * g (u n) ≤ f y + e n * g y)
    (p : Y) (hp : ∀ z, f p ≤ f z)
    (huniq : ∀ y, (∀ z, f y ≤ f z) → g y ≤ g p → y = p) :
    Tendsto u atTop (𝓝 p) := by
  apply isCompact_univ.tendsto_nhds_of_unique_mapClusterPt (Eventually.of_forall (fun _ => mem_univ _))
  intro y _ hy
  let L : Filter ℕ := comap u (𝓝 y) ⊓ atTop
  haveI : NeBot L := (neBot_inf_comap_iff_map').mpr hy
  have huy : Tendsto u L (𝓝 y) := tendsto_comap.mono_left inf_le_left
  have heL : Tendsto e L (𝓝 0) := he.mono_left inf_le_right
  have hfu := hf.tendsto y |>.comp huy
  have hgu := hg.tendsto y |>.comp huy
  have hprimary : ∀ z, f y ≤ f z := by
    intro z
    have hleft := hfu.add (heL.mul hgu)
    have hright := (tendsto_const_nhds (x := f z) (f := L)).add (heL.mul_const (g z))
    simpa using le_of_tendsto_of_tendsto hleft hright
      (Eventually.of_forall fun n => hu n z)
  have hnorm : g y ≤ g p := by
    apply le_of_tendsto hgu
    apply Eventually.of_forall
    intro n
    change g (u n) ≤ g p
    have hreg := hu n p
    have hpri := hp (u n)
    exact (mul_le_mul_iff_right₀ (hepos n)).mp (by linarith)
  exact huniq y hprimary hnorm

end Part2.CNDCompactSelection

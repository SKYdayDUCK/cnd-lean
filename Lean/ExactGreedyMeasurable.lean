import ExactGreedyTransport
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Borel measurability of the actual frozen numbered transport and least-index rule. -/

noncomputable section

namespace Part2.ExactGreedyMeasurable

open scoped BigOperators
open ExactGreedyTransport

variable {n : ℕ}

abbrev Vec (n : ℕ) := Fin n → ℝ
abbrev Mat (n : ℕ) := Fin n → Fin n → ℝ
abbrev TransportInput (n : ℕ) := Vec n × (Vec n × Vec n)

/-- Exact finite comparison fibers of the frozen min' choice. -/
theorem leastArgmin_eq_iff (g : Vec n) (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (i : Fin n) : leastArgmin g hne = i ↔
      (∀ j, g i ≤ g j) ∧ (∀ j, j < i → g i < g j) := by
  constructor
  · intro h
    have hmin := leastArgmin_minimizes g hne
    rw [h] at hmin
    refine ⟨hmin, ?_⟩
    intro j hj
    have hle := hmin j
    by_contra hlt
    have heq : g j = g i := le_antisymm (le_of_not_gt hlt) hle
    have hjmin : ∀ k, g j ≤ g k := by intro k; rw [heq]; exact hmin k
    have hidx := leastArgmin_le_every_minimizer g hne j hjmin
    rw [h] at hidx
    exact (not_le_of_gt hj) hidx
  · intro h
    have hidx := leastArgmin_le_every_minimizer g hne i h.1
    by_contra hnequal
    have hlt : leastArgmin g hne < i := lt_of_le_of_ne hidx hnequal
    have hstrict := h.2 _ hlt
    have hmin := leastArgmin_minimizes g hne i
    linarith

theorem continuous_finiteValue (i : ℕ) : Continuous (fun s : Vec n => finiteValue s i) := by
  by_cases hi : i < n
  · simpa [finiteValue, hi] using (continuous_apply (⟨i, hi⟩ : Fin n))
  · simpa [finiteValue, hi] using (continuous_const : Continuous (fun _ : Vec n => (0 : ℝ)))

theorem continuous_massPrefix (i : ℕ) :
    Continuous (fun s : Vec n => massPrefix (finiteValue s) i) := by
  unfold massPrefix
  exact continuous_finset_sum _ (fun j _ => continuous_finiteValue j)

theorem continuous_excess : Continuous (fun z : Vec n × Vec n => ConvexRemap.excess z.1 z.2) := by
  apply continuous_pi
  intro i
  unfold ConvexRemap.excess
  fun_prop

theorem continuous_demand : Continuous (fun z : Vec n × Vec n => ConvexRemap.demand z.1 z.2) := by
  apply continuous_pi
  intro i
  unfold ConvexRemap.demand
  fun_prop

/-- The frozen recursive greedy flow is continuous through its proven exact overlap identity. -/
theorem continuous_orderedFlow (i j : Fin n) :
    Continuous (fun z : Vec n × Vec n => orderedFlow z.1 z.2 i j) := by
  simp_rw [orderedFlow_eq_overlap]
  unfold intervalFlow overlap excessNat demandNat
  exact continuous_const.max
    ((((continuous_massPrefix (i.val + 1)).comp continuous_excess).min
      ((continuous_massPrefix (j.val + 1)).comp continuous_demand)).sub
      (((continuous_massPrefix i.val).comp continuous_excess).max
        ((continuous_massPrefix j.val).comp continuous_demand)))

theorem continuous_orderedPlan (i j : Fin n) :
    Continuous (fun z : Vec n × Vec n => orderedPlan z.1 z.2 i j) := by
  unfold orderedPlan
  apply Continuous.add _ (continuous_orderedFlow i j)
  by_cases hij : i = j
  · simp only [hij, if_true]
    fun_prop
  · simp only [hij, if_false]
    exact continuous_const

variable {Ω : Type*} [MeasurableSpace Ω]

/-- The min' tie rule has Borel comparison fibers, including all ties. -/
theorem measurable_leastArgmin_history (g : Ω → Vec n) (hg : Measurable g)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    Measurable (fun ω => leastArgmin (g ω) hne) := by
  apply measurable_to_countable'
  intro i
  change MeasurableSet {ω | leastArgmin (g ω) hne = i}
  have hmin : MeasurableSet {ω | ∀ j, g ω i ≤ g ω j} := by
    simpa only [Set.setOf_forall] using
      (MeasurableSet.iInter (fun j => measurableSet_le
        ((measurable_pi_apply i).comp hg) ((measurable_pi_apply j).comp hg)))
  have hstrict : MeasurableSet {ω | ∀ j, j < i → g ω i < g ω j} := by
    have heach (j : Fin n) : MeasurableSet {ω | j < i → g ω i < g ω j} := by
      by_cases hj : j < i
      · simpa only [hj, true_implies] using measurableSet_lt
          ((measurable_pi_apply i).comp hg) ((measurable_pi_apply j).comp hg)
      · simp [hj]
    simpa only [Set.setOf_forall] using MeasurableSet.iInter heach
  have heq : {ω | leastArgmin (g ω) hne = i} =
      {ω | ∀ j, g ω i ≤ g ω j} ∩ {ω | ∀ j, j < i → g ω i < g ω j} := by
    ext ω
    exact leastArgmin_eq_iff (g ω) hne i
  rw [heq]
  exact hmin.inter hstrict

theorem measurable_leastArgmin (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    Measurable (fun g : Vec n => leastArgmin g hne) :=
  measurable_leastArgmin_history _ measurable_id hne

/-- Evaluation at the actual least-index choice is measurable by a finite partition. -/
theorem measurable_chosen_gradient_history (g : Ω → Vec n) (hg : Measurable g)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    Measurable (fun ω => g ω (leastArgmin (g ω) hne)) := by
  have hm := measurable_leastArgmin_history g hg hne
  have hterm (i : Fin n) : Measurable (fun ω =>
      if leastArgmin (g ω) hne = i then g ω i else 0) :=
    Measurable.ite ((measurableSet_singleton i).preimage hm)
      ((measurable_pi_apply i).comp hg) measurable_const
  have hsum := Finset.measurable_sum (Finset.univ : Finset (Fin n)) (fun i _ => hterm i)
  simpa using hsum

/-- Every entry of the frozen exactRemap is measurable for arbitrary measurable inputs.
No nonzero-source or generic-position premise is used. -/
theorem measurable_exactRemap_entry_history (q p g : Ω → Vec n) (W : Ω → ℝ)
    (hq : Measurable q) (hp : Measurable p) (hg : Measurable g) (hW : Measurable W)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) (k j : Fin n) :
    Measurable (fun ω => exactRemap (q ω) (p ω) (g ω) (W ω) hne k j) := by
  have hqk := (measurable_pi_apply k).comp hq
  have hgk := (measurable_pi_apply k).comp hg
  have hm := measurable_leastArgmin_history g hg hne
  have hgm := measurable_chosen_gradient_history g hg hne
  have hzero : MeasurableSet {ω | q ω k = 0} := measurableSet_eq_fun hqk measurable_const
  have hsafe : MeasurableSet {ω | g ω k ≤ g ω (leastArgmin (g ω) hne) + W ω} :=
    measurableSet_le hgk (hgm.add hW)
  have hrepair : Measurable (fun ω => if leastArgmin (g ω) hne = j then (1 : ℝ) else 0) :=
    Measurable.ite ((measurableSet_singleton j).preimage hm) measurable_const measurable_const
  have hzeroRow : Measurable (fun ω =>
      if g ω k ≤ g ω (leastArgmin (g ω) hne) + W ω then (if k = j then (1 : ℝ) else 0)
      else (if leastArgmin (g ω) hne = j then 1 else 0)) :=
    Measurable.ite hsafe measurable_const hrepair
  have hplan : Measurable (fun ω => orderedPlan (q ω) (p ω) k j) :=
    (continuous_orderedPlan k j).measurable.comp (hq.prodMk hp)
  simpa only [exactRemap] using Measurable.ite hzero hzeroRow (hplan.div hqk)

/-- The complete original matrix, including zero rows and ties, is a Borel map. -/
theorem measurable_exactRemap_history (q p g : Ω → Vec n) (W : Ω → ℝ)
    (hq : Measurable q) (hp : Measurable p) (hg : Measurable g) (hW : Measurable W)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    Measurable (fun ω => exactRemap (q ω) (p ω) (g ω) (W ω) hne) := by
  apply measurable_pi_iff.mpr
  intro k
  apply measurable_pi_iff.mpr
  intro j
  exact measurable_exactRemap_entry_history q p g W hq hp hg hW hne k j

/-- Process interface layout is exactly (q,(p,g)), with the fixed width captured. -/
def actualTransport (W : ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (z : TransportInput n) : Mat n := exactRemap z.1 z.2.1 z.2.2 W hne

theorem actualTransport_eq_exactRemap (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) (z : TransportInput n) :
    actualTransport W hne z = exactRemap z.1 z.2.1 z.2.2 W hne := rfl

theorem measurable_actualTransport (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) : Measurable (actualTransport W hne) :=
  measurable_exactRemap_history _ _ _ _ measurable_fst (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd) measurable_const hne

theorem measurable_actualTransport_history (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) (z : Ω → TransportInput n) (hz : Measurable z) :
    Measurable (fun ω => actualTransport W hne (z ω)) :=
  (measurable_actualTransport W hne).comp hz

theorem measurable_gradient_history (θ : Ω → Vec n) (r : Ω → Mat n) (p : Ω → Vec n)
    (hθ : Measurable θ) (hr : Measurable r) (hp : Measurable p) :
    Measurable (fun ω => CNDMatrixProx.gradient (θ ω) (r ω) (p ω)) := by
  apply measurable_pi_iff.mpr
  intro i
  have hsum : Measurable (fun ω => ∑ j, r ω i j * p ω j) :=
    Finset.measurable_sum Finset.univ (fun j _ =>
      (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hr)).mul
        ((measurable_pi_apply j).comp hp)))
  exact ((measurable_pi_apply i).comp hθ).sub hsum

theorem measurable_prediction_history (θ : Ω → Vec n) (r : Ω → Mat n) (p : Ω → Vec n)
    (hθ : Measurable θ) (hr : Measurable r) (hp : Measurable p) :
    Measurable (fun ω => CNDMatrixProx.prediction (θ ω) (r ω) (p ω)) := by
  have hgrad := measurable_gradient_history θ r p hθ hr hp
  have hsum : Measurable (fun ω => ∑ j, p ω j * θ ω j) :=
    Finset.measurable_sum Finset.univ (fun j _ =>
      ((measurable_pi_apply j).comp hp).mul ((measurable_pi_apply j).comp hθ))
  apply measurable_pi_iff.mpr
  intro i
  exact ((measurable_pi_apply i).comp hgrad).sub hsum

/-- Choosing a fixed proof of index nonemptiness does not change the actual matrix. -/
theorem actualTransport_proof_irrel (W : ℝ)
    (hne hne' : (Finset.univ : Finset (Fin n)).Nonempty) (z : TransportInput n) :
    actualTransport W hne z = exactRemap z.1 z.2.1 z.2.2 W hne' := rfl

end Part2.ExactGreedyMeasurable

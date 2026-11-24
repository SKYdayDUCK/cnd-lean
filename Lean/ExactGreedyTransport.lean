import CNDMatrixProx
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.BigOperators.Fin

noncomputable section

namespace Part2.ExactGreedyTransport

open scoped BigOperators

def overlap (a b c d : ℝ) : ℝ := max 0 (min b d - max a c)

theorem overlap_nonneg (a b c d : ℝ) : 0 ≤ overlap a b c d := le_max_left _ _

theorem overlap_symmetric (a b c d : ℝ) : overlap a b c d = overlap c d a b := by
  simp [overlap, min_comm, max_comm]

theorem overlap_min_identity (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    overlap a b c d = min b d - min a d - min b c + min a c := by
  unfold overlap
  rcases le_total a c with hac | hca <;>
    rcases le_total b d with hbd | hdb
  · rw [max_eq_right hac, min_eq_left hbd, min_eq_left (hac.trans hcd), min_eq_left hac]
    by_cases hbc : b ≤ c
    · rw [min_eq_left hbc, max_eq_left (by linarith)]
      ring
    · rw [min_eq_right (le_of_not_ge hbc), max_eq_right (by linarith)]
      ring
  · rw [max_eq_right hac, min_eq_right hdb, min_eq_left (hac.trans hcd),
      min_eq_right (hcd.trans hdb), min_eq_left hac, max_eq_right (by linarith)]
    ring
  · rw [max_eq_left hca, min_eq_left hbd, min_eq_left (hab.trans hbd),
      min_eq_right (hca.trans hab), min_eq_right hca, max_eq_right (by linarith)]
    ring
  · rw [max_eq_left hca, min_eq_right hdb, min_eq_right (hca.trans hab), min_eq_right hca]
    by_cases had : a ≤ d
    · rw [min_eq_left had, max_eq_right (by linarith)]
      ring
    · rw [min_eq_right (le_of_not_ge had), max_eq_left (by linarith)]
      ring

def massPrefix (s : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, s i

theorem prefix_zero (s : ℕ → ℝ) : massPrefix s 0 = 0 := by simp [massPrefix]

theorem prefix_succ (s : ℕ → ℝ) (n : ℕ) : massPrefix s (n + 1) = massPrefix s n + s n :=
  Finset.sum_range_succ s n

theorem prefix_mono (s : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i) : Monotone (massPrefix s) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [prefix_succ]
  linarith [hs n]

def intervalFlow (s d : ℕ → ℝ) (i j : ℕ) : ℝ :=
  overlap (massPrefix s i) (massPrefix s (i + 1)) (massPrefix d j) (massPrefix d (j + 1))

theorem intervalFlow_nonneg (s d : ℕ → ℝ) (i j : ℕ) : 0 ≤ intervalFlow s d i j :=
  overlap_nonneg _ _ _ _

/-- massPrefix telescoping is the main marginal identity for ordered interval filling. -/
theorem intervalFlow_row_prefix (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (i n : ℕ) :
    (∑ j ∈ Finset.range n, intervalFlow s d i j) =
      min (massPrefix s (i + 1)) (massPrefix d n) - min (massPrefix s i) (massPrefix d n) := by
  have ha : massPrefix s i ≤ massPrefix s (i + 1) := prefix_mono s hs (Nat.le_succ i)
  have hnonneg : ∀ k, 0 ≤ massPrefix s k := by
    intro k
    simpa [prefix_zero] using prefix_mono s hs (Nat.zero_le k)
  have hterm (j : ℕ) : intervalFlow s d i j =
      (min (massPrefix s (i + 1)) (massPrefix d (j + 1)) - min (massPrefix s i) (massPrefix d (j + 1))) -
      (min (massPrefix s (i + 1)) (massPrefix d j) - min (massPrefix s i) (massPrefix d j)) := by
    rw [intervalFlow, overlap_min_identity _ _ _ _ ha (prefix_mono d hd (Nat.le_succ j))]
    ring
  simp_rw [hterm]
  rw [Finset.sum_range_sub (fun j =>
    min (massPrefix s (i + 1)) (massPrefix d j) - min (massPrefix s i) (massPrefix d j)) n]
  simp [prefix_zero, min_eq_right (hnonneg (i + 1)), min_eq_right (hnonneg i)]

theorem intervalFlow_column_prefix (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (j n : ℕ) :
    (∑ i ∈ Finset.range n, intervalFlow s d i j) =
      min (massPrefix s n) (massPrefix d (j + 1)) - min (massPrefix s n) (massPrefix d j) := by
  have h := intervalFlow_row_prefix d s hd hs j n
  simpa only [intervalFlow, overlap_symmetric, min_comm] using h

theorem intervalFlow_row_sum (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (n i : ℕ) (hi : i < n)
    (hbal : massPrefix s n = massPrefix d n) :
    (∑ j ∈ Finset.range n, intervalFlow s d i j) = s i := by
  rw [intervalFlow_row_prefix s d hs hd i n, ← hbal]
  rw [min_eq_left (prefix_mono s hs (by omega : i + 1 ≤ n)),
    min_eq_left (prefix_mono s hs (by omega : i ≤ n)), prefix_succ]
  ring

theorem intervalFlow_column_sum (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (n j : ℕ) (hj : j < n)
    (hbal : massPrefix s n = massPrefix d n) :
    (∑ i ∈ Finset.range n, intervalFlow s d i j) = d j := by
  have h := intervalFlow_row_sum d s hd hs n j hj hbal.symm
  simpa only [intervalFlow, overlap_symmetric] using h

theorem overlap_le_length_left (a b c d : ℝ) (hab : a ≤ b) :
    overlap a b c d ≤ b - a := by
  apply max_le
  · linarith
  · have h1 := min_le_left b d
    have h2 := le_max_left a c
    linarith

theorem intervalFlow_positive_edge (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (i j : ℕ) (hflow : intervalFlow s d i j ≠ 0) :
    0 < s i ∧ 0 < d j := by
  have hpos := lt_of_le_of_ne (intervalFlow_nonneg s d i j) (Ne.symm hflow)
  have hleft := overlap_le_length_left (massPrefix s i) (massPrefix s (i + 1))
    (massPrefix d j) (massPrefix d (j + 1)) (prefix_mono s hs (Nat.le_succ i))
  have hright := overlap_le_length_left (massPrefix d j) (massPrefix d (j + 1))
    (massPrefix s i) (massPrefix s (i + 1)) (prefix_mono d hd (Nat.le_succ j))
  rw [← overlap_symmetric] at hright
  change overlap _ _ _ _ > 0 at hpos
  simp only [prefix_succ] at hleft hright hpos
  constructor <;> linarith

/-- The northwest rule: fill the smaller of the two remaining cell margins. -/
theorem residual_min_identity (a b c d : ℝ) (hab : a ≤ b) (hcd : c ≤ d) :
    min (b - a - (min b c - min a c))
      (d - c - (min a d - min a c)) = overlap a b c d := by
  rcases le_total a c with hac | hca
  · rw [min_eq_left hac, min_eq_left (hac.trans hcd)]
    by_cases hbc : b ≤ c
    · rw [min_eq_left hbc]
      have hnonneg : 0 ≤ d - c := sub_nonneg.mpr hcd
      have hdisj : min b d - max a c ≤ 0 := by
        have h1 := min_le_left b d
        have h2 := le_max_right a c
        linarith
      simp [overlap, max_eq_left hdisj, min_eq_left hnonneg]
    · have hcb : c ≤ b := le_of_not_ge hbc
      rw [min_eq_right hcb]
      have h1 : b - a - (c - a) = b - c := by ring
      have h2 : d - c - (a - a) = d - c := by ring
      rw [h1, h2, min_sub_sub_right, overlap, max_eq_right hac,
        max_eq_right (sub_nonneg.mpr (le_min hcb hcd))]
  · rw [min_eq_right hca, min_eq_right (hca.trans hab)]
    by_cases hda : d ≤ a
    · rw [min_eq_right hda]
      have hdisj : min b d - max a c ≤ 0 := by
        have h1 := min_le_right b d
        have h2 := le_max_left a c
        linarith
      simp [overlap, max_eq_left hdisj, min_eq_right (sub_nonneg.mpr hab)]
    · have had : a ≤ d := le_of_not_ge hda
      rw [min_eq_left had]
      have h1 : b - a - (c - c) = b - a := by ring
      have h2 : d - c - (a - c) = d - a := by ring
      rw [h1, h2, min_sub_sub_right, overlap, max_eq_left hca,
        max_eq_right (sub_nonneg.mpr (le_min hab had))]

theorem intervalFlow_greedy_recurrence (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (i j : ℕ) :
    intervalFlow s d i j =
      min (s i - ∑ l : Fin j, intervalFlow s d i l.val)
        (d j - ∑ k : Fin i, intervalFlow s d k.val j) := by
  rw [Fin.sum_univ_eq_sum_range (fun l => intervalFlow s d i l),
    Fin.sum_univ_eq_sum_range (fun k => intervalFlow s d k j),
    intervalFlow_row_prefix s d hs hd i j, intervalFlow_column_prefix s d hs hd j i]
  have h := residual_min_identity (massPrefix s i) (massPrefix s (i + 1))
    (massPrefix d j) (massPrefix d (j + 1))
    (prefix_mono s hs (Nat.le_succ i)) (prefix_mono d hd (Nat.le_succ j))
  rw [prefix_succ s i, prefix_succ d j] at h
  simpa only [add_sub_cancel_left, intervalFlow, prefix_succ] using h.symm

/-- An actual well-founded fill recursion, in increasing row and column indices. -/
def greedyFlow (s d : ℕ → ℝ) (i j : ℕ) : ℝ :=
  min (s i - ∑ l : Fin j, greedyFlow s d i l.val)
    (d j - ∑ k : Fin i, greedyFlow s d k.val j)
termination_by i + j
decreasing_by all_goals omega

/-- Closed prefix overlap is exactly the original increasing-index greedy recursion. -/
theorem intervalFlow_eq_greedyFlow (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (i j : ℕ) : intervalFlow s d i j = greedyFlow s d i j := by
  have main : ∀ N i j, i + j = N → intervalFlow s d i j = greedyFlow s d i j := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro i j hij
      rw [greedyFlow, intervalFlow_greedy_recurrence s d hs hd i j]
      congr 1
      · congr 1
        apply Finset.sum_congr rfl
        intro l _
        exact ih (i + l.val) (by omega) i l.val rfl
      · congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact ih (k.val + j) (by omega) k.val j rfl
  exact main (i + j) i j rfl

/-- Every increasing-index fill table satisfying the actual residual rule is unique. -/
theorem greedyFlow_unique (s d : ℕ → ℝ) (f : ℕ → ℕ → ℝ)
    (hf : ∀ i j, f i j = min (s i - ∑ l : Fin j, f i l.val)
      (d j - ∑ k : Fin i, f k.val j)) : f = greedyFlow s d := by
  have main : ∀ N i j, i + j = N → f i j = greedyFlow s d i j := by
    intro N
    induction N using Nat.strong_induction_on with
    | h N ih =>
      intro i j hij
      rw [hf, greedyFlow]
      congr 1
      · congr 1
        apply Finset.sum_congr rfl
        intro l _
        exact ih (i + l.val) (by omega) i l.val rfl
      · congr 1
        apply Finset.sum_congr rfl
        intro k _
        exact ih (k.val + j) (by omega) k.val j rfl
  funext i j
  exact main (i + j) i j rfl

/-- The two quantities minimized by the fill recursion really are nonnegative residuals. -/
theorem greedyFlow_remaining_nonneg (s d : ℕ → ℝ) (hs : ∀ i, 0 ≤ s i)
    (hd : ∀ i, 0 ≤ d i) (i j : ℕ) :
    0 ≤ s i - ∑ l : Fin j, greedyFlow s d i l.val ∧
      0 ≤ d j - ∑ k : Fin i, greedyFlow s d k.val j := by
  have hg : 0 ≤ greedyFlow s d i j := by
    rw [← intervalFlow_eq_greedyFlow s d hs hd i j]
    exact intervalFlow_nonneg _ _ _ _
  rw [greedyFlow] at hg
  exact ⟨hg.trans (min_le_left _ _), hg.trans (min_le_right _ _)⟩

variable {n : ℕ}

def finiteValue (s : Fin n → ℝ) (i : ℕ) : ℝ := if h : i < n then s ⟨i, h⟩ else 0

theorem finiteValue_apply (s : Fin n → ℝ) (i : Fin n) : finiteValue s i.val = s i := by
  simp [finiteValue, i.isLt]

theorem finiteValue_nonneg (s : Fin n → ℝ) (hs : ∀ i, 0 ≤ s i) (i : ℕ) :
    0 ≤ finiteValue s i := by
  unfold finiteValue
  split_ifs
  · apply hs
  · exact le_refl _

theorem finiteValue_total (s : Fin n → ℝ) : massPrefix (finiteValue s) n = ∑ i, s i := by
  symm
  exact Finset.sum_fin_eq_sum_range s

def excessNat (q p : Fin n → ℝ) : ℕ → ℝ := finiteValue (ConvexRemap.excess q p)
def demandNat (q p : Fin n → ℝ) : ℕ → ℝ := finiteValue (ConvexRemap.demand q p)

theorem excessNat_nonneg (q p : Fin n → ℝ) (i : ℕ) : 0 ≤ excessNat q p i :=
  finiteValue_nonneg _ (ConvexRemap.excess_nonneg q p) i

theorem demandNat_nonneg (q p : Fin n → ℝ) (i : ℕ) : 0 ≤ demandNat q p i :=
  finiteValue_nonneg _ (ConvexRemap.demand_nonneg q p) i

/-- These are the actual recursive greedy excess-to-demand masses. -/
def orderedFlow (q p : Fin n → ℝ) (i j : Fin n) : ℝ :=
  greedyFlow (excessNat q p) (demandNat q p) i.val j.val

theorem orderedFlow_eq_overlap (q p : Fin n → ℝ) (i j : Fin n) :
    orderedFlow q p i j = intervalFlow (excessNat q p) (demandNat q p) i.val j.val :=
  (intervalFlow_eq_greedyFlow _ _ (excessNat_nonneg q p) (demandNat_nonneg q p) _ _).symm

theorem orderedFlow_nonneg (q p : Fin n → ℝ) (i j : Fin n) : 0 ≤ orderedFlow q p i j := by
  rw [orderedFlow_eq_overlap]
  exact intervalFlow_nonneg _ _ _ _

theorem orderedFlow_balanced (q p : Fin n → ℝ) (hs : (∑ i, q i) = ∑ i, p i) :
    massPrefix (excessNat q p) n = massPrefix (demandNat q p) n := by
  unfold excessNat demandNat
  rw [finiteValue_total, finiteValue_total]
  exact (ConvexRemap.balanced_mass q p hs).symm

theorem orderedFlow_row_sum (q p : Fin n → ℝ) (hs : (∑ i, q i) = ∑ i, p i) (i : Fin n) :
    (∑ j, orderedFlow q p i j) = ConvexRemap.excess q p i := by
  simp_rw [orderedFlow_eq_overlap]
  rw [Fin.sum_univ_eq_sum_range (fun j => intervalFlow (excessNat q p) (demandNat q p) i.val j),
    intervalFlow_row_sum _ _ (excessNat_nonneg q p) (demandNat_nonneg q p) n i.val i.isLt
      (orderedFlow_balanced q p hs)]
  exact finiteValue_apply _ i

theorem orderedFlow_column_sum (q p : Fin n → ℝ) (hs : (∑ i, q i) = ∑ i, p i) (j : Fin n) :
    (∑ i, orderedFlow q p i j) = ConvexRemap.demand q p j := by
  simp_rw [orderedFlow_eq_overlap]
  rw [Fin.sum_univ_eq_sum_range (fun i => intervalFlow (excessNat q p) (demandNat q p) i j.val),
    intervalFlow_column_sum _ _ (excessNat_nonneg q p) (demandNat_nonneg q p) n j.val j.isLt
      (orderedFlow_balanced q p hs)]
  exact finiteValue_apply _ j

theorem orderedFlow_edge (q p : Fin n → ℝ) (i j : Fin n) (hf : orderedFlow q p i j ≠ 0) :
    p i < q i ∧ q j < p j := by
  rw [orderedFlow_eq_overlap] at hf
  obtain ⟨hi, hj⟩ := intervalFlow_positive_edge _ _ (excessNat_nonneg q p) (demandNat_nonneg q p) _ _ hf
  change 0 < finiteValue (ConvexRemap.excess q p) i.val at hi
  change 0 < finiteValue (ConvexRemap.demand q p) j.val at hj
  rw [finiteValue_apply] at hi hj
  constructor
  · by_contra h
    have hz : ConvexRemap.excess q p i = 0 := max_eq_right (by linarith : q i - p i ≤ 0)
    linarith
  · by_contra h
    have hz : ConvexRemap.demand q p j = 0 := max_eq_right (by linarith : p j - q j ≤ 0)
    linarith

/-- Excess and demand never coexist at one index, so the retained diagonal is exact. -/
theorem orderedFlow_diagonal_zero (q p : Fin n → ℝ) (i : Fin n) : orderedFlow q p i i = 0 := by
  by_contra h
  obtain ⟨h1, h2⟩ := orderedFlow_edge q p i i h
  linarith

def orderedPlan (q p : Fin n → ℝ) (i j : Fin n) : ℝ :=
  (if i = j then min (q i) (p i) else 0) + orderedFlow q p i j

theorem orderedPlan_nonneg (q p : Fin n → ℝ) (hq : ∀ i, 0 ≤ q i)
    (hp : ∀ i, 0 ≤ p i) (i j : Fin n) : 0 ≤ orderedPlan q p i j := by
  apply add_nonneg _ (orderedFlow_nonneg q p i j)
  split_ifs
  · exact le_min (hq i) (hp i)
  · exact le_refl _

theorem orderedPlan_row_sum (q p : Fin n → ℝ) (hs : (∑ i, q i) = ∑ i, p i) (i : Fin n) :
    (∑ j, orderedPlan q p i j) = q i := by
  simp only [orderedPlan, Finset.sum_add_distrib]
  rw [orderedFlow_row_sum q p hs i]
  simpa using ConvexRemap.retained_add_excess q p i

theorem orderedPlan_column_sum (q p : Fin n → ℝ) (hs : (∑ i, q i) = ∑ i, p i) (j : Fin n) :
    (∑ i, orderedPlan q p i j) = p j := by
  simp only [orderedPlan, Finset.sum_add_distrib]
  rw [orderedFlow_column_sum q p hs j]
  simpa using ConvexRemap.retained_add_demand q p j

/-- The least numbered gradient minimizer, implemented with Finset.min'. -/
def argminSet (g : Fin n → ℝ) : Finset (Fin n) := Finset.univ.filter (fun i => ∀ j, g i ≤ g j)

theorem argminSet_nonempty (g : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    (argminSet g).Nonempty := by
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image Finset.univ g hne
  exact ⟨m, Finset.mem_filter.mpr ⟨hm, fun j => hmin j (Finset.mem_univ j)⟩⟩

def leastArgmin (g : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty) : Fin n :=
  (argminSet g).min' (argminSet_nonempty g hne)

theorem leastArgmin_minimizes (g : Fin n → ℝ) (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    ∀ j, g (leastArgmin g hne) ≤ g j := by
  exact (Finset.mem_filter.mp (Finset.min'_mem (argminSet g) (argminSet_nonempty g hne))).2

theorem leastArgmin_le_every_minimizer (g : Fin n → ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) (i : Fin n) (hi : ∀ j, g i ≤ g j) :
    leastArgmin g hne ≤ i := by
  exact Finset.min'_le (argminSet g) i (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)

theorem simplex_index_nonempty (q : Fin n → ℝ) (hq : q ∈ stdSimplex ℝ (Fin n)) :
    (Finset.univ : Finset (Fin n)).Nonempty := by
  by_contra hempty
  have hmass := hq.2
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hmass
  norm_num at hmass

/-- The original algorithm's exact numbered transport and least-index zero-row repair. -/
def exactRemap (q p g : Fin n → ℝ) (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty) (k j : Fin n) : ℝ :=
  if q k = 0 then
    if g k ≤ g (leastArgmin g hne) + W then (if k = j then 1 else 0)
    else (if leastArgmin g hne = j then 1 else 0)
  else orderedPlan q p k j / q k

theorem exactRemap_nonneg (q p g : Fin n → ℝ) (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (k j : Fin n) :
    0 ≤ exactRemap q p g W hne k j := by
  unfold exactRemap
  split_ifs
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact div_nonneg (orderedPlan_nonneg q p hq hp k j) (hq k)

theorem exactRemap_row_sum (q p g : Fin n → ℝ) (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (hs : (∑ i, q i) = ∑ i, p i) (k : Fin n) :
    (∑ j, exactRemap q p g W hne k j) = 1 := by
  by_cases hz : q k = 0
  · by_cases hsafe : g k ≤ g (leastArgmin g hne) + W <;> simp [exactRemap, hz, hsafe]
  · simp only [exactRemap, hz, if_false, ← Finset.sum_div]
    rw [orderedPlan_row_sum q p hs k, div_self hz]

theorem orderedPlan_zero_source (q p : Fin n → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, q i) = ∑ i, p i)
    (k j : Fin n) (hz : q k = 0) : orderedPlan q p k j = 0 := by
  have hle : orderedPlan q p k j ≤ ∑ l, orderedPlan q p k l :=
    Finset.single_le_sum (fun l _ => orderedPlan_nonneg q p hq hp k l) (Finset.mem_univ j)
  rw [orderedPlan_row_sum q p hs k, hz] at hle
  exact le_antisymm hle (orderedPlan_nonneg q p hq hp k j)

theorem source_times_exactRemap (q p g : Fin n → ℝ) (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, q i) = ∑ i, p i)
    (k j : Fin n) : q k * exactRemap q p g W hne k j = orderedPlan q p k j := by
  by_cases hz : q k = 0
  · rw [orderedPlan_zero_source q p hq hp hs k j hz]
    simp [hz]
  · simp only [exactRemap, hz, if_false]
    exact mul_div_cancel₀ _ hz

theorem exactRemap_consistent (q p g : Fin n → ℝ) (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, q i) = ∑ i, p i)
    (j : Fin n) : (∑ k, q k * exactRemap q p g W hne k j) = p j := by
  simp_rw [source_times_exactRemap q p g W hne hq hp hs]
  exact orderedPlan_column_sum q p hs j

theorem exactRemap_positive_destination (q p g : Fin n → ℝ) (W : ℝ)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, q i) = ∑ i, p i)
    (k j : Fin n) (hk : q k ≠ 0) (hM : exactRemap q p g W hne k j ≠ 0) : 0 < p j := by
  have hqpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hk)
  have hMpos : 0 < exactRemap q p g W hne k j :=
    lt_of_le_of_ne (exactRemap_nonneg q p g W hne hq hp k j) (Ne.symm hM)
  have hle : q k * exactRemap q p g W hne k j ≤ p j := by
    rw [← exactRemap_consistent q p g W hne hq hp hs j]
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (hq i) (exactRemap_nonneg q p g W hne hq hp i j))
      (Finset.mem_univ k)
  exact (mul_pos hqpos hMpos).trans_le hle

theorem exactRemap_allowed (θ : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (q p : Fin n → ℝ)
    (W : ℝ) (hr : CND.IsCND r) (hW : 0 ≤ W)
    (hq : q ∈ stdSimplex ℝ (Fin n)) (hp : p ∈ stdSimplex ℝ (Fin n))
    (hmin : IsMinOn (CNDMatrixProx.objective θ r q W) (stdSimplex ℝ (Fin n)) p)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (k j : Fin n) (hM : exactRemap q p (CNDMatrixProx.gradient θ r p) W hne k j ≠ 0) :
    CNDMatrixProx.gradient θ r p j ≤
      CNDMatrixProx.gradient θ r p (leastArgmin (CNDMatrixProx.gradient θ r p) hne) + W ∧
      (j = k ∨ W ≤ CNDMatrixProx.gradient θ r p k - CNDMatrixProx.gradient θ r p j) := by
  let g := CNDMatrixProx.gradient θ r p
  let m := leastArgmin g hne
  change g j ≤ g m + W ∧ (j = k ∨ W ≤ g k - g j)
  change exactRemap q p g W hne k j ≠ 0 at hM
  by_cases hz : q k = 0
  · by_cases hsafe : g k ≤ g m + W
    · have hkj : k = j := by
        by_contra h
        exact hM (by simp [exactRemap, hz, hsafe, h, m])
      subst j
      exact ⟨hsafe, Or.inl rfl⟩
    · have hmj : m = j := by
        by_contra h
        exact hM (by simp [exactRemap, hz, hsafe, h, m])
      subst j
      exact ⟨by linarith, Or.inr (by linarith [lt_of_not_ge hsafe])⟩
  · have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
    have hpj := exactRemap_positive_destination q p g W hne hq.1 hp.1 hs k j hz hM
    have hsupport := CNDMatrixProx.minimizer_support_bound θ r q p W hr.1 hr.2.1 hW hp hmin j m hpj
    refine ⟨by linarith, ?_⟩
    by_cases hjk : j = k
    · exact Or.inl hjk
    · right
      have hplan : orderedPlan q p k j ≠ 0 := by
        intro hplan
        exact hM (by simp [exactRemap, hz, hplan])
      have hflow : orderedFlow q p k j ≠ 0 := by
        simpa [orderedPlan, Ne.symm hjk] using hplan
      obtain ⟨hk, hj⟩ := orderedFlow_edge q p k j hflow
      exact CNDMatrixProx.minimizer_donor_receiver θ r q p W hr.1 hr.2.1 hq hp hmin j k hj hk

/-- Exact original numbered remapping for every actual matrix-proximal minimizer. -/
theorem exactRemap_all_destinations_public_span
    (θ : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (q p b : Fin n → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hp : p ∈ stdSimplex ℝ (Fin n))
    (hmin : IsMinOn (CNDMatrixProx.objective θ r q W) (stdSimplex ℝ (Fin n)) p)
    (hne : (Finset.univ : Finset (Fin n)).Nonempty)
    (hb : ∀ i j, b j - b i ≤ W) (k l i j : Fin n)
    (hi : exactRemap q p (CNDMatrixProx.gradient θ r p) W hne k i ≠ 0)
    (hj : exactRemap q p (CNDMatrixProx.gradient θ r p) W hne l j ≠ 0) :
    |(CNDMatrixProx.prediction θ r p i + b i) -
      (CNDMatrixProx.prediction θ r p j + b j)| ≤ 2 * W := by
  have hiu := (exactRemap_allowed θ r q p W hr hW hq hp hmin hne k i hi).1
  have hju := (exactRemap_allowed θ r q p W hr hW hq hp hmin hne l j hj).1
  have hil := leastArgmin_minimizes (CNDMatrixProx.gradient θ r p) hne i
  have hjl := leastArgmin_minimizes (CNDMatrixProx.gradient θ r p) hne j
  have hbij := hb i j
  have hbji := hb j i
  rw [abs_le]
  dsimp [CNDMatrixProx.prediction]
  constructor <;> linarith

/-- Exact original numbered remapping for every actual matrix-proximal minimizer. -/
theorem original_numbered_remapping_for_minimizer
    (θ : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (q p : Fin n → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ (Fin n))
    (hp : p ∈ stdSimplex ℝ (Fin n))
    (hmin : IsMinOn (CNDMatrixProx.objective θ r q W) (stdSimplex ℝ (Fin n)) p) :
    let hne := simplex_index_nonempty q hq
    let m := leastArgmin (CNDMatrixProx.gradient θ r p) hne
    let M := exactRemap q p (CNDMatrixProx.gradient θ r p) W hne
    (∀ i, CNDMatrixProx.gradient θ r p m ≤ CNDMatrixProx.gradient θ r p i) ∧
    (∀ i, (∀ j, CNDMatrixProx.gradient θ r p i ≤ CNDMatrixProx.gradient θ r p j) → m ≤ i) ∧
    (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
    (∀ j, ∑ k, q k * M k j = p j) ∧
    (∀ k j, M k j ≠ 0 →
      CNDMatrixProx.prediction θ r p j ≤ CNDMatrixProx.prediction θ r p m + W ∧
      (j = k ∨ W ≤ CNDMatrixProx.prediction θ r p k - CNDMatrixProx.prediction θ r p j)) ∧
    (∀ b : Fin n → ℝ, (∀ i j, b j - b i ≤ W) →
      (∀ k, (∑ j, M k j * (CNDMatrixProx.prediction θ r p j + b j)) ≤
        CNDMatrixProx.prediction θ r p k + b k) ∧
      (∀ i j, 0 < p i → 0 < p j →
        |(CNDMatrixProx.prediction θ r p i + b i) -
          (CNDMatrixProx.prediction θ r p j + b j)| ≤ 2 * W)) := by
  dsimp only
  let hne := simplex_index_nonempty q hq
  let g := CNDMatrixProx.gradient θ r p
  let m := leastArgmin g hne
  let M := exactRemap q p g W hne
  have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
  have hMn : ∀ k j, 0 ≤ M k j := exactRemap_nonneg q p g W hne hq.1 hp.1
  have hMs : ∀ k, ∑ j, M k j = 1 := exactRemap_row_sum q p g W hne hs
  have hMc : ∀ j, ∑ k, q k * M k j = p j := exactRemap_consistent q p g W hne hq.1 hp.1 hs
  have hallowed : ∀ k j, M k j ≠ 0 →
      CNDMatrixProx.prediction θ r p j ≤ CNDMatrixProx.prediction θ r p m + W ∧
      (j = k ∨ W ≤ CNDMatrixProx.prediction θ r p k - CNDMatrixProx.prediction θ r p j) := by
    intro k j hM
    obtain ⟨hsmall, hgap⟩ := exactRemap_allowed θ r q p W hr hW hq hp hmin hne k j hM
    constructor
    · dsimp [CNDMatrixProx.prediction]
      linarith
    · rcases hgap with hsame | hdrop
      · exact Or.inl hsame
      · right
        rw [CNDMatrixProx.prediction_difference]
        exact hdrop
  refine ⟨leastArgmin_minimizes g hne, leastArgmin_le_every_minimizer g hne,
    hMn, hMs, hMc, hallowed, ?_⟩
  intro b hb
  constructor
  · intro k
    calc
      _ ≤ ∑ j, M k j * (CNDMatrixProx.prediction θ r p k + b k) := by
        apply Finset.sum_le_sum
        intro j _
        change M k j * (CNDMatrixProx.prediction θ r p j + b j) ≤
          M k j * (CNDMatrixProx.prediction θ r p k + b k)
        by_cases hz : M k j = 0
        · simp [hz]
        · have horder : CNDMatrixProx.prediction θ r p j + b j ≤
              CNDMatrixProx.prediction θ r p k + b k := by
            rcases (hallowed k j hz).2 with hsame | hdrop
            · subst j
              exact le_refl _
            · have hpub := hb k j
              linarith
          exact mul_le_mul_of_nonneg_left horder (hMn k j)
      _ = CNDMatrixProx.prediction θ r p k + b k := by rw [← Finset.sum_mul, hMs k, one_mul]
  · exact CNDMatrixProx.minimizer_public_support_span θ r q p b W hr hW hp hmin hb

/-- The paper's actual minimum-norm proximal point and exact numbered step 4,
with no input minimizer or gradient-gap premise. -/
theorem canonical_original_numbered_remapping
    (θ : Fin n → ℝ) (r : Fin n → Fin n → ℝ) (q : Fin n → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ (Fin n)) :
    let p := CNDMatrixProx.minimumNormProx θ r q W hr hW hq
    let hne := simplex_index_nonempty q hq
    let m := leastArgmin (CNDMatrixProx.gradient θ r p) hne
    let M := exactRemap q p (CNDMatrixProx.gradient θ r p) W hne
    p ∈ stdSimplex ℝ (Fin n) ∧
    IsMinOn (CNDMatrixProx.objective θ r q W) (stdSimplex ℝ (Fin n)) p ∧
    IsMinOn CNDMatrixProx.squaredNorm (CNDMatrixProx.minimizerSet θ r q W) p ∧
    (∀ i, CNDMatrixProx.gradient θ r p m ≤ CNDMatrixProx.gradient θ r p i) ∧
    (∀ i, (∀ j, CNDMatrixProx.gradient θ r p i ≤ CNDMatrixProx.gradient θ r p j) → m ≤ i) ∧
    (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
    (∀ j, ∑ k, q k * M k j = p j) ∧
    (∀ k j, M k j ≠ 0 →
      CNDMatrixProx.prediction θ r p j ≤ CNDMatrixProx.prediction θ r p m + W ∧
      (j = k ∨ W ≤ CNDMatrixProx.prediction θ r p k - CNDMatrixProx.prediction θ r p j)) ∧
    (∀ b : Fin n → ℝ, (∀ i j, b j - b i ≤ W) →
      (∀ k, (∑ j, M k j * (CNDMatrixProx.prediction θ r p j + b j)) ≤
        CNDMatrixProx.prediction θ r p k + b k) ∧
      (∀ i j, 0 < p i → 0 < p j →
        |(CNDMatrixProx.prediction θ r p i + b i) -
          (CNDMatrixProx.prediction θ r p j + b j)| ≤ 2 * W)) := by
  dsimp only
  have hs := CNDMatrixProx.minimumNormProx_spec θ r q W hr hW hq
  exact ⟨hs.1.1, hs.1.2, hs.2,
    original_numbered_remapping_for_minimizer θ r q _ W hr hW hq hs.1.1 hs.1.2⟩

end Part2.ExactGreedyTransport

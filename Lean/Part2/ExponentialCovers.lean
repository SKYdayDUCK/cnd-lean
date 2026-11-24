import Part2.ExponentialExperts
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Actual finite-trajectory interval and covering costs

This module connects the local exact exponential potential bound to the
original time indices and to admissible covers with actual log-beta costs.
It does not assert the kappa remainder inequality or a statistical event.
-/

namespace Part2.ExponentialCovers

noncomputable section

open Finset Part2.ExponentialExperts

variable {E A : Type*} [Fintype E] [DecidableEq E] [Nonempty E]

/-- E7 on an actual interval of the original finite trajectory, not an
assumed restarted process. The update and positivity at its start are
derived from the one original trajectory. -/
theorem interval_regret (N u n : ℕ) (hwithin : u + n ≤ N)
    (w z x : ℕ → E → ℝ) (eta : E → ℝ) (active : ℕ → Finset E)
    (r : ℕ → ℝ) (e : E) (heta : 0 < eta e)
    (hinit : ∀ i, 0 < w 0 i)
    (hupdate : ∀ t < N, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hlinear : ∀ t < N, ∀ i ∈ active t, z t i = eta i * x t i)
    (hcover : ∀ t ∈ Ico u (u + n), e ∈ active t)
    (hgap : ∀ t ∈ Ico u (u + n), r t ≤ x t e) :
    (∑ t ∈ Ico u (u + n), r t) ≤
      (Real.log (1 / beta (w u) e) +
        ∑ t ∈ Ico u (u + n), increment (w t) (z t)) / eta e := by
  have h := segment_regret n (fun t => w (u + t)) (fun t => z (u + t))
    (fun t => x (u + t) e) (fun t => r (u + t)) (eta e) heta e
    (by simpa using trajectory_pos N w z hinit hupdate u (by omega))
    (by
      intro t ht i
      simpa [Nat.add_assoc] using hupdate (u + t) (by omega) i)
    (by
      intro t ht
      exact hlinear (u + t) (by omega) e (hcover _ (by simp; omega)))
    (by
      intro t ht
      exact hgap _ (by simp; omega))
  simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, Nat.add_zero] using h

/-- E8 with the original global time index and an actual birth-weight
equality. No normalization of the later birth-time total mass is assumed. -/
theorem interval_birth_regret (N u n : ℕ) (hwithin : u + n ≤ N)
    (w z x : ℕ → E → ℝ) (eta : E → ℝ) (active : ℕ → Finset E)
    (r : ℕ → ℝ) (e : E) (pi : ℝ) (heta : 0 < eta e)
    (hinit : ∀ i, 0 < w 0 i) (hbirth : w u e = pi)
    (hupdate : ∀ t < N, ∀ i, w (t + 1) i = step (w t) (z t) i)
    (hlinear : ∀ t < N, ∀ i ∈ active t, z t i = eta i * x t i)
    (hcover : ∀ t ∈ Ico u (u + n), e ∈ active t)
    (hgap : ∀ t ∈ Ico u (u + n), r t ≤ x t e) :
    (∑ t ∈ Ico u (u + n), r t) ≤
      (Real.log (1 / pi) + Real.log (mass (w (u + n)))) / eta e := by
  have h := birth_regret n (fun t => w (u + t)) (fun t => z (u + t))
    (fun t => x (u + t) e) (fun t => r (u + t)) (eta e) pi heta e
    (by simpa using trajectory_pos N w z hinit hupdate u (by omega))
    (by simpa using hbirth)
    (by
      intro t ht i
      simpa [Nat.add_assoc] using hupdate (u + t) (by omega) i)
    (by
      intro t ht
      exact hlinear (u + t) (by omega) e (hcover _ (by simp; omega)))
    (by
      intro t ht
      exact hgap _ (by simp; omega))
  simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left] using h

/-- A finite interval partition with an actual selected expert for each
nonempty block. The label equation makes all selected experts compare the
same arm, and all endpoints remain in the finite horizon. -/
structure Cover (N : ℕ) (active : ℕ → Finset E) (arm : E → A)
    (target : A) (H : Finset ℕ) where
  partition : Part2.Intervals.Partition H
  start : ℕ → ℕ
  length : ℕ → ℕ
  expert : ℕ → E
  block_eq : ∀ j ∈ partition.labels,
    partition.block j = Ico (start j) (start j + length j)
  length_pos : ∀ j ∈ partition.labels, 0 < length j
  within : ∀ j ∈ partition.labels, start j + length j ≤ N
  awake : ∀ j ∈ partition.labels, ∀ t ∈ partition.block j, expert j ∈ active t
  same_arm : ∀ j ∈ partition.labels, arm (expert j) = target

def Cover.localCost {N : ℕ} {active : ℕ → Finset E} {arm : E → A}
    {target : A} {H : Finset ℕ} (C : Cover N active arm target H)
    (w z : ℕ → E → ℝ) (eta : E → ℝ) (j : ℕ) : ℝ :=
  (Real.log (1 / beta (w (C.start j)) (C.expert j)) +
    ∑ t ∈ C.partition.block j, increment (w t) (z t)) / eta (C.expert j)

def Cover.totalCost {N : ℕ} {active : ℕ → Finset E} {arm : E → A}
    {target : A} {H : Finset ℕ} (C : Cover N active arm target H)
    (w z : ℕ → E → ℝ) (eta : E → ℝ) : ℝ :=
  ∑ j ∈ C.partition.labels, C.localCost w z eta j

theorem block_regret {N : ℕ} {active : ℕ → Finset E} {arm : E → A}
    {target : A} {H : Finset ℕ} (C : Cover N active arm target H)
    (w z x : ℕ → E → ℝ) (eta : E → ℝ) (r : ℕ → ℝ)
    (heta : ∀ e, 0 < eta e) (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < N, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hlinear : ∀ t < N, ∀ e ∈ active t, z t e = eta e * x t e)
    (hgap : ∀ t < N, ∀ e ∈ active t, arm e = target → r t ≤ x t e)
    (j : ℕ) (hj : j ∈ C.partition.labels) :
    (∑ t ∈ C.partition.block j, r t) ≤ C.localCost w z eta j := by
  unfold Cover.localCost
  rw [C.block_eq j hj]
  apply interval_regret N (C.start j) (C.length j) (C.within j hj)
    w z x eta active r (C.expert j) (heta _) hinit hupdate hlinear
  · intro t ht
    exact C.awake j hj t (by rwa [C.block_eq j hj])
  · intro t ht
    exact hgap t (by have ht' := Finset.mem_Ico.mp ht; have hh := C.within j hj; omega)
      (C.expert j) (C.awake j hj t (by rwa [C.block_eq j hj])) (C.same_arm j hj)

/-- Actual E7 costs are summed here; local regret bounds are proved by
`block_regret`, rather than supplied as the target inequality. -/
theorem cover_regret {N : ℕ} {active : ℕ → Finset E} {arm : E → A}
    {target : A} {H : Finset ℕ} (C : Cover N active arm target H)
    (w z x : ℕ → E → ℝ) (eta : E → ℝ) (r : ℕ → ℝ)
    (heta : ∀ e, 0 < eta e) (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < N, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hlinear : ∀ t < N, ∀ e ∈ active t, z t e = eta e * x t e)
    (hgap : ∀ t < N, ∀ e ∈ active t, arm e = target → r t ≤ x t e) :
    (∑ t ∈ H, r t) ≤ C.totalCost w z eta := by
  rw [← C.partition.sum_blocks r]
  exact Finset.sum_le_sum (fun j hj =>
    block_regret C w z x eta r heta hinit hupdate hlinear hgap j hj)

def singlePartition (H : Finset ℕ) : Part2.Intervals.Partition H where
  labels := {0}
  block := fun _ => H
  disjoint := by
    intro i hi j hj hij
    simp only [Finset.mem_coe, Finset.mem_singleton] at hi hj
    exact (hij (hi.trans hj.symm)).elim
  covers := by simp

/-- A full-horizon expert of the desired arm supplies an admissible single
block cover for every subinterval, proving the cover family nonempty. -/
def rootCover (N u n : ℕ) (hn : 0 < n) (hwithin : u + n ≤ N)
    (active : ℕ → Finset E) (arm : E → A) (target : A) (root : E)
    (hroot : ∀ t < N, root ∈ active t) (hlabel : arm root = target) :
    Cover N active arm target (Ico u (u + n)) where
  partition := singlePartition _
  start := fun _ => u
  length := fun _ => n
  expert := fun _ => root
  block_eq := by intro j _; rfl
  length_pos := by intro j _; exact hn
  within := by intro j _; exact hwithin
  awake := by
    intro j _ t ht
    change t ∈ Ico u (u + n) at ht
    exact hroot t (by have hh := Finset.mem_Ico.mp ht; omega)
  same_arm := by intro j _; exact hlabel

/-- E10 with the actual E9 log-beta and exact-increment costs. The full
trajectory and one root expert establish all local inequalities and the
nonempty admissible family. The per-round span/transport inputs remain
explicit deterministic assumptions, independently of any probability claim. -/
theorem interval_envelope (N u n : ℕ) (hn : 0 < n) (hwithin : u + n ≤ N)
    (active : ℕ → Finset E) (arm : E → A) (target : A)
    (w z x : ℕ → E → ℝ) (eta : E → ℝ) (r : ℕ → ℝ) (W : ℝ)
    (heta : ∀ e, 0 < eta e) (hinit : ∀ e, 0 < w 0 e)
    (hupdate : ∀ t < N, ∀ e, w (t + 1) e = step (w t) (z t) e)
    (hlinear : ∀ t < N, ∀ e ∈ active t, z t e = eta e * x t e)
    (hgap : ∀ t < N, ∀ e ∈ active t, arm e = target → r t ≤ x t e)
    (hspan : ∀ t ∈ Ico u (u + n), r t ≤ 2 * W)
    (root : E) (hroot : ∀ t < N, root ∈ active t) (hlabel : arm root = target) :
    (∑ t ∈ Ico u (u + n), r t) ≤
      min (2 * W * ((Ico u (u + n)).card : ℝ))
        (sInf (Set.range (fun C : Cover N active arm target (Ico u (u + n)) =>
          C.totalCost w z eta))) := by
  apply le_min
  · calc
      _ ≤ ∑ _t ∈ Ico u (u + n), 2 * W := Finset.sum_le_sum hspan
      _ = _ := by simp; ring
  · have hn : Nonempty (Cover N active arm target (Ico u (u + n))) :=
      ⟨rootCover N u n hn hwithin active arm target root hroot hlabel⟩
    letI := hn
    apply le_csInf (Set.range_nonempty _)
    rintro y ⟨C, rfl⟩
    exact cover_regret C w z x eta r heta hinit hupdate hlinear hgap

end

end Part2.ExponentialCovers

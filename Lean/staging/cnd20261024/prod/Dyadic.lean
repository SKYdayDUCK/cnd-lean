import Part2.Prod
import Mathlib.Data.Real.Sqrt

namespace Part2.CNDProd
open Finset
noncomputable section

/-- All nodes of the complete binary interval tree, in zero-based time. -/
def blocks : ℕ → ℕ → Finset (ℕ × ℕ)
  | 0, a => {(a, 1)}
  | d + 1, a => insert (a, 2 ^ (d + 1)) (blocks d a ∪ blocks d (a + 2 ^ d))

theorem root_mem (d a : ℕ) : (a, 2 ^ d) ∈ blocks d a := by
  cases d <;> simp [blocks]

theorem block_bounds {d a : ℕ} {J : ℕ × ℕ} (hJ : J ∈ blocks d a) :
    a ≤ J.1 ∧ 0 < J.2 ∧ J.1 + J.2 ≤ a + 2 ^ d := by
  induction d generalizing a with
  | zero =>
    have heq : J = (a, 1) := by simpa [blocks] using hJ
    subst J
    simp
  | succ d ih =>
    simp only [blocks, mem_insert, mem_union] at hJ
    rcases hJ with rfl | hJ | hJ
    · exact ⟨le_rfl, by positivity, le_rfl⟩
    · obtain ⟨h₁, h₂, h₃⟩ := ih hJ
      rw [pow_succ]
      omega
    · obtain ⟨h₁, h₂, h₃⟩ := ih hJ
      rw [pow_succ]
      omega

theorem blocks_card (d a : ℕ) : (blocks d a).card = 2 ^ (d + 1) - 1 := by
  induction d generalizing a with
  | zero => simp [blocks]
  | succ d ih =>
    have hd : Disjoint (blocks d a) (blocks d (a + 2 ^ d)) := by
      apply disjoint_left.mpr
      intro J hl hr
      have hl' := block_bounds hl
      have hr' := block_bounds hr
      omega
    have hn : (a, 2 ^ (d + 1)) ∉ blocks d a ∪ blocks d (a + 2 ^ d) := by
      intro h
      rcases mem_union.mp h with h | h
      · have hb := (block_bounds h).2.2
        have hp : 0 < 2 ^ d := by positivity
        rw [pow_succ] at hb
        omega
      · have hb := (block_bounds h).1
        have hp : 0 < 2 ^ d := by positivity
        omega
    rw [blocks, card_insert_of_notMem hn, card_union_of_disjoint hd, ih, ih]
    have hp : 0 < 2 ^ (d + 1) := by positivity
    rw [pow_succ (2 : ℕ) (d + 1)]
    omega

/-- A numerical boundary-cover estimate; valid also for an empty remainder. -/
theorem sqrt_boundary {m x : ℝ} (hm : 0 ≤ m) (hx : 0 ≤ x) (hxm : x ≤ m) :
    Real.sqrt m + 3 * Real.sqrt x ≤ 3 * Real.sqrt (m + x) := by
  have hs := Real.sqrt_le_sqrt hxm
  have hp := mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg m)
  have hm' := Real.sq_sqrt hm
  have hx' := Real.sq_sqrt hx
  have hmx := Real.sq_sqrt (add_nonneg hm hx)
  have hn := Real.sqrt_nonneg (m + x)
  have hn' := Real.sqrt_nonneg m
  have hn'' := Real.sqrt_nonneg x
  nlinarith [sq_nonneg (3 * Real.sqrt (m + x) - (Real.sqrt m + 3 * Real.sqrt x))]

/-- Recursive maximal dyadic decomposition of a prefix, without a supplied cover. -/
theorem prefix_bound (d a n : ℕ) (hn : n ≤ 2 ^ d) (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hblock : ∀ J ∈ blocks d a, J.1 + J.2 ≤ a + n →
      (∑ t ∈ Ico J.1 (J.1 + J.2), f t) ≤ C * Real.sqrt (J.2 : ℝ)) :
    (∑ t ∈ Ico a (a + n), f t) ≤ 3 * C * Real.sqrt (n : ℝ) := by
  induction d generalizing a n with
  | zero =>
    simp only [pow_zero] at hn
    interval_cases n
    · simp
    · have h := hblock (a, 1) (by simp [blocks]) (by simp)
      simpa using h.trans (by simpa using (show C ≤ 3 * C by linarith))
  | succ d ih =>
    by_cases hhalf : n ≤ 2 ^ d
    · exact ih a n hhalf (by
        intro J hJ hEnd
        exact hblock J (by simp [blocks, hJ]) hEnd)
    · have hrem : n - 2 ^ d ≤ 2 ^ d := by rw [pow_succ] at hn; omega
      have hleft := hblock (a, 2 ^ d) (by simp [blocks, root_mem]) (by omega)
      have hright := ih (a + 2 ^ d) (n - 2 ^ d) hrem (by
        intro J hJ hEnd
        apply hblock J (by simp [blocks, hJ])
        omega)
      have hsplit := sum_Ico_consecutive f (show a ≤ a + 2 ^ d by omega)
        (show a + 2 ^ d ≤ a + n by omega)
      have heq : a + 2 ^ d + (n - 2 ^ d) = a + n := by omega
      rw [heq] at hright
      have hs := sqrt_boundary (Nat.cast_nonneg (2 ^ d)) (Nat.cast_nonneg (n - 2 ^ d))
        (by exact_mod_cast hrem)
      have hcast : ((2 ^ d : ℕ) : ℝ) + ((n - 2 ^ d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast (show 2 ^ d + (n - 2 ^ d) = n by omega)
      rw [hcast] at hs
      have hs' := mul_le_mul_of_nonneg_left hs hC
      nlinarith

/-- The symmetric suffix decomposition. -/
theorem suffix_bound (d a n : ℕ) (hn : n ≤ 2 ^ d) (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hblock : ∀ J ∈ blocks d a, a + 2 ^ d - n ≤ J.1 →
      (∑ t ∈ Ico J.1 (J.1 + J.2), f t) ≤ C * Real.sqrt (J.2 : ℝ)) :
    (∑ t ∈ Ico (a + 2 ^ d - n) (a + 2 ^ d), f t) ≤ 3 * C * Real.sqrt (n : ℝ) := by
  induction d generalizing a n with
  | zero =>
    simp only [pow_zero] at hn
    interval_cases n
    · simp
    · have h := hblock (a, 1) (by simp [blocks]) (by omega)
      simpa using h.trans (by simpa using (show C ≤ 3 * C by linarith))
  | succ d ih =>
    by_cases hhalf : n ≤ 2 ^ d
    · have h := ih (a + 2 ^ d) n hhalf (by
        intro J hJ hStart
        apply hblock J (by simp [blocks, hJ])
        rw [pow_succ]
        omega)
      convert h using 1 <;> congr 2 <;> rw [pow_succ] <;> omega
    · have hrem : n - 2 ^ d ≤ 2 ^ d := by rw [pow_succ] at hn; omega
      have hright := hblock (a + 2 ^ d, 2 ^ d) (by simp [blocks, root_mem]) (by rw [pow_succ]; omega)
      have hleft := ih a (n - 2 ^ d) hrem (by
        intro J hJ hStart
        apply hblock J (by simp [blocks, hJ])
        rw [pow_succ]
        omega)
      have heq : a + 2 ^ d - (n - 2 ^ d) = a + 2 ^ (d + 1) - n := by rw [pow_succ]; omega
      rw [heq] at hleft
      have hsplit := sum_Ico_consecutive f (show a + 2 ^ (d + 1) - n ≤ a + 2 ^ d by rw [pow_succ]; omega)
        (show a + 2 ^ d ≤ a + 2 ^ (d + 1) by rw [pow_succ]; omega)
      have heq' : a + 2 ^ d + 2 ^ d = a + 2 ^ (d + 1) := by rw [pow_succ]; omega
      rw [heq'] at hright
      have hs := sqrt_boundary (Nat.cast_nonneg (2 ^ d)) (Nat.cast_nonneg (n - 2 ^ d))
        (by exact_mod_cast hrem)
      have hcast : ((2 ^ d : ℕ) : ℝ) + ((n - 2 ^ d : ℕ) : ℝ) = (n : ℝ) := by
        exact_mod_cast (show 2 ^ d + (n - 2 ^ d) = n by omega)
      rw [hcast] at hs
      have hs' := mul_le_mul_of_nonneg_left hs hC
      nlinarith

/-- Every actual subinterval is decomposed recursively into genuine tree nodes.
The estimate is deliberately rounded up to the paper's geometric constant 8. -/
theorem dyadic_interval_bound (d a u v : ℕ) (hau : a ≤ u) (huv : u ≤ v)
    (hv : v ≤ a + 2 ^ d) (f : ℕ → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hblock : ∀ J ∈ blocks d a, u ≤ J.1 → J.1 + J.2 ≤ v →
      (∑ t ∈ Ico J.1 (J.1 + J.2), f t) ≤ C * Real.sqrt (J.2 : ℝ)) :
    (∑ t ∈ Ico u v, f t) ≤ 8 * C * Real.sqrt ((v - u : ℕ) : ℝ) := by
  induction d generalizing a u v with
  | zero =>
    simp only [pow_zero] at hv
    by_cases he : u = v
    · simp [he]
    · have hu : u = a := by omega
      have hv' : v = a + 1 := by omega
      subst u; subst v
      have h := hblock (a, 1) (by simp [blocks]) le_rfl le_rfl
      simpa using h.trans (by simpa using (show C ≤ 8 * C by linarith))
  | succ d ih =>
    by_cases hl : v ≤ a + 2 ^ d
    · exact ih a u v hau huv hl (by
        intro J hJ h₁ h₂
        exact hblock J (by simp [blocks, hJ]) h₁ h₂)
    · by_cases hr : a + 2 ^ d ≤ u
      · apply ih (a + 2 ^ d) u v hr huv (by rw [pow_succ] at hv; omega)
        intro J hJ h₁ h₂
        exact hblock J (by simp [blocks, hJ]) h₁ h₂
      · have hleft := suffix_bound d a (a + 2 ^ d - u) (by omega) f C hC (by
          intro J hJ hStart
          apply hblock J (by simp [blocks, hJ]) (by omega)
          have hb := (block_bounds hJ).2.2
          omega)
        have hright := prefix_bound d (a + 2 ^ d) (v - (a + 2 ^ d))
          (by rw [pow_succ] at hv; omega) f C hC (by
            intro J hJ hEnd
            apply hblock J (by simp [blocks, hJ])
            · have hb := (block_bounds hJ).1; omega
            · omega)
        have heq₁ : a + 2 ^ d - (a + 2 ^ d - u) = u := by omega
        have heq₂ : a + 2 ^ d + (v - (a + 2 ^ d)) = v := by omega
        rw [heq₁] at hleft
        rw [heq₂] at hright
        have hsplit := sum_Ico_consecutive f (show u ≤ a + 2 ^ d by omega) (show a + 2 ^ d ≤ v by omega)
        have hs₁ := Real.sqrt_le_sqrt (show ((a + 2 ^ d - u : ℕ) : ℝ) ≤ ((v - u : ℕ) : ℝ) by exact_mod_cast (show a + 2 ^ d - u ≤ v - u by omega))
        have hs₂ := Real.sqrt_le_sqrt (show ((v - (a + 2 ^ d) : ℕ) : ℝ) ≤ ((v - u : ℕ) : ℝ) by exact_mod_cast (show v - (a + 2 ^ d) ≤ v - u by omega))
        have hs₁' := mul_le_mul_of_nonneg_left hs₁ (show 0 ≤ 3 * C by positivity)
        have hs₂' := mul_le_mul_of_nonneg_left hs₂ (show 0 ≤ 3 * C by positivity)
        have hn := mul_nonneg hC (Real.sqrt_nonneg ((v - u : ℕ) : ℝ))
        nlinarith

end
end Part2.CNDProd

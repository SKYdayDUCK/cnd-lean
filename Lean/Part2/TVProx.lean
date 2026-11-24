import Part2.ConvexRemap
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
The finite diagonal-quadratic TV-proximal remapping theorem E2.
Gradient inequalities are derived from actual minimizing inequalities by
two-coordinate perturbations, rather than supplied as remapping hypotheses.
-/

noncomputable section

namespace Part2.TVProx

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def smooth (l d p : ι → ℝ) : ℝ := ∑ i, (l i * p i + d i * (p i) ^ 2 / 2)

def gradient (l d p : ι → ℝ) (i : ι) : ℝ := l i + d i * p i

def l1 (q p : ι → ℝ) : ℝ := ∑ i, |p i - q i|

def objective (l d q : ι → ℝ) (W : ℝ) (p : ι → ℝ) : ℝ :=
  smooth l d p + W / 2 * l1 q p

/-- Move mass from `j` to `k`, with no implicit renormalization. -/
def move (p : ι → ℝ) (j k : ι) (ε : ℝ) (i : ι) : ℝ :=
  p i + (if i = k then ε else 0) - (if i = j then ε else 0)

theorem sum_move (p : ι → ℝ) (j k : ι) (ε : ℝ) :
    (∑ i, move p j k ε i) = ∑ i, p i := by
  simp [move, Finset.sum_add_distrib, Finset.sum_sub_distrib]

theorem move_mem_simplex (p : ι → ℝ) (hp : p ∈ stdSimplex ℝ ι)
    (j k : ι) (ε : ℝ) (hε : 0 ≤ ε) (hle : ε ≤ p j) :
    move p j k ε ∈ stdSimplex ℝ ι := by
  constructor
  · intro i
    by_cases hij : i = j
    · subst i
      by_cases hjk : j = k
      · simp [move, hjk, hp.1 k]
      · simp only [move, if_neg hjk, if_true, add_zero]
        linarith
    · by_cases hik : i = k
      · simp only [move, if_pos hik, if_neg hij, sub_zero]
        exact add_nonneg (hp.1 i) hε
      · simpa [move, hij, hik] using hp.1 i
  · rw [sum_move]
    exact hp.2

/-- Any separable finite sum changes in exactly its two moved coordinates. -/
theorem separable_move (f : ι → ℝ → ℝ) (p : ι → ℝ) (j k : ι)
    (hjk : j ≠ k) (ε : ℝ) :
    (∑ i, f i (move p j k ε i)) = (∑ i, f i (p i)) +
      (f k (p k + ε) - f k (p k)) + (f j (p j - ε) - f j (p j)) := by
  have hterm (i : ι) : f i (move p j k ε i) = f i (p i) +
      (if i = k then f k (p k + ε) - f k (p k) else 0) +
      (if i = j then f j (p j - ε) - f j (p j) else 0) := by
    by_cases hik : i = k
    · subst i
      simp [move, Ne.symm hjk]
    · by_cases hij : i = j
      · subst i
        simp [move, hjk]
      · simp [move, hik, hij]
  simp_rw [hterm, Finset.sum_add_distrib]
  simp

theorem smooth_move (l d p : ι → ℝ) (j k : ι) (hjk : j ≠ k) (ε : ℝ) :
    smooth l d (move p j k ε) = smooth l d p +
      ε * (gradient l d p k - gradient l d p j) +
      ε ^ 2 * ((d k + d j) / 2) := by
  unfold smooth
  rw [separable_move (fun i z => l i * z + d i * z ^ 2 / 2) p j k hjk ε]
  unfold gradient
  ring

theorem l1_move_le (q p : ι → ℝ) (j k : ι) (hjk : j ≠ k)
    (ε : ℝ) (hε : 0 ≤ ε) : l1 q (move p j k ε) ≤ l1 q p + 2 * ε := by
  have hk : |p k + ε - q k| ≤ |p k - q k| + ε := by
    calc
      _ = |(p k - q k) + ε| := by congr 1 <;> ring
      _ ≤ |p k - q k| + |ε| := abs_add_le _ _
      _ = _ := by rw [abs_of_nonneg hε]
  have hj : |p j - ε - q j| ≤ |p j - q j| + ε := by
    calc
      _ = |(p j - q j) - ε| := by congr 1 <;> ring
      _ ≤ |p j - q j| + |ε| := abs_sub _ _
      _ = _ := by rw [abs_of_nonneg hε]
  unfold l1
  rw [separable_move (fun i z => |z - q i|) p j k hjk ε]
  linarith

theorem l1_move_donor_receiver (q p : ι → ℝ) (j k : ι) (hjk : j ≠ k)
    (ε : ℝ) (hε : 0 ≤ ε) (hk : ε ≤ q k - p k) (hj : ε ≤ p j - q j) :
    l1 q (move p j k ε) = l1 q p - 2 * ε := by
  unfold l1
  rw [separable_move (fun i z => |z - q i|) p j k hjk ε]
  rw [abs_of_nonpos (show p k + ε - q k ≤ 0 by linarith),
    abs_of_nonpos (show p k - q k ≤ 0 by linarith),
    abs_of_nonneg (show 0 ≤ p j - ε - q j by linarith),
    abs_of_nonneg (show 0 ≤ p j - q j by linarith)]
  ring

/-- An explicit small step rules out a negative one-sided linear coefficient. -/
theorem slope_nonneg (A B r : ℝ) (hr : 0 < r)
    (h : ∀ ε : ℝ, 0 < ε → ε ≤ r → 0 ≤ ε * A + ε ^ 2 * B) : 0 ≤ A := by
  by_contra hA
  have hA' : A < 0 := lt_of_not_ge hA
  have hden : 0 < 2 * (|B| + 1) := by nlinarith [abs_nonneg B]
  let ε := min r (-A / (2 * (|B| + 1)))
  have hε : 0 < ε := lt_min hr (div_pos (neg_pos.mpr hA') hden)
  have hεr : ε ≤ r := min_le_left _ _
  have hεfrac : ε ≤ -A / (2 * (|B| + 1)) := min_le_right _ _
  have hsmall : ε * (2 * (|B| + 1)) ≤ -A := (le_div_iff₀ hden).mp hεfrac
  have hB : ε * B ≤ ε * |B| := mul_le_mul_of_nonneg_left (le_abs_self B) hε.le
  have hinside : A + ε * B < 0 := by nlinarith
  have hneg : ε * A + ε ^ 2 * B < 0 := by
    calc
      _ = ε * (A + ε * B) := by ring
      _ < 0 := mul_neg_of_pos_of_neg hε hinside
  have hpos := h ε hε hεr
  linarith

theorem continuous_smooth (l d : ι → ℝ) : Continuous (smooth l d) := by
  unfold smooth
  exact continuous_finset_sum _ (fun i _ =>
    (continuous_const.mul (continuous_apply i)).add
      ((continuous_const.mul ((continuous_apply i).pow 2)).div_const 2))

theorem continuous_l1 (q : ι → ℝ) : Continuous (l1 q) := by
  unfold l1
  exact continuous_finset_sum _ (fun i _ => ((continuous_apply i).sub continuous_const).abs)

theorem continuous_objective (l d q : ι → ℝ) (W : ℝ) : Continuous (objective l d q W) :=
  (continuous_smooth l d).add (continuous_const.mul (continuous_l1 q))

/-- The compact simplex supplies an actual minimizer, including W=0 and d_i=0. -/
theorem exists_minimizer (l d q : ι → ℝ) (W : ℝ) (hq : q ∈ stdSimplex ℝ ι) :
    ∃ p ∈ stdSimplex ℝ ι, IsMinOn (objective l d q W) (stdSimplex ℝ ι) p := by
  exact (isCompact_stdSimplex ι).exists_isMinOn ⟨q, hq⟩
    (continuous_objective l d q W).continuousOn

/-- E14 is derived from minimizing the objective along a mass-transfer direction. -/
theorem minimizer_donor_receiver (l d q p : ι → ℝ) (W : ℝ)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p)
    (j k : ι) (hj : q j < p j) (hk : p k < q k) :
    W ≤ gradient l d p k - gradient l d p j := by
  have hjk : j ≠ k := by intro h; subst k; linarith
  let r := min (q k - p k) (p j - q j)
  have hr : 0 < r := lt_min (sub_pos.mpr hk) (sub_pos.mpr hj)
  have hslope : 0 ≤ gradient l d p k - gradient l d p j - W := by
    apply slope_nonneg _ ((d k + d j) / 2) r hr
    intro ε hε hεr
    have hεk : ε ≤ q k - p k := hεr.trans (min_le_left _ _)
    have hεj : ε ≤ p j - q j := hεr.trans (min_le_right _ _)
    have hεp : ε ≤ p j := by linarith [hq.1 j]
    have hm := move_mem_simplex p hp j k ε hε.le hεp
    have ho := hmin hm
    change smooth l d p + W / 2 * l1 q p ≤
      smooth l d (move p j k ε) + W / 2 * l1 q (move p j k ε) at ho
    rw [smooth_move l d p j k hjk ε,
      l1_move_donor_receiver q p j k hjk ε hε.le hεk hεj] at ho
    nlinarith [ho]
  linarith

/-- Every positive-mass coordinate is within W of every coordinate's gradient. -/
theorem minimizer_support_bound (l d q p : ι → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p)
    (j k : ι) (hj : 0 < p j) :
    gradient l d p j - gradient l d p k ≤ W := by
  by_cases hjk : j = k
  · subst k
    simpa using hW
  have hslope : 0 ≤ gradient l d p k - gradient l d p j + W := by
    apply slope_nonneg _ ((d k + d j) / 2) (p j) hj
    intro ε hε hεj
    have hm := move_mem_simplex p hp j k ε hε.le hεj
    have ho := hmin hm
    have hl := mul_le_mul_of_nonneg_left (l1_move_le q p j k hjk ε hε.le)
      (show 0 ≤ W / 2 by positivity)
    change smooth l d p + W / 2 * l1 q p ≤
      smooth l d (move p j k ε) + W / 2 * l1 q (move p j k ε) at ho
    rw [smooth_move l d p j k hjk ε] at ho
    nlinarith [ho, hl]
  linarith

/-- Box prediction E11: lower endpoint plus diagonal gradient, up to a common shift. -/
def prediction (l d p : ι → ℝ) (i : ι) : ℝ :=
  gradient l d p i - ∑ k, p k * (l k + d k)

theorem prediction_difference (l d p : ι → ℝ) (i j : ι) :
    prediction l d p i - prediction l d p j = gradient l d p i - gradient l d p j := by
  unfold prediction
  ring

theorem minimizer_prediction_gap (l d q p : ι → ℝ) (W : ℝ)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p) :
    ∀ k j, p k < q k → q j < p j →
      W ≤ prediction l d p k - prediction l d p j := by
  intro k j hk hj
  rw [prediction_difference]
  exact minimizer_donor_receiver l d q p W hq hp hmin j k hj hk

theorem minimizer_public_support_span (l d q p b : ι → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p)
    (hb : ∀ i j, b j - b i ≤ W) :
    ∀ i j, 0 < p i → 0 < p j →
      |(prediction l d p i + b i) - (prediction l d p j + b j)| ≤ 2 * W := by
  intro i j hi hj
  have hij := minimizer_support_bound l d q p W hW hp hmin i j hi
  have hji := minimizer_support_bound l d q p W hW hp hmin j i hj
  have hbij := hb j i
  have hbji := hb i j
  rw [abs_le]
  dsimp [prediction]
  constructor <;> linarith

/-- Full E2 minimizer conclusion: construct one transport before the public vector.
This includes every source row, q_i=0, d_i=0 and W=0. -/
theorem minimizer_has_robust_remap (l d q p : ι → ℝ) (W : ℝ) (hW : 0 ≤ W)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p) :
    ∃ M : ι → ι → ℝ,
      (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
      (∀ j, ∑ k, q k * M k j = p j) ∧
      (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
        (∀ k, (∑ j, M k j * (prediction l d p j + b j)) ≤ prediction l d p k + b k) ∧
        (∀ i j, 0 < p i → 0 < p j →
          |(prediction l d p i + b i) - (prediction l d p j + b j)| ≤ 2 * W)) := by
  have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
  obtain ⟨M, hMn, hMs, hMc, hMd⟩ :=
    Part2.ConvexRemap.exists_robust_remap q p (prediction l d p) W hq.1 hp.1 hs
      (minimizer_prediction_gap l d q p W hq hp hmin)
  refine ⟨M, hMn, hMs, hMc, ?_⟩
  intro b hb
  exact ⟨hMd b hb, minimizer_public_support_span l d q p b W hW hp hmin hb⟩

/-- E2 with its existence obligation discharged, rather than assumed. -/
theorem exists_proximal_robust_remap (l d q : ι → ℝ) (W : ℝ)
    (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) :
    ∃ p ∈ stdSimplex ℝ ι,
      IsMinOn (objective l d q W) (stdSimplex ℝ ι) p ∧
      ∃ M : ι → ι → ℝ,
        (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
        (∀ j, ∑ k, q k * M k j = p j) ∧
        (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
          (∀ k, (∑ j, M k j * (prediction l d p j + b j)) ≤ prediction l d p k + b k) ∧
          (∀ i j, 0 < p i → 0 < p j →
            |(prediction l d p i + b i) - (prediction l d p j + b j)| ≤ 2 * W)) := by
  obtain ⟨p, hp, hmin⟩ := exists_minimizer l d q W hq
  exact ⟨p, hp, hmin, minimizer_has_robust_remap l d q p W hW hq hp hmin⟩

/-- With genuine nonnegative box widths, E12 is a convex objective. -/
theorem convex_objective (l d q : ι → ℝ) (W : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hW : 0 ≤ W) :
    ConvexOn ℝ Set.univ (objective l d q W) := by
  refine ⟨convex_univ, ?_⟩
  intro x _hx y _hy a b ha hb hab
  have hbeq : b = 1 - a := by linarith
  have hsm : smooth l d (a • x + b • y) ≤ a * smooth l d x + b * smooth l d y := by
    have hpoint (i : ι) : l i * (a * x i + b * y i) +
        d i * (a * x i + b * y i) ^ 2 / 2 ≤
        a * (l i * x i + d i * (x i) ^ 2 / 2) +
        b * (l i * y i + d i * (y i) ^ 2 / 2) := by
      have hn : 0 ≤ d i * (a * b) * (x i - y i) ^ 2 :=
        mul_nonneg (mul_nonneg (hd i) (mul_nonneg ha hb)) (sq_nonneg _)
      have hid : a * (l i * x i + d i * (x i) ^ 2 / 2) +
          b * (l i * y i + d i * (y i) ^ 2 / 2) -
          (l i * (a * x i + b * y i) + d i * (a * x i + b * y i) ^ 2 / 2) =
          d i * (a * b) * (x i - y i) ^ 2 / 2 := by
        rw [hbeq]
        ring
      linarith
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    simpa only [smooth, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  have hl : l1 q (a • x + b • y) ≤ a * l1 q x + b * l1 q y := by
    have hpoint (i : ι) : |a * x i + b * y i - q i| ≤
        a * |x i - q i| + b * |y i - q i| := by
      calc
        _ = |a * (x i - q i) + b * (y i - q i)| := by
          congr 1
          rw [hbeq]
          ring
        _ ≤ |a * (x i - q i)| + |b * (y i - q i)| := abs_add_le _ _
        _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg ha, abs_of_nonneg hb]
    have hsum := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
    simpa only [l1, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum] using hsum
  have hw := mul_le_mul_of_nonneg_left hl (show 0 ≤ W / 2 by positivity)
  change smooth l d (a • x + b • y) + W / 2 * l1 q (a • x + b • y) ≤
    a * (smooth l d x + W / 2 * l1 q x) + b * (smooth l d y + W / 2 * l1 q y)
  nlinarith [hsm, hw]

/-- Source-zero rows are redirected if necessary, so every row obeys E1's J_k.
All positive source rows use the previously verified explicit transport. -/
def safeRemap (q p G : ι → ℝ) (m : ι) (W : ℝ) (k j : ι) : ℝ :=
  if q k = 0 then
    if G k ≤ G m + W then (if k = j then 1 else 0)
    else (if m = j then 1 else 0)
  else Part2.ConvexRemap.remap q p k j

theorem safeRemap_nonneg (q p G : ι → ℝ) (m : ι) (W : ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) (k j : ι) :
    0 ≤ safeRemap q p G m W k j := by
  by_cases hz : q k = 0
  · unfold safeRemap
    simp only [hz, if_true]
    split_ifs <;> norm_num
  · simpa [safeRemap, hz] using Part2.ConvexRemap.remap_nonneg q p hq hp k j

theorem safeRemap_row_sum (q p G : ι → ℝ) (m : ι) (W : ℝ)
    (hs : (∑ i, q i) = ∑ i, p i) (k : ι) :
    (∑ j, safeRemap q p G m W k j) = 1 := by
  by_cases hz : q k = 0
  · by_cases hsafe : G k ≤ G m + W <;> simp [safeRemap, hz, hsafe]
  · simpa [safeRemap, hz] using Part2.ConvexRemap.remap_row_stochastic q p hs k

theorem safeRemap_consistent (q p G : ι → ℝ) (m : ι) (W : ℝ)
    (hp : ∀ i, 0 ≤ p i) (hs : (∑ i, q i) = ∑ i, p i) (j : ι) :
    (∑ k, q k * safeRemap q p G m W k j) = p j := by
  have hterm (k : ι) : q k * safeRemap q p G m W k j =
      q k * Part2.ConvexRemap.remap q p k j := by
    by_cases hz : q k = 0
    · simp [hz]
    · simp [safeRemap, hz]
  simp_rw [hterm]
  exact Part2.ConvexRemap.remap_consistent q p hp hs j

theorem remap_positive_destination (q p : ι → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hs : (∑ i, q i) = ∑ i, p i) (k j : ι) (hk : q k ≠ 0)
    (hM : Part2.ConvexRemap.remap q p k j ≠ 0) : 0 < p j := by
  have hqpos : 0 < q k := lt_of_le_of_ne (hq k) (Ne.symm hk)
  have hMpos : 0 < Part2.ConvexRemap.remap q p k j :=
    lt_of_le_of_ne (Part2.ConvexRemap.remap_nonneg q p hq hp k j) (Ne.symm hM)
  have hle : q k * Part2.ConvexRemap.remap q p k j ≤ p j := by
    rw [← Part2.ConvexRemap.remap_consistent q p hp hs j]
    exact Finset.single_le_sum
      (fun i _ => mul_nonneg (hq i) (Part2.ConvexRemap.remap_nonneg q p hq hp i j))
      (Finset.mem_univ k)
  exact (mul_pos hqpos hMpos).trans_le hle

/-- The repaired map satisfies every allowed-destination condition, including q_k=0. -/
theorem safeRemap_allowed (l d q p : ι → ℝ) (W : ℝ) (m : ι) (hW : 0 ≤ W)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p)
    (k j : ι) (hM : safeRemap q p (gradient l d p) m W k j ≠ 0) :
    gradient l d p j ≤ gradient l d p m + W ∧
      (j = k ∨ W ≤ gradient l d p k - gradient l d p j) := by
  by_cases hz : q k = 0
  · by_cases hsafe : gradient l d p k ≤ gradient l d p m + W
    · have hkj : k = j := by
        by_contra h
        exact hM (by simp [safeRemap, hz, hsafe, h])
      subst j
      exact ⟨hsafe, Or.inl rfl⟩
    · have hmj : m = j := by
        by_contra h
        exact hM (by simp [safeRemap, hz, hsafe, h])
      subst j
      refine ⟨by linarith, Or.inr ?_⟩
      have hdrop := lt_of_not_ge hsafe
      linarith
  · have hR : Part2.ConvexRemap.remap q p k j ≠ 0 := by
      simpa [safeRemap, hz] using hM
    have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
    have hpj := remap_positive_destination q p hq.1 hp.1 hs k j hz hR
    have hsupport := minimizer_support_bound l d q p W hW hp hmin j m hpj
    refine ⟨by linarith, ?_⟩
    by_cases hjk : j = k
    · exact Or.inl hjk
    · right
      have hplan : Part2.ConvexRemap.plan q p k j ≠ 0 := by
        intro hplan
        exact hR (by simp [Part2.ConvexRemap.remap, hz, hplan])
      have hflow : Part2.ConvexRemap.flow q p k j ≠ 0 := by
        simpa [Part2.ConvexRemap.plan, Ne.symm hjk] using hplan
      obtain ⟨hk, hj⟩ := Part2.ConvexRemap.flow_edge q p k j hflow
      exact minimizer_donor_receiver l d q p W hq hp hmin j k hj hk

/-- E2 for every given proximal minimizer, as quantified in the original theorem.
The constructed matrix precedes the universally quantified public vector b. -/
theorem box_proximal_remapping_E2_for_minimizer (l d q p : ι → ℝ) (W : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι)
    (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective l d q W) (stdSimplex ℝ ι) p) :
    ConvexOn ℝ (stdSimplex ℝ ι) (objective l d q W) ∧
    p ∈ stdSimplex ℝ ι ∧ IsMinOn (objective l d q W) (stdSimplex ℝ ι) p ∧
      ∃ m : ι, (∀ i, prediction l d p m ≤ prediction l d p i) ∧
      ∃ M : ι → ι → ℝ,
        (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
        (∀ j, ∑ k, q k * M k j = p j) ∧
        (∀ k j, M k j ≠ 0 →
          prediction l d p j ≤ prediction l d p m + W ∧
          (j = k ∨ W ≤ prediction l d p k - prediction l d p j)) ∧
        (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
          (∀ k, (∑ j, M k j * (prediction l d p j + b j)) ≤ prediction l d p k + b k) ∧
          (∀ i j, 0 < p i → 0 < p j →
            |(prediction l d p i + b i) - (prediction l d p j + b j)| ≤ 2 * W)) := by
  have hconv := (convex_objective l d q W hd hW).subset
    (Set.subset_univ (stdSimplex ℝ ι)) (convex_stdSimplex ℝ ι)
  have hu : (Finset.univ : Finset ι).Nonempty := by
    by_contra hempty
    have hmass := hq.2
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hmass
    norm_num at hmass
  obtain ⟨m, _hm, hmmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) (gradient l d p) hu
  have hminpred : ∀ i, prediction l d p m ≤ prediction l d p i := by
    intro i
    have hmi := hmmin i (Finset.mem_univ i)
    dsimp [prediction]
    linarith
  let M := safeRemap q p (gradient l d p) m W
  have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
  have hMn : ∀ k j, 0 ≤ M k j := safeRemap_nonneg q p (gradient l d p) m W hq.1 hp.1
  have hMs : ∀ k, ∑ j, M k j = 1 := safeRemap_row_sum q p (gradient l d p) m W hs
  have hMc : ∀ j, ∑ k, q k * M k j = p j :=
    safeRemap_consistent q p (gradient l d p) m W hp.1 hs
  have hallowed : ∀ k j, M k j ≠ 0 →
      prediction l d p j ≤ prediction l d p m + W ∧
      (j = k ∨ W ≤ prediction l d p k - prediction l d p j) := by
    intro k j hM
    obtain ⟨hsmall, hgap⟩ := safeRemap_allowed l d q p W m hW hq hp hmin k j hM
    constructor
    · dsimp [prediction]
      linarith
    · rcases hgap with hsame | hdrop
      · exact Or.inl hsame
      · right
        rw [prediction_difference]
        exact hdrop
  refine ⟨hconv, hp, hmin, m, hminpred, M, hMn, hMs, hMc, hallowed, ?_⟩
  intro b hb
  constructor
  · intro k
    calc
      _ ≤ ∑ j, M k j * (prediction l d p k + b k) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hz : M k j = 0
        · simp [hz]
        · have horder : prediction l d p j + b j ≤ prediction l d p k + b k := by
            rcases (hallowed k j hz).2 with hsame | hdrop
            · subst j
              exact le_refl _
            · have hpub := hb k j
              linarith
          exact mul_le_mul_of_nonneg_left horder (hMn k j)
      _ = prediction l d p k + b k := by rw [← Finset.sum_mul, hMs k, one_mul]
  · exact minimizer_public_support_span l d q p b W hW hp hmin hb

/-- Existence corollary of the arbitrary-minimizer E2 theorem and compactness. -/
theorem box_proximal_remapping_E2 (l d q : ι → ℝ) (W : ℝ)
    (hd : ∀ i, 0 ≤ d i) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) :
    ConvexOn ℝ (stdSimplex ℝ ι) (objective l d q W) ∧
    ∃ p ∈ stdSimplex ℝ ι,
      IsMinOn (objective l d q W) (stdSimplex ℝ ι) p ∧
      ∃ m : ι, (∀ i, prediction l d p m ≤ prediction l d p i) ∧
      ∃ M : ι → ι → ℝ,
        (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
        (∀ j, ∑ k, q k * M k j = p j) ∧
        (∀ k j, M k j ≠ 0 →
          prediction l d p j ≤ prediction l d p m + W ∧
          (j = k ∨ W ≤ prediction l d p k - prediction l d p j)) ∧
        (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
          (∀ k, (∑ j, M k j * (prediction l d p j + b j)) ≤ prediction l d p k + b k) ∧
          (∀ i j, 0 < p i → 0 < p j →
            |(prediction l d p i + b i) - (prediction l d p j + b j)| ≤ 2 * W)) := by
  obtain ⟨p, hp, hmin⟩ := exists_minimizer l d q W hq
  obtain ⟨hconv, hp', hmin', hremap⟩ :=
    box_proximal_remapping_E2_for_minimizer l d q p W hd hW hq hp hmin
  exact ⟨hconv, p, hp', hmin', hremap⟩

end Part2.TVProx

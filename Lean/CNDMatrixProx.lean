import Part2.CND
import Part2.TVProx

/-!
General finite symmetric zero-diagonal CND matrix proximal remapping.
The variational conclusions are derived from actual minimizing inequalities.
-/

noncomputable section

namespace Part2.CNDMatrixProx

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def action (r : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ := ∑ j, r i j * p j

def gradient (θ : ι → ℝ) (r : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  θ i - action r p i

def objective (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (p : ι → ℝ) : ℝ := CND.potential θ r p + W / 2 * TVProx.l1 q p

theorem action_move (r : ι → ι → ℝ) (p : ι → ℝ)
    (j k i : ι) (hjk : j ≠ k) (ε : ℝ) :
    action r (TVProx.move p j k ε) i = action r p i + ε * (r i k - r i j) := by
  unfold action
  rw [TVProx.separable_move (fun l z => r i l * z) p j k hjk ε]
  ring

omit [DecidableEq ι] in
theorem quadratic_eq_action (r : ι → ι → ℝ) (p : ι → ℝ) :
    CND.quadratic r p = ∑ i, p i * action r p i := by
  unfold CND.quadratic action
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [DecidableEq ι] in
theorem cross_eq_action (r : ι → ι → ℝ) (p : ι → ℝ)
    (hsym : ∀ i j, r i j = r j i) (j k : ι) :
    (∑ i, p i * (r i k - r i j)) = action r p k - action r p j := by
  unfold action
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hsym i k, hsym i j]
  ring

/-- The exact two-coordinate quadratic expansion, with general matrix cross terms. -/
theorem quadratic_move (r : ι → ι → ℝ) (p : ι → ℝ)
    (hsym : ∀ i j, r i j = r j i) (hdiag : ∀ i, r i i = 0)
    (j k : ι) (hjk : j ≠ k) (ε : ℝ) :
    CND.quadratic r (TVProx.move p j k ε) = CND.quadratic r p +
      2 * ε * (action r p k - action r p j) - 2 * ε ^ 2 * r j k := by
  rw [quadratic_eq_action]
  simp_rw [action_move r p j k _ hjk ε, mul_add]
  rw [Finset.sum_add_distrib]
  have hsecond : (∑ i, TVProx.move p j k ε i * (ε * (r i k - r i j))) =
      ε * ∑ i, TVProx.move p j k ε i * (r i k - r i j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hsecond]
  rw [TVProx.separable_move (fun i z => z * action r p i) p j k hjk ε,
    TVProx.separable_move (fun i z => z * (r i k - r i j)) p j k hjk ε]
  rw [cross_eq_action r p hsym j k, ← quadratic_eq_action, hdiag k, hdiag j, hsym k j]
  ring

/-- Actual smooth objective expansion; no diagonal/separability restriction on r. -/
theorem potential_move (θ : ι → ℝ) (r : ι → ι → ℝ) (p : ι → ℝ)
    (hsym : ∀ i j, r i j = r j i) (hdiag : ∀ i, r i i = 0)
    (j k : ι) (hjk : j ≠ k) (ε : ℝ) :
    CND.potential θ r (TVProx.move p j k ε) = CND.potential θ r p +
      ε * (gradient θ r p k - gradient θ r p j) + ε ^ 2 * r j k := by
  unfold CND.potential
  rw [TVProx.separable_move (fun i z => θ i * z) p j k hjk ε,
    quadratic_move r p hsym hdiag j k hjk ε]
  unfold gradient
  ring

omit [DecidableEq ι] in
theorem continuous_potential (θ : ι → ℝ) (r : ι → ι → ℝ) :
    Continuous (CND.potential θ r) := by
  unfold CND.potential CND.quadratic
  fun_prop

theorem continuous_objective (θ : ι → ℝ) (r : ι → ι → ℝ)
    (q : ι → ℝ) (W : ℝ) : Continuous (objective θ r q W) :=
  (continuous_potential θ r).add (continuous_const.mul (TVProx.continuous_l1 q))

/-- Compactness supplies a real minimizer without strict CND or positive W. -/
theorem exists_minimizer (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hq : q ∈ stdSimplex ℝ ι) :
    ∃ p ∈ stdSimplex ℝ ι, IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p := by
  exact (isCompact_stdSimplex ι).exists_isMinOn ⟨q, hq⟩
    (continuous_objective θ r q W).continuousOn

theorem minimizer_donor_receiver (θ : ι → ℝ) (r : ι → ι → ℝ) (q p : ι → ℝ)
    (W : ℝ) (hsym : ∀ i j, r i j = r j i) (hdiag : ∀ i, r i i = 0)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p)
    (j k : ι) (hj : q j < p j) (hk : p k < q k) :
    W ≤ gradient θ r p k - gradient θ r p j := by
  have hjk : j ≠ k := by intro h; subst k; linarith
  let a := min (q k - p k) (p j - q j)
  have ha : 0 < a := lt_min (sub_pos.mpr hk) (sub_pos.mpr hj)
  have hslope : 0 ≤ gradient θ r p k - gradient θ r p j - W := by
    apply TVProx.slope_nonneg _ (r j k) a ha
    intro ε hε hεa
    have hεk : ε ≤ q k - p k := hεa.trans (min_le_left _ _)
    have hεj : ε ≤ p j - q j := hεa.trans (min_le_right _ _)
    have hεp : ε ≤ p j := by linarith [hq.1 j]
    have hm := TVProx.move_mem_simplex p hp j k ε hε.le hεp
    have ho := hmin hm
    change CND.potential θ r p + W / 2 * TVProx.l1 q p ≤
      CND.potential θ r (TVProx.move p j k ε) +
        W / 2 * TVProx.l1 q (TVProx.move p j k ε) at ho
    rw [potential_move θ r p hsym hdiag j k hjk ε,
      TVProx.l1_move_donor_receiver q p j k hjk ε hε.le hεk hεj] at ho
    nlinarith [ho]
  linarith

/-- Every positive-mass coordinate is within W above every gradient coordinate. -/
theorem minimizer_support_bound (θ : ι → ℝ) (r : ι → ι → ℝ) (q p : ι → ℝ)
    (W : ℝ) (hsym : ∀ i j, r i j = r j i) (hdiag : ∀ i, r i i = 0)
    (hW : 0 ≤ W) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p)
    (j k : ι) (hj : 0 < p j) :
    gradient θ r p j - gradient θ r p k ≤ W := by
  by_cases hjk : j = k
  · subst k
    simpa using hW
  have hslope : 0 ≤ gradient θ r p k - gradient θ r p j + W := by
    apply TVProx.slope_nonneg _ (r j k) (p j) hj
    intro ε hε hεj
    have hm := TVProx.move_mem_simplex p hp j k ε hε.le hεj
    have ho := hmin hm
    have hl := mul_le_mul_of_nonneg_left (TVProx.l1_move_le q p j k hjk ε hε.le)
      (show 0 ≤ W / 2 by positivity)
    change CND.potential θ r p + W / 2 * TVProx.l1 q p ≤
      CND.potential θ r (TVProx.move p j k ε) +
        W / 2 * TVProx.l1 q (TVProx.move p j k ε) at ho
    rw [potential_move θ r p hsym hdiag j k hjk ε] at ho
    nlinarith [ho, hl]
  linarith

theorem convex_objective (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ)
    (W : ℝ) (hr : CND.IsCND r) (hW : 0 ≤ W) :
    ConvexOn ℝ (stdSimplex ℝ ι) (objective θ r q W) := by
  have hpot : ConvexOn ℝ (stdSimplex ℝ ι) (CND.potential θ r) :=
    CND.potential_convexOn_simplex θ r hr
  have hpen := (TVProx.convex_objective (fun _ : ι => 0) (fun _ : ι => 0) q W
    (fun _ => le_refl 0) hW).subset (Set.subset_univ (stdSimplex ℝ ι))
      (convex_stdSimplex ℝ ι)
  convert hpot.add hpen using 1
  ext p
  simp [objective, TVProx.objective, TVProx.smooth, Pi.add_apply]

/-- The paper's gauge is a common shift of the genuine matrix gradient. -/
def prediction (θ : ι → ℝ) (r : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  gradient θ r p i - ∑ k, p k * θ k

omit [DecidableEq ι] in
theorem prediction_difference (θ : ι → ℝ) (r : ι → ι → ℝ) (p : ι → ℝ) (i j : ι) :
    prediction θ r p i - prediction θ r p j = gradient θ r p i - gradient θ r p j := by
  unfold prediction
  ring

theorem minimizer_public_support_span (θ : ι → ℝ) (r : ι → ι → ℝ) (q p b : ι → ℝ)
    (W : ℝ) (hr : CND.IsCND r) (hW : 0 ≤ W) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p)
    (hb : ∀ i j, b j - b i ≤ W) :
    ∀ i j, 0 < p i → 0 < p j →
      |(prediction θ r p i + b i) - (prediction θ r p j + b j)| ≤ 2 * W := by
  intro i j hi hj
  have hij := minimizer_support_bound θ r q p W hr.1 hr.2.1 hW hp hmin i j hi
  have hji := minimizer_support_bound θ r q p W hr.1 hr.2.1 hW hp hmin j i hj
  have hbij := hb j i
  have hbji := hb i j
  rw [abs_le]
  dsimp [prediction]
  constructor <;> linarith

/-- Every nonzero entry of the explicit repaired transport is safe, including zero source rows. -/
theorem safeRemap_allowed (θ : ι → ℝ) (r : ι → ι → ℝ) (q p : ι → ℝ)
    (W : ℝ) (m : ι) (hr : CND.IsCND r) (hW : 0 ≤ W)
    (hq : q ∈ stdSimplex ℝ ι) (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p)
    (k j : ι) (hM : TVProx.safeRemap q p (gradient θ r p) m W k j ≠ 0) :
    gradient θ r p j ≤ gradient θ r p m + W ∧
      (j = k ∨ W ≤ gradient θ r p k - gradient θ r p j) := by
  by_cases hz : q k = 0
  · by_cases hsafe : gradient θ r p k ≤ gradient θ r p m + W
    · have hkj : k = j := by
        by_contra h
        exact hM (by simp [TVProx.safeRemap, hz, hsafe, h])
      subst j
      exact ⟨hsafe, Or.inl rfl⟩
    · have hmj : m = j := by
        by_contra h
        exact hM (by simp [TVProx.safeRemap, hz, hsafe, h])
      subst j
      refine ⟨by linarith, Or.inr ?_⟩
      have hdrop := lt_of_not_ge hsafe
      linarith
  · have hR : Part2.ConvexRemap.remap q p k j ≠ 0 := by
      simpa [TVProx.safeRemap, hz] using hM
    have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
    have hpj := TVProx.remap_positive_destination q p hq.1 hp.1 hs k j hz hR
    have hsupport := minimizer_support_bound θ r q p W hr.1 hr.2.1 hW hp hmin j m hpj
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
      exact minimizer_donor_receiver θ r q p W hr.1 hr.2.1 hq hp hmin j k hj hk

/-- Complete deterministic matrix-proximal theorem for every actual minimizer.
The single transport is selected before every possible public vector b. -/
theorem matrix_proximal_remapping_for_minimizer
    (θ : ι → ℝ) (r : ι → ι → ℝ) (q p : ι → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι)
    (hp : p ∈ stdSimplex ℝ ι)
    (hmin : IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p) :
    ConvexOn ℝ (stdSimplex ℝ ι) (objective θ r q W) ∧
    ∃ m : ι, (∀ i, prediction θ r p m ≤ prediction θ r p i) ∧
      ∃ M : ι → ι → ℝ,
        (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
        (∀ j, ∑ k, q k * M k j = p j) ∧
        (∀ k j, M k j ≠ 0 →
          prediction θ r p j ≤ prediction θ r p m + W ∧
          (j = k ∨ W ≤ prediction θ r p k - prediction θ r p j)) ∧
        (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
          (∀ k, (∑ j, M k j * (prediction θ r p j + b j)) ≤ prediction θ r p k + b k) ∧
          (∀ i j, 0 < p i → 0 < p j →
            |(prediction θ r p i + b i) - (prediction θ r p j + b j)| ≤ 2 * W)) := by
  have hu : (Finset.univ : Finset ι).Nonempty := by
    by_contra hempty
    have hmass := hq.2
    rw [Finset.not_nonempty_iff_eq_empty.mp hempty, Finset.sum_empty] at hmass
    norm_num at hmass
  obtain ⟨m, _hm, hmmin⟩ :=
    Finset.exists_min_image (Finset.univ : Finset ι) (gradient θ r p) hu
  have hminpred : ∀ i, prediction θ r p m ≤ prediction θ r p i := by
    intro i
    have hmi := hmmin i (Finset.mem_univ i)
    dsimp [prediction]
    linarith
  let M := TVProx.safeRemap q p (gradient θ r p) m W
  have hs : (∑ i, q i) = ∑ i, p i := hq.2.trans hp.2.symm
  have hMn : ∀ k j, 0 ≤ M k j := TVProx.safeRemap_nonneg q p (gradient θ r p) m W hq.1 hp.1
  have hMs : ∀ k, ∑ j, M k j = 1 := TVProx.safeRemap_row_sum q p (gradient θ r p) m W hs
  have hMc : ∀ j, ∑ k, q k * M k j = p j :=
    TVProx.safeRemap_consistent q p (gradient θ r p) m W hp.1 hs
  have hallowed : ∀ k j, M k j ≠ 0 →
      prediction θ r p j ≤ prediction θ r p m + W ∧
      (j = k ∨ W ≤ prediction θ r p k - prediction θ r p j) := by
    intro k j hM
    obtain ⟨hsmall, hgap⟩ := safeRemap_allowed θ r q p W m hr hW hq hp hmin k j hM
    constructor
    · dsimp [prediction]
      linarith
    · rcases hgap with hsame | hdrop
      · exact Or.inl hsame
      · right
        rw [prediction_difference]
        exact hdrop
  refine ⟨convex_objective θ r q W hr hW, m, hminpred, M, hMn, hMs, hMc, hallowed, ?_⟩
  intro b hb
  constructor
  · intro k
    calc
      _ ≤ ∑ j, M k j * (prediction θ r p k + b k) := by
        apply Finset.sum_le_sum
        intro j _
        by_cases hz : M k j = 0
        · simp [hz]
        · have horder : prediction θ r p j + b j ≤ prediction θ r p k + b k := by
            rcases (hallowed k j hz).2 with hsame | hdrop
            · subst j
              exact le_refl _
            · have hpub := hb k j
              linarith
          exact mul_le_mul_of_nonneg_left horder (hMn k j)
      _ = prediction θ r p k + b k := by rw [← Finset.sum_mul, hMs k, one_mul]
  · exact minimizer_public_support_span θ r q p b W hr hW hp hmin hb

/-- Complete finite CND matrix proximal existence and safe remapping, with no KKT premises. -/
theorem exists_matrix_proximal_safe_remap
    (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) :
    ∃ p ∈ stdSimplex ℝ ι,
      IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p ∧
      ∃ m : ι, (∀ i, prediction θ r p m ≤ prediction θ r p i) ∧
        ∃ M : ι → ι → ℝ,
          (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
          (∀ j, ∑ k, q k * M k j = p j) ∧
          (∀ k j, M k j ≠ 0 →
            prediction θ r p j ≤ prediction θ r p m + W ∧
            (j = k ∨ W ≤ prediction θ r p k - prediction θ r p j)) ∧
          (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
            (∀ k, (∑ j, M k j * (prediction θ r p j + b j)) ≤ prediction θ r p k + b k) ∧
            (∀ i j, 0 < p i → 0 < p j →
              |(prediction θ r p i + b i) - (prediction θ r p j + b j)| ≤ 2 * W)) := by
  obtain ⟨p, hp, hmin⟩ := exists_minimizer θ r q W hq
  exact ⟨p, hp, hmin, (matrix_proximal_remapping_for_minimizer θ r q p W hr hW hq hp hmin).2⟩

/-- Symmetric zero-diagonal CND itself forces every radius to be nonnegative. -/
theorem radius_nonneg (r : ι → ι → ℝ) (hr : CND.IsCND r) (j k : ι) : 0 ≤ r j k := by
  by_cases hjk : j = k
  · subst k
    rw [hr.2.1 j]
  · have hmass : (∑ i, TVProx.move (fun _ : ι => 0) j k 1 i) = 0 := by
      rw [TVProx.sum_move]
      simp
    have hquad := hr.2.2 (TVProx.move (fun _ : ι => 0) j k 1) hmass
    rw [quadratic_move r (fun _ : ι => 0) hr.1 hr.2.1 j k hjk 1] at hquad
    simp [CND.quadratic, action] at hquad
    linarith

def minimizerSet (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ) :
    Set (ι → ℝ) := {p | p ∈ stdSimplex ℝ ι ∧
      IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p}

def squaredNorm (p : ι → ℝ) : ℝ := ∑ i, (p i) ^ 2

omit [DecidableEq ι] in
theorem continuous_squaredNorm : Continuous (squaredNorm : (ι → ℝ) → ℝ) := by
  unfold squaredNorm
  fun_prop

omit [DecidableEq ι] in
theorem minimizerSet_eq_level (θ : ι → ℝ) (r : ι → ι → ℝ) (q p : ι → ℝ) (W : ℝ)
    (hp : p ∈ minimizerSet θ r q W) :
    minimizerSet θ r q W = (stdSimplex ℝ ι) ∩
      {x | objective θ r q W x = objective θ r q W p} := by
  ext x
  constructor
  · intro hx
    exact ⟨hx.1, le_antisymm (hx.2 hp.1) (hp.2 hx.1)⟩
  · intro hx
    refine ⟨hx.1, ?_⟩
    intro y hy
    rw [hx.2]
    exact hp.2 hy

theorem compact_minimizerSet (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hq : q ∈ stdSimplex ℝ ι) : IsCompact (minimizerSet θ r q W) := by
  obtain ⟨p, hp, hmin⟩ := exists_minimizer θ r q W hq
  rw [minimizerSet_eq_level θ r q p W ⟨hp, hmin⟩]
  exact (isCompact_stdSimplex ι).inter_right
    (isClosed_eq (continuous_objective θ r q W) continuous_const)

theorem convex_minimizerSet (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ)
    (W : ℝ) (hr : CND.IsCND r) (hW : 0 ≤ W) :
    Convex ℝ (minimizerSet θ r q W) := by
  intro x hx y hy a b ha hb hab
  have hxy : objective θ r q W y = objective θ r q W x :=
    le_antisymm (hy.2 hx.1) (hx.2 hy.1)
  have hconv := convex_objective θ r q W hr hW
  refine ⟨hconv.1 hx.1 hy.1 ha hb hab, ?_⟩
  intro z hz
  have hmix := hconv.2 hx.1 hy.1 ha hb hab
  simp only [smul_eq_mul] at hmix
  rw [hxy] at hmix
  have heq : a * objective θ r q W x + b * objective θ r q W x =
      objective θ r q W x := by rw [← add_mul, hab, one_mul]
  rw [heq] at hmix
  exact hmix.trans (hx.2 hz)

omit [DecidableEq ι] in
theorem squaredNorm_midpoint (x y : ι → ℝ) :
    squaredNorm ((1 / 2 : ℝ) • x + (1 / 2 : ℝ) • y) =
      (squaredNorm x + squaredNorm y) / 2 - squaredNorm (x - y) / 4 := by
  have hid (i : ι) : ((1 / 2 : ℝ) * x i + (1 / 2 : ℝ) * y i) ^ 2 =
      (x i ^ 2 + y i ^ 2) / 2 - (x i - y i) ^ 2 / 4 := by ring
  simp only [squaredNorm, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.sub_apply, hid,
    Finset.sum_sub_distrib]
  simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, Finset.sum_mul]

omit [DecidableEq ι] in
theorem squaredNorm_sub_pos {x y : ι → ℝ} (hxy : x ≠ y) : 0 < squaredNorm (x - y) := by
  have hex : ∃ i, x i ≠ y i := by
    by_contra h
    push_neg at h
    exact hxy (funext h)
  obtain ⟨i, hi⟩ := hex
  have hpos : 0 < (x i - y i) ^ 2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hi)
  have hle : (x i - y i) ^ 2 ≤ squaredNorm (x - y) :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((x - y) j)) (Finset.mem_univ i)
  exact hpos.trans_le hle

/-- The canonical minimum-Euclidean-norm proximal minimizer exists uniquely,
even when the CND quadratic and the primary minimizer are degenerate. -/
theorem exists_unique_minimumNorm_minimizer
    (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) :
    ∃! p : ι → ℝ, p ∈ minimizerSet θ r q W ∧
      IsMinOn squaredNorm (minimizerSet θ r q W) p := by
  obtain ⟨x, hx, hxmin⟩ := exists_minimizer θ r q W hq
  have hne : (minimizerSet θ r q W).Nonempty := ⟨x, hx, hxmin⟩
  obtain ⟨p, hp, hn⟩ := (compact_minimizerSet θ r q W hq).exists_isMinOn hne
    continuous_squaredNorm.continuousOn
  refine ⟨p, ⟨hp, hn⟩, ?_⟩
  intro y hy
  by_contra hyp
  have hmid := (convex_minimizerSet θ r q W hr hW) hy.1 hp
    (show (0 : ℝ) ≤ 1 / 2 by norm_num) (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by norm_num)
  have hn1 := hn hmid
  have hn2 := hy.2 hmid
  change squaredNorm p ≤ squaredNorm ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • p) at hn1
  change squaredNorm y ≤ squaredNorm ((1 / 2 : ℝ) • y + (1 / 2 : ℝ) • p) at hn2
  rw [squaredNorm_midpoint] at hn1 hn2
  have hpositive := squaredNorm_sub_pos hyp
  nlinarith

/-- Unique secondary minimization fixes a deterministic pointwise choice. -/
def minimumNormProx (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) : ι → ℝ :=
  Classical.choose (exists_unique_minimumNorm_minimizer θ r q W hr hW hq)

theorem minimumNormProx_spec (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) :
    minimumNormProx θ r q W hr hW hq ∈ minimizerSet θ r q W ∧
      IsMinOn squaredNorm (minimizerSet θ r q W) (minimumNormProx θ r q W hr hW hq) :=
  (Classical.choose_spec (exists_unique_minimumNorm_minimizer θ r q W hr hW hq)).1

/-- All deterministic guarantees also hold for the unique minimum-norm choice. -/
theorem canonical_matrix_proximal_safe_remap
    (θ : ι → ℝ) (r : ι → ι → ℝ) (q : ι → ℝ) (W : ℝ)
    (hr : CND.IsCND r) (hW : 0 ≤ W) (hq : q ∈ stdSimplex ℝ ι) :
    let p := minimumNormProx θ r q W hr hW hq
    p ∈ stdSimplex ℝ ι ∧ IsMinOn (objective θ r q W) (stdSimplex ℝ ι) p ∧
      IsMinOn squaredNorm (minimizerSet θ r q W) p ∧
      ∃ m : ι, (∀ i, prediction θ r p m ≤ prediction θ r p i) ∧
        ∃ M : ι → ι → ℝ,
          (∀ k j, 0 ≤ M k j) ∧ (∀ k, ∑ j, M k j = 1) ∧
          (∀ j, ∑ k, q k * M k j = p j) ∧
          (∀ k j, M k j ≠ 0 →
            prediction θ r p j ≤ prediction θ r p m + W ∧
            (j = k ∨ W ≤ prediction θ r p k - prediction θ r p j)) ∧
          (∀ b : ι → ℝ, (∀ i j, b j - b i ≤ W) →
            (∀ k, (∑ j, M k j * (prediction θ r p j + b j)) ≤ prediction θ r p k + b k) ∧
            (∀ i j, 0 < p i → 0 < p j →
              |(prediction θ r p i + b i) - (prediction θ r p j + b j)| ≤ 2 * W)) := by
  dsimp only
  have hs := minimumNormProx_spec θ r q W hr hW hq
  exact ⟨hs.1.1, hs.1.2, hs.2,
    (matrix_proximal_remapping_for_minimizer θ r q _ W hr hW hq hs.1.1 hs.1.2).2⟩

end Part2.CNDMatrixProx

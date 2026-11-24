import Part2.Pairwise

/-!
Actual finite CND proxy, observable payment, and physical-regret conversion.
This module is deterministic. Confidence and safe-transport hypotheses are
explicit eventwise inputs, not an end-to-end probability certification.
-/

noncomputable section

namespace Part2.CNDPhysicalRegret

open Finset
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def avg (p f : ι → ℝ) : ℝ := ∑ i, p i * f i

def rowRadius (r : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, p j * r i j

def proxy (a p : ι → ℝ) (r : ι → ι → ℝ) (i : ι) : ℝ :=
  a i - avg p a - rowRadius r p i

def privateDeficit (θ a p : ι → ℝ) (r : ι → ι → ℝ) (i : ι) : ℝ :=
  θ i - avg p θ - proxy a p r i

def payment (r : ι → ι → ℝ) (p : ι → ℝ) (i : ι) : ℝ :=
  2 * rowRadius r p i

def gamma (r : ι → ι → ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * p j * r i j

def physical (c θ ξ : ι → ℝ) (z : ℝ) (i : ι) : ℝ :=
  c i + θ i + z + ξ i

def broadcast (c e : ι → ℝ) (i : ι) : ℝ := c i + e i

def surrogate (a p c e : ι → ℝ) (r : ι → ι → ℝ) (i : ι) : ℝ :=
  proxy a p r i + broadcast c e i

def transported (M : ι → ι → ℝ) (loss : ι → ℝ) (k : ι) : ℝ :=
  ∑ j, M k j * loss j

theorem privateDeficit_expansion (θ a p : ι → ℝ) (r : ι → ι → ℝ)
    (hp : ∑ j, p j = 1) (i : ι) :
    privateDeficit θ a p r i =
      ∑ j, p j * ((θ i - θ j) - (a i - a j) + r i j) := by
  exact Part2.Pairwise.moving_gauge_identity p θ a r hp i

theorem confidence_controls_actual_deficit (θ a p : ι → ℝ) (r : ι → ι → ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hcover : ∀ i j, |(θ i - θ j) - (a i - a j)| ≤ r i j) (i : ι) :
    0 ≤ privateDeficit θ a p r i ∧ privateDeficit θ a p r i ≤ payment r p i := by
  rw [privateDeficit_expansion θ a p r hp1 i]
  constructor
  · apply sum_nonneg
    intro j _
    have hj := (abs_le.mp (hcover i j)).1
    exact mul_nonneg (hp0 j) (by linarith)
  · calc
      _ ≤ ∑ j, p j * (2 * r i j) := by
        apply sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.mp (hcover i j)).2]) (hp0 j)
      _ = payment r p i := by
        unfold payment rowRadius
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j _
        ring

theorem payment_range (r : ι → ι → ℝ) (p : ι → ℝ) (rmax : ℝ)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hr : ∀ i j, 0 ≤ r i j ∧ r i j ≤ rmax) (i : ι) :
    0 ≤ payment r p i ∧ payment r p i ≤ 2 * rmax := by
  unfold payment rowRadius
  constructor
  · exact mul_nonneg (by norm_num) (sum_nonneg fun j _ => mul_nonneg (hp0 j) (hr i j).1)
  · have hs : (∑ j, p j * r i j) ≤ rmax := by
      calc
        _ ≤ ∑ j, p j * rmax :=
          sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hr i j).2 (hp0 j)
        _ = rmax := by rw [← sum_mul, hp1, one_mul]
    linarith

theorem average_actual_deficit (θ a p : ι → ℝ) (r : ι → ι → ℝ)
    (hp1 : ∑ j, p j = 1) :
    avg p (privateDeficit θ a p r) = gamma r p := by
  unfold avg
  simp_rw [privateDeficit_expansion θ a p r hp1]
  simpa only [gamma] using
    (Part2.Pairwise.gamma_full_sum p (fun i j => θ i - θ j)
      (fun i j => a i - a j) r (by intro i j; ring) (by intro i j; ring))

theorem average_payment (r : ι → ι → ℝ) (p : ι → ℝ) :
    avg p (payment r p) = 2 * gamma r p := by
  unfold avg payment rowRadius gamma
  simp_rw [Finset.mul_sum]
  apply sum_congr rfl
  intro i _
  apply sum_congr rfl
  intro j _
  ring

theorem physical_identity (θ a p c e ξ : ι → ℝ) (r : ι → ι → ℝ)
    (z : ℝ) (I k : ι) :
    physical c θ ξ z I - physical c θ ξ z k =
      (avg p (surrogate a p c e r) - surrogate a p c e r k) +
      (surrogate a p c e r I - avg p (surrogate a p c e r)) +
      (privateDeficit θ a p r I - privateDeficit θ a p r k) +
      ((ξ I - e I) - (ξ k - e k)) := by
  unfold physical surrogate broadcast privateDeficit proxy
  ring

theorem transported_mixture (p q loss : ι → ℝ) (M : ι → ι → ℝ)
    (hcons : ∀ j, (∑ k, q k * M k j) = p j) :
    avg q (transported M loss) = avg p loss := by
  unfold avg transported
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro j _
  calc
    (∑ k, q k * (M k j * loss j)) = (∑ k, q k * M k j) * loss j := by
      rw [Finset.sum_mul]
      apply sum_congr rfl
      intro k _
      ring
    _ = p j * loss j := by rw [hcons j]

theorem physical_regret_le_transported (θ a p q c e ξ : ι → ℝ)
    (r M : ι → ι → ℝ) (z : ℝ) (I k : ι)
    (hp0 : ∀ j, 0 ≤ p j) (hp1 : ∑ j, p j = 1)
    (hcover : ∀ i j, |(θ i - θ j) - (a i - a j)| ≤ r i j)
    (hcons : ∀ j, (∑ l, q l * M l j) = p j)
    (hdom : transported M (surrogate a p c e r) k ≤ surrogate a p c e r k) :
    physical c θ ξ z I - physical c θ ξ z k ≤
      (avg q (transported M (surrogate a p c e r)) -
        transported M (surrogate a p c e r) k) +
      (surrogate a p c e r I - avg p (surrogate a p c e r)) +
      payment r p I + ((ξ I - e I) - (ξ k - e k)) := by
  have hid := physical_identity θ a p c e ξ r z I k
  have hI := (confidence_controls_actual_deficit θ a p r hp0 hp1 hcover I).2
  have hk := (confidence_controls_actual_deficit θ a p r hp0 hp1 hcover k).1
  have hm := transported_mixture p q (surrogate a p c e r) M hcons
  linarith

variable {τ : Type*} [DecidableEq τ]

def ledger (s : Finset τ) (r : τ → ι → ι → ℝ) (p : τ → ι → ℝ)
    (I : τ → ι) : ℝ := ∑ t ∈ s, payment (r t) (p t) (I t)

theorem ledger_nonnegative (s : Finset τ) (r : τ → ι → ι → ℝ)
    (p : τ → ι → ℝ) (I : τ → ι)
    (hp : ∀ t ∈ s, ∀ i, 0 ≤ p t i)
    (hr : ∀ t ∈ s, ∀ i j, 0 ≤ r t i j) :
    0 ≤ ledger s r p I := by
  unfold ledger payment rowRadius
  apply sum_nonneg
  intro t ht
  exact mul_nonneg (by norm_num)
    (sum_nonneg fun j _ => mul_nonneg (hp t ht j) (hr t ht (I t) j))

theorem ledger_disjoint_union (s u : Finset τ) (r : τ → ι → ι → ℝ)
    (p : τ → ι → ℝ) (I : τ → ι) (hdisj : Disjoint s u) :
    ledger (s ∪ u) r p I = ledger s r p I + ledger u r p I := by
  exact sum_union hdisj

theorem ledger_mono (s u : Finset τ) (r : τ → ι → ι → ℝ)
    (p : τ → ι → ℝ) (I : τ → ι) (hsub : s ⊆ u)
    (hp : ∀ t ∈ u, ∀ i, 0 ≤ p t i)
    (hr : ∀ t ∈ u, ∀ i j, 0 ≤ r t i j) :
    ledger s r p I ≤ ledger u r p I := by
  apply sum_le_sum_of_subset_of_nonneg hsub
  intro t ht _
  unfold payment rowRadius
  exact mul_nonneg (by norm_num)
    (sum_nonneg fun j _ => mul_nonneg (hp t ht j) (hr t ht (I t) j))

theorem all_paths_physical_conversion (s : Finset τ) (θ : ι → ℝ)
    (a p q c e ξ : τ → ι → ℝ) (r M : τ → ι → ι → ℝ)
    (z : τ → ℝ) (I : τ → ι)
    (hp0 : ∀ t ∈ s, ∀ j, 0 ≤ p t j)
    (hp1 : ∀ t ∈ s, (∑ j, p t j) = 1)
    (hcover : ∀ t ∈ s, ∀ i j, |(θ i - θ j) - (a t i - a t j)| ≤ r t i j)
    (hcons : ∀ t ∈ s, ∀ j, (∑ l, q t l * M t l j) = p t j)
    (hdom : ∀ t ∈ s, ∀ k,
      transported (M t) (surrogate (a t) (p t) (c t) (e t) (r t)) k ≤
        surrogate (a t) (p t) (c t) (e t) (r t) k) :
    ∀ k : τ → ι,
      (∑ t ∈ s, (physical (c t) θ (ξ t) (z t) (I t) -
        physical (c t) θ (ξ t) (z t) (k t))) ≤
      (∑ t ∈ s, (avg (q t) (transported (M t)
        (surrogate (a t) (p t) (c t) (e t) (r t))) -
        transported (M t) (surrogate (a t) (p t) (c t) (e t) (r t)) (k t))) +
      (∑ t ∈ s, (surrogate (a t) (p t) (c t) (e t) (r t) (I t) -
        avg (p t) (surrogate (a t) (p t) (c t) (e t) (r t)))) +
      (∑ t ∈ s, ((ξ t (I t) - e t (I t)) - (ξ t (k t) - e t (k t)))) +
      ledger s r p I := by
  intro k
  have hsum := sum_le_sum (s := s) fun t ht =>
    physical_regret_le_transported θ (a t) (p t) (q t) (c t) (e t) (ξ t)
      (r t) (M t) (z t) (I t) (k t) (hp0 t ht) (hp1 t ht) (hcover t ht)
      (hcons t ht) (hdom t ht (k t))
  simpa only [Finset.sum_add_distrib, ledger, add_assoc, add_left_comm, add_comm] using hsum

end Part2.CNDPhysicalRegret

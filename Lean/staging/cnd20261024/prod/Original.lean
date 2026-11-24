import staging.cnd20261024.prod.TreeProd
import ExactGreedyTransport

namespace Part2.CNDProd
open Finset
noncomputable section

def pureAdvice {E K : Type*} [DecidableEq K] (arm : E → K) (e : E) (k : K) : ℝ :=
  if arm e = k then 1 else 0

theorem mixture_remap {E K : Type*} [Fintype E] [DecidableEq E] [Fintype K] [DecidableEq K]
    (active : Finset E) (eta w : E → ℝ) (arm : E → K) (M : K → K → ℝ) (j : K) :
    Part2.Prod.mixture active eta w (fun e k => M (arm e) k) j =
      ∑ k, Part2.Prod.mixture active eta w (pureAdvice arm) k * M k j := by
  have hnum : (∑ k, (∑ e ∈ active, Part2.Prod.coefficient eta w e * pureAdvice arm e k) * M k j) =
      ∑ e ∈ active, Part2.Prod.coefficient eta w e * M (arm e) j := by
    simp_rw [sum_mul]
    rw [sum_comm]
    apply sum_congr rfl
    intro e he
    simp [pureAdvice, mul_ite, ite_mul]
  simp only [Part2.Prod.mixture, div_mul_eq_mul_div, ← sum_div]
  rw [hnum]

def armNonempty {K : ℕ} (hK : 2 ≤ K) : (univ : Finset (Fin K)).Nonempty :=
  ⟨⟨0, by omega⟩, mem_univ _⟩

def numberedMatrix {K : ℕ} (hK : 2 ≤ K) (W : ℝ)
    (θ : Fin K → ℝ) (r : Fin K → Fin K → ℝ) (q p : Fin K → ℝ) : Fin K → Fin K → ℝ :=
  ExactGreedyTransport.exactRemap q p (CNDMatrixProx.gradient θ r p) W (armNonempty hK)

def numberedAdvice {d K : ℕ} (hK : 2 ≤ K) (W : ℝ)
    (θ : ℕ → Fin K → ℝ) (r : ℕ → Fin K → Fin K → ℝ) (q p : ℕ → Fin K → ℝ)
    (t : ℕ) (e : TreeExpert d K) (j : Fin K) : ℝ :=
  numberedMatrix hK W (θ t) (r t) (q t) (p t) e.2 j

def proxyLoss {K : ℕ} (θ : ℕ → Fin K → ℝ) (r : ℕ → Fin K → Fin K → ℝ)
    (p b : ℕ → Fin K → ℝ) (t : ℕ) (j : Fin K) : ℝ :=
  CNDMatrixProx.prediction (θ t) (r t) (p t) j + b t j

/-- Exact ordered greedy transport, not an existential replacement, supplies
the primitive row ranges and comparator domination required by Prod. -/
theorem numbered_rows_geometry {d K : ℕ} (hK : 2 ≤ K) {W : ℝ} (hW : 0 ≤ W)
    (θ : Fin K → ℝ) (r : Fin K → Fin K → ℝ) (q p b : Fin K → ℝ)
    (hr : Part2.CND.IsCND r) (hq : q ∈ stdSimplex ℝ (Fin K)) (hp : p ∈ stdSimplex ℝ (Fin K))
    (hmin : IsMinOn (CNDMatrixProx.objective θ r q W) (stdSimplex ℝ (Fin K)) p)
    (hb : ∀ i j, b j - b i ≤ W) :
    (∀ e f : TreeExpert d K,
      |Part2.Prod.adviceLoss (fun e j => numberedMatrix hK W θ r q p e.2 j)
          (fun j => CNDMatrixProx.prediction θ r p j + b j) e -
        Part2.Prod.adviceLoss (fun e j => numberedMatrix hK W θ r q p e.2 j)
          (fun j => CNDMatrixProx.prediction θ r p j + b j) f| ≤ 2 * W) ∧
    (∀ e : TreeExpert d K,
      Part2.Prod.adviceLoss (fun e j => numberedMatrix hK W θ r q p e.2 j)
        (fun j => CNDMatrixProx.prediction θ r p j + b j) e ≤
        CNDMatrixProx.prediction θ r p e.2 + b e.2) := by
  have hM := ExactGreedyTransport.exactRemap_nonneg q p (CNDMatrixProx.gradient θ r p)
    W (armNonempty hK) hq.1 hp.1
  have hrow := ExactGreedyTransport.exactRemap_row_sum q p (CNDMatrixProx.gradient θ r p)
    W (armNonempty hK) (hq.2.trans hp.2.symm)
  constructor
  · intro e f
    apply averages_abs_sub_le _ _ _ _ (hM e.2) (hM f.2) (hrow e.2) (hrow f.2)
    intro i j hi hj
    exact ExactGreedyTransport.exactRemap_all_destinations_public_span θ r q p b W hr hW hq hp hmin
      (armNonempty hK) hb e.2 f.2 i j hi hj
  · intro e
    apply allowed_row_dominates _ _ _ W hM hrow _ hb e.2
    intro k j hkj
    have h := (ExactGreedyTransport.exactRemap_allowed θ r q p W hr hW hq hp hmin
      (armNonempty hK) k j hkj).2
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [CNDMatrixProx.prediction_difference]
      exact h

/-- Original proximal points and original ordered transport, coupled to the
actual recursively updated expert mixture, give paper (19) on every interval.
The q equality is the algorithm's pre-action mixture identity, not a regret premise. -/
theorem original_proxy_interval {d K T : ℕ} (hK : 2 ≤ K) {W : ℝ} (hW : 0 < W)
    (hT : T ≤ 2 ^ d) (θ : ℕ → Fin K → ℝ) (r : ℕ → Fin K → Fin K → ℝ)
    (q p b : ℕ → Fin K → ℝ)
    (hr : ∀ t < T, Part2.CND.IsCND (r t))
    (hq : ∀ t < T, q t ∈ stdSimplex ℝ (Fin K)) (hp : ∀ t < T, p t ∈ stdSimplex ℝ (Fin K))
    (hmin : ∀ t < T, IsMinOn (CNDMatrixProx.objective (θ t) (r t) (q t) W)
      (stdSimplex ℝ (Fin K)) (p t))
    (hb : ∀ t < T, ∀ i j, b t j - b t i ≤ W)
    (hqrun : ∀ t < T, q t = Part2.Prod.mixture (treeActive d K t) (treeRate d K W)
      (treeWeights d K W (numberedAdvice hK W θ r q p) (proxyLoss θ r p b) t)
      (pureAdvice (fun e : TreeExpert d K => e.2)))
    (u v : ℕ) (huv : u ≤ v) (hv : v ≤ T) (k : Fin K) :
    (∑ t ∈ Ico u v, ((∑ j, p t j * proxyLoss θ r p b t j) - proxyLoss θ r p b t k)) ≤
      32 * W * Real.sqrt (((v - u : ℕ) : ℝ) * logExperts d K) := by
  have hgeom (t : ℕ) (ht : t < T) := numbered_rows_geometry (d := d) hK hW.le
    (θ t) (r t) (q t) (p t) (b t) (hr t ht) (hq t ht) (hp t ht) (hmin t ht) (hb t ht)
  have hpair : ∀ t < T, ∀ i ∈ treeActive d K t, ∀ j ∈ treeActive d K t,
      |Part2.Prod.adviceLoss (numberedAdvice hK W θ r q p t) (proxyLoss θ r p b t) i -
        Part2.Prod.adviceLoss (numberedAdvice hK W θ r q p t) (proxyLoss θ r p b t) j| ≤ 2 * W := by
    intro t ht i _ j _
    exact (hgeom t ht).1 i j
  have hdom : ∀ t < T, ∀ e ∈ treeActive d K t,
      Part2.Prod.adviceLoss (numberedAdvice hK W θ r q p t) (proxyLoss θ r p b t) e ≤ proxyLoss θ r p b t e.2 := by
    intro t ht e _
    exact (hgeom t ht).2 e
  have hplayed (t : ℕ) (ht : t < T) :
      treePlayed d K W (numberedAdvice hK W θ r q p) (proxyLoss θ r p b) t =
      ∑ j, p t j * proxyLoss θ r p b t j := by
    unfold treePlayed Part2.Prod.mixtureLoss
    apply sum_congr rfl
    intro j _
    congr 1
    change Part2.Prod.mixture (treeActive d K t) (treeRate d K W)
      (treeWeights d K W (numberedAdvice hK W θ r q p) (proxyLoss θ r p b) t)
      (fun e j => numberedMatrix hK W (θ t) (r t) (q t) (p t) e.2 j) j = p t j
    rw [mixture_remap]
    rw [← hqrun t ht]
    exact ExactGreedyTransport.exactRemap_consistent (q t) (p t) _ W (armNonempty hK)
      (hq t ht).1 (hp t ht).1 ((hq t ht).2.trans (hp t ht).2.symm) j
  have h := tree_interval_regret hK hW hT (numberedAdvice hK W θ r q p) (proxyLoss θ r p b)
    hpair hdom u v huv hv k
  convert h using 1
  apply sum_congr rfl
  intro t ht
  rw [hplayed t (by have := (mem_Ico.mp ht).2; omega)]

/-- The W=0 branch skips Prod. Actual optimality forces the played support
onto minimum proxy coordinates, so the public comparator loss is nonpositive. -/
theorem zero_width_proxy_interval {K T : ℕ}
    (θ : ℕ → Fin K → ℝ) (r : ℕ → Fin K → Fin K → ℝ) (q p b : ℕ → Fin K → ℝ)
    (hr : ∀ t < T, Part2.CND.IsCND (r t))
    (hp : ∀ t < T, p t ∈ stdSimplex ℝ (Fin K))
    (hmin : ∀ t < T, IsMinOn (CNDMatrixProx.objective (θ t) (r t) (q t) 0)
      (stdSimplex ℝ (Fin K)) (p t))
    (hb : ∀ t < T, ∀ i j, b t j - b t i ≤ 0)
    (u v : ℕ) (hv : v ≤ T) (k : Fin K) :
    (∑ t ∈ Ico u v, ((∑ j, p t j * proxyLoss θ r p b t j) - proxyLoss θ r p b t k)) ≤ 0 := by
  apply sum_nonpos
  intro t ht
  have htT : t < T := lt_of_lt_of_le (mem_Ico.mp ht).2 hv
  have hle : (∑ j, p t j * proxyLoss θ r p b t j) ≤ proxyLoss θ r p b t k := by
    calc
      _ ≤ ∑ j, p t j * proxyLoss θ r p b t k := by
        apply sum_le_sum
        intro j _
        by_cases hz : p t j = 0
        · simp [hz]
        · have hj : 0 < p t j := lt_of_le_of_ne ((hp t htT).1 j) (Ne.symm hz)
          have hg := CNDMatrixProx.minimizer_support_bound (θ t) (r t) (q t) (p t) 0
            (hr t htT).1 (hr t htT).2.1 le_rfl (hp t htT) (hmin t htT) j k hj
          have hd : proxyLoss θ r p b t j ≤ proxyLoss θ r p b t k := by
            have hpred : CNDMatrixProx.prediction (θ t) (r t) (p t) j -
                CNDMatrixProx.prediction (θ t) (r t) (p t) k ≤ 0 := by
              rw [CNDMatrixProx.prediction_difference]
              exact hg
            dsimp [proxyLoss]
            linarith [hb t htT k j]
          exact mul_le_mul_of_nonneg_left hd ((hp t htT).1 j)
      _ = _ := by rw [← sum_mul, (hp t htT).2, one_mul]
  linarith

end
end Part2.CNDProd

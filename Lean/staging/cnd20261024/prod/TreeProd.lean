import staging.cnd20261024.prod.Evolution
import Mathlib.Data.Nat.Log

namespace Part2.CNDProd
open Finset
noncomputable section

abbrev TreeExpert (d K : ℕ) := {J // J ∈ blocks d 0} × Fin K

def expertCount (d K : ℕ) : ℕ := K * (2 ^ (d + 1) - 1)

theorem padded_horizon (T : ℕ) : T ≤ 2 ^ Nat.clog 2 T := Nat.le_pow_clog (by omega) T

theorem padded_expert_count_lt {K T : ℕ} (hK : 0 < K) (hT : 0 < T) :
    expertCount (Nat.clog 2 T) K < 4 * K * T := by
  have hp : 2 ^ Nat.clog 2 T < 2 * T := by
    by_cases hT₁ : T = 1
    · simp [hT₁]
    · have hT' : 1 < T := by omega
      have hc := Nat.clog_pos (by omega : 1 < 2) hT'
      have hp := Nat.pow_pred_clog_lt_self (by omega : 1 < 2) hT'
      have he : 2 ^ Nat.clog 2 T = 2 * 2 ^ (Nat.clog 2 T).pred := by
        conv_lhs => rw [← Nat.succ_pred_eq_of_pos hc]
        rw [pow_succ]
        omega
      rw [he]
      omega
  unfold expertCount
  rw [pow_succ]
  have hpow : 0 < 2 ^ Nat.clog 2 T := by positivity
  have hpred : 2 ^ Nat.clog 2 T * 2 - 1 < 4 * T := by omega
  nlinarith

theorem card_tree_expert (d K : ℕ) : Fintype.card (TreeExpert d K) = expertCount d K := by
  simp [TreeExpert, Fintype.card_prod, blocks_card, expertCount, mul_comm]

def logExperts (d K : ℕ) : ℝ := Real.log (expertCount d K : ℝ)

theorem logExperts_pos {d K : ℕ} (hK : 2 ≤ K) : 0 < logExperts d K := by
  have hp : 2 ≤ 2 ^ (d + 1) := by
    rw [pow_succ]
    have h : 0 < 2 ^ d := by positivity
    omega
  have hN : 2 ≤ expertCount d K := by
    unfold expertCount
    simpa using (Nat.mul_le_mul hK (show 1 ≤ 2 ^ (d + 1) - 1 by omega))
  exact Real.log_pos (by exact_mod_cast (show 1 < expertCount d K by omega))

def treeActive (d K t : ℕ) : Finset (TreeExpert d K) :=
  univ.filter (fun e => e.1.1.1 ≤ t ∧ t < e.1.1.1 + e.1.1.2)

def treeRate (d K : ℕ) (W : ℝ) (e : TreeExpert d K) : ℝ :=
  rate W (logExperts d K) (e.1.1.2 : ℝ)

def treeInit (d K : ℕ) (_ : TreeExpert d K) : ℝ := 1 / (expertCount d K : ℝ)

def treeWeights (d K : ℕ) (W : ℝ) (advice : ℕ → TreeExpert d K → Fin K → ℝ)
    (loss : ℕ → Fin K → ℝ) : ℕ → TreeExpert d K → ℝ :=
  evolution (treeActive d K) (treeRate d K W) (treeInit d K) advice loss

def treePlayed (d K : ℕ) (W : ℝ) (advice : ℕ → TreeExpert d K → Fin K → ℝ)
    (loss : ℕ → Fin K → ℝ) (t : ℕ) : ℝ :=
  Part2.Prod.mixtureLoss (treeActive d K t) (treeRate d K W)
    (treeWeights d K W advice loss t) (advice t) (loss t)

theorem tree_active_nonempty {d K T : ℕ} (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    {t : ℕ} (ht : t < T) : (treeActive d K t).Nonempty := by
  let e : TreeExpert d K := (⟨(0, 2 ^ d), root_mem d 0⟩, ⟨0, by omega⟩)
  refine ⟨e, ?_⟩
  simp [treeActive, e]
  omega

theorem tree_initial_mass (d K : ℕ) (hK : 2 ≤ K) : ∑ e, treeInit d K e = 1 := by
  have hN : (expertCount d K : ℝ) ≠ 0 := by
    have := logExperts_pos (d := d) hK
    by_contra h
    simp [logExperts, h] at this
  simp only [treeInit, sum_const, nsmul_eq_mul, card_univ, card_tree_expert, one_div]
  exact mul_inv_cancel₀ hN

theorem tree_rates_pos {d K : ℕ} {W : ℝ} (hK : 2 ≤ K) (hW : 0 < W)
    (e : TreeExpert d K) : 0 < treeRate d K W e := by
  apply rate_pos hW (logExperts_pos hK)
  exact_mod_cast (block_bounds e.1.2).2.1

theorem tree_weights_invariant {d K T : ℕ} {W : ℝ} (hK : 2 ≤ K) (hW : 0 < W)
    (hT : T ≤ 2 ^ d) (advice : ℕ → TreeExpert d K → Fin K → ℝ) (loss : ℕ → Fin K → ℝ)
    (hpair : ∀ t < T, ∀ i ∈ treeActive d K t, ∀ j ∈ treeActive d K t,
      |Part2.Prod.adviceLoss (advice t) (loss t) i - Part2.Prod.adviceLoss (advice t) (loss t) j| ≤ 2 * W)
    {t : ℕ} (ht : t ≤ T) :
    (∀ e, 0 < treeWeights d K W advice loss t e) ∧ (∑ e, treeWeights d K W advice loss t e) = 1 := by
  apply evolution_invariant T (treeActive d K) (treeRate d K W) (treeInit d K) advice loss W hW.le
    (tree_rates_pos hK hW) (fun _ => rate_cap hW) (fun _ ht => tree_active_nonempty hK hT ht)
    _ (tree_initial_mass d K hK) hpair t ht
  intro e
  have hA := logExperts_pos (d := d) hK
  have hN : 0 < (expertCount d K : ℝ) := by
    by_contra hn
    have he : expertCount d K = 0 := by exact_mod_cast (le_antisymm (le_of_not_gt hn) (Nat.cast_nonneg _))
    simp [logExperts, he] at hA
  exact one_div_pos.mpr hN

/-- Full tree blocks: both long and short branches are proved for the same
prescribed eta and the same actual recursively updated trajectory. -/
theorem tree_block_bound {d K T : ℕ} {W : ℝ} (hK : 2 ≤ K) (hW : 0 < W)
    (hT : T ≤ 2 ^ d) (advice : ℕ → TreeExpert d K → Fin K → ℝ) (loss : ℕ → Fin K → ℝ)
    (hpair : ∀ t < T, ∀ i ∈ treeActive d K t, ∀ j ∈ treeActive d K t,
      |Part2.Prod.adviceLoss (advice t) (loss t) i - Part2.Prod.adviceLoss (advice t) (loss t) j| ≤ 2 * W)
    (J : ℕ × ℕ) (hJ : J ∈ blocks d 0) (hEnd : J.1 + J.2 ≤ T) (k : Fin K) :
    (∑ t ∈ Ico J.1 (J.1 + J.2),
      (treePlayed d K W advice loss t - Part2.Prod.adviceLoss (advice t) (loss t) (⟨J, hJ⟩, k))) ≤
      (4 * W * Real.sqrt (logExperts d K)) * Real.sqrt (J.2 : ℝ) := by
  let e : TreeExpert d K := (⟨J, hJ⟩, k)
  have hfilter : (range T).filter (fun t => e ∈ treeActive d K t) = Ico J.1 (J.1 + J.2) := by
    ext t
    simp only [mem_filter, mem_range, treeActive, mem_univ, true_and, mem_Ico]
    dsimp [e]
    omega
  have heq : (∑ t ∈ range T, Part2.Prod.excess (treeActive d K t) (treeRate d K W)
      (treeWeights d K W advice loss t) (advice t) (loss t) e) =
      ∑ t ∈ Ico J.1 (J.1 + J.2), (treePlayed d K W advice loss t -
        Part2.Prod.adviceLoss (advice t) (loss t) e) := by
    simp_rw [Part2.Prod.excess]
    rw [← sum_filter, hfilter]
    rfl
  have hi (t : ℕ) (ht : t ≤ T) := tree_weights_invariant hK hW hT advice loss hpair ht
  have hspan : ∀ t < T, ∀ i ∈ treeActive d K t,
      |treePlayed d K W advice loss t - Part2.Prod.adviceLoss (advice t) (loss t) i| ≤ 2 * W := by
    intro t ht i he
    exact mixture_span _ _ _ _ _ _ (tree_active_nonempty hK hT ht)
      (tree_rates_pos hK hW) (hi t (by omega)).1 (hpair t ht) i he
  have hm : 0 < (J.2 : ℝ) := by exact_mod_cast (block_bounds hJ).2.1
  have hA : 0 < logExperts d K := logExperts_pos hK
  by_cases hl : 4 * logExperts d K ≤ (J.2 : ℝ)
  · have hp := evolution_regret T (treeActive d K) (treeRate d K W) (treeInit d K)
      advice loss W hW.le (tree_rates_pos hK hW) (fun _ => rate_cap hW)
      (fun _ ht => tree_active_nonempty hK hT ht)
      (fun i => (hi 0 (by omega)).1 i) (tree_initial_mass d K hK) hpair e
    change (∑ t ∈ range T, Part2.Prod.excess (treeActive d K t) (treeRate d K W)
      (treeWeights d K W advice loss t) (advice t) (loss t) e) ≤ _ at hp
    rw [heq, hfilter, Nat.card_Ico] at hp
    have hn : J.1 + J.2 - J.1 = J.2 := by omega
    rw [hn] at hp
    simp only [treeInit, one_div_one_div] at hp
    change (∑ t ∈ Ico J.1 (J.1 + J.2), (treePlayed d K W advice loss t -
      Part2.Prod.adviceLoss (advice t) (loss t) e)) ≤
      logExperts d K / rate W (logExperts d K) (J.2 : ℝ) +
      4 * rate W (logExperts d K) (J.2 : ℝ) * W ^ 2 * (J.2 : ℝ) at hp
    rw [long_block_tuning hW hA hm hl] at hp
    exact hp
  · calc
      _ ≤ ∑ _t ∈ Ico J.1 (J.1 + J.2), 2 * W := by
        apply sum_le_sum
        intro t ht
        have ht' := mem_Ico.mp ht
        exact (abs_le.mp (hspan t (by omega) e (by simp [treeActive, e, ht'.1, ht'.2]))).2
      _ = 2 * W * (J.2 : ℝ) := by simp [mul_comm]
      _ ≤ _ := short_block_tuning hW.le hA.le hm.le (le_of_not_ge hl)

/-- The original 32W sqrt(n A_d) bound for every interval and comparator,
from actual tree experts and actual nonnegative multiplicative updates. -/
theorem tree_interval_regret {d K T : ℕ} {W : ℝ} (hK : 2 ≤ K) (hW : 0 < W)
    (hT : T ≤ 2 ^ d) (advice : ℕ → TreeExpert d K → Fin K → ℝ) (loss : ℕ → Fin K → ℝ)
    (hpair : ∀ t < T, ∀ i ∈ treeActive d K t, ∀ j ∈ treeActive d K t,
      |Part2.Prod.adviceLoss (advice t) (loss t) i - Part2.Prod.adviceLoss (advice t) (loss t) j| ≤ 2 * W)
    (hdom : ∀ t < T, ∀ e ∈ treeActive d K t,
      Part2.Prod.adviceLoss (advice t) (loss t) e ≤ loss t e.2)
    (u v : ℕ) (huv : u ≤ v) (hv : v ≤ T) (k : Fin K) :
    (∑ t ∈ Ico u v, (treePlayed d K W advice loss t - loss t k)) ≤
      32 * W * Real.sqrt (((v - u : ℕ) : ℝ) * logExperts d K) := by
  have h := dyadic_interval_bound d 0 u v (Nat.zero_le _) huv (by omega)
    (fun t => treePlayed d K W advice loss t - loss t k)
    (4 * W * Real.sqrt (logExperts d K)) (by positivity) (by
      intro J hJ hStart hEnd
      calc
        _ ≤ ∑ t ∈ Ico J.1 (J.1 + J.2), (treePlayed d K W advice loss t -
            Part2.Prod.adviceLoss (advice t) (loss t) (⟨J, hJ⟩, k)) := by
          apply sum_le_sum
          intro t ht
          have ht' := mem_Ico.mp ht
          have hd := hdom t (by omega) (⟨J, hJ⟩, k) (by simp [treeActive, ht'.1, ht'.2])
          linarith
        _ ≤ _ := tree_block_bound hK hW hT advice loss hpair J hJ (by omega) k)
  rw [Real.sqrt_mul (Nat.cast_nonneg (v - u))]
  nlinarith

end
end Part2.CNDProd

import staging.cnd20261024.process.ConcreteMaps
import staging.cnd20261024.process.TreeAdapter
import staging.cnd20261024.prod.Original

/-! Positive actual weights and a genuine pre-action probability suggestion
are obtained simultaneously by induction from the original public span.
No span of expert losses, q-simplex, update identity or regret is a field. -/
noncomputable section
open Finset MeasureTheory Set
open scoped BigOperators
namespace Part2.CNDProcess

theorem suggestion_simplex_of_positive {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype E] [DecidableEq E] (d : ExpertData ι E) (hW : d.W ≠ 0)
    (t : ℕ) (s : State ι E) (he : (activeSet d t).Nonempty)
    (heta : ∀ e, 0 < d.eta e) (hw : ∀ e, 0 < s.2 e) : suggestion d t s ∈ CND.simplex := by
  have hd : 0 < denominator d t s := by
    rw [denominator_eq_prod]
    exact Part2.Prod.denominator_pos _ _ _ (fun e _ ↦ heta e) (fun e _ ↦ hw e) he
  have ha (e : E) : 0 ≤ alpha d t s e := by
    unfold alpha
    split_ifs
    · exact div_nonneg (mul_pos (heta e) (hw e)).le hd.le
    · exact le_rfl
  have hm : (∑ e, alpha d t s e) = 1 := by
    have hh := alpha_weighted_sum d t s (fun _ ↦ 1)
    simp only [mul_one] at hh
    rw [hh, ← denominator_eq_prod, div_self (ne_of_gt hd)]
  constructor
  · intro i
    unfold suggestion
    rw [if_neg hW]
    exact sum_nonneg (fun e _ ↦ by split_ifs; exact ha e; exact le_rfl)
  · unfold suggestion
    simp only [if_neg hW]
    rw [sum_comm]
    simpa using hm

open CNDProd in
def actualData (d K : ℕ) (W R : ℝ) := treeData d K W R

variable {d K T : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀}

theorem actual_weights_invariant (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (H L R W : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (hW : 0 < W)
    (f : Feedback (ι := Fin K) ℱ) (ω : Ω)
    (hb : ∀ t < T, ∀ i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    {n : ℕ} (hn : n ≤ T) :
    let o := concreteMaps (K := K) H L R W hR hW.le
    let a := treeData d K W R
    (∀ e, 0 < (run o a f n ω).2 e) ∧ (∑ e, (run o a f n ω).2 e) = 1 := by
  let o := concreteMaps (K := K) H L R W hR hW.le
  let a := treeData d K W R
  change (∀ e, 0 < (run o a f n ω).2 e) ∧ (∑ e, (run o a f n ω).2 e) = 1
  have heta (e : CNDProd.TreeExpert d K) : 0 < a.eta e := CNDProd.tree_rates_pos hK hW e
  have hactive (t : ℕ) (ht : t < T) : (activeSet a t).Nonempty := by
    rw [treeData_active]
    exact CNDProd.tree_active_nonempty hK hT ht
  induction n with
  | zero =>
    have hc : 0 < (Fintype.card (CNDProd.TreeExpert d K) : ℝ) := by
      rw [CNDProd.card_tree_expert]
      have hl := CNDProd.logExperts_pos (d := d) hK
      by_contra hh
      have hz : CNDProd.expertCount d K = 0 := by
        exact_mod_cast (le_antisymm (le_of_not_gt hh) (Nat.cast_nonneg _))
      simp [CNDProd.logExperts, hz] at hl
    constructor
    · intro e; exact inv_pos.mpr hc
    · change (∑ _ : CNDProd.TreeExpert d K, (Fintype.card (CNDProd.TreeExpert d K) : ℝ)⁻¹) = 1
      simp only [sum_const, card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt hc)
  | succ t ih =>
    have hi := ih (by omega)
    let s := run o a f t ω
    have hq : suggestion a t s ∈ CND.simplex :=
      suggestion_simplex_of_positive a (ne_of_gt hW) t s (hactive t (by omega)) heta hi.1
    have hr := concrete_radius_isCND H L R W hH hL hR hW.le a rfl f t ω
    have hp := runProbability_simplex o a f t ω
    have hmin := extendedProx_minimizes W hW.le
      (confidence o a s, (radius o a s, suggestion a t s)) hr
    have hg := CNDProd.numbered_rows_geometry (d := d) hK hW.le
      (confidence o a s) (radius o a s) (suggestion a t s) (probability o a t s)
      (f.broadcast t ω) hr hq hp hmin (hb t (by omega))
    have hpair (e e' : CNDProd.TreeExpert d K) :
        |Part2.Prod.adviceLoss (processAdvice o a t s) (processLoss o a t s (f.broadcast t ω)) e -
          Part2.Prod.adviceLoss (processAdvice o a t s) (processLoss o a t s (f.broadcast t ω)) e'| ≤ 2 * W := by
      exact hg.1 e e'
    have hs := CNDProd.mixture_span (activeSet a t) a.eta s.2
      (processAdvice o a t s) (processLoss o a t s (f.broadcast t ω)) (2 * W)
      (hactive t (by omega)) heta hi.1 (fun e _ e' _ ↦ hpair e e')
    have hbound (e : CNDProd.TreeExpert d K) :
        |a.eta e * Part2.Prod.excess (activeSet a t) a.eta s.2
          (processAdvice o a t s) (processLoss o a t s (f.broadcast t ω)) e| ≤ 1 / 2 := by
      rw [abs_mul, abs_of_pos (heta e)]
      by_cases he : e ∈ activeSet a t
      · exact (mul_le_mul_of_nonneg_left
          (by simpa [Part2.Prod.excess, he] using hs e he) (heta e).le).trans (CNDProd.rate_cap hW)
      · simp [Part2.Prod.excess, he]
    change (∀ e, 0 < (step o a t s _ _ _).2 e) ∧ (∑ e, (step o a t s _ _ _).2 e) = 1
    rw [step_weights_eq_prod o a (ne_of_gt hW)]
    constructor
    · intro e
      exact Part2.Prod.step_pos _ _ _ _ _ e (hi.1 e) (hbound e)
    · rw [Part2.Prod.mass_conserved]
      · exact hi.2
      · exact ne_of_gt (Part2.Prod.denominator_pos _ _ _ (fun e _ ↦ heta e)
          (fun e _ ↦ hi.1 e) (hactive t (by omega)))

theorem actual_suggestion_simplex (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (H L R W : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (hW : 0 < W)
    (f : Feedback (ι := Fin K) ℱ) (ω : Ω)
    (hb : ∀ t < T, ∀ i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    {n : ℕ} (hn : n < T) :
    suggestion (treeData d K W R) n
      (run (concreteMaps H L R W hR hW.le) (treeData d K W R) f n ω) ∈ CND.simplex := by
  apply suggestion_simplex_of_positive _ (ne_of_gt hW) _ _
  · rw [treeData_active]
    exact CNDProd.tree_active_nonempty hK hT hn
  · exact CNDProd.tree_rates_pos hK hW
  · exact (actual_weights_invariant hK hT H L R W hH hL hR hW f ω hb hn.le).1

theorem actual_proxy_interval (hK : 2 ≤ K) (hT : T ≤ 2 ^ d)
    (H L R W : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L) (hR : 0 ≤ R) (hW : 0 < W)
    (f : Feedback (ι := Fin K) ℱ) (ω : Ω)
    (hb : ∀ t < T, ∀ i j, f.broadcast t ω j - f.broadcast t ω i ≤ W)
    (u v : ℕ) (huv : u ≤ v) (hv : v ≤ T) (k : Fin K) :
    let o := concreteMaps (K := K) H L R W hR hW.le
    let a := treeData d K W R
    (∑ t ∈ Ico u v,
      ((∑ j, runProbability o a f t j ω *
          processLoss o a t (run o a f t ω) (f.broadcast t ω) j) -
        processLoss o a t (run o a f t ω) (f.broadcast t ω) k)) ≤
      32 * W * Real.sqrt (((v - u : ℕ) : ℝ) * CNDProd.logExperts d K) := by
  let o := concreteMaps (K := K) H L R W hR hW.le
  let a := treeData d K W R
  let s := fun t ↦ run o a f t ω
  let θ := fun t ↦ confidence o a (s t)
  let r := fun t ↦ radius o a (s t)
  let q := fun t ↦ suggestion a t (s t)
  let p := fun t ↦ probability o a t (s t)
  let b := fun t ↦ f.broadcast t ω
  have hr (t : ℕ) (_ : t < T) : CND.IsCND (r t) :=
    concrete_radius_isCND H L R W hH hL hR hW.le a rfl f t ω
  have hq (t : ℕ) (ht : t < T) : q t ∈ stdSimplex ℝ (Fin K) :=
    actual_suggestion_simplex hK hT H L R W hH hL hR hW f ω hb ht
  have hp (t : ℕ) (_ : t < T) : p t ∈ stdSimplex ℝ (Fin K) := runProbability_simplex o a f t ω
  have hm (t : ℕ) (ht : t < T) :
      IsMinOn (CNDMatrixProx.objective (θ t) (r t) (q t) W) (stdSimplex ℝ (Fin K)) (p t) :=
    extendedProx_minimizes W hW.le (θ t, (r t, q t)) (hr t ht)
  have hqr (t : ℕ) (_ : t < T) :
      q t = Part2.Prod.mixture (CNDProd.treeActive d K t) (CNDProd.treeRate d K W)
        (CNDProd.treeWeights d K W (CNDProd.numberedAdvice hK W θ r q p)
          (CNDProd.proxyLoss θ r p b) t) (CNDProd.pureAdvice (fun e : CNDProd.TreeExpert d K ↦ e.2)) := by
    exact runSuggestion_eq_tree_mixture o W R (ne_of_gt hW) f ω t
  exact CNDProd.original_proxy_interval hK hW hT θ r q p b hr hq hp hm hb hqr u v huv hv k

theorem actual_zero_width_proxy_interval (H L R : ℝ) (hH : 0 ≤ H) (hL : 0 ≤ L)
    (hR : 0 ≤ R) (f : Feedback (ι := Fin K) ℱ) (ω : Ω)
    (hb : ∀ t < T, ∀ i j, f.broadcast t ω j - f.broadcast t ω i ≤ 0)
    (u v : ℕ) (hv : v ≤ T) (k : Fin K) :
    let o := concreteMaps (K := K) H L R 0 hR le_rfl
    let a := treeData d K 0 R
    (∑ t ∈ Ico u v,
      ((∑ j, runProbability o a f t j ω *
          processLoss o a t (run o a f t ω) (f.broadcast t ω) j) -
        processLoss o a t (run o a f t ω) (f.broadcast t ω) k)) ≤ 0 := by
  let o := concreteMaps (K := K) H L R 0 hR le_rfl
  let a := treeData d K 0 R
  let s := fun t ↦ run o a f t ω
  let θ := fun t ↦ confidence o a (s t)
  let r := fun t ↦ radius o a (s t)
  let q := fun t ↦ suggestion a t (s t)
  let p := fun t ↦ probability o a t (s t)
  have hr (t : ℕ) (_ : t < T) : CND.IsCND (r t) :=
    concrete_radius_isCND H L R 0 hH hL hR le_rfl a rfl f t ω
  have hm (t : ℕ) (ht : t < T) :
      IsMinOn (CNDMatrixProx.objective (θ t) (r t) (q t) 0) (stdSimplex ℝ (Fin K)) (p t) :=
    extendedProx_minimizes 0 le_rfl (θ t, (r t, q t)) (hr t ht)
  exact CNDProd.zero_width_proxy_interval θ r q p (fun t ↦ f.broadcast t ω) hr
    (fun t _ ↦ runProbability_simplex o a f t ω) hm hb u v hv k

end Part2.CNDProcess
end

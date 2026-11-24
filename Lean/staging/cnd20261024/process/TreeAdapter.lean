import staging.cnd20261024.process.ProdBridge
import staging.cnd20261024.prod.TreeProd

/-! The process expert state is the actual tree sleeping-Prod evolution.
This is a deterministic recursion identity, valid before any tail argument. -/
noncomputable section
open Finset MeasureTheory
open scoped BigOperators
namespace Part2.CNDProcess
open CNDProd

def treeData (d K : ℕ) (W R : ℝ) : ExpertData (Fin K) (TreeExpert d K) where
  active := fun t e ↦ decide (e ∈ treeActive d K t)
  arm := Prod.snd
  eta := treeRate d K W
  W := W
  R := R

theorem treeData_active (d K t : ℕ) (W R : ℝ) :
    activeSet (treeData d K W R) t = treeActive d K t := by
  ext e
  simp [activeSet, treeData]

variable {d K : ℕ} [MeasurableSpace (Fin K)] [MeasurableSingletonClass (Fin K)]
  {Ω : Type*} [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀}

theorem runWeights_eq_treeWeights (o : DecisionMaps (Fin K)) (W R : ℝ) (hW : W ≠ 0)
    (f : Feedback (ι := Fin K) ℱ) (ω : Ω) :
    (fun t ↦ (run o (treeData d K W R) f t ω).2) =
      treeWeights d K W
        (fun t ↦ processAdvice o (treeData d K W R) t (run o (treeData d K W R) f t ω))
        (fun t ↦ processLoss o (treeData d K W R) t (run o (treeData d K W R) f t ω)
          (f.broadcast t ω)) := by
  apply evolution_unique
  · funext e
    change (Fintype.card (TreeExpert d K) : ℝ)⁻¹ = 1 / (expertCount d K : ℝ)
    rw [card_tree_expert]
    exact (one_div _).symm
  · intro t
    change (step o (treeData d K W R) t _ _ _ _).2 = _
    rw [step_weights_eq_prod o _ hW, treeData_active]
    rfl

theorem runSuggestion_eq_tree_mixture (o : DecisionMaps (Fin K)) (W R : ℝ) (hW : W ≠ 0)
    (f : Feedback (ι := Fin K) ℱ) (ω : Ω) (t : ℕ) :
    suggestion (treeData d K W R) t (run o (treeData d K W R) f t ω) =
      Part2.Prod.mixture (treeActive d K t) (treeRate d K W)
        (treeWeights d K W
          (fun s ↦ processAdvice o (treeData d K W R) s (run o (treeData d K W R) f s ω))
          (fun s ↦ processLoss o (treeData d K W R) s (run o (treeData d K W R) f s ω)
            (f.broadcast s ω)) t)
        (pureAdvice (treeData d K W R)) := by
  rw [suggestion_eq_pure_mixture _ hW, treeData_active]
  have he := congrFun (runWeights_eq_treeWeights (d := d) o W R hW f ω) t
  rw [he]
  rfl

end Part2.CNDProcess
end

import staging.cnd20261026.«fix-bounded-sg».FiniteBoundedRate
import staging.cnd20261026.«fix-bounded-sg».FiniteSGRate

noncomputable section
open MeasureTheory
open scoped NNReal
namespace Part2.CNDHorizon
variable {K T d : ℕ} [Nonempty (Fin K)] [MeasurableSpace (Fin K)]
  [MeasurableSingletonClass (Fin K)] {Ω : Type*} [m₀ : MeasurableSpace Ω]
  {ℱ : Filtration ℕ m₀} {θ : Fin K → ℝ} {R M D : ℝ}

theorem bounded_zero_range_ledger (h : BoundedInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (t : ℕ) (ω : Ω) :
    FiniteBounded.actualLedger (d:=d) h B L hB t ω=0 := by
  simp [FiniteBounded.actualLedger,ledger,CNDPhysicalRegret.payment,CNDPhysicalRegret.rowRadius,
    CNDPhysical.actualSaturatedRadius,CNDPhysical.saturatedRadius,hR]

theorem sg_zero_range_ledger (ν : ℝ≥0) (h : SGInputs ℱ θ R M D T)
    (B L : ℝ) (hB : 0≤B) (hR : R=0) (t : ℕ) (ω : Ω) :
    FiniteSG.actualLedger (d:=d) ν h B L hB t ω=0 := by
  simp [FiniteSG.actualLedger,ledger,CNDPhysicalRegret.payment,CNDPhysicalRegret.rowRadius,
    CNDPhysical.actualSaturatedRadius,CNDPhysical.saturatedRadius,hR]

theorem sg_zero_range_keeps_noise (h : SGInputs ℱ θ R M D T) (hR : R=0) (t : ℕ) (ω : Ω) :
    h.residual t ω=h.drift t ω+h.noise t ω (h.action t ω)-h.error t (h.action t ω) ω := by
  have ht : θ (h.action t ω)=0 :=
    le_antisymm (by simpa only [hR] using (h.theta_range (h.action t ω)).2) (h.theta_range _).1
  unfold SGInputs.residual SGInputs.physical SGInputs.broadcast
  rw [ht]
  ring

theorem sg_zero_width_keeps_noise (ν : ℝ≥0) (d K T : ℕ) (B D δa δn : ℝ) (hW : B+2*D=0) :
    SGMain.publicCoefficient ν d K T B D δa δn=
      (2*(ν:ℝ))*Real.sqrt (2*Real.log ((K:ℝ)*(T:ℝ)^2/δn)) :=
  SGMain.zero_width_keeps_noise ν d K T B D δa δn hW

theorem bounded_zero_horizon (h : BoundedInputs ℱ θ R M D 0) (path : ℕ → Fin K) (ω : Ω) :
    FiniteBounded.pathRegret h path ω=0 := by simp [FiniteBounded.pathRegret]

theorem sg_zero_horizon (h : SGInputs ℱ θ R M D 0) (path : ℕ → Fin K) (ω : Ω) :
    FiniteSG.pathRegret h path ω=0 := by simp [FiniteSG.pathRegret]

theorem bounded_singleton_path {θ : Fin 1 → ℝ} (h : BoundedInputs ℱ θ R M D T)
    (path : ℕ → Fin 1) (ω : Ω) : FiniteBounded.pathRegret h path ω=0 := by
  unfold FiniteBounded.pathRegret
  apply Finset.sum_eq_zero
  intro t ht
  rw [Subsingleton.elim (h.action t ω) (path t),sub_self]

theorem sg_singleton_path {θ : Fin 1 → ℝ} (h : SGInputs ℱ θ R M D T)
    (path : ℕ → Fin 1) (ω : Ω) : FiniteSG.pathRegret h path ω=0 := by
  unfold FiniteSG.pathRegret
  apply Finset.sum_eq_zero
  intro t ht
  rw [Subsingleton.elim (h.action t ω) (path t),sub_self]
end Part2.CNDHorizon

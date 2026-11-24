import staging.cnd20261026.«fix-bounded-sg».FiniteLaws
import staging.cnd20261024.payment.Closure
import CNDPhysicalRegret

noncomputable section
open MeasureTheory Finset
open scoped BigOperators Matrix
namespace Part2.CNDHorizon
variable {ι η Ω : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι]
  [MeasurableSpace ι] [MeasurableSingletonClass ι] [Fintype η] [DecidableEq η]
  [m₀ : MeasurableSpace Ω] {ℱ : Filtration ℕ m₀} {θ : ι → ℝ} {R M D : ℝ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {T : ℕ}

def ledger (p : ℕ → ι → Ω → ℝ) (A : ℕ → Ω → ι) (H L R : ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  CNDPhysicalRegret.payment (CNDPhysical.actualSaturatedRadius (fun s i => p s i ω) t H L R)
    (fun i => p t i ω) (A t ω)

theorem inverseInformation_prefix (p q : ℕ → ι → ℝ) (n : ℕ) (hpq : ∀ t<n,p t=q t) :
    CNDPhysical.inverseInformation p n=CNDPhysical.inverseInformation q n := by
  unfold CNDPhysical.inverseInformation
  rw [information_prefix p q n hpq]

theorem resistance_prefix (p q : ℕ → ι → ℝ) (n : ℕ) (hpq : ∀ t<n,p t=q t) :
    CNDPhysical.resistance p n=CNDPhysical.resistance q n := by
  unfold CNDPhysical.resistance
  rw [information_prefix p q n hpq]

theorem gamma_prefix (p q : ℕ → ι → ℝ) (t : ℕ) (H L R : ℝ) (hpq : ∀ s≤t,p s=q s) :
    CNDInformation.actualGamma p t H L R=CNDInformation.actualGamma q t H L R := by
  unfold CNDInformation.actualGamma
  rw [radius_prefix p q t H L R (fun s hs => hpq s (Nat.le_of_lt hs)),hpq t le_rfl]

theorem ledger_prefix (m : CNDProbability.M1Model ℱ μ θ R M D)
    (p : ℕ → ι → Ω → ℝ) (A : ℕ → Ω → ι)
    (hp : ∀ t<T, m.p t=p t) (hA : ∀ t<T, m.action t=A t)
    (H L : ℝ) (t : ℕ) (ht : t<T) (ω : Ω) :
    CNDPayment.observablePayment m (CNDPayment.actualRadius m H L) t ω=ledger p A H L R t ω := by
  unfold CNDPayment.observablePayment CNDPayment.paymentAt CNDPayment.rowMean
    CNDPayment.actualRadius ledger CNDPhysicalRegret.payment CNDPhysicalRegret.rowRadius
  rw [hA t ht]
  have hr := radius_prefix (fun s i => m.p s i ω) (fun s i => p s i ω) t H L R
    (fun s hs => congrArg (fun q => fun i => q i ω) (hp s (lt_trans hs ht)))
  rw [hr,hp t ht]

theorem logdet_prefix (Q : Matrix ι η ℝ) (p q : ℕ → ι → ℝ) (n : ℕ)
    (hpq : ∀ t<n,p t=q t) : CNDInformation.coordinateLogdet Q p n=CNDInformation.coordinateLogdet Q q n := by
  unfold CNDInformation.coordinateLogdet CNDInformation.coordinateDesign CNDInformation.matrixDesign
  congr 3
  apply sum_congr rfl
  intro t ht
  dsimp only
  rw [hpq t (mem_range.mp ht)]

theorem budgetQ_prefix (Q : Matrix ι η ℝ) (p q : ℕ → ι → ℝ) (u n : ℕ) (H L R : ℝ)
    (hpq : ∀ t<u+n,p t=q t) :
    CNDInformation.branchedQ Q p u n H L R=CNDInformation.branchedQ Q q u n H L R := by
  unfold CNDInformation.branchedQ CNDInformation.actualQ
  rw [logdet_prefix Q p q (u+n) hpq,
    logdet_prefix Q p q u (fun t ht => hpq t (lt_of_lt_of_le ht (Nat.le_add_right u n)))]

theorem intervalSum_prefix (X Y : ℕ → Ω → ℝ) (hXY : ∀ t<T,X t=Y t)
    (u n : ℕ) (hu : u+n≤T) (ω : Ω) : CNDPayment.intervalSum X u n ω=CNDPayment.intervalSum Y u n ω := by
  apply sum_congr rfl
  intro t ht
  rw [hXY (u+t) (by have := mem_range.mp ht; omega)]

end Part2.CNDHorizon

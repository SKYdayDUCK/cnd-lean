import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Physical double-code quantization: deterministic core of U4

This module keeps both current/+1 codes. Seeds are hidden: the channel masses
below integrate them out. No public dither resource or private-component
observation is introduced. The finite-channel algebra is not the adaptive
statistical lower bound; see `audit/physical_quant.md` for the remaining steps.
-/

noncomputable section

namespace Part2.PhysicalQuantization

def lowerQueue (β X : ℝ) : ℝ := X / (1 + β * X)
def upperQueue (β X : ℝ) : ℝ := X / (1 - β * X)

/-- The actual capped M/M/1 cost, with a normalized numerator `A = α/Cmax`. -/
def cappedQueue (A F μ n lam : ℝ) : ℝ :=
  if n * lam < μ then min (A / (μ - n * lam)) F else F

def service (A lam m x : ℝ) : ℝ := (m + 1) * lam + A / x

/-- All three loads use the same service parameter; this is the Q4/Q5 identity. -/
theorem service_three_denominators (A lam m x : ℝ) :
    service A lam m x - m * lam = A / x + lam ∧
    service A lam m x - (m + 1) * lam = A / x ∧
    service A lam m x - (m + 2) * lam = A / x - lam := by
  unfold service
  constructor
  · ring
  constructor <;> ring

theorem cappedQueue_inverse_middle (A F lam m x : ℝ)
    (hA : 0 < A) (hx : 0 < x) (hxF : x ≤ F) :
    cappedQueue A F (service A lam m x) (m + 1) lam = x := by
  have ha : 0 < A / x := div_pos hA hx
  have hs : (m + 1) * lam < service A lam m x := by
    unfold service
    linarith
  unfold cappedQueue
  rw [if_pos hs, (service_three_denominators A lam m x).2.1]
  rw [div_div_cancel₀ (ne_of_gt hA)]
  simp [min_eq_left hxF]

/-- A common denominator bound for every physical point in the three-state family. -/
theorem geometry_margin (β X : ℝ) (hβ : 0 < β) (hβu : β ≤ 1/4)
    (hXl : 15/64 ≤ X) (hXu : X ≤ 49/64) :
    0 < 1 - β * X ∧ 1 - β * X ≥ 207/256 ∧
    0 < lowerQueue β X ∧ lowerQueue β X < X ∧
    X < upperQueue β X ∧ upperQueue β X ≤ 196/207 ∧
    upperQueue β X < 1 := by
  have hX : 0 < X := by linarith
  have hbX : 0 < β * X := mul_pos hβ hX
  have hbXu : β * X ≤ 49/256 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hβu) (le_of_lt hX)]
  have hd : 0 < 1 - β * X := by linarith
  have hp : 0 < 1 + β * X := by linarith
  have hl : 0 < lowerQueue β X := div_pos hX hp
  have hll : lowerQueue β X < X := by
    unfold lowerQueue
    apply (div_lt_iff₀ hp).2
    nlinarith [mul_pos hX hbX]
  have hu : X < upperQueue β X := by
    unfold upperQueue
    apply (lt_div_iff₀ hd).2
    nlinarith [mul_pos hX hbX]
  have huu : upperQueue β X ≤ 196/207 := by
    unfold upperQueue
    apply (div_le_iff₀ hd).2
    nlinarith
  exact ⟨hd, by linarith, hl, hll, hu, huu, by linarith⟩

theorem state_window (r u : ℝ) (hrl : 1/4 ≤ r) (hru : r ≤ 3/4)
    (hul : -(1/64) ≤ u) (huu : u ≤ 1/64) :
    15/64 ≤ r-u ∧ r-u ≤ 49/64 := by
  constructor <;> linarith

/-- Strong normalization includes the cap plus the largest private offset. -/
theorem normalization_margin (F H u : ℝ) (hH : 0 ≤ H)
    (hu : u ≤ 1/64) (hcap : F + 9*H/64 ≤ 1) :
    F + H*(1/8+u) ≤ 1 := by
  nlinarith [mul_nonneg hH (sub_nonneg.mpr hu)]

/-- The exact selected total has fixed support even as the private parameter moves. -/
theorem selected_total_support (H r u : ℝ) :
    H * (r-u) + H * (1/8+u) = H * (r+1/8) := by ring

/-- The physical points are strictly in the first quantization cell, including
the selected server's extra `m+2` point. -/
theorem first_cell_all_three (β X H Δ : ℝ)
    (hβ : 0 < β) (hβu : β ≤ 1/4)
    (hXl : 15/64 ≤ X) (hXu : X ≤ 49/64)
    (hH : 0 < H) (hHΔ : H ≤ Δ) :
    0 < H * lowerQueue β X ∧ H * lowerQueue β X < H * X ∧
    H * X < H * upperQueue β X ∧ H * upperQueue β X < Δ := by
  obtain ⟨_, _, hl, hll, hu, _, huu⟩ := geometry_margin β X hβ hβu hXl hXu
  refine ⟨mul_pos hH hl, mul_lt_mul_of_pos_left hll hH,
    mul_lt_mul_of_pos_left hu hH, ?_⟩
  have ht := mul_lt_mul_of_pos_left huu hH
  nlinarith

/-- The entire original current/+1 record before seeds are hidden. -/
def fullCodes (chosen : Bool) (Q : ℝ → ℝ) (β X : ℝ) : ℝ × ℝ :=
  if chosen then (Q X, Q (upperQueue β X)) else (Q (lowerQueue β X), Q X)

def counterfactualCode (chosen : Bool) (codes : ℝ × ℝ) : ℝ :=
  if chosen then codes.1 else codes.2

/-- For a fixed physical state and fixed common seed, the correct member of
the pair is the same counterfactual value whatever the learner's action. -/
theorem counterfactual_code_identity (chosen : Bool) (Q : ℝ → ℝ) (β X : ℝ) :
    counterfactualCode chosen (fullCodes chosen Q β X) = Q X := by
  cases chosen <;> rfl

/-- The midpoint collision requires all three points in one cell. Merely
colliding the two counterfactual values would not justify this conclusion. -/
theorem midpoint_complete_collision (chosen : Bool) (Q : ℝ → ℝ)
    (β X q : ℝ) (hh : Q (lowerQueue β X) = q) (hx : Q X = q)
    (hv : Q (upperQueue β X) = q) :
    fullCodes chosen Q β X = (q,q) := by
  cases chosen <;> simp [fullCodes, hh, hx, hv]

def weight1 (s u : ℝ) : ℝ := s/2 - 2*u
def weight2 (s : ℝ) : ℝ := 1-s
def weight3 (s u : ℝ) : ℝ := s/2 + 2*u

def threeMean (s u : ℝ) (f : ℝ → ℝ) : ℝ :=
  weight1 s u * f (1/4-u) + weight2 s * f (1/2-u) +
    weight3 s u * f (3/4-u)

theorem weights_sum (s u : ℝ) : weight1 s u + weight2 s + weight3 s u = 1 := by
  unfold weight1 weight2 weight3
  ring

theorem weights_positive (s u : ℝ)
    (hs : |s-2/3| ≤ 1/32) (hu : |u| ≤ 1/64) :
    1/4 ≤ weight1 s u ∧ 1/4 ≤ weight2 s ∧ 1/4 ≤ weight3 s u := by
  rw [abs_le] at hs hu
  unfold weight1 weight2 weight3
  constructor
  · linarith [hs.1, hu.2]
  constructor <;> linarith [hs.1, hs.2, hu.1]

theorem first_moment (s u : ℝ) : threeMean s u (fun X => X) = 1/2 := by
  unfold threeMean weight1 weight2 weight3
  ring

def momentS (β u : ℝ) : ℝ :=
  let b₀ := 1+β/2
  let e := β/4
  let m := (3*b₀^2-e^2)/(3*b₀*(b₀^2-e^2))
  let c := (3*b₀^2+e^2)/(3*b₀*(b₀^2-e^2))
  2/3-β*c*u+16*(3*m*b₀-2)*u^2-16*m*β*u^3

/-- The exact algebraic equation behind Q12/Q13, without a divided-by-curvature
definition of the weights. Positivity is a separate obligation. -/
theorem momentS_equation (β u : ℝ) (hβ : β ≠ 0)
    (hb : 1+β/2 ≠ 0) (hd : (1+β/2)^2-(β/4)^2 ≠ 0) :
    let b₀ := 1+β/2
    let e := β/4
    let m := (3*b₀^2-e^2)/(3*b₀*(b₀^2-e^2))
    let b := b₀-β*u
    e^2 * momentS β u = m*b*(b^2-e^2)+b*b₀-2*b^2+e^2 := by
  dsimp only [momentS]
  generalize hb₀ : (1+β/2) = b₀ at *
  generalize he : β/4 = e at *
  field_simp [hb, hd]
  rw [← hb₀, ← he]
  ring

/-- Finite weighted expectation of the inverse denominator, derived from the
three-node polynomial. No probabilistic independence is asserted here. -/
theorem inverse_moment_from_equation (b e m s u : ℝ)
    (hminus : b-e ≠ 0) (hzero : b ≠ 0) (hplus : b+e ≠ 0)
    (hm : e^2*s = m*b*(b^2-e^2)+b*(b+4*e*u)-2*b^2+e^2) :
    weight1 s u / (b-e) + weight2 s / b + weight3 s u / (b+e) = m := by
  unfold weight1 weight2 weight3
  field_simp [hminus, hzero, hplus]
  linear_combination 2*hm

/-- Q9's actual polynomial weights satisfy the required inverse moment.
The nonzero assumptions here are denominator checks, not moment assumptions. -/
theorem momentS_inverse_moment (β u : ℝ) (hβ : β ≠ 0)
    (hb : 1+β/2 ≠ 0) (hd : (1+β/2)^2-(β/4)^2 ≠ 0)
    (h1 : 1+β*(1/4-u) ≠ 0) (h2 : 1+β*(1/2-u) ≠ 0)
    (h3 : 1+β*(3/4-u) ≠ 0) :
    threeMean (momentS β u) u (fun X => 1/(1+β*X)) =
      (3*(1+β/2)^2-(β/4)^2) /
        (3*(1+β/2)*((1+β/2)^2-(β/4)^2)) := by
  let b₀ := 1+β/2
  let e := β/4
  let m := (3*b₀^2-e^2)/(3*b₀*(b₀^2-e^2))
  let b := b₀-β*u
  have heq : e^2 * momentS β u =
      m*b*(b^2-e^2)+b*(b+4*e*u)-2*b^2+e^2 := by
    calc
      _ = m*b*(b^2-e^2)+b*b₀-2*b^2+e^2 := momentS_equation β u hβ hb hd
      _ = _ := by dsimp [b, b₀, e]; ring
  have hn1 : b-e ≠ 0 := by
    convert h1 using 1 <;> dsimp [b, b₀, e] <;> ring
  have hn2 : b ≠ 0 := by
    convert h2 using 1 <;> dsimp [b, b₀] <;> ring
  have hn3 : b+e ≠ 0 := by
    convert h3 using 1 <;> dsimp [b, b₀, e] <;> ring
  have hi := inverse_moment_from_equation b e m (momentS β u) u hn1 hn2 hn3 heq
  change threeMean (momentS β u) u (fun X => 1/(1+β*X)) = m
  convert hi using 1 <;> dsimp [threeMean, b, b₀, e] <;> ring

theorem lowerQueue_inverse_identity (β X : ℝ) (hβ : β ≠ 0)
    (hd : 1+β*X ≠ 0) :
    lowerQueue β X = (1-1/(1+β*X))/β := by
  have hcancel := mul_inv_cancel₀ hd
  apply (eq_div_iff hβ).2
  unfold lowerQueue
  simp only [div_eq_mul_inv, one_mul]
  linear_combination hcancel

/-- Q13's second public moment follows from the explicit three-state weights.
In particular this is not a marginal-match assumption. -/
theorem momentS_lower_moment (β u : ℝ) (hβ : β ≠ 0)
    (hb : 1+β/2 ≠ 0) (hd : (1+β/2)^2-(β/4)^2 ≠ 0)
    (h1 : 1+β*(1/4-u) ≠ 0) (h2 : 1+β*(1/2-u) ≠ 0)
    (h3 : 1+β*(3/4-u) ≠ 0) :
    threeMean (momentS β u) u (lowerQueue β) =
      (1-(3*(1+β/2)^2-(β/4)^2) /
        (3*(1+β/2)*((1+β/2)^2-(β/4)^2)))/β := by
  have hi := momentS_inverse_moment β u hβ hb hd h1 h2 h3
  calc
    _ = (1-threeMean (momentS β u) u (fun X => 1/(1+β*X)))/β := by
      dsimp [threeMean]
      rw [lowerQueue_inverse_identity β (1/4-u) hβ h1,
        lowerQueue_inverse_identity β (1/2-u) hβ h2,
        lowerQueue_inverse_identity β (3/4-u) hβ h3]
      unfold weight1 weight2 weight3
      ring
    _ = _ := by rw [hi]

/-- Rational M/M/1 geometry closes the extra product moment needed when the
two hidden rounding seeds are independent. -/
theorem product_moment_identity (β X : ℝ) (hβ : β ≠ 0)
    (hd : 1+β*X ≠ 0) :
    X * lowerQueue β X = (X-lowerQueue β X)/β := by
  have hcancel := mul_inv_cancel₀ hd
  apply (eq_div_iff hβ).2
  unfold lowerQueue
  simp only [div_eq_mul_inv]
  linear_combination X * hcancel

/-- Full two-bit masses after integrating a shared hidden uniform seed.
`false,true` means lower zero, upper one. -/
def pairedMass (τ a b : ℝ) (code : Bool × Bool) : ℝ :=
  match code with
  | (false, false) => 1-τ*b
  | (false, true) => τ*(b-a)
  | (true, false) => 0
  | (true, true) => τ*a

def independentMass (τ a b : ℝ) (code : Bool × Bool) : ℝ :=
  match code with
  | (false, false) => 1-τ*(a+b)+τ^2*(a*b)
  | (false, true) => τ*b-τ^2*(a*b)
  | (true, false) => τ*a-τ^2*(a*b)
  | (true, true) => τ^2*(a*b)

theorem pairedMass_nonneg (τ a b : ℝ) (hτ : 0 ≤ τ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : τ*b ≤ 1) (code : Bool × Bool) :
    0 ≤ pairedMass τ a b code := by
  rcases code with ⟨c,d⟩
  cases c <;> cases d <;> dsimp [pairedMass]
  · linarith
  · exact mul_nonneg hτ (sub_nonneg.mpr hab)
  · exact le_refl 0
  · exact mul_nonneg hτ ha

theorem pairedMass_sum (τ a b : ℝ) :
    pairedMass τ a b (false,false) + pairedMass τ a b (false,true) +
    pairedMass τ a b (true,false) + pairedMass τ a b (true,true) = 1 := by
  dsimp [pairedMass]
  ring

/-- All four joint masses, rather than just each code's marginal, are fixed
by the two first moments in the paired protocol. -/
theorem paired_complete_channel (s u τ a b : ℝ) (f g : ℝ → ℝ)
    (hf : threeMean s u f = a) (hg : threeMean s u g = b)
    (code : Bool × Bool) :
    threeMean s u (fun X => pairedMass τ (f X) (g X) code) =
      pairedMass τ a b code := by
  rcases code with ⟨c,d⟩
  have htf := congrArg (fun z : ℝ => τ*z) hf
  have htg := congrArg (fun z : ℝ => τ*z) hg
  cases c <;> cases d <;>
    dsimp [threeMean, pairedMass] at * <;>
    unfold weight1 weight2 weight3 at * <;> nlinarith [htf, htg]

/-- Complete unselected paired record under the actual Q9 weights. The right
side has no `u`, including for the mixed-code outcome. -/
theorem unselected_paired_channel (β u τ : ℝ) (hβ : β ≠ 0)
    (hb : 1+β/2 ≠ 0) (hd : (1+β/2)^2-(β/4)^2 ≠ 0)
    (h1 : 1+β*(1/4-u) ≠ 0) (h2 : 1+β*(1/2-u) ≠ 0)
    (h3 : 1+β*(3/4-u) ≠ 0) (code : Bool × Bool) :
    threeMean (momentS β u) u
      (fun X => pairedMass τ (lowerQueue β X) X code) =
    pairedMass τ ((1-(3*(1+β/2)^2-(β/4)^2) /
      (3*(1+β/2)*((1+β/2)^2-(β/4)^2)))/β) (1/2) code := by
  exact paired_complete_channel _ _ _ _ _ _ _
    (momentS_lower_moment β u hβ hb hd h1 h2 h3) (first_moment _ _) code

/-- For independent hidden seeds the product moment is essential. This result
does not discard the otherwise possible `(true,false)` outcome. -/
theorem independent_complete_channel (s u τ a b ab : ℝ) (f g : ℝ → ℝ)
    (hf : threeMean s u f = a) (hg : threeMean s u g = b)
    (hfg : threeMean s u (fun X => f X*g X) = ab)
    (code : Bool × Bool) :
    threeMean s u (fun X => independentMass τ (f X) (g X) code) =
      independentMass τ a b code +
        (if code.1 = code.2 then τ^2*(ab-a*b) else -τ^2*(ab-a*b)) := by
  rcases code with ⟨c,d⟩
  cases c <;> cases d
  all_goals
    dsimp [threeMean, independentMass] at *
    unfold weight1 weight2 weight3 at *
  · linear_combination -τ*hf -τ*hg + τ^2*hfg
  · linear_combination τ*hg - τ^2*hfg
  · linear_combination τ*hf - τ^2*hfg
  · linear_combination τ^2*hfg

/-- The selected channel really contains the `m+2` value, not a repeated code. -/
def selectedPairedMass (β τ X : ℝ) (code : Bool × Bool) : ℝ :=
  pairedMass τ X (upperQueue β X) code

theorem selected_extra_code_positive (β τ X : ℝ)
    (hβ : 0 < β) (hβu : β ≤ 1/4) (hτ : 0 < τ)
    (hXl : 15/64 ≤ X) (hXu : X ≤ 49/64) :
    0 < selectedPairedMass β τ X (false,true) := by
  have h := (geometry_margin β X hβ hβu hXl hXu).2.2.2.2.1
  exact mul_pos hτ (sub_pos.mpr h)

/-- Revealing the uniform seed produces a distinguishing interval. The same
threshold with hidden seeds is averaged in `pairedMass`; it is not public U. -/
theorem public_seed_distinguishing_interval (τ r ε U : ℝ)
    (hτ : 0 < τ) (hε : 0 < ε) (hUl : τ*r < U)
    (hUu : U ≤ τ*(r+ε)) :
    ¬ U ≤ τ*r ∧ U ≤ τ*(r-(-ε)) ∧ τ*r < τ*(r+ε) := by
  constructor
  · exact not_le.mpr hUl
  constructor
  · simpa using hUu
  · nlinarith

end Part2.PhysicalQuantization

import staging.cnd20261024.net.FiniteNet
import Mathlib.Analysis.Seminorm
import Mathlib.Analysis.Normed.Operator.Basic

noncomputable section
namespace Part2.CNDNet

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Finite net control extends to the entire sphere, including for unbounded observations.
The operator norm is finite independently of any bounded-increment argument. -/
theorem extend_sphere (s : Finset E) {ε A B C : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hs : ∀ b ∈ s, ‖b‖ = 1)
    (hnet : ∀ a : E, ‖a‖ = 1 → ∃ b ∈ s, ‖a - b‖ ≤ ε)
    (energy : Seminorm ℝ E) (henergy : ∀ a, energy a ≤ C * ‖a‖)
    (F : E →L[ℝ] ℝ) (hfinite : ∀ b ∈ s, ‖F b‖ ≤ A * energy b + B)
    (a : E) (ha : ‖a‖ = 1) :
    ‖F a‖ ≤ A * energy a + B + A * C * ε + ε * ((A * C + B) / (1 - ε)) := by
  have hunit : ∀ x : E, ‖x‖ = 1 → ‖F x‖ ≤ A * C + B + ‖F‖ * ε := by
    intro x hx
    obtain ⟨b, hb, hxb⟩ := hnet x hx
    have hbc : energy b ≤ C := by simpa [hs b hb] using henergy b
    calc
      ‖F x‖ ≤ ‖F b‖ + ‖F (x - b)‖ := by
        simpa only [map_sub, add_sub_cancel] using norm_add_le (F b) (F x - F b)
      _ ≤ A * energy b + B + ‖F‖ * ε :=
        add_le_add (hfinite b hb) ((F.le_opNorm _).trans (mul_le_mul_of_nonneg_left hxb (norm_nonneg _)))
      _ ≤ _ := by nlinarith
  have hop : ‖F‖ ≤ A * C + B + ‖F‖ * ε :=
    ContinuousLinearMap.opNorm_le_of_unit_norm (by positivity) hunit
  have hop' : ‖F‖ ≤ (A * C + B) / (1 - ε) := by
    apply (le_div_iff₀ (sub_pos.mpr hε1)).2
    nlinarith
  obtain ⟨b, hb, hab⟩ := hnet a ha
  have he : energy b ≤ energy a + C * ε := by
    have hd := henergy (b - a)
    rw [norm_sub_rev] at hd
    have hp := map_add_le_add energy a (b - a)
    rw [add_sub_cancel] at hp
    nlinarith
  calc
    ‖F a‖ ≤ ‖F b‖ + ‖F (a - b)‖ := by
      simpa only [map_sub, add_sub_cancel] using norm_add_le (F b) (F a - F b)
    _ ≤ A * energy b + B + ‖F‖ * ε :=
      add_le_add (hfinite b hb) ((F.le_opNorm _).trans (mul_le_mul_of_nonneg_left hab (norm_nonneg _)))
    _ ≤ _ := by nlinarith

/-- A convenient rational error budget for the paper's epsilon choice. -/
theorem extension_error_bound {ε A B C : ℝ} (hε : 0 ≤ ε) (hε16 : ε ≤ 1 / 16)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hεC : ε * C ≤ 1 / 8) :
    A * C * ε + ε * ((A * C + B) / (1 - ε)) ≤ (4 * A + B) / 15 := by
  have hd : 0 < 1 - ε := by linarith
  have h1 : A * C * ε ≤ A / 8 := by nlinarith
  have h2 : ε * (A * C + B) ≤ A / 8 + B / 16 := by nlinarith
  have h3 : ε * ((A * C + B) / (1 - ε)) ≤ (2 * A + B) / 15 := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hd).2
    nlinarith
  linarith

theorem extend_all (s : Finset E) {ε A B C : ℝ}
    (hε : 0 ≤ ε) (hε1 : ε < 1) (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hs : ∀ b ∈ s, ‖b‖ = 1)
    (hnet : ∀ a : E, ‖a‖ = 1 → ∃ b ∈ s, ‖a - b‖ ≤ ε)
    (energy : Seminorm ℝ E) (henergy : ∀ a, energy a ≤ C * ‖a‖)
    (F : E →L[ℝ] ℝ) (hfinite : ∀ b ∈ s, ‖F b‖ ≤ A * energy b + B)
    (x : E) :
    ‖F x‖ ≤ A * energy x +
      (B + A * C * ε + ε * ((A * C + B) / (1 - ε))) * ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx]
  have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let a : E := ‖x‖⁻¹ • x
  have ha : ‖a‖ = 1 := by simp [a, norm_smul, abs_of_pos hn, hn.ne']
  have hu := extend_sphere s hε hε1 hA hB hC hs hnet energy henergy F hfinite a ha
  have hf : ‖F a‖ = ‖F x‖ / ‖x‖ := by
    simp [a, map_smul, norm_smul, abs_of_pos hn, div_eq_inv_mul]
  have he : energy a = energy x / ‖x‖ := by
    simp [a, map_smul_eq_mul, abs_of_pos hn, div_eq_inv_mul]
  rw [hf, he] at hu
  have hr : A * (energy x / ‖x‖) + B + A * C * ε + ε * ((A * C + B) / (1 - ε)) =
      (A * energy x + (B + A * C * ε + ε * ((A * C + B) / (1 - ε))) * ‖x‖) / ‖x‖ := by
    field_simp
    <;> ring
  rw [hr] at hu
  exact (div_le_div_iff_of_pos_right hn).mp hu

end Part2.CNDNet

#print axioms Part2.CNDNet.extend_sphere
#print axioms Part2.CNDNet.extension_error_bound
#print axioms Part2.CNDNet.extend_all

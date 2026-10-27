module

public import GlobalPhi43.Attachment.IntegerModelMoments

/-! # A real-power seventh-degree moment profile from all integer moments -/

public noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace GlobalPhi43.Attachment

/-- The source three-term estimate, valid also for extended observables. -/
theorem triple_pow_bound (X Y : ℝ≥0∞) (n : ℕ) :
    (1 + X + Y) ^ n ≤ 3 ^ n * (1 + X ^ n + Y ^ n) := by
  let A := max 1 (max X Y)
  have h1 : 1 ≤ A := le_max_left _ _
  have hX : X ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hY : Y ≤ A := (le_max_right _ _).trans (le_max_right _ _)
  have hsum : 1 + X + Y ≤ 3 * A := by
    calc
      _ ≤ A + A + A := add_le_add (add_le_add h1 hX) hY
      _ = _ := by ring
  have hpow : A ^ n ≤ 1 + X ^ n + Y ^ n := by
    by_cases hA : max X Y ≤ 1
    · simp only [A, max_eq_left hA, one_pow]
      exact (le_add_of_nonneg_right bot_le).trans (le_add_of_nonneg_right bot_le)
    · rw [show A = max X Y from max_eq_right (le_of_not_ge hA)]
      by_cases hXY : X ≤ Y
      · rw [max_eq_right hXY]
        exact le_add_of_nonneg_left bot_le
      · rw [max_eq_left (le_of_not_ge hXY)]
        exact (le_add_of_nonneg_left bot_le).trans (le_add_of_nonneg_right bot_le)
  calc
    _ ≤ (3 * A) ^ n := pow_le_pow_left' hsum n
    _ = 3 ^ n * A ^ n := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_right hpow _

/-- Real p is bounded using the one integer ceil(p), with no new random variable. -/
theorem rpow_le_one_add_nat_pow (x : ℝ≥0∞) {p : ℝ} (hp : 0 ≤ p)
    (q : ℕ) (hpq : p ≤ q) : x ^ p ≤ 1 + x ^ q := by
  by_cases hx : x ≤ 1
  · exact (ENNReal.rpow_le_one hx hp).trans (le_add_of_nonneg_right bot_le)
  · have h := ENNReal.rpow_le_rpow_of_exponent_le (le_of_not_ge hx) hpq
    rw [ENNReal.rpow_natCast] at h
    exact h.trans (le_add_of_nonneg_left bot_le)

/-- This finite profile is deterministic and precedes the probability space. -/
def seventhMomentProfile (c : ℝ≥0) (CX CY : ℕ → ℝ≥0) (p : ℝ) : ℝ≥0 :=
  1 + c ^ (⌈p⌉₊) * 3 ^ (7 * ⌈p⌉₊) * (1 + CX (7 * ⌈p⌉₊) + CY (7 * ⌈p⌉₊))

/-- Extended seventh-power Q has the same space-independent real-p profile.
Only X measurability is needed to split the sum integral; Y's integer moments
are enough for the last summand. -/
theorem seventh_moment_le (c : ℝ≥0) (CX CY : ℕ → ℝ≥0)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X Y : Ω → ℝ≥0∞) (hX : AEMeasurable X P)
    (hCX : ∀ n : ℕ, 1 ≤ n → ∫⁻ ω, X ω ^ n ∂P ≤ CX n)
    (hCY : ∀ n : ℕ, 1 ≤ n → ∫⁻ ω, Y ω ^ n ∂P ≤ CY n)
    {p : ℝ} (hp : 1 ≤ p) :
    ∫⁻ ω, ((c : ℝ≥0∞) * (1 + X ω + Y ω) ^ 7) ^ p ∂P ≤ seventhMomentProfile c CX CY p := by
  let q : ℕ := ⌈p⌉₊
  have hpq : p ≤ (q : ℝ) := Nat.le_ceil p
  have hq : 1 ≤ q := by
    have h : 0 < (q : ℝ) := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hp) hpq
    exact_mod_cast h
  have hn : 1 ≤ 7 * q := by omega
  have hi : ∫⁻ ω, ((c : ℝ≥0∞) * (1 + X ω + Y ω) ^ 7) ^ q ∂P ≤
      (c : ℝ≥0∞) ^ q * 3 ^ (7 * q) * (1 + CX (7 * q) + CY (7 * q)) := by
    have hb (ω : Ω) : ((c : ℝ≥0∞) * (1 + X ω + Y ω) ^ 7) ^ q ≤
        ((c : ℝ≥0∞) ^ q * 3 ^ (7 * q)) * (1 + X ω ^ (7*q) + Y ω ^ (7*q)) := by
      rw [mul_pow, ← pow_mul]
      exact (mul_le_mul_right (triple_pow_bound (X ω) (Y ω) (7*q)) _).trans_eq (mul_assoc _ _ _).symm
    apply (lintegral_mono hb).trans
    rw [lintegral_const_mul' _ _ (by finiteness)]
    have hXm : AEMeasurable (fun ω => (1 : ℝ≥0∞) + X ω ^ (7*q)) P :=
      aemeasurable_const.add (hX.pow_const _)
    have hs : (∫⁻ ω, 1 + X ω ^ (7*q) + Y ω ^ (7*q) ∂P) =
        1 + (∫⁻ ω, X ω ^ (7*q) ∂P) + ∫⁻ ω, Y ω ^ (7*q) ∂P := by
      rw [lintegral_add_left' hXm]
      rw [lintegral_add_left (measurable_const : Measurable (fun _ : Ω => (1 : ℝ≥0∞)))]
      simp only [lintegral_const, measure_univ, mul_one]
    rw [hs]
    exact mul_le_mul_right (add_le_add (add_le_add le_rfl (hCX _ hn)) (hCY _ hn)) _
  have hb (ω : Ω) := rpow_le_one_add_nat_pow
    ((c : ℝ≥0∞) * (1 + X ω + Y ω) ^ 7) (le_trans zero_le_one hp) q hpq
  apply (lintegral_mono hb).trans
  rw [lintegral_add_left measurable_const]
  simp only [lintegral_const, measure_univ, mul_one]
  have h := add_le_add (le_rfl : (1 : ℝ≥0∞) ≤ 1) hi
  simpa only [seventhMomentProfile, q, ENNReal.coe_add, ENNReal.coe_one,
    ENNReal.coe_mul, ENNReal.coe_pow, ENNReal.coe_ofNat] using h

end GlobalPhi43.Attachment

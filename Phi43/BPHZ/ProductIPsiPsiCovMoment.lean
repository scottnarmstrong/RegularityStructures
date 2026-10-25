/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovField
public import Phi43.BPHZ.GammaFullUniform
public import Phi43.BPHZ.SemigroupTestCoord
import Mathlib.Tactic

/-!
# Moments of `v₁(x, y)` for all `r = ‖y - x‖`

* `hairerIPsiRecentred_integral_sq_le`: `E v₁² ≤ C r^(3-δ)` for every `y` (local bound for
  `r ≤ 1/2`, the uniform `(1 + r)` bound beyond);
* `hairerIPsiRecentred_pow_le`: all moments of `v₁`, in terms of `1 + r`;
* `abs_integral_mul_le_of_sq_le`: `|E v₁(y) v₁(y')| ≤ C ρ ρ'` if `E v₁² ≤ C ρ²`, `E v₁'² ≤ C ρ'²`;
* `integrable_and_integral_pow_le_of_lintegral`: from an `Lᵠ` bound in lower-integral form to a
  real moment, for an even power.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- From an `Lᵠ` bound in lower-integral form to a real moment, for an even power. -/
theorem integrable_and_integral_pow_le_of_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Y : Ω → ℝ} (hY : AEStronglyMeasurable Y P) {k : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : ∫⁻ ω, ‖Y ω‖ₑ ^ (2 * k) ∂P ≤ ENNReal.ofReal c ^ (2 * k)) :
    Integrable (fun ω => Y ω ^ (2 * k)) P ∧ ∫ ω, Y ω ^ (2 * k) ∂P ≤ c ^ (2 * k) := by
  have hnn : ∀ ω, 0 ≤ Y ω ^ (2 * k) := fun ω => by
    rw [pow_mul]; positivity
  have he : ∀ ω, ‖Y ω‖ₑ ^ (2 * k) = ENNReal.ofReal (Y ω ^ (2 * k)) := fun ω => by
    rw [← enorm_pow, Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn ω)]
  simp_rw [he] at h
  have hlt : ∫⁻ ω, ENNReal.ofReal (Y ω ^ (2 * k)) ∂P < ⊤ :=
    lt_of_le_of_lt h (ENNReal.pow_lt_top ENNReal.ofReal_lt_top)
  have hm : AEStronglyMeasurable (fun ω => Y ω ^ (2 * k)) P := hY.pow _
  have hi : Integrable (fun ω => Y ω ^ (2 * k)) P :=
    ⟨hm, (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall hnn)).2 hlt⟩
  refine ⟨hi, ?_⟩
  have h2 : ENNReal.ofReal (∫ ω, Y ω ^ (2 * k) ∂P) ≤ ENNReal.ofReal (c ^ (2 * k)) := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hnn),
      ENNReal.ofReal_pow hc]
    exact h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h2

/-- **All moments of `v₁`**, in terms of `1 + r`. -/
theorem hairerIPsiRecentred_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    {k : ℕ} (hk : 1 ≤ 2 * k) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        Integrable (fun ω => hairerIPsiRecentred N ξ ω x y ^ (2 * k)) P ∧
        ∫ ω, hairerIPsiRecentred N ξ ω x y ^ (2 * k) ∂P ≤
          (C * (1 + parabolicNorm (y - x))) ^ (2 * k) := by
  obtain ⟨C, hC, h⟩ := gammaPsiTaylor_lintegral_enorm_pow_le_uniform.{u} N hρ hk
  refine ⟨C, hC, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have hm : Measurable (fun ω => hairerIPsiRecentred N ξ ω x y) :=
    Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ q.1 x q.2)
      (f := fun ω : Ω => (ω, y)) (measurable_hairerIPsiRecentred_prod_uncurry N hξ x)
      (measurable_id.prodMk measurable_const)
  have hr : ∀ i, |(y.2 - x.2) i| ≤ parabolicNorm (y - x) := fun i =>
    abs_coord_le_parabolicNorm (y - x) i
  have h1 := h hW hε hξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) (parabolicNorm (y - x))
    (parabolicNorm_nonneg _) hr
  have e : ∀ ω, hairerIPsiRecentred N ξ ω x y =
      gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω := fun ω =>
    hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ.1 ω) x y
  have hc : 0 ≤ C * (1 + parabolicNorm (y - x)) := by
    have := parabolicNorm_nonneg (y - x); positivity
  have hm' : AEStronglyMeasurable (fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1)
      (y.2 - x.2) ω) P := by
    have : (fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω) =
        fun ω => hairerIPsiRecentred N ξ ω x y := funext fun ω => (e ω).symm
    rw [this]; exact hm.aestronglyMeasurable
  have key := integrable_and_integral_pow_le_of_lintegral (k := k) hm' hc h1
  have hfun : (fun ω => hairerIPsiRecentred N ξ ω x y) =
      fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω := funext e
  simp only [e]
  exact key

/-- `E v₁(x, y)² ≤ C r^(3-δ)`, for every `y`. -/
theorem hairerIPsiRecentred_integral_sq_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫ ω, hairerIPsiRecentred N ξ ω x y ^ 2 ∂P ≤ C * parabolicNorm (y - x) ^ (3 - δ) := by
  obtain ⟨C1, hC1, h1⟩ := gammaPsiTaylor_second_moment_le.{u} N hρ hδ hδ1
  obtain ⟨C2, hC2, h2⟩ := hairerIPsiRecentred_pow_le.{u} N hρ (k := 1) (by norm_num)
  refine ⟨C1 + 18 * C2 ^ 2, by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  set r := parabolicNorm (y - x) with hr
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hp0 : 0 ≤ r ^ (3 - δ) := Real.rpow_nonneg hr0 _
  by_cases hsm : r ≤ 1 / 2
  · have := h1 hW hε hξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) hsm
    have e : ∀ ω, hairerIPsiRecentred N ξ ω x y =
        gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω := fun ω =>
      hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ.1 ω) x y
    simp_rw [e]
    rw [show parabolicNorm (y.1 - x.1, y.2 - x.2) = r from rfl] at this
    refine this.trans ?_
    nlinarith [mul_nonneg (mul_nonneg (by positivity : (0 : ℝ) ≤ 18) (sq_nonneg C2)) hp0]
  · have hbig : 1 / 2 < r := lt_of_not_ge hsm
    have := (h2 hW hε hξ x y).2
    refine this.trans ?_
    have hr3 : r ^ 2 ≤ 2 * r ^ (3 - δ) := by
      have e : r ^ (3 - δ) = r ^ (2 : ℕ) * r ^ (1 - δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num; ring_nf
      have hq : 1 / 2 ≤ r ^ (1 - δ) := by
        have a1 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 - δ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        have a2 : (1 / 2 : ℝ) ^ (1 - δ) ≤ r ^ (1 - δ) :=
          Real.rpow_le_rpow (by norm_num) hbig.le (by linarith)
        simpa using a1.trans a2
      rw [e]
      nlinarith [sq_nonneg r]
    have : (C2 * (1 + r)) ^ (2 * 1) ≤ 9 * C2 ^ 2 * r ^ 2 := by
      have : 1 + r ≤ 3 * r := by linarith
      calc (C2 * (1 + r)) ^ (2 * 1) = C2 ^ 2 * (1 + r) ^ 2 := by ring
        _ ≤ C2 ^ 2 * (3 * r) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) this 2) (sq_nonneg _)
        _ = _ := by ring
    nlinarith [mul_nonneg (sq_nonneg C2) hp0, mul_nonneg hC1 hp0]

/-- `|E v₁(y) v₁(y')| ≤ C ρ ρ'` from the second moment bounds `C ρ²`, `C ρ'²`. -/
theorem abs_integral_mul_le_of_sq_le {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {v v' : Ω → ℝ} (hv : Integrable (fun ω => v ω ^ 2) P) (hv' : Integrable (fun ω => v' ω ^ 2) P)
    (hm : AEStronglyMeasurable v P) (hm' : AEStronglyMeasurable v' P) {C a a' : ℝ} (ha : 0 < a)
    (ha' : 0 < a') (h1 : ∫ ω, v ω ^ 2 ∂P ≤ C * a ^ 2) (h2 : ∫ ω, v' ω ^ 2 ∂P ≤ C * a' ^ 2) :
    |∫ ω, v ω * v' ω ∂P| ≤ C * (a * a') := by
  have hpt : ∀ ω, |v ω * v' ω| ≤ ((a' / a) * v ω ^ 2 + (a / a') * v' ω ^ 2) / 2 := fun ω => by
    have h' : 0 < a' / a := div_pos ha' ha
    have hinv : a / a' = (a' / a)⁻¹ := (inv_div a' a).symm
    set l := a' / a with hl
    rw [hinv]
    have e1 : 0 ≤ (l * v ω - v' ω) ^ 2 / l := div_nonneg (sq_nonneg _) h'.le
    have e2 : 0 ≤ (l * v ω + v' ω) ^ 2 / l := div_nonneg (sq_nonneg _) h'.le
    have e3 : (l * v ω - v' ω) ^ 2 / l = l * v ω ^ 2 - 2 * (v ω * v' ω) + l⁻¹ * v' ω ^ 2 := by
      field_simp; ring
    have e4 : (l * v ω + v' ω) ^ 2 / l = l * v ω ^ 2 + 2 * (v ω * v' ω) + l⁻¹ * v' ω ^ 2 := by
      field_simp; ring
    rw [abs_le]
    constructor <;> linarith
  have hG : Integrable (fun ω => ((a' / a) * v ω ^ 2 + (a / a') * v' ω ^ 2) / 2) P :=
    ((hv.const_mul _).add (hv'.const_mul _)).div_const 2
  have hi : Integrable (fun ω => v ω * v' ω) P :=
    hG.mono' (hm.mul hm') (Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs]; exact hpt ω)
  have := (abs_integral_le_integral_abs (μ := P) (f := fun ω => v ω * v' ω)).trans
    (integral_mono hi.abs hG hpt)
  refine this.trans ?_
  rw [integral_div, integral_add (hv.const_mul _) (hv'.const_mul _), integral_const_mul,
    integral_const_mul]
  have e1 : (a' / a) * (C * a ^ 2) = C * (a * a') := by field_simp
  have e2 : (a / a') * (C * a' ^ 2) = C * (a * a') := by field_simp
  have := mul_le_mul_of_nonneg_left h1 (div_pos ha' ha).le
  have := mul_le_mul_of_nonneg_left h2 (div_pos ha ha').le
  linarith

end RegularityStructures.Phi43

end

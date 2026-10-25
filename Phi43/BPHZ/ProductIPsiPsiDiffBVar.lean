/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiCovBound
public import Phi43.BPHZ.ProductIPsiPsiDiffKernel
public import Phi43.BPHZ.GammaMomentGradDiff
public import Phi43.BPHZ.GammaFullUniform
public import Phi43.BPHZ.ProductIPsiPsiDiffPairingArr
import Mathlib.Tactic

/-!
# Second moments of `v₁^ε - v₁^ε'` and the array `E[v_i(y) v_j(y')]`

* `hairerIPsiRecentred_sub_integral_sq_le`:
  `E (v₁ - v₁')² ≤ C m^(2θ) r^(3 - 2θ - δ)` for every `y` (`m = max ε ε'`, `r = ‖y - x‖`): the local
  bound of `gammaPsiTaylor_sub_second_moment_le` for `r ≤ 1/2` and the uniform bound
  `‖v₁ - v₁'‖_{L²} ≤ C m^θ (1 + r)` beyond;
* `ipsi_B_isArrR`: the array `(i, j) ↦ E[v_i(y) v_j(y')]` is in ratio form with base
  `C r^((3-δ)/2) r'^((3-δ)/2)` and ratio `min 1 (σ(r) + σ(r'))`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Second moment of the difference `v₁^ε - v₁^ε'`.** -/
theorem hairerIPsiRecentred_sub_integral_sq_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4)
    (hδ : 0 < δ) (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        Integrable (fun ω => (hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) ^ 2) P ∧
        ∫ ω, (hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * parabolicNorm (y - x) ^ (3 - 2 * θ - δ) := by
  obtain ⟨C1, hC1, h1⟩ := gammaPsiTaylor_sub_second_moment_le.{u} N hρ hρ' hθ (by linarith) hδ hθδ
  obtain ⟨C2, hC2, h2⟩ := gammaPsiTaylor_sub_lintegral_enorm_pow_le_uniform.{u} N hρ hρ' hθ hθ4
    (q := 2) (by norm_num)
  refine ⟨C1 + 18 * C2 ^ 2, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  set r := parabolicNorm (y - x) with hr
  set m := max ε ε' with hm
  have hr0 : 0 ≤ r := parabolicNorm_nonneg _
  have hm0 : 0 ≤ m := le_max_of_le_left hε.1.le
  have hmθ : 0 ≤ m ^ θ := Real.rpow_nonneg hm0 _
  have hmeas : Measurable (fun ω => hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) := by
    have a1 : Measurable (fun ω => hairerIPsiRecentred N ξ ω x y) :=
      Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ q.1 x q.2)
        (f := fun ω : Ω => (ω, y)) (measurable_hairerIPsiRecentred_prod_uncurry N hξ x)
        (measurable_id.prodMk measurable_const)
    have a2 : Measurable (fun ω => hairerIPsiRecentred N ξ' ω x y) :=
      Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ' q.1 x q.2)
        (f := fun ω : Ω => (ω, y)) (measurable_hairerIPsiRecentred_prod_uncurry N hξ' x)
        (measurable_id.prodMk measurable_const)
    exact a1.sub a2
  have hrr : ∀ i, |(y.2 - x.2) i| ≤ r := fun i => abs_coord_le_parabolicNorm (y - x) i
  have e : ∀ ω, hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y =
      gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
        gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω := fun ω => by
    rw [hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ.1 ω), hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ'.1 ω)]
  have hu := h2 hW hε hε' hξ hξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) r hr0 hrr
  have hc : 0 ≤ C2 * m ^ θ * (1 + r) := by positivity
  have hmeas' : AEStronglyMeasurable (fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
      gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω) P := by
    have : (fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
      gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω) =
        fun ω => hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y :=
      funext fun ω => (e ω).symm
    rw [this]; exact hmeas.aestronglyMeasurable
  have key := integrable_and_integral_pow_le_of_lintegral (k := 1) hmeas' hc (by simpa using hu)
  have hfun : ∀ ω, (hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y) ^ 2 =
      (gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
        gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω) ^ (2 * 1) := fun ω => by
    rw [e ω]; try ring
  simp_rw [hfun]
  refine ⟨key.1, ?_⟩
  by_cases hsm : r ≤ 1 / 2
  · have := h1 hW hε hε' hξ hξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) hsm
    rw [show parabolicNorm (y.1 - x.1, y.2 - x.2) = r from rfl] at this
    have e2 : ∀ ω, (gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
        gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω) ^ (2 * 1) =
        (gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
        gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω) ^ 2 := fun ω => by norm_num
    simp_rw [e2]
    refine this.trans ?_
    have hp0 : 0 ≤ m ^ (2 * θ) * r ^ (3 - 2 * θ - δ) :=
      mul_nonneg (Real.rpow_nonneg hm0 _) (Real.rpow_nonneg hr0 _)
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 18) (sq_nonneg C2)) hp0]
  · have hbig : 1 / 2 < r := lt_of_not_ge hsm
    refine key.2.trans ?_
    have hm2 : m ^ (2 * θ) = (m ^ θ) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hm0]; congr 1; push_cast; ring
    have hr3 : r ^ 2 ≤ 2 * r ^ (3 - 2 * θ - δ) := by
      have e3 : r ^ (3 - 2 * θ - δ) = r ^ (2 : ℕ) * r ^ (1 - 2 * θ - δ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add (by linarith)]; norm_num; ring_nf
      have hq : 1 / 2 ≤ r ^ (1 - 2 * θ - δ) := by
        have a1 : (1 / 2 : ℝ) ^ (1 : ℝ) ≤ (1 / 2 : ℝ) ^ (1 - 2 * θ - δ) :=
          Real.rpow_le_rpow_of_exponent_ge (by norm_num) (by norm_num) (by linarith)
        have a2 : (1 / 2 : ℝ) ^ (1 - 2 * θ - δ) ≤ r ^ (1 - 2 * θ - δ) :=
          Real.rpow_le_rpow (by norm_num) hbig.le (by linarith)
        simpa using a1.trans a2
      rw [e3]; nlinarith [sq_nonneg r]
    have : (C2 * m ^ θ * (1 + r)) ^ (2 * 1) ≤ 9 * C2 ^ 2 * (m ^ θ) ^ 2 * r ^ 2 := by
      have : 1 + r ≤ 3 * r := by linarith
      calc (C2 * m ^ θ * (1 + r)) ^ (2 * 1) = (C2 * m ^ θ) ^ 2 * (1 + r) ^ 2 := by ring
        _ ≤ (C2 * m ^ θ) ^ 2 * (3 * r) ^ 2 :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) this 2) (sq_nonneg _)
        _ = _ := by ring
    have hp0 : 0 ≤ (m ^ θ) ^ 2 * r ^ (3 - 2 * θ - δ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hr0 _)
    rw [hm2]
    nlinarith [mul_nonneg (sq_nonneg C2) hp0, mul_nonneg hC1 hp0, mul_nonneg (sq_nonneg C2) (sq_nonneg (m ^ θ))]

/-- Integrability of a product from integrable squares. -/
theorem integrable_mul_of_sq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {u v : Ω → ℝ}
    (hu : Integrable (fun ω => u ω ^ 2) P) (hv : Integrable (fun ω => v ω ^ 2) P)
    (hum : AEStronglyMeasurable u P) (hvm : AEStronglyMeasurable v P) :
    Integrable (fun ω => u ω * v ω) P := by
  have hpt : ∀ ω, |u ω * v ω| ≤ (u ω ^ 2 + v ω ^ 2) / 2 := fun ω => by
    rw [abs_le]
    constructor <;> linarith [sq_nonneg (u ω + v ω), sq_nonneg (u ω - v ω)]
  have hG : Integrable (fun ω => (u ω ^ 2 + v ω ^ 2) / 2) P := (hu.add hv).div_const 2
  exact hG.mono' (hum.mul hvm) (Filter.Eventually.of_forall fun ω => by
    rw [Real.norm_eq_abs]; exact hpt ω)

/-- Cauchy-Schwarz in the form used for the array `B`. -/
theorem ipsi_cs {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {u v : Ω → ℝ}
    (hu : Integrable (fun ω => u ω ^ 2) P) (hv : Integrable (fun ω => v ω ^ 2) P)
    (hum : AEStronglyMeasurable u P) (hvm : AEStronglyMeasurable v P) {K A B : ℝ} (hA : 0 < A)
    (hB : 0 < B) (h1 : ∫ ω, u ω ^ 2 ∂P ≤ K * A ^ 2) (h2 : ∫ ω, v ω ^ 2 ∂P ≤ K * B ^ 2) :
    |∫ ω, u ω * v ω ∂P| ≤ K * (A * B) :=
  abs_integral_mul_le_of_sq_le hu hv hum hvm hA hB h1 h2

/-- Abstract Cauchy-Schwarz estimates for the array `E[u_i w_j]`, `u_i = u₁ + [i = 0] (u₀ - u₁)`. -/
theorem ipsi_B_estimates {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {u0 u1 w0 w1 : Ω → ℝ}
    (iu0 : Integrable (fun ω => u0 ω ^ 2) P) (iu1 : Integrable (fun ω => u1 ω ^ 2) P)
    (iw0 : Integrable (fun ω => w0 ω ^ 2) P) (iw1 : Integrable (fun ω => w1 ω ^ 2) P)
    (iud : Integrable (fun ω => (u0 ω - u1 ω) ^ 2) P)
    (iwd : Integrable (fun ω => (w0 ω - w1 ω) ^ 2) P)
    (mu0 : AEStronglyMeasurable u0 P) (mu1 : AEStronglyMeasurable u1 P)
    (mw0 : AEStronglyMeasurable w0 P) (mw1 : AEStronglyMeasurable w1 P)
    {K A A' Bu Bw : ℝ} (hK : 0 ≤ K) (hA : 0 < A) (hA' : 0 < A') (hBu : 0 < Bu) (hBw : 0 < Bw)
    (m0 : ∫ ω, u0 ω ^ 2 ∂P ≤ K * A ^ 2) (m1 : ∫ ω, u1 ω ^ 2 ∂P ≤ K * A ^ 2)
    (md : ∫ ω, (u0 ω - u1 ω) ^ 2 ∂P ≤ K * Bu ^ 2)
    (n0 : ∫ ω, w0 ω ^ 2 ∂P ≤ K * A' ^ 2) (n1 : ∫ ω, w1 ω ^ 2 ∂P ≤ K * A' ^ 2)
    (nd : ∫ ω, (w0 ω - w1 ω) ^ 2 ∂P ≤ K * Bw ^ 2) :
    |∫ ω, u1 ω * w1 ω ∂P| ≤ K * (A * A') ∧
    (|(∫ ω, u0 ω * w1 ω ∂P) - ∫ ω, u1 ω * w1 ω ∂P| ≤ 2 * K * (A * A') ∧
      |(∫ ω, u0 ω * w1 ω ∂P) - ∫ ω, u1 ω * w1 ω ∂P| ≤ K * (Bu * A')) ∧
    (|(∫ ω, u1 ω * w0 ω ∂P) - ∫ ω, u1 ω * w1 ω ∂P| ≤ 2 * K * (A * A') ∧
      |(∫ ω, u1 ω * w0 ω ∂P) - ∫ ω, u1 ω * w1 ω ∂P| ≤ K * (A * Bw)) ∧
    (|(∫ ω, u0 ω * w0 ω ∂P) - (∫ ω, u0 ω * w1 ω ∂P) - (∫ ω, u1 ω * w0 ω ∂P) +
        ∫ ω, u1 ω * w1 ω ∂P| ≤ 4 * K * (A * A') ∧
      |(∫ ω, u0 ω * w0 ω ∂P) - (∫ ω, u0 ω * w1 ω ∂P) - (∫ ω, u1 ω * w0 ω ∂P) +
        ∫ ω, u1 ω * w1 ω ∂P| ≤ K * (Bu * Bw)) := by
  have mud : AEStronglyMeasurable (fun ω => u0 ω - u1 ω) P := mu0.sub mu1
  have mwd : AEStronglyMeasurable (fun ω => w0 ω - w1 ω) P := mw0.sub mw1
  have c11 := ipsi_cs iu1 iw1 mu1 mw1 hA hA' m1 n1
  have c01 := ipsi_cs iu0 iw1 mu0 mw1 hA hA' m0 n1
  have c10 := ipsi_cs iu1 iw0 mu1 mw0 hA hA' m1 n0
  have c00 := ipsi_cs iu0 iw0 mu0 mw0 hA hA' m0 n0
  have d01 := ipsi_cs iud iw1 mud mw1 hBu hA' md n1
  have d10 := ipsi_cs iu1 iwd mu1 mwd hA hBw m1 nd
  have d11 := ipsi_cs iud iwd mud mwd hBu hBw md nd
  have p00 := integrable_mul_of_sq iu0 iw0 mu0 mw0
  have p01 := integrable_mul_of_sq iu0 iw1 mu0 mw1
  have p10 := integrable_mul_of_sq iu1 iw0 mu1 mw0
  have p11 := integrable_mul_of_sq iu1 iw1 mu1 mw1
  have e01 : (∫ ω, u0 ω * w1 ω ∂P) - ∫ ω, u1 ω * w1 ω ∂P = ∫ ω, (u0 ω - u1 ω) * w1 ω ∂P := by
    rw [← integral_sub p01 p11]; congr 1; funext ω; ring
  have e10 : (∫ ω, u1 ω * w0 ω ∂P) - ∫ ω, u1 ω * w1 ω ∂P = ∫ ω, u1 ω * (w0 ω - w1 ω) ∂P := by
    rw [← integral_sub p10 p11]; congr 1; funext ω; ring
  have e11 : (∫ ω, u0 ω * w0 ω ∂P) - (∫ ω, u0 ω * w1 ω ∂P) - (∫ ω, u1 ω * w0 ω ∂P) +
      ∫ ω, u1 ω * w1 ω ∂P = ∫ ω, (u0 ω - u1 ω) * (w0 ω - w1 ω) ∂P := by
    have j1 : Integrable (fun ω => u0 ω * w0 ω - u0 ω * w1 ω) P := p00.sub p01
    have j2 : Integrable (fun ω => u0 ω * w0 ω - u0 ω * w1 ω - u1 ω * w0 ω) P := j1.sub p10
    rw [← integral_sub p00 p01, ← integral_sub j1 p10, ← integral_add j2 p11]
    congr 1; funext ω; ring
  have hAA : 0 ≤ K * (A * A') := mul_nonneg hK (mul_pos hA hA').le
  refine ⟨c11, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · refine (abs_sub _ _).trans ?_; linarith only [c01, c11]
  · rw [e01]; exact d01
  · refine (abs_sub _ _).trans ?_; linarith only [c10, c11]
  · rw [e10]; exact d10
  · have := abs_add_four_le (∫ ω, u0 ω * w0 ω ∂P) (-(∫ ω, u0 ω * w1 ω ∂P))
      (-(∫ ω, u1 ω * w0 ω ∂P)) (∫ ω, u1 ω * w1 ω ∂P)
    simp only [abs_neg] at this
    have e : (∫ ω, u0 ω * w0 ω ∂P) - (∫ ω, u0 ω * w1 ω ∂P) - (∫ ω, u1 ω * w0 ω ∂P) +
        ∫ ω, u1 ω * w1 ω ∂P = (∫ ω, u0 ω * w0 ω ∂P) + -(∫ ω, u0 ω * w1 ω ∂P) +
        -(∫ ω, u1 ω * w0 ω ∂P) + ∫ ω, u1 ω * w1 ω ∂P := by ring
    rw [e]; linarith only [this, c00, c01, c10, c11]
  · rw [e11]; exact d11

/-- The algebra: from the estimates to `IsArrR`. -/
theorem ipsi_B_alg {h : Fin 2 → Fin 2 → ℝ} {K b0 σ : ℝ} (hK : 0 ≤ K) (hb : 0 ≤ b0) (hσ : 0 ≤ σ)
    (h11 : |h 1 1| ≤ K * b0) (c1 : |h 0 1 - h 1 1| ≤ 2 * K * b0)
    (r1 : |h 0 1 - h 1 1| ≤ K * b0 * σ ^ 1) (c2 : |h 1 0 - h 1 1| ≤ 2 * K * b0)
    (r2 : |h 1 0 - h 1 1| ≤ K * b0 * σ ^ 1) (c3 : |arrSd h| ≤ 4 * K * b0)
    (r3 : |arrSd h| ≤ K * b0 * σ ^ 2) :
    IsArrR h (4 * K * b0) (min 1 σ) := by
  have cm : 0 ≤ min 1 σ := le_min zero_le_one hσ
  have cm1 : min 1 σ ≤ 1 := min_le_left _ _
  have hKb : 0 ≤ K * b0 := mul_nonneg hK hb
  have k1 := cap_le 1 hb hσ r1 c1
  have k2 := cap_le 1 hb hσ r2 c2
  have k3 := cap_le 2 hb hσ r3 c3
  have m1 : max K (2 * K) ≤ 4 * K := max_le (by linarith) (by linarith)
  have m3 : max K (4 * K) ≤ 4 * K := max_le (by linarith) le_rfl
  refine ⟨cm, cm1, ?_, ?_, ?_, ?_⟩
  · exact h11.trans (by linarith)
  · rw [pow_one] at k1
    exact k1.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right m1 hb) cm)
  · rw [pow_one] at k2
    exact k2.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right m1 hb) cm)
  · exact k3.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right m3 hb) (sq_nonneg _))

theorem ipsi_B_ratio {m θ α r r' K : ℝ} (hm0 : 0 < m) (hr : 0 < r) (hr' : 0 < r') (hK0 : 0 ≤ K) :
    K * ((m ^ θ * r ^ (α - θ)) * r' ^ α) ≤
      K * (r ^ α * r' ^ α) * (ipsiRatio m θ r + ipsiRatio m θ r') ^ 1 ∧
    K * (r ^ α * (m ^ θ * r' ^ (α - θ))) ≤
      K * (r ^ α * r' ^ α) * (ipsiRatio m θ r + ipsiRatio m θ r') ^ 1 ∧
    K * ((m ^ θ * r ^ (α - θ)) * (m ^ θ * r' ^ (α - θ))) ≤
      K * (r ^ α * r' ^ α) * (ipsiRatio m θ r + ipsiRatio m θ r') ^ 2 := by
  have hmθ : 0 < m ^ θ := Real.rpow_pos_of_pos hm0 _
  have hσr0 : 0 ≤ ipsiRatio m θ r := ipsiRatio_nonneg m θ r hm0.le hr.le
  have hσr0' : 0 ≤ ipsiRatio m θ r' := ipsiRatio_nonneg m θ r' hm0.le hr'.le
  have gain : ∀ {t : ℝ}, 0 < t → m ^ θ * t ^ (α - θ) ≤ t ^ α * ipsiRatio m θ t := fun {t} ht => by
    have : t ^ (α - θ) = t ^ α * t ^ (-θ) := by
      rw [← Real.rpow_add ht]; congr 1
    rw [this]; unfold ipsiRatio
    have h1 := Real.rpow_nonneg ht.le α
    have h2 := Real.rpow_nonneg ht.le (-θ)
    linarith [mul_nonneg h1 hmθ.le]
  have g1 := gain hr
  have g1' := gain hr'
  have hα0 : 0 ≤ r ^ α := Real.rpow_nonneg hr.le _
  have hα0' : 0 ≤ r' ^ α := Real.rpow_nonneg hr'.le _
  have hA' : 0 ≤ m ^ θ * r' ^ (α - θ) := mul_nonneg hmθ.le (Real.rpow_nonneg hr'.le _)
  have b0 : 0 ≤ r ^ α * r' ^ α := mul_nonneg hα0 hα0'
  set σr := ipsiRatio m θ r
  set σr' := ipsiRatio m θ r'
  refine ⟨?_, ?_, ?_⟩
  · rw [pow_one]
    have := mul_le_mul g1 le_rfl hα0' (mul_nonneg hα0 hσr0)
    refine le_trans (mul_le_mul_of_nonneg_left this hK0) ?_
    have : r ^ α * σr * r' ^ α ≤ r ^ α * r' ^ α * (σr + σr') := by
      linarith [mul_nonneg b0 hσr0']
    calc K * (r ^ α * σr * r' ^ α) ≤ K * (r ^ α * r' ^ α * (σr + σr')) :=
          mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  · rw [pow_one]
    refine le_trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left g1' hα0) hK0) ?_
    have : r ^ α * (r' ^ α * σr') ≤ r ^ α * r' ^ α * (σr + σr') := by
      linarith [mul_nonneg b0 hσr0]
    calc K * (r ^ α * (r' ^ α * σr')) ≤ K * (r ^ α * r' ^ α * (σr + σr')) :=
          mul_le_mul_of_nonneg_left this hK0
      _ = _ := by ring
  · have h1 := mul_le_mul g1 g1' hA' (mul_nonneg hα0 hσr0)
    refine le_trans (mul_le_mul_of_nonneg_left h1 hK0) ?_
    have : σr * σr' ≤ (σr + σr') ^ 2 := by
      linarith [mul_nonneg hσr0 hσr0', sq_nonneg σr, sq_nonneg σr']
    calc K * ((r ^ α * σr) * (r' ^ α * σr')) = K * (r ^ α * r' ^ α) * (σr * σr') := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left this (mul_nonneg hK0 b0)

/-- The three moment bounds, for the array `B`. -/
theorem ipsi_B_moments (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθδ : 2 * θ + δ ≤ 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ (x z : ParabolicSpace), 0 < parabolicNorm (z - x) →
        ∫ ω, hairerIPsiRecentred N ξ ω x z ^ 2 ∂P ≤ K * (parabolicNorm (z - x) ^ ((3 - δ) / 2)) ^ 2 ∧
        ∫ ω, hairerIPsiRecentred N ξ' ω x z ^ 2 ∂P ≤ K * (parabolicNorm (z - x) ^ ((3 - δ) / 2)) ^ 2 ∧
        ∫ ω, (hairerIPsiRecentred N ξ ω x z - hairerIPsiRecentred N ξ' ω x z) ^ 2 ∂P ≤
          K * ((max ε ε') ^ θ * parabolicNorm (z - x) ^ ((3 - δ) / 2 - θ)) ^ 2 := by
  obtain ⟨C0, hC0, h0⟩ := hairerIPsiRecentred_integral_sq_le.{u} N hρ hδ hδ1
  obtain ⟨C0', hC0', h0'⟩ := hairerIPsiRecentred_integral_sq_le.{u} N hρ' hδ hδ1
  obtain ⟨C1, hC1, h1⟩ := hairerIPsiRecentred_sub_integral_sq_le.{u} N hρ hρ' hθ hθ4 hδ hθδ
  refine ⟨C0 + C0' + C1, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x z hz
  have hm0 : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have rpw : ∀ {t : ℝ}, 0 < t → ∀ {a : ℝ}, (t ^ a) ^ 2 = t ^ (2 * a) := fun {t} ht {a} => by
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]; congr 1; push_cast; ring
  have hp := Real.rpow_nonneg hz.le (3 - δ)
  have e1 : (parabolicNorm (z - x) ^ ((3 - δ) / 2)) ^ 2 = parabolicNorm (z - x) ^ (3 - δ) := by
    rw [rpw hz, show 2 * ((3 - δ) / 2) = 3 - δ by ring]
  refine ⟨?_, ?_, ?_⟩
  · rw [e1]
    have := h0 hW hε hξ x z
    linarith [mul_nonneg hC0' hp, mul_nonneg hC1 hp]
  · rw [e1]
    have := h0' hW hε' hξ' x z
    linarith [mul_nonneg hC0 hp, mul_nonneg hC1 hp]
  · rw [mul_pow, rpw hm0 (a := θ), rpw hz (a := (3 - δ) / 2 - θ),
      show 2 * ((3 - δ) / 2 - θ) = 3 - 2 * θ - δ by ring]
    have := (h1 hW hε hε' hξ hξ' x z).2
    have hp2 : 0 ≤ (max ε ε') ^ (2 * θ) * parabolicNorm (z - x) ^ (3 - 2 * θ - δ) :=
      mul_nonneg (Real.rpow_nonneg hm0.le _) (Real.rpow_nonneg hz.le _)
    linarith [mul_nonneg hC0 hp2, mul_nonneg hC0' hp2]

/-- **The array `E[v_i(y) v_j(y')]` in ratio form.** -/
theorem ipsi_B_isArrR (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ δ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : ParabolicSpace, 0 < parabolicNorm (y - x) → 0 < parabolicNorm (y' - x) →
        IsArrR (fun i j => ∫ ω, hairerIPsiRecentred N (![ξ, ξ'] i) ω x y *
            hairerIPsiRecentred N (![ξ, ξ'] j) ω x y' ∂P)
          (C * (parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2)))
          (min 1 (ipsiRatio (max ε ε') θ (parabolicNorm (y - x)) +
            ipsiRatio (max ε ε') θ (parabolicNorm (y' - x)))) := by
  obtain ⟨K, hK0, hmo⟩ := ipsi_B_moments.{u} N hρ hρ' hθ hθ4 hδ hδ1 hθδ
  obtain ⟨Ci, hCi, hi⟩ := hairerIPsiRecentred_pow_le.{u} N hρ (k := 1) (by norm_num)
  obtain ⟨Ci', hCi', hi'⟩ := hairerIPsiRecentred_pow_le.{u} N hρ' (k := 1) (by norm_num)
  obtain ⟨C1, hC1, h1⟩ := hairerIPsiRecentred_sub_integral_sq_le.{u} N hρ hρ' hθ hθ4 hδ hθδ
  refine ⟨4 * K, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hr hr'
  have := hW.isProbabilityMeasure
  have hm0 : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hmθ : 0 < (max ε ε') ^ θ := Real.rpow_pos_of_pos hm0 _
  have mu : ∀ (ξ₀ : Ω → SpaceTime → ℝ) (ρ₀ : ℝ × (Fin 3 → ℝ) → ℝ) (ε₀ : ℝ) (z : ParabolicSpace),
      IsRegularisedNoise P W ρ₀ ε₀ ξ₀ →
      AEStronglyMeasurable (fun ω => hairerIPsiRecentred N ξ₀ ω x z) P := fun ξ₀ ρ₀ ε₀ z hξ₀ =>
    (Measurable.comp (g := fun q : Ω × ParabolicSpace => hairerIPsiRecentred N ξ₀ q.1 x q.2)
      (f := fun ω : Ω => (ω, z)) (measurable_hairerIPsiRecentred_prod_uncurry N hξ₀ x)
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have s0 : ∀ z, Integrable (fun ω => hairerIPsiRecentred N ξ ω x z ^ 2) P := fun z => by
    simpa using (hi hW hε hξ x z).1
  have s1 : ∀ z, Integrable (fun ω => hairerIPsiRecentred N ξ' ω x z ^ 2) P := fun z => by
    simpa using (hi' hW hε' hξ' x z).1
  have hα0 : 0 < parabolicNorm (y - x) ^ ((3 - δ) / 2) := Real.rpow_pos_of_pos hr _
  have hα0' : 0 < parabolicNorm (y' - x) ^ ((3 - δ) / 2) := Real.rpow_pos_of_pos hr' _
  have hA : 0 < (max ε ε') ^ θ * parabolicNorm (y - x) ^ ((3 - δ) / 2 - θ) :=
    mul_pos hmθ (Real.rpow_pos_of_pos hr _)
  have hA' : 0 < (max ε ε') ^ θ * parabolicNorm (y' - x) ^ ((3 - δ) / 2 - θ) :=
    mul_pos hmθ (Real.rpow_pos_of_pos hr' _)
  obtain ⟨my0, my1, myd⟩ := hmo hW hε hε' hξ hξ' x y hr
  obtain ⟨mz0, mz1, mzd⟩ := hmo hW hε hε' hξ hξ' x y' hr'
  have est := ipsi_B_estimates (s0 y) (s1 y) (s0 y') (s1 y') (h1 hW hε hε' hξ hξ' x y).1
    (h1 hW hε hε' hξ hξ' x y').1 (mu ξ ρ ε y hξ) (mu ξ' ρ' ε' y hξ') (mu ξ ρ ε y' hξ)
    (mu ξ' ρ' ε' y' hξ') hK0 hα0 hα0' hA hA' my0 my1 myd mz0 mz1 mzd
  obtain ⟨e11, ⟨c1, r1⟩, ⟨c2, r2⟩, ⟨c3, r3⟩⟩ := est
  obtain ⟨f1, f1', f2⟩ := ipsi_B_ratio (α := (3 - δ) / 2) (θ := θ) hm0 hr hr' hK0
  have hσ0 : 0 ≤ ipsiRatio (max ε ε') θ (parabolicNorm (y - x)) +
      ipsiRatio (max ε ε') θ (parabolicNorm (y' - x)) :=
    add_nonneg (ipsiRatio_nonneg _ θ _ hm0.le hr.le) (ipsiRatio_nonneg _ θ _ hm0.le hr'.le)
  have b0 : 0 ≤ parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2) :=
    mul_nonneg hα0.le hα0'.le
  exact ipsi_B_alg (h := fun i j => ∫ ω, hairerIPsiRecentred N (![ξ, ξ'] i) ω x y *
      hairerIPsiRecentred N (![ξ, ξ'] j) ω x y' ∂P) hK0 b0 hσ0 e11 (by simpa using c1)
    (by simpa using r1.trans f1) (by simpa using c2) (by simpa using r2.trans f1')
    (by unfold arrSd; simpa using c3) (by unfold arrSd; simpa using r3.trans f2)

end RegularityStructures.Phi43

end

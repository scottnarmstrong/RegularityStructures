/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossMean
public import Phi43.BPHZ.TreeI2Psi2CrossDiffCov
public import Phi43.BPHZ.TreeI2Psi2DifferenceBound

/-!
# The pointwise covariance bound for the cross-mollifier difference of `I(Ψ²) Ψ²`

`hairerI2Psi2Field_sub_cov_bound_cross`: for `θ ∈ (0, 1/8]`, `δ ∈ (0, 1/4]`, scales
`ε, ε' ∈ (0, 1]`, a base point `x` and points `y, y'` with `s(y - x), s(y' - x) ≤ 1` and `y, y', x`
distinct,
`|E[(F_{ρ,ε} - F_{ρ',ε'})(y) (F_{ρ,ε} - F_{ρ',ε'})(y')]| ≤ C (max ε ε')^(2θ) F(r, r', d)`,
with `r = s(y - x)`, `r' = s(y' - x)`, `d = s(y - y')` and `F = i2Psi2DiffF θ δ r r' d`.  The
constant is independent of the scales, the points, the probability space and the noises.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

/-- **Pointwise covariance bound for the difference `F_ε - F_ε'` of `I(Ψ²) Ψ²`**, with the full
gain `(max ε ε')^(2θ)`. -/
theorem hairerI2Psi2Field_sub_cov_bound_cross (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') → torusParabolicSize (y - x) ≤ 1 →
        torusParabolicSize (y' - x) ≤ 1 →
          |∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) *
              (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y') ∂P| ≤
            C * (max ε ε') ^ (2 * θ) * i2Psi2DiffF θ δ (torusParabolicSize (y - x))
              (torusParabolicSize (y' - x)) (torusParabolicSize (y - y')) := by
  have hθ1' : θ ≤ 1 := by linarith
  obtain ⟨B, hB, hK⟩ := i2Psi2KernelHyp_hairerKernelTorus N
  obtain ⟨K4, hK4, h4⟩ := abs_i2Psi2DiffChaos4Two_le N ρ ρ' hρ hρ' hθ hθ1'
  obtain ⟨K2, hK2, h2⟩ := abs_i2Psi2DiffChaos2Two_le N ρ ρ' hρ hρ' hθ hθ1'
  obtain ⟨C4, hC4, I4⟩ := integrable_and_abs_integral_diff_chaos4_le hθ hθ1 hδ hδ1
  obtain ⟨C2, hC2, I2⟩ := integrable_and_abs_integral_diff_chaos2_le hθ hθ1 hδ hδ1
  obtain ⟨Cm, hCm, hm⟩ := abs_i2Psi2Mean_sub_le_cross.{u} N hρ hρ' hθ hθ1'
  refine ⟨K4 * C4 * B ^ 2 + K2 * C2 * B ^ 2 + Cm ^ 2, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hr hr' hd hr1 hr1'
  have hcfg : i2Psi2PointCfg x y y' := ⟨hr, hr1, hr', hr1', hd⟩
  rw [(hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y').2,
    hairerI2Psi2Cov_sub_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y']
  have hmax : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hμ2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hmax.le _
  have hFn := i2Psi2DiffF_nonneg (θ := θ) (δ := δ) hr hr' hd
  set F := i2Psi2DiffF θ δ (torusParabolicSize (y - x)) (torusParabolicSize (y' - x))
    (torusParabolicSize (y - y')) with hF
  -- measurability from integrability of the four pieces
  obtain ⟨a4, a2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ hρ hε.1 hε.1 hW hξ hξ x y y'
  obtain ⟨b4, b2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y'
  obtain ⟨c4, c2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ' hρ hε'.1 hε.1 hW hξ' hξ x y y'
  obtain ⟨d4, d2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ' hρ' hε'.1 hε'.1 hW hξ' hξ' x y y'
  have m4 : AEStronglyMeasurable (fun q : SpaceTime × SpaceTime =>
      hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos4Two N ρ ρ' ε ε' y y' q.1 q.2) volume := by
    have := (((a4.aestronglyMeasurable.sub b4.aestronglyMeasurable).sub
      c4.aestronglyMeasurable).add d4.aestronglyMeasurable)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [i2Psi2DiffChaos4Two, Pi.add_apply, Pi.sub_apply]
    ring
  have m2 : AEStronglyMeasurable (fun q : SpaceTime × SpaceTime =>
      hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos2Two N ρ ρ' ε ε' y y' q.1 q.2) volume := by
    have := (((a2.aestronglyMeasurable.sub b2.aestronglyMeasurable).sub
      c2.aestronglyMeasurable).add d2.aestronglyMeasurable)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [i2Psi2DiffChaos2Two, Pi.add_apply, Pi.sub_apply]
    ring
  have hae := ae_prod_pos_i2Psi2_diff y y'
  -- the chaos-4 part
  have e4 := I4 hK (c := K4 * (max ε ε') ^ (2 * θ)) (mul_nonneg hK4 hμ2) m4 x y y' hcfg (by
    filter_upwards [hae] with q hq
    obtain ⟨p02, p03, p12, p13, p23⟩ := hq
    have := h4 hε.1 hε.2 hε'.1 hε'.2 x y y' q.1 q.2 p02 p03 p12 hd
    exact this)
  -- the chaos-2 part
  have e2 := I2 hK (c := K2 * (max ε ε') ^ (2 * θ)) (mul_nonneg hK2 hμ2) m2 x y y' hcfg (by
    filter_upwards [hae] with q hq
    obtain ⟨p02, p03, p12, p01, p23⟩ := hq
    have := h2 hε.1 hε.2 hε'.1 hε'.2 x y y' q.1 q.2 p01 p23 p02 p03 p12 hd
    exact this)
  -- the chaos-0 part
  have mm1 := hm hW hε.1 hε.2 hε'.1 hε'.2 hξ hξ' x y hr
  have mm2 := hm hW hε.1 hε.2 hε'.1 hε'.2 hξ hξ' x y' hr'
  have hM : |(i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y) *
      (i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y')| ≤ Cm ^ 2 * (max ε ε') ^ (2 * θ) * F := by
    rw [abs_mul]
    have hμθ : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg hmax.le _
    have n1 : 0 ≤ torusParabolicSize (y - x) ^ (-θ) := Real.rpow_nonneg hr.le _
    have n2 : 0 ≤ torusParabolicSize (y' - x) ^ (-θ) := Real.rpow_nonneg hr'.le _
    have p := mul_le_mul mm1 mm2 (abs_nonneg _) (by positivity)
    have amgm := rpow_mul_rpow_le_add_two hr hr' (g := -θ)
    have g1 : torusParabolicSize (y - x) ^ (2 * -θ) ≤ torusParabolicSize (y - x) ^ (-(2 * θ + δ)) :=
      Real.rpow_le_rpow_of_exponent_ge hr hr1 (by linarith)
    have g2 : torusParabolicSize (y' - x) ^ (2 * -θ) ≤
        torusParabolicSize (y' - x) ^ (-(2 * θ + δ)) :=
      Real.rpow_le_rpow_of_exponent_ge hr' hr1' (by linarith)
    have hF4 := i2Psi2DiffF_ge_four (θ := θ) (δ := δ) hr hr' hd
    have e : (max ε ε') ^ (2 * θ) = (max ε ε') ^ θ * (max ε ε') ^ θ := by
      rw [← Real.rpow_add hmax]; congr 1; ring
    have hq : torusParabolicSize (y - x) ^ (-θ) * torusParabolicSize (y' - x) ^ (-θ) ≤ F := by
      linarith
    calc |i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y| *
          |i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y'|
        ≤ Cm * (max ε ε') ^ θ * torusParabolicSize (y - x) ^ (-θ) *
          (Cm * (max ε ε') ^ θ * torusParabolicSize (y' - x) ^ (-θ)) := p
      _ = Cm ^ 2 * (max ε ε') ^ (2 * θ) *
          (torusParabolicSize (y - x) ^ (-θ) * torusParabolicSize (y' - x) ^ (-θ)) := by
        rw [e]; ring
      _ ≤ Cm ^ 2 * (max ε ε') ^ (2 * θ) * F :=
        mul_le_mul_of_nonneg_left hq (by positivity)
  have t3 := abs_add_three
    (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos4Two N ρ ρ' ε ε' y y' q.1 q.2)
    (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos2Two N ρ ρ' ε ε' y y' q.1 q.2)
    ((i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y) *
        (i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y'))
  have b4 := e4.2
  have b2 := e2.2
  calc _ ≤ _ := t3
    _ ≤ K4 * (max ε ε') ^ (2 * θ) * (C4 * B ^ 2 * F) + K2 * (max ε ε') ^ (2 * θ) * (C2 * B ^ 2 * F) +
        Cm ^ 2 * (max ε ε') ^ (2 * θ) * F := by linarith
    _ = _ := by ring

end RegularityStructures.Phi43

end

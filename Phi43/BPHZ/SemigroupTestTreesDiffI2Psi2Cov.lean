/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesDiffI2Psi2Maj2
public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Field
public import Phi43.BPHZ.TreeI2Psi2CrossBound

/-!
# The global covariance bound for the cross-mollifier difference of `I(Ψ²) Ψ²`

`hairerI2Psi2Field_sub_cov_bound_cross_global`: for `θ ∈ (0, 1/8]`, mollifiers `ρ, ρ'`, scales
`ε, ε' ∈ (0, 1]` and arbitrary `x, y, y'` with `y, y' ≠ x`, `y ≠ y'`,
`|E[(F_{ρ,ε} - F_{ρ',ε'})(y) (F_{ρ,ε} - F_{ρ',ε'})(y')]| ≤ C (max ε ε')^(2θ)
  (1 + s(y - x)² + s(y' - x)²)³ (s(y - y')^(-(2+2θ)) + s(y - x)^(-1) + s(y' - x)^(-1) + 1)`.
There is no restriction `s(y - x), s(y' - x) ≤ 1`.  The proof is that of the local bound
(`hairerI2Psi2Field_sub_cov_bound_cross`), with the diagram integrals replaced by the global ones
(`i2Psi2Diff_maj4_global`, `i2Psi2Diff_maj2_global`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem combine_alg {K4 K2 C4 C2 Cm B μ F τ Sg Pp S md : ℝ} (hK4 : 0 ≤ K4) (hK2 : 0 ≤ K2)
    (hC4 : 0 ≤ C4) (hC2 : 0 ≤ C2) (hμ : 0 ≤ μ) (hF : 0 ≤ F) (hτ : 0 ≤ τ)
    (hSg : 0 ≤ Sg) (hFτ : F * τ ≤ 125 * Pp) (hSgS : Sg ≤ 2 * S) (hPp : 1 ≤ Pp) (hS : 0 ≤ S)
    (hmd : md ≤ Cm ^ 2 * μ * (2 * S)) :
    K4 * μ * (C4 * B ^ 2 * F * τ * Sg) + K2 * μ * (C2 * B ^ 2 * F * τ * Sg) + md ≤
      (250 * K4 * C4 * B ^ 2 + 250 * K2 * C2 * B ^ 2 + 2 * Cm ^ 2) * μ * Pp * S := by
  have hFτ0 : 0 ≤ F * τ := mul_nonneg hF hτ
  have h1 : F * τ * Sg ≤ (125 * Pp) * (2 * S) := mul_le_mul hFτ hSgS hSg (by linarith)
  have e4 : K4 * μ * (C4 * B ^ 2 * F * τ * Sg) = (K4 * μ * C4 * B ^ 2) * (F * τ * Sg) := by ring
  have e2 : K2 * μ * (C2 * B ^ 2 * F * τ * Sg) = (K2 * μ * C2 * B ^ 2) * (F * τ * Sg) := by ring
  have c4 : 0 ≤ K4 * μ * C4 * B ^ 2 := by positivity
  have c2 : 0 ≤ K2 * μ * C2 * B ^ 2 := by positivity
  have b4 := mul_le_mul_of_nonneg_left h1 c4
  have b2 := mul_le_mul_of_nonneg_left h1 c2
  have hm : Cm ^ 2 * μ * (2 * S) ≤ 2 * Cm ^ 2 * μ * Pp * S := by
    have : 0 ≤ Cm ^ 2 * μ * S := by positivity
    nlinarith
  rw [e4, e2]
  nlinarith [b4, b2, hm, hmd]


/-- **Global covariance bound for the cross-mollifier difference of `I(Ψ²) Ψ²`.** -/
theorem hairerI2Psi2Field_sub_cov_bound_cross_global (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1 / 8) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - x) → 0 < torusParabolicSize (y' - x) →
        0 < torusParabolicSize (y - y') →
          |∫ ω, (hairerI2Psi2Field N ρ ε ξ x ω y - hairerI2Psi2Field N ρ' ε' ξ' x ω y) *
              (hairerI2Psi2Field N ρ ε ξ x ω y' - hairerI2Psi2Field N ρ' ε' ξ' x ω y') ∂P| ≤
            C * (max ε ε') ^ (2 * θ) *
              (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3 *
              (torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) + torusParabolicSize (y - x) ^ (-(1 : ℝ)) +
                torusParabolicSize (y' - x) ^ (-(1 : ℝ)) + 1) := by
  have hθ1' : θ ≤ 1 := by linarith
  obtain ⟨CK, hCK, hKb⟩ := constantsComparison_hairerKernelTorus_uniform_singular_bound_unconditional N
  have hdata : SingularKernelData (hairerKernelTorus N) (fun _ => (0 : ℝ)) CK :=
    { nonneg := hCK
      measurable_K := measurable_constantsComparison_hairerKernelTorus N
      measurable_Q := measurable_const
      K_bound := fun z hz => hKb hz
      K_supp := fun z hz => hairerKernelTorus_eq_zero_of_one_lt_time N hz
      Q_bound := fun z _ => by
        rw [abs_zero]
        exact mul_nonneg hCK (Real.rpow_nonneg (torusParabolicSize_nonneg _) _) }
  obtain ⟨K4, hK4, h4⟩ := abs_i2Psi2DiffChaos4Two_le N ρ ρ' hρ hρ' hθ hθ1'
  obtain ⟨K2, hK2, h2⟩ := abs_i2Psi2DiffChaos2Two_le N ρ ρ' hρ hρ' hθ hθ1'
  obtain ⟨C4, hC4, m4⟩ := i2Psi2Diff_maj4_global hθ hθ1
  obtain ⟨C2, hC2, m2⟩ := i2Psi2Diff_maj2_global hθ hθ1
  obtain ⟨Cm, hCm, hm⟩ := abs_i2Psi2Mean_sub_le_cross.{u} N hρ hρ' hθ hθ1'
  refine ⟨250 * K4 * C4 * CK ^ 2 + 250 * K2 * C2 * CK ^ 2 + 2 * Cm ^ 2, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hr hr' hd
  rw [(hairerI2Psi2Field_sub_integral_mul_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y').2,
    hairerI2Psi2Cov_sub_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y']
  have hxy : 0 < torusParabolicSize (x - y) := torusParabolicSize_sub_pos_symm hr
  have hxy' : 0 < torusParabolicSize (x - y') := torusParabolicSize_sub_pos_symm hr'
  have hmax : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hμ2 : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hmax.le _
  set μ2 : ℝ := (max ε ε') ^ (2 * θ) with hμ2def
  -- measurability from integrability of the four pieces
  obtain ⟨a4, a2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ hρ hε.1 hε.1 hW hξ hξ x y y'
  obtain ⟨b4, b2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y'
  obtain ⟨c4, c2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ' hρ hε'.1 hε.1 hW hξ' hξ x y y'
  obtain ⟨d4, d2⟩ := integrable_hairerI2Psi2_chaos_two_mollifier N hρ' hρ' hε'.1 hε'.1 hW hξ' hξ' x y y'
  have mm4 : AEStronglyMeasurable (fun q : SpaceTime × SpaceTime =>
      hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos4Two N ρ ρ' ε ε' y y' q.1 q.2) volume := by
    have := (((a4.aestronglyMeasurable.sub b4.aestronglyMeasurable).sub
      c4.aestronglyMeasurable).add d4.aestronglyMeasurable)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [i2Psi2DiffChaos4Two, Pi.add_apply, Pi.sub_apply]
    ring
  have mm2 : AEStronglyMeasurable (fun q : SpaceTime × SpaceTime =>
      hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos2Two N ρ ρ' ε ε' y y' q.1 q.2) volume := by
    have := (((a2.aestronglyMeasurable.sub b2.aestronglyMeasurable).sub
      c2.aestronglyMeasurable).add d2.aestronglyMeasurable)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [i2Psi2DiffChaos2Two, Pi.add_apply, Pi.sub_apply]
    ring
  have hae := ae_prod_pos_i2Psi2_diff y y'
  -- the slab
  set t : ℝ := |y.1 - x.1| with ht
  set t' : ℝ := |y'.1 - x.1| with ht'
  have ht0 : 0 ≤ t := abs_nonneg _
  have ht0' : 0 ≤ t' := abs_nonneg _
  have hslab : I2Psi2DiffSlab x y y' (√(2 * (t + t' + 2)) + 1) := by
    intro a b ha hb
    refine torusParabolicSize_le_sqrt_add_one ?_
    have : (a - b).1 = a.1 - b.1 := rfl
    rw [this]
    have h1 : |a.1 - b.1| ≤ |a.1 - x.1| + |b.1 - x.1| := by
      calc |a.1 - b.1| = |(a.1 - x.1) - (b.1 - x.1)| := by ring_nf
        _ ≤ _ := abs_sub _ _
    linarith
  have hD0 : 0 ≤ √(2 * (t + t' + 2)) + 1 := by positivity
  set D : ℝ := √(2 * (t + t' + 2)) + 1 with hD
  have i4 := (m4 hdata x y y' hD0 hslab hd hxy hxy')
  have i2 := (m2 hdata x y y' hD0 hslab hd hxy hxy')
  have e4 := i4.abs_integral_le (mul_nonneg hK4 hμ2) mm4 (by
    filter_upwards [hae] with q hq
    obtain ⟨p02, p03, p12, p13, p23⟩ := hq
    exact h4 hε.1 hε.2 hε'.1 hε'.2 x y y' q.1 q.2 p02 p03 p12 hd)
  have e2 := i2.abs_integral_le (mul_nonneg hK2 hμ2) mm2 (by
    filter_upwards [hae] with q hq
    obtain ⟨p02, p03, p12, p01, p23⟩ := hq
    exact h2 hε.1 hε.2 hε'.1 hε'.2 x y y' q.1 q.2 p01 p23 p02 p03 p12 hd)
  -- the chaos-0 part
  have mm1 := hm hW hε.1 hε.2 hε'.1 hε'.2 hξ hξ' x y hr
  have mm1' := hm hW hε.1 hε.2 hε'.1 hε'.2 hξ hξ' x y' hr'
  have hμθ : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg hmax.le _
  have e : μ2 = (max ε ε') ^ θ * (max ε ε') ^ θ := by
    rw [hμ2def, ← Real.rpow_add hmax]; congr 1; ring
  have nS : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set S : ℝ := torusParabolicSize (y - y') ^ (-(2 + 2 * θ)) + torusParabolicSize (y - x) ^ (-(1 : ℝ)) +
    torusParabolicSize (y' - x) ^ (-(1 : ℝ)) + 1 with hS
  have hS1 : 1 ≤ S := by
    have := nS (y - y') (-(2 + 2 * θ))
    have := nS (y - x) (-(1 : ℝ))
    have := nS (y' - x) (-(1 : ℝ))
    linarith
  have hmd : |(i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y) *
      (i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y')| ≤ Cm ^ 2 * μ2 * (2 * S) := by
    rw [abs_mul]
    have p := mul_le_mul mm1 mm1' (abs_nonneg _) (by positivity)
    have amgm := rpow_mul_rpow_le_add_two hr hr' (g := -θ)
    have k1 : torusParabolicSize (y - x) ^ (2 * -θ) ≤ torusParabolicSize (y - x) ^ (-(1 : ℝ)) + 1 := by
      have := i2Psi2Diff_rpow_neg_le hr (e := 2 * θ) (f := 1) (by linarith) (by linarith)
      have e2θ : (2 * -θ) = -(2 * θ) := by ring
      rw [e2θ]; exact this
    have k2 : torusParabolicSize (y' - x) ^ (2 * -θ) ≤
        torusParabolicSize (y' - x) ^ (-(1 : ℝ)) + 1 := by
      have := i2Psi2Diff_rpow_neg_le hr' (e := 2 * θ) (f := 1) (by linarith) (by linarith)
      have e2θ : (2 * -θ) = -(2 * θ) := by ring
      rw [e2θ]; exact this
    have hdd := nS (y - y') (-(2 + 2 * θ))
    calc |i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y| *
          |i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y'|
        ≤ Cm * (max ε ε') ^ θ * torusParabolicSize (y - x) ^ (-θ) *
          (Cm * (max ε ε') ^ θ * torusParabolicSize (y' - x) ^ (-θ)) := p
      _ = Cm ^ 2 * μ2 * (torusParabolicSize (y - x) ^ (-θ) * torusParabolicSize (y' - x) ^ (-θ)) := by
        rw [e]; ring
      _ ≤ Cm ^ 2 * μ2 * (2 * S) := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [hS]
        linarith
  have t3 := abs_add_three
    (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos4Two N ρ ρ' ε ε' y y' q.1 q.2)
    (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        i2Psi2DiffChaos2Two N ρ ρ' ε ε' y y' q.1 q.2)
    ((i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y) *
        (i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y'))
  -- the polynomial prefactor and the singular sums
  have f1 : torusParabolicSize (x - y) ^ (-(1 : ℝ)) ≤ 2 * torusParabolicSize (y - x) ^ (-(1 : ℝ)) :=
    torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := 1) (by norm_num) le_rfl hr
  have f2 : torusParabolicSize (x - y') ^ (-(1 : ℝ)) ≤
      2 * torusParabolicSize (y' - x) ^ (-(1 : ℝ)) :=
    torusParabolicSize_sub_rpow_neg_le (a := x) (b := y') (e := 1) (by norm_num) le_rfl hr'
  have hSg : i2Psi2DiffSg θ x y y' ≤ 2 * S := by
    simp only [i2Psi2DiffSg, hS]
    have := nS (y - y') (-(2 + 2 * θ))
    have := nS (y - x) (-(1 : ℝ))
    have := nS (y' - x) (-(1 : ℝ))
    linarith
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have e2' := abs_fst_le_sq_torusParabolicSize (y' - x)
  have hpoly := poly_prefactor_le ht0 ht0' (a := torusParabolicSize (y - x) ^ 2)
    (b := torusParabolicSize (y' - x) ^ 2) e1 e2'
  have hFτ : (1 + D) ^ 2 * (1 + t) ≤
      125 * (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3 := by
    refine le_trans (mul_le_mul_of_nonneg_left (by linarith) (by positivity)) hpoly
  have hPp : 1 ≤ (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3 := by
    have : 1 ≤ 1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2 := by
      have := sq_nonneg (torusParabolicSize (y - x))
      have := sq_nonneg (torusParabolicSize (y' - x))
      linarith
    exact one_le_pow₀ this
  have hfin := combine_alg (K4 := K4) (K2 := K2) (C4 := C4) (C2 := C2) (Cm := Cm) (B := CK) (μ := μ2)
    (F := (1 + D) ^ 2) (τ := 1 + t) (Sg := i2Psi2DiffSg θ x y y') (S := S)
    (Pp := (1 + torusParabolicSize (y - x) ^ 2 + torusParabolicSize (y' - x) ^ 2) ^ 3)
    (md := |(i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y) *
      (i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y')|) hK4 hK2 hC4 hC2 hμ2 (by positivity)
    (by linarith) (i2Psi2DiffSg_nonneg θ x y y') hFτ hSg hPp (by linarith) hmd
  calc _ ≤ _ := t3
    _ ≤ K4 * μ2 * (C4 * CK ^ 2 * (1 + D) ^ 2 * (1 + t) * i2Psi2DiffSg θ x y y') +
        K2 * μ2 * (C2 * CK ^ 2 * (1 + D) ^ 2 * (1 + t) * i2Psi2DiffSg θ x y y') +
        |(i2Psi2Mean N ρ x ε y - i2Psi2Mean N ρ' x ε' y) *
          (i2Psi2Mean N ρ x ε y' - i2Psi2Mean N ρ' x ε' y')| := by
        have b4 := e4.2
        have b2 := e2.2
        have : K4 * μ2 = K4 * μ2 := rfl
        rw [mul_comm K4 μ2, mul_comm K2 μ2] at *
        linarith
    _ ≤ _ := hfin

end RegularityStructures.Phi43

end

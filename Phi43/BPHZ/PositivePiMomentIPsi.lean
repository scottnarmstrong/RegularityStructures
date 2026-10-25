/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentNearFar
public import Phi43.BPHZ.PositivePiMomentLinear
public import Phi43.BPHZ.GammaMomentGradDiffLq
public import Phi43.BPHZ.GammaMomentGradBridgeIncrements
import Mathlib.Tactic

/-!
# `q`-th moments of the recentred convolution `hairerIPsiRecentred` at all distances

`R(x, y) = (K * Ψ)(y) - (K * Ψ)(x) - ∑ᵢ ∂ᵢ(K * Ψ)(x) (y - x)ᵢ` satisfies the cocycle relation
`R(x, y) = R(x, z) + R(z, y) + ∑ᵢ γᵢ(x, z) (y - z)ᵢ` with `γᵢ(x, y) = ∂ᵢ(K * Ψ)(y) - ∂ᵢ(K * Ψ)(x)`.
The local bounds of `v₁` and `gᵢ` (`GammaMomentGradLq`, `GammaMomentGradDiffLq`) therefore give, by
`lintegral_enorm_nearFar_pow_le`, `∫⁻ ‖R(x, y)‖ₑ^q ≤ ofReal (C (d^s + d^4))^q`, `d = ‖y - x‖_𝔰`,
`s = 3/2 - κ + κ̄`, for all `x, y`, and the same for the two-scale difference with the factor
`(ε ∨ ε')^θ`.
-/

@[expose] public noncomputable section

namespace RegularityStructures.Phi43

open RegularityStructures

/-- The spatial gradient increment `γᵢ(x, y) = ∂ᵢ(K * Ψ)(y) - ∂ᵢ(K * Ψ)(x)` as a random variable. -/
def iPsiGradIncr {Ω : Type*} (N : ℕ) (ξ : Ω → SpaceTime → ℝ) (i : Fin 3) (x y : ParabolicSpace)
    (ω : Ω) : ℝ :=
  hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i y -
    hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x


end RegularityStructures.Phi43

end

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

section Algebra

variable {Ω : Type*} {ξ : Ω → SpaceTime → ℝ} (N : ℕ)

theorem iPsiGradIncr_add (i : Fin 3) (x z y : ParabolicSpace) (ω : Ω) :
    iPsiGradIncr N ξ i x y ω = iPsiGradIncr N ξ i x z ω + iPsiGradIncr N ξ i z y ω := by
  unfold iPsiGradIncr
  ring

theorem hairerIPsiRecentred_cocycle (x z y : ParabolicSpace) (ω : Ω) :
    hairerIPsiRecentred N ξ ω x y = hairerIPsiRecentred N ξ ω x z + hairerIPsiRecentred N ξ ω z y +
      ∑ i : Fin 3, iPsiGradIncr N ξ i x z ω * (y.2 i - z.2 i) := by
  have hc : ∀ (w : ParabolicSpace) (j : Fin 3), parabolicCoords w j.succ = w.2 j := by
    intro w j
    fin_cases j <;> rfl
  unfold hairerIPsiRecentred iPsiGradIncr CanonicalData.relCoord
  simp only [hc]
  have : ∑ i : Fin 3, (hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i z -
      hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x) *
        (y.2 i - z.2 i) =
      ∑ i : Fin 3, (hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i z *
        (y.2 i - z.2 i)) - ∑ i : Fin 3, (hairerSpatialGradient N
          (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x * (y.2 i - z.2 i)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]
  have h2 : ∑ i : Fin 3, hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x *
      (y.2 i - x.2 i) = ∑ i : Fin 3, hairerSpatialGradient N
        (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x * (z.2 i - x.2 i) +
        ∑ i : Fin 3, hairerSpatialGradient N (fun w => hairerPsiField N ξ ω (spaceTimeProj w)) i x *
          (y.2 i - z.2 i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h2]
  ring

end Algebra

section Moments

variable {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {W : (SpaceTime → ℝ) → Ω → ℝ}
  {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

private theorem iPsiRecentred_eq (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (x y : ParabolicSpace) :
    (fun ω => hairerIPsiRecentred N ξ ω x y) =
      fun ω => gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω :=
  funext fun ω => hairerIPsiRecentred_eq_gammaPsiTaylor N (hξ.1 ω) x y

private theorem iPsiGradIncr_eq (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (i : Fin 3)
    (x y : ParabolicSpace) :
    iPsiGradIncr N ξ i x y = gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) :=
  funext fun ω => hairerSpatialGradient_sub_eq_gammaGrad N (hξ.1 ω) i x y

theorem measurable_hairerIPsiRecentred (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ)
    (x y : ParabolicSpace) : Measurable fun ω => hairerIPsiRecentred N ξ ω x y := by
  rw [iPsiRecentred_eq N hξ]
  exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
    (measurable_hairerTaylorKernel N _ _ _)

theorem measurable_iPsiGradIncr (N : ℕ) (hξ : IsRegularisedNoise P W ρ ε ξ) (i : Fin 3)
    (x y : ParabolicSpace) : Measurable fun ω => iPsiGradIncr N ξ i x y ω := by
  rw [iPsiGradIncr_eq N hξ]
  exact measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
    (measurable_hairerGradIncrementKernel N i _ _)

/-- **`q`-th moment of `R(x, y)` at all distances.** -/
theorem hairerIPsiRecentred_lintegral_enorm_pow_le_all (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (parabolicSemigroup.scaleDist y x ^ (homogeneity κ .iPsi + κbar) +
            parabolicSemigroup.scaleDist y x ^ (4 : ℝ))) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨C1, hC1, h1⟩ := gammaPsiTaylor_lintegral_enorm_pow_le_kappa.{u} N hρ hk0 (by linarith) hκb0 hκb hq
  have hg : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * torusParabolicSize (y - x) ^ (1 / 2 - κ.1 + κbar)) ^ q :=
    fun i => gammaGrad_lintegral_enorm_pow_le_kappa.{u} N hρ i hk0 (by linarith) hκb0 hκb hq
  choose Cg hCg hgb using hg
  set B' : ℝ := ∑ i, Cg i with hB'
  have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun i _ => hCg i
  refine ⟨C1 + 128 * max C1 B', by positivity, ?_⟩
  intro Ω _ P W ε ξ hW hε hξ x y
  have := hW.isProbabilityMeasure
  have hs0 : 0 ≤ homogeneity κ .iPsi + κbar := by
    simp only [homogeneity]; linarith
  have key := lintegral_enorm_nearFar_pow_le (P := P) hq hC1 hs0
    (fun x y ω => hairerIPsiRecentred N ξ ω x y)
    (fun i x y ω => iPsiGradIncr N ξ i x y ω)
    (fun x y => measurable_hairerIPsiRecentred N hξ x y)
    (fun i x y => measurable_iPsiGradIncr N hξ i x y)
    (fun x z y ω => hairerIPsiRecentred_cocycle N x z y ω)
    (fun i x z y ω => iPsiGradIncr_add N i x z y ω)
    (B' := B')
    (fun x y hd => by
      have hh := h1 hW hε hξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) hd
      have e0 : ∀ ω, hairerIPsiRecentred N ξ ω x y =
          gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω :=
        fun ω => congrFun (iPsiRecentred_eq N hξ x y) ω
      show ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y‖ₑ ^ q ∂P ≤ _
      simp_rw [e0]
      have e : (3 / 2 - κ.1 + κbar) = homogeneity κ .iPsi + κbar := by
        simp only [homogeneity]
      rw [e] at hh
      exact hh)
    (fun i x y hd => by
      have hdt := (torusParabolicSize_spaceTimeProj_sub_le y x).trans hd
      have hh := hgb i hW hε hξ (spaceTimeProj x) (spaceTimeProj y) (hdt.trans (by norm_num))
      show ∫⁻ ω, ‖iPsiGradIncr N ξ i x y ω‖ₑ ^ q ∂P ≤ _
      have e0 : ∀ ω, iPsiGradIncr N ξ i x y ω =
          gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω :=
        fun ω => congrFun (iPsiGradIncr_eq N hξ i x y) ω
      simp_rw [e0]
      refine hh.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
      have h01 : torusParabolicSize (spaceTimeProj y - spaceTimeProj x) ^ (1 / 2 - κ.1 + κbar) ≤ 1 :=
        Real.rpow_le_one (torusParabolicSize_nonneg _) (hdt.trans (by norm_num))
          (by linarith)
      calc Cg i * _ ≤ Cg i * 1 := mul_le_mul_of_nonneg_left h01 (hCg i)
        _ = Cg i := mul_one _
        _ ≤ B' := Finset.single_le_sum (f := Cg) (fun j _ => hCg j) (Finset.mem_univ i))
    x y
  have e4 : parabolicNorm (y - x) ^ (4 : ℝ) = parabolicNorm (y - x) ^ (4 : ℕ) := by
    norm_num
  rw [show parabolicSemigroup.scaleDist y x = parabolicNorm (y - x) from rfl, e4]
  exact key

/-- **Two-scale difference of `R(x, y)` at all distances.** -/
theorem hairerIPsiRecentred_sub_lintegral_enorm_pow_le_all (N : ℕ)
    {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa)
    {κbar θ : ℝ} (hκb0 : 0 ≤ κbar) (hθ : 0 < θ)
    (hθκ : θ < κ.1 - κbar) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C₀ : ℝ, 0 ≤ C₀ ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C₀ * (max ε ε') ^ θ *
            (parabolicSemigroup.scaleDist y x ^ (homogeneity κ .iPsi + κbar) +
            parabolicSemigroup.scaleDist y x ^ (4 : ℝ))) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨C1, hC1, h1⟩ := gammaPsiTaylor_sub_lintegral_enorm_pow_le_kappa.{u} N hρ hρ' (κ := κ.1)
    (κ' := κbar) (θ := θ) (by linarith) hκb0 hθ hθκ hq
  have hg : ∀ i : Fin 3, ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y : SpaceTime, torusParabolicSize (y - x) ≤ 1 →
        ∫⁻ ω, ‖gammaGrad N ξ i x y ω - gammaGrad N ξ' i x y ω‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            torusParabolicSize (y - x) ^ (1 / 2 - κ.1 + κbar)) ^ q :=
    fun i => gammaGrad_sub_lintegral_enorm_pow_le_kappa.{u} N hρ hρ' i (κ := κ.1) (κ' := κbar)
      (θ := θ) (by linarith) hκb0 hθ hθκ hq
  choose Cg hCg hgb using hg
  set B' : ℝ := ∑ i, Cg i with hB'
  have hB'0 : 0 ≤ B' := Finset.sum_nonneg fun i _ => hCg i
  refine ⟨C1 + 128 * max C1 B', by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y
  have := hW.isProbabilityMeasure
  have hs0 : 0 ≤ homogeneity κ .iPsi + κbar := by
    simp only [homogeneity]; linarith
  have hm : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have key := lintegral_enorm_nearFar_pow_le (P := P) hq (mul_nonneg hC1 hm) hs0
    (fun x y ω => hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y)
    (fun i x y ω => iPsiGradIncr N ξ i x y ω - iPsiGradIncr N ξ' i x y ω)
    (fun x y => (measurable_hairerIPsiRecentred N hξ x y).sub
      (measurable_hairerIPsiRecentred N hξ' x y))
    (fun i x y => (measurable_iPsiGradIncr N hξ i x y).sub (measurable_iPsiGradIncr N hξ' i x y))
    (fun x z y ω => by
      rw [hairerIPsiRecentred_cocycle N x z y ω (ξ := ξ),
        hairerIPsiRecentred_cocycle N x z y ω (ξ := ξ')]
      simp only [sub_mul, Finset.sum_sub_distrib]
      ring)
    (fun i x z y ω => by
      rw [iPsiGradIncr_add N i x z y ω (ξ := ξ), iPsiGradIncr_add N i x z y ω (ξ := ξ')]
      ring)
    (B' := B' * (max ε ε') ^ θ)
    (fun x y hd => by
      have hh := h1 hW hε hε' hξ hξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) hd
      have e0 : ∀ ω, hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y =
          gammaPsiTaylor N ξ (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω -
            gammaPsiTaylor N ξ' (spaceTimeProj x) (y.1 - x.1) (y.2 - x.2) ω :=
        fun ω => by
          rw [congrFun (iPsiRecentred_eq N hξ x y) ω, congrFun (iPsiRecentred_eq N hξ' x y) ω]
      show ∫⁻ ω, ‖hairerIPsiRecentred N ξ ω x y - hairerIPsiRecentred N ξ' ω x y‖ₑ ^ q ∂P ≤ _
      simp_rw [e0]
      have e : (3 / 2 - κ.1 + κbar) = homogeneity κ .iPsi + κbar := by
        simp only [homogeneity]
      rw [e] at hh
      exact hh)
    (fun i x y hd => by
      have hdt := (torusParabolicSize_spaceTimeProj_sub_le y x).trans hd
      have hh := hgb i hW hε hε' hξ hξ' (spaceTimeProj x) (spaceTimeProj y)
        (hdt.trans (by norm_num))
      show ∫⁻ ω, ‖iPsiGradIncr N ξ i x y ω - iPsiGradIncr N ξ' i x y ω‖ₑ ^ q ∂P ≤ _
      have e0 : ∀ ω, iPsiGradIncr N ξ i x y ω - iPsiGradIncr N ξ' i x y ω =
          gammaGrad N ξ i (spaceTimeProj x) (spaceTimeProj y) ω -
            gammaGrad N ξ' i (spaceTimeProj x) (spaceTimeProj y) ω := fun ω => by
        rw [congrFun (iPsiGradIncr_eq N hξ i x y) ω, congrFun (iPsiGradIncr_eq N hξ' i x y) ω]
      simp_rw [e0]
      refine hh.trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q)
      have h01 : torusParabolicSize (spaceTimeProj y - spaceTimeProj x) ^ (1 / 2 - κ.1 + κbar) ≤ 1 :=
        Real.rpow_le_one (torusParabolicSize_nonneg _) (hdt.trans (by norm_num))
          (by linarith)
      have hsum : Cg i ≤ B' := Finset.single_le_sum (f := Cg) (fun j _ => hCg j) (Finset.mem_univ i)
      calc Cg i * (max ε ε') ^ θ * _ ≤ Cg i * (max ε ε') ^ θ * 1 :=
            mul_le_mul_of_nonneg_left h01 (mul_nonneg (hCg i) hm)
        _ = Cg i * (max ε ε') ^ θ := mul_one _
        _ ≤ B' * (max ε ε') ^ θ := mul_le_mul_of_nonneg_right hsum hm)
    x y
  have e4 : parabolicNorm (y - x) ^ (4 : ℝ) = parabolicNorm (y - x) ^ (4 : ℕ) := by
    norm_num
  rw [show parabolicSemigroup.scaleDist y x = parabolicNorm (y - x) from rfl, e4]
  refine key.trans (le_of_eq ?_)
  congr 2
  rw [← max_mul_of_nonneg _ _ hm]
  ring

end Moments

end RegularityStructures.Phi43

end

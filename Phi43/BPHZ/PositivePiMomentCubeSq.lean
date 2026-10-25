/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.PositivePiMomentSq
public import Phi43.BPHZ.PositivePiMomentSquare
import Mathlib.Tactic

/-!
# `q`-th moments of `Q_t Π_x I(Ψ³)² (x)` for the canonical models

`Π_x I(Ψ³)² = (Π_x I(Ψ³))² = v₃²`, so the `q`-th moment of its semigroup average follows from
Minkowski and the `2q`-th moment of `v₃` at the exponent `(1/2 - 3κ + κ̄/2)`
(`lintegral_enorm_sq_pow_le`); for the difference of two models
`v₃² - v₃'² = (v₃ - v₃')(v₃ + v₃')` and Cauchy-Schwarz are used
(`lintegral_enorm_sq_sub_sq_pow_le`).
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem cubeSq_exponent (κ : Kappa) (κbar : ℝ) :
    (homogeneity κ .iPsiCube + κbar / 2) * 2 = homogeneity κ .iPsiCubeSq + κbar := by
  simp only [homogeneity]; ring

private theorem rpow_two_mul {d : ℝ} (hd : 0 ≤ d) (e : ℝ) : (d ^ e) ^ 2 = d ^ (e * 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hd]
  norm_num

/-- **`q`-th moment of `Q_t Π_x I(Ψ³)² (x)`.** -/
theorem regPi_iPsiCubeSq_lintegral_enorm_pow_le (N : ℕ) {ρ : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (κ : Kappa) {κbar : ℝ} (hκb0 : 0 ≤ κbar) (hκb : κbar ≤ κ.1 / 2)
    {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}
      {Cst : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → IsRegularisedNoise P W ρ ε ξ →
      C₁ Cst = hairerWickConstant N ρ ε →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCubeSq + κbar) /
            parabolicSemigroup.order)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  obtain ⟨C₀, hC₀, h⟩ := gammaWickCube_lintegral_enorm_pow_le_all.{u} N hρ (κ := κ) (κbar := κbar / 2)
    (by linarith) (by linarith) (q := 2 * q) (by omega)
  have hs : 0 ≤ homogeneity κ .iPsiCubeSq + κbar := by
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  refine ⟨C * C₀ ^ 2, mul_nonneg hC (sq_nonneg _), ?_⟩
  intro Ω _ P W ε ξ Cst hW hε hξ hC1 hg t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) ^ 2 := by
    filter_upwards [hg] with ω hgω
    rw [regPi_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω _ ht.1 x,
      extensionPi_iPsiCubeSq_eq (hξ.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hC1, hairerKernelIncrementPairing_psiCube_eq_gammaWickCube]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  have := hM (C₀ := C₀ ^ 2) (sq_nonneg _) x
    (F := fun ω y => (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) ^ 2)
    ((measurable_gammaWickCube_proj N hξ (spaceTimeProj x)).pow_const 2)
    (fun y => by
      have hd : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg y x
      have h1 := lintegral_enorm_sq_pow_le (P := P)
        (f := fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) (q := q)
        (D := C₀ * parabolicSemigroup.scaleDist y x ^ (homogeneity κ .iPsiCube + κbar / 2))
        (mul_nonneg hC₀ (Real.rpow_nonneg hd _)) (h hW hε hξ x y)
      refine h1.trans (le_of_eq ?_)
      congr 2
      rw [mul_pow, rpow_two_mul hd, cubeSq_exponent]) ht.1
  simpa [mul_assoc] using this

/-- The pointwise (in `y`) bound for the difference of squares. -/
private theorem cubeSq_pointwise {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {f g : Ω → ℝ}
    (hf : Measurable f) (hg : Measurable g) {q : ℕ} (hq : 1 ≤ q) {B₀ D₀ d e : ℝ}
    (hB₀ : 0 ≤ B₀) (hd : 0 ≤ d) (he : 0 < e)
    (h1 : ∫⁻ ω, ‖f ω - g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (B₀ * d ^ e) ^ (2 * q))
    (h2 : ∫⁻ ω, ‖f ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (D₀ * d ^ e) ^ (2 * q))
    (h3 : ∫⁻ ω, ‖g ω‖ₑ ^ (2 * q) ∂P ≤ ENNReal.ofReal (D₀ * d ^ e) ^ (2 * q)) :
    ∫⁻ ω, ‖f ω ^ 2 - g ω ^ 2‖ₑ ^ q ∂P ≤ ENNReal.ofReal (2 * B₀ * D₀ * d ^ (e * 2)) ^ q := by
  have hdd : 0 ≤ d ^ e := Real.rpow_nonneg hd _
  have h := lintegral_enorm_sq_sub_sq_pow_le hf hg hq (mul_nonneg hB₀ hdd) h1 h2 h3
  refine h.trans (le_of_eq ?_)
  congr 2
  have : d ^ (e * 2) = d ^ e * d ^ e := by
    rw [mul_two, Real.rpow_add' hd (by linarith)]
  rw [this]
  ring

/-- **Two-model difference of `Q_t Π_x I(Ψ³)² (x)`.** -/
theorem regPi_iPsiCubeSq_sub_lintegral_enorm_pow_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') (κ : Kappa) {κbar θ : ℝ} (hκb0 : 0 ≤ κbar)
    (hκb : κbar ≤ κ.1 / 2) (hθ : 0 < θ) (hθκ : θ ≤ κ.1) {q : ℕ} (hq : 1 ≤ q) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}
      {Cst Cst' : RenormalisationConstants},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      C₁ Cst = hairerWickConstant N ρ ε → C₁ Cst' = hairerWickConstant N ρ' ε' →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ ω)) →
      (∀ᵐ ω ∂P, Statements.HasPhi43NoiseGrowth (ξ' ω)) →
      ∀ t ∈ Set.Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(canonicalModelOfLift N κ Cst (ξ ω)).regPi x
            (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x -
          (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
            (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * (max ε ε') ^ θ *
            t ^ (((phi43RegularityStructure κ).deg Symbol.iPsiCubeSq + κbar) /
              parabolicSemigroup.order)) ^ q := by
  have hk0 := κ.2.1
  have hk1 := κ.2.2
  have hq2 : 1 ≤ 2 * q := by omega
  obtain ⟨C₀, hC₀, h⟩ := gammaWickCube_lintegral_enorm_pow_le_all.{u} N hρ (κ := κ) (κbar := κbar / 2)
    (by linarith) (by linarith) hq2
  obtain ⟨C₀', hC₀', h'⟩ := gammaWickCube_lintegral_enorm_pow_le_all.{u} N hρ' (κ := κ)
    (κbar := κbar / 2) (by linarith) (by linarith) hq2
  obtain ⟨C₁, hC₁, hd⟩ := gammaWickCube_sub_lintegral_enorm_pow_le_all.{u} N hρ hρ' (κ := κ)
    (κbar := κbar / 2) (θ := θ) (by linarith) (by linarith) hθ hθκ hq2
  have hs : 0 ≤ homogeneity κ .iPsiCubeSq + κbar := by
    simp only [homogeneity]; linarith
  have he : 0 < homogeneity κ .iPsiCube + κbar / 2 := by
    simp only [homogeneity]; linarith
  obtain ⟨C, hC, hM⟩ := lintegral_enorm_semigroup_apply_pow_le.{u} hq hs
  set Dm : ℝ := max C₀ C₀' with hDm
  have hDm0 : 0 ≤ Dm := le_max_of_le_left hC₀
  refine ⟨C * (2 * C₁ * Dm), mul_nonneg hC (by positivity), ?_⟩
  intro Ω _ P W ε ε' ξ ξ' Cst Cst' hW hε hε' hξ hξ' hC1 hC1' hg hg' t ht x
  have := hW.isProbabilityMeasure
  rw [posPi_exponent_eq]
  have hMx : 0 ≤ (max ε ε') ^ θ := Real.rpow_nonneg (le_max_of_le_left hε.1.le) _
  have hae : ∀ᵐ ω ∂P, (canonicalModelOfLift N κ Cst (ξ ω)).regPi x
      (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x -
        (canonicalModelOfLift N κ Cst' (ξ' ω)).regPi x
      (Pi.single Symbol.iPsiCubeSq (1 : ℝ) : Symbol → ℝ) t x =
      ∫ y, parabolicSemigroup.kernel t x y *
        ((gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) ^ 2 -
          (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) ^ 2) := by
    filter_upwards [hg, hg'] with ω hgω hgω'
    rw [regPi_sub_canonicalModelOfLift_eq_integral (hξ.1 ω) hgω (hξ'.1 ω) hgω' _ ht.1 x,
      extensionPi_iPsiCubeSq_eq (hξ.1 ω) x, extensionPi_iPsiCubeSq_eq (hξ'.1 ω) x]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    beta_reduce
    rw [hC1, hC1', hairerKernelIncrementPairing_psiCube_eq_gammaWickCube,
      hairerKernelIncrementPairing_psiCube_eq_gammaWickCube]
  rw [lintegral_congr_ae (hae.mono fun ω hω => by rw [hω])]
  have hF : Measurable fun z : Ω × ParabolicSpace =>
      (gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj z.2) z.1) ^ 2 -
        (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj z.2) z.1) ^ 2 :=
    ((measurable_gammaWickCube_proj N hξ (spaceTimeProj x)).pow_const 2).sub
      ((measurable_gammaWickCube_proj N hξ' (spaceTimeProj x)).pow_const 2)
  have hpt : ∀ y : ParabolicSpace,
      ∫⁻ ω, ‖(gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω) ^ 2 -
        (gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω) ^ 2‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (2 * (C₁ * (max ε ε') ^ θ) * Dm * parabolicSemigroup.scaleDist y x ^
        ((homogeneity κ .iPsiCube + κbar / 2) * 2)) ^ q := by
    intro y
    have hdy : 0 ≤ parabolicSemigroup.scaleDist y x := parabolicSemigroup.scaleDist_nonneg y x
    have hmf : Measurable fun ω => gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω :=
      measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ)
        (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y))
    have hmg : Measurable fun ω => gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω :=
      measurable_integral_mul_field (measurable_hairerPsiWickCube_uncurry N hξ')
        (measurable_hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y))
    have hdd : 0 ≤ parabolicSemigroup.scaleDist y x ^ (homogeneity κ .iPsiCube + κbar / 2) :=
      Real.rpow_nonneg hdy _
    have h2 : ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ (2 * q) ∂P ≤
        ENNReal.ofReal (Dm * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) :=
      (h hW hε hξ x y).trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_left _ _) hdd)) _)
    have h3 : ∫⁻ ω, ‖gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ (2 * q) ∂P ≤
        ENNReal.ofReal (Dm * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) :=
      (h' hW hε' hξ' x y).trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (le_max_right _ _) hdd)) _)
    have h1 : ∫⁻ ω, ‖gammaWickCube N ρ ε ξ (spaceTimeProj x) (spaceTimeProj y) ω -
        gammaWickCube N ρ' ε' ξ' (spaceTimeProj x) (spaceTimeProj y) ω‖ₑ ^ (2 * q) ∂P ≤
        ENNReal.ofReal ((C₁ * (max ε ε') ^ θ) * parabolicSemigroup.scaleDist y x ^
          (homogeneity κ .iPsiCube + κbar / 2)) ^ (2 * q) := by
      exact hd hW hε hε' hξ hξ' x y
    exact cubeSq_pointwise hmf hmg hq (mul_nonneg hC₁ hMx) hdy he h1 h2 h3
  have hcoef : 0 ≤ 2 * C₁ * Dm * (max ε ε') ^ θ := by positivity
  have key := hM (C₀ := 2 * C₁ * Dm * (max ε ε') ^ θ) hcoef x hF
    (fun y => by
      have e : 2 * (C₁ * (max ε ε') ^ θ) * Dm = 2 * C₁ * Dm * (max ε ε') ^ θ := by ring
      have e2 : (homogeneity κ .iPsiCube + κbar / 2) * 2 = homogeneity κ .iPsiCubeSq + κbar :=
        cubeSq_exponent κ κbar
      have := hpt y
      rwa [e, e2] at this) ht.1
  have e3 : C * (2 * C₁ * Dm * (max ε ε') ^ θ) = C * (2 * C₁ * Dm) * (max ε ε') ^ θ := by ring
  rwa [e3] at key

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSqDiffCov
import Mathlib.Tactic

/-!
# The pointwise bound of `Δ e` for `I(Ψ)(Ψ² - c₁)`, two mollifiers

`ipsiMixSq_sd_abs_le`: `Δ e` for `e_{ij}(y, y') = E[F_i(y) F_j(y')]`, `F_i = Π_x^{ρ_i,ε_i} I(Ψ)(Ψ² - c₁)`,
is bounded by `C m^(2θ) (X₀ D S₁ + a D² S₂)` with the notation of `ProductIPsiPsiSqDiffCov`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem ipsiMixSq_hρ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') : ∀ i, IsMollifier (![ρ, ρ'] i) := by
  intro i; fin_cases i
  · exact hρ
  · exact hρ'

private theorem ipsiMixSq_hε {ε ε' : ℝ} (hε : 0 < ε) (hε' : 0 < ε') : ∀ i, 0 < (![ε, ε'] : Fin 2 → ℝ) i := by
  intro i; fin_cases i
  · exact hε
  · exact hε'

private theorem ipsiMixSq_hξ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
    {ξ ξ' : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') :
    ∀ i, IsRegularisedNoise P W (![ρ, ρ'] i) (![ε, ε'] i) (![ξ, ξ'] i) := by
  intro i; fin_cases i
  · exact hξ
  · exact hξ'

private theorem ipsiMixSq_meas (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') (ε ε' : ℝ) (i j : Fin 2) :
    Measurable (qMix N ![ρ, ρ'] ![ε, ε'] i j) :=
  measurable_hairerCrossCovarianceTwo N (ipsiMixSq_hρ hρ hρ' i) (ipsiMixSq_hρ hρ hρ' j) _ _

/-- **The pointwise bound of the second difference `Δ e` for the Wick-square field.** -/
theorem ipsiMixSq_sd_abs_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {θ p γ δ : ℝ} (hθ : 0 < θ) (hθ4 : θ ≤ 1 / 4) (hp : 0 < p) (hp1 : p < 1)
    (hγ : 0 < γ) (hγ1 : γ < 1) (hγθ : γ + 2 * θ < 1) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hθδ : 2 * θ + δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : ParabolicSpace, 0 < parabolicNorm (y - x) → 0 < parabolicNorm (y' - x) →
        0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y) →
        0 < torusParabolicSize (spaceTimeProj x - spaceTimeProj y') →
        0 < torusParabolicSize (spaceTimeProj y - spaceTimeProj y') →
        |arrSd (fun i j => ∫ ω, hairerIPsiPsiSqField N (![ξ, ξ'] i)
              (hairerWickConstant N (![ρ, ρ'] i) (![ε, ε'] i)) x ω y *
            hairerIPsiPsiSqField N (![ξ, ξ'] j)
              (hairerWickConstant N (![ρ, ρ'] j) (![ε, ε'] j)) x ω y' ∂P)| ≤
          C * max ε ε' ^ (2 * θ) *
            ((((parabolicNorm (y - x) ^ γ * (1 + parabolicNorm (y - x))) *
                (parabolicNorm (y' - x) ^ γ * (1 + parabolicNorm (y' - x))) *
              ((1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-p)) *
                (1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y') ^ (-p)))) *
                torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ))) *
              ((1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y) ^ (-(2 * θ))) +
                (1 + torusParabolicSize (spaceTimeProj x - spaceTimeProj y') ^ (-(2 * θ))) +
                (1 + torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(2 * θ)))) +
            (parabolicNorm (y - x) ^ ((3 - δ) / 2) * parabolicNorm (y' - x) ^ ((3 - δ) / 2) *
                (torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ)) *
                  torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(1 : ℝ)))) *
              ((1 + parabolicNorm (y - x) ^ (-(2 * θ))) + (1 + parabolicNorm (y' - x) ^ (-(2 * θ))) +
                (1 + torusParabolicSize (spaceTimeProj y - spaceTimeProj y') ^ (-(2 * θ))))) := by
  obtain ⟨CQ, hCQ, hQ⟩ := qMix_isArrR N ρ ρ' hρ hρ' hθ (by linarith)
  obtain ⟨Cp, hCp, hP⟩ := ipsi_pairing_isArrR N hθ hp hp1 hγ hγ1 hγθ
  obtain ⟨CB, hCB, hBB⟩ := ipsi_B_isArrR.{u} N hρ hρ' hθ hθ4 hδ hδ1 hθδ
  refine ⟨2 * (10240 * Cp ^ 2 * CQ ^ 3) + 2 * (512 * CB * CQ ^ 2), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hr hr' he1 he2 hd
  have := hW.isProbabilityMeasure
  set m := max ε ε' with hm
  have hm0 : 0 ≤ m := le_max_of_le_left hε.1.le
  set r := parabolicNorm (y - x) with hrdef
  set r' := parabolicNorm (y' - x) with hr'def
  set e1 := torusParabolicSize (spaceTimeProj x - spaceTimeProj y) with he1def
  set e2 := torusParabolicSize (spaceTimeProj x - spaceTimeProj y') with he2def
  set d := torusParabolicSize (spaceTimeProj y - spaceTimeProj y') with hddef
  have hQz : ∀ z : SpaceTime, 0 < torusParabolicSize z →
      IsArrR (fun i j => qMix N ![ρ, ρ'] ![ε, ε'] i j z) (CQ * torusParabolicSize z ^ (-(1 : ℝ)))
        (min 1 (ipsiRatio m θ (torusParabolicSize z))) :=
    fun z hz => hQ hε.1 hε.2 hε'.1 hε'.2 z hz
  have hmeas := ipsiMixSq_meas N hρ hρ' ε ε'
  -- the four pairing arrays
  have hrowΦ : ∀ z : SpaceTime, 0 < torusParabolicSize z →
      IsArrR (fun i j => (fun (i _ : Fin 2) (z : SpaceTime) => qMix N ![ρ, ρ'] ![ε, ε'] i i z) i j z)
        ((3 * CQ) * torusParabolicSize z ^ (-(1 : ℝ))) (min 1 (ipsiRatio m θ (torusParabolicSize z))) :=
    fun z hz => by
      have := (hQz z hz).diag_row
      simpa only [mul_assoc] using this
  have hcolΦ : ∀ z : SpaceTime, 0 < torusParabolicSize z →
      IsArrR (fun i j => (fun (_ j : Fin 2) (z : SpaceTime) => qMix N ![ρ, ρ'] ![ε, ε'] j j z) i j z)
        ((3 * CQ) * torusParabolicSize z ^ (-(1 : ℝ))) (min 1 (ipsiRatio m θ (torusParabolicSize z))) :=
    fun z hz => by
      have := (hQz z hz).diag_col
      simpa only [mul_assoc] using this
  have hnegΦ : ∀ z : SpaceTime, 0 < torusParabolicSize z →
      IsArrR (fun i j => (fun (i j : Fin 2) (z : SpaceTime) => qMix N ![ρ, ρ'] ![ε, ε'] i j (-z)) i j z)
        (CQ * torusParabolicSize z ^ (-(1 : ℝ))) (min 1 (ipsiRatio m θ (torusParabolicSize z))) :=
    fun z hz => by
      have h0 : torusParabolicSize (-z) = torusParabolicSize z := by
        have := ipsi_size_swap 0 z
        simpa using this
      have := hQz (-z) (by rw [h0]; exact hz)
      rw [h0] at this
      exact this
  have h3CQ : 0 ≤ 3 * CQ := by positivity
  obtain ⟨iA, AR⟩ := hP (m := m) hm0 (Φ := fun i _ z => qMix N ![ρ, ρ'] ![ε, ε'] i i z) (CΦ := 3 * CQ)
    h3CQ (fun i j => hmeas i i) hrowΦ x y (g := spaceTimeProj y) he1
  obtain ⟨iA', AR'⟩ := hP (m := m) hm0 (Φ := fun _ j z => qMix N ![ρ, ρ'] ![ε, ε'] j j z) (CΦ := 3 * CQ)
    h3CQ (fun i j => hmeas j j) hcolΦ x y' (g := spaceTimeProj y') he2
  obtain ⟨iR, RR⟩ := hP (m := m) hm0 (Φ := fun i j z => qMix N ![ρ, ρ'] ![ε, ε'] i j z) (CΦ := CQ) hCQ
    hmeas hQz x y (g := spaceTimeProj y') he2
  obtain ⟨iR', RR'⟩ := hP (m := m) hm0 (Φ := fun i j z => qMix N ![ρ, ρ'] ![ε, ε'] i j (-z)) (CΦ := CQ)
    hCQ (fun i j => (hmeas i j).comp measurable_neg) hnegΦ x y' (g := spaceTimeProj y) he1
  have hRB := hBB hW hε hε' hξ hξ' x y y' hr hr'
  have hQd := hQz (spaceTimeProj y - spaceTimeProj y') hd
  have hid : ∀ i j : Fin 2, ∫ ω, hairerIPsiPsiSqField N (![ξ, ξ'] i)
        (hairerWickConstant N (![ρ, ρ'] i) (![ε, ε'] i)) x ω y *
        hairerIPsiPsiSqField N (![ξ, ξ'] j)
          (hairerWickConstant N (![ρ, ρ'] j) (![ε, ε'] j)) x ω y' ∂P =
      2 * (∫ ω, hairerIPsiRecentred N (![ξ, ξ'] i) ω x y *
          hairerIPsiRecentred N (![ξ, ξ'] j) ω x y' ∂P) *
        qMix N ![ρ, ρ'] ![ε, ε'] i j (spaceTimeProj y - spaceTimeProj y') ^ 2 +
      4 * ((∫ w, ipsiTaylorKernel N x y w * qMix N ![ρ, ρ'] ![ε, ε'] i i (w - spaceTimeProj y)) *
        (∫ w, ipsiTaylorKernel N x y' w * qMix N ![ρ, ρ'] ![ε, ε'] j j (w - spaceTimeProj y')) *
          qMix N ![ρ, ρ'] ![ε, ε'] i j (spaceTimeProj y - spaceTimeProj y')) +
      4 * ((∫ w, ipsiTaylorKernel N x y w * qMix N ![ρ, ρ'] ![ε, ε'] i j (w - spaceTimeProj y')) *
        (∫ w, ipsiTaylorKernel N x y' w * qMix N ![ρ, ρ'] ![ε, ε'] i j (spaceTimeProj y - w)) *
          qMix N ![ρ, ρ'] ![ε, ε'] i j (spaceTimeProj y - spaceTimeProj y')) := by
    intro i j
    refine hairerIPsiPsiSqField_mix_integral_mul N (ipsiMixSq_hρ hρ hρ') (ipsiMixSq_hε hε.1 hε'.1) hW
      (ipsiMixSq_hξ hξ hξ') i j x y y' (iA i i) (iA' j j) (iR i j) ?_
    have := iR' i j
    simpa only [neg_sub] using this
  simp only [neg_sub] at RR'
  have hbound := ipsiSq_e_sd_le (e := fun i j => ∫ ω, hairerIPsiPsiSqField N (![ξ, ξ'] i)
        (hairerWickConstant N (![ρ, ρ'] i) (![ε, ε'] i)) x ω y *
        hairerIPsiPsiSqField N (![ξ, ξ'] j)
          (hairerWickConstant N (![ρ, ρ'] j) (![ε, ε'] j)) x ω y' ∂P) AR AR' hRB hQd RR RR' hid
  refine hbound.trans ?_
  have σ0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ ipsiRatio m θ s := fun s hs => ipsiRatio_nonneg m θ s hm0 hs
  have ς0 : ∀ s : ℝ, 0 ≤ s → 0 ≤ min 1 (ipsiRatio m θ s) := fun s hs => le_min zero_le_one (σ0 s hs)
  have hr0 : 0 < r := hr
  have hW0 : 0 ≤ r ^ γ * (1 + r) := mul_nonneg (Real.rpow_nonneg hr.le _) (by linarith)
  have hW0' : 0 ≤ r' ^ γ * (1 + r') := mul_nonneg (Real.rpow_nonneg hr'.le _) (by linarith)
  have hE : ∀ e : ℝ, 0 < e → 0 ≤ 1 + e ^ (-p) := fun e he => by
    have := Real.rpow_nonneg he.le (-p); linarith
  have hu : ∀ e : ℝ, 0 < e → 0 ≤ e ^ (-(2 * θ)) := fun e he => Real.rpow_nonneg he.le _
  have hsq : ∀ s : ℝ, 0 < s → ipsiRatio m θ s ^ 2 ≤ 2 * m ^ (2 * θ) * (1 + s ^ (-(2 * θ))) :=
    fun s hs => ipsi_ratio_sq_le hm0 hs
  have hM : 0 ≤ m ^ (2 * θ) := Real.rpow_nonneg hm0 _
  have hα : 0 ≤ r ^ ((3 - δ) / 2) * r' ^ ((3 - δ) / 2) :=
    mul_nonneg (Real.rpow_nonneg hr.le _) (Real.rpow_nonneg hr'.le _)
  have hd1 : 0 ≤ d ^ (-(1 : ℝ)) := Real.rpow_nonneg hd.le _
  have hςB : 0 ≤ min 1 (ipsiRatio m θ r + ipsiRatio m θ r') :=
    le_min zero_le_one (add_nonneg (σ0 r hr.le) (σ0 r' hr'.le))
  refine (ipsiMixSq_alg (Cp := Cp) (CQ := CQ) (CB := CB) hCQ hCB hW0 hW0' (hE e1 he1) (hE e2 he2)
    hα hd1 (ς0 e1 he1.le) (ς0 e2 he2.le) hςB (ς0 d hd.le) (min_le_right _ _) (min_le_right _ _)
    (min_le_right _ _) (min_le_right _ _)).trans ?_
  have hX : 0 ≤ (r ^ γ * (1 + r)) * (r' ^ γ * (1 + r')) * ((1 + e1 ^ (-p)) * (1 + e2 ^ (-p))) *
      d ^ (-(1 : ℝ)) :=
    mul_nonneg (mul_nonneg (mul_nonneg hW0 hW0') (mul_nonneg (hE e1 he1) (hE e2 he2))) hd1
  have hY : 0 ≤ r ^ ((3 - δ) / 2) * r' ^ ((3 - δ) / 2) * (d ^ (-(1 : ℝ)) * d ^ (-(1 : ℝ))) :=
    mul_nonneg hα (mul_nonneg hd1 hd1)
  have := ipsiMixSq_weighted_sq_alg (K1 := 10240 * Cp ^ 2 * CQ ^ 3) (K2 := 512 * CB * CQ ^ 2) hX hY
    (by positivity) (by positivity) hM (hu e1 he1) (hu e2 he2)
    (hu r hr) (hu r' hr') (hu d hd) (hsq e1 he1) (hsq e2 he2) (hsq r hr) (hsq r' hr') (hsq d hd)
  refine le_of_le_of_eq this ?_
  ring

end RegularityStructures.Phi43

end

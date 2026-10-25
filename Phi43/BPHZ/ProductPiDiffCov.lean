/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductPiCrossCov
public import Phi43.BPHZ.ProductPiCov
public import Phi43.BPHZ.TreeI3Psi2DifferenceTwoChaos
public import Phi43.BPHZ.ProductDiagramDiff4

/-!
# The pointwise covariance bound for the difference `I₂Ψ_{ρ,ε} - I₂Ψ_{ρ',ε'}`

For `θ' > 0`, `δ > 0` with `2 θ' + δ < 1`, uniformly in `ε, ε' ∈ (0, 1]` and the base point,
`|E[Δ(y) Δ(ȳ)]| ≤ C (max ε ε')^(2θ') (1 + s(y-x)²) (s(y-ȳ)^(-1) s_u^θA s_v^θA +
  s(y-ȳ)^(-(1+2θ')) s_u^θB s_v^θB + s_u^η s_v^η)` with `θA = 1 - δ/2 - θ'`, `θB = 1 - δ/2`,
`η = (1 - δ)/2 - θ'`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ξ ξ' : Ω → SpaceTime → ℝ}

/-- The algebra of the final combination. -/
private theorem diff_combine_alg {I₁ I₂ I₃ C₁ C₂ C₃ Y TA TB TC : ℝ} (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (hC₃ : 0 ≤ C₃) (hY : 0 ≤ Y) (hA : 0 ≤ TA) (hB : 0 ≤ TB) (hC : 0 ≤ TC)
    (b₁ : |I₁| ≤ C₁ * Y * (TA + TB)) (b₂ : |I₂| ≤ C₂ * Y * TC) (b₃ : |I₃| ≤ C₃ * Y * TC) :
    |2 * I₁ + 4 * I₂ + 4 * I₃| ≤ (2 * C₁ + 4 * C₂ + 4 * C₃) * Y * (TA + TB + TC) := by
  have t1 := abs_add_le (2 * I₁ + 4 * I₂) (4 * I₃)
  have t2 := abs_add_le (2 * I₁) (4 * I₂)
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at t2
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)] at t1
  have t3 : |4 * I₂| = 4 * |I₂| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
  have t4 : |2 * I₁| = 2 * |I₁| := by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  have u1 : 0 ≤ C₁ * Y := mul_nonneg hC₁ hY
  have u2 : 0 ≤ C₂ * Y := mul_nonneg hC₂ hY
  have u3 : 0 ≤ C₃ * Y := mul_nonneg hC₃ hY
  linarith [mul_nonneg u1 hC, mul_nonneg u2 hA, mul_nonneg u2 hB, mul_nonneg u3 hA,
    mul_nonneg u3 hB]

/-- **Pointwise covariance bound for the difference field.** -/
theorem productISqPsiField_sub_cov_bound (N : ℕ) (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ')
    {θ δ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1) (hδ : 0 < δ) (hθδ : 2 * θ + δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ x y y' : SpaceTime, 0 < torusParabolicSize (y - y') →
        |∫ ω, (productISqPsiField N ρ ε ξ x ω y - productISqPsiField N ρ' ε' ξ' x ω y) *
            (productISqPsiField N ρ ε ξ x ω y' - productISqPsiField N ρ' ε' ξ' x ω y') ∂P| ≤
          C * (max ε ε') ^ (2 * θ) * (1 + torusParabolicSize (y - x) ^ 2) *
            (torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
                (torusParabolicSize (y - x) ^ (1 - δ / 2 - θ) *
                  torusParabolicSize (y' - x) ^ (1 - δ / 2 - θ)) +
              torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) *
                (torusParabolicSize (y - x) ^ (1 - δ / 2) *
                  torusParabolicSize (y' - x) ^ (1 - δ / 2)) +
              torusParabolicSize (y - x) ^ ((1 - δ) / 2 - θ) *
                torusParabolicSize (y' - x) ^ ((1 - δ) / 2 - θ)) := by
  have hθA : 0 < 1 - δ / 2 - θ := by linarith
  have hθB : 0 < 1 - δ / 2 := by linarith
  have hη : 0 < (1 - δ) / 2 - θ := by linarith
  obtain ⟨B, hB, hG, -⟩ := productKernelData N hρ
  obtain ⟨CD1, hCD1, hD1⟩ := productDiffPiece1_bound (Θ := 1) (σ := 2 * θ) (θA := 1 - δ / 2 - θ)
    (θB := 1 - δ / 2) (by linarith) hθA (by linarith) (by linarith) hθB (by linarith)
    (by linarith)
  obtain ⟨CD2, hCD2, hD2⟩ := productDiffPiece2_bound (Θ := 1) (σ := 2 * θ)
    (η := (1 - δ) / 2 - θ) (by linarith) hη (by linarith) (by linarith)
  obtain ⟨CD3, hCD3, hD3⟩ := productDiffPiece3_bound (Θ := 1) (σ := 2 * θ)
    (η := (1 - δ) / 2 - θ) (by linarith) hη (by linarith) (by linarith)
  obtain ⟨K1, hK1, hE1⟩ := isqDiffE1_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨K2, hK2, hE2⟩ := isqDiffE2_abs_le N ρ ρ' hρ hρ' hθ hθ1
  obtain ⟨K3, hK3, hE3⟩ := isqDiffE3_abs_le N ρ ρ' hρ hρ' hθ hθ1
  set K : ℝ := max K1 (max K2 K3) with hKdef
  have hK0 : 0 ≤ K := le_max_of_le_left hK1
  refine ⟨(2 * CD1 + 4 * CD2 + 4 * CD3) * (12 * B) * (12 * B) * K * 2, by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' x y y' hzz
  rw [productISqPsiField_sub_integral_mul_cross N hρ hρ' hε.1 hε'.1 hW hξ hξ' x y y']
  have hga := hG (y - x)
  have hgb := hG (y' - x)
  have hmax : 0 < max ε ε' := lt_max_of_lt_left hε.1
  have hμ : 0 ≤ (max ε ε') ^ (2 * θ) := Real.rpow_nonneg hmax.le _
  have h11 := measurable_hairerCrossCovarianceTwo N hρ hρ ε ε
  have h12 := measurable_hairerCrossCovarianceTwo N hρ hρ' ε ε'
  have h21 := measurable_hairerCrossCovarianceTwo N hρ' hρ ε' ε
  have h22 := measurable_hairerCrossCovarianceTwo N hρ' hρ' ε' ε'
  have m1 : Measurable (Function.uncurry (isqDiffE1 N ρ ρ' ε ε')) := by
    unfold isqDiffE1 Function.uncurry
    fun_prop
  have m2 : Measurable (fun q : SpaceTime × SpaceTime × SpaceTime =>
      isqDiffE2 N ρ ρ' ε ε' q.1 q.2.1 q.2.2) := by
    unfold isqDiffE2
    fun_prop
  have m3 : Measurable (fun q : SpaceTime × SpaceTime × SpaceTime =>
      isqDiffE3 N ρ ρ' ε ε' q.1 q.2.1 q.2.2) := by
    unfold isqDiffE3
    fun_prop
  have hz : y - x - (y' - x) = y - y' := by abel
  have hzz' : 0 < torusParabolicSize (y - x - (y' - x)) := by rw [hz]; exact hzz
  have KK1 : K1 ≤ K := le_max_left _ _
  have KK2 : K2 ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have KK3 : K3 ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  have cmono : ∀ {K' : ℝ}, K' ≤ K → ∀ {u : ℝ}, 0 ≤ u → K' * (max ε ε') ^ (2 * θ) * u ≤
      K * (max ε ε') ^ (2 * θ) * u := by
    intro K' hK' u hu
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK' hμ) hu
  obtain ⟨i1, b1⟩ := hD1 (z := y - x) (z' := y' - x) (T := |(y - x).1| + 1) (T' := |(y' - x).1| + 1)
    (K := K) (μ := (max ε ε') ^ (2 * θ)) (by positivity) (by positivity) hK0 hμ (by positivity)
    hga hgb m1 hzz' (fun x₁ x₂ p1 p2 => by
      refine (hE1 hε.1 hε.2 hε'.1 hε'.2 x₁ x₂ p1 p2).trans ?_
      exact cmono KK1 (by positivity))
  obtain ⟨i2, b2⟩ := hD2 (z := y - x) (z' := y' - x) (T := |(y - x).1| + 1) (T' := |(y' - x).1| + 1)
    (K := K) (μ := (max ε ε') ^ (2 * θ)) (by positivity) (by positivity) hK0 hμ (by positivity)
    hga hgb m2 (fun x₁ x₂ x₃ p1 p2 p3 => by
      refine (hE2 hε.1 hε.2 hε'.1 hε'.2 x₁ x₂ x₃ p1 p2 p3).trans ?_
      exact cmono KK2 (by positivity))
  obtain ⟨i3, b3⟩ := hD3 (z := y - x) (z' := y' - x) (T := |(y - x).1| + 1) (T' := |(y' - x).1| + 1)
    (K := K) (μ := (max ε ε') ^ (2 * θ)) (by positivity) (by positivity) hK0 hμ (by positivity)
    hga hgb m3 (fun x₁ x₂ x₃ p1 p2 p3 => by
      refine (hE3 hε.1 hε.2 hε'.1 hε'.2 x₁ x₂ x₃ p1 p2 p3).trans ?_
      exact cmono KK3 (by positivity))
  rw [hz] at b1 i1
  set a₀ : SpaceTime → ℝ := fun w => hairerKernelTorus N (y - x - w) - hairerKernelTorus N (-w)
    with ha₀
  set b₀ : SpaceTime → ℝ := fun w => hairerKernelTorus N (y' - x - w) - hairerKernelTorus N (-w)
    with hb₀
  set U1 : SpaceTime × SpaceTime → ℝ := Function.uncurry fun w v =>
    a₀ w * b₀ v * isqDiffE1 N ρ ρ' ε ε' (w - v) (y - y') with hU1
  set U2 : SpaceTime × SpaceTime → ℝ := Function.uncurry fun w v =>
    a₀ w * b₀ v * isqDiffE2 N ρ ρ' ε ε' (w - v) (w - (y' - x)) (y - x - v) with hU2
  set U3 : SpaceTime × SpaceTime → ℝ := Function.uncurry fun w v =>
    a₀ w * b₀ v * isqDiffE3 N ρ ρ' ε ε' (w - (y - x)) (w - v) (v - (y' - x)) with hU3
  have j1 : Integrable (fun p => 2 * U1 p) (volume.prod volume) := i1.const_mul _
  have j2 : Integrable (fun p => 4 * U2 p) (volume.prod volume) := i2.const_mul _
  have j3 : Integrable (fun p => 4 * U3 p) (volume.prod volume) := i3.const_mul _
  have j12 : Integrable (fun p => 2 * U1 p + 4 * U2 p) (volume.prod volume) := j1.add j2
  have eF : (Function.uncurry fun a b => a₀ a * b₀ b *
      (2 * isqDiffE1 N ρ ρ' ε ε' (a - b) (y - x - (y' - x)) +
        4 * isqDiffE2 N ρ ρ' ε ε' (a - b) (a - (y' - x)) (y - x - b) +
        4 * isqDiffE3 N ρ ρ' ε ε' (a - (y - x)) (a - b) (b - (y' - x)))) =
      fun p => 2 * U1 p + 4 * U2 p + 4 * U3 p := by
    funext p
    simp only [hU1, hU2, hU3, Function.uncurry, hz]
    ring
  have hint : Integrable (Function.uncurry fun a b => a₀ a * b₀ b *
      (2 * isqDiffE1 N ρ ρ' ε ε' (a - b) (y - x - (y' - x)) +
        4 * isqDiffE2 N ρ ρ' ε ε' (a - b) (a - (y' - x)) (y - x - b) +
        4 * isqDiffE3 N ρ ρ' ε ε' (a - (y - x)) (a - b) (b - (y' - x))))
      (volume.prod volume) := by
    rw [eF]
    exact j12.add j3
  have key : ∀ G : SpaceTime → SpaceTime → ℝ,
      Integrable (Function.uncurry G) (volume.prod volume) →
        ∫ p, Function.uncurry G p ∂(volume.prod volume) = ∫ w, ∫ v, G w v :=
    fun G hG => integral_prod _ hG
  have hT' : ∫ a, ∫ b, a₀ a * b₀ b *
      (2 * isqDiffE1 N ρ ρ' ε ε' (a - b) (y - x - (y' - x)) +
        4 * isqDiffE2 N ρ ρ' ε ε' (a - b) (a - (y' - x)) (y - x - b) +
        4 * isqDiffE3 N ρ ρ' ε ε' (a - (y - x)) (a - b) (b - (y' - x))) =
      2 * (∫ w, ∫ v, a₀ w * b₀ v * isqDiffE1 N ρ ρ' ε ε' (w - v) (y - y')) +
        4 * (∫ w, ∫ v, a₀ w * b₀ v *
          isqDiffE2 N ρ ρ' ε ε' (w - v) (w - (y' - x)) (y - x - v)) +
        4 * (∫ w, ∫ v, a₀ w * b₀ v *
          isqDiffE3 N ρ ρ' ε ε' (w - (y - x)) (w - v) (v - (y' - x))) := by
    rw [← key _ hint, eF, integral_add j12 j3, integral_add j1 j2, integral_const_mul,
      integral_const_mul, integral_const_mul]
    congr 1
    · congr 1
      · congr 1; exact key _ i1
      · congr 1; exact key _ i2
    · congr 1; exact key _ i3
  rw [hT']
  have rp := fun (u : SpaceTime) (e : ℝ) => Real.rpow_nonneg (torusParabolicSize_nonneg u) e
  set TA : ℝ := torusParabolicSize (y - y') ^ (-(1 : ℝ)) *
    (torusParabolicSize (y - x) ^ (1 - δ / 2 - θ) * torusParabolicSize (y' - x) ^ (1 - δ / 2 - θ))
    with hTA
  set TB : ℝ := torusParabolicSize (y - y') ^ (-(1 + 2 * θ)) *
    (torusParabolicSize (y - x) ^ (1 - δ / 2) * torusParabolicSize (y' - x) ^ (1 - δ / 2))
    with hTB
  set TC : ℝ := torusParabolicSize (y - x) ^ ((1 - δ) / 2 - θ) *
    torusParabolicSize (y' - x) ^ ((1 - δ) / 2 - θ) with hTC
  have nA : 0 ≤ TA := mul_nonneg (rp _ _) (mul_nonneg (rp _ _) (rp _ _))
  have nB : 0 ≤ TB := mul_nonneg (rp _ _) (mul_nonneg (rp _ _) (rp _ _))
  have nC : 0 ≤ TC := mul_nonneg (rp _ _) (rp _ _)
  set Y : ℝ := 12 * B * (12 * B) * K * (max ε ε') ^ (2 * θ) * (1 + (|(y - x).1| + 1)) with hY
  have hY0 : 0 ≤ Y := by
    have : 0 ≤ 1 + (|(y - x).1| + 1) := by positivity
    positivity
  have fin := diff_combine_alg hCD1 hCD2 hCD3 hY0 nA nB nC
    (by calc _ ≤ _ := b1
          _ = CD1 * Y * (TA + TB) := by simp only [hY, hTA, hTB]; ring)
    (by calc _ ≤ _ := b2
          _ = CD2 * Y * TC := by simp only [hY, hTC]; ring)
    (by calc _ ≤ _ := b3
          _ = CD3 * Y * TC := by simp only [hY, hTC]; ring)
  refine fin.trans ?_
  have e1 := abs_fst_le_sq_torusParabolicSize (y - x)
  have hT : 1 + (|(y - x).1| + 1) ≤ 2 * (1 + torusParabolicSize (y - x) ^ 2) := by
    linarith [sq_nonneg (torusParabolicSize (y - x))]
  have hS : 0 ≤ TA + TB + TC := by linarith
  have hX : 0 ≤ (2 * CD1 + 4 * CD2 + 4 * CD3) * (12 * B * (12 * B) * K *
      (max ε ε') ^ (2 * θ)) := by positivity
  calc (2 * CD1 + 4 * CD2 + 4 * CD3) * Y * (TA + TB + TC)
      = ((2 * CD1 + 4 * CD2 + 4 * CD3) * (12 * B * (12 * B) * K * (max ε ε') ^ (2 * θ))) *
        (1 + (|(y - x).1| + 1)) * (TA + TB + TC) := by simp only [hY]; ring
    _ ≤ ((2 * CD1 + 4 * CD2 + 4 * CD3) * (12 * B * (12 * B) * K * (max ε ε') ^ (2 * θ))) *
        (2 * (1 + torusParabolicSize (y - x) ^ 2)) * (TA + TB + TC) := by gcongr
    _ = _ := by ring

end RegularityStructures.Phi43

end

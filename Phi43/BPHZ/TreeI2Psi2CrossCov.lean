/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2CrossChaosFour

/-!
# The tree `I(Ψ²) Ψ²`: covariance of the field (10.39) at two mollifiers

Let `F_{ρ,a}(y) = hairerI2Psi2Field N ρ a ξ x · y`.  For mollifiers `ρ, ρ'`, scales `a`, `b` and
noises `ξ`, `ξ'` of the same white noise,
`E[F_{ρ,a}(y) F_{ρ',b}(y')] = ∫∫ δK_y(w) δK_{y'}(w') (χ₄ + χ₂)(w, w') dw dw' + E[F_{ρ,a}(y)]
E[F_{ρ',b}(y')]`, where the chaos kernels are those of `TreeI2Psi2CrossChaos` with the mixed
mollifiers `(ρ, ρ, ρ', ρ')` and scales `(a, a, b, b)`.  The covariance of the difference of the two
fields is the second difference of these (`hairerI2Psi2Field_sub_integral_mul_cross`).
-/

@[expose] public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

/-- The covariance `E[F_{ρ,a}(y) F_{ρ',b}(y')]` of the field `(10.39)` at `(ρ, a)`, `(ρ', b)`:
chaos `4`, plus chaos `2`, plus the product of the means (chaos `0`). -/
def hairerI2Psi2CovTwo (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (x : SpaceTime) (a b : ℝ)
    (y y' : SpaceTime) : ℝ :=
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
  (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
    hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
  (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ a (w - y) ^ 2) *
    (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ' b (w - y') ^ 2)

end RegularityStructures.Phi43

end

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

variable {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ}

/-- The chaos-`0` integral factorises: it is the product of the two mean integrals. -/
private theorem integral_chaos0_eq_two (N : ℕ) (ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (a b : ℝ)
    {g₁ g₃ : SpaceTime → ℝ} (y y' : SpaceTime) :
    ∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI2Psi2Chaos0Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2 =
      (∫ w, g₁ w * (2 * hairerCovariance N ρ a (w - y) ^ 2)) *
        ∫ w, g₃ w * (2 * hairerCovariance N ρ' b (w - y') ^ 2) := by
  rw [← integral_prod_mul (μ := (volume : Measure SpaceTime)) (ν := volume)
    (fun w => g₁ w * (2 * hairerCovariance N ρ a (w - y) ^ 2))
    (fun w => g₃ w * (2 * hairerCovariance N ρ' b (w - y') ^ 2))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [hairerI2Psi2Chaos0Two, hairerWickSquareFourChaos0, hairerCrossCovarianceTwo_self,
    hairerCrossCovariance_self, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  ring

/-- Algebra of the covariance of two shifted products. -/
private theorem integral_sub_mul_sub_of_integrable_two {U V : Ω → ℝ} [IsProbabilityMeasure P]
    (hUV : Integrable (fun ω => U ω * V ω) P) (hU : Integrable U P) (hV : Integrable V P)
    (Ca Cb : ℝ) :
    Integrable (fun ω => (U ω - Ca) * (V ω - Cb)) P ∧
      ∫ ω, (U ω - Ca) * (V ω - Cb) ∂P =
        ∫ ω, U ω * V ω ∂P - Cb * ∫ ω, U ω ∂P - Ca * ∫ ω, V ω ∂P + Ca * Cb := by
  have hpt : ∀ ω, (U ω - Ca) * (V ω - Cb) = U ω * V ω - Cb * U ω - Ca * V ω + Ca * Cb :=
    fun ω => by ring
  have h1 : Integrable (fun ω => U ω * V ω - Cb * U ω) P := hUV.sub (hU.const_mul Cb)
  have h2 : Integrable (fun ω => U ω * V ω - Cb * U ω - Ca * V ω) P := h1.sub (hV.const_mul Ca)
  simp_rw [hpt]
  refine ⟨h2.add (integrable_const _), ?_⟩
  rw [integral_add h2 (integrable_const _), integral_sub h1 (hV.const_mul Ca),
    integral_sub hUV (hU.const_mul Cb), integral_const_mul, integral_const_mul]
  simp

/-- The four-argument identity with scales `(a, a, b, b)`, in the product form `U V`. -/
private theorem hairerI2Psi2_integral_mul_two_mollifier (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    {g₁ g₃ : SpaceTime → ℝ} (hg₁ : Integrable g₁) (hg₃ : Integrable g₃) (y y' : SpaceTime) :
    Integrable (fun ω => ((∫ w, g₁ w * hairerPsiWickSquare N ρ a ξ ω w) *
        hairerPsiWickSquare N ρ a ξ ω y) * ((∫ w, g₃ w * hairerPsiWickSquare N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y')) P ∧
    ∫ ω, ((∫ w, g₁ w * hairerPsiWickSquare N ρ a ξ ω w) * hairerPsiWickSquare N ρ a ξ ω y) *
        ((∫ w, g₃ w * hairerPsiWickSquare N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y') ∂P =
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, g₁ q.1 * g₃ q.2 *
        hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
      (∫ w, g₁ w * (2 * hairerCovariance N ρ a (w - y) ^ 2)) *
        ∫ w, g₃ w * (2 * hairerCovariance N ρ' b (w - y') ^ 2) := by
  have hρs : ∀ i, IsMollifier ((![ρ, ρ, ρ', ρ'] : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have hε : ∀ i, 0 < (![a, a, b, b] : Fin 4 → ℝ) i := by
    intro i
    fin_cases i <;> simpa
  have hξs : ∀ i, IsRegularisedNoise P W ((![ρ, ρ, ρ', ρ'] : Fin 4 → ℝ × (Fin 3 → ℝ) → ℝ) i)
      ((![a, a, b, b] : Fin 4 → ℝ) i) ((![ξ, ξ, ξ', ξ'] : Fin 4 → Ω → SpaceTime → ℝ) i) := by
    intro i
    fin_cases i <;> simpa
  have h := hairerI2Psi2_integral_mul_four_two N hρs hε hW hξs hg₁ hg₃ y y'
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.cons_val_three] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨by simpa only [mul_assoc] using h1, ?_⟩
  rw [integral_chaos0_eq_two N ρ ρ' a b y y'] at h2
  simpa only [mul_assoc] using h2

/-- **Covariance of the field `(10.39)` of the tree `I(Ψ²) Ψ²`, two scales and four arguments**
[Hai14, (10.39)-(10.42)]. For scales `a`, `b`, noises `ξ`, `ξ'` of the same white noise, a base
point `x` and points `y`, `y'`:
`E[F_a(y) F_b(y')] = ∫∫ δK_y(w) δK_{y'}(w') χ₄(w, w') + ∫∫ δK_y(w) δK_{y'}(w') χ₂(w, w')
  + E[F_a(y)] E[F_b(y')]`
with `E[F_a(y)] = -2 ∫ K(x - w) Q_a(w - y)² dw` (chaos `0`).  The chaos kernels have the
cross covariances `Q_{ab}` as entries for pairs `(w or y, w' or y')`, and `Q_a`, `Q_b` for the
contracted pairs `(w, y)`, `(w', y')`.  The field product is integrable. -/
theorem hairerI2Psi2Field_integral_mul_cross (N : ℕ) (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') {a b : ℝ}
    (ha : 0 < a) (hb : 0 < b) (hW : IsWhiteNoise P W) {ξ ξ' : Ω → SpaceTime → ℝ}
    (hξ : IsRegularisedNoise P W ρ a ξ) (hξ' : IsRegularisedNoise P W ρ' b ξ')
    (x y y' : SpaceTime) :
    Integrable (fun ω => hairerI2Psi2Field N ρ a ξ x ω y * hairerI2Psi2Field N ρ' b ξ' x ω y') P ∧
    ∫ ω, hairerI2Psi2Field N ρ a ξ x ω y * hairerI2Psi2Field N ρ' b ξ' x ω y' ∂P =
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos4Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
      (∫ q : SpaceTime × SpaceTime, hairerI2Psi2Kernel N x y q.1 * hairerI2Psi2Kernel N x y' q.2 *
        hairerI2Psi2Chaos2Two N ![ρ, ρ, ρ', ρ'] ![a, a, b, b] y y' q.1 q.2) +
      (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ a (w - y) ^ 2) *
        (-2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ' b (w - y') ^ 2) := by
  have hprob := hW.isProbabilityMeasure
  have hg₁ := integrable_hairerI2Psi2Kernel N x y
  have hg₃ := integrable_hairerI2Psi2Kernel N x y'
  obtain ⟨hUV, hUVe⟩ := hairerI2Psi2_integral_mul_two_mollifier N hρ hρ' ha hb hW hξ hξ' hg₁ hg₃ y y'
  obtain ⟨hU, hUe⟩ := integral_integral_mul_hairerPsiWickSquare N hρ ha hW hξ hg₁ y
  obtain ⟨hV, hVe⟩ := integral_integral_mul_hairerPsiWickSquare N hρ' hb hW hξ' hg₃ y'
  obtain ⟨-, hFae⟩ := integral_hairerI2Psi2Field N hρ ha hW hξ x y
  obtain ⟨-, hFbe⟩ := integral_hairerI2Psi2Field N hρ' hb hW hξ' x y'
  obtain ⟨hint, hcov⟩ := integral_sub_mul_sub_of_integrable_two hUV hU hV
    (hairerSunsetConstant N ρ a) (hairerSunsetConstant N ρ' b)
  refine ⟨hint, ?_⟩
  have hFa' : ∫ ω, hairerI2Psi2Field N ρ a ξ x ω y ∂P =
      (∫ w, hairerI2Psi2Kernel N x y w * (2 * hairerCovariance N ρ a (w - y) ^ 2)) -
        hairerSunsetConstant N ρ a := by
    unfold hairerI2Psi2Field
    rw [integral_sub hU (integrable_const _), hUe]
    simp
  have hFb' : ∫ ω, hairerI2Psi2Field N ρ' b ξ' x ω y' ∂P =
      (∫ w, hairerI2Psi2Kernel N x y' w * (2 * hairerCovariance N ρ' b (w - y') ^ 2)) -
        hairerSunsetConstant N ρ' b := by
    unfold hairerI2Psi2Field
    rw [integral_sub hV (integrable_const _), hVe]
    simp
  have ea : -2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ a (w - y) ^ 2 =
      (∫ w, hairerI2Psi2Kernel N x y w * (2 * hairerCovariance N ρ a (w - y) ^ 2)) -
        hairerSunsetConstant N ρ a := by rw [← hFae]; exact hFa'
  have eb : -2 * ∫ w, hairerKernelTorus N (x - w) * hairerCovariance N ρ' b (w - y') ^ 2 =
      (∫ w, hairerI2Psi2Kernel N x y' w * (2 * hairerCovariance N ρ' b (w - y') ^ 2)) -
        hairerSunsetConstant N ρ' b := by rw [← hFbe]; exact hFb'
  have hcov' : ∫ ω, hairerI2Psi2Field N ρ a ξ x ω y * hairerI2Psi2Field N ρ' b ξ' x ω y' ∂P =
      ∫ ω, (∫ w, hairerI2Psi2Kernel N x y w * hairerPsiWickSquare N ρ a ξ ω w) *
          hairerPsiWickSquare N ρ a ξ ω y *
        ((∫ w, hairerI2Psi2Kernel N x y' w * hairerPsiWickSquare N ρ' b ξ' ω w) *
          hairerPsiWickSquare N ρ' b ξ' ω y') ∂P -
      hairerSunsetConstant N ρ' b * ∫ ω, (∫ w, hairerI2Psi2Kernel N x y w *
        hairerPsiWickSquare N ρ a ξ ω w) * hairerPsiWickSquare N ρ a ξ ω y ∂P -
      hairerSunsetConstant N ρ a * ∫ ω, (∫ w, hairerI2Psi2Kernel N x y' w *
        hairerPsiWickSquare N ρ' b ξ' ω w) * hairerPsiWickSquare N ρ' b ξ' ω y' ∂P +
      hairerSunsetConstant N ρ a * hairerSunsetConstant N ρ' b := hcov
  rw [hcov', hUVe, hUe, hVe, ea, eb]
  ring

end RegularityStructures.Phi43

end

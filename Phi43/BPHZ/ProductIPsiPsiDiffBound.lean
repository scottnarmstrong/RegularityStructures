/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiDiffDomination
public import Phi43.BPHZ.ProductIPsiPsiDiffDouble
public import Phi43.BPHZ.ProductIPsiPsiDiffField
import Mathlib.Tactic

/-!
# Second moment of the difference `Q_t Π_x I(Ψ)Ψ (x)` of two mollifications

`hairerIPsiPsiField_semigroup_sub_second_moment_le`: for `κ ∈ (0, 1/16)`, `0 < θ ≤ κ/2`,
`t ∈ (0, 1]`, uniformly in `ε, ε' ∈ (0, 1]` and `x`,
`E |∫ Q_t(x, y) (Π_x^{ρ,ε} I(Ψ)Ψ - Π_x^{ρ',ε'} I(Ψ)Ψ)(y) dy|² ≤
  C (ε ∨ ε')^(2θ) (t^(1/4))^(2 (1 - 2κ) + κ - 2θ)`.

Proof: the difference Fubini identity (`ipsiMix_sub_integral_sq_eq`), the domination
(`ipsiDiff_tested_dominated`), and the profile double bounds with parameters
`p = κ/4`, `γ = 1 - 5κ/4`, `δ = κ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem ipsiDiff_hρ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') : ∀ i, IsMollifier (![ρ, ρ'] i) := by
  intro i; fin_cases i
  · exact hρ
  · exact hρ'

private theorem ipsiDiff_hε {ε ε' : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1) (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1) :
    ∀ i, (![ε, ε'] : Fin 2 → ℝ) i ∈ Set.Ioc (0 : ℝ) 1 := by
  intro i; fin_cases i
  · exact hε
  · exact hε'

private theorem ipsiDiff_hξ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
    {ξ ξ' : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') :
    ∀ i, IsRegularisedNoise P W (![ρ, ρ'] i) (![ε, ε'] i) (![ξ, ξ'] i) := by
  intro i; fin_cases i
  · exact hξ
  · exact hξ'

private theorem ipsiDiff_rpow_mul_le {l a b c E : ℝ} (hl : 0 < l) (hl1 : l ≤ 1)
    (h : E ≤ a + b + c) : l ^ a * l ^ b * l ^ c ≤ l ^ E := by
  rw [← Real.rpow_add hl, ← Real.rpow_add hl]
  exact Real.rpow_le_rpow_of_exponent_ge hl hl1 h

/-- Pure algebra: the four majorant terms against `l ^ E`. -/
private theorem ipsiDiff_combine_alg {Cd M K1 K1' K2 K3 aa c1 c2 L1 L1' L2 L3 LE : ℝ} (hCd : 0 ≤ Cd)
    (hM : 0 ≤ M) (hK1 : 0 ≤ K1) (hK1' : 0 ≤ K1') (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (u1 : aa * L1 ≤ LE) (u1' : aa * L1' ≤ LE) (u2 : c1 * L2 ≤ LE) (u3 : c2 * L3 ≤ LE) :
    Cd * M * (aa * (4 * (K1 * L1) + 4 * (K1' * L1')) + c1 * (5 * (K2 * L2)) + c2 * (K3 * L3)) ≤
      Cd * (4 * K1 + 4 * K1' + 5 * K2 + K3) * M * LE := by
  have k1 := mul_le_mul_of_nonneg_left u1 hK1
  have k1' := mul_le_mul_of_nonneg_left u1' hK1'
  have k2 := mul_le_mul_of_nonneg_left u2 hK2
  have k3 := mul_le_mul_of_nonneg_left u3 hK3
  have h : aa * (4 * (K1 * L1) + 4 * (K1' * L1')) + c1 * (5 * (K2 * L2)) + c2 * (K3 * L3) ≤
      (4 * K1 + 4 * K1' + 5 * K2 + K3) * LE := by nlinarith [k1, k1', k2, k3]
  have := mul_le_mul_of_nonneg_left h (mul_nonneg hCd hM)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Second moment of the difference of `Q_t Π_x I(Ψ)Ψ (x)` for two mollifications.** -/
theorem hairerIPsiPsiField_semigroup_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ θ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1 / 16)
    (hθ : 0 < θ) (hθκ : θ ≤ κ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) * (t ^ (1 / 4 : ℝ)) ^ (2 * (1 - 2 * κ) + κ - 2 * θ) := by
  obtain ⟨Cd, hCd, hdom⟩ := ipsiDiff_tested_dominated.{u} N hρ hρ' (θ := θ) (p := κ / 4)
    (γ := 1 - 5 * κ / 4) (δ := κ) hθ (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hκ (by linarith) (by linarith)
  obtain ⟨K1, hK1, hI1⟩ := ipsi_majorant_integral_ab_le (a := κ / 4 + 2 * θ) (b := κ / 4)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨K1', hK1', hI1'⟩ := ipsi_majorant_integral_ab_le (a := κ / 4) (b := κ / 4 + 2 * θ)
    (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨K2, hK2, hI2⟩ := ipsi_majorant_integral_inv_le_of_exp (e := 1) (by norm_num)
  obtain ⟨K3, hK3, hI3⟩ := ipsi_majorant_integral_inv_le_of_exp (e := 1 + 2 * θ) (by linarith)
  refine ⟨Cd * (4 * K1 + 4 * K1' + 5 * K2 + K3), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  have hid := ipsiMix_sub_integral_sq_eq.{u} N (ρ := ![ρ, ρ']) (ipsiDiff_hρ hρ hρ') hW
    (ipsiDiff_hε hε hε') (ipsiDiff_hξ hξ hξ') ht x
  have hid' : ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y * hairerIPsiPsiField N ξ' x ω y) ^ 2 ∂P =
      ∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
        parabolicSemigroup.kernel t x q.2 *
        arrSd (fun i j => ∫ ω, hairerIPsiPsiField N (![ξ, ξ'] i) x ω q.1 *
          hairerIPsiPsiField N (![ξ, ξ'] j) x ω q.2 ∂P) := hid
  rw [hid']
  set A : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 4 + 2 * θ))) *
        (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 4)))) with hA
  set B : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      ((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 4))) *
        (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 4 + 2 * θ)))) with hB
  set D1 : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 : ℝ)) with hD1
  set D2 : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 + 2 * θ)) with hD2
  obtain ⟨iA, eA⟩ : Integrable A ∧ ∫ q, A q ≤ K1 * l ^ (-(κ / 4 + 2 * θ + κ / 4)) :=
    hI1 ht ht1 x
  obtain ⟨iB, eB⟩ : Integrable B ∧ ∫ q, B q ≤ K1' * l ^ (-(κ / 4 + (κ / 4 + 2 * θ))) :=
    hI1' ht ht1 x
  obtain ⟨iD1, eD1⟩ : Integrable D1 ∧ ∫ q, D1 q ≤ K2 * l ^ (-(1 : ℝ)) := hI2 ht ht1 x
  obtain ⟨iD2, eD2⟩ : Integrable D2 ∧ ∫ q, D2 q ≤ K3 * l ^ (-(1 + 2 * θ)) := hI3 ht ht1 x
  have hd := hdom hW hε hε' hξ hξ' ht ht1 x
  set M := max ε ε' with hM
  have hM0 : 0 ≤ M := le_max_of_le_left hε.1.le
  have hMp : 0 ≤ M ^ (2 * θ) := Real.rpow_nonneg hM0 _
  set aa := l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) with haadef
  set c1 := l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2 - 2 * θ) with hc1def
  set c2 := l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2) with hc2def
  have p1 : Integrable (fun q => 4 * A q + 4 * B q) := (iA.const_mul 4).add (iB.const_mul 4)
  have p2 : Integrable (fun q => aa * (4 * A q + 4 * B q)) := p1.const_mul aa
  have p3 : Integrable (fun q => c1 * (5 * D1 q)) := (iD1.const_mul 5).const_mul c1
  have p4 : Integrable (fun q => c2 * D2 q) := iD2.const_mul c2
  have p5 : Integrable (fun q => aa * (4 * A q + 4 * B q) + c1 * (5 * D1 q)) := p2.add p3
  have p6 : Integrable (fun q => aa * (4 * A q + 4 * B q) + c1 * (5 * D1 q) + c2 * D2 q) :=
    p5.add p4
  have hMi : Integrable (fun q => Cd * M ^ (2 * θ) *
      (aa * (4 * A q + 4 * B q) + c1 * (5 * D1 q) + c2 * D2 q)) := p6.const_mul _
  refine (Real.le_norm_self _).trans ((norm_integral_le_of_norm_le hMi ?_).trans ?_)
  · filter_upwards [hd] with q hq
    rw [Real.norm_eq_abs]
    exact hq
  rw [integral_const_mul, integral_add p5 p4, integral_add p2 p3, integral_const_mul aa,
    integral_add (iA.const_mul 4) (iB.const_mul 4)]
  simp only [integral_const_mul]
  have u1 : l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) * l ^ (-(κ / 4 + 2 * θ + κ / 4)) ≤
      l ^ (2 * (1 - 2 * κ) + κ - 2 * θ) :=
    ipsiDiff_rpow_mul_le hlam hlam1 (by linarith)
  have u1' : l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) * l ^ (-(κ / 4 + (κ / 4 + 2 * θ))) ≤
      l ^ (2 * (1 - 2 * κ) + κ - 2 * θ) :=
    ipsiDiff_rpow_mul_le hlam hlam1 (by linarith)
  have u2 : l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2 - 2 * θ) * l ^ (-(1 : ℝ)) ≤
      l ^ (2 * (1 - 2 * κ) + κ - 2 * θ) :=
    ipsiDiff_rpow_mul_le hlam hlam1 (by linarith)
  have u3 : l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2) * l ^ (-(1 + 2 * θ)) ≤
      l ^ (2 * (1 - 2 * κ) + κ - 2 * θ) :=
    ipsiDiff_rpow_mul_le hlam hlam1 (by linarith)
  refine le_trans ?_ (ipsiDiff_combine_alg hCd hMp hK1 hK1' hK2 hK3 u1 u1' u2 u3)
  gcongr

end RegularityStructures.Phi43

end

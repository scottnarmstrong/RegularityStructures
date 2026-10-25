/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ProductIPsiPsiSqDiffDomination
public import Phi43.BPHZ.ProductIPsiPsiSqDiffDouble
public import Phi43.BPHZ.ProductIPsiPsiSqDiffField
import Mathlib.Tactic

/-!
# Second moment of the difference `Q_t Π_x I(Ψ)(Ψ² - c₁) (x)` of two mollifications

`hairerIPsiPsiSqField_semigroup_sub_second_moment_le`: for `κ ∈ (0, 1/16)`, `0 < θ ≤ κ/2`,
`t ∈ (0, 1]`, uniformly in `ε, ε' ∈ (0, 1]` and `x`,
`E |∫ Q_t(x, y) (F^{ρ,ε} - F^{ρ',ε'})(y) dy|² ≤
  C (ε ∨ ε')^(2θ) (t^(1/4))^(2 (1/2 - 3κ) + κ - 2θ)`.

Proof: the difference Fubini identity (`ipsiMixSq_sub_integral_sq_eq`), the domination
(`ipsiDiffSq_tested_dominated`), and the profile double bounds with `p = κ/4`, `γ = 1 - 5κ/4`,
`δ = κ`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem ipsiDiffSq_hρ {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} (hρ : IsMollifier ρ)
    (hρ' : IsMollifier ρ') : ∀ i, IsMollifier (![ρ, ρ'] i) := by
  intro i; fin_cases i
  · exact hρ
  · exact hρ'

private theorem ipsiDiffSq_hε {ε ε' : ℝ} (hε : ε ∈ Set.Ioc (0 : ℝ) 1)
    (hε' : ε' ∈ Set.Ioc (0 : ℝ) 1) : ∀ i, (![ε, ε'] : Fin 2 → ℝ) i ∈ Set.Ioc (0 : ℝ) 1 := by
  intro i; fin_cases i
  · exact hε
  · exact hε'

private theorem ipsiDiffSq_hξ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ} {ε ε' : ℝ}
    {ξ ξ' : Ω → SpaceTime → ℝ} (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hξ' : IsRegularisedNoise P W ρ' ε' ξ') :
    ∀ i, IsRegularisedNoise P W (![ρ, ρ'] i) (![ε, ε'] i) (![ξ, ξ'] i) := by
  intro i; fin_cases i
  · exact hξ
  · exact hξ'

private theorem ipsiDiffSq_rpow_mul_le {l a b c E : ℝ} (hl : 0 < l) (hl1 : l ≤ 1)
    (h : E ≤ a + b + c) : l ^ a * l ^ b * l ^ c ≤ l ^ E := by
  rw [← Real.rpow_add hl, ← Real.rpow_add hl]
  exact Real.rpow_le_rpow_of_exponent_ge hl hl1 h

/-- Pure algebra: the six majorant terms against `l ^ E`. -/
private theorem ipsiDiffSq_combine_alg {Cd M K1 K1' K0 K02 K2 K3 aa c1 c2 IA IB I0 I02 IS1 IS2
    L1 L1' L0 L02 L2 L3 LE : ℝ} (hCd : 0 ≤ Cd) (hM : 0 ≤ M) (hK1 : 0 ≤ K1) (hK1' : 0 ≤ K1')
    (hK0 : 0 ≤ K0) (hK02 : 0 ≤ K02) (hK2 : 0 ≤ K2) (hK3 : 0 ≤ K3)
    (eA : IA ≤ K1 * L1) (eB : IB ≤ K1' * L1') (e0 : I0 ≤ K0 * L0) (e02 : I02 ≤ K02 * L02)
    (e2 : IS1 ≤ K2 * L2) (e3 : IS2 ≤ K3 * L3) (haa : 0 ≤ aa) (hc1 : 0 ≤ c1) (hc2 : 0 ≤ c2)
    (u1 : aa * L1 ≤ LE) (u1' : aa * L1' ≤ LE) (u0 : aa * L0 ≤ LE) (u02 : aa * L02 ≤ LE)
    (u2 : c1 * L2 ≤ LE) (u3 : c2 * L3 ≤ LE) :
    Cd * M * (aa * (4 * IA + 4 * IB + I0 + I02) + c1 * (5 * IS1) + c2 * IS2) ≤
      Cd * (4 * K1 + 4 * K1' + K0 + K02 + 5 * K2 + K3) * M * LE := by
  have k1 := mul_le_mul_of_nonneg_left u1 hK1
  have k1' := mul_le_mul_of_nonneg_left u1' hK1'
  have k0 := mul_le_mul_of_nonneg_left u0 hK0
  have k02 := mul_le_mul_of_nonneg_left u02 hK02
  have k2 := mul_le_mul_of_nonneg_left u2 hK2
  have k3 := mul_le_mul_of_nonneg_left u3 hK3
  have m1 := mul_le_mul_of_nonneg_left eA haa
  have m1' := mul_le_mul_of_nonneg_left eB haa
  have m0 := mul_le_mul_of_nonneg_left e0 haa
  have m02 := mul_le_mul_of_nonneg_left e02 haa
  have m2 := mul_le_mul_of_nonneg_left e2 hc1
  have m3 := mul_le_mul_of_nonneg_left e3 hc2
  have h : aa * (4 * IA + 4 * IB + I0 + I02) + c1 * (5 * IS1) + c2 * IS2 ≤
      (4 * K1 + 4 * K1' + K0 + K02 + 5 * K2 + K3) * LE := by
    nlinarith only [k1, k1', k0, k02, k2, k3, m1, m1', m0, m02, m2, m3]
  have := mul_le_mul_of_nonneg_left h (mul_nonneg hCd hM)
  calc _ ≤ _ := this
    _ = _ := by ring

/-- **Second moment of the difference of `Q_t Π_x I(Ψ)(Ψ² - c₁) (x)` for two mollifications.** -/
theorem hairerIPsiPsiSqField_semigroup_sub_second_moment_le (N : ℕ) {ρ ρ' : ℝ × (Fin 3 → ℝ) → ℝ}
    (hρ : IsMollifier ρ) (hρ' : IsMollifier ρ') {κ θ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1 / 16)
    (hθ : 0 < θ) (hθκ : θ ≤ κ / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
      {W : (SpaceTime → ℝ) → Ω → ℝ} {ε ε' : ℝ} {ξ ξ' : Ω → SpaceTime → ℝ},
      IsWhiteNoise P W → ε ∈ Set.Ioc (0 : ℝ) 1 → ε' ∈ Set.Ioc (0 : ℝ) 1 →
      IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ' ε' ξ' →
      ∀ {t : ℝ}, 0 < t → t ≤ 1 → ∀ x : ParabolicSpace,
        ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y *
              hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y *
              hairerIPsiPsiSqField N ξ' (hairerWickConstant N ρ' ε') x ω y) ^ 2 ∂P ≤
          C * (max ε ε') ^ (2 * θ) *
            (t ^ (1 / 4 : ℝ)) ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) := by
  obtain ⟨Cd, hCd, hdom⟩ := ipsiDiffSq_tested_dominated.{u} N hρ hρ' (θ := θ) (p := κ / 4)
    (γ := 1 - 5 * κ / 4) (δ := κ) hθ (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith) hκ (by linarith) (by linarith)
  obtain ⟨K1, hK1, hI1⟩ := ipsi_majorant_integral_ab_inv_le (a := κ / 4 + 2 * θ) (b := κ / 4)
    (ν := 1) (by linarith) (by linarith) (by linarith) (by norm_num)
  obtain ⟨K1', hK1', hI1'⟩ := ipsi_majorant_integral_ab_inv_le (a := κ / 4) (b := κ / 4 + 2 * θ)
    (ν := 1) (by linarith) (by linarith) (by linarith) (by norm_num)
  obtain ⟨K0, hK0, hI0⟩ := ipsi_majorant_integral_ab_inv_le (a := κ / 4) (b := κ / 4)
    (ν := 1) (by linarith) (by linarith) (by linarith) (by norm_num)
  obtain ⟨K02, hK02, hI02⟩ := ipsi_majorant_integral_ab_inv_le (a := κ / 4) (b := κ / 4)
    (ν := 1 + 2 * θ) (by linarith) (by linarith) (by linarith) (by linarith)
  obtain ⟨K2, hK2, hI2⟩ := ipsi_majorant_integral_inv_le_of_exp (e := 2) (by norm_num)
  obtain ⟨K3, hK3, hI3⟩ := ipsi_majorant_integral_inv_le_of_exp (e := 2 + 2 * θ) (by linarith)
  refine ⟨Cd * (4 * K1 + 4 * K1' + K0 + K02 + 5 * K2 + K3), by positivity, ?_⟩
  intro Ω _ P W ε ε' ξ ξ' hW hε hε' hξ hξ' t ht ht1 x
  have hlam : 0 < t ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos ht _
  have hlam1 : t ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  set l := t ^ (1 / 4 : ℝ) with hl
  have hid := ipsiMixSq_sub_integral_sq_eq.{u} N (ρ := ![ρ, ρ']) (ipsiDiffSq_hρ hρ hρ') hW
    (ipsiDiffSq_hε hε hε') (ipsiDiffSq_hξ hξ hξ') ht x
  have hid' : ∫ ω, ((∫ y, parabolicSemigroup.kernel t x y *
              hairerIPsiPsiSqField N ξ (hairerWickConstant N ρ ε) x ω y) -
            ∫ y, parabolicSemigroup.kernel t x y *
              hairerIPsiPsiSqField N ξ' (hairerWickConstant N ρ' ε') x ω y) ^ 2 ∂P =
      ∫ q : ParabolicSpace × ParabolicSpace, parabolicSemigroup.kernel t x q.1 *
        parabolicSemigroup.kernel t x q.2 *
        arrSd (fun i j => ∫ ω, hairerIPsiPsiSqField N (![ξ, ξ'] i)
            (hairerWickConstant N (![ρ, ρ'] i) (![ε, ε'] i)) x ω q.1 *
          hairerIPsiPsiSqField N (![ξ, ξ'] j)
            (hairerWickConstant N (![ρ, ρ'] j) (![ε, ε'] j)) x ω q.2 ∂P) := hid
  rw [hid']
  set A : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 4 + 2 * θ))) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 4)))) *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-((1 : ℝ)))) with hA
  set B : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 4))) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 4 + 2 * θ)))) *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-((1 : ℝ)))) with hB
  set T0 : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 4))) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 4)))) *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-((1 : ℝ)))) with hT0
  set T02 : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      (((1 + torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj x) ^ (-(κ / 4))) *
          (1 + torusParabolicSize (spaceTimeProj q.2 - spaceTimeProj x) ^ (-(κ / 4)))) *
        torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(1 + 2 * θ))) with hT02
  set S1 : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(2 : ℝ)) with hS1
  set S2 : ParabolicSpace × ParabolicSpace → ℝ := fun q => ipsiWeightedKernel t x q.1 *
    ipsiWeightedKernel t x q.2 *
      torusParabolicSize (spaceTimeProj q.1 - spaceTimeProj q.2) ^ (-(2 + 2 * θ)) with hS2
  obtain ⟨iA, eA⟩ : Integrable A ∧ ∫ q, A q ≤ K1 * l ^ (-(κ / 4 + 2 * θ + κ / 4 + 1)) :=
    hI1 ht ht1 x
  obtain ⟨iB, eB⟩ : Integrable B ∧ ∫ q, B q ≤ K1' * l ^ (-(κ / 4 + (κ / 4 + 2 * θ) + 1)) :=
    hI1' ht ht1 x
  obtain ⟨i0, e0⟩ : Integrable T0 ∧ ∫ q, T0 q ≤ K0 * l ^ (-(κ / 4 + κ / 4 + 1)) := hI0 ht ht1 x
  obtain ⟨i02, e02⟩ : Integrable T02 ∧ ∫ q, T02 q ≤ K02 * l ^ (-(κ / 4 + κ / 4 + (1 + 2 * θ))) :=
    hI02 ht ht1 x
  obtain ⟨iS1, eS1⟩ : Integrable S1 ∧ ∫ q, S1 q ≤ K2 * l ^ (-(2 : ℝ)) := hI2 ht ht1 x
  obtain ⟨iS2, eS2⟩ : Integrable S2 ∧ ∫ q, S2 q ≤ K3 * l ^ (-(2 + 2 * θ)) := hI3 ht ht1 x
  have hd := hdom hW hε hε' hξ hξ' ht ht1 x
  set M := max ε ε' with hM
  have hM0 : 0 ≤ M := le_max_of_le_left hε.1.le
  have hMp : 0 ≤ M ^ (2 * θ) := Real.rpow_nonneg hM0 _
  set aa := l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) with haadef
  set c1 := l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2 - 2 * θ) with hc1def
  set c2 := l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2) with hc2def
  have haa : 0 ≤ aa := by positivity
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have p1a : Integrable (fun q => 4 * A q + 4 * B q) := (iA.const_mul 4).add (iB.const_mul 4)
  have p1b : Integrable (fun q => 4 * A q + 4 * B q + T0 q) := p1a.add i0
  have p1 : Integrable (fun q => 4 * A q + 4 * B q + T0 q + T02 q) := p1b.add i02
  have p2 : Integrable (fun q => aa * (4 * A q + 4 * B q + T0 q + T02 q)) := p1.const_mul aa
  have p3 : Integrable (fun q => c1 * (5 * S1 q)) := (iS1.const_mul 5).const_mul c1
  have p4 : Integrable (fun q => c2 * S2 q) := iS2.const_mul c2
  have p5 : Integrable (fun q => aa * (4 * A q + 4 * B q + T0 q + T02 q) + c1 * (5 * S1 q)) :=
    p2.add p3
  have p6 : Integrable (fun q => aa * (4 * A q + 4 * B q + T0 q + T02 q) + c1 * (5 * S1 q) +
      c2 * S2 q) := p5.add p4
  have hMi : Integrable (fun q => Cd * M ^ (2 * θ) *
      (aa * (4 * A q + 4 * B q + T0 q + T02 q) + c1 * (5 * S1 q) + c2 * S2 q)) :=
    p6.const_mul _
  refine (Real.le_norm_self _).trans ((norm_integral_le_of_norm_le hMi ?_).trans ?_)
  · filter_upwards [hd] with q hq
    rw [Real.norm_eq_abs]
    exact hq
  rw [integral_const_mul, integral_add p5 p4, integral_add p2 p3, integral_const_mul aa,
    integral_add p1b i02, integral_add p1a i0, integral_add (iA.const_mul 4) (iB.const_mul 4)]
  simp only [integral_const_mul]
  have u1 : l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) * l ^ (-(κ / 4 + 2 * θ + κ / 4 + 1)) ≤
      l ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) :=
    ipsiDiffSq_rpow_mul_le hlam hlam1 (by linarith)
  have u1' : l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) *
      l ^ (-(κ / 4 + (κ / 4 + 2 * θ) + 1)) ≤ l ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) :=
    ipsiDiffSq_rpow_mul_le hlam hlam1 (by linarith)
  have u0 : l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) * l ^ (-(κ / 4 + κ / 4 + 1)) ≤
      l ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) :=
    ipsiDiffSq_rpow_mul_le hlam hlam1 (by linarith)
  have u02 : l ^ (1 - 5 * κ / 4) * l ^ (1 - 5 * κ / 4) *
      l ^ (-(κ / 4 + κ / 4 + (1 + 2 * θ))) ≤ l ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) :=
    ipsiDiffSq_rpow_mul_le hlam hlam1 (by linarith)
  have u2 : l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2 - 2 * θ) * l ^ (-(2 : ℝ)) ≤
      l ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) :=
    ipsiDiffSq_rpow_mul_le hlam hlam1 (by linarith)
  have u3 : l ^ ((3 - κ) / 2) * l ^ ((3 - κ) / 2) * l ^ (-(2 + 2 * θ)) ≤
      l ^ (2 * (1 / 2 - 3 * κ) + κ - 2 * θ) :=
    ipsiDiffSq_rpow_mul_le hlam hlam1 (by linarith)
  exact ipsiDiffSq_combine_alg hCd hMp hK1 hK1' hK0 hK02 hK2 hK3 eA eB e0 e02 eS1 eS2 haa hc1 hc2
    u1 u1' u0 u02 u2 u3

end RegularityStructures.Phi43

end

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyDiffMoment
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitCompact
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffInduction
public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments

/-!
# The `Π` half on a compact subset of the unit box (step C1)

`piHalfStmt_unitBox`: for compact `T ⊆ [0,1]⁴`, the `Π` half holds with constants `qPi`, `KPi`
depending only on the structure data and on `p`.  The `Γ`-half inputs are the proved
`randomModel_gammaNormOn_moment` and `randomModel_gammaDiffNormOn_moment` at moment
`2p`.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Lowering the order of a `Γ`-coefficient moment premise. -/
theorem lower_gammaMoment {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} (hf : Measurable f) {m q : ℕ} (hm : 1 ≤ m)
    (hmq : m ≤ q) {b : ℝ}
    (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤ ENNReal.ofReal b ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ m ∂P ≤ ENNReal.ofReal b ^ m :=
  probability_natMoment_le_of_higher hf.aemeasurable hm hmq _ h

theorem piHalfStmt_unitBox (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (hκ : 0 < κbar)
    (hθ : 0 ≤ θ) (Dπ : Set ι) (DΓ : Set (ι × ι)) (T : Set ParabolicSpace)
    (hT : IsCompact T) (hTbox : T ⊆ piHalfUnitBox) (p : ℕ) (hp : 1 ≤ p) :
    ∃ qPi : ℕ, p ≤ qPi ∧ ∃ KPi : ℝ → ℝ, (∀ C, 0 ≤ KPi C) ∧
      PiHalfStmt.{u} 𝒯 γ κbar θ Dπ DΓ T p qPi KPi := by
  obtain ⟨qΓ, hqΓ, hΓ⟩ := randomModel_gammaNormOn_moment.{_, u} 𝒯 γ κbar θ hκ hθ DΓ T hT (2 * p)
    (by omega)
  obtain ⟨qD, hqD, hΓd⟩ := randomModel_gammaDiffNormOn_moment.{_, u} 𝒯 γ κbar θ hκ hθ DΓ T hT
    (2 * p) (by omega)
  choose KΓ hKΓ0 hKΓ using hΓ
  choose KD hKD0 hKD using hΓd
  set q : ℕ := max (2 * p) ⌈12 / κbar⌉₊ with hq
  have hq2 : 2 * p ≤ q := le_max_left _ _
  have hq1 : 1 ≤ q := by omega
  have hqκ : 12 ≤ (q : ℝ) * κbar := by
    have h1 : 12 / κbar ≤ (q : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
    rwa [div_le_iff₀ hκ] at h1
  set qPi : ℕ := max (max qΓ qD) (2 * q) with hqPi
  have hqΓPi : qΓ ≤ qPi := le_trans (le_max_left _ _) (le_max_left _ _)
  have hqDPi : qD ≤ qPi := le_trans (le_max_right _ _) (le_max_left _ _)
  have hq2Pi : 2 * q ≤ qPi := le_max_right _ _
  obtain ⟨Kc⟩ := exists_piHalfConsts.{u} 𝒯 γ κbar θ hκ Dπ DΓ q qPi hq1 hq2Pi
  set MΓ : ℝ → ℝ := fun Cbar => 2 ^ (2 * p) * (1 + KΓ Cbar * Cbar ^ (2 * p)) with hMΓ
  have hMΓ0 : ∀ Cbar, 0 ≤ MΓ Cbar := by
    intro Cbar
    have h1 := hKΓ0 Cbar
    have h2 : 0 ≤ Cbar ^ (2 * p) := (even_two_mul p).pow_nonneg Cbar
    simp only [hMΓ]; positivity
  choose Ks hKs0 hKs using fun Cbar : ℝ => piHalf_single_moment.{u} 𝒯 γ κbar θ Dπ DΓ q qPi Kc T
    hTbox p hp hq2 hqκ (max Cbar 0) (MΓ (max Cbar 0)) (hMΓ0 _)
  choose Kf hKf0 hKf using fun Cbar : ℝ => piHalf_diff_moment.{u} 𝒯 γ κbar θ Dπ DΓ q qPi Kc T
    hTbox p hp hq2 hqκ (max Cbar 0) (MΓ (max Cbar 0)) (KD (max Cbar 0)) (le_max_right _ _)
    (hMΓ0 _) (hKD0 _)
  refine ⟨qPi, by omega, fun Cbar => max (Ks Cbar) (Kf Cbar),
    fun Cbar => le_trans (hKs0 Cbar) (le_max_left _ _), ?_⟩
  unfold PiHalfStmt
  intro Cbar Ω _ P _ Z₁ Z₂ C ε hC hCb hε hV₁ hV₂ h1 h2 h3 h4 h5 h6 h7 h8
  have hCb' : C ≤ max Cbar 0 := hCb.trans (le_max_left _ _)
  have prem : PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε := ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hV₁' : IsContinuousRandomModelWithFieldsOn Z₁ T := hV₁
  have hV₂' : IsContinuousRandomModelWithFieldsOn Z₂ T := hV₂
  have hε' : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
  have hVZ : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      IsContinuousRandomModelWithFieldsOn Z T := by
    intro Z hZ
    rcases hZ with rfl | hZ
    · exact hV₁'
    · rw [mem_singleton_iff] at hZ; exact hZ ▸ hV₂'
  have hGs : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      ∫⁻ ω, (1 + (Z ω).gammaNormOn γ T) ^ (2 * p) ∂P ≤ ENNReal.ofReal (MΓ (max Cbar 0)) := by
    intro Z hZ
    have hmom := (hKΓ (max Cbar 0) P Z C hC hCb' (hVZ Z hZ)
      (fun i j hij hi hj ω x y => prem.detGamma Z hZ i j hij hi hj ω x y)
      (fun i j hij hi hj x y => lower_gammaMoment ((hVZ Z hZ).1.2.1 i j x y) (by omega) hqΓPi
        (prem.momGamma Z hZ i j hij hi hj x y))).2
    have hB : 0 ≤ KΓ (max Cbar 0) * C ^ (2 * p) :=
      mul_nonneg (hKΓ0 _) (pow_nonneg hC _)
    refine (lintegral_one_add_pow_le (2 * p) hB hmom).trans (ENNReal.ofReal_le_ofReal ?_)
    simp only [hMΓ]
    have := pow_le_pow_left₀ hC hCb' (2 * p)
    have h0 := hKΓ0 (max Cbar 0)
    gcongr
  have hGD := (hKD (max Cbar 0) P Z₁ Z₂ C ε hC hCb' hε hV₁ hV₂
    (fun Z hZ i j hij hi hj ω x y => prem.detGamma Z hZ i j hij hi hj ω x y)
    (fun i j hij hi hj ω x y => prem.detGammaDiff i j hij hi hj ω x y)
    (fun Z hZ i j hij hi hj x y => lower_gammaMoment ((hVZ Z hZ).1.2.1 i j x y) (by omega) hqDPi
      (prem.momGamma Z hZ i j hij hi hj x y))
    (fun i j hij hi hj x y => lower_gammaMoment
      (((hVZ Z₁ (by simp)).1.2.1 i j x y).sub ((hVZ Z₂ (by simp)).1.2.1 i j x y))
      (by omega) hqDPi (prem.momGammaDiff i j hij hi hj x y))).2
  have hGD' : ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T ^ (2 * p) ∂P ≤
      ENNReal.ofReal (KD (max Cbar 0) * ((C * ε ^ θ) ^ p) ^ 2) := by
    rw [← pow_mul, mul_comm p 2]; exact hGD
  refine ⟨?_, ?_, ?_⟩
  · intro Z hZ
    refine ⟨((hVZ Z hZ).measurable_piNormOn γ).aemeasurable, ?_⟩
    have := hKs Cbar P Z C hC hCb' (hVZ Z hZ) (prem.toSingle hZ) (hGs Z hZ)
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hC p)
  · exact (hV₁'.measurable_piDiffNormOn hV₂' γ).aemeasurable
  · have := hKf Cbar P Z₁ Z₂ C ε hC hCb' hε hV₁ hV₂ prem (hGs Z₁ (by simp)) hGD'
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    exact mul_le_mul_of_nonneg_right (le_max_right _ _) (pow_nonneg hε' p)

end RegularityStructures

end

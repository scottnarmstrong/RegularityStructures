/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyConsts
public import RegularityStructures.Probability.ModelKolmogorovFieldContinuity

/-!
# The unit-box `Π` moment for a single model

`piHalf_single_moment`: with the constants of `PiHalfConsts`, a `Γ`-norm moment bound of order `2p`
and `IsContinuousRandomModelWithFieldsOn`, `E ‖Π‖_{γ;T}^p ≤ K₀ C^p` for `T` in the unit box.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem piHalfScale_mem (j : ℕ) : piHalfScale j ∈ Ioc (0 : ℝ) 1 :=
  ⟨piHalfScale_pos j, by unfold piHalfScale; exact pow_le_one₀ (by norm_num) (by norm_num)⟩

theorem measurable_regPi_scale_of_continuousWithFields {Ω : Type*} [MeasurableSpace Ω] {ι' : Type*} [Fintype ι']
    [DecidableEq ι'] {𝒯 : RegularityStructure ι'} {Z : Ω → Model 𝒯 parabolicSemigroup}
    {S : Set ParabolicSpace} (hZ : IsContinuousRandomModelWithFieldsOn Z S) (ω : Ω)
    (x : ParabolicSpace) (k : ι') (j : ℕ) :
    Measurable (fun w => (Z ω).regPi x (Pi.single k 1) (piHalfScale j) w) := by
  have h := (hZ.2 ω k x).comp_continuous (continuous_const.prodMk continuous_id)
    (fun w => ⟨piHalfScale_mem j, mem_univ w⟩)
  exact h.measurable

theorem piHalf_single_moment (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (q qPi : ℕ) (K : PiHalfConsts.{u} 𝒯 γ κbar θ Dπ DΓ q qPi)
    (T : Set ParabolicSpace) (hTbox : T ⊆ piHalfUnitBox) (p : ℕ) (hp : 1 ≤ p)
    (hpq : 2 * p ≤ q) (hqκ : 12 ≤ (q : ℝ) * κbar) (Cbar MΓ : ℝ)
    (hMΓ : 0 ≤ MΓ) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : Ω → Model 𝒯 parabolicSemigroup) (C : ℝ), 0 ≤ C → C ≤ Cbar →
        IsContinuousRandomModelWithFieldsOn Z T →
        PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ qPi P Z C →
        ∫⁻ ω, (1 + (Z ω).gammaNormOn γ T) ^ (2 * p) ∂P ≤ ENNReal.ofReal MΓ →
        ∫⁻ ω, (Z ω).piNormOn γ T ^ p ∂P ≤ ENNReal.ofReal (K₀ * C ^ p) := by
  have hq1 : 1 ≤ q := by omega
  have hKR0 : 0 ≤ ∑ k, K.KR k := Finset.sum_nonneg fun k _ => K.hKR k
  have hKd0 : 0 ≤ ∑ k, K.Kdet k := Finset.sum_nonneg fun k _ => K.hKdet k
  have hm0 : 0 ≤ max 1 Cbar := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨K₀, hK₀, hsk⟩ := piHalf_moment_le_of_dyadic_cells_of_hyps.{u} 𝒯 γ κbar Dπ T p q hp hpq
    hqκ (piHalfCellCount T) ((2 : ℝ) ^ 24)
    (K.c₀ * ((Fintype.card ι : ℝ) * ∑ k, K.KR k) * max 1 Cbar) (K.c₀ * (∑ k, K.Kdet k) * max 1 Cbar)
    MΓ (by positivity)
    (mul_nonneg (mul_nonneg K.hc₀ (mul_nonneg (Nat.cast_nonneg _) hKR0)) hm0)
    (mul_nonneg (mul_nonneg K.hc₀ hKd0) hm0) hMΓ (fun j => piHalfCellCount_le T j)
  refine ⟨K₀, hK₀, fun {Ω} _ P _ Z C hC hCb hV hH hG => ?_⟩
  have hV' : IsContinuousRandomModelWithFieldsOn Z T := hV
  have hord : parabolicSemigroup.order = 4 := rfl
  have hmOff : ∀ k j x₀, Measurable (fun z : Ω × ParabolicSpace =>
      (Z z.1).regPi x₀ (Pi.single k 1) (piHalfScale j) z.2) := fun k j x₀ =>
    hV'.offDiagonal_regPi_jointMeasurable k x₀ (piHalfScale_mem j)
  have hpartM : ∀ j k c, Measurable (fun ω => piHalfCellRandPartA 𝒯 Dπ DΓ K.nEnv C (piHalfScale j)
      (piHalfCellRep T j c) k (Z ω)) := fun j k c =>
    measurable_piHalfCellRandPartA_omega Dπ DΓ K.nEnv C _ _ k (hmOff k j _)
  have hRm : ∀ j i c, AEMeasurable (fun ω => piHalfCellRand 𝒯 Dπ DΓ K.nEnv T C K.c₀ (Z ω) j i c) P :=
    fun j i c => (Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
      (hpartM j k c).const_mul _) _).aemeasurable
  have hGm : AEMeasurable (fun ω => (Z ω).gammaNormOn γ T) P :=
    (hV'.measurable_gammaNormOn γ).aemeasurable
  have hfin : ∀ᵐ ω ∂P, (Z ω).gammaNormOn γ T < ⊤ := by
    have h1 : ∫⁻ ω, (1 + (Z ω).gammaNormOn γ T) ^ (2 * p) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hG
    filter_upwards [ae_lt_top' ((aemeasurable_const.add hGm).pow_const (2 * p)) h1] with ω hω
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have h2p : 2 * p ≠ 0 := by omega
    simp [hcon, h2p] at hω
  refine hsk P Z (fun ω => (Z ω).gammaNormOn γ T)
    (fun j i c ω => piHalfCellRand 𝒯 Dπ DΓ K.nEnv T C K.c₀ (Z ω) j i c)
    (piHalfCellDet 𝒯 K.Kdet K.c₀ C) C hC hGm hRm hG
    (fun i hi hγ ω t ht x _ => hH.piDet i hi hγ ω t ht x) ?_ ?_ ?_
  · -- deterministic part
    intro j i _ _
    unfold piHalfCellDet
    have hs0 := (piHalfScale_pos j).le
    have h1 : ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), K.Kdet k ≤ ∑ k, K.Kdet k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => K.hKdet k
    have h2 : max 1 C ≤ max 1 Cbar := max_le_max le_rfl hCb
    have h3 : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), K.Kdet k :=
      Finset.sum_nonneg fun k _ => K.hKdet k
    have h4 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
    have h5 := K.hc₀
    calc _ ≤ K.c₀ * (∑ k, K.Kdet k) * max 1 C * C * piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order) := by
          gcongr
      _ ≤ _ := by
          gcongr
  · -- moments
    intro j i hi hγ c hc
    have hs := piHalfScale_mem j
    have hmom := (lintegral_piHalfCellRand_pow_le 𝒯 Dπ DΓ K.nEnv T κbar C K.c₀ q hq1 K.KR K.hKR
      K.hc₀ hC Z j i c (fun k => (hpartM j k c).aemeasurable) (fun k hk => by
        have hkγ : 𝒯.deg k < γ := lt_of_le_of_lt (Finset.mem_filter.1 hk).2 hγ
        exact K.hRk k hkγ P Z C hC hH hs _ (hmOff k j _)
          (fun j' w => hV.1.1 j' w _ hs.1) (fun j' w => hV.1.2.1 k j' _ w))).2
    refine hmom.trans ?_
    rw [hord]
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
    have h2 : max 1 C ≤ max 1 Cbar := max_le_max le_rfl hCb
    have hs0 := Real.rpow_nonneg (piHalfScale_pos j).le ((𝒯.deg i + κbar) / 4)
    have h5 := K.hc₀
    have h6 : 0 ≤ ∑ k, K.KR k := hKR0
    calc _ = (K.c₀ * ((Fintype.card ι : ℝ) * ∑ k, K.KR k)) * max 1 C * C *
            piHalfScale j ^ ((𝒯.deg i + κbar) / 4) := by ring
      _ ≤ (K.c₀ * ((Fintype.card ι : ℝ) * ∑ k, K.KR k)) * max 1 Cbar * C *
            piHalfScale j ^ ((𝒯.deg i + κbar) / 4) := by gcongr
      _ = _ := by ring
  · -- pathwise
    filter_upwards [hfin] with ω hω
    intro i hi hγ j u hu x hx
    have hGB : (Z ω).GammaBoundOn γ ((Z ω).gammaNormOn γ T).toReal T := by
      have := ((Z ω).gammaNormOn_le_iff (γ := γ) (S := T) ((Z ω).gammaNormOn γ T).toNNReal).1
        (by rw [ENNReal.coe_toNNReal hω.ne])
      exact this
    have hb := K.hpw (Z ω) T hTbox _ C ENNReal.toReal_nonneg hC hGB
      (fun x _ k j => measurable_regPi_scale_of_continuousWithFields hV ω x k j) i hγ j u hu x hx
    refine ⟨piHalfCellOf T j ⟨x, hx⟩, piHalfCellOf_lt T j ⟨x, hx⟩, ?_⟩
    have h1 : ENNReal.ofReal (1 + ((Z ω).gammaNormOn γ T).toReal) = 1 + (Z ω).gammaNormOn γ T := by
      rw [ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω.ne]
      simp
    rw [h1] at hb
    exact hb

end RegularityStructures

end

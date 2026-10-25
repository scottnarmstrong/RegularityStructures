/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblySingle
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyRandDiff
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblySkeletonDiff

/-!
# The unit-box `Π` difference moment

`piHalf_diff_moment`: with the constants of `PiHalfConsts`, moment bounds of order `2p` for the
`Γ`-norm of the first model and the `Γ`-difference norm, and `IsContinuousRandomModelWithFieldsOn`,
`E ‖Π¹ - Π²‖_{γ;T}^p ≤ K₀ (C ε^θ)^p` for `T` in the unit box.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem piHalf_diff_moment (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (q qPi : ℕ) (K : PiHalfConsts.{u} 𝒯 γ κbar θ Dπ DΓ q qPi)
    (T : Set ParabolicSpace) (hTbox : T ⊆ piHalfUnitBox) (p : ℕ) (hp : 1 ≤ p)
    (hpq : 2 * p ≤ q) (hqκ : 12 ≤ (q : ℝ) * κbar) (Cbar MΓ MΓ' : ℝ)
    (hCbar : 0 ≤ Cbar) (hMΓ : 0 ≤ MΓ) (hMΓ' : 0 ≤ MΓ') :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ), 0 ≤ C → C ≤ Cbar → 0 ≤ ε →
        IsContinuousRandomModelWithFieldsOn Z₁ T →
        IsContinuousRandomModelWithFieldsOn Z₂ T →
        PiHalfPrem 𝒯 γ κbar θ Dπ DΓ qPi P Z₁ Z₂ C ε →
        ∫⁻ ω, (1 + (Z₁ ω).gammaNormOn γ T) ^ (2 * p) ∂P ≤ ENNReal.ofReal MΓ →
        ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T ^ (2 * p) ∂P ≤
          ENNReal.ofReal (MΓ' * ((C * ε ^ θ) ^ p) ^ 2) →
        ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ T ^ p ∂P ≤
          ENNReal.ofReal (K₀ * (C * ε ^ θ) ^ p) := by
  have hq1 : 1 ≤ q := by omega
  have hKR0 : 0 ≤ ∑ k, K.KR k := Finset.sum_nonneg fun k _ => K.hKR k
  have hKRd0 : 0 ≤ ∑ k, K.KRd k := Finset.sum_nonneg fun k _ => K.hKRd k
  have hKd0 : 0 ≤ ∑ k, K.Kdet k := Finset.sum_nonneg fun k _ => K.hKdet k
  have hKdD0 : 0 ≤ ∑ k, K.KdetD k := Finset.sum_nonneg fun k _ => K.hKdetD k
  have hm0 : 0 ≤ max 1 Cbar := le_trans zero_le_one (le_max_left _ _)
  obtain ⟨K₀, hK₀, hsk⟩ := piHalfDiff_moment_le_of_dyadic_cells_of_hyps.{u} 𝒯 γ κbar Dπ T p q hp
    hpq hqκ (piHalfCellCount T) ((2 : ℝ) ^ 24)
    (K.c₀d * ((Fintype.card ι : ℝ) * ∑ k, K.KRd k) * max 1 Cbar)
    (K.c₀d * (∑ k, K.KdetD k) * max 1 Cbar)
    (K.c₀d * ((Fintype.card ι : ℝ) * ∑ k, K.KR k) * max 1 Cbar)
    (K.c₀d * (∑ k, K.Kdet k) * max 1 Cbar) MΓ MΓ' Cbar (by positivity)
    (mul_nonneg (mul_nonneg K.hc₀d (mul_nonneg (Nat.cast_nonneg _) hKRd0)) hm0)
    (mul_nonneg (mul_nonneg K.hc₀d hKdD0) hm0)
    (mul_nonneg (mul_nonneg K.hc₀d (mul_nonneg (Nat.cast_nonneg _) hKR0)) hm0)
    (mul_nonneg (mul_nonneg K.hc₀d hKd0) hm0) hMΓ hMΓ' hCbar
    (fun j => piHalfCellCount_le T j)
  refine ⟨K₀, hK₀, fun {Ω} _ P _ Z₁ Z₂ C ε hC hCb hε hV₁ hV₂ hH hG hGd => ?_⟩
  have hV₁' : IsContinuousRandomModelWithFieldsOn Z₁ T := hV₁
  have hV₂' : IsContinuousRandomModelWithFieldsOn Z₂ T := hV₂
  have hord : parabolicSemigroup.order = 4 := rfl
  have hC' : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
  have hmem₁ : Z₁ ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)) := by simp
  have hmem₂ : Z₂ ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)) := by simp
  have hmOff₁ : ∀ k j x₀, Measurable (fun z : Ω × ParabolicSpace =>
      (Z₁ z.1).regPi x₀ (Pi.single k 1) (piHalfScale j) z.2) := fun k j x₀ =>
    hV₁'.offDiagonal_regPi_jointMeasurable k x₀ (piHalfScale_mem j)
  have hmOff₂ : ∀ k j x₀, Measurable (fun z : Ω × ParabolicSpace =>
      (Z₂ z.1).regPi x₀ (Pi.single k 1) (piHalfScale j) z.2) := fun k j x₀ =>
    hV₂'.offDiagonal_regPi_jointMeasurable k x₀ (piHalfScale_mem j)
  have hpartM₁ : ∀ j k c, Measurable (fun ω => piHalfCellDiffRandPartA 𝒯 Dπ DΓ K.nEnv C ε θ
      (piHalfScale j) (piHalfCellRep T j c) k (Z₁ ω) (Z₂ ω)) := fun j k c =>
    measurable_piHalfCellDiffRandPartA_omega Dπ DΓ K.nEnv C ε θ _ _ k
      ((hmOff₁ k j _).sub (hmOff₂ k j _))
  have hpartM₂ : ∀ j k c, Measurable (fun ω => piHalfCellRandPartA 𝒯 Dπ DΓ K.nEnv C
      (piHalfScale j) (piHalfCellRep T j c) k (Z₂ ω)) := fun j k c =>
    measurable_piHalfCellRandPartA_omega Dπ DΓ K.nEnv C _ _ k (hmOff₂ k j _)
  have hR₁m : ∀ j i c, AEMeasurable (fun ω => piHalfCellDiffRand 𝒯 Dπ DΓ K.nEnv T C ε θ K.c₀d
      (Z₁ ω) (Z₂ ω) j i c) P := fun j i c =>
    (Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
      (hpartM₁ j k c).const_mul _) _).aemeasurable
  have hR₂m : ∀ j i c, AEMeasurable (fun ω => piHalfCellRand 𝒯 Dπ DΓ K.nEnv T C K.c₀d
      (Z₂ ω) j i c) P := fun j i c =>
    (Measurable.const_mul (Finset.measurable_sum _ fun k _ =>
      (hpartM₂ j k c).const_mul _) _).aemeasurable
  have hGm : AEMeasurable (fun ω => (Z₁ ω).gammaNormOn γ T) P :=
    (hV₁'.measurable_gammaNormOn γ).aemeasurable
  have hGdm : AEMeasurable (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T) P :=
    (hV₁'.measurable_gammaDiffNormOn hV₂' γ).aemeasurable
  have hfin : ∀ᵐ ω ∂P, (Z₁ ω).gammaNormOn γ T < ⊤ := by
    have h1 : ∫⁻ ω, (1 + (Z₁ ω).gammaNormOn γ T) ^ (2 * p) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hG
    filter_upwards [ae_lt_top' ((aemeasurable_const.add hGm).pow_const (2 * p)) h1] with ω hω
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have h2p : 2 * p ≠ 0 := by omega
    simp [hcon, h2p] at hω
  have hfind : ∀ᵐ ω ∂P, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T < ⊤ := by
    have h1 : ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T ^ (2 * p) ∂P ≠ ⊤ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top hGd
    filter_upwards [ae_lt_top' (hGdm.pow_const (2 * p)) h1] with ω hω
    by_contra hcon
    rw [not_lt, top_le_iff] at hcon
    have h2p : 2 * p ≠ 0 := by omega
    simp [hcon, h2p] at hω
  refine hsk P Z₁ Z₂ (fun ω => (Z₁ ω).gammaNormOn γ T)
    (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T)
    (fun j i c ω => piHalfCellDiffRand 𝒯 Dπ DΓ K.nEnv T C ε θ K.c₀d (Z₁ ω) (Z₂ ω) j i c)
    (fun j i c ω => piHalfCellRand 𝒯 Dπ DΓ K.nEnv T C K.c₀d (Z₂ ω) j i c)
    (piHalfCellDetG 𝒯 K.KdetD K.c₀d (max 1 C) (C * ε ^ θ)) (piHalfCellDet 𝒯 K.Kdet K.c₀d C)
    C (C * ε ^ θ) hC hCb hC' hGm hGdm hR₁m hR₂m hG hGd
    (fun i hi hγ ω t ht x _ => hH.detPiDiff i hi hγ ω t ht x) ?_ ?_ ?_ ?_ ?_
  · -- deterministic part, difference
    intro j i _ _
    unfold piHalfCellDetG
    have hs0 := (piHalfScale_pos j).le
    have h1 : ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), K.KdetD k ≤ ∑ k, K.KdetD k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => K.hKdetD k
    have h2 : max 1 C ≤ max 1 Cbar := max_le_max le_rfl hCb
    have h3 : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), K.KdetD k :=
      Finset.sum_nonneg fun k _ => K.hKdetD k
    have h4 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
    have h5 := K.hc₀d
    calc _ ≤ K.c₀d * (∑ k, K.KdetD k) * max 1 C * (C * ε ^ θ) *
          piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order) := by gcongr
      _ ≤ _ := by gcongr
  · -- deterministic part, second model
    intro j i _ _
    unfold piHalfCellDet
    have hs0 := (piHalfScale_pos j).le
    have h1 : ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), K.Kdet k ≤ ∑ k, K.Kdet k :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun k _ _ => K.hKdet k
    have h2 : max 1 C ≤ max 1 Cbar := max_le_max le_rfl hCb
    have h3 : 0 ≤ ∑ k ∈ Finset.univ.filter (fun k => 𝒯.deg k ≤ 𝒯.deg i), K.Kdet k :=
      Finset.sum_nonneg fun k _ => K.hKdet k
    have h4 : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
    have h5 := K.hc₀d
    calc _ ≤ K.c₀d * (∑ k, K.Kdet k) * max 1 C * C *
          piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order) := by gcongr
      _ ≤ _ := by gcongr
  · -- moments, difference
    intro j i hi hγ c hc
    have hs := piHalfScale_mem j
    have hmom := (lintegral_piHalfCellDiffRand_pow_le 𝒯 Dπ DΓ K.nEnv T κbar C ε θ K.c₀d q hq1
      K.KRd K.hKRd K.hc₀d hC' Z₁ Z₂ j i c (fun k => (hpartM₁ j k c).aemeasurable) (fun k hk => by
        have hkγ : 𝒯.deg k < γ := lt_of_le_of_lt (Finset.mem_filter.1 hk).2 hγ
        exact K.hRkd k hkγ P Z₁ Z₂ C ε hC hε (hH.toSingle hmem₁) (hH.toSingle hmem₂) hH.toDiff
          hs _ ((hmOff₁ k j _).sub (hmOff₂ k j _))
          (fun j' w => hV₁'.1.1 j' w _ hs.1) (fun j' w => hV₂'.1.1 j' w _ hs.1)
          (fun j' w => hV₁'.1.2.1 k j' _ w) (fun j' w => hV₂'.1.2.1 k j' _ w))).2
    refine hmom.trans ?_
    rw [hord]
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
    have h2 : max 1 C ≤ max 1 Cbar := max_le_max le_rfl hCb
    have hs0 := Real.rpow_nonneg (piHalfScale_pos j).le ((𝒯.deg i + κbar) / 4)
    have h5 := K.hc₀d
    have h6 : 0 ≤ ∑ k, K.KRd k := hKRd0
    calc _ = (K.c₀d * ((Fintype.card ι : ℝ) * ∑ k, K.KRd k)) * max 1 C * (C * ε ^ θ) *
            piHalfScale j ^ ((𝒯.deg i + κbar) / 4) := by ring
      _ ≤ (K.c₀d * ((Fintype.card ι : ℝ) * ∑ k, K.KRd k)) * max 1 Cbar * (C * ε ^ θ) *
            piHalfScale j ^ ((𝒯.deg i + κbar) / 4) := by gcongr
      _ = _ := by ring
  · -- moments, second model
    intro j i hi hγ c hc
    have hs := piHalfScale_mem j
    have hmom := (lintegral_piHalfCellRand_pow_le 𝒯 Dπ DΓ K.nEnv T κbar C K.c₀d q hq1 K.KR K.hKR
      K.hc₀d hC Z₂ j i c (fun k => (hpartM₂ j k c).aemeasurable) (fun k hk => by
        have hkγ : 𝒯.deg k < γ := lt_of_le_of_lt (Finset.mem_filter.1 hk).2 hγ
        exact K.hRk k hkγ P Z₂ C hC (hH.toSingle hmem₂) hs _ (hmOff₂ k j _)
          (fun j' w => hV₂'.1.1 j' w _ hs.1) (fun j' w => hV₂'.1.2.1 k j' _ w))).2
    refine hmom.trans ?_
    rw [hord]
    refine pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) q
    have h2 : max 1 C ≤ max 1 Cbar := max_le_max le_rfl hCb
    have hs0 := Real.rpow_nonneg (piHalfScale_pos j).le ((𝒯.deg i + κbar) / 4)
    have h5 := K.hc₀d
    have h6 : 0 ≤ ∑ k, K.KR k := hKR0
    calc _ = (K.c₀d * ((Fintype.card ι : ℝ) * ∑ k, K.KR k)) * max 1 C * C *
            piHalfScale j ^ ((𝒯.deg i + κbar) / 4) := by ring
      _ ≤ (K.c₀d * ((Fintype.card ι : ℝ) * ∑ k, K.KR k)) * max 1 Cbar * C *
            piHalfScale j ^ ((𝒯.deg i + κbar) / 4) := by gcongr
      _ = _ := by ring
  · -- pathwise
    filter_upwards [hfin, hfind] with ω hω hωd
    intro i hi hγ j u hu x hx
    have hGB : (Z₁ ω).GammaBoundOn γ ((Z₁ ω).gammaNormOn γ T).toReal T := by
      have := ((Z₁ ω).gammaNormOn_le_iff (γ := γ) (S := T) ((Z₁ ω).gammaNormOn γ T).toNNReal).1
        (by rw [ENNReal.coe_toNNReal hω.ne])
      exact this
    have hGdB : Model.GammaDiffBoundOn (Z₁ ω) (Z₂ ω) γ
        ((Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T).toReal T := by
      have := (Model.gammaDiffNormOn_le_iff (Z₁ ω) (Z₂ ω) γ T
        ((Z₁ ω).gammaDiffNormOn (Z₂ ω) γ T).toNNReal).1
        (by rw [ENNReal.coe_toNNReal hωd.ne])
      exact this
    have hb := K.hpwd (Z₁ ω) (Z₂ ω) T hTbox _ _ C ε ENNReal.toReal_nonneg ENNReal.toReal_nonneg hC hε
      hGB hGdB (fun x _ k j => measurable_regPi_scale_of_continuousWithFields hV₁' ω x k j)
      (fun x _ k j => measurable_regPi_scale_of_continuousWithFields hV₂' ω x k j) i hγ j u hu x hx
    refine ⟨piHalfCellOf T j ⟨x, hx⟩, piHalfCellOf_lt T j ⟨x, hx⟩, ?_⟩
    have h1 : ENNReal.ofReal (1 + ((Z₁ ω).gammaNormOn γ T).toReal) =
        1 + (Z₁ ω).gammaNormOn γ T := by
      rw [ENNReal.ofReal_add zero_le_one ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hω.ne]
      simp
    rw [h1, ENNReal.ofReal_toReal hωd.ne] at hb
    exact hb

end RegularityStructures

end

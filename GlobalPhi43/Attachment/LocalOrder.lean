module

public import RegularityStructures.Abstract.QFamilyModelBound
import Mathlib.Tactic.Ring

/-! Compact-domain local order from model compatibility and the Pi/Gamma bounds. -/

public section

open MeasureTheory Set
namespace GlobalPhi43.Attachment
open RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}
  (M : Model 𝒯 K)

/-- The local-order bound on any set containing both base and evaluation point. -/
theorem regPi_single_le_on {γ CPi CGam : ℝ} {S : Set E}
    (hPi : M.PiBoundOn γ CPi S) (hGam : M.GammaBoundOn γ CGam S)
    (hCPi : 0 ≤ CPi) {i : ι} (hi : 𝒯.deg i < γ)
    {x y : E} (hx : x ∈ S) (hy : y ∈ S) {u : ℝ} (hu : u ∈ Ioc (0 : ℝ) 1) :
    |M.regPi x (Pi.single i 1) u y| ≤
      Fintype.card ι * (max CGam 1 * CPi) *
        ∑ a ∈ 𝒯.degreesAtMost (𝒯.deg i),
          u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a) := by
  classical
  let F := Finset.univ.filter (fun j => 𝒯.deg j ≤ 𝒯.deg i)
  let w := fun a => u ^ (a / K.order) * K.scaleDist y x ^ (𝒯.deg i - a)
  have hw (a : ℝ) : 0 ≤ w a :=
    mul_nonneg (Real.rpow_nonneg hu.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _)
  have hm : 0 ≤ max CGam 1 := le_trans zero_le_one (le_max_right _ _)
  have ht (j : ι) (hj : j ∈ F) :
      |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| ≤
        (max CGam 1 * CPi) * w (𝒯.deg j) := by
    have hji : 𝒯.deg j ≤ 𝒯.deg i := (Finset.mem_filter.mp hj).2
    have hP := hPi j (hji.trans_lt hi) u hu y hy
    rw [abs_mul]
    by_cases he : j = i
    · subst j
      rw [M.gammaMap_single_apply_self, abs_one, one_mul]
      simp only [w, sub_self, Real.rpow_zero, mul_one]
      calc _ ≤ CPi * u ^ (𝒯.deg i / K.order) := hP
        _ ≤ _ := by
          have h1 := mul_le_mul_of_nonneg_right (le_max_right CGam 1) hCPi
          simpa only [one_mul, mul_assoc] using
            mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.1.le (𝒯.deg i / K.order))
    · by_cases hlt : 𝒯.deg j < 𝒯.deg i
      · have hG := hGam i j hi hlt x hx y hy
        calc _ ≤ (CGam * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) *
            (CPi * u ^ (𝒯.deg j / K.order)) :=
              mul_le_mul hG hP (abs_nonneg _) ((abs_nonneg _).trans hG)
          _ ≤ (max CGam 1 * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) *
            (CPi * u ^ (𝒯.deg j / K.order)) :=
              mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_right (le_max_left _ _)
                  (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
                (mul_nonneg hCPi (Real.rpow_nonneg hu.1.le _))
          _ = _ := by dsimp [w]; ring
      · rw [M.gammaMap_single_apply_of_le x y he (le_of_not_gt hlt), abs_zero, zero_mul]
        exact mul_nonneg (mul_nonneg hm hCPi) (hw _)
  have heq : M.regPi x (Pi.single i 1) u y =
      ∑ j ∈ F, M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y := by
    rw [← M.regPi_gammaMap y x, M.regPi_eq_sum]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    have hj' : 𝒯.deg i ≤ 𝒯.deg j := le_of_not_ge (fun h => hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩))
    have hne : j ≠ i := by intro h; subst j; exact hj (by simp [F])
    rw [M.gammaMap_single_apply_of_le x y hne hj', zero_mul]
  rw [heq]
  calc _ ≤ ∑ j ∈ F, |M.gammaMap y x (Pi.single i 1) j * M.regPi y (Pi.single j 1) u y| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ F, (max CGam 1 * CPi) * w (𝒯.deg j) := Finset.sum_le_sum ht
    _ = (max CGam 1 * CPi) * ∑ j ∈ F, w (𝒯.deg j) := by rw [Finset.mul_sum]
    _ ≤ (max CGam 1 * CPi) * (Fintype.card ι * ∑ a ∈ F.image 𝒯.deg, w a) :=
      mul_le_mul_of_nonneg_left (sum_le_card_mul_sum_image 𝒯 F (fun a _ => hw a)) (mul_nonneg hm hCPi)
    _ = _ := by dsimp [F, w, RegularityStructure.degreesAtMost]; ring

end GlobalPhi43.Attachment

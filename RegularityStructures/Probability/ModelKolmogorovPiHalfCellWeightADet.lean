/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightA
public import RegularityStructures.Abstract.QFamilyR4ModelMollify

/-!
# The deterministic part of the cell weight

For the indices in `piHalfDetIndexA` both factors of the summand are bounded deterministically, by
`max 1 C * d(w, x₀)^(deg k - deg j)` for `Γ` and by `C s^(deg j / 4)` for the diagonal `Π`.
Pathwise, `‖Q_s Π_{x₀} e_k (w)‖ ≤ Det_k(w) + ∑_{random j} ‖(Γ_{w x₀} e_k)_j‖ ‖Q_s Π_w e_j (w)‖`
(`piHalfCellRandRemA_le_sum`), and the envelope moments give
`D = ∫⁻ E^n_s(x₀ - w) Det_k(w) ≤ K max(1, C) C s^(deg k / 4)` (`exists_piHalfCellDetPartA_le`).
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem piHalf_scaleDist_eq (y x : ParabolicSpace) :
    parabolicSemigroup.scaleDist y x = parabolicNorm (x - y) := by
  change parabolicNorm (y - x) = _
  rw [← neg_sub, parabolicNorm_neg]

/-- Deterministic bound for the `Γ` factor when its coefficient is trivial or in `DΓ`. -/
theorem piHalf_gamma_enorm_le_of_det {𝒯 : RegularityStructure ι} {γ C : ℝ}
    {DΓ : Set (ι × ι)} {k : ι} (hkγ : 𝒯.deg k < γ)
    (Z : Model 𝒯 parabolicSemigroup)
    (hΓ : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
      |Z.gammaMap y x (Pi.single i 1) j| ≤ C * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j))
    {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k) (hj2 : 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ)
    (x₀ w : ParabolicSpace) :
    ‖Z.gammaMap w x₀ (Pi.single k 1) j‖ₑ ≤
      ENNReal.ofReal (max 1 C * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
  have hd : 0 ≤ parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) :=
    Real.rpow_nonneg (parabolicNorm_nonneg _) _
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have hU := (Z.isGradedUnipotent_gammaMap w x₀)
  rcases hj2 with hdeg | hDΓ
  · by_cases hjkeq : j = k
    · subst hjkeq
      rw [hU.apply_single_self, sub_self, Real.rpow_zero, abs_one, mul_one]
      exact le_max_left _ _
    · rw [hU.apply_single_of_le hjkeq (le_of_eq hdeg.symm), abs_zero]
      exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hd
  · rcases hjk.lt_or_eq with hlt | heq
    · have := hΓ k j hDΓ hkγ hlt x₀ w
      rw [piHalf_scaleDist_eq] at this
      exact this.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hd)
    · by_cases hjkeq : j = k
      · subst hjkeq
        rw [hU.apply_single_self, sub_self, Real.rpow_zero, abs_one, mul_one]
        exact le_max_left _ _
      · rw [hU.apply_single_of_le hjkeq (le_of_eq heq.symm), abs_zero]
        exact mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hd

/-- Deterministic bound for the `Γ` factor on a deterministic index. -/
theorem piHalf_gamma_enorm_le_det {𝒯 : RegularityStructure ι} {γ C : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {k : ι} (hkγ : 𝒯.deg k < γ)
    (Z : Model 𝒯 parabolicSemigroup)
    (hΓ : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
      |Z.gammaMap y x (Pi.single i 1) j| ≤ C * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j))
    {j : ι} (hj : j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k) (x₀ w : ParabolicSpace) :
    ‖Z.gammaMap w x₀ (Pi.single k 1) j‖ₑ ≤
      ENNReal.ofReal (max 1 C * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
  classical
  simp only [piHalfDetIndexA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact piHalf_gamma_enorm_le_of_det hkγ Z hΓ hj.1 hj.2.2 x₀ w

/-- Deterministic bound for the diagonal `Π` factor on an index of `Dπ`. -/
theorem piHalf_pi_enorm_le_det {𝒯 : RegularityStructure ι} {γ C : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {k : ι} (hkγ : 𝒯.deg k < γ)
    (Z : Model 𝒯 parabolicSemigroup)
    (hPiDet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      |Z.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / parabolicSemigroup.order))
    {j : ι} (hj : j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (w : ParabolicSpace) :
    ‖Z.regPi w (Pi.single j 1) s w‖ₑ ≤ ENNReal.ofReal (C * s ^ (𝒯.deg j / 4)) := by
  classical
  simp only [piHalfDetIndexA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨hjk, hjD, -⟩ := hj
  rw [Real.enorm_eq_ofReal_abs]
  refine ENNReal.ofReal_le_ofReal ?_
  have := hPiDet j hjD (lt_of_le_of_lt hjk hkγ) s hs w
  exact this

/-- The pointwise bound of a deterministic summand. -/
theorem piHalfCellTermA_det_le {𝒯 : RegularityStructure ι} {γ C : ℝ} {Dπ : Set ι}
    {DΓ : Set (ι × ι)} {k : ι} (hkγ : 𝒯.deg k < γ) (hC : 0 ≤ C)
    (Z : Model 𝒯 parabolicSemigroup)
    (hPiDet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      |Z.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / parabolicSemigroup.order))
    (hΓ : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
      |Z.gammaMap y x (Pi.single i 1) j| ≤ C * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j))
    {j : ι} (hj : j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (x₀ w : ParabolicSpace) :
    piHalfCellTermA 𝒯 s x₀ k Z j w ≤
      ENNReal.ofReal (max 1 C * C * s ^ (𝒯.deg j / 4)) *
        ENNReal.ofReal (parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
  have h1 := piHalf_gamma_enorm_le_det (Dπ := Dπ) hkγ Z hΓ hj x₀ w
  have h2 := piHalf_pi_enorm_le_det (DΓ := DΓ) (k := k) hkγ Z hPiDet hj hs w
  have hd : 0 ≤ parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) :=
    Real.rpow_nonneg (parabolicNorm_nonneg _) _
  have hm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hsb : 0 ≤ s ^ (𝒯.deg j / 4) := Real.rpow_nonneg hs.1.le _
  calc piHalfCellTermA 𝒯 s x₀ k Z j w
      ≤ ENNReal.ofReal (max 1 C * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) *
        ENNReal.ofReal (C * s ^ (𝒯.deg j / 4)) := mul_le_mul' h1 h2
    _ = _ := by
        rw [← ENNReal.ofReal_mul (mul_nonneg hm hd), ← ENNReal.ofReal_mul
          (mul_nonneg (mul_nonneg hm hC) hsb)]
        congr 1
        ring

/-- Constants for the envelope moments `∫ E^n_s(x - w) d(x, w)^(deg k - deg j)`, one per `j`. -/
theorem exists_piHalf_envelopeConstants (𝒯 : RegularityStructure ι) (k : ι) {n : ℕ}
    (hn : ∀ j, 𝒯.deg j ≤ 𝒯.deg k → 𝒯.deg k - 𝒯.deg j + 1 < n) :
    ∃ M : ι → ℝ, (∀ j, 0 ≤ M j) ∧ ∀ j, 𝒯.deg j ≤ 𝒯.deg k → ∀ {s : ℝ}, 0 < s →
      ∀ x : ParabolicSpace,
      ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
          ENNReal.ofReal (parabolicNorm (x - w) ^ (𝒯.deg k - 𝒯.deg j)) ≤
        ENNReal.ofReal (M j * s ^ ((𝒯.deg k - 𝒯.deg j) / 4)) := by
  have h : ∀ j, ∃ M : ℝ, 0 ≤ M ∧ (𝒯.deg j ≤ 𝒯.deg k → ∀ {s : ℝ}, 0 < s →
      ∀ x : ParabolicSpace,
      ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x - w)) *
          ENNReal.ofReal (parabolicNorm (x - w) ^ (𝒯.deg k - 𝒯.deg j)) ≤
        ENNReal.ofReal (M * s ^ ((𝒯.deg k - 𝒯.deg j) / 4))) := by
    intro j
    by_cases hj : 𝒯.deg j ≤ 𝒯.deg k
    · obtain ⟨M, hM, hM'⟩ := exists_lintegral_kernelBlockEnvelope_shift_mul_rpow_le
        (n := n) (a := 𝒯.deg k - 𝒯.deg j) (by linarith) (hn j hj)
      exact ⟨M, hM, fun _ {s} hs x => hM' hs x⟩
    · exact ⟨0, le_rfl, fun h => absurd h hj⟩
  choose M hM0 hM using h
  exact ⟨M, hM0, hM⟩

/-- **(A1, integral, general coefficient)** `∫⁻ E^n_s(x₀ - w) DetCoeff_A(w) ≤ K A s^(deg k/4)`. -/
theorem exists_piHalfCellDetCoeffPartA_le (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (k : ι) {n : ℕ}
    (hn : ∀ j, 𝒯.deg j ≤ 𝒯.deg k → 𝒯.deg k - 𝒯.deg j + 1 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (A : ℝ), 0 ≤ A → ∀ {s : ℝ}, 0 < s → ∀ (x₀ : ParabolicSpace),
      ∫⁻ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
          ENNReal.ofReal (piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k A s x₀ w) ≤
        ENNReal.ofReal (K * A * s ^ (𝒯.deg k / 4)) := by
  classical
  obtain ⟨M, hM0, hM⟩ := exists_piHalf_envelopeConstants 𝒯 k hn
  refine ⟨∑ j, M j, Finset.sum_nonneg fun j _ => hM0 j, fun A hA s hs0 x₀ => ?_⟩
  have hE : Measurable (fun w => ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w))) :=
    (measurable_kernelBlockEnvelope_shift n hs0 x₀).ennreal_ofReal
  have hdm : ∀ a : ℝ, Measurable (fun w : ParabolicSpace =>
      ENNReal.ofReal (parabolicNorm (x₀ - w) ^ a)) := fun a =>
    Measurable.ennreal_ofReal
      (((continuous_parabolicNorm.comp (continuous_const.sub continuous_id)).measurable).pow_const a)
  have hcj : ∀ j, 0 ≤ A * s ^ (𝒯.deg j / 4) := fun j =>
    mul_nonneg hA (Real.rpow_nonneg hs0.le _)
  have hpt : ∀ w, ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
      ENNReal.ofReal (piHalfCellDetFunCoeffA 𝒯 Dπ DΓ k A s x₀ w) =
      ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, ENNReal.ofReal (A * s ^ (𝒯.deg j / 4)) *
        (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
          ENNReal.ofReal (parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j))) := by
    intro w
    unfold piHalfCellDetFunCoeffA
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (hcj j) (Real.rpow_nonneg (parabolicNorm_nonneg _) _), Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [ENNReal.ofReal_mul (hcj j)]
    ring
  simp_rw [hpt]
  have hmj : ∀ j : ι, Measurable (fun w : ParabolicSpace =>
      ENNReal.ofReal (A * s ^ (𝒯.deg j / 4)) *
        (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
          ENNReal.ofReal (parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)))) := fun j =>
    Measurable.const_mul (hE.mul (hdm _)) _
  rw [lintegral_finsetSum _ fun j _ => hmj j]
  have hterm : ∀ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k,
      ∫⁻ w, ENNReal.ofReal (A * s ^ (𝒯.deg j / 4)) *
        (ENNReal.ofReal (kernelBlockEnvelope n s (x₀ - w)) *
          ENNReal.ofReal (parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j))) ≤
      ENNReal.ofReal (M j * A * s ^ (𝒯.deg k / 4)) := by
    intro j hj
    have hjk : 𝒯.deg j ≤ 𝒯.deg k := by
      simp only [piHalfDetIndexA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
      exact hj.1
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine (mul_le_mul_of_nonneg_left (hM j hjk hs0 x₀) zero_le).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (hcj j)]
    congr 1
    have : s ^ (𝒯.deg j / 4) * s ^ ((𝒯.deg k - 𝒯.deg j) / 4) = s ^ (𝒯.deg k / 4) := by
      rw [← Real.rpow_add hs0]; congr 1; ring
    calc A * s ^ (𝒯.deg j / 4) * (M j * s ^ ((𝒯.deg k - 𝒯.deg j) / 4))
        = M j * A * (s ^ (𝒯.deg j / 4) * s ^ ((𝒯.deg k - 𝒯.deg j) / 4)) := by ring
      _ = _ := by rw [this]
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← ENNReal.ofReal_sum_of_nonneg fun j _ =>
    mul_nonneg (mul_nonneg (hM0 j) hA) (Real.rpow_nonneg hs0.le _)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, M j * A * s ^ (𝒯.deg k / 4)
      ≤ ∑ j, M j * A * s ^ (𝒯.deg k / 4) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun j _ _ =>
          mul_nonneg (mul_nonneg (hM0 j) hA) (Real.rpow_nonneg hs0.le _)
    _ = _ := by rw [← Finset.sum_mul, ← Finset.sum_mul]

/-- **(A1, integral)** `∫⁻ E^n_s(x₀ - w) Det_k(w) ≤ K max(1,C) C s^(deg k/4)`. -/
theorem exists_piHalfCellDetPartA_le (𝒯 : RegularityStructure ι) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (k : ι) {n : ℕ}
    (hn : ∀ j, 𝒯.deg j ≤ 𝒯.deg k → 𝒯.deg k - 𝒯.deg j + 1 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (C : ℝ), 0 ≤ C → ∀ {s : ℝ}, 0 < s → ∀ (x₀ : ParabolicSpace),
      piHalfCellDetPartA 𝒯 Dπ DΓ n C s x₀ k ≤
        ENNReal.ofReal (K * max 1 C * C * s ^ (𝒯.deg k / 4)) := by
  obtain ⟨K, hK, h⟩ := exists_piHalfCellDetCoeffPartA_le 𝒯 Dπ DΓ k hn
  refine ⟨K, hK, fun C hC s hs x₀ => ?_⟩
  have := h (max 1 C * C) (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) hC) hs x₀
  rw [← mul_assoc] at this
  exact this

/-- **(A1, pathwise)** `R'_k(w) ≤ ∑_{random j} ‖(Γ_{w x₀} e_k)_j‖ ‖Q_s Π_w e_j (w)‖`. -/
theorem piHalfCellRandRemA_le_sum {𝒯 : RegularityStructure ι} {γ C : ℝ} {Dπ : Set ι}
    {DΓ : Set (ι × ι)} {k : ι} (hkγ : 𝒯.deg k < γ) (hC : 0 ≤ C)
    (Z : Model 𝒯 parabolicSemigroup)
    (hPiDet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
      |Z.regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / parabolicSemigroup.order))
    (hGamDet : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
      |Z.gammaMap y x (Pi.single i 1) j| ≤ C * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j))
    {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1) (x₀ w : ParabolicSpace) :
    piHalfCellRandRemA 𝒯 Dπ DΓ k C s x₀ Z w ≤
      ∑ j ∈ piHalfRandIndexA 𝒯 Dπ DΓ k, piHalfCellTermA 𝒯 s x₀ k Z j w := by
  classical
  unfold piHalfCellRandRemA
  rw [tsub_le_iff_left]
  have hset : (Finset.univ.filter fun j => 𝒯.deg j ≤ 𝒯.deg k) = piHalfLowIndexA 𝒯 k := by
    ext j; simp [piHalfLowIndexA]
  have hsum := Z.regPi_single_eq_sum_filter_gammaMap x₀ w k s w
  rw [hset] at hsum
  have hDet : ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, piHalfCellTermA 𝒯 s x₀ k Z j w ≤
      ENNReal.ofReal (piHalfCellDetFunA 𝒯 Dπ DΓ k C s x₀ w) := by
    unfold piHalfCellDetFunA piHalfCellDetFunCoeffA
    have hm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (mul_nonneg hm hC) (Real.rpow_nonneg hs.1.le _))
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _)]
    refine Finset.sum_le_sum fun j hj => ?_
    refine (piHalfCellTermA_det_le hkγ hC Z hPiDet hGamDet hj hs x₀ w).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg (mul_nonneg hm hC) (Real.rpow_nonneg hs.1.le _))]
  calc ‖Z.regPi x₀ (Pi.single k 1) s w‖ₑ
      = ‖∑ j ∈ piHalfLowIndexA 𝒯 k, Z.gammaMap w x₀ (Pi.single k 1) j *
          Z.regPi w (Pi.single j 1) s w‖ₑ := by rw [← hsum]
    _ ≤ ∑ j ∈ piHalfLowIndexA 𝒯 k, piHalfCellTermA 𝒯 s x₀ k Z j w := by
        refine (enorm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun j _ => ?_))
        rw [enorm_mul]; rfl
    _ = ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, piHalfCellTermA 𝒯 s x₀ k Z j w +
        ∑ j ∈ piHalfRandIndexA 𝒯 Dπ DΓ k, piHalfCellTermA 𝒯 s x₀ k Z j w :=
        piHalfDetIndexA_union 𝒯 Dπ DΓ k _
    _ ≤ _ := add_le_add_left hDet _

end RegularityStructures

end

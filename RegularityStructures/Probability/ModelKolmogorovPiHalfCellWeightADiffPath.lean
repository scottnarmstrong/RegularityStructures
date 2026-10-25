/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADiff

/-!
# The pathwise bound for the difference remainder

`piHalfCellDiffRandRemA_le_sum`: `R'_{12}(w) ≤ ∑_{(j, b) ∈ J_rand × Bool} diffTerm (j, b) w`, from
`Π^i_{x₀} e_k = ∑_{deg j ≤ deg k} (Γ^i_{w x₀} e_k)_j Π^i_w e_j` and the deterministic bounds on the
summands with both factors deterministic.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two summands of a deterministic index are bounded by the `Det` coefficient. -/
theorem piHalfCellDiffTerm_det_le {𝒯 : RegularityStructure ι} {γ κbar θ C ε : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hH₁ : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₁ C)
    (hH₂ : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₂ C)
    (hD : PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε)
    {k : ι} (hkγ : 𝒯.deg k < γ) (hC : 0 ≤ C) (hε : 0 ≤ ε) {j : ι}
    (hj : j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (ω : Ω) (x₀ w : ParabolicSpace) :
    piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, true) w +
        piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, false) w ≤
      ENNReal.ofReal (2 * max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
        parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
  classical
  have hord : parabolicSemigroup.order = 4 := rfl
  simp only [piHalfDetIndexA, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  obtain ⟨hjk, hjP, hG⟩ := hj
  have hjγ : 𝒯.deg j < γ := lt_of_le_of_lt hjk hkγ
  have hs0 : 0 < s := hs.1
  have hCm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
  have hCd : 0 ≤ C * ε ^ θ := mul_nonneg hC (Real.rpow_nonneg hε _)
  have hd := Real.rpow_nonneg (parabolicNorm_nonneg (x₀ - w)) (𝒯.deg k - 𝒯.deg j)
  have hsb := Real.rpow_nonneg hs0.le (𝒯.deg j / 4)
  -- the four factor bounds
  have hGa1 := piHalf_gamma_enorm_le_of_det hkγ (Z₁ ω)
    (fun i j' h1 h2 h3 x y => hH₁.gammaDet i j' h1 h2 h3 ω x y) hjk hG x₀ w
  have hdGa := piHalf_gammaDiff_enorm_le_of_det hD hkγ hjk hC hε hG ω x₀ w
  have hdPi : ‖(Z₁ ω).regPi w (Pi.single j 1) s w - (Z₂ ω).regPi w (Pi.single j 1) s w‖ₑ ≤
      ENNReal.ofReal (C * ε ^ θ * s ^ (𝒯.deg j / 4)) := by
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hD.piDet j hjP hjγ ω s hs w
    rwa [hord] at this
  have hPi2 : ‖(Z₂ ω).regPi w (Pi.single j 1) s w‖ₑ ≤ ENNReal.ofReal (C * s ^ (𝒯.deg j / 4)) := by
    rw [Real.enorm_eq_ofReal_abs]
    refine ENNReal.ofReal_le_ofReal ?_
    have := hH₂.piDet j hjP hjγ ω s hs w
    rwa [hord] at this
  have h1 : piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, true) w ≤
      ENNReal.ofReal (max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
        parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
    simp only [piHalfCellDiffTermA, ite_true]
    refine (mul_le_mul' hGa1 hdPi).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_mul (mul_nonneg hCm hd)]
    congr 1; ring
  have h2 : piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, false) w ≤
      ENNReal.ofReal (max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
        parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := by
    simp only [piHalfCellDiffTermA, Bool.false_eq_true, ite_false]
    refine (mul_le_mul' hdGa hPi2).trans ?_
    rw [← ENNReal.ofReal_mul (mul_nonneg hCd hd)]
    refine ENNReal.ofReal_le_ofReal ?_
    have hm : C ≤ max 1 C := le_max_right _ _
    have : C * ε ^ θ * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) *
        (C * s ^ (𝒯.deg j / 4)) = (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
          parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) * C := by ring
    rw [this]
    have h0 : 0 ≤ (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
        parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) := mul_nonneg (mul_nonneg hCd hsb) hd
    calc _ ≤ (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
          parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) * max 1 C :=
          mul_le_mul_of_nonneg_left hm h0
      _ = _ := by ring
  calc _ ≤ ENNReal.ofReal (max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
        parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) +
        ENNReal.ofReal (max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
        parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := add_le_add h1 h2
    _ = _ := by
        have h0 : 0 ≤ max 1 C * (C * ε ^ θ) * s ^ (𝒯.deg j / 4) *
            parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j) :=
          mul_nonneg (mul_nonneg (mul_nonneg hCm hCd) hsb) hd
        rw [← ENNReal.ofReal_add h0 h0]
        congr 1; ring

/-- **(A3, pathwise)** The remainder of the difference is dominated by the random summands. -/
theorem piHalfCellDiffRandRemA_le_sum {𝒯 : RegularityStructure ι} {γ κbar θ C ε : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup}
    (hH₁ : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₁ C)
    (hH₂ : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z₂ C)
    (hD : PiHalfDiffMomentHypsA 𝒯 γ κbar θ Dπ DΓ q P Z₁ Z₂ C ε)
    {k : ι} (hkγ : 𝒯.deg k < γ) (hC : 0 ≤ C) (hε : 0 ≤ ε) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) 1)
    (ω : Ω) (x₀ w : ParabolicSpace) :
    piHalfCellDiffRandRemA 𝒯 Dπ DΓ k C ε θ s x₀ (Z₁ ω) (Z₂ ω) w ≤
      ∑ jb ∈ piHalfRandIndexA 𝒯 Dπ DΓ k ×ˢ (Finset.univ : Finset Bool),
        piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) jb w := by
  classical
  unfold piHalfCellDiffRandRemA
  rw [tsub_le_iff_left]
  have hset : (Finset.univ.filter fun j => 𝒯.deg j ≤ 𝒯.deg k) = piHalfLowIndexA 𝒯 k := by
    ext j; simp [piHalfLowIndexA]
  have hsum1 := (Z₁ ω).regPi_single_eq_sum_filter_gammaMap x₀ w k s w
  have hsum2 := (Z₂ ω).regPi_single_eq_sum_filter_gammaMap x₀ w k s w
  rw [hset] at hsum1 hsum2
  let T : ι → ℝ≥0∞ := fun j =>
    piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, true) w +
      piHalfCellDiffTermA 𝒯 s x₀ k (Z₁ ω) (Z₂ ω) (j, false) w
  have hDet : ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, T j ≤
      ENNReal.ofReal (piHalfCellDiffDetFunA 𝒯 Dπ DΓ k C ε θ s x₀ w) := by
    unfold piHalfCellDiffDetFunA piHalfCellDetFunCoeffA
    have hCm : 0 ≤ max 1 C := le_trans zero_le_one (le_max_left _ _)
    rw [ENNReal.ofReal_sum_of_nonneg fun j _ =>
      mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hCm)
        (mul_nonneg hC (Real.rpow_nonneg hε _))) (Real.rpow_nonneg hs.1.le _))
        (Real.rpow_nonneg (parabolicNorm_nonneg _) _)]
    exact Finset.sum_le_sum fun j hj => piHalfCellDiffTerm_det_le hH₁ hH₂ hD hkγ hC hε hj hs ω x₀ w
  have hterm : ∀ j, ‖(Z₁ ω).gammaMap w x₀ (Pi.single k 1) j * (Z₁ ω).regPi w (Pi.single j 1) s w -
      (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j * (Z₂ ω).regPi w (Pi.single j 1) s w‖ₑ ≤ T j := by
    intro j
    have : (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j * (Z₁ ω).regPi w (Pi.single j 1) s w -
        (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j * (Z₂ ω).regPi w (Pi.single j 1) s w =
        (Z₁ ω).gammaMap w x₀ (Pi.single k 1) j *
          ((Z₁ ω).regPi w (Pi.single j 1) s w - (Z₂ ω).regPi w (Pi.single j 1) s w) +
        ((Z₁ ω).gammaMap w x₀ (Pi.single k 1) j - (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j) *
          (Z₂ ω).regPi w (Pi.single j 1) s w := by ring
    rw [this]
    refine (enorm_add_le _ _).trans ?_
    simp only [T, piHalfCellDiffTermA, enorm_mul, ite_true, Bool.false_eq_true, ite_false]
    exact le_rfl
  calc ‖(Z₁ ω).regPi x₀ (Pi.single k 1) s w - (Z₂ ω).regPi x₀ (Pi.single k 1) s w‖ₑ
      = ‖∑ j ∈ piHalfLowIndexA 𝒯 k, ((Z₁ ω).gammaMap w x₀ (Pi.single k 1) j *
          (Z₁ ω).regPi w (Pi.single j 1) s w - (Z₂ ω).gammaMap w x₀ (Pi.single k 1) j *
          (Z₂ ω).regPi w (Pi.single j 1) s w)‖ₑ := by
        rw [Finset.sum_sub_distrib, ← hsum1, ← hsum2]
    _ ≤ ∑ j ∈ piHalfLowIndexA 𝒯 k, T j :=
        (enorm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm j)
    _ = ∑ j ∈ piHalfDetIndexA 𝒯 Dπ DΓ k, T j + ∑ j ∈ piHalfRandIndexA 𝒯 Dπ DΓ k, T j :=
        piHalfDetIndexA_union 𝒯 Dπ DΓ k _
    _ ≤ _ := by
        refine add_le_add_left hDet _ |>.trans (le_of_eq ?_)
        rw [Finset.sum_product]
        refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
        rw [Fintype.sum_bool]

end RegularityStructures

end

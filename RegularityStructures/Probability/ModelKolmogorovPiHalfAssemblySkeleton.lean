/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblySupMoment

/-!
# The abstract unit-box skeleton of the `Π` half

`piHalf_moment_le_of_dyadic_cells_of_hyps`: the honest `_of_` form of step C1.  The hypotheses are
exactly the outputs of the cell-block reduction (`exists_piHalfBase_block_bound`), of the
deterministic/random split (`piHalfCellWeightA_le_add` and the moment bounds) and of the Gamma half:

* `hpath`: for every dyadic block `u ∈ [2^{-(j+1)}, 2^{-j}]` and `x ∈ S` there is a cell `c < n j`
  with `‖Π_x e_i(u,x)‖ ≤ (1 + G) (D_{j,i} + R_{j,i,c})`;
* `hD`: `D_{j,i} ≤ Kd · C · s_j^{deg i/ℓ}`;
* `hR`: `E R_{j,i,c}^q ≤ (K C s_j^{(deg i + κ)/ℓ})^q`, with `q κ ≥ 12`, `2 p ≤ q`;
* `hn`: the number of cells is `n j ≤ A 2^{5⌊j/4⌋}`;
* `hG`: `E (1 + G)^{2p} ≤ MΓ` (from the Gamma half at moment `2p`);
* `hdet`: the deterministic bound for the symbols in `Dπ`.

The conclusion is `E ‖Π‖_{γ;S}^p ≤ K₀ C^p` with `K₀` depending only on the numeric parameters.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem piHalf_moment_le_of_dyadic_cells_of_hyps (𝒯 : RegularityStructure ι) (γ κ : ℝ)
    (Dπ : Set ι) (S : Set ParabolicSpace) (p q : ℕ) (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    (hqκ : 12 ≤ (q : ℝ) * κ) (n : ℕ → ℕ) (A K Kd MΓ : ℝ) (hA : 0 ≤ A) (hK : 0 ≤ K)
    (hKd : 0 ≤ Kd) (hMΓ : 0 ≤ MΓ) (hn : ∀ j, (n j : ℝ) ≤ A * (2 : ℝ) ^ (5 * (j / 4))) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z : Ω → Model 𝒯 parabolicSemigroup) (G : Ω → ℝ≥0∞) (R : ℕ → ι → ℕ → Ω → ℝ≥0∞)
        (Dd : ℕ → ι → ℝ) (C : ℝ), 0 ≤ C →
        AEMeasurable G P → (∀ j i c, AEMeasurable (R j i c) P) →
        ∫⁻ ω, (1 + G ω) ^ (2 * p) ∂P ≤ ENNReal.ofReal MΓ →
        (∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
          |(Z ω).regPi x (Pi.single i 1) t x| ≤
            C * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ j i, i ∉ Dπ → 𝒯.deg i < γ →
          Dd j i ≤ Kd * C * piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ j i, i ∉ Dπ → 𝒯.deg i < γ → ∀ c < n j,
          ∫⁻ ω, R j i c ω ^ q ∂P ≤ ENNReal.ofReal
            (K * C * piHalfScale j ^ ((𝒯.deg i + κ) / parabolicSemigroup.order)) ^ q) →
        (∀ᵐ ω ∂P, ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ j : ℕ,
          ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j), ∀ x ∈ S,
            ∃ c < n j, ‖(Z ω).regPi x (Pi.single i 1) u x‖ₑ ≤
              (1 + G ω) * (ENNReal.ofReal (Dd j i) + R j i c ω)) →
        ∫⁻ ω, (Z ω).piNormOn γ S ^ p ∂P ≤ ENNReal.ofReal (K₀ * C ^ p) := by
  have hq : q ≠ 0 := by omega
  set c1 : ℝ := 2 * (Fintype.card ι : ℝ) * A * K ^ q with hc1
  have hc1nn : 0 ≤ c1 := by positivity
  set c2 : ℝ := c1 ^ ((q : ℝ)⁻¹) with hc2
  have hc2nn : 0 ≤ c2 := Real.rpow_nonneg hc1nn _
  have hc2q : c2 ^ q = c1 := Real.rpow_inv_natCast_pow hc1nn hq
  set c3 : ℝ := 2 ^ (2 * p) * (Kd ^ (2 * p) + c2 ^ (2 * p)) with hc3
  have hc3nn : 0 ≤ c3 := by positivity
  set W : ℝ := piHalfBlockConst 𝒯 with hW
  have hWnn : 0 ≤ W := piHalfBlockConst_nonneg 𝒯
  refine ⟨2 ^ p * (1 + W ^ p * (Real.sqrt MΓ * Real.sqrt c3)), by positivity, ?_⟩
  intro Ω _ P _ Z G R Dd C hC hGm hRm hG hdet hD hR hpath
  set Y : Ω → ℝ≥0∞ := piHalfRandomSup 𝒯 γ Dπ n R with hY
  have hYm : AEMeasurable Y P := aemeasurable_piHalfRandomSup 𝒯 γ Dπ n R hRm
  have hYq : ∫⁻ ω, Y ω ^ q ∂P ≤ ENNReal.ofReal (c2 * C) ^ q := by
    have := lintegral_piHalfRandomSup_pow_le (P := P) 𝒯 γ κ Dπ n R q hq hA hK hC hqκ hn hRm hR
    refine this.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [mul_pow c2 C q, hc2q, hc1]
    ring
  have hY2 : ∫⁻ ω, Y ω ^ (2 * p) ∂P ≤ ENNReal.ofReal (c2 * C) ^ (2 * p) :=
    lintegral_pow_le_of_pow_le hYm (by omega) hpq hYq
  set V : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Kd * C) + Y ω with hV
  have hVm : AEMeasurable V P := hYm.const_add _
  have hV2 : ∫⁻ ω, V ω ^ (2 * p) ∂P ≤ ENNReal.ofReal (c3 * (C ^ p) ^ 2) := by
    calc ∫⁻ ω, V ω ^ (2 * p) ∂P
        ≤ ∫⁻ ω, 2 ^ (2 * p) * (ENNReal.ofReal (Kd * C) ^ (2 * p) + Y ω ^ (2 * p)) ∂P :=
          lintegral_mono fun ω => ennreal_add_pow_le _ _ _
      _ = 2 ^ (2 * p) * (ENNReal.ofReal (Kd * C) ^ (2 * p) + ∫⁻ ω, Y ω ^ (2 * p) ∂P) := by
          rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
            lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ 2 ^ (2 * p) * (ENNReal.ofReal (Kd * C) ^ (2 * p) +
            ENNReal.ofReal (c2 * C) ^ (2 * p)) := by gcongr
      _ = ENNReal.ofReal (c3 * (C ^ p) ^ 2) := by
          rw [← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_pow (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity)]
          have h2 : (2 : ℝ≥0∞) ^ (2 * p) = ENNReal.ofReal ((2 : ℝ) ^ (2 * p)) := by
            rw [ENNReal.ofReal_pow (by norm_num)]; simp
          rw [h2, ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          rw [hc3]
          ring
  have hpiBound : ∀ᵐ ω ∂P, (Z ω).piNormOn γ S ≤
      ENNReal.ofReal C + ENNReal.ofReal W * ((1 + G ω) * V ω) := by
    filter_upwards [hpath] with ω hpath
    refine piNormOn_le_of_dyadic_blocks (Z ω) γ S Dπ C _ (fun i hi hγ => hdet i hi hγ ω) ?_
    intro i hi hγ j u hu x hx
    obtain ⟨c, hc, hle⟩ := hpath i hi hγ j u hu x hx
    have hs := piHalfScale_pos j
    have h1 : ENNReal.ofReal (Dd j i) ≤ ENNReal.ofReal (Kd * C) *
        ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) := by
      rw [← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (hD j i hi hγ)
    have h2 : R j i c ω ≤ Y ω *
        ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) := by
      have h3 := le_piHalfRandomSup 𝒯 γ Dπ n R ω hi hγ hc
      calc R j i c ω = R j i c ω * ENNReal.ofReal (piHalfScale j ^
            (-(𝒯.deg i / parabolicSemigroup.order))) *
            ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) := by
            rw [mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
              Real.rpow_neg hs.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hs _).ne']
            simp
        _ ≤ _ := by gcongr
    calc ‖(Z ω).regPi x (Pi.single i 1) u x‖ₑ
        ≤ (1 + G ω) * (ENNReal.ofReal (Dd j i) + R j i c ω) := hle
      _ ≤ (1 + G ω) * (ENNReal.ofReal (Kd * C) *
            ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) +
            Y ω * ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order))) := by
          gcongr
      _ = ((1 + G ω) * V ω) *
            ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) := by
          simp only [hV]; ring
  have hCS : ∫⁻ ω, (1 + G ω) ^ p * V ω ^ p ∂P ≤
      ENNReal.ofReal (Real.sqrt MΓ * (Real.sqrt c3 * C ^ p)) := by
    have := lintegral_mul_le_sqrt_mul_sqrt (P := P) (f := fun ω => (1 + G ω) ^ p)
      (g := fun ω => V ω ^ p) ((hGm.const_add 1).pow_const p) (hVm.pow_const p) (a := MΓ) (b := c3 * (C ^ p) ^ 2) hMΓ
      (by positivity)
      (by simpa only [← pow_mul, mul_comm p 2] using hG)
      (by simpa only [← pow_mul, mul_comm p 2] using hV2)
    rwa [Real.sqrt_mul hc3nn, Real.sqrt_sq (pow_nonneg hC p)] at this
  calc ∫⁻ ω, (Z ω).piNormOn γ S ^ p ∂P
      ≤ ∫⁻ ω, 2 ^ p * (ENNReal.ofReal C ^ p +
          ENNReal.ofReal W ^ p * ((1 + G ω) ^ p * V ω ^ p)) ∂P :=
        lintegral_mono_ae <| hpiBound.mono fun ω hω => by
          refine (pow_le_pow_left' hω p).trans ?_
          refine (ennreal_add_pow_le _ _ p).trans (le_of_eq ?_)
          rw [mul_pow, mul_pow]
    _ = 2 ^ p * (ENNReal.ofReal C ^ p +
          ENNReal.ofReal W ^ p * ∫⁻ ω, (1 + G ω) ^ p * V ω ^ p ∂P) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)]
    _ ≤ 2 ^ p * (ENNReal.ofReal C ^ p + ENNReal.ofReal W ^ p *
          ENNReal.ofReal (Real.sqrt MΓ * (Real.sqrt c3 * C ^ p))) := by gcongr
    _ = ENNReal.ofReal ((2 ^ p * (1 + W ^ p * (Real.sqrt MΓ * Real.sqrt c3))) * C ^ p) := by
        have h2 : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) := by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp
        rw [h2, ← ENNReal.ofReal_pow hC, ← ENNReal.ofReal_pow hWnn,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_add (by positivity)
            (by positivity), ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end RegularityStructures

end

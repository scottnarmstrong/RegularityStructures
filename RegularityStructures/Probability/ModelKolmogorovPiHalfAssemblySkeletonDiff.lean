/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblySkeleton
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyDiffDyadic

/-!
# The abstract unit-box skeleton of the `Π` half, difference version

`piHalfDiff_moment_le_of_dyadic_cells_of_hyps`: with `C' = C ε^θ`, pathwise
`‖(Π¹ - Π²)_x e_i(u,x)‖ ≤ (1 + G)(D¹ + R¹_c) + Gd (D² + R²_c)` (the output of
`exists_piHalfBase_block_bound_diff` together with the cell weight splits), where `G` bounds the
`Γ¹` norm, `Gd` the `Γ`-difference norm, `R¹` is the difference remainder (moment scale `C'`) and
`R²` the remainder of the second model (moment scale `C`), gives
`E ‖Π¹ - Π²‖^p ≤ K₀ C'^p` for `0 ≤ C ≤ Cbar`.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Moment bound for `piHalfRandomSup` in the form needed by the skeletons. -/
theorem lintegral_piHalfRandomSup_pow_le_rpow {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (𝒯 : RegularityStructure ι) (γ κ : ℝ) (Dπ : Set ι) (n : ℕ → ℕ)
    (R : ℕ → ι → ℕ → Ω → ℝ≥0∞) (q m : ℕ) (hm : 1 ≤ m) (hmq : m ≤ q) {A K C : ℝ}
    (hA : 0 ≤ A) (hK : 0 ≤ K) (hC : 0 ≤ C) (hqκ : 12 ≤ (q : ℝ) * κ)
    (hn : ∀ j, (n j : ℝ) ≤ A * (2 : ℝ) ^ (5 * (j / 4)))
    (hmeas : ∀ j i c, AEMeasurable (R j i c) P)
    (hR : ∀ j i, i ∉ Dπ → 𝒯.deg i < γ → ∀ c < n j,
      ∫⁻ ω, R j i c ω ^ q ∂P ≤
        ENNReal.ofReal (K * C * piHalfScale j ^ ((𝒯.deg i + κ) / parabolicSemigroup.order)) ^ q) :
    ∫⁻ ω, piHalfRandomSup 𝒯 γ Dπ n R ω ^ m ∂P ≤
      ENNReal.ofReal ((2 * (Fintype.card ι : ℝ) * A * K ^ q) ^ ((q : ℝ)⁻¹) * C) ^ m := by
  have hq : q ≠ 0 := by omega
  have hc1nn : 0 ≤ 2 * (Fintype.card ι : ℝ) * A * K ^ q := by positivity
  have hYq := lintegral_piHalfRandomSup_pow_le (P := P) 𝒯 γ κ Dπ n R q hq hA hK hC hqκ hn hmeas hR
  have hYq' : ∫⁻ ω, piHalfRandomSup 𝒯 γ Dπ n R ω ^ q ∂P ≤
      ENNReal.ofReal ((2 * (Fintype.card ι : ℝ) * A * K ^ q) ^ ((q : ℝ)⁻¹) * C) ^ q := by
    refine hYq.trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_pow (mul_nonneg (Real.rpow_nonneg hc1nn _) hC)]
    congr 1
    rw [mul_pow ((2 * (Fintype.card ι : ℝ) * A * K ^ q) ^ ((q : ℝ)⁻¹)) C q,
      Real.rpow_inv_natCast_pow hc1nn hq]
    ring
  exact lintegral_pow_le_of_pow_le (aemeasurable_piHalfRandomSup 𝒯 γ Dπ n R hmeas) hm hmq hYq'

theorem piHalfDiff_moment_le_of_dyadic_cells_of_hyps (𝒯 : RegularityStructure ι) (γ κ : ℝ)
    (Dπ : Set ι) (S : Set ParabolicSpace) (p q : ℕ) (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    (hqκ : 12 ≤ (q : ℝ) * κ) (n : ℕ → ℕ) (A K₁ Kd₁ K₂ Kd₂ MΓ MΓ' Cbar : ℝ) (hA : 0 ≤ A)
    (hK₁ : 0 ≤ K₁) (hKd₁ : 0 ≤ Kd₁) (hK₂ : 0 ≤ K₂) (hKd₂ : 0 ≤ Kd₂) (hMΓ : 0 ≤ MΓ)
    (hMΓ' : 0 ≤ MΓ') (hCbar : 0 ≤ Cbar)
    (hn : ∀ j, (n j : ℝ) ≤ A * (2 : ℝ) ^ (5 * (j / 4))) :
    ∃ K₀ : ℝ, 0 ≤ K₀ ∧
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (G Gd : Ω → ℝ≥0∞)
        (R₁ R₂ : ℕ → ι → ℕ → Ω → ℝ≥0∞) (Dd₁ Dd₂ : ℕ → ι → ℝ) (C C' : ℝ),
        0 ≤ C → C ≤ Cbar → 0 ≤ C' →
        AEMeasurable G P → AEMeasurable Gd P →
        (∀ j i c, AEMeasurable (R₁ j i c) P) → (∀ j i c, AEMeasurable (R₂ j i c) P) →
        ∫⁻ ω, (1 + G ω) ^ (2 * p) ∂P ≤ ENNReal.ofReal MΓ →
        ∫⁻ ω, Gd ω ^ (2 * p) ∂P ≤ ENNReal.ofReal (MΓ' * (C' ^ p) ^ 2) →
        (∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x ∈ S,
          |(Z₁ ω).regPi x (Pi.single i 1) t x - (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
            C' * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ j i, i ∉ Dπ → 𝒯.deg i < γ →
          Dd₁ j i ≤ Kd₁ * C' * piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ j i, i ∉ Dπ → 𝒯.deg i < γ →
          Dd₂ j i ≤ Kd₂ * C * piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ j i, i ∉ Dπ → 𝒯.deg i < γ → ∀ c < n j,
          ∫⁻ ω, R₁ j i c ω ^ q ∂P ≤ ENNReal.ofReal
            (K₁ * C' * piHalfScale j ^ ((𝒯.deg i + κ) / parabolicSemigroup.order)) ^ q) →
        (∀ j i, i ∉ Dπ → 𝒯.deg i < γ → ∀ c < n j,
          ∫⁻ ω, R₂ j i c ω ^ q ∂P ≤ ENNReal.ofReal
            (K₂ * C * piHalfScale j ^ ((𝒯.deg i + κ) / parabolicSemigroup.order)) ^ q) →
        (∀ᵐ ω ∂P, ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ j : ℕ,
          ∀ u ∈ Icc ((1 / 2 : ℝ) ^ (j + 1)) ((1 / 2 : ℝ) ^ j), ∀ x ∈ S,
            ∃ c < n j, ‖(Z₁ ω).regPi x (Pi.single i 1) u x - (Z₂ ω).regPi x (Pi.single i 1) u x‖ₑ ≤
              (1 + G ω) * (ENNReal.ofReal (Dd₁ j i) + R₁ j i c ω) +
                Gd ω * (ENNReal.ofReal (Dd₂ j i) + R₂ j i c ω)) →
        ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤ ENNReal.ofReal (K₀ * C' ^ p) := by
  have hq : q ≠ 0 := by omega
  set c₁ : ℝ := (2 * (Fintype.card ι : ℝ) * A * K₁ ^ q) ^ ((q : ℝ)⁻¹) with hc₁
  set c₂ : ℝ := (2 * (Fintype.card ι : ℝ) * A * K₂ ^ q) ^ ((q : ℝ)⁻¹) with hc₂
  have hc₁nn : 0 ≤ c₁ := Real.rpow_nonneg (by positivity) _
  have hc₂nn : 0 ≤ c₂ := Real.rpow_nonneg (by positivity) _
  set a₁ : ℝ := 2 ^ (2 * p) * (Kd₁ ^ (2 * p) + c₁ ^ (2 * p)) with ha₁
  set a₂ : ℝ := 2 ^ (2 * p) * (Kd₂ ^ (2 * p) + c₂ ^ (2 * p)) with ha₂
  have ha₁nn : 0 ≤ a₁ := by positivity
  have ha₂nn : 0 ≤ a₂ := by positivity
  set W : ℝ := piHalfBlockConst 𝒯 with hW
  have hWnn : 0 ≤ W := piHalfBlockConst_nonneg 𝒯
  set T : ℝ := Real.sqrt MΓ * Real.sqrt a₁ + Real.sqrt MΓ' * Real.sqrt a₂ * Cbar ^ p with hT
  have hTnn : 0 ≤ T := by positivity
  refine ⟨2 ^ p * (1 + W ^ p * (2 ^ p * T)), by positivity, ?_⟩
  intro Ω _ P _ Z₁ Z₂ G Gd R₁ R₂ Dd₁ Dd₂ C C' hC hCb hC' hGm hGdm hR₁m hR₂m hG hGd hdet hD₁ hD₂
    hR₁ hR₂ hpath
  set Y₁ : Ω → ℝ≥0∞ := piHalfRandomSup 𝒯 γ Dπ n R₁ with hY₁
  set Y₂ : Ω → ℝ≥0∞ := piHalfRandomSup 𝒯 γ Dπ n R₂ with hY₂
  have hY₁m : AEMeasurable Y₁ P := aemeasurable_piHalfRandomSup 𝒯 γ Dπ n R₁ hR₁m
  have hY₂m : AEMeasurable Y₂ P := aemeasurable_piHalfRandomSup 𝒯 γ Dπ n R₂ hR₂m
  have hY₁b := lintegral_piHalfRandomSup_pow_le_rpow (P := P) 𝒯 γ κ Dπ n R₁ q (2 * p)
    (by omega) hpq hA hK₁ hC' hqκ hn hR₁m hR₁
  have hY₂b := lintegral_piHalfRandomSup_pow_le_rpow (P := P) 𝒯 γ κ Dπ n R₂ q (2 * p)
    (by omega) hpq hA hK₂ hC hqκ hn hR₂m hR₂
  set V₁ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Kd₁ * C') + Y₁ ω with hV₁
  set V₂ : Ω → ℝ≥0∞ := fun ω => ENNReal.ofReal (Kd₂ * C) + Y₂ ω with hV₂
  have hV₁m : AEMeasurable V₁ P := hY₁m.const_add _
  have hV₂m : AEMeasurable V₂ P := hY₂m.const_add _
  have hV₁b : ∫⁻ ω, V₁ ω ^ (2 * p) ∂P ≤ ENNReal.ofReal (a₁ * (C' ^ p) ^ 2) := by
    refine (lintegral_ofReal_add_pow_le (2 * p) (by positivity) (by positivity) hY₁b).trans
      (le_of_eq ?_)
    congr 1; rw [ha₁]; ring
  have hV₂b : ∫⁻ ω, V₂ ω ^ (2 * p) ∂P ≤ ENNReal.ofReal (a₂ * (C ^ p) ^ 2) := by
    refine (lintegral_ofReal_add_pow_le (2 * p) (by positivity) (by positivity) hY₂b).trans
      (le_of_eq ?_)
    congr 1; rw [ha₂]; ring
  have hB₁ : ∫⁻ ω, ((1 + G ω) * V₁ ω) ^ p ∂P ≤
      ENNReal.ofReal (Real.sqrt MΓ * Real.sqrt a₁ * C' ^ p) := by
    have := lintegral_mul_pow_le_sqrt (P := P) (hGm.const_add 1) hV₁m p hMΓ
      (by positivity) hG hV₁b
    rwa [Real.sqrt_mul ha₁nn, Real.sqrt_sq (pow_nonneg hC' p), ← mul_assoc] at this
  have hB₂ : ∫⁻ ω, (Gd ω * V₂ ω) ^ p ∂P ≤
      ENNReal.ofReal (Real.sqrt MΓ' * Real.sqrt a₂ * Cbar ^ p * C' ^ p) := by
    have := lintegral_mul_pow_le_sqrt (P := P) hGdm hV₂m p (by positivity)
      (by positivity) hGd hV₂b
    rw [Real.sqrt_mul hMΓ', Real.sqrt_sq (pow_nonneg hC' p), Real.sqrt_mul ha₂nn,
      Real.sqrt_sq (pow_nonneg hC p)] at this
    refine this.trans (ENNReal.ofReal_le_ofReal ?_)
    have hCp : C ^ p ≤ Cbar ^ p := pow_le_pow_left₀ hC hCb p
    have h1 : 0 ≤ Real.sqrt MΓ' * Real.sqrt a₂ := by positivity
    nlinarith [mul_nonneg h1 (pow_nonneg hC' p), mul_le_mul_of_nonneg_left hCp
      (mul_nonneg h1 (pow_nonneg hC' p))]
  have hpiBound : ∀ᵐ ω ∂P, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ≤ ENNReal.ofReal C' +
      ENNReal.ofReal W * ((1 + G ω) * V₁ ω + Gd ω * V₂ ω) := by
    filter_upwards [hpath] with ω hpath
    refine piDiffNormOn_le_of_dyadic_blocks (Z₁ ω) (Z₂ ω) γ S Dπ C' _
      (fun i hi hγ => hdet i hi hγ ω) ?_
    intro i hi hγ j u hu x hx
    obtain ⟨c, hc, hle⟩ := hpath i hi hγ j u hu x hx
    have hs := piHalfScale_pos j
    set sc := ENNReal.ofReal (piHalfScale j ^ (𝒯.deg i / parabolicSemigroup.order)) with hsc
    have hDd : ∀ (D : ℝ) (K' : ℝ), 0 ≤ K' → D ≤ K' * piHalfScale j ^ (𝒯.deg i /
        parabolicSemigroup.order) → ENNReal.ofReal D ≤ ENNReal.ofReal K' * sc := by
      intro D K' hK' hD
      rw [hsc, ← ENNReal.ofReal_mul hK']
      exact ENNReal.ofReal_le_ofReal hD
    have hRY : ∀ (R : ℕ → ι → ℕ → Ω → ℝ≥0∞), R j i c ω ≤
        piHalfRandomSup 𝒯 γ Dπ n R ω * sc := by
      intro R
      have h3 := le_piHalfRandomSup 𝒯 γ Dπ n R ω hi hγ hc
      calc R j i c ω = R j i c ω * ENNReal.ofReal (piHalfScale j ^
            (-(𝒯.deg i / parabolicSemigroup.order))) * sc := by
            rw [hsc, mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le _),
              Real.rpow_neg hs.le, inv_mul_cancel₀ (Real.rpow_pos_of_pos hs _).ne']
            simp
        _ ≤ _ := by gcongr
    have h1 := hDd (Dd₁ j i) (Kd₁ * C') (by positivity)
      (by have := hD₁ j i hi hγ; linarith)
    have h2 := hDd (Dd₂ j i) (Kd₂ * C) (by positivity)
      (by have := hD₂ j i hi hγ; linarith)
    calc _ ≤ (1 + G ω) * (ENNReal.ofReal (Dd₁ j i) + R₁ j i c ω) +
          Gd ω * (ENNReal.ofReal (Dd₂ j i) + R₂ j i c ω) := hle
      _ ≤ (1 + G ω) * (ENNReal.ofReal (Kd₁ * C') * sc + Y₁ ω * sc) +
          Gd ω * (ENNReal.ofReal (Kd₂ * C) * sc + Y₂ ω * sc) := by
          gcongr
          · exact hRY R₁
          · exact hRY R₂
      _ = ((1 + G ω) * V₁ ω + Gd ω * V₂ ω) * sc := by
          simp only [hV₁, hV₂]; ring
  have hB₁m : AEMeasurable (fun ω => ((1 + G ω) * V₁ ω) ^ p) P :=
    ((hGm.const_add 1).mul hV₁m).pow_const p
  have hB₂m : AEMeasurable (fun ω => (Gd ω * V₂ ω) ^ p) P := (hGdm.mul hV₂m).pow_const p
  calc ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ^ p ∂P
      ≤ ∫⁻ ω, 2 ^ p * (ENNReal.ofReal C' ^ p + ENNReal.ofReal W ^ p *
          (2 ^ p * (((1 + G ω) * V₁ ω) ^ p + (Gd ω * V₂ ω) ^ p))) ∂P :=
        lintegral_mono_ae <| hpiBound.mono fun ω hω => by
          refine (pow_le_pow_left' hω p).trans ?_
          refine (ennreal_add_pow_le _ _ p).trans ?_
          rw [mul_pow]
          gcongr
          exact ennreal_add_pow_le _ _ p
    _ = 2 ^ p * (ENNReal.ofReal C' ^ p + ENNReal.ofReal W ^ p * (2 ^ p *
          (∫⁻ ω, ((1 + G ω) * V₁ ω) ^ p ∂P + ∫⁻ ω, (Gd ω * V₂ ω) ^ p ∂P))) := by
        rw [lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofNat_ne_top),
          lintegral_add_left' hB₁m]
    _ ≤ 2 ^ p * (ENNReal.ofReal C' ^ p + ENNReal.ofReal W ^ p * (2 ^ p *
          (ENNReal.ofReal (Real.sqrt MΓ * Real.sqrt a₁ * C' ^ p) +
            ENNReal.ofReal (Real.sqrt MΓ' * Real.sqrt a₂ * Cbar ^ p * C' ^ p)))) := by
        gcongr
    _ = ENNReal.ofReal ((2 ^ p * (1 + W ^ p * (2 ^ p * T))) * C' ^ p) := by
        have h2 : (2 : ℝ≥0∞) ^ p = ENNReal.ofReal ((2 : ℝ) ^ p) := by
          rw [ENNReal.ofReal_pow (by norm_num)]; simp
        rw [h2, ← ENNReal.ofReal_pow hC', ← ENNReal.ofReal_pow hWnn,
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity),
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        rw [hT]
        ring

end RegularityStructures

end

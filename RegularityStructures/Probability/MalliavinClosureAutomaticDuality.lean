/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.MalliavinClosureCrossDuality
public import RegularityStructures.Probability.MalliavinClosureGrowth
public import RegularityStructures.Probability.MalliavinClosureLaw

/-!
# Automatic Gaussian duality for smooth random tests

The finite-rank random-test identity is instantiated here with the augmented Gaussian vector
whose coordinates are the two cylindrical lists and the deterministic test function.  All value
and first-derivative growth assumptions are displayed, and the required product integrability is
derived from Gaussian polynomial moments.  This is the duality input for the closability argument
in [HS23, Definition 2.20 and Remark 2.22].
-/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace RegularityStructures

private lemma malliavin_auto_coordinate_value_bound {N : ℕ} {g : (Fin N → ℝ) → ℝ}
    {C : ℝ} {M : ℕ} (_hC : 0 ≤ C)
    (hg : ∀ x : Fin N → ℝ,
      |g x| + ‖fderiv ℝ g x‖ ≤ C * (1 + ‖x‖) ^ M)
    (i : Fin N) : ∀ x : Fin N → ℝ,
      |coordinateDerivative g i x| ≤ C * (1 + ‖x‖) ^ M := by
  intro x
  have hnorm : ‖fderiv ℝ g x (Pi.single i 1)‖ ≤ ‖fderiv ℝ g x‖ := by
    have h := ContinuousLinearMap.le_opNorm (fderiv ℝ g x) (Pi.single i 1)
    have hs : ‖(Pi.single i (1 : ℝ) : Fin N → ℝ)‖ = 1 := by
      classical
      rw [Pi.norm_single]
      simp
    simpa [hs] using h
  have hsum : ‖fderiv ℝ g x‖ ≤ |g x| + ‖fderiv ℝ g x‖ :=
    le_add_of_nonneg_left (abs_nonneg _)
  have h := hnorm.trans (hsum.trans (hg x))
  simpa [coordinateDerivative, Real.norm_eq_abs] using h

private lemma malliavin_auto_comp_value_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : E → ℝ} {L : F →L[ℝ] E} {C : ℝ} {M : ℕ} (hC : 0 ≤ C)
    (hg : ∀ x : E, |g x| ≤ C * (1 + ‖x‖) ^ M) :
    ∀ z : F, |g (L z)| ≤ C * (max 1 ‖L‖) ^ M * (1 + ‖z‖) ^ M := by
  intro z
  let K : ℝ := max 1 ‖L‖
  have _hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hbase : 1 + ‖L z‖ ≤ K * (1 + ‖z‖) := by
    have hL : ‖L z‖ ≤ ‖L‖ * ‖z‖ := L.le_opNorm z
    dsimp [K]
    calc
      1 + ‖L z‖ ≤ 1 + ‖L‖ * ‖z‖ := by linarith
      _ ≤ max 1 ‖L‖ + max 1 ‖L‖ * ‖z‖ := by
        gcongr
        · exact le_max_left (1 : ℝ) ‖L‖
        · exact le_max_right (1 : ℝ) ‖L‖
      _ = max 1 ‖L‖ * (1 + ‖z‖) := by ring
  have hpow : (1 + ‖L z‖) ^ M ≤ (K * (1 + ‖z‖)) ^ M := by
    exact pow_le_pow_left₀ (by positivity) hbase M
  have hbound : |g (L z)| ≤ C * (K * (1 + ‖z‖)) ^ M := by
    exact (hg (L z)).trans (mul_le_mul_of_nonneg_left hpow hC)
  dsimp [K] at hbound ⊢
  calc
    |g (L z)| ≤ C * (max 1 ‖L‖ * (1 + ‖z‖)) ^ M := hbound
    _ = C * (max 1 ‖L‖) ^ M * (1 + ‖z‖) ^ M := by
      rw [mul_pow]
      ring

private lemma malliavin_auto_product_value_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g u : E → ℝ} {C D : ℝ} {M N : ℕ} (hC : 0 ≤ C) (hD : 0 ≤ D)
    (hg : ∀ x, |g x| ≤ C * (1 + ‖x‖) ^ M)
    (hu : ∀ x, |u x| ≤ D * (1 + ‖x‖) ^ N) :
    ∀ x, |g x * u x| ≤ C * D * (1 + ‖x‖) ^ (M + N) := by
  intro x
  have hr : 0 ≤ 1 + ‖x‖ := by positivity
  have hp : 0 ≤ (1 + ‖x‖) ^ M := pow_nonneg hr _
  have hq : 0 ≤ (1 + ‖x‖) ^ N := pow_nonneg hr _
  have hCb : 0 ≤ C * (1 + ‖x‖) ^ M := mul_nonneg hC hp
  have hDq : 0 ≤ D * (1 + ‖x‖) ^ N := mul_nonneg hD hq
  calc
    |g x * u x| = |g x| * |u x| := abs_mul _ _
    _ ≤ (C * (1 + ‖x‖) ^ M) * (D * (1 + ‖x‖) ^ N) := by
      exact mul_le_mul (hg x) (hu x) (abs_nonneg _) hCb
    _ = C * D * ((1 + ‖x‖) ^ M * (1 + ‖x‖) ^ N) := by ring
    _ = C * D * (1 + ‖x‖) ^ (M + N) := by rw [← pow_add]

private theorem malliavin_auto_integrable_gaussian_pullback
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {X : Ω → Fin N → ℝ} {C : Fin N → Fin N → ℝ}
    (hX : IsCentredGaussianVector P X C) {g : (Fin N → ℝ) → ℝ}
    (hg_meas : AEStronglyMeasurable g (P.map X))
    (hgrowth : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin N → ℝ, |g x| ≤ K * (1 + ‖x‖) ^ M) :
    Integrable (fun ω => g (X ω)) P := by
  have hmem : MemLp g 2 (P.map X) :=
    @memLp_of_polynomial_bound_gaussian (Fin N → ℝ) _ _ _ _ _ _ (P.map X) hX.2.1 g
      hg_meas hgrowth
  exact (hmem.comp_of_map hX.1).integrable (by norm_num)

private theorem malliavin_auto_continuous_coordinate {N : ℕ}
    {g : (Fin N → ℝ) → ℝ} (hcont : ContDiff ℝ 1 g) (i : Fin N) :
    Continuous (coordinateDerivative g i) := by
  have h := hcont.continuous_fderiv_apply one_ne_zero
  change Continuous (fun x : Fin N → ℝ => fderiv ℝ g x (Pi.single i 1))
  simpa [Function.comp_def] using h.comp
    (by fun_prop : Continuous (fun x : Fin N → ℝ => (x, Pi.single i 1)))

theorem malliavin_random_test_duality_of_polynomial_growth
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {W : (SpaceTime → ℝ) → Ω → ℝ} {n m : ℕ}
    {h : Fin n → SpaceTime → ℝ} {k : Fin m → SpaceTime → ℝ}
    {f : (Fin n → ℝ) → ℝ} {u : (Fin m → ℝ) → ℝ}
    {r : SpaceTime → ℝ}
    (hW : IsWhiteNoise P W)
    (hmem_h : ∀ i, MemLp (h i) 2) (hmem_k : ∀ j, MemLp (k j) 2)
    (hmem_r : MemLp r 2)
    (hcont_f : ContDiff ℝ 1 f) (hcont_u : ContDiff ℝ 1 u)
    (hgrowth_f : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin n → ℝ, |f x| + ‖fderiv ℝ f x‖ ≤ K * (1 + ‖x‖) ^ M)
    (hgrowth_u : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin m → ℝ, |u x| + ‖fderiv ℝ u x‖ ≤ K * (1 + ‖x‖) ^ M) :
    ∫ p, cylindricalDerivative W h f p.1 p.2 *
        (u (fun i => W (k i) p.1) * r p.2) ∂(whiteNoiseDerivativeMeasure P) =
      ∫ ω, f (fun i => W (h i) ω) *
        (u (fun j => W (k j) ω) * W r ω -
          ∑ j, (∫ z, k j z * r z) *
            coordinateDerivative u j (fun i => W (k i) ω)) ∂P := by
  let H : Fin (n + m) → SpaceTime → ℝ := malliavinConcatTest h k
  let Z : Ω → Fin (n + m) → ℝ := fun ω i => W (H i) ω
  have hmem_H : ∀ i, MemLp (H i) 2 := by
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa [H, malliavinConcatTest] using hmem_h j
    · intro j
      simpa [H, malliavinConcatTest] using hmem_k j
  have hZ : IsCentredGaussianVector P Z
      (fun i j => ∫ z, H i z * H j z) := by
    simpa [Z] using hW.2 (n + m) H hmem_H
  let Lf := malliavinConcatLeftCLM n m
  let Lu := malliavinConcatRightCLM n m
  let F : (Fin (n + m) → ℝ) → ℝ := fun x => f (Lf x)
  let U : (Fin (n + m) → ℝ) → ℝ := fun x => u (Lu x)
  have hcont_F : ContDiff ℝ 1 F := by
    exact hcont_f.comp Lf.contDiff
  have hcont_U : ContDiff ℝ 1 U := by
    exact hcont_u.comp Lu.contDiff
  have hgrowth_F : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin (n + m) → ℝ, |F x| + ‖fderiv ℝ F x‖ ≤ K * (1 + ‖x‖) ^ M := by
    simpa [F, Lf] using malliavin_comp_continuousLinearMap_polynomial_bound
      hcont_f hgrowth_f
  have hgrowth_U : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
      ∀ x : Fin (n + m) → ℝ, |U x| + ‖fderiv ℝ U x‖ ≤ K * (1 + ‖x‖) ^ M := by
    simpa [U, Lu] using malliavin_comp_continuousLinearMap_polynomial_bound
      hcont_u hgrowth_u
  have hIBP : ∫ ω, (F (Z ω) * U (Z ω)) * W r ω ∂P =
      ∑ i, (∫ ω, coordinateDerivative (fun x => F x * U x) i (Z ω) ∂P) *
        ∫ z, H i z * r z := by
    let v : Fin ((n + m) + 1) → SpaceTime → ℝ := Fin.cons r H
    let Y : Ω → Fin ((n + m) + 1) → ℝ := fun ω i => W (v i) ω
    have hmem_v : ∀ i, MemLp (v i) 2 := by
      intro i
      refine Fin.cases ?_ (fun j => hmem_H j) i
      simpa [v] using hmem_r
    have hY : IsCentredGaussianVector P Y
        (fun i j => ∫ z, v i z * v j z) := by
      simpa [Y] using hW.2 ((n + m) + 1) v hmem_v
    obtain ⟨A, hAsymm, hAsq, hlaw⟩ := centredGaussianVector_standard_representation hY
    let G : (Fin (n + m) → ℝ) → ℝ := fun x => F x * U x
    have hcont_G : ContDiff ℝ 1 G := by
      exact hcont_F.mul hcont_U
    have hgrowth_G : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
        ∀ x : Fin (n + m) → ℝ, |G x| + ‖fderiv ℝ G x‖ ≤ K * (1 + ‖x‖) ^ M := by
      exact malliavin_product_contDiff_polynomial_bound hcont_F hcont_U hgrowth_F hgrowth_U
    have hgrowth_tail := malliavin_comp_continuousLinearMap_polynomial_bound
      (g := G) (L := malliavinTailCLM (n + m))
      (hcont_G) hgrowth_G
    have hgrowth_trans := malliavin_comp_continuousLinearMap_polynomial_bound
      (g := G) (L := (malliavinTailCLM (n + m)).comp
        (Matrix.mulVecLin A).toContinuousLinearMap)
      hcont_G hgrowth_G
    have hY_zero : ∀ ω, Y ω 0 = W r ω := by
      intro ω
      simp [Y, v]
    have hY_succ : ∀ (ω : Ω) (i : Fin (n + m)), Y ω i.succ = W (H i) ω := by
      intro ω i
      simp [Y, v]
    have hB : ∀ i : Fin (n + m),
        (fun i j => ∫ z, v i z * v j z) 0 i.succ = ∫ z, r z * H i z := by
      intro i
      simp [v]
    have hparts := malliavin_cylindrical_ibp_of_polynomial_growth
      (W := W) (h := H) (k := r) (f := G) hY hAsymm hAsq hlaw
      hcont_G hgrowth_G hgrowth_tail hgrowth_trans hY_zero hY_succ hB
    simpa [G, Z, F, U, H] using hparts
  have hgrad : ∀ i, Integrable
      (fun ω => coordinateDerivative f i (fun j => W (h j) ω) *
        u (fun j => W (k j) ω)) P := by
    rcases hgrowth_f with ⟨Cf, Mf, hCf, hf⟩
    rcases hgrowth_u with ⟨Cu, Mu, hCu, hu⟩
    intro i
    let g : (Fin (n + m) → ℝ) → ℝ := fun x =>
      coordinateDerivative f i (Lf x) * u (Lu x)
    have hcont_g : Continuous g := by
      exact (malliavin_auto_continuous_coordinate hcont_f i).comp Lf.continuous |>.mul
        (hcont_u.continuous.comp Lu.continuous)
    have hbound_f : ∀ x : Fin n → ℝ,
        |coordinateDerivative f i x| ≤ Cf * (1 + ‖x‖) ^ Mf :=
      malliavin_auto_coordinate_value_bound hCf hf i
    have hbound_u : ∀ x : Fin m → ℝ,
        |u x| ≤ Cu * (1 + ‖x‖) ^ Mu := by
      intro x
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hu x)
    have hbound_g : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
        ∀ x : Fin (n + m) → ℝ, |g x| ≤ K * (1 + ‖x‖) ^ M := by
      let Kf : ℝ := max 1 ‖Lf‖
      let Ku : ℝ := max 1 ‖Lu‖
      refine ⟨Cf * Kf ^ Mf * (Cu * Ku ^ Mu), Mf + Mu, by positivity, ?_⟩
      intro x
      exact malliavin_auto_product_value_bound (by positivity) (by positivity)
        (malliavin_auto_comp_value_bound hCf hbound_f)
        (malliavin_auto_comp_value_bound hCu hbound_u) x
    have hint := malliavin_auto_integrable_gaussian_pullback hZ
      hcont_g.measurable.aestronglyMeasurable hbound_g
    have hleft (ω : Ω) : Lf (fun i => W (H i) ω) = (fun i => W (h i) ω) := by
      funext i
      rw [malliavinConcatLeftCLM_apply]
      simp [H, malliavinConcatTest]
    have hright (ω : Ω) : Lu (fun i => W (H i) ω) = (fun j => W (k j) ω) := by
      funext j
      rw [malliavinConcatRightCLM_apply]
      simp [H, malliavinConcatTest]
    have heq : (fun ω => g (Z ω)) =
        (fun ω => coordinateDerivative f i (fun j => W (h j) ω) *
          u (fun j => W (k j) ω)) := by
      funext ω
      dsimp [g, Z]
      rw [hleft, hright]
    rw [heq] at hint
    exact hint
  have hfdu : ∀ j, Integrable
      (fun ω => f (fun i => W (h i) ω) *
        coordinateDerivative u j (fun i => W (k i) ω)) P := by
    rcases hgrowth_f with ⟨Cf, Mf, hCf, hf⟩
    rcases hgrowth_u with ⟨Cu, Mu, hCu, hu⟩
    intro j
    let g : (Fin (n + m) → ℝ) → ℝ := fun x =>
      f (Lf x) * coordinateDerivative u j (Lu x)
    have hcont_g : Continuous g := by
      exact (hcont_f.continuous.comp Lf.continuous).mul
        ((malliavin_auto_continuous_coordinate hcont_u j).comp Lu.continuous)
    have hbound_f : ∀ x : Fin n → ℝ, |f x| ≤ Cf * (1 + ‖x‖) ^ Mf := by
      intro x
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hf x)
    have hbound_u : ∀ x : Fin m → ℝ,
        |coordinateDerivative u j x| ≤ Cu * (1 + ‖x‖) ^ Mu :=
      malliavin_auto_coordinate_value_bound hCu hu j
    have hbound_g : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
        ∀ x : Fin (n + m) → ℝ, |g x| ≤ K * (1 + ‖x‖) ^ M := by
      let Kf : ℝ := max 1 ‖Lf‖
      let Ku : ℝ := max 1 ‖Lu‖
      refine ⟨Cf * Kf ^ Mf * (Cu * Ku ^ Mu), Mf + Mu, by positivity, ?_⟩
      intro x
      exact malliavin_auto_product_value_bound (by positivity) (by positivity)
        (malliavin_auto_comp_value_bound hCf hbound_f)
        (malliavin_auto_comp_value_bound hCu hbound_u) x
    have hint := malliavin_auto_integrable_gaussian_pullback hZ
      hcont_g.measurable.aestronglyMeasurable hbound_g
    have hleft (ω : Ω) : Lf (fun i => W (H i) ω) = (fun i => W (h i) ω) := by
      funext i
      rw [malliavinConcatLeftCLM_apply]
      simp [H, malliavinConcatTest]
    have hright (ω : Ω) : Lu (fun i => W (H i) ω) = (fun j => W (k j) ω) := by
      funext j
      rw [malliavinConcatRightCLM_apply]
      simp [H, malliavinConcatTest]
    have heq : (fun ω => g (Z ω)) =
        (fun ω => f (fun i => W (h i) ω) *
          coordinateDerivative u j (fun i => W (k i) ω)) := by
      funext ω
      dsimp [g, Z]
      rw [hleft, hright]
    rw [heq] at hint
    exact hint
  have hfuW : Integrable
      (fun ω => (f (fun i => W (h i) ω) * u (fun j => W (k j) ω)) * W r ω) P := by
    rcases hgrowth_f with ⟨Cf, Mf, hCf, hf⟩
    rcases hgrowth_u with ⟨Cu, Mu, hCu, hu⟩
    let v : Fin ((n + m) + 1) → SpaceTime → ℝ := Fin.cons r H
    let Y : Ω → Fin ((n + m) + 1) → ℝ := fun ω i => W (v i) ω
    have hmem_v : ∀ i, MemLp (v i) 2 := by
      intro i
      refine Fin.cases ?_ (fun j => hmem_H j) i
      simpa [v] using hmem_r
    have hY : IsCentredGaussianVector P Y
        (fun i j => ∫ z, v i z * v j z) := by
      simpa [Y] using hW.2 ((n + m) + 1) v hmem_v
    let g : (Fin ((n + m) + 1) → ℝ) → ℝ := fun x =>
      f (Lf (malliavinTailCLM (n + m) x)) *
        u (Lu (malliavinTailCLM (n + m) x)) * x 0
    have hcont_g : Continuous g := by
      dsimp [g]
      have hc := (hcont_f.continuous.comp (Lf.continuous.comp
        (malliavinTailCLM (n + m)).continuous)).mul
        ((hcont_u.continuous.comp (Lu.continuous.comp
          (malliavinTailCLM (n + m)).continuous)).mul
          (continuous_apply 0))
      convert hc using 1
      funext x
      simp [Function.comp_def, mul_assoc]
    have hbound_f : ∀ x : Fin n → ℝ, |f x| ≤ Cf * (1 + ‖x‖) ^ Mf := by
      intro x
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hf x)
    have hbound_u : ∀ x : Fin m → ℝ, |u x| ≤ Cu * (1 + ‖x‖) ^ Mu := by
      intro x
      exact (le_add_of_nonneg_right (norm_nonneg _)).trans (hu x)
    have hbound_fL : ∀ y : Fin (n + m) → ℝ,
        |f (Lf y)| ≤ Cf * (max 1 ‖Lf‖) ^ Mf * (1 + ‖y‖) ^ Mf := by
      intro y
      simpa [mul_assoc] using malliavin_auto_comp_value_bound hCf hbound_f y
    have hbound_uL : ∀ y : Fin (n + m) → ℝ,
        |u (Lu y)| ≤ Cu * (max 1 ‖Lu‖) ^ Mu * (1 + ‖y‖) ^ Mu := by
      intro y
      simpa [mul_assoc] using malliavin_auto_comp_value_bound hCu hbound_u y
    have hbound_tail_f : ∀ x : Fin ((n + m) + 1) → ℝ,
        |f (Lf (malliavinTailCLM (n + m) x))| ≤
          Cf * (max 1 ‖Lf‖) ^ Mf * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mf *
            (1 + ‖x‖) ^ Mf := by
      intro x
      simpa [mul_assoc] using
        (malliavin_auto_comp_value_bound
          (C := Cf * (max 1 ‖Lf‖) ^ Mf) (M := Mf)
          (by positivity) hbound_fL x)
    have hbound_tail_u : ∀ x : Fin ((n + m) + 1) → ℝ,
        |u (Lu (malliavinTailCLM (n + m) x))| ≤
          Cu * (max 1 ‖Lu‖) ^ Mu * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mu *
            (1 + ‖x‖) ^ Mu := by
      intro x
      simpa [mul_assoc] using
        (malliavin_auto_comp_value_bound
          (C := Cu * (max 1 ‖Lu‖) ^ Mu) (M := Mu)
          (by positivity) hbound_uL x)
    have hbound_x : ∀ x : Fin ((n + m) + 1) → ℝ, |x 0| ≤ 1 * (1 + ‖x‖) ^ 1 := by
      intro x
      have hx : |x 0| ≤ ‖x‖ := by
        simpa [Real.norm_eq_abs] using (norm_le_pi_norm x 0)
      have hnonneg : 0 ≤ 1 + ‖x‖ := by positivity
      calc
        |x 0| ≤ 1 + ‖x‖ := by linarith
        _ = 1 * (1 + ‖x‖) ^ 1 := by simp
    have hbound_g : ∃ K : ℝ, ∃ M : ℕ, 0 ≤ K ∧
        ∀ x : Fin ((n + m) + 1) → ℝ, |g x| ≤ K * (1 + ‖x‖) ^ M := by
      refine ⟨Cf * (max 1 ‖Lf‖) ^ Mf * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mf *
          (Cu * (max 1 ‖Lu‖) ^ Mu * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mu),
        Mf + Mu + 1, by positivity, ?_⟩
      intro x
      have hprod' := malliavin_auto_product_value_bound
        (C := Cf * (max 1 ‖Lf‖) ^ Mf * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mf)
        (D := Cu * (max 1 ‖Lu‖) ^ Mu * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mu)
        (M := Mf) (N := Mu) (by positivity) (by positivity) hbound_tail_f hbound_tail_u
      simpa [g, mul_assoc] using (malliavin_auto_product_value_bound
        (C := Cf * (max 1 ‖Lf‖) ^ Mf * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mf *
          (Cu * (max 1 ‖Lu‖) ^ Mu * (max 1 ‖malliavinTailCLM (n + m)‖) ^ Mu))
        (D := 1) (M := Mf + Mu) (N := 1) (by positivity) (by positivity)
        (fun y => hprod' y) hbound_x x)
    have hint := malliavin_auto_integrable_gaussian_pullback hY
      hcont_g.measurable.aestronglyMeasurable hbound_g
    have htail (ω : Ω) :
        malliavinTailCLM (n + m) (fun i => W (v i) ω) =
          (fun i => W (H i) ω) := by
      funext i
      rw [malliavinTailCLM_apply]
      simp [v]
    have hleft (ω : Ω) :
        Lf (malliavinTailCLM (n + m) (fun i => W (v i) ω)) =
          (fun i => W (h i) ω) := by
      rw [htail]
      funext i
      rw [malliavinConcatLeftCLM_apply]
      simp [H, malliavinConcatTest]
    have hright (ω : Ω) :
        Lu (malliavinTailCLM (n + m) (fun i => W (v i) ω)) =
          (fun j => W (k j) ω) := by
      rw [htail]
      funext j
      rw [malliavinConcatRightCLM_apply]
      simp [H, malliavinConcatTest]
    have heq : (fun ω => g (Y ω)) =
        (fun ω => (f (fun i => W (h i) ω) * u (fun j => W (k j) ω)) * W r ω) := by
      funext ω
      dsimp [g, Y]
      rw [hleft, hright]
      simp [v]
    rw [heq] at hint
    exact hint
  exact malliavin_cross_random_test_duality_of_ibp hmem_h hmem_k hmem_r
    hcont_f hcont_u hgrad hfdu hfuW hIBP

end RegularityStructures

end

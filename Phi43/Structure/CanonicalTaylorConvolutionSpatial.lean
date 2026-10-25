/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Structure.CanonicalTaylorSpatial
public import Phi43.Structure.AbstractPolynomial
import RegularityStructures.Analysis.Heat.Annihilating.Translate
public import RegularityStructures.Analysis.Heat.Schauder.TaylorKernel

/-!
# Actual convolution and first-spatial Taylor-subtracted shell sums

Hairer [Hai14, (5.14), Definition 5.9, Proposition 8.27]. The retained
`I(Ψ)` has target degree in `(1,2)`, so its Taylor subtraction contains
the constant and the three spatial linear coefficients. Each coefficient
is the actual convolution value or spatial gradient.
-/

public noncomputable section

open MeasureTheory

namespace RegularityStructures.Phi43

local instance : (volume : Measure ParabolicSpace).IsAddLeftInvariant := by
  rw [Measure.volume_eq_prod]; infer_instance

local instance : (volume : Measure ParabolicSpace).IsNegInvariant := by
  rw [Measure.volume_eq_prod]
  have : (volume.prod volume : Measure ParabolicSpace).IsAddHaarMeasure := inferInstance
  have : (volume.prod volume : Measure ParabolicSpace).Regular := inferInstance
  infer_instance

private theorem taylorIdx_spatial {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) :
    taylorIdx σ = {(0 : Fin 4 →₀ ℕ), Finsupp.single 1 1,
      Finsupp.single 2 1, Finsupp.single 3 1} := by
  ext k
  rw [mem_taylorIdx_iff]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hk
    have hn : multiDeg k < 2 := by exact_mod_cast hk.trans_le hσ2
    exact polyIndex_two_cases ⟨k, hn⟩
  · rintro (rfl | rfl | rfl | rfl) <;>
      simp [multiDeg, weight_parabolicWeight] <;> linarith

private theorem spatial_multiDirs (i : Fin 3) :
    multiDirs (Finsupp.single i.succ 1) = [spaceDir i] := by
  simp [multiDirs, Finsupp.toMultiset_single, coordDir_succ]

private theorem shell_integrand_integrable (N n : ℕ) {f : ParabolicSpace → ℝ}
    (hf : Continuous f) (L : List ParabolicSpace) (x : ParabolicSpace) :
    Integrable (fun w => f w * lineIter L (annShellC N n) (x - w)) := by
  have hφ : Continuous (fun w => lineIter L (annShellC N n) (x - w)) :=
    (contDiff_lineIter (contDiff_annShellC N n) _).continuous.comp
      (continuous_const.sub continuous_id)
  have hφc : HasCompactSupport (fun w => lineIter L (annShellC N n) (x - w)) :=
    (hasCompactSupport_lineIter
      (hasCompactSupport_scaledShell (fun _ hz => annKernel0C_eq_zero N hz) n) _).comp_homeomorph
      (Homeomorph.subLeft x)
  exact (hf.mul hφ).integrable_of_hasCompactSupport hφc.mul_left

private theorem shell_reflect_integral (N n : ℕ) (f : ParabolicSpace → ℝ)
    (z : ParabolicSpace) :
    (∫ w, f w * annShellC N n (z - w)) = ∫ w, annShellC N n w * f (z - w) := by
  simpa only [sub_sub_cancel, mul_comm] using
    (integral_sub_left_eq_self (fun w => annShellC N n w * f (z - w)) volume z)

private theorem integral_taylorKernel (N n : ℕ) {f : ParabolicSpace → ℝ}
    (hf : Continuous f) (σ : ℝ) (x y : ParabolicSpace) :
    (∫ w, f w * taylorKernel (annKernel0C N) n σ x y w) =
      (∫ w, f w * annShellC N n (y - w)) -
        ∑ k ∈ taylorIdx σ,
          (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
            ∫ w, f w * lineIter (multiDirs k) (annShellC N n) (x - w) := by
  let c := fun k : Fin 4 →₀ ℕ =>
    evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k
  have he : (fun w => f w * taylorKernel (annKernel0C N) n σ x y w) =
      (fun w => f w * annShellC N n (y - w) -
        ∑ k ∈ taylorIdx σ, c k * (f w * lineIter (multiDirs k) (annShellC N n) (x - w))) := by
    funext w
    simp only [taylorKernel, annShellC, mul_sub, Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro k _
    simpa only [annShellC] using!
      (mul_left_comm (f w) (c k)
        (lineIter (multiDirs k) (scaledShell (annKernel0C N) n) (x - w)))
  rw [he]
  have hi (k : Fin 4 →₀ ℕ) : Integrable
      (fun w => c k * (f w * lineIter (multiDirs k) (annShellC N n) (x - w))) :=
    (shell_integrand_integrable N n hf _ x).const_mul _
  have hy : Integrable (fun w => f w * annShellC N n (y - w)) := by
    simpa only [lineIter_nil] using shell_integrand_integrable N n hf [] y
  rw [integral_sub hy
    (integrable_finsetSum _ (fun k _ => hi k)), integral_finsetSum _ (fun k _ => hi k)]
  simp only [integral_const_mul]
  rfl

private theorem taylor_polynomial_spatial {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (j : (Fin 4 →₀ ℕ) → ℝ) (x y : ParabolicSpace) :
    (∑ k ∈ taylorIdx σ,
      (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) * j k) =
      j 0 + ∑ i : Fin 3, (parabolicCoords y i.succ - parabolicCoords x i.succ) *
        j (Finsupp.single i.succ 1) := by
  have hz : evalParabolic (MvPolynomial.monomial 0 1) (y - x) / multiFact 0 = 1 := by
    simp [evalParabolic, multiFact]
  have h0 : (0 : Fin 4 →₀ ℕ) ∉
      ({Finsupp.single 1 1, Finsupp.single 2 1, Finsupp.single 3 1} : Finset _) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h | h
    · have hh := congrArg (fun k : Fin 4 →₀ ℕ => k 1) h
      simp at hh
    · have hh := congrArg (fun k : Fin 4 →₀ ℕ => k 2) h
      simp at hh
    · have hh := congrArg (fun k : Fin 4 →₀ ℕ => k 3) h
      simp at hh
  have h1 : (Finsupp.single 1 1 : Fin 4 →₀ ℕ) ∉
      ({Finsupp.single 2 1, Finsupp.single 3 1} : Finset _) := by
    intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h | h <;>
      have hh := congrArg (fun k : Fin 4 →₀ ℕ => k 1) h <;> simp at hh
  have h2 : (Finsupp.single 2 1 : Fin 4 →₀ ℕ) ∉ ({Finsupp.single 3 1} : Finset _) := by
    intro h
    simp only [Finset.mem_singleton] at h
    have hh := congrArg (fun k : Fin 4 →₀ ℕ => k 2) h
    simp at hh
  rw [taylorIdx_spatial hσ1 hσ2, Finset.sum_insert h0, Finset.sum_insert h1,
    Finset.sum_insert h2, Finset.sum_singleton, hz]
  norm_num [evalParabolic, MvPolynomial.eval_monomial, multiFact,
    Fin.prod_univ_succ, Fin.sum_univ_succ, parabolicCoords]

open scoped ContDiff in
/-- The actual first-spatial Taylor subtraction is the sum of the causal
Taylor-kernel integrals [Hai14, (5.14), Definition 5.9]. -/
theorem hairerConvolution_eq_tsum_taylorKernel_spatial (N : ℕ)
    {f : ParabolicSpace → ℝ} (hf : ContDiff ℝ ∞ f) {σ : ℝ}
    (hσ1 : 1 < σ) (hσ2 : σ ≤ 2) (x y : ParabolicSpace) :
    hairerConvolution N f y - hairerConvolution N f x -
      ∑ i : Fin 3, hairerSpatialGradient N f i x *
        (parabolicCoords y i.succ - parabolicCoords x i.succ) =
      ∑' n : ℕ, ∫ w, f w * taylorKernel (annKernel0C N) n σ x y w := by
  let J := fun k : Fin 4 →₀ ℕ =>
    ∑' n : ℕ, ∫ w, f w * lineIter (multiDirs k) (annShellC N n) (x - w)
  have hs0 (z : ParabolicSpace) :
      Summable (fun n : ℕ => ∫ w, f w * annShellC N n (z - w)) := by
    simp_rw [shell_reflect_integral]
    exact (canonicalShell_summable_integral_norm N hf.continuous z).of_norm_bounded
      (fun n => norm_integral_le_integral_norm _)
  have hc (z : ParabolicSpace) :
      (∑' n : ℕ, ∫ w, f w * annShellC N n (z - w)) = hairerConvolution N f z := by
    simp_rw [shell_reflect_integral]
    exact (hairerConvolution_eq_tsum_shellConvolution N hf.continuous z).symm
  have hJ0 : J 0 = hairerConvolution N f x := by
    simpa only [J, multiDirs, Finsupp.toMultiset_zero, Multiset.toList_zero,
      List.map_nil, lineIter_nil] using hc x
  have hJi (i : Fin 3) : J (Finsupp.single i.succ 1) = hairerSpatialGradient N f i x := by
    simp only [J, spatial_multiDirs]
    exact (hairerSpatialGradient_eq_tsum_shellPairing N hf i x).symm
  have hsD (k : Fin 4 →₀ ℕ) (hk : k ∈ taylorIdx σ) :
      Summable (fun n : ℕ => ∫ w,
        f w * lineIter (multiDirs k) (annShellC N n) (x - w)) := by
    have hn : multiDeg k < 2 := by
      exact_mod_cast ((mem_taylorIdx_iff k).1 hk).trans_le hσ2
    rcases polyIndex_two_cases ⟨k, hn⟩ with hk | hk | hk | hk
    · change k = 0 at hk
      rw [hk]
      simpa only [multiDirs, Finsupp.toMultiset_zero, Multiset.toList_zero,
        List.map_nil, lineIter_nil] using hs0 x
    · change k = Finsupp.single (1 : Fin 4) 1 at hk
      rw [hk]
      have hd : multiDirs (Finsupp.single (1 : Fin 4) 1) = [spaceDir 0] := by
        simpa only using! spatial_multiDirs (0 : Fin 3)
      rw [hd]
      exact summable_hairerSpatialShellPairing N hf.continuous 0 x
    · change k = Finsupp.single (2 : Fin 4) 1 at hk
      rw [hk]
      have hd : multiDirs (Finsupp.single (2 : Fin 4) 1) = [spaceDir 1] := by
        simpa only using! spatial_multiDirs (1 : Fin 3)
      rw [hd]
      exact summable_hairerSpatialShellPairing N hf.continuous 1 x
    · change k = Finsupp.single (3 : Fin 4) 1 at hk
      rw [hk]
      have hd : multiDirs (Finsupp.single (3 : Fin 4) 1) = [spaceDir 2] := by
        simpa only using! spatial_multiDirs (2 : Fin 3)
      rw [hd]
      exact summable_hairerSpatialShellPairing N hf.continuous 2 x
  have hsk : ∀ k ∈ taylorIdx σ, Summable (fun n : ℕ =>
      (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) *
        ∫ w, f w * lineIter (multiDirs k) (annShellC N n) (x - w)) :=
    fun k hk => (hsD k hk).mul_left _
  simp_rw [integral_taylorKernel N _ hf.continuous σ x y]
  rw [(hs0 y).tsum_sub (summable_sum hsk), Summable.tsum_finsetSum hsk]
  simp_rw [tsum_mul_left]
  change _ = _ - ∑ k ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) * J k
  rw [hc y, taylor_polynomial_spatial hσ1 hσ2 J x y, hJ0]
  simp_rw [hJi]
  have he : (∑ i : Fin 3, (parabolicCoords y i.succ - parabolicCoords x i.succ) *
        hairerSpatialGradient N f i x) =
      ∑ i : Fin 3, hairerSpatialGradient N f i x *
        (parabolicCoords y i.succ - parabolicCoords x i.succ) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  ring

open scoped ContDiff in
/-- The Taylor profile of the actual convolution uses precisely its value
and its three actual spatial gradient coefficients. -/
theorem hairerTaylorProfile_eq_firstSpatial (N : ℕ) {f : ParabolicSpace → ℝ}
    (hf : ContDiff ℝ ∞ f) {σ : ℝ} (hσ1 : 1 < σ) (hσ2 : σ ≤ 2)
    (x y : ParabolicSpace) :
    taylorProfile (hairerConvolution N f) σ (y - x) x =
      hairerConvolution N f y - hairerConvolution N f x -
        ∑ i : Fin 3, hairerSpatialGradient N f i x *
          (parabolicCoords y i.succ - parabolicCoords x i.succ) := by
  let J : (Fin 4 →₀ ℕ) → ℝ := fun k => lineIter (multiDirs k) (hairerConvolution N f) x
  have hJ0 : J 0 = hairerConvolution N f x := by simp [J, multiDirs, lineIter_nil]
  have hJi (i : Fin 3) : J (Finsupp.single i.succ 1) = hairerSpatialGradient N f i x := by
    change lineIter (multiDirs (Finsupp.single i.succ 1)) (hairerConvolution N f) x = _
    rw [spatial_multiDirs, lineIter_cons, lineIter_nil]
    rw [hairerSpatialGradient_eq_fderiv N hf]
    rfl
  unfold taylorProfile
  rw [show x + (y - x) = y by abel]
  change _ - ∑ k ∈ taylorIdx σ,
    (evalParabolic (MvPolynomial.monomial k 1) (y - x) / multiFact k) * J k = _
  rw [taylor_polynomial_spatial hσ1 hσ2 J x y, hJ0]
  simp_rw [hJi]
  have he : (∑ i : Fin 3, (parabolicCoords y i.succ - parabolicCoords x i.succ) *
      hairerSpatialGradient N f i x) =
      ∑ i : Fin 3, hairerSpatialGradient N f i x *
        (parabolicCoords y i.succ - parabolicCoords x i.succ) :=
    Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [he]
  ring

/-- The actual retained `I(Ψ)` satisfies the source's full first-spatial
Taylor shell identity, without any temporal growth assumption. -/
theorem canonicalPi_integration_shell_sum_psi (N : ℕ) (κ : Kappa)
    (noise : CanonicalNoise) (x y : ParabolicSpace) :
    (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .iPsi) y =
      ∑' n : ℕ, ∫ w,
        (hairerCanonicalData (κ := κ) N noise).canonicalPi x (basis .psi) w *
          taylorKernel (annKernel0C N) n (homogeneity κ .psi + 2) x y w := by
  have hκ0 := κ.property.1
  have hκ1 := κ.property.2
  have h1 : 1 < homogeneity κ .iPsi := by simp only [homogeneity]; linarith
  have h2 : homogeneity κ .iPsi ≤ 2 := by simp only [homogeneity]; linarith
  have h0 : 0 < homogeneity κ .iPsi := zero_lt_one.trans h1
  have hr : homogeneity κ .psi + 2 = homogeneity κ .iPsi := by
    simp only [homogeneity]; ring
  rw [CanonicalData.canonicalPi_integration]
  change hairerConvolution N _ y -
    ((if 0 < homogeneity κ .iPsi then hairerConvolution N _ x else 0) +
      (if 1 < homogeneity κ .iPsi then ∑ i : Fin 3,
        hairerSpatialGradient N _ i x *
          (parabolicCoords y i.succ - parabolicCoords x i.succ) else 0)) = _
  simp only [h0, h1, ite_true]
  have hh := hairerConvolution_eq_tsum_taylorKernel_spatial N
    (canonicalPi_smooth N (κ := κ) noise x (basis .psi))
    (σ := homogeneity κ .psi + 2) (by rwa [hr]) (by rwa [hr]) x y
  convert hh using 1
  ring

end RegularityStructures.Phi43

end

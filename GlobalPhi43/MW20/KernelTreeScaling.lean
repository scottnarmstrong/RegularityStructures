module

public import GlobalPhi43.MW20.TestNormTransport
public import GlobalPhi43.Local.ScalarHolderTransport

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal

/-- The amplitude/degree factor, before any data-dependent supremum. -/
theorem naturalAmplitude_weight {ℓ : ℝ} (hℓ : 0<ℓ) (q : ℕ) (α : ℝ) :
    |ℓ^q| * ℓ^α = ℓ^((q : ℝ)+α) := by
  rw [abs_of_nonneg (pow_nonneg hℓ.le q),← Real.rpow_natCast,← Real.rpow_add hℓ]

/-- Ordinary negative tests: the transported upper scale is exactly ℓ. -/
theorem negativeTreeSeminorm_parabolicPullback (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (a : ℝ) (f : ParabolicSpace → ℝ) (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0<ℓ)
    (D : Set ParabolicSpace) (α : ℝ) :
    negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D α (parabolicPullback a f b ℓ) =
      ENNReal.ofReal (|a| * ℓ^α) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioc 0 ℓ) α (fun _ => f) := by
  have hh := localTestSeminorm_parabolicMap Φ hΦ a (fun _ => f) b hℓ D (Ioc 0 1)
    (fun _ ht => ht.1) α
  have he : (fun _ : ParabolicSpace => parabolicPullback a f b ℓ) =
      (fun _ y => a*f (parabolicMap b ℓ y)) := by
    funext x y
    rfl
  unfold negativeTreeSeminorm
  rw [he]
  simpa only [image_scale_Ioc hℓ] using hh

/-- The three ordinary source entries share the source q+n-degree identity. -/
theorem ordinary_tree_scaling (Φ : ParabolicSpace → ℝ) (hΦ : KernelProfile Φ)
    (J V W : ParabolicSpace → ℝ) (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0<ℓ)
    (D : Set ParabolicSpace) (κ : ℝ) :
    negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D (-1/2-κ) (parabolicPullback ℓ J b ℓ) =
      ENNReal.ofReal (ℓ^(1/2-κ)) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioc 0 ℓ) (-1/2-κ) (fun _ => J) ∧
    negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D (-1-2*κ) (parabolicPullback (ℓ^2) V b ℓ) =
      ENNReal.ofReal (ℓ^(2*(1/2-κ))) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioc 0 ℓ) (-1-2*κ) (fun _ => V) ∧
    negativeTreeSeminorm (mw20TestingKernel Φ hΦ) D (-3/2-3*κ) (parabolicPullback (ℓ^3) W b ℓ) =
      ENNReal.ofReal (ℓ^(3*(1/2-κ))) * localTestSeminorm (mw20TestingKernel Φ hΦ)
        (parabolicMap b ℓ '' D) (Ioc 0 ℓ) (-3/2-3*κ) (fun _ => W) := by
  have hc (q : ℕ) (α β : ℝ) (he : (q : ℝ)+α = β) : |ℓ^q| * ℓ^α = ℓ^β := by
    rw [naturalAmplitude_weight hℓ,he]
  refine ⟨?_,?_,?_⟩
  · have hh := negativeTreeSeminorm_parabolicPullback Φ hΦ ℓ J b hℓ D (-1/2-κ)
    have he := hc 1 (-1/2-κ) (1/2-κ) (by norm_num; ring)
    simp only [pow_one] at he
    rwa [he] at hh
  · have hh := negativeTreeSeminorm_parabolicPullback Φ hΦ (ℓ^2) V b hℓ D (-1-2*κ)
    rwa [hc 2 (-1-2*κ) (2*(1/2-κ)) (by norm_num; ring)] at hh
  · have hh := negativeTreeSeminorm_parabolicPullback Φ hΦ (ℓ^3) W b hℓ D (-3/2-3*κ)
    rwa [hc 3 (-3/2-3*κ) (3*(1/2-κ)) (by norm_num; ring)] at hh

/-- Positive Y/Z norms transport pairs; no artificial test-scale cutoff occurs. -/
theorem positive_tree_scaling (Y Z : ParabolicSpace → ℝ) (b : ParabolicSpace)
    {ℓ : ℝ} (hℓ : 0<ℓ) (D : Set ParabolicSpace) (κ : ℝ) :
    scalarHolderSeminorm (parabolicPullback 1 Y b ℓ) D (1-2*κ) =
      ENNReal.ofReal (ℓ^(1-2*κ))*scalarHolderSeminorm Y (parabolicMap b ℓ '' D) (1-2*κ) ∧
    scalarHolderSeminorm (parabolicPullback ℓ Z b ℓ) D (1/2-3*κ) =
      ENNReal.ofReal (ℓ^(3/2-3*κ))*scalarHolderSeminorm Z (parabolicMap b ℓ '' D) (1/2-3*κ) := by
  constructor
  · simpa only [abs_one,one_mul] using
      scalarHolderSeminorm_parabolicPullback 1 Y b hℓ D (1-2*κ)
  · have hh := scalarHolderSeminorm_parabolicPullback ℓ Z b hℓ D (1/2-3*κ)
    have he := naturalAmplitude_weight hℓ 1 (1/2-3*κ)
    simp only [pow_one,Nat.cast_one] at he
    rw [show (1:ℝ)+(1/2-3*κ)=3/2-3*κ by ring] at he
    rwa [he] at hh

end GlobalPhi43.MW20

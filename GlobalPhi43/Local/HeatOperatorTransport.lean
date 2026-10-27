module

public import GlobalPhi43.Local.ParabolicTransport
public import GlobalPhi43.MW20.Setting.HeatOperator
public import Mathlib.Analysis.Calculus.ContDiff.Operations

public section

namespace GlobalPhi43.Local

open RegularityStructures Set Filter
open scoped ContDiff Topology

theorem parabolicMap_hasFDerivAt (b : ParabolicSpace) (ℓ : ℝ) (x : ParabolicSpace) :
    HasFDerivAt (parabolicMap b ℓ) (parabolicDilateCLM ℓ) x := by
  have he : parabolicMap b ℓ = fun z => b+parabolicDilateCLM ℓ z := by
    funext z
    simp only [parabolicMap,parabolicDilateCLM_apply]
  rw [he]
  have hfun : (fun z => b+parabolicDilateCLM ℓ z) =
      ((fun _ : ParabolicSpace => b)+(parabolicDilateCLM ℓ : ParabolicSpace → ParabolicSpace)) := by
    funext z
    rfl
  rw [hfun]
  simpa only [zero_add] using
    (hasFDerivAt_const b x).add (parabolicDilateCLM ℓ).hasFDerivAt

/-- Pointwise Fréchet chain rule on the actual source smoothness domain. -/
theorem fderiv_parabolicPullback_apply (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (x v : ParabolicSpace)
    (hf : DifferentiableAt ℝ f (parabolicMap b ℓ x)) :
    fderiv ℝ (parabolicPullback a f b ℓ) x v =
      a*fderiv ℝ f (parabolicMap b ℓ x) (parabolicDilate ℓ v) := by
  have hd := (hf.hasFDerivAt.comp x (parabolicMap_hasFDerivAt b ℓ x)).const_mul a
  have he : parabolicPullback a f b ℓ = fun z => a*f (parabolicMap b ℓ z) := rfl
  have hfun : (fun y => a*(f ∘ parabolicMap b ℓ) y) =
      (fun z => a*f (parabolicMap b ℓ z)) := by
    funext z
    rfl
  rw [hfun] at hd
  rw [he,hd.fderiv]
  simp only [smul_apply,ContinuousLinearMap.comp_apply,
    parabolicDilateCLM_apply,smul_eq_mul]

/-- Exact transport of the Fréchet heat operator, using only local
smoothness near the actual source point, not global smoothness of f. -/
theorem heatOperator_parabolicPullback (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) {O : Set ParabolicSpace} (hO : IsOpen O)
    (hf : ContDiffOn ℝ ∞ f O) (x : ParabolicSpace) (hx : parabolicMap b ℓ x ∈ O) :
    heatOperator (parabolicPullback a f b ℓ) x =
      a*ℓ^2*heatOperator f (parabolicMap b ℓ x) := by
  have hcf := (hf _ hx).contDiffAt (hO.mem_nhds hx)
  have htime : parabolicDilate ℓ (1,0) = ℓ^2 • ((1,0) : ParabolicSpace) := by
    simp [parabolicDilate,smul_eq_mul]
  have hspace (i : Fin 3) : parabolicDilate ℓ (0,Pi.single i 1) =
      ℓ • ((0,Pi.single i 1) : ParabolicSpace) := by
    simp [parabolicDilate,smul_eq_mul]
  have ht : fderiv ℝ (parabolicPullback a f b ℓ) x (1,0) =
      a*ℓ^2*fderiv ℝ f (parabolicMap b ℓ x) (1,0) := by
    rw [fderiv_parabolicPullback_apply a f b ℓ x _ (hcf.differentiableAt (by simp)),htime]
    simp only [map_smul,smul_eq_mul]
    ring
  have hs (i : Fin 3) :
      fderiv ℝ (fun w => fderiv ℝ (parabolicPullback a f b ℓ) w (0,Pi.single i 1)) x
        (0,Pi.single i 1) =
      a*ℓ^2*fderiv ℝ (fun w => fderiv ℝ f w (0,Pi.single i 1)) (parabolicMap b ℓ x)
        (0,Pi.single i 1) := by
    let g := fun w => fderiv ℝ f w (0,Pi.single i 1)
    have hg : ContDiffAt ℝ ∞ g (parabolicMap b ℓ x) :=
      (hcf.fderiv_right (by simp)).clm_apply contDiffAt_const
    have hnear : ∀ᶠ w in 𝓝 x, parabolicMap b ℓ w ∈ O :=
      (parabolicMap_hasFDerivAt b ℓ x).continuousAt.eventually (hO.mem_nhds hx)
    have he : (fun w => fderiv ℝ (parabolicPullback a f b ℓ) w (0,Pi.single i 1)) =ᶠ[𝓝 x]
        parabolicPullback (a*ℓ) g b ℓ := by
      filter_upwards [hnear] with w hw
      rw [fderiv_parabolicPullback_apply a f b ℓ w _
        (((hf _ hw).contDiffAt (hO.mem_nhds hw)).differentiableAt (by simp)),hspace]
      simp only [map_smul,smul_eq_mul,parabolicPullback,g]
      ring
    rw [he.fderiv_eq,fderiv_parabolicPullback_apply (a*ℓ) g b ℓ x _
      (hg.differentiableAt (by simp)),hspace]
    simp only [map_smul,smul_eq_mul,g]
    ring
  unfold heatOperator
  rw [ht]
  simp only [hs,← Finset.mul_sum]
  ring

end GlobalPhi43.Local

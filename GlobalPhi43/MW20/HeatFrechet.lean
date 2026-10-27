module

public import GlobalPhi43.MW20.LocalMaximum
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The actual coordinate heat operator in terms of Fréchet derivatives
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Filter Topology

/-- The source time derivative is the derivative in direction (1,0). -/
theorem source_time_deriv_eq_fderiv (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hf : DifferentiableAt ℝ f x) :
    deriv (fun t => f (t, x.2)) x.1 = fderiv ℝ f x (1, 0) := by
  have ht := (hasDerivAt_id x.1).prodMk (hasDerivAt_const x.1 x.2)
  exact (hf.hasFDerivAt.comp_hasDerivAt x.1 ht).deriv

/-- The source spatial derivative is the derivative in its coordinate direction. -/
theorem source_space_deriv_eq_fderiv (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hf : DifferentiableAt ℝ f x) (i : Fin 3) :
    deriv (fun a => f (x.1, Function.update x.2 i a)) (x.2 i) =
      fderiv ℝ f x (0, Pi.single i 1) := by
  have ht := (hasDerivAt_const (x.2 i) x.1).prodMk (hasDerivAt_update x.2 i (x.2 i))
  have hd := hf.hasFDerivAt.comp_hasDerivAt_of_eq (x.2 i) ht
    (by simp only [Function.update_eq_self])
  exact hd.deriv

/-- The second coordinate derivative is the iterated Fréchet derivative on
the same coordinate direction. Only local differentiability is required. -/
theorem source_space_second_deriv_eq_fderiv (f : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z)
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) (i : Fin 3) :
    deriv (deriv (fun a => f (x.1, Function.update x.2 i a))) (x.2 i) =
      fderiv ℝ (fderiv ℝ f) x (0, Pi.single i 1) (0, Pi.single i 1) := by
  let e : ParabolicSpace := (0, Pi.single i 1)
  have ht := (hasDerivAt_const (x.2 i) x.1).prodMk (hasDerivAt_update x.2 i (x.2 i))
  have hd := hdf.hasFDerivAt.comp_hasDerivAt_of_eq (x.2 i) ht
    (by simp only [Function.update_eq_self])
  have heval := hd.clm_apply (hasDerivAt_const (x.2 i) e)
  have heq : deriv (fun a => f (x.1, Function.update x.2 i a)) =ᶠ[𝓝 (x.2 i)]
      (fun a => fderiv ℝ f (x.1, Function.update x.2 i a) e) := by
    have hcont : Continuous (fun a => (x.1, Function.update x.2 i a)) :=
      continuous_const.prodMk (continuous_iff_continuousAt.mpr
        (fun a => (hasDerivAt_update x.2 i a).continuousAt))
    have hto : Tendsto (fun a => (x.1, Function.update x.2 i a))
        (𝓝 (x.2 i)) (𝓝 x) := by
      simpa only [Function.update_eq_self] using (hcont.continuousAt (x := x.2 i)).tendsto
    have ha := hto.eventually hf
    filter_upwards [ha] with a hfa
    have hline := (hasDerivAt_const a x.1).prodMk (hasDerivAt_update x.2 i a)
    exact (hfa.hasFDerivAt.comp_hasDerivAt a hline).deriv
  have hfinal := heval.congr_of_eventuallyEq heq
  simpa only [Function.comp_def, ContinuousLinearMap.map_zero, add_zero, e] using hfinal.deriv

/-- The literal coordinate source heat operator has this linear expression
in the actual first and second Fréchet derivatives. -/
theorem sourceHeat_eq_fderiv (f : ParabolicSpace → ℝ) (x : ParabolicSpace)
    (hf : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z)
    (hdf : DifferentiableAt ℝ (fderiv ℝ f) x) :
    sourceHeat f x = fderiv ℝ f x (1, 0) -
      ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) x (0, Pi.single i 1) (0, Pi.single i 1) := by
  rw [sourceHeat, source_time_deriv_eq_fderiv f x hf.self_of_nhds]
  simp only [source_space_second_deriv_eq_fderiv f x hf hdf]

/-- A C² germ supplies all local differentiability hypotheses in the
Fréchet expression for the source heat operator. -/
theorem sourceHeat_eq_fderiv_of_contDiffAt (f : ParabolicSpace → ℝ)
    (x : ParabolicSpace) (hf : ContDiffAt ℝ 2 f x) :
    sourceHeat f x = fderiv ℝ f x (1, 0) -
      ∑ i : Fin 3, fderiv ℝ (fderiv ℝ f) x (0, Pi.single i 1) (0, Pi.single i 1) := by
  have hnear : ∀ᶠ z in 𝓝 x, DifferentiableAt ℝ f z :=
    (hf.eventually (by norm_num)).mono fun z hz => hz.differentiableAt (by norm_num)
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) x := hf.fderiv_right (m := 1) (by norm_num)
  exact sourceHeat_eq_fderiv f x hnear (hd.differentiableAt one_ne_zero)

end GlobalPhi43.MW20

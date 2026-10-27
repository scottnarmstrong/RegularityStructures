module

public import GlobalPhi43.Local.RadiusGeometry
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The diagonal spatial derivative in MW20 (2.6)

A finite remainder of order greater than one forces each affine coefficient
to equal the corresponding spatial derivative on the diagonal. Thus finite
local Hölder control cannot be achieved by a different coefficient choice.
No infinite testing kernel is involved in this selection.
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set Filter
open scoped Topology ContDiff

/-- A finite positive-order affine remainder forces the diagonal value to
vanish; it need not be an additional hypothesis in (2.6). -/
theorem affine_bound_at_zero {f : ℝ → ℝ} {a C γ r : ℝ}
    (hf : ContinuousAt f 0) (hγ : 0 < γ) (hr : 0 < r)
    (hbound : ∀ t ∈ Ioo 0 r, |f t - a * t| ≤ C * t ^ γ) : f 0 = 0 := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hs : Tendsto (fun t => |f t - a * t|) (𝓝[>] 0) (𝓝 |f 0|) := by
    simpa using ((hf.tendsto.mono_left nhdsWithin_le_nhds).sub
      (tendsto_const_nhds.mul hid)).abs
  have hp : Tendsto (fun t : ℝ => C * t ^ γ) (𝓝[>] 0) (𝓝 0) := by
    have hpow := (Real.continuous_rpow_const hγ.le).tendsto (0 : ℝ)
    simpa only [Real.zero_rpow (ne_of_gt hγ), mul_zero] using
      (tendsto_const_nhds.mul hpow).mono_left nhdsWithin_le_nhds
  apply abs_nonpos_iff.mp
  apply le_of_tendsto_of_tendsto hs hp
  filter_upwards [Ioo_mem_nhdsGT hr] with t ht using hbound t ht

/-- A finite superlinear affine remainder identifies the derivative. -/
theorem affine_coefficient_eq_deriv {f : ℝ → ℝ} {a b C γ r : ℝ}
    (hf : HasDerivAt f b 0) (hγ : 1 < γ) (hr : 0 < r)
    (hbound : ∀ t ∈ Ioo 0 r, |f t - a * t| ≤ C * t ^ γ) : b = a := by
  have hf₀ := affine_bound_at_zero hf.continuousAt (by linarith : 0 < γ) hr hbound
  have hs : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 b) := by
    simpa only [zero_add, hf₀, sub_zero, smul_eq_mul, div_eq_mul_inv, mul_comm] using
      hf.tendsto_slope_zero_right
  have hp : Tendsto (fun t : ℝ => C * t ^ (γ - 1)) (𝓝[>] 0) (𝓝 0) := by
    have hpow := (Real.continuous_rpow_const (by linarith : 0 ≤ γ - 1)).tendsto (0 : ℝ)
    simpa only [Real.zero_rpow (by linarith : γ - 1 ≠ 0), mul_zero] using
      (tendsto_const_nhds.mul hpow).mono_left nhdsWithin_le_nhds
  have he : ∀ᶠ t in 𝓝[>] (0 : ℝ), |f t / t - a| ≤ C * t ^ (γ - 1) := by
    filter_upwards [Ioo_mem_nhdsGT hr] with t ht
    calc
      |f t / t - a| = |(f t - a * t) / t| := by
        rw [sub_div, mul_div_cancel_right₀ _ (ne_of_gt ht.1)]
      _ = |f t - a * t| / t := by rw [abs_div, abs_of_pos ht.1]
      _ ≤ C * t ^ γ / t := div_le_div_of_nonneg_right (hbound t ht) ht.1.le
      _ = C * t ^ (γ - 1) := by rw [Real.rpow_sub ht.1, Real.rpow_one]; ring
  have hb : |b - a| ≤ 0 := le_of_tendsto_of_tendsto (hs.sub_const a).abs hp he
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)

/-- Vary just one spatial coordinate in the second argument of a germ. -/
@[expose] def spatialCoordinateLine (x : ParabolicSpace) (i : Fin 3) (t : ℝ) :
    ParabolicSpace := (x.1, x.2 + t • Pi.single i (1 : ℝ))

/-- MW20's prescribed optimal coefficient: the spatial derivative in the
second variable at the diagonal, written in coordinate directions. -/
@[expose] noncomputable def diagonalSpatialCoefficient
    (U : ParabolicSpace × ParabolicSpace → ℝ) (x : ParabolicSpace) (i : Fin 3) : ℝ :=
  deriv (fun t => U (x, spatialCoordinateLine x i t)) 0

/-- Source smoothness supplies the derivative used by the canonical choice. -/
theorem hasDerivAt_diagonalSpatialCoefficient
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (x : ParabolicSpace) (i : Fin 3) :
    HasDerivAt (fun t => U (x, spatialCoordinateLine x i t))
      (diagonalSpatialCoefficient U x i) 0 := by
  have hl : ContDiff ℝ ∞ (fun t => (x, spatialCoordinateLine x i t)) := by
    unfold spatialCoordinateLine
    fun_prop
  exact ((hU.comp hl).differentiable (by simp)).differentiableAt.hasDerivAt

/-- Every finite superlinear affine remainder on coordinate rays selects
exactly the source's diagonal spatial gradient. The rays may be arbitrarily
short, so this applies inside each open local domain. -/
theorem diagonalSpatialCoefficient_eq_of_affine_bound
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (x : ParabolicSpace) (ν : Fin 3 → ℝ)
    {γ C r : ℝ} (hγ : 1 < γ) (hr : 0 < r)
    (hbound : ∀ i t, t ∈ Ioo 0 r →
      |U (x, spatialCoordinateLine x i t) - ν i * t| ≤ C * t ^ γ) :
    diagonalSpatialCoefficient U x = ν := by
  funext i
  apply affine_coefficient_eq_deriv (hasDerivAt_diagonalSpatialCoefficient U hU x i)
    hγ hr
  exact hbound i

/-- Spatial coordinate rays have their exact ambient distance. -/
theorem spatialCoordinateLine_dist (x : ParabolicSpace) (i : Fin 3) (t : ℝ) :
    dist (spatialCoordinateLine x i t) x = |t| := by
  simp [spatialCoordinateLine, dist_eq_norm, Prod.norm_def, Pi.norm_single, norm_smul]

/-- The same rays have exactly the same max parabolic distance. -/
theorem spatialCoordinateLine_pdist (x : ParabolicSpace) (i : Fin 3) (t : ℝ) :
    pdist x (spatialCoordinateLine x i t) = |t| := by
  simp [spatialCoordinateLine, pdist, Pi.norm_single, norm_smul]

/-- The source's spatial affine term on a coordinate ray. -/
theorem spatialCoordinateLine_affine (x : ParabolicSpace) (i : Fin 3) (t : ℝ)
    (ν : Fin 3 → ℝ) :
    (∑ j, ν j * ((spatialCoordinateLine x i t).2 j - x.2 j)) = ν i * t := by
  simp [spatialCoordinateLine, Pi.single_apply, mul_ite]

/-- On every open source domain, any coefficient with finite Hölder remainder
is exactly the spatial derivative on the diagonal specified after (2.6). -/
theorem diagonalSpatialCoefficient_eq_on_open
    (U : ParabolicSpace × ParabolicSpace → ℝ) (hU : ContDiff ℝ ∞ U)
    (D : Set ParabolicSpace) (hD : IsOpen D) {x : ParabolicSpace} (hx : x ∈ D)
    (ν : Fin 3 → ℝ) {γ C : ℝ} (hγ : 1 < γ)
    (hbound : ∀ y ∈ D, y ≠ x →
      |U (x, y) - ∑ j, ν j * (y.2 j - x.2 j)| ≤ C * pdist x y ^ γ) :
    diagonalSpatialCoefficient U x = ν := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hD x hx
  apply diagonalSpatialCoefficient_eq_of_affine_bound U hU x ν hγ hr
  intro i t ht
  have hy : spatialCoordinateLine x i t ∈ D := hball (by
    rw [Metric.mem_ball, spatialCoordinateLine_dist, abs_of_pos ht.1]
    exact ht.2)
  have hne : spatialCoordinateLine x i t ≠ x := by
    intro he
    have hh := spatialCoordinateLine_dist x i t
    rw [he, dist_self, abs_of_pos ht.1] at hh
    linarith [ht.1]
  simpa only [spatialCoordinateLine_affine, spatialCoordinateLine_pdist, abs_of_pos ht.1] using
    hbound _ hy hne

end GlobalPhi43.MW20

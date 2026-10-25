/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HeatKernel
public import RegularityStructures.PDE.TorusLift

/-!
# The heat operator on `C(T³, E)`

For a Banach space `E`, `t ∈ ℝ` and `g ∈ C(T³, E)`,
`heatOp t g x = ∫_{ℝ³} γ₁(z) g(x - √t z) dz`, where `γ₁ = gaussKernel 1` is the unit-time heat
kernel on `ℝ³`. For `t > 0` this is the heat semigroup `P_t g(x) = ∫ γ_t(y) g(x - y) dy` after the
substitution `y = √t z`. For `t ≤ 0` the square root vanishes and `heatOp t g = g`.

Writing the operator with the unit Gaussian makes the dependence on `t` sit inside the argument of
`g`, so continuity in `(t, x)`, up to and including `t = 0`, is one application of dominated
convergence.

## Main results

* `norm_heatOp_le`: `P_t` contracts the supremum norm;
* `heatOpCLM`: `P_t` as a continuous linear map;
* `continuous_heatOp`: `(t, g) ↦ P_t g` is jointly continuous, so `t ↦ P_t g` is a continuous path
  in `C(T³, E)` with `P_0 g = g`;
* `heatOp_torusShift`, `heatOp_compLeftContinuous`: `P_t` commutes with translations and with
  continuous linear maps of the values.
-/

open MeasureTheory Real Filter Topology

namespace RegularityStructures.PDE

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-! ### The unit Gaussian -/

public section

@[fun_prop]
theorem continuous_gaussKernel_one : Continuous (gaussKernel 1) := by
  unfold gaussKernel sqNorm3
  fun_prop

theorem integrable_gaussKernel_one : Integrable (gaussKernel 1) :=
  integrable_gaussKernel one_pos

theorem integral_gaussKernel_one : ∫ z, gaussKernel 1 z = 1 :=
  integral_gaussKernel one_pos

theorem gaussKernel_one_nonneg (z : Fin 3 → ℝ) : 0 ≤ gaussKernel 1 z :=
  gaussKernel_nonneg one_pos z

/-! ### The integrand -/

theorem continuous_heatOp_integrand (g : C(Torus3, E)) (z : Fin 3 → ℝ) :
    Continuous fun p : ℝ × Torus3 => gaussKernel 1 z • g (p.2 - torusProj (√p.1 • z)) := by
  have h1 : Continuous fun p : ℝ × Torus3 => torusProj (√p.1 • z) :=
    continuous_torusProj.comp ((continuous_sqrt.comp continuous_fst).smul continuous_const)
  exact continuous_const.smul (g.continuous.comp (continuous_snd.sub h1))

theorem continuous_heatOp_integrand_right (g : C(Torus3, E)) (t : ℝ) (x : Torus3) :
    Continuous fun z : Fin 3 → ℝ => gaussKernel 1 z • g (x - torusProj (√t • z)) :=
  continuous_gaussKernel_one.smul (g.continuous.comp (continuous_const.sub
    (continuous_torusProj.comp (continuous_const_smul _))))

theorem norm_heatOp_integrand_le (g : C(Torus3, E)) (t : ℝ) (x : Torus3) (z : Fin 3 → ℝ) :
    ‖gaussKernel 1 z • g (x - torusProj (√t • z))‖ ≤ gaussKernel 1 z * ‖g‖ := by
  rw [norm_smul, Real.norm_of_nonneg (gaussKernel_one_nonneg z)]
  exact mul_le_mul_of_nonneg_left (g.norm_coe_le_norm _) (gaussKernel_one_nonneg z)

theorem integrable_heatOp_integrand (g : C(Torus3, E)) (t : ℝ) (x : Torus3) :
    Integrable fun z => gaussKernel 1 z • g (x - torusProj (√t • z)) :=
  (integrable_gaussKernel_one.mul_const ‖g‖).mono'
    (continuous_heatOp_integrand_right g t x).aestronglyMeasurable
    (Eventually.of_forall (norm_heatOp_integrand_le g t x))

theorem continuous_heatOpFun (g : C(Torus3, E)) :
    Continuous fun p : ℝ × Torus3 =>
      ∫ z : Fin 3 → ℝ, gaussKernel 1 z • g (p.2 - torusProj (√p.1 • z)) :=
  continuous_of_dominated
    (fun p => (continuous_heatOp_integrand_right g p.1 p.2).aestronglyMeasurable)
    (fun p => Eventually.of_forall (norm_heatOp_integrand_le g p.1 p.2))
    (integrable_gaussKernel_one.mul_const ‖g‖)
    (Eventually.of_forall (continuous_heatOp_integrand g))

end

/-! ### The operator -/

@[expose] public noncomputable section

/-- The heat operator `P_t g(x) = ∫_{ℝ³} γ₁(z) g(x - √t z) dz` on `C(T³, E)`. It is the heat
semigroup for `t > 0` and the identity for `t ≤ 0`. -/
def heatOp (t : ℝ) (g : C(Torus3, E)) : C(Torus3, E) where
  toFun x := ∫ z : Fin 3 → ℝ, gaussKernel 1 z • g (x - torusProj (√t • z))
  continuous_toFun :=
    (continuous_heatOpFun g).comp (Continuous.prodMk continuous_const continuous_id)

end

public section

theorem heatOp_apply (t : ℝ) (g : C(Torus3, E)) (x : Torus3) :
    heatOp t g x = ∫ z : Fin 3 → ℝ, gaussKernel 1 z • g (x - torusProj (√t • z)) := rfl

theorem heatOp_torusProj (t : ℝ) (g : C(Torus3, E)) (y : Fin 3 → ℝ) :
    heatOp t g (torusProj y) = ∫ z : Fin 3 → ℝ, gaussKernel 1 z • g (torusProj (y - √t • z)) := by
  simp_rw [heatOp_apply, torusProj_sub]

theorem norm_heatOp_apply_le (t : ℝ) (g : C(Torus3, E)) (x : Torus3) :
    ‖heatOp t g x‖ ≤ ‖g‖ := by
  rw [heatOp_apply]
  calc ‖∫ z, gaussKernel 1 z • g (x - torusProj (√t • z))‖
      ≤ ∫ z, gaussKernel 1 z * ‖g‖ :=
        norm_integral_le_of_norm_le (integrable_gaussKernel_one.mul_const _)
          (Eventually.of_forall (norm_heatOp_integrand_le g t x))
    _ = ‖g‖ := by rw [integral_mul_const, integral_gaussKernel_one, one_mul]

/-- `P_t` contracts the supremum norm. -/
theorem norm_heatOp_le (t : ℝ) (g : C(Torus3, E)) : ‖heatOp t g‖ ≤ ‖g‖ :=
  (ContinuousMap.norm_le _ (norm_nonneg _)).2 (norm_heatOp_apply_le t g)

theorem heatOp_add (t : ℝ) (g h : C(Torus3, E)) : heatOp t (g + h) = heatOp t g + heatOp t h := by
  ext x
  simp only [ContinuousMap.add_apply, heatOp_apply, smul_add]
  exact integral_add (integrable_heatOp_integrand g t x) (integrable_heatOp_integrand h t x)

theorem heatOp_smul (t c : ℝ) (g : C(Torus3, E)) : heatOp t (c • g) = c • heatOp t g := by
  ext x
  simp only [ContinuousMap.smul_apply, heatOp_apply, smul_comm (gaussKernel 1 _) c]
  exact integral_smul c _

theorem heatOp_neg (t : ℝ) (g : C(Torus3, E)) : heatOp t (-g) = -heatOp t g := by
  simpa using heatOp_smul t (-1) g

theorem heatOp_sub (t : ℝ) (g h : C(Torus3, E)) : heatOp t (g - h) = heatOp t g - heatOp t h := by
  rw [sub_eq_add_neg, heatOp_add, heatOp_neg, ← sub_eq_add_neg]

theorem heatOp_zero_right (t : ℝ) : heatOp t (0 : C(Torus3, E)) = 0 := by
  simpa using heatOp_smul t 0 (0 : C(Torus3, E))

theorem heatOp_torusShift (t : ℝ) (a : Torus3) (g : C(Torus3, E)) :
    heatOp t (torusShift a g) = torusShift a (heatOp t g) := by
  ext x
  simp only [heatOp_apply, torusShift_apply, sub_add_eq_add_sub]

variable [CompleteSpace E]

theorem heatOp_of_nonpos {t : ℝ} (ht : t ≤ 0) (g : C(Torus3, E)) : heatOp t g = g := by
  ext x
  rw [heatOp_apply, Real.sqrt_eq_zero'.2 ht]
  simp only [zero_smul, torusProj_zero, sub_zero]
  rw [integral_smul_const, integral_gaussKernel_one, one_smul]

theorem heatOp_zero_left (g : C(Torus3, E)) : heatOp 0 g = g :=
  heatOp_of_nonpos le_rfl g

end

@[expose] public noncomputable section

variable [CompleteSpace E]

/-- `P_t` as a continuous linear map of norm at most one. -/
def heatOpCLM (t : ℝ) : C(Torus3, E) →L[ℝ] C(Torus3, E) :=
  LinearMap.mkContinuous
    { toFun := heatOp t
      map_add' := heatOp_add t
      map_smul' := heatOp_smul t } 1 fun g => by simpa using norm_heatOp_le t g

end

public section

@[simp]
theorem heatOpCLM_apply [CompleteSpace E] (t : ℝ) (g : C(Torus3, E)) :
    heatOpCLM t g = heatOp t g := rfl

theorem norm_heatOp_sub_le (t : ℝ) (g h : C(Torus3, E)) :
    ‖heatOp t g - heatOp t h‖ ≤ ‖g - h‖ := by
  rw [← heatOp_sub]
  exact norm_heatOp_le t _

/-- For fixed `g`, `t ↦ P_t g` is a continuous path in `C(T³, E)`. -/
theorem continuous_heatOp_left (g : C(Torus3, E)) : Continuous fun t => heatOp t g :=
  (ContinuousMap.curry ⟨_, continuous_heatOpFun g⟩).continuous

/-- `(t, g) ↦ P_t g` is jointly continuous. -/
theorem continuous_heatOp : Continuous fun p : ℝ × C(Torus3, E) => heatOp p.1 p.2 := by
  rw [continuous_iff_continuousAt]
  rintro ⟨t₀, g₀⟩
  rw [ContinuousAt, tendsto_iff_norm_sub_tendsto_zero]
  have h1 : Tendsto (fun p : ℝ × C(Torus3, E) => ‖heatOp p.1 g₀ - heatOp t₀ g₀‖)
      (𝓝 (t₀, g₀)) (𝓝 0) := by
    have := ((continuous_heatOp_left g₀).comp continuous_fst).tendsto (t₀, g₀)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  have h2 : Tendsto (fun p : ℝ × C(Torus3, E) => ‖p.2 - g₀‖) (𝓝 (t₀, g₀)) (𝓝 0) := by
    have := (continuous_snd (X := ℝ) (Y := C(Torus3, E))).tendsto (t₀, g₀)
    rw [tendsto_iff_norm_sub_tendsto_zero] at this
    exact this
  refine squeeze_zero (fun _ => norm_nonneg _) (fun p => ?_) (by simpa using h2.add h1)
  calc ‖heatOp p.1 p.2 - heatOp t₀ g₀‖
      = ‖(heatOp p.1 p.2 - heatOp p.1 g₀) + (heatOp p.1 g₀ - heatOp t₀ g₀)‖ := by abel_nf
    _ ≤ ‖heatOp p.1 p.2 - heatOp p.1 g₀‖ + ‖heatOp p.1 g₀ - heatOp t₀ g₀‖ := norm_add_le _ _
    _ ≤ ‖p.2 - g₀‖ + ‖heatOp p.1 g₀ - heatOp t₀ g₀‖ := by
        gcongr
        exact norm_heatOp_sub_le _ _ _

theorem _root_.Continuous.heatOp {X : Type*} [TopologicalSpace X] {t : X → ℝ} {g : X → C(Torus3, E)}
    (ht : Continuous t) (hg : Continuous g) : Continuous fun x => heatOp (t x) (g x) :=
  continuous_heatOp.comp (ht.prodMk hg)

/-! ### Commutation with translations and with linear maps of the values -/

variable [CompleteSpace E] [CompleteSpace F]

theorem heatOp_compLeftContinuous (t : ℝ) (L : E →L[ℝ] F) (g : C(Torus3, E)) :
    heatOp t (L.compLeftContinuous ℝ Torus3 g) = L.compLeftContinuous ℝ Torus3 (heatOp t g) := by
  ext x
  simp only [heatOp_apply, compLeftContinuous_apply_apply]
  rw [← L.integral_comp_comm (integrable_heatOp_integrand g t x)]
  simp only [L.map_smul]

end

end RegularityStructures.PDE

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Theorem A: the renormalised dynamical Φ⁴₃ model on the three-torus

A standalone, Mathlib-only statement of local well-posedness and convergence of the renormalised
dynamical Φ⁴₃ model on `T³` (M. Hairer, *A theory of regularity structures*, Invent. Math. 198
(2014), Theorem 1.15), together with the theorems showing that its hypotheses can be met.

Let `W` be a space-time white noise on `ℝ × T³`, `ρ` a mollifier, and `ξ_ε` the regularised noise
`ξ_ε(z) = W(ρ_ε^♯(z - ·))`. Let `u_ε` be the classical solution of
`∂_t u_ε = Δu_ε - u_ε³ + (a + 3C₁^ε - 9C₂^ε) u_ε + ξ_ε`, `u_ε(0) = u₀`, with smooth `u₀` and the
explicit constants `C₁^ε = ∫ G_ε²`, `C₂^ε = 2 ∫ G Q_ε²`, where `G` is the massive heat kernel,
`G_ε = G * ρ_ε^♯` and `Q_ε(z) = ∫ G_ε(z + w) G_ε(w) dw`.

* `theoremA`: for `η ∈ (-2/3, -1/2)` there are a random time `τ > 0` and a random path `v` in the
  Hölder–Besov space `𝒞^η`, continuous on `[0, τ)` with `v(0) = u₀` and exploding in `𝒞^η` at `τ`
  when `τ < ∞`, such that `u_ε → v` in probability in `𝒞^η`, uniformly on `[0, T]` on `{τ > T}`, as
  `ε ↓ 0`. The pair `(τ, v)` does not depend on the mollifier (up to null sets).
* `phi43Limit_unique`: for given solutions `u_ε`, the pair `(τ, v)` is unique up to null sets.
* `exists_whiteNoise`: a space-time white noise exists.
* `regularisedNoise_exists_unique`: the regularised noise exists, is unique up to null sets, and is
  jointly measurable.
* `classicalSolution_exists_unique`: for smooth forcing and smooth initial data the equation has a
  global classical solution, unique on `[0, ∞)`.
* `constants_finite`: every integral in the definitions of `C₁^ε` and `C₂^ε` is absolutely
  convergent, so the constants are not junk values of Lean's totalised integral.

Compared with Hairer's Theorem 1.15, the initial data are smooth rather than in `𝒞^α`, the
renormalisation constants are the displayed explicit ones (built from the massive heat kernel)
rather than "suitably chosen" ones, and convergence is stated up to the explosion time of the
limit.

Conventions: `T³ = ℝ³/ℤ³` is `UnitAddTorus (Fin 3)`, points of `ℝ³` are functions `Fin 3 → ℝ`,
and derivatives are taken on spatially periodic lifts to `ℝ × ℝ³`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TheoremAChallenge

/-! ## The torus and space-time -/

/-- The three-torus `T³ = ℝ³/ℤ³`. -/
abbrev Torus3 : Type := UnitAddTorus (Fin 3)

/-- Space-time `ℝ × T³`. -/
abbrev SpaceTime : Type := ℝ × Torus3

/-- The projection `ℝ³ → T³`. -/
def torusProj (y : Fin 3 → ℝ) : Torus3 := fun i => ((y i : ℝ) : UnitAddCircle)

/-- The representative of a point of `T³` in `[0, 1)³`. -/
def torusRep (x : Torus3) : Fin 3 → ℝ := fun i => (AddCircle.equivIco (1 : ℝ) 0 (x i) : ℝ)

/-- The Euclidean square norm `|v|² = v₁² + v₂² + v₃²` on `ℝ³`. -/
def sqNorm3 (v : Fin 3 → ℝ) : ℝ := ∑ i, v i ^ 2

open scoped ContDiff in
/-- A function on `T³` is smooth if its periodic lift to `ℝ³` is smooth. -/
def IsSmoothOnTorus (f : Torus3 → ℝ) : Prop := ContDiff ℝ ∞ (fun y => f (torusProj y))

open scoped ContDiff in
/-- A function on `ℝ × T³` is smooth if its spatially periodic lift to `ℝ × ℝ³` is smooth. -/
def IsSmoothOnSpaceTime (g : SpaceTime → ℝ) : Prop :=
  ContDiff ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => g (p.1, torusProj p.2))

/-! ## Heat kernels -/

/-- The heat kernel on `ℝ³`: `gaussKernel t y = (4πt)^{-3/2} exp(-|y|²/(4t))`. -/
def gaussKernel (t : ℝ) (y : Fin 3 → ℝ) : ℝ :=
  (4 * Real.pi * t) ^ (-(3 : ℝ) / 2) * Real.exp (-sqNorm3 y / (4 * t))

/-- The heat kernel on `T³`, `p_t(x) = ∑_{k ∈ ℤ³} (4πt)^{-3/2} exp(-|x + k|²/(4t))`, evaluated at
the representative of `x` in `[0, 1)³`. -/
def heatKernel (t : ℝ) (x : Torus3) : ℝ :=
  ∑' k : Fin 3 → ℤ, gaussKernel t (torusRep x + fun i => (k i : ℝ))

/-- The heat semigroup on `T³`: `(P_s f)(x) = ∫_{ℝ³} γ_s(y) f(x - y) dy`, where `γ_s` is the
heat kernel on `ℝ³` and `x - y` is taken in `T³`. -/
def heatSemigroup (s : ℝ) (f : C(Torus3, ℝ)) (x : Torus3) : ℝ :=
  ∫ y : Fin 3 → ℝ, gaussKernel s y * f (x - torusProj y)

/-- The massive space-time heat kernel `G(t, x) = 1_{t>0} e^{-t} p_t(x)` on `ℝ × T³`, the kernel of
`(∂_t - Δ + 1)⁻¹`. -/
def massiveHeatKernel (z : SpaceTime) : ℝ :=
  if 0 < z.1 then Real.exp (-z.1) * heatKernel z.1 z.2 else 0

/-! ## Hölder–Besov spaces of negative order

For `η < 0`, `‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_x |P_s f(x)|` on `C(T³)`, and `𝒞^η` is the
completion of `C(T³)` for this norm. The lemmas below only show that `‖·‖_η` is a finite
seminorm, which the completion needs. -/

/-- Negative regularity exponents `η < 0`. -/
abbrev NegExponent : Type := {η : ℝ // η < 0}

/-- `‖f‖_η = sup_{0 < s ≤ 1} s^{-η/2} sup_x |P_s f(x)|`, as an extended real. -/
def holderBesovENorm (η : ℝ) (f : C(Torus3, ℝ)) : ℝ≥0∞ :=
  ⨆ s ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ

/-- For `s > 0`, `γ_s` is a probability density on `ℝ³`. -/
theorem gaussKernel_density {s : ℝ} (hs : 0 < s) :
    (∀ y, 0 ≤ gaussKernel s y) ∧ Integrable (gaussKernel s) ∧ ∫ y, gaussKernel s y = 1 := by
  have ha : 0 < 4 * Real.pi * s := by positivity
  have hb : 0 < (4 * s)⁻¹ := by positivity
  have hprod : ∀ y, gaussKernel s y =
      (4 * Real.pi * s) ^ (-(3 : ℝ) / 2) * ∏ i, Real.exp (-(4 * s)⁻¹ * y i ^ 2) := fun y => by
    rw [gaussKernel, ← Real.exp_sum, sqNorm3, ← Finset.mul_sum]
    ring_nf
  refine ⟨fun y => by unfold gaussKernel; positivity, ?_, ?_⟩
  · exact ((Integrable.fintype_prod (ι := Fin 3) (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ v => Real.exp (-(4 * s)⁻¹ * v ^ 2)) fun _ =>
        integrable_exp_neg_mul_sq hb).const_mul ((4 * Real.pi * s) ^ (-(3 : ℝ) / 2))).congr
      (Eventually.of_forall fun y => (hprod y).symm)
  · simp_rw [hprod]
    rw [integral_const_mul, integral_fintype_prod_volume_eq_pow (ι := Fin 3)
      (fun v : ℝ => Real.exp (-(4 * s)⁻¹ * v ^ 2)), integral_gaussian, Fintype.card_fin,
      show Real.pi / (4 * s)⁻¹ = 4 * Real.pi * s by field_simp, Real.sqrt_eq_rpow,
      ← Real.rpow_natCast, ← Real.rpow_mul ha.le, ← Real.rpow_add ha]
    norm_num

theorem integrable_heatSemigroup_integrand {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ))
    (x : Torus3) : Integrable fun y : Fin 3 → ℝ => gaussKernel s y * f (x - torusProj y) :=
  (gaussKernel_density hs).2.1.mul_bdd (c := ‖f‖)
    (f.continuous.comp (continuous_const.sub (continuous_pi fun i =>
      (AddCircle.continuous_mk' (1 : ℝ)).comp (continuous_apply i)))).aestronglyMeasurable
    (Eventually.of_forall fun _ => f.norm_coe_le_norm _)

/-- `|P_s f(x)| ≤ ‖f‖_∞`. -/
theorem norm_heatSemigroup_le {s : ℝ} (hs : 0 < s) (f : C(Torus3, ℝ)) (x : Torus3) :
    ‖heatSemigroup s f x‖ ≤ ‖f‖ := by
  obtain ⟨hnn, hint, hone⟩ := gaussKernel_density hs
  calc ‖∫ y, gaussKernel s y * f (x - torusProj y)‖
      ≤ ∫ y, gaussKernel s y * ‖f‖ := by
        refine norm_integral_le_of_norm_le (hint.mul_const _) (Eventually.of_forall fun y => ?_)
        rw [norm_mul, Real.norm_of_nonneg (hnn y)]
        exact mul_le_mul_of_nonneg_left (f.norm_coe_le_norm _) (hnn y)
    _ = ‖f‖ := by rw [integral_mul_const, hone, one_mul]

theorem holderBesovENorm_lt_top {η : ℝ} (hη : η ≤ 0) (f : C(Torus3, ℝ)) :
    holderBesovENorm η f < ⊤ := by
  refine lt_of_le_of_lt (iSup₂_le fun s hs => ?_) (enorm_lt_top (x := f))
  have h1 : ENNReal.ofReal (s ^ (-η / 2)) ≤ 1 :=
    ENNReal.ofReal_le_one.2 (Real.rpow_le_one hs.1.le hs.2 (by linarith))
  have h2 : ⨆ x, ‖heatSemigroup s f x‖ₑ ≤ ‖f‖ₑ :=
    iSup_le fun x => enorm_le_iff_norm_le.2 (norm_heatSemigroup_le hs.1 f x)
  simpa using mul_le_mul' h1 h2

theorem holderBesovENorm_add_le (η : ℝ) (f g : C(Torus3, ℝ)) :
    holderBesovENorm η (f + g) ≤ holderBesovENorm η f + holderBesovENorm η g := by
  refine iSup₂_le fun s hs => ?_
  have hsum : ⨆ x, ‖heatSemigroup s (f + g) x‖ₑ ≤
      (⨆ x, ‖heatSemigroup s f x‖ₑ) + ⨆ x, ‖heatSemigroup s g x‖ₑ := by
    refine iSup_le fun x => ?_
    have hadd : heatSemigroup s (f + g) x = heatSemigroup s f x + heatSemigroup s g x := by
      rw [heatSemigroup, heatSemigroup, heatSemigroup, ← integral_add
        (integrable_heatSemigroup_integrand hs.1 f x) (integrable_heatSemigroup_integrand hs.1 g x)]
      congr 1
      funext y
      rw [ContinuousMap.add_apply, mul_add]
    rw [hadd]
    exact (enorm_add_le _ _).trans
      (add_le_add (le_iSup (fun x => ‖heatSemigroup s f x‖ₑ) x)
        (le_iSup (fun x => ‖heatSemigroup s g x‖ₑ) x))
  calc ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s (f + g) x‖ₑ
      ≤ ENNReal.ofReal (s ^ (-η / 2)) *
          ((⨆ x, ‖heatSemigroup s f x‖ₑ) + ⨆ x, ‖heatSemigroup s g x‖ₑ) :=
        mul_le_mul_right hsum _
    _ = ENNReal.ofReal (s ^ (-η / 2)) * (⨆ x, ‖heatSemigroup s f x‖ₑ) +
          ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s g x‖ₑ := mul_add _ _ _
    _ ≤ holderBesovENorm η f + holderBesovENorm η g :=
        add_le_add
          (le_iSup₂ (f := fun s (_ : s ∈ Ioc (0 : ℝ) 1) =>
            ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s f x‖ₑ) s hs)
          (le_iSup₂ (f := fun s (_ : s ∈ Ioc (0 : ℝ) 1) =>
            ENNReal.ofReal (s ^ (-η / 2)) * ⨆ x, ‖heatSemigroup s g x‖ₑ) s hs)

/-- The seminorm `‖·‖_η` on `C(T³)`, for `η < 0`. -/
def holderBesovSeminorm (η : NegExponent) : AddGroupSeminorm C(Torus3, ℝ) where
  toFun f := (holderBesovENorm η f).toReal
  map_zero' := by simp [holderBesovENorm, heatSemigroup]
  add_le' f g := by
    have hf := holderBesovENorm_lt_top η.2.le f
    have hg := holderBesovENorm_lt_top η.2.le g
    rw [← ENNReal.toReal_add hf.ne hg.ne]
    exact ENNReal.toReal_mono (ENNReal.add_lt_top.2 ⟨hf, hg⟩).ne (holderBesovENorm_add_le η f g)
  neg' f := by simp [holderBesovENorm, heatSemigroup, integral_neg]

/-- `C(T³)` equipped with the seminorm `‖·‖_η`. -/
def HolderBesovPre (_η : NegExponent) : Type := C(Torus3, ℝ)

instance instAddCommGroupHolderBesovPre (η : NegExponent) : AddCommGroup (HolderBesovPre η) :=
  inferInstanceAs (AddCommGroup C(Torus3, ℝ))

instance instSeminormedAddCommGroupHolderBesovPre (η : NegExponent) :
    SeminormedAddCommGroup (HolderBesovPre η) :=
  AddGroupSeminorm.toSeminormedAddCommGroup (E := HolderBesovPre η) (holderBesovSeminorm η)

/-- The Hölder–Besov space `𝒞^η`, the completion of `C(T³)` for `‖·‖_η`. -/
abbrev HolderBesov (η : NegExponent) : Type := UniformSpace.Completion (HolderBesovPre η)

/-- `𝒞^η` carries its Borel σ-algebra. -/
instance instMeasurableSpaceHolderBesov (η : NegExponent) : MeasurableSpace (HolderBesov η) :=
  borel _

/-- The embedding `C(T³) → 𝒞^η`. -/
def toHolderBesov (η : NegExponent) (f : C(Torus3, ℝ)) : HolderBesov η :=
  UniformSpace.Completion.coe' (show HolderBesovPre η from f)

/-! ## White noise, mollifiers and the regularised noise -/

variable {Ω : Type*} [MeasurableSpace Ω]

/-- `X` is a centred Gaussian vector in `ℝⁿ` with covariance matrix `C` under `P`: it is
a.e.-measurable, its law is Gaussian, and it has mean zero and covariance `C`. -/
def IsCentredGaussianVector (P : Measure Ω) {n : ℕ} (X : Ω → Fin n → ℝ)
    (C : Fin n → Fin n → ℝ) : Prop :=
  AEMeasurable X P ∧ ProbabilityTheory.IsGaussian (P.map X) ∧ (∀ i, ∫ ω, X ω i ∂P = 0) ∧
    ∀ i j, ∫ ω, X ω i * X ω j ∂P = C i j

/-- `W` is a space-time white noise on `ℝ × T³` under `P`: each `W h` with `h` square-integrable
is a random variable, and every finite family is a centred Gaussian vector with covariance
`∫ hᵢ hⱼ`. Measurability is required explicitly: in Mathlib the law of a non-measurable map is a
point mass, which counts as Gaussian. -/
def IsWhiteNoise (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) : Prop :=
  (∀ h : SpaceTime → ℝ, MemLp h 2 → Measurable (W h)) ∧
    ∀ (n : ℕ) (h : Fin n → SpaceTime → ℝ), (∀ i, MemLp (h i) 2) →
      IsCentredGaussianVector P (fun ω i => W (h i) ω) fun i j => ∫ z, h i z * h j z

open scoped ContDiff in
/-- The class of mollifiers: smooth, compactly supported functions on `ℝ × ℝ³` with integral one. -/
structure IsMollifier (ρ : ℝ × (Fin 3 → ℝ) → ℝ) : Prop where
  contDiff : ContDiff ℝ ∞ ρ
  hasCompactSupport : HasCompactSupport ρ
  integral_eq_one : ∫ z, ρ z = 1

/-- The parabolic rescaling `ρ_ε(t, x) = ε⁻⁵ ρ(ε⁻² t, ε⁻¹ x)`. -/
def rescale (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : ℝ × (Fin 3 → ℝ)) : ℝ :=
  ε ^ (-5 : ℤ) * ρ (ε ^ (-2 : ℤ) * z.1, ε⁻¹ • z.2)

/-- The spatial periodisation `ρ_ε^♯(t, x) = ∑_{k ∈ ℤ³} ρ_ε(t, x + k)`. -/
def periodise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∑' k : Fin 3 → ℤ, rescale ρ ε (z.1, torusRep z.2 + fun i => (k i : ℝ))

/-- The test function `ρ_{ε,z}(w) = ρ_ε^♯(z - w)`. -/
def mollifierAt (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) (w : SpaceTime) : ℝ :=
  periodise ρ ε (z - w)

/-- `ξ` is a regularised noise at scale `ε`, `ξ(z) = W(ρ_{ε,z})`: smooth in space-time for every
`ω`, and for every `z` measurable and almost surely equal to `W(ρ_{ε,z})`. -/
def IsRegularisedNoise (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (ξ : Ω → SpaceTime → ℝ) : Prop :=
  (∀ ω, IsSmoothOnSpaceTime (ξ ω)) ∧
    ∀ z, Measurable (fun ω => ξ ω z) ∧ (fun ω => ξ ω z) =ᵐ[P] W (mollifierAt ρ ε z)

/-! ## The renormalisation constants -/

/-- `G_ε(z) = ∫ G(z - w) ρ_ε^♯(w) dw`. -/
def mollifiedKernel (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, massiveHeatKernel (z - w) * periodise ρ ε w

/-- `Q_ε(z) = ∫ G_ε(z + w) G_ε(w) dw`, the covariance of the stationary mollified field. -/
def covariance (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w

/-- The Wick constant `C₁^ε = ∫ G_ε²`. -/
def wickConstant (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  ∫ z, mollifiedKernel ρ ε z ^ 2

/-- The logarithmically divergent constant `C₂^ε = 2 ∫ G Q_ε²`. -/
def sunsetConstant (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) : ℝ :=
  2 * ∫ z, massiveHeatKernel z * covariance ρ ε z ^ 2

/-! ## Solutions and the limit -/

open scoped ContDiff in
/-- `u` is a classical solution of `∂_t u = Δu - u³ + c u + f` on `[0, ∞) × T³` with `u(0) = u₀`:
continuous on `[0, ∞) × T³`, smooth on `(0, ∞) × T³`, and satisfying the equation pointwise
there. Derivatives are taken on the spatially periodic lift; only `t ≥ 0` matters. -/
structure IsClassicalSolution (c : ℝ) (f : SpaceTime → ℝ) (u₀ : C(Torus3, ℝ))
    (u : ℝ → C(Torus3, ℝ)) : Prop where
  continuousOn : ContinuousOn (fun z : ℝ × Torus3 => u z.1 z.2) (Set.Ici 0 ×ˢ Set.univ)
  initial : u 0 = u₀
  contDiffOn :
    ContDiffOn ℝ ∞ (fun p : ℝ × (Fin 3 → ℝ) => u p.1 (torusProj p.2)) (Set.Ioi 0 ×ˢ Set.univ)
  equation : ∀ t, 0 < t → ∀ y : Fin 3 → ℝ,
    deriv (fun s => u s (torusProj y)) t =
      (∑ i, deriv (deriv fun r => u t (torusProj (Function.update y i r))) (y i))
        - u t (torusProj y) ^ 3 + c * u t (torusProj y) + f (t, torusProj y)

/-- `(τ, v)` is a limit of the solutions `u ε` with data `u₀` in `𝒞^η`:
* (A1) `τ` is a positive random time, each path `v ω` is continuous on `[0, τ ω)` with
  `v ω 0 = u₀`, and `ω ↦ v ω t` is measurable on `{τ > t}`;
* (A2) `τ` is the explosion time: if `τ ω < ∞` then `‖v ω t‖_η` is unbounded on `[0, τ ω)`;
* (A3) for all `T, δ > 0`, `P(τ > T and sup_{t ≤ T} ‖u_ε(t) - v(t)‖_η > δ) → 0` as `ε ↓ 0`. -/
structure IsPhi43Limit (P : Measure Ω) (η : NegExponent)
    (u₀ : C(Torus3, ℝ)) (u : ℝ → Ω → ℝ → C(Torus3, ℝ)) (τ : Ω → ℝ≥0∞)
    (v : Ω → ℝ → HolderBesov η) : Prop where
  measurable_τ : Measurable τ
  τ_pos : ∀ ω, 0 < τ ω
  continuousOn : ∀ ω, ContinuousOn (v ω) {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω}
  initial : ∀ ω, v ω 0 = toHolderBesov η u₀
  measurable : ∀ t, 0 ≤ t → ∀ s : Set (HolderBesov η), MeasurableSet s →
    MeasurableSet {ω | ENNReal.ofReal t < τ ω ∧ v ω t ∈ s}
  explosion : ∀ ω, τ ω < ⊤ →
    ¬ BddAbove ((fun t => ‖v ω t‖) '' {t | 0 ≤ t ∧ ENNReal.ofReal t < τ ω})
  converges : ∀ T, 0 < T → ∀ δ, 0 < δ →
    Tendsto (fun ε => P {ω | ENNReal.ofReal T < τ ω ∧
      ∃ t ∈ Set.Icc 0 T, δ < ‖toHolderBesov η (u ε ω t) - v ω t‖}) (𝓝[>] 0) (𝓝 0)

/-! ## The theorems -/

/-- **Theorem A** ([Hai14, Theorem 1.15], with smooth initial data and explicit constants). Let
`W` be a space-time white noise, `a ∈ ℝ`, `u₀` smooth on `T³`, `η ∈ (-2/3, -1/2)` and `ρ` a
mollifier. For `ε ∈ (0, 1]` let `ξ ε` be a regularised noise at scale `ε`, and let `u ε ω` be the
classical solution, driven by `ξ ε ω`, of the equation with counterterm `a + 3C₁^ε - 9C₂^ε`. Then
there are a random time `τ` and paths `v` with (A1)–(A3), and for every other mollifier `ρ'`, with
regularised noises `ξ'` driven by the same `W`, solutions `u'` and a pair `(τ', v')` with
(A1)–(A3) for them, one has `τ' = τ` almost surely, and almost surely `v' t = v t` for `t < τ`. -/
theorem theoremA :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
    (a : ℝ) (u₀ : C(Torus3, ℝ)) (_hu₀ : IsSmoothOnTorus u₀)
    (η : NegExponent) (_hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ)
    (ξ : ℝ → Ω → SpaceTime → ℝ) (_hξ : ∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε))
    (u : ℝ → Ω → ℝ → C(Torus3, ℝ))
    (_hu : ∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) u₀ (u ε ω)),
    ∃ (τ : Ω → ℝ≥0∞) (v : Ω → ℝ → HolderBesov η),
      IsPhi43Limit P η u₀ u τ v ∧
      ∀ (ρ' : ℝ × (Fin 3 → ℝ) → ℝ) (ξ' : ℝ → Ω → SpaceTime → ℝ)
        (u' : ℝ → Ω → ℝ → C(Torus3, ℝ)) (τ' : Ω → ℝ≥0∞) (v' : Ω → ℝ → HolderBesov η),
        IsMollifier ρ' →
        (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ' ε (ξ' ε)) →
        (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
          (a + 3 * wickConstant ρ' ε - 9 * sunsetConstant ρ' ε) (ξ' ε ω) u₀ (u' ε ω)) →
        IsPhi43Limit P η u₀ u' τ' v' →
        τ' =ᵐ[P] τ ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v' ω t = v ω t := by
  sorry

/-- The limit is unique: two pairs `(τ, v)`, `(τ', v')` with (A1)–(A3) for the same solutions `u`
have `τ = τ'` almost surely, and almost surely `v t = v' t` for `t < τ`. -/
theorem phi43Limit_unique :
    ∀ {Ω : Type*} {η : NegExponent} {u₀ : C(Torus3, ℝ)} {u : ℝ → Ω → ℝ → C(Torus3, ℝ)}
      {τ τ' : Ω → ℝ≥0∞} {v v' : Ω → ℝ → HolderBesov η} [MeasurableSpace Ω] {P : Measure Ω},
      IsPhi43Limit P η u₀ u τ v → IsPhi43Limit P η u₀ u τ' v' →
        τ =ᵐ[P] τ' ∧ ∀ᵐ ω ∂P, ∀ t, 0 ≤ t → ENNReal.ofReal t < τ ω → v ω t = v' ω t := by
  sorry

/-- A space-time white noise exists on some probability space. -/
theorem exists_whiteNoise :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ),
      IsProbabilityMeasure P ∧ IsWhiteNoise P W := by
  sorry

/-- For a white noise `W`, a mollifier `ρ` and `ε ∈ (0, 1]`, a regularised noise exists, any two
agree almost surely as functions on space-time, and each is jointly measurable. -/
theorem regularisedNoise_exists_unique :
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W)
    (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ) {ε : ℝ} (_hε : ε ∈ Ioc (0 : ℝ) 1),
    (∃ ξ, IsRegularisedNoise P W ρ ε ξ) ∧
      (∀ ξ ξ', IsRegularisedNoise P W ρ ε ξ → IsRegularisedNoise P W ρ ε ξ' →
        ∀ᵐ ω ∂P, ξ ω = ξ' ω) ∧
      ∀ ξ, IsRegularisedNoise P W ρ ε ξ → Measurable fun p : Ω × SpaceTime => ξ p.1 p.2 := by
  sorry

/-- For smooth forcing `f` and smooth initial data `u₀`, the equation
`∂_t u = Δu - u³ + c u + f`, `u(0) = u₀`, has a classical solution, unique on `[0, ∞)`. -/
theorem classicalSolution_exists_unique :
    ∀ (c : ℝ) {f : SpaceTime → ℝ} (_hf : IsSmoothOnSpaceTime f)
    {u₀ : C(Torus3, ℝ)} (_hu₀ : IsSmoothOnTorus u₀),
    (∃ u, IsClassicalSolution c f u₀ u) ∧
      ∀ u u', IsClassicalSolution c f u₀ u → IsClassicalSolution c f u₀ u' →
        ∀ t, 0 ≤ t → u t = u' t := by
  sorry

/-- Every integral in the definitions of `C₁^ε` and `C₂^ε` converges absolutely, the test
functions `ρ_{ε,z}` are square integrable, and `G_ε` and `Q_ε` are continuous and bounded. -/
theorem constants_finite :
    ∀ (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (_hρ : IsMollifier ρ) {ε : ℝ}
    (_hε : ε ∈ Ioc (0 : ℝ) 1),
    Integrable massiveHeatKernel ∧
      (∀ z, MemLp (mollifierAt ρ ε z) 2) ∧
      (∀ z, Integrable fun w => massiveHeatKernel (z - w) * periodise ρ ε w) ∧
      (Continuous (mollifiedKernel ρ ε) ∧ Integrable (mollifiedKernel ρ ε) ∧
        ∃ C, ∀ z, |mollifiedKernel ρ ε z| ≤ C) ∧
      (∀ z, Integrable fun w => mollifiedKernel ρ ε (z + w) * mollifiedKernel ρ ε w) ∧
      (Continuous (covariance ρ ε) ∧ ∃ C, ∀ z, |covariance ρ ε z| ≤ C) ∧
      Integrable (fun z => mollifiedKernel ρ ε z ^ 2) ∧
      Integrable fun z => massiveHeatKernel z * covariance ρ ε z ^ 2 := by
  sorry

end TheoremAChallenge

end

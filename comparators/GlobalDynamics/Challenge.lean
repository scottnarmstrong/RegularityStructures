/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Mathlib

/-!
# Global dynamics of the Φ⁴₃ equation on the three-torus

Global flow, coming down from infinity, Markov and Feller property, invariant measure and
stationary solution: a standalone, Mathlib-only statement of global well-posedness of the
renormalised dynamical Φ⁴₃ model on `T³`, with an invariant measure obtained by stochastic
quantisation, together with theorems showing that its hypotheses can be met and that the extended
norm is the intended one. (The white-noise space of `exists_whiteNoise` is completed and a smooth
bump of positive integral normalised to a mollifier; both steps are standard.)

For a mass `a` and an exponent `η ∈ (-2/3, -1/2)`, Theorem A (`comparators/TheoremA`) constructs
the limit `v` of the renormalised solutions `u_ε` up to an explosion time. `globalDynamics`
constructs, on every complete probability space carrying a space-time white noise, a flow
`u(t,s;x)` on the Hölder–Besov space `𝒞^η` with the clauses (B1)–(B8):
(B1) a continuous measurable flow, the identity off an event `Ω₀` of probability one;
(B2) `u(t,s;x)` depends only on the noise in the window `(s,t]`;
(B3) for smooth data it is the limit of the renormalised solutions of Theorem A, for every
  mollifier, so the limit of Theorem A never explodes;
(B4) it comes down from infinity: the supremum over all data of `√t ‖u(s+t,s;x)‖_η`, `t ∈ (0,1]`,
  has every moment, bounded by a constant chosen before the probability space;
(B5) it is time homogeneous; (B6) it is a Feller Markov process;
(B7) a probability measure `μ`, obtained by the Krylov–Bogoliubov procedure, is invariant and
  has all moments of the stronger norms `𝒩^η_{η'}`, `η' ∈ [η, -1/2)`; and
(B8) the solution started from an independent `μ`-distributed field is stationary.

* `globalDynamics`: the theorem.
* `exists_whiteNoise`, `regularisedNoise_exists_unique`, `classicalSolution_exists_unique`,
  `constants_finite`: the objects quantified in (B3) exist and the constants are not junk values
  (the same theorems as in `comparators/TheoremA`).
* `heatAt_toHolderBesov`, `continuous_heatAt`: `heatAt`, used in `𝒩^η_{η'}`, is the continuous
  extension of `f ↦ (P_s f)(x)` to `𝒞^η`.

This is the global formulation proved in this repository's `GlobalPhi43` library; its analytic
input is Mourrat–Weber (*The dynamic Φ⁴₃ model comes down from infinity*, Commun. Math. Phys. 356
(2017)) and Moinat–Weber (*Space-time localisation for the dynamic Φ⁴₃ model*, Comm. Pure Appl.
Math. 73 (2020)). The definitions shared with Theorem A are copied
verbatim from `comparators/TheoremA`.

Conventions: `T³ = ℝ³/ℤ³` is `UnitAddTorus (Fin 3)`, points of `ℝ³` are functions `Fin 3 → ℝ`,
derivatives are taken on spatially periodic lifts to `ℝ × ℝ³`, and `u t s x ω` is `u(t,s;x)(ω)`.
-/

@[expose] public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace GlobalDynamicsChallenge

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

/-! ## The noise windows and the extended norms -/

open ProbabilityTheory
open scoped NNReal BoundedContinuousFunction

/-- The noise σ-algebra `𝓕_{s,t}` of the window `(s,t]`: generated by the `P`-null sets and by the
random variables `W(h)`, `h ∈ L²(ℝ × T³)` supported in `(s,t] × T³`. -/
@[instance_reducible]
def noiseWindowSigma (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (s t : ℝ) : MeasurableSpace Ω :=
  MeasurableSpace.generateFrom {A | MeasurableSet A ∧ P A = 0} ⊔
    ⨆ (h : SpaceTime → ℝ) (_ : MemLp h 2 ∧ Function.support h ⊆ Ioc s t ×ˢ univ),
      MeasurableSpace.comap (W h) inferInstance

/-- `(P_s z)(x)` for `z ∈ 𝒞^η` and `s ∈ (0, 1]`: the continuous extension of `f ↦ (P_s f)(x)` from
`C(T³)`. Characterised by `heatAt_toHolderBesov` and `continuous_heatAt`. -/
def heatAt (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3) : HolderBesov η → ℝ :=
  UniformSpace.Completion.extension fun f : HolderBesovPre η => heatSemigroup s f x

/-- The extended norm `𝒩^η_{η'}(z) = sup_{0<s≤1} s^{-η'/2} sup_x |(P_s z)(x)| ∈ [0, ∞]` on `𝒞^η`. -/
def extNorm (η : NegExponent) (η' : ℝ) (z : HolderBesov η) : ℝ≥0∞ :=
  ⨆ s : Ioc (0 : ℝ) 1, ENNReal.ofReal ((s : ℝ) ^ (-η' / 2)) * ⨆ x, ‖heatAt η s x z‖ₑ

/-! ## Laws of the flow -/

/-- The law `P_t(x, ·)` of `u(t, 0; x)`. -/
def flowLaw {η : NegExponent} (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (t : ℝ) (x : HolderBesov η) : Measure (HolderBesov η) :=
  P.map fun ω => u t 0 x ω

/-- The transition operator `(P_t f)(x) = ∫ f dP_t(x, ·)`. -/
def flowTransition {η : NegExponent} (P : Measure Ω)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (t : ℝ) (f : HolderBesov η → ℝ)
    (x : HolderBesov η) : ℝ :=
  ∫ y, f y ∂flowLaw P u t x

/-- The averaged law `ν_T = T⁻¹ ∫₀ᵀ Law(u(t,0;0)) dt`. -/
def averagedLaw {η : NegExponent} (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (T : ℝ) : Measure (HolderBesov η) :=
  (ENNReal.ofReal T)⁻¹ • (volume.restrict (Ioc (0 : ℝ) T)).bind fun t => flowLaw P u t 0

/-- The all-data window supremum `S_s(ω) = sup_{x ∈ 𝒞^η} sup_{0<t≤1} √t ‖u(s+t,s;x)(ω)‖_η ∈ [0, ∞]`. -/
def windowSup {η : NegExponent} (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (s : ℝ) (ω : Ω) :
    ℝ≥0∞ :=
  ⨆ x, ⨆ t ∈ Ioc (0 : ℝ) 1, ENNReal.ofReal (√t * ‖u (s + t) s x ω‖)

/-! ## The clauses (B1)–(B8) of the global dynamics

Here `u t s x ω` is `u(t,s;x)(ω)`, the state at time `t` of the flow started from `x` at time `s`. -/

variable {η : NegExponent}

/-- **(B1)** Continuous measurable flow: `u` is jointly measurable on
`{(t,s) : 0 ≤ s ≤ t} × 𝒞^η × Ω`; it is the identity off `Ω₀`; for every `ω` and `s ≥ 0`,
`(t, x) ↦ u(t,s;x)(ω)` is continuous on `[s, ∞) × 𝒞^η`; `u(s,s;x) = x`; and
`u(r,s; u(s,t;x)) = u(r,t;x)` for `t ≤ s ≤ r`. -/
def IsContinuousMeasurableFlow (Ω₀ : Set Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) :
    Prop :=
  Measurable (fun q : {p : ℝ × ℝ // 0 ≤ p.2 ∧ p.2 ≤ p.1} × HolderBesov η × Ω =>
      u q.1.1.1 q.1.1.2 q.2.1 q.2.2) ∧
    (∀ ω ∉ Ω₀, ∀ t s, 0 ≤ s → s ≤ t → ∀ x, u t s x ω = x) ∧
    (∀ ω, ∀ s, 0 ≤ s → Continuous fun p : Ici s × HolderBesov η => u p.1 s p.2 ω) ∧
    (∀ s, 0 ≤ s → ∀ x ω, u s s x ω = x) ∧
    ∀ t s r, 0 ≤ t → t ≤ s → s ≤ r → ∀ x ω, u r s (u s t x ω) ω = u r t x ω

/-- **(B2)** Adaptedness: `ω ↦ u(t,s;x)(ω)` is `𝓕_{s,t}`-measurable for `0 ≤ s ≤ t`. -/
def IsWindowAdapted (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ s t, 0 ≤ s → s ≤ t → ∀ x, Measurable[noiseWindowSigma P W s t] fun ω => u t s x ω

/-- **(B3)** Consistency with Theorem A: for every mollifier `ρ`, regularised noises `ξ_ε` driven by
`W`, smooth `x` and classical solutions `u_ε` of the equation with counterterm
`a + 3C₁^ε - 9C₂^ε` and initial value `x`, `P(sup_{0≤t≤T} ‖u_ε(t) - u(t,0;x)‖_η > δ) → 0` as
`ε ↓ 0`, for all `T, δ > 0`; and the pair `(τ ≡ ∞, t ↦ u(t,0;x))` satisfies (A1)–(A3) of
Theorem A. -/
def IsConsistentWithTheoremA (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ) (η : NegExponent)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ (ρ : ℝ × (Fin 3 → ℝ) → ℝ), IsMollifier ρ →
  ∀ (ξ : ℝ → Ω → SpaceTime → ℝ), (∀ ε ∈ Ioc (0 : ℝ) 1, IsRegularisedNoise P W ρ ε (ξ ε)) →
  ∀ (x : C(Torus3, ℝ)), IsSmoothOnTorus x →
  ∀ (uε : ℝ → Ω → ℝ → C(Torus3, ℝ)),
    (∀ ε ∈ Ioc (0 : ℝ) 1, ∀ ω, IsClassicalSolution
      (a + 3 * wickConstant ρ ε - 9 * sunsetConstant ρ ε) (ξ ε ω) x (uε ε ω)) →
    (∀ T, 0 < T → ∀ δ, 0 < δ →
      Tendsto (fun ε => P {ω | ∃ t ∈ Icc 0 T,
          δ < ‖toHolderBesov η (uε ε ω t) - u t 0 (toHolderBesov η x) ω‖})
        (𝓝[>] 0) (𝓝 0)) ∧
    IsPhi43Limit P η x uε (fun _ => ⊤) fun ω t => u t 0 (toHolderBesov η x) ω

/-- **(B4)** Coming down from infinity, with the constant profile `K : [1, ∞) → [0, ∞)`: for every
`s ≥ 0` the all-data window supremum `S_s = windowSup u s` is `𝓕`-measurable, and
`𝔼[S_s^p] ≤ K p` for every `p ≥ 1` (extended expectation). -/
def ComesDownFromInfinity (P : Measure Ω) (K : ℝ → ℝ≥0)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ s, 0 ≤ s → Measurable (windowSup u s) ∧
    ∀ p : ℝ, 1 ≤ p → ∫⁻ ω, windowSup u s ω ^ p ∂P ≤ K p

/-- **(B5)** Time homogeneity: for `s ≥ 0`, `k ≥ 1`, times `tᵢ ≥ 0` and data `xᵢ`, the
`(𝒞^η)^k`-valued vectors `(u(s+tᵢ,s;xᵢ))ᵢ` and `(u(tᵢ,0;xᵢ))ᵢ` have the same law. -/
def IsTimeHomogeneous (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  ∀ s, 0 ≤ s → ∀ (k : ℕ), 1 ≤ k → ∀ (t : Fin k → ℝ), (∀ i, 0 ≤ t i) → ∀ x : Fin k → HolderBesov η,
    P.map (fun ω i => u (s + t i) s (x i) ω) = P.map fun ω i => u (t i) 0 (x i) ω

/-- **(B6)** Feller Markov process for `P_t(x, A) = P(u(t,0;x) ∈ A)`: probability kernels, jointly
measurable in `(t, x)`, `P_0(x, ·) = δ_x`, `P_{t+s} = P_t P_s`; the Markov property
`𝔼[f(u(s+t,0;x)) | 𝓕_s] = (P_t f)(u(s,0;x))` a.s. for bounded measurable `f`; and the Feller
property: `P_t f` is bounded and continuous for bounded continuous `f`, and `t ↦ (P_t f)(x)` is
continuous. -/
def IsFellerMarkovFlow (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) : Prop :=
  (∀ t, 0 ≤ t → ∀ x, IsProbabilityMeasure (flowLaw P u t x)) ∧
    (∀ A : Set (HolderBesov η), MeasurableSet A →
      Measurable fun p : Ici (0 : ℝ) × HolderBesov η => flowLaw P u p.1 p.2 A) ∧
    (∀ x, flowLaw P u 0 x = Measure.dirac x) ∧
    (∀ s t, 0 ≤ s → 0 ≤ t → ∀ x, ∀ A : Set (HolderBesov η), MeasurableSet A →
      flowLaw P u (t + s) x A = ∫⁻ y, flowLaw P u s y A ∂flowLaw P u t x) ∧
    (∀ f : HolderBesov η → ℝ, Measurable f → (∃ M, ∀ y, |f y| ≤ M) →
      ∀ s t, 0 ≤ s → 0 ≤ t → ∀ x,
        P[fun ω => f (u (s + t) 0 x ω) | noiseWindowSigma P W 0 s] =ᵐ[P]
          fun ω => flowTransition P u t f (u s 0 x ω)) ∧
    ∀ f : HolderBesov η →ᵇ ℝ,
      (∀ t, 0 ≤ t → Continuous (flowTransition P u t f) ∧
        ∃ M, ∀ x, |flowTransition P u t f x| ≤ M) ∧
      ∀ x, ContinuousOn (fun t => flowTransition P u t f x) (Ici 0)

/-- **(B7)** for a probability measure `μ` on `𝒞^η`: (i) `μ P_t = μ` for `t ≥ 0`; (ii) `μ` is the
weak limit of `ν_{T_k}` along some `T_k > 0`, `T_k → ∞`; (iii) `∫ 𝒩_{η'}^p dμ < ∞` for `p ≥ 1` and
`η' ∈ [η, -1/2)`. -/
def IsKrylovBogoliubovInvariant (P : Measure Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (μ : Measure (HolderBesov η)) : Prop :=
  (∀ t, 0 ≤ t → ∀ A : Set (HolderBesov η), MeasurableSet A →
      ∫⁻ x, flowLaw P u t x A ∂μ = μ A) ∧
    (∃ T : ℕ → ℝ, (∀ k, 0 < T k) ∧ Tendsto T atTop atTop ∧
      ∀ f : HolderBesov η →ᵇ ℝ,
        Tendsto (fun k => ∫ z, f z ∂averagedLaw P u (T k)) atTop (𝓝 (∫ z, f z ∂μ))) ∧
    ∀ p : ℝ, 1 ≤ p → ∀ η' : ℝ, (η : ℝ) ≤ η' → η' < -(1 / 2) →
      ∫⁻ z, extNorm η η' z ^ p ∂μ < ⊤

/-- **(B8)** Stationary solution, on `(Ω × 𝒞^η, 𝓕 ⊗ 𝓑(𝒞^η), P ⊗ μ)`: the process
`ũ(t)(ω, z) = u(t,0;z)(ω)` has finite-dimensional distributions invariant under time shifts and
law `μ` at every `t ≥ 0`; `(ω, z) ↦ W(h)(ω)` is a white noise, independent of the initial field
`(ω, z) ↦ z`, which has law `μ`. -/
def IsStationarySolution (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ)
    (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (μ : Measure (HolderBesov η)) : Prop :=
  (∀ (k : ℕ) (t : Fin k → ℝ), (∀ i, 0 ≤ t i) → ∀ r, 0 ≤ r →
      (P.prod μ).map (fun q i => u (t i + r) 0 q.2 q.1) =
        (P.prod μ).map fun q i => u (t i) 0 q.2 q.1) ∧
    (∀ t, 0 ≤ t → (P.prod μ).map (fun q => u t 0 q.2 q.1) = μ) ∧
    IsWhiteNoise (P.prod μ) (fun h q => W h q.1) ∧
    (P.prod μ).map Prod.snd = μ ∧
    Indep (⨆ (h : SpaceTime → ℝ) (_ : MemLp h 2),
        MeasurableSpace.comap (fun q : Ω × HolderBesov η => W h q.1) inferInstance)
      (MeasurableSpace.comap Prod.snd inferInstance) (P.prod μ)

/-- The conclusion of `globalDynamics` for the witnesses `(Ω₀, u, μ)`: `Ω₀` is an event of probability one,
and (B1)–(B8) hold, with the constant profile `K` in (B4) and the one probability measure `μ`
witnessing both (B7) and (B8). -/
def IsGlobalPhi43Flow (K : ℝ → ℝ≥0) (P : Measure Ω) (W : (SpaceTime → ℝ) → Ω → ℝ) (a : ℝ)
    (η : NegExponent) (Ω₀ : Set Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η)
    (μ : Measure (HolderBesov η)) : Prop :=
  MeasurableSet Ω₀ ∧ P Ω₀ = 1 ∧
    IsContinuousMeasurableFlow Ω₀ u ∧
    IsWindowAdapted P W u ∧
    IsConsistentWithTheoremA P W a η u ∧
    ComesDownFromInfinity P K u ∧
    IsTimeHomogeneous P u ∧
    IsFellerMarkovFlow P W u ∧
    IsProbabilityMeasure μ ∧ IsKrylovBogoliubovInvariant P u μ ∧ IsStationarySolution P W u μ

/-! ## The theorems -/

/-- **Global dynamics of the Φ⁴₃ equation**: global flow, coming down from infinity, Markov
and Feller property, invariant measure and stationary solution. Let `a ∈ ℝ` and `η ∈ (-2/3, -1/2)`.
There is a function `K : [1, ∞) → [0, ∞)`, chosen before the probability space, such that for every complete
probability space carrying a space-time white noise `W` there are an event `Ω₀` of probability
one, a flow `u(t,s;x)` on `𝒞^η` and a probability measure `μ` on `𝒞^η` with (B1)–(B8). -/
theorem globalDynamics :
    ∀ (a : ℝ) (η : NegExponent) (_hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ))),
    ∃ K : ℝ → ℝ≥0,
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] [P.IsComplete]
      (W : (SpaceTime → ℝ) → Ω → ℝ) (_hW : IsWhiteNoise P W),
    ∃ (Ω₀ : Set Ω) (u : ℝ → ℝ → HolderBesov η → Ω → HolderBesov η) (μ : Measure (HolderBesov η)),
      IsGlobalPhi43Flow K P W a η Ω₀ u μ := by
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

/-- On `C(T³)`, `heatAt η s x` is `f ↦ (P_s f)(x)`. -/
theorem heatAt_toHolderBesov (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3)
    (f : C(Torus3, ℝ)) : heatAt η s x (toHolderBesov η f) = heatSemigroup s f x := by
  sorry

/-- `heatAt η s x` is continuous on `𝒞^η`; with `heatAt_toHolderBesov` and the density of
`C(T³)` this makes it the unique continuous extension of `f ↦ (P_s f)(x)`. -/
theorem continuous_heatAt (η : NegExponent) (s : Ioc (0 : ℝ) 1) (x : Torus3) :
    Continuous (heatAt η s x) := by
  sorry

end GlobalDynamicsChallenge

end

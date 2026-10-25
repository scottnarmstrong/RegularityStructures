/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# A non-measurable white-noise candidate

In this Mathlib revision `Measure.map f μ` of a non-a.e.-measurable `f` (with `μ ≠ 0`) is a Dirac
mass, which `IsGaussian` accepts, and the Bochner integral of a non-a.e.-strongly-measurable
function is `0`. So the Gaussian and centring conjuncts of `IsCentredGaussianVector` are
junk-satisfied by non-measurable vectors, and only the second-moment conjunct has content.

We build `W h (z, b) = ±(h z / √φ z)`, the sign depending on a coordinate `b : Bool` that the
σ-algebra cannot see. `W h` is not a random variable for any `h ≠ 0` in `L²`, yet it has the
white-noise second moments (`Fake.integral_W_mul`). A white-noise predicate without measurability
would therefore accept `W`: Lemma 4.1 (W1) of the statement would have this junk witness, and the
existence part of (W2) would fail for it (`Fake.no_regularisedNoise`). `IsWhiteNoise` requires
measurability, which excludes `W` (`Fake.not_isWhiteNoise`).
-/

open MeasureTheory ProbabilityTheory RegularityStructures
open scoped ENNReal

noncomputable section

namespace Fake

/-- A positive probability density in the time variable. -/
def φ (z : SpaceTime) : ℝ := gaussianPDFReal 0 1 z.1

lemma φ_pos (z : SpaceTime) : 0 < φ z := gaussianPDFReal_pos _ _ _ one_ne_zero

lemma measurable_φ : Measurable φ := (measurable_gaussianPDFReal 0 1).comp measurable_fst

/-- A probability measure on space-time equivalent to Lebesgue measure. -/
def P₀ : Measure SpaceTime := volume.withDensity fun z => ENNReal.ofReal (φ z)

instance : IsProbabilityMeasure P₀ := by
  constructor
  rw [P₀, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    show (volume : Measure SpaceTime) = (volume : Measure ℝ).prod (volume : Measure Torus3) from rfl,
    lintegral_prod _ (measurable_φ.ennreal_ofReal.aemeasurable)]
  simp only [φ, lintegral_const]
  have hT : (volume : Measure Torus3) Set.univ = 1 := by
    rw [show (volume : Measure Torus3) = Measure.pi fun _ => (volume : Measure UnitAddCircle)
      from rfl, Measure.pi_univ]
    simp [AddCircle.measure_univ]
  simp only [hT, mul_one]
  exact lintegral_gaussianPDFReal_eq_one 0 one_ne_zero

/-- The sample space: space-time times a hidden sign. -/
def Ω : Type := SpaceTime × Bool

def mk (z : SpaceTime) (b : Bool) : Ω := (z, b)

def fst' (ω : Ω) : SpaceTime := Prod.fst (α := SpaceTime) (β := Bool) ω

def snd' (ω : Ω) : Bool := Prod.snd (α := SpaceTime) (β := Bool) ω

/-- The σ-algebra only sees the space-time coordinate. -/
instance mΩ : MeasurableSpace Ω := MeasurableSpace.comap fst' inferInstance

def emb (z : SpaceTime) : Ω := mk z true

lemma measurable_fst' : Measurable fst' := fun s hs => ⟨s, hs, rfl⟩

lemma measurable_emb : Measurable emb := by
  rintro _ ⟨s, hs, rfl⟩
  exact hs

def P : Measure Ω := P₀.map emb

instance : IsProbabilityMeasure P := by unfold P; infer_instance

def sgn (b : Bool) : ℝ := if b then 1 else -1

def U (h : SpaceTime → ℝ) (z : SpaceTime) : ℝ := h z / Real.sqrt (φ z)

/-- The fake noise. -/
def W (h : SpaceTime → ℝ) (ω : Ω) : ℝ := sgn (snd' ω) * U h (fst' ω)

/-- A measurable real function on `Ω` cannot see the hidden sign. -/
lemma measurable_eq_of_bool {g : Ω → ℝ} (hg : Measurable g) (z : SpaceTime) :
    g (mk z false) = g (mk z true) := by
  obtain ⟨s, -, hs⟩ := hg (measurableSet_singleton (g (mk z true)))
  have h1 : mk z true ∈ fst' ⁻¹' s := by
    rw [hs]; rfl
  have h2 : mk z false ∈ fst' ⁻¹' s := h1
  rw [hs] at h2
  exact h2

lemma P_preimage {A : Set SpaceTime} (hA : MeasurableSet A) : P (fst' ⁻¹' A) = P₀ A := by
  rw [P, Measure.map_apply measurable_emb (measurable_fst' hA)]
  rfl

/-- If `W h` is a.e. measurable then `U h = 0` almost everywhere. -/
lemma U_ae_zero {h : SpaceTime → ℝ} (hW : AEMeasurable (W h) P) : U h =ᵐ[P₀] 0 := by
  obtain ⟨g, hg, hWg⟩ := hW
  rw [Filter.EventuallyEq, ae_iff] at hWg
  obtain ⟨N, hsub, hN, hN0⟩ := exists_measurable_superset_of_null hWg
  obtain ⟨A, hA, rfl⟩ := hN
  have hA0 : P₀ A = 0 := by rw [← P_preimage hA]; exact hN0
  rw [Filter.EventuallyEq, ae_iff]
  refine measure_mono_null (fun z hz => ?_) hA0
  by_contra hzA
  have ht : W h (mk z true) = g (mk z true) := by
    by_contra hne
    exact hzA (hsub hne)
  have hf : W h (mk z false) = g (mk z false) := by
    by_contra hne
    exact hzA (hsub hne)
  rw [measurable_eq_of_bool hg z, ← ht] at hf
  simp only [W, sgn, fst', snd', mk, Bool.false_eq_true, ite_false, ite_true] at hf
  apply hz
  simp only [Pi.zero_apply]
  linarith

lemma W_ae_zero {h : SpaceTime → ℝ} (hU : U h =ᵐ[P₀] 0) : W h =ᵐ[P] 0 := by
  rw [Filter.EventuallyEq, ae_iff] at hU ⊢
  obtain ⟨A, hsub, hA, hA0⟩ := exists_measurable_superset_of_null hU
  refine measure_mono_null (fun ω hω => hsub ?_) ((P_preimage hA).trans hA0)
  simp only [Set.mem_ofPred_eq, W, Pi.zero_apply] at hω ⊢
  intro h0
  apply hω
  rw [h0, mul_zero]

/-- The fake noise has the white-noise second moments. -/
lemma integral_W_mul {h g : SpaceTime → ℝ} (hh : AEStronglyMeasurable h volume)
    (hg : AEStronglyMeasurable g volume) :
    ∫ ω, W h ω * W g ω ∂P = ∫ z, h z * g z := by
  have hpt : ∀ ω, W h ω * W g ω = U h (fst' ω) * U g (fst' ω) := by
    intro ω
    simp only [W]
    cases snd' ω <;> simp [sgn]
  simp_rw [hpt]
  have hmap : P.map fst' = P₀ := by
    rw [P, Measure.map_map measurable_fst' measurable_emb]
    exact Measure.map_id
  have hac : P₀ ≪ volume := withDensity_absolutelyContinuous _ _
  have hU : ∀ k : SpaceTime → ℝ, AEStronglyMeasurable k volume → AEStronglyMeasurable (U k) P₀ :=
    fun k hk => by
      have : U k = fun z => k z * (Real.sqrt (φ z))⁻¹ := by
        funext z; simp [U, div_eq_mul_inv]
      rw [this]
      exact (hk.mono_ac hac).mul measurable_φ.sqrt.inv.aestronglyMeasurable
  have hF : AEStronglyMeasurable (fun z => U h z * U g z) P₀ := (hU h hh).mul (hU g hg)
  rw [← hmap] at hF
  rw [← integral_map measurable_fst'.aemeasurable hF, hmap, P₀,
    integral_withDensity_eq_integral_toReal_smul measurable_φ.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  have hp := φ_pos z
  have hs : Real.sqrt (φ z) ^ 2 = φ z := Real.sq_sqrt hp.le
  have hs0 : Real.sqrt (φ z) ≠ 0 := (Real.sqrt_pos.2 hp).ne'
  simp only [U, smul_eq_mul, ENNReal.toReal_ofReal hp.le]
  field_simp
  rw [hs]
  ring

/-- `W h` is not a random variable for any `h` with `∫ h² ≠ 0`. -/
theorem not_aemeasurable_W {h : SpaceTime → ℝ} (hh : MemLp h 2) (hpos : ∫ z, h z * h z ≠ 0) :
    ¬ AEMeasurable (W h) P := by
  intro hm
  apply hpos
  have h0 := W_ae_zero (U_ae_zero hm)
  rw [← integral_W_mul hh.aestronglyMeasurable hh.aestronglyMeasurable]
  refine integral_eq_zero_of_ae ?_
  filter_upwards [h0] with ω hω
  simp [hω]

/-- No regularised noise exists for the fake `W` as soon as `ρ_{ε,z}` is a nonzero `L²` function.
For every mollifier this holds, since `∫ ρ_ε^♯ = 1` on `ℝ × T³`. -/
theorem no_regularisedNoise (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (ε : ℝ) (z : SpaceTime)
    (hz : MemLp (Phi43.mollifierAt ρ ε z) 2)
    (hpos : ∫ w, Phi43.mollifierAt ρ ε z w * Phi43.mollifierAt ρ ε z w ≠ 0)
    (ξ : Ω → SpaceTime → ℝ) : ¬ Phi43.IsRegularisedNoise P W ρ ε ξ := by
  rintro ⟨-, hξ⟩
  obtain ⟨hm, hae⟩ := hξ z
  exact not_aemeasurable_W hz hpos (hm.aemeasurable.congr hae)

end Fake

/-- `IsWhiteNoise` requires measurability, so the fake family is excluded: one nonzero
square-integrable `h` is enough. -/
theorem Fake.not_isWhiteNoise {h : SpaceTime → ℝ} (hh : MemLp h 2) (hpos : ∫ z, h z * h z ≠ 0) :
    ¬ IsWhiteNoise Fake.P Fake.W :=
  fun hW => Fake.not_aemeasurable_W hh hpos (hW.1 h hh).aemeasurable

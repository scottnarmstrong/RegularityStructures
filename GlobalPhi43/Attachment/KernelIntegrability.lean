module

public import GlobalPhi43.Attachment.Realisation
public import RegularityStructures.Analysis.Semigroup.PairingGrowth.Kernel
public import RegularityStructures.Analysis.Kernel.GeneratorProps
public import Phi43.Structure.RenormalisedExtensionRealisation
public import RegularityStructures.Abstract.Integration.PolyPairing.Limit
import Mathlib.Tactic.Linarith

/-! Qualitative kernel integrability for the canonical realisations. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43

/-- Uniform polynomial growth supplies precisely the qualitative kernel-integrability input. -/
theorem kernel_int_of_uniform_polynomial {Λ : ℝ → ParabolicSpace → ℝ} {B : ℝ} {n : ℕ}
    (hB : 0 ≤ B) (hΛ : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      |Λ u z| ≤ B * (1 + parabolicNorm z) ^ n)
    (x : ParabolicSpace) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) (h₀ : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y, parabolicNorm (y - x) ≤ 1 →
      ∫ z, |parabolicSemigroup.kernel v y z| * |Λ s z| ≤ W := by
  have hloc : parabolicSemigroup.IsLocalOrderGrowth Λ 0 0 {0} B (n : ℝ) := by
    intro u hu z
    simpa only [RegularisingSemigroup.IsLocalOrderGrowth, Finset.sum_singleton,
      zero_div, Real.rpow_zero, sub_zero, sub_self, mul_one, Real.rpow_natCast, parabolicSemigroup] using hΛ u hu z
  obtain ⟨W, hW⟩ := RegularisingSemigroup.LocalBall.kernel_int_of_growth
    parabolicSemigroup_isMetricScale hB (Nat.cast_nonneg n)
    (by simp : ∀ a ∈ ({0} : Finset ℝ), a ≤ (0 : ℝ)) hloc hs
    (show 0 ≤ parabolicNorm x + 1 by linarith [parabolicNorm_nonneg x]) h₀
  refine ⟨W, fun v hv y hy => hW v hv y ?_⟩
  change parabolicNorm (y - 0) ≤ parabolicNorm x + 1
  rw [sub_zero]
  have h := parabolicNorm_add_le (y - x) x
  rw [sub_add_cancel] at h
  linarith

/-- Polynomially bounded function realisations have the required uniform Q-kernel integrability. -/
theorem kernel_int_of_polyBounded {g : ParabolicSpace → ℝ} (hg : PolyBounded g)
    (x : ParabolicSpace) {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) (h₀ : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y, parabolicNorm (y - x) ≤ 1 →
      ∫ z, |parabolicSemigroup.kernel v y z| * |parabolicSemigroup.apply s g z| ≤ W := by
  obtain ⟨hgm, B, n, hB⟩ := hg
  obtain ⟨C, hC⟩ := exists_kernelPowMoment_le n
  have hB0 := nonneg_of_bound hB
  have hbound : ∀ u ∈ Set.Ioc (0 : ℝ) 1, ∀ z,
      |parabolicSemigroup.apply u g z| ≤ (B * max C 0) * (1 + parabolicNorm z) ^ n := by
    intro u hu z
    have h := abs_apply_le_of_kernelPowMoment_le hgm hB
      (fun t ht ht1 => (hC t ht ht1).trans (le_max_left C 0)) hu.1 hu.2 z
    simpa only [mul_assoc] using h
  exact kernel_int_of_uniform_polynomial (mul_nonneg hB0 (le_max_right C 0)) hbound x hs h₀

/-- Kernel integrability in model form, for every symbol of a moderate model. -/
theorem model_kernel_int {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ}
    {C : RenormalisationConstants} {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}
    (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z)
    {τ : Symbol} (hτ : IsPinnedSymbol τ) (x : ParabolicSpace)
    {s : ℝ} (hs : s ∈ Set.Ioc (0 : ℝ) 1) (h₀ : ℝ) :
    ∃ W : ℝ, ∀ v ∈ Set.Ioc (0 : ℝ) h₀, ∀ y, parabolicNorm (y - x) ≤ 1 →
      ∫ z, |parabolicSemigroup.kernel v y z| * |Z.regPi x (Pi.single τ 1) s z| ≤ W := by
  obtain ⟨noise, hn, hRC, _⟩ := regPi_fMinus hZ
  obtain ⟨Cg, q, hgr⟩ := hg
  have hz : noise.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    rw [hz]; exact hgr
  have hcan := canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg' C
  have hcoord : phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
    apply phi43CoordinateEquiv.injective
    simp only [LinearEquiv.apply_symm_apply, phi43CoordinateEquiv_basis]
  have he (z : ParabolicSpace) : Z.regPi x (Pi.single τ 1) s z =
      parabolicSemigroup.apply s
        ((hairerCanonicalData (κ := κ) N noise).renormalisedExtensionPi C x (basis τ)) z := by
    rw [regPi_eq_of_isRenormalisedCanonicalModel hRC hcan hτ x hs.1 z,
      canonicalRenormalisedModel_regPi N κ noise Cg q hg' C x _ hs.1 z, hcoord]
  simp_rw [he]
  exact kernel_int_of_polyBounded
    (renormalisedExtensionPi_growth N noise
      (canonicalNoise_polyBounded_of_derivatives noise Cg q hg') C x (basis τ)) x hs h₀

end GlobalPhi43.Attachment

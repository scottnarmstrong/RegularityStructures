module

public import GlobalPhi43.Attachment.RealisationRecenter
public import GlobalPhi43.Attachment.ScaledTestSupport

/-! The finite partition/recentering identity for the ordinary function integral. -/

public section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43 Set

open scoped ContDiff in
/-- The exact finite decomposition used before the large-scale coefficient estimates. The
function recentering identity is proved from the model, rather than included as an assumption. -/
theorem integral_partition_recenter {ι : Type*} [Fintype ι] {κ : Kappa}
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    {g : ParabolicSpace → Symbol → ParabolicSpace → ℝ}
    (hgc : ∀ x τ, Continuous (g x τ) ∧ PolyBounded (g x τ))
    (hQ : ∀ x τ, τ ∈ fMinus → ∀ t, 0 < t → ∀ y,
      Z.regPi x (Pi.single τ 1) t y = parabolicSemigroup.apply t (g x τ) y)
    {τ : Symbol} (hτ : τ ∈ fMinus) (x : ParabolicSpace) (centers : ι → ParabolicSpace)
    {φ : ParabolicSpace → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hs4 : ∀ z, 4 < parabolicNorm z → φ z = 0)
    {K : Set ParabolicSpace} (hsK : ∀ z, z ∉ K → φ z = 0)
    (χ : ι → ParabolicSpace → ℝ) (hχ : ∀ i, ContDiff ℝ ∞ (χ i))
    (hsum : ∀ z ∈ K, ∑ i, χ i z = 1) {T : ℝ} (hT : 0 < T) :
    ∫ y, g x τ y * rescaledTestFunction φ T x y =
      ∑ i, ∑ σ ∈ fMinus, Z.gammaMap (centers i) x (Pi.single τ 1) σ *
        ∫ y, g (centers i) σ y * rescaledTestFunction (φ * χ i) T x y := by
  classical
  have hsplit (z : ParabolicSpace) : φ z = ∑ i, (φ * χ i) z := by
    change φ z = ∑ i, φ z * χ i z
    rw [← Finset.mul_sum]
    by_cases hz : z ∈ K
    · rw [hsum z hz, mul_one]
    · rw [hsK z hz, zero_mul]
  have htest (y : ParabolicSpace) : rescaledTestFunction φ T x y =
      ∑ i, rescaledTestFunction (φ * χ i) T x y := by
    unfold rescaledTestFunction
    rw [hsplit, Finset.mul_sum]
  have hpoint (y : ParabolicSpace) : g x τ y * rescaledTestFunction φ T x y =
      ∑ i, ∑ σ ∈ fMinus, Z.gammaMap (centers i) x (Pi.single τ 1) σ *
        (g (centers i) σ y * rescaledTestFunction (φ * χ i) T x y) := by
    rw [htest, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [negative_realisations_recenter Z hgc hQ hτ x (centers i) y, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro σ _
    exact mul_assoc _ _ _
  have hint (i : ι) (σ : Symbol) : Integrable (fun y =>
      Z.gammaMap (centers i) x (Pi.single τ 1) σ *
        (g (centers i) σ y * rescaledTestFunction (φ * χ i) T x y)) := by
    have hp := contDiff_rescaledTestFunction (hφ.mul (hχ i)) T x
    have hc : HasCompactSupport (rescaledTestFunction (φ * χ i) T x) :=
      hasCompactSupport_of_eq_zero (mul_pos (by norm_num : (0 : ℝ) < 4) hT) x (by
        intro y hy
        apply rescaled_eq_zero_outside (T := T) ?_ hT hy
        intro z hz
        change φ z * χ i z = 0
        rw [hs4 z hz, zero_mul])
    exact (((hgc (centers i) σ).1.mul hp.continuous).integrable_of_hasCompactSupport hc.mul_left).const_mul _
  simp_rw [hpoint]
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun σ _ => hint i σ))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun σ _ => hint i σ)]
  apply Finset.sum_congr rfl
  intro σ _
  exact integral_const_mul _ _

end GlobalPhi43.Attachment

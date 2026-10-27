module

public import GlobalPhi43.Attachment.NegativeRealisations
public import GlobalPhi43.Attachment.LocalOrder
import Mathlib.Tactic.Linarith

/-! Pointwise recentering of negative function realisations from the actual model axiom. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43 Filter Set
open scoped Topology

/-- The realisation identity used in large-scale recentering, obtained from pi_gamma and
uniqueness of the continuous polynomially bounded Q-realisation. -/
theorem negative_realisations_recenter {κ : Kappa}
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    {g : ParabolicSpace → Symbol → ParabolicSpace → ℝ}
    (hgc : ∀ x τ, Continuous (g x τ) ∧ PolyBounded (g x τ))
    (hQ : ∀ x τ, τ ∈ fMinus → ∀ t, 0 < t → ∀ y,
      Z.regPi x (Pi.single τ 1) t y = parabolicSemigroup.apply t (g x τ) y)
    {τ : Symbol} (hτ : τ ∈ fMinus) (x w y : ParabolicSpace) :
    g x τ y = ∑ σ ∈ fMinus, Z.gammaMap w x (Pi.single τ 1) σ * g w σ y := by
  classical
  have hneg : homogeneity κ τ < 0 := (homogeneity_neg_iff_isFMinus κ τ).mpr
    ((mem_fMinus_iff_isFMinus τ).mp hτ)
  have hzero (σ : Symbol) (hσ : σ ∉ fMinus) : Z.gammaMap w x (Pi.single τ 1) σ = 0 := by
    have hnonneg : 0 ≤ homogeneity κ σ := le_of_not_gt (fun h =>
      hσ ((mem_fMinus_iff_isFMinus σ).mpr ((homogeneity_neg_iff_isFMinus κ σ).mp h)))
    have hne : σ ≠ τ := by intro he; subst σ; exact hσ hτ
    exact Z.gammaMap_single_apply_of_le x w hne (hneg.le.trans hnonneg)
  have he (t : ℝ) (ht : 0 < t) :
      parabolicSemigroup.apply t (g x τ) y =
        ∑ σ ∈ fMinus, Z.gammaMap w x (Pi.single τ 1) σ * parabolicSemigroup.apply t (g w σ) y := by
    rw [← hQ x τ hτ t ht y, ← Z.regPi_gammaMap w x, Z.regPi_eq_sum]
    calc _ = ∑ σ ∈ fMinus, Z.gammaMap w x (Pi.single τ 1) σ * Z.regPi w (Pi.single σ 1) t y := by
          symm
          apply Finset.sum_subset (Finset.subset_univ fMinus)
          intro σ _ hσ
          rw [hzero σ hσ, zero_mul]
      _ = _ := Finset.sum_congr rfl (fun σ hσ => by rw [hQ w σ hσ t ht y])
  obtain ⟨_, B, n, hB⟩ := (hgc x τ).2
  have hleft := tendsto_apply_parabolicSemigroup_nhdsGT (hgc x τ).1 hB y
  have hright : Tendsto
      (fun t => ∑ σ ∈ fMinus, Z.gammaMap w x (Pi.single τ 1) σ * parabolicSemigroup.apply t (g w σ) y)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ σ ∈ fMinus, Z.gammaMap w x (Pi.single τ 1) σ * g w σ y)) := by
    apply tendsto_finsetSum
    intro σ _
    obtain ⟨_, Bσ, nσ, hBσ⟩ := (hgc w σ).2
    exact (tendsto_apply_parabolicSemigroup_nhdsGT (hgc w σ).1 hBσ y).const_mul _
  have hevent : (fun t => parabolicSemigroup.apply t (g x τ) y) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => ∑ σ ∈ fMinus, Z.gammaMap w x (Pi.single τ 1) σ * parabolicSemigroup.apply t (g w σ) y) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact he t ht
  exact tendsto_nhds_unique hleft (hright.congr' hevent.symm)

end GlobalPhi43.Attachment

module

public import GlobalPhi43.Attachment.ModelTestBoundReal
public import GlobalPhi43.Attachment.RescaleFormula
public import Phi43.Potential.TestFunction

/-! Unit-scale model test estimates for the actual compact remainder and every derivative. -/

@[expose] public noncomputable section

namespace GlobalPhi43.Attachment
open MeasureTheory RegularityStructures RegularityStructures.Phi43
open RegularityStructures.Potential RegularityStructures.Inhomogeneity GlobalPhi43.Local
open scoped ContDiff

/-- The reflected derivative of `L R` is supported in the source max-metric unit ball. -/
theorem potQRefl_tsupport (N : ℕ) (l : List (Fin 4)) :
    tsupport (potQRefl N l) ⊆ {z | pdist 0 z ≤ 1} := by
  apply closure_minimal
  · intro z hz
    by_contra hn
    have hnorm : 1 < parabolicNorm (-z) := by
      have hp := pdist_le_parabolicNorm 0 z
      simp only [zero_sub] at hp
      exact (lt_of_not_ge hn).trans_le hp
    exact hz (ddA_potQ_eq_zero_of_one_lt N l hnorm)
  · apply isClosed_le _ continuous_const
    unfold pdist
    fun_prop

/-- Unit-scale test identity for the real derivative convolution, with its sign kept explicit. -/
theorem integral_potQRefl (N : ℕ) (l : List (Fin 4)) (f : ParabolicSpace → ℝ)
    (x : ParabolicSpace) :
    (∫ y, f y * rescaledTestFunction (potQRefl N l) 1 x y) =
      potConv f (ddA l (potQ N)) x := by
  simp only [rescaledTestFunction_formula, one_zpow, one_pow, div_one, inv_one,
    one_smul, one_mul, potQRefl, potConv]
  congr 1
  funext y
  rw [Prod.mk.eta, neg_sub]

/-- The model test bound controls derivatives of the remainder convolution
under the continuous polynomial-growth realisation hypotheses. -/
theorem remainder_derivative_bound (N : ℕ) (κ : Kappa) (l : List (Fin 4)) :
    ∃ c : ℝ, 0 < c ∧
    ∀ (f₀ : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup),
      Statements.IsModeratePhi43ModelOf N κ f₀ C Z → Statements.HasPhi43NoiseGrowth f₀ →
    ∀ S : Set ParabolicSpace, IsCompact S → ∀ x ∈ S,
    ∀ τ : Symbol, homogeneity κ τ < 0 →
    ∀ f : ParabolicSpace → ℝ, Continuous f →
      (∃ (Cg : ℝ) (q : ℕ), ∀ z, |f z| ≤ Cg * (1 + parabolicNorm z) ^ q) →
      (∀ u, 0 < u → ∀ y, Z.regPi x (Pi.single τ 1) u y = parabolicSemigroup.apply u f y) →
      |ddA l (potConv f (potQ N)) x| ≤
        c * (1 + (Z.normOn (gamma κ) {y | ∃ z ∈ S, pdist z y ≤ 3}).toReal) ^ 3 := by
  obtain ⟨c, hc, h⟩ := modelTestBound_real N κ
  let A : ℝ := (⨆ k ∈ Finset.range 5, ⨆ z,
    ‖iteratedFDeriv ℝ k (potQRefl N l) z‖ₑ : ENNReal).toReal
  refine ⟨c * (1 + A), mul_pos hc (by dsimp [A]; positivity), ?_⟩
  intro f₀ C Z hZ hg S hS x hx τ hτ f hf hfg hreal
  have hb := h f₀ C Z hZ hg S hS x hx 1 ⟨one_pos, le_rfl⟩
    (potQRefl N l) (contDiff_potQRefl N l) (hasCompactSupport_potQRefl N l)
    (potQRefl_tsupport N l) τ hτ f hf hfg hreal
  rw [integral_potQRefl, Real.one_rpow, mul_one] at hb
  rw [ddA_potConv hf (contDiff_potQ N) (hasCompactSupport_ddA_potQ N)]
  refine hb.trans ?_
  change c * A * _ ≤ c * (1 + A) * _
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by linarith : A ≤ 1 + A) hc.le) (by positivity)

end GlobalPhi43.Attachment

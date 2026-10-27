module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssemblyTranslate

/-! Translation of the full model norm.
The argument uses only the model translation and translation invariance of scale distance.
It applies to every set and every space-time translation. -/

public section

namespace RegularityStructures.Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}
  (M : RegularityStructures.Model 𝒯 parabolicSemigroup) (a : ParabolicSpace)

/-- The `Γ` analogue of `Model.piBoundOn_translate_iff` (missing from the base). -/
theorem gammaBoundOn_translate_iff {γ C : ℝ} {S : Set ParabolicSpace} :
    (M.translate a).GammaBoundOn γ C S ↔ M.GammaBoundOn γ C ((· + a) '' S) := by
  constructor
  · intro h i j hi hji x hx y hy
    obtain ⟨x', hx', rfl⟩ := hx
    obtain ⟨y', hy', rfl⟩ := hy
    have := h i j hi hji x' hx' y' hy'
    rw [gammaMap_translate] at this
    simpa only [parabolicSemigroup_scaleDist_translate] using this
  · intro h i j hi hji x hx y hy
    have := h i j hi hji (x + a) ⟨x, hx, rfl⟩ (y + a) ⟨y, hy, rfl⟩
    rw [gammaMap_translate]
    simpa only [parabolicSemigroup_scaleDist_translate] using this

theorem gammaNormOn_translate (γ : ℝ) (S : Set ParabolicSpace) :
    (M.translate a).gammaNormOn γ S = M.gammaNormOn γ ((· + a) '' S) := by
  simp only [gammaNormOn, gammaBoundOn_translate_iff]

/-- `‖Z^a‖_{γ;S} = ‖Z‖_{γ;S+a}`, specialized to time translation when `a = (k, 0)`. -/
theorem normOn_translate (γ : ℝ) (S : Set ParabolicSpace) :
    (M.translate a).normOn γ S = M.normOn γ ((· + a) '' S) := by
  simp only [normOn, piNormOn_translate,
    gammaNormOn_translate]

variable (M₂ : RegularityStructures.Model 𝒯 parabolicSemigroup)

/-- Translation covariance of the two-model structure-group bound. -/
theorem gammaDiffBoundOn_translate_iff {γ C : ℝ} {S : Set ParabolicSpace} :
    (M.translate a).GammaDiffBoundOn (M₂.translate a) γ C S ↔
      M.GammaDiffBoundOn M₂ γ C ((· + a) '' S) := by
  constructor
  · intro h i j hi hj x hx y hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    simpa only [gammaMap_translate, parabolicSemigroup_scaleDist_translate] using
      h i j hi hj x hx y hy
  · intro h i j hi hj x hx y hy
    simpa only [gammaMap_translate, parabolicSemigroup_scaleDist_translate] using
      h i j hi hj (x + a) ⟨x, hx, rfl⟩ (y + a) ⟨y, hy, rfl⟩

/-- The difference-norm covariance used by `l.flow.covariance`. -/
theorem gammaDiffNormOn_translate (γ : ℝ) (S : Set ParabolicSpace) :
    (M.translate a).gammaDiffNormOn (M₂.translate a) γ S =
      M.gammaDiffNormOn M₂ γ ((· + a) '' S) := by
  simp only [gammaDiffNormOn, gammaDiffBoundOn_translate_iff]

/-- Full two-model distance commutes with translation. -/
theorem diffNormOn_translate (γ : ℝ) (S : Set ParabolicSpace) :
    (M.translate a).diffNormOn (M₂.translate a) γ S =
      M.diffNormOn M₂ γ ((· + a) '' S) := by
  simp only [diffNormOn, piDiffNormOn_translate, gammaDiffNormOn_translate]

end RegularityStructures.Model

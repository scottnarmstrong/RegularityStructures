module

public import GlobalPhi43.Attachment.TranslateNorm
public import Phi43.BPHZ.BphzCauchyTransfer
public import Phi43Statements.Defs.Phi43Size
public import Phi43Statements.Defs.Phi43Dist
import Mathlib.Tactic.Linarith

/-! Deterministic translated-window size and distance bounds of `l.flow.covariance`. -/

public section

namespace GlobalPhi43.Attachment

open RegularityStructures RegularityStructures.Phi43 Set

private theorem normOn_mono_set {ι : Type*} [Fintype ι] [DecidableEq ι]
    {𝒯 : RegularityStructure ι} (Z : Model 𝒯 parabolicSemigroup) (γ : ℝ)
    {A B : Set ParabolicSpace} (h : A ⊆ B) : Z.normOn γ A ≤ Z.normOn γ B := by
  unfold Model.normOn Model.piNormOn Model.gammaNormOn
  apply add_le_add
  · exact le_iInf₂ fun C hC => iInf₂_le C fun i hi t ht x hx => hC i hi t ht x (h hx)
  · exact le_iInf₂ fun C hC => iInf₂_le C fun i j hi hj x hx y hy =>
      hC i j hi hj x (h hx) y (h hy)

/-- The translated restart window is contained in the common larger window. -/
theorem translated_phi43Box_subset {s S T : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S) :
    (· + ((s, 0) : ParabolicSpace)) '' Statements.phi43Box (T + 1) ⊆
      Statements.phi43Box (T + S + 1) := by
  rintro z ⟨w, hw, rfl⟩
  rcases hw with ⟨ht, hx⟩
  constructor
  · change -1 ≤ w.1 + s ∧ w.1 + s ≤ T + S + 1 + 1
    constructor <;> linarith [ht.1, ht.2]
  · simpa only [Prod.snd_add, Prod.snd, add_zero] using hx

/-- Uniform covariance bound for the potential on a bounded strip of starts. -/
theorem phi43NoiseSize_translate_le (η T : ℝ) {s S : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S)
    (ψ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseSize η T (fun t => ψ (s + t)) ≤
      Statements.phi43NoiseSize η (T + S) ψ := by
  apply iSup₂_le
  intro t ht
  apply le_iSup₂_of_le (s + t)
  · exact le_rfl
  · constructor <;> linarith [ht.1, ht.2]

/-- Uniform covariance bound for the potential difference. -/
theorem phi43NoiseDist_translate_le (η T : ℝ) {s S : ℝ} (hs : 0 ≤ s) (hsS : s ≤ S)
    (ψ ψ' : ℝ → C(Torus3, ℝ)) :
    Statements.phi43NoiseDist η T (fun t => ψ (s + t)) (fun t => ψ' (s + t)) ≤
      Statements.phi43NoiseDist η (T + S) ψ ψ' := by
  apply iSup₂_le
  intro t ht
  apply le_iSup₂_of_le (s + t)
  · exact le_rfl
  · constructor <;> linarith [ht.1, ht.2]

/-- The size inequality in the part-3 covariance display. -/
theorem phi43Size_translate_le (κ : Kappa) (η T : ℝ) {s S : ℝ}
    (hs : 0 ≤ s) (hsS : s ≤ S)
    (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ : ℝ → C(Torus3, ℝ)) :
    Statements.phi43Size κ η T (Z.translate (s, 0)) (fun t => ψ (s + t)) ≤
      Statements.phi43Size κ η (T + S) Z ψ := by
  unfold Statements.phi43Size
  rw [Model.normOn_translate]
  exact add_le_add (normOn_mono_set Z _ (translated_phi43Box_subset hs hsS))
    (phi43NoiseSize_translate_le η T hs hsS ψ)

/-- The distance inequality in the part-3 covariance display. -/
theorem phi43Dist_translate_le (κ : Kappa) (η T : ℝ) {s S : ℝ}
    (hs : 0 ≤ s) (hsS : s ≤ S)
    (Z Z' : Model (phi43RegularityStructure κ) parabolicSemigroup)
    (ψ ψ' : ℝ → C(Torus3, ℝ)) :
    Statements.phi43Dist κ η T (Z.translate (s, 0)) (Z'.translate (s, 0))
        (fun t => ψ (s + t)) (fun t => ψ' (s + t)) ≤
      Statements.phi43Dist κ η (T + S) Z Z' ψ ψ' := by
  unfold Statements.phi43Dist
  rw [Model.diffNormOn_translate]
  exact add_le_add (Model.diffNormOn_mono_set (translated_phi43Box_subset hs hsS))
    (phi43NoiseDist_translate_le η T hs hsS ψ ψ')

end GlobalPhi43.Attachment

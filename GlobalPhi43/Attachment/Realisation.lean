module

public import Phi43Statements.Defs.IsModeratePhi43ModelOf
public import Phi43Statements.Defs.HasPhi43NoiseGrowth
public import Phi43.BPHZ.CanonicalBridgeRealises
public import Phi43.BPHZ.PositiveTreeFormulasBridge
public import Phi43.BPHZ.CanonicalBridgeHairer
public import Phi43.BPHZ.PsiGaussianVectorContinuous
public import Phi43.Pinned.PiPinned
public import Phi43.Structure.RenormalisedExtensionModel
public import Phi43.Structure.CanonicalModelExistence
public import Phi43.BPHZ.PositiveMomentGammaSq
public import Phi43.Structure.RenormalisedExtensionTensorIntegration
public import Phi43.BPHZ.GModelsConstantShift
public import Phi43.BPHZ.ShiftedMomentDefs
public import Phi43.Stochastic.ConstantsComparisonLimits

@[expose] public section

namespace GlobalPhi43.Attachment

open MeasureTheory
open RegularityStructures RegularityStructures.Phi43

/-! ### The renormalised trees, on `ℝ × T³` -/

/-- `J = K ∗ ζ`, with the periodised truncated kernel (`hairerPsiField` on a one-point sample
space). -/
noncomputable def treeJ (N : ℕ) (f : SpaceTime → ℝ) : SpaceTime → ℝ :=
  hairerPsiField N (fun _ : Unit => f) ()

/-- `V = J² - C₁`. -/
noncomputable def treeV (N : ℕ) (f : SpaceTime → ℝ) (c₁ : ℝ) (z : SpaceTime) : ℝ :=
  treeJ N f z ^ 2 - c₁

/-- `W = J³ - 3 C₁ J`. -/
noncomputable def treeW (N : ℕ) (f : SpaceTime → ℝ) (c₁ : ℝ) (z : SpaceTime) : ℝ :=
  treeJ N f z ^ 3 - 3 * c₁ * treeJ N f z

/-- `Y = K ∗ V`. -/
noncomputable def treeY (N : ℕ) (f : SpaceTime → ℝ) (c₁ : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, hairerKernelTorus N (z - w) * treeV N f c₁ w

/-- `Z = K ∗ W`. -/
noncomputable def treeZ (N : ℕ) (f : SpaceTime → ℝ) (c₁ : ℝ) (z : SpaceTime) : ℝ :=
  ∫ w, hairerKernelTorus N (z - w) * treeW N f c₁ w

variable {N : ℕ} {κ : Kappa} {f : SpaceTime → ℝ} {C : RenormalisationConstants}
  {Z : Model (phi43RegularityStructure κ) parabolicSemigroup}

theorem continuous_treeJ (hf : IsSmoothOnSpaceTime f) : Continuous (treeJ N f) :=
  continuous_hairerKernelTorus_convolution N (IsSmoothOnSpaceTime.continuous hf)

theorem continuous_treeV (hf : IsSmoothOnSpaceTime f) (c₁ : ℝ) : Continuous (treeV N f c₁) := by
  have := continuous_treeJ (N := N) hf
  unfold treeV; fun_prop

theorem continuous_treeW (hf : IsSmoothOnSpaceTime f) (c₁ : ℝ) : Continuous (treeW N f c₁) := by
  have := continuous_treeJ (N := N) hf
  unfold treeW; fun_prop

/-- The kernel increment paired with `V` is the increment of `Y`. -/
theorem pairing_treeV (hf : IsSmoothOnSpaceTime f) (c₁ : ℝ) (x y : SpaceTime) :
    hairerKernelIncrementPairing N x y (treeV N f c₁) = treeY N f c₁ y - treeY N f c₁ x :=
  hairerKernelIncrementPairing_eq N x y (continuous_treeV hf c₁)

/-- The kernel increment paired with `W` is the increment of `Z`. -/
theorem pairing_treeW (hf : IsSmoothOnSpaceTime f) (c₁ : ℝ) (x y : SpaceTime) :
    hairerKernelIncrementPairing N x y (treeW N f c₁) = treeZ N f c₁ y - treeZ N f c₁ x :=
  hairerKernelIncrementPairing_eq N x y (continuous_treeW hf c₁)

/-- Constant independence of increments: `C₁` does not change the increment of `Y`
(`∫ K̃ = 0`, `integral_hairerKernelTorus_sub_mul_one_sub`). -/
theorem pairing_treeJ_sq (hf : IsSmoothOnSpaceTime f) (c₁ : ℝ) (x y : SpaceTime) :
    hairerKernelIncrementPairing N x y (fun w => treeJ N f w * treeJ N f w) =
      treeY N f c₁ y - treeY N f c₁ x := by
  have hJ := continuous_treeJ (N := N) hf
  have hJJ : Continuous (fun w => treeJ N f w * treeJ N f w) := by fun_prop
  have h1 : Continuous (fun _ : SpaceTime => (1 : ℝ)) := continuous_const
  have e : treeV N f c₁ = fun w => treeJ N f w * treeJ N f w - c₁ * (fun _ => (1 : ℝ)) w := by
    funext w; simp only [treeV]; ring
  rw [← pairing_treeV hf c₁, e, hairerKernelIncrementPairing_sub_const_mul N x y hJJ h1,
    hairerKernelIncrementPairing_eq N x y h1, integral_hairerKernelTorus_sub_mul_one_sub,
    mul_zero, sub_zero]

/-! ### The predicate, unpacked -/

/-- The noise of `IsModeratePhi43ModelOf` is the periodic lift of `f`, in the form the bridge
theorems take (`ξ = fun _ : Unit => f`). -/
theorem noise_zeta_eq {noise : CanonicalNoise}
    (hn : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2)) :
    ∀ z, noise.zeta z = (fun _ : Unit => f) () (spaceTimeProj z) := hn

/-- Realisation on `F₋` for the moderate predicate (its second conjunct). -/
theorem regPi_fMinus (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) :
    ∃ noise : CanonicalNoise, (∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2)) ∧
      Statements.IsRenormalisedCanonicalModel N κ noise C Z ∧
      ∀ τ ∈ fMinus, ∀ (x : ParabolicSpace) (t : ℝ), 0 < t → ∀ z : ParabolicSpace,
        Z.regPi x (Pi.single τ 1) t z =
          parabolicSemigroup.apply t
            ((hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis τ)) z := by
  obtain ⟨noise, hn, hM⟩ := hZ
  exact ⟨noise, hn, ⟨hM.1, hM.2.1, hM.2.2.1⟩, hM.2.1⟩

private theorem coord_symm_single (τ : Symbol) :
    phi43CoordinateEquiv.symm (Pi.single τ 1) = basis τ := by
  apply phi43CoordinateEquiv.injective
  simp [phi43CoordinateEquiv_basis]

/-- Integrated symbols `I(Ψ²)`, `I(Ψ³)`: any model of the predicate agrees with the base's
canonical model (`regPi_eq_of_isRenormalisedCanonicalModel`), whose realisation
is `renormalisedPi` (`canonicalRenormalisedModel_regPi`, `renormalisedExtensionPi_tensor_*`). -/
theorem regPi_integrated (hg : Statements.HasPhi43NoiseGrowth f) {noise : CanonicalNoise}
    (hn : ∀ z : ParabolicSpace, noise.zeta z = f (z.1, torusProj z.2))
    (hZ : Statements.IsRenormalisedCanonicalModel N κ noise C Z)
    {τ : Symbol} (hτ : τ = .iPsiSq ∨ τ = .iPsiCube) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t)
    (z : ParabolicSpace) :
    Z.regPi x (Pi.single τ 1) t z =
      parabolicSemigroup.apply t
        ((hairerCanonicalData (κ := κ) N noise).renormalisedPi C x (basis τ)) z := by
  obtain ⟨Cg, q, hgr⟩ := hg
  have hz : noise.zeta = fun w : ParabolicSpace => f (w.1, torusProj w.2) := funext hn
  have hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
      ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q := by
    rw [hz]; exact hgr
  have hcan := canonicalRenormalisedModel_isRenormalisedCanonicalModel N κ noise Cg q hg' C
  have hpin : IsPinnedSymbol τ := by
    rcases hτ with rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  rw [regPi_eq_of_isRenormalisedCanonicalModel hZ hcan hpin x ht z,
    canonicalRenormalisedModel_regPi N κ noise Cg q hg' C x _ ht z, coord_symm_single]
  rcases hτ with rfl | rfl
  · rw [renormalisedExtensionPi_tensor_iPsiSq]
  · rw [renormalisedExtensionPi_tensor_iPsiCube]

/-! ### Ten realisation identities, for arbitrary constants -/

/-- **Realisation identities** for arbitrary constants `C = (C₁, C₂)`. Each identity is
`Q_t Π_x e_τ = Q_t f_{τ,x}` for `t > 0`, which is how part2 defines the realisation `f_{τ,x}`. -/
theorem realise (hf : IsSmoothOnSpaceTime f) (hg : Statements.HasPhi43NoiseGrowth f)
    (hZ : Statements.IsModeratePhi43ModelOf N κ f C Z) (x : ParabolicSpace) {t : ℝ} (ht : 0 < t)
    (z : ParabolicSpace) :
    let p := spaceTimeProj
    let Q := fun g : ParabolicSpace → ℝ => parabolicSemigroup.apply t g z
    let J := treeJ N f
    let V := treeV N f (C₁ C)
    let W := treeW N f (C₁ C)
    let Y := treeY N f (C₁ C)
    let Zt := treeZ N f (C₁ C)
    Z.regPi x (Pi.single .noise 1) t z = Q (fun y => f (p y)) ∧
    Z.regPi x (Pi.single .psi 1) t z = Q (fun y => J (p y)) ∧
    Z.regPi x (Pi.single .psiSq 1) t z = Q (fun y => V (p y)) ∧
    Z.regPi x (Pi.single .psiCube 1) t z = Q (fun y => W (p y)) ∧
    Z.regPi x (Pi.single .iPsiSq 1) t z = Q (fun y => Y (p y) - Y (p x)) ∧
    Z.regPi x (Pi.single .iPsiCube 1) t z = Q (fun y => Zt (p y) - Zt (p x)) ∧
    (∀ i : Fin 3, Z.regPi x (Pi.single (.psiSqX i) 1) t z = Q (fun y => (y.2 i - x.2 i) * V (p y))) ∧
    Z.regPi x (Pi.single .iPsiSqPsiSq 1) t z = Q (fun y => (Y (p y) - Y (p x)) * V (p y) - C₂ C) ∧
    Z.regPi x (Pi.single .iPsiCubePsi 1) t z = Q (fun y => (Zt (p y) - Zt (p x)) * J (p y)) ∧
    Z.regPi x (Pi.single .iPsiCubePsiSq 1) t z =
      Q (fun y => (Zt (p y) - Zt (p x)) * V (p y) - 3 * C₂ C * J (p y)) := by
  obtain ⟨noise, hn, hRC, hF⟩ := regPi_fMinus hZ
  have hn' := noise_zeta_eq hn
  have hf' : IsSmoothOnSpaceTime ((fun _ : Unit => f) ()) := hf
  have hpsi := CanonicalData.hairerCanonicalData_renormalisedPi_basis_psi_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) (κ := κ)
    (N := N) C x hn' hf'
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_noise_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn']
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z, hpsi]; rfl
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_psiSq_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf']
    rfl
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_psiCube_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf']
    rfl
  · rw [regPi_integrated hg hn hRC (Or.inl rfl) x ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiSq_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf']
    congr 1; funext y
    exact pairing_treeJ_sq hf (C₁ C) _ _
  · rw [regPi_integrated hg hn hRC (Or.inr rfl) x ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCube_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf']
    congr 1; funext y
    exact pairing_treeW hf (C₁ C) _ _
  · intro i
    rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_psiSqX_eq (ξ := fun _ : Unit => f) (ω := ()) x C hn' hf' i]
    congr 1; funext y; simp only [treeV, hairerTreePsiSq, treeJ]; ring
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiSqPsiSq_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf']
    congr 1; funext y
    simp only [hairerTreeI2Psi2]
    rw [show (∫ w, hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
        hairerTreePsiSq N (fun _ : Unit => f) (C₁ C) () w) =
        hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y) (treeV N f (C₁ C))
      from rfl, pairing_treeV hf]
    rfl
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCubePsi_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn' hf']
    congr 1; funext y
    simp only [hairerTreeI3Psi]
    rw [show (∫ w, hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
        hairerTreePsiCube N (fun _ : Unit => f) (C₁ C) () w) =
        hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y) (treeW N f (C₁ C))
      from rfl, pairing_treeW hf]
    rfl
  · rw [hF _ (by simp [mem_fMinus_iff_isFMinus, isFMinus]) x t ht z,
      CanonicalData.hairerCanonicalData_renormalisedPi_basis_iPsiCubePsiSq_eq_treeField (ξ := fun _ : Unit => f) (ω := ()) C x hn'
        hf']
    congr 1; funext y
    simp only [hairerTreeI3Psi2]
    rw [show (∫ w, hairerI2Psi2Kernel N (spaceTimeProj x) (spaceTimeProj y) w *
        hairerTreePsiCube N (fun _ : Unit => f) (C₁ C) () w) =
        hairerKernelIncrementPairing N (spaceTimeProj x) (spaceTimeProj y) (treeW N f (C₁ C))
      from rfl, pairing_treeW hf]
    rfl

/-! ### Renormalisation constants `(C₁', C₂')` -/

end GlobalPhi43.Attachment

end

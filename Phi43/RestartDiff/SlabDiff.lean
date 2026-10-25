/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.Slab
public import Phi43.RestartDiff.OldGammaDiff

/-!
# Near-pair `Γ`-difference of two enlarged models at level `κ + 2` on a time slab

Two-model companion of `Phi43.Restart.Slab`.  Let `M₁'`, `M₂'` be compatible with the translates
by the same point `a` of the renormalised canonical models of two noises.  Given the Hairer
estimate for the integrals of the sources for each model (constant `E`, `hb₁`, `hb₂`) and for
their difference (constant `Ed`, `hbd`), all entries of `Γ'¹_{yx} − Γ'²_{yx}` of degree
`< κ + 2` obey `max (oldGammaDiffConst (max 1 E) · Ed) Ed · d^{deg i - deg j}` for `d ≤ 1`:

* old symbols: the four integrated entries (`𝓘 Ψ`, `𝓘 Ψ²`, `𝓘 Ψ³`) are controlled by `hb₁`,
  `hb₂` (sizes) and `hbd` (differences); all old entries follow from the Lipschitz bound of the
  structure-group action (`translate_gammaMap_bound_diff`);
* planted symbols of degree `< κ + 2` are `𝓘 e_d` with `deg d < κ`: `hbd` again;
* old symbols never reach planted coordinates.
-/

public section

open Set

namespace RegularityStructures.Phi43.Restart

variable {κ : Kappa}

private theorem integration_old_psi' :
    phi43IntegrationF (Pi.single (SymbolF.old .psi) 1) = Pi.single (SymbolF.old .iPsi) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ =>
      simp only [phi43IntegrationF]
      exact (Pi.single_eq_of_ne (fun h => phi43PlantDE_ne_psi (phi43PlantSource_symbol_mem σ)
        (SymbolF.old.inj h)) _).symm.symm

private theorem integration_old_psiSq' :
    phi43IntegrationF (Pi.single (SymbolF.old .psiSq) 1) = Pi.single (SymbolF.old .iPsiSq) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ =>
      simp only [phi43IntegrationF]
      exact (Pi.single_eq_of_ne (fun h => phi43PlantDE_ne_psiSq (phi43PlantSource_symbol_mem σ)
        (SymbolF.old.inj h)) _).symm.symm

private theorem integration_old_psiCube' :
    phi43IntegrationF (Pi.single (SymbolF.old .psiCube) 1) =
      Pi.single (SymbolF.old .iPsiCube) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ =>
      simp only [phi43IntegrationF]
      exact (Pi.single_eq_of_ne (fun h => phi43PlantDE_ne_psiCube (phi43PlantSource_symbol_mem σ)
        (SymbolF.old.inj h)) _).symm.symm

variable {N : ℕ} {M₁' M₂' : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {noise noise' : CanonicalNoise} {Cg Cg' : ℝ} {q q' : ℕ}
  {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
  {hg' : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise'.zeta z‖ ≤ Cg' * (1 + parabolicNorm z) ^ q'}
  {C C' : RenormalisationConstants} {a : ParabolicSpace}

/-- **The `Γ`-difference of `M₁'` and `M₂'` at level `κ + 2`** on the slab `(0, T']`, `T' ≤ 1`,
near pairs. -/
theorem gammaBoundNearOn_kappa_add_two_diff {E Ed : ℝ} (hEd : 0 ≤ Ed)
    (hC₁ : EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate a) M₁')
    (hC₂ : EnlargedCompat κ ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a)
      M₂')
    (hb₁ : ∀ i, ExtSource κ i → ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j,
      phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M₁'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        E * parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j))
    (hb₂ : ∀ i, ExtSource κ i → ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j,
      phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M₂'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        E * parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j))
    (hbd : ∀ i, ExtSource κ i → ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j,
      phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M₁'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j -
          M₂'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        Ed * parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j))
    {T' : ℝ} (hT' : T' ≤ 1) :
    M₁'.GammaDiffBoundNearOn M₂' (κ.1 + 2)
      (max (oldGammaDiffConst (max 1 E) * Ed) Ed) 1 (timeSlab T') := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hsub : timeSlab T' ⊆ timeSlab 1 := fun z hz => ⟨hz.1, hz.2.trans hT'⟩
  have hA : (1 : ℝ) ≤ max 1 E := le_max_left _ _
  have hC0 : 0 ≤ max (oldGammaDiffConst (max 1 E) * Ed) Ed := le_trans hEd (le_max_right _ _)
  intro i j hi hji x hx y hy hxy
  have hxy4 : parabolicNorm (y - x) ≤ gammaNearRadius :=
    le_gammaNearRadius_of_le_one hxy
  have hx1 := hsub hx
  have hy1 := hsub hy
  set d := parabolicNorm (y - x) with hd
  have hd0 : 0 ≤ d := parabolicNorm_nonneg _
  have key : ∀ (s s' u : Symbol), ExtSource κ (.old s) →
      phi43IntegrationF (Pi.single (SymbolF.old s) 1) = Pi.single (SymbolF.old s') 1 →
      homogeneity κ s' = homogeneity κ s + 2 → homogeneity κ u < homogeneity κ s' →
      |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
          (Pi.single s' 1) u| ≤ max 1 E * d ^ (homogeneity κ s' - homogeneity κ u) ∧
      |((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
          (Pi.single s' 1) u| ≤ max 1 E * d ^ (homogeneity κ s' - homogeneity κ u) ∧
      |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap y x
          (Pi.single s' 1) u -
        ((canonicalRenormalisedModel N κ noise' Cg' q' hg' C').translate a).gammaMap y x
          (Pi.single s' 1) u| ≤ Ed * d ^ (homogeneity κ s' - homogeneity κ u) := by
    intro s s' u hext hI hs' hu
    have hlt : phi43DegreeF κ (.old u) < phi43DegreeF κ (.old s) + 2 := by
      change homogeneity κ u < homogeneity κ s + 2
      linarith
    have h1 := hb₁ _ hext hx1 hy1 hxy4 (.old u) hlt
    have h2 := hb₂ _ hext hx1 hy1 hxy4 (.old u) hlt
    have h3 := hbd _ hext hx1 hy1 hxy4 (.old u) hlt
    rw [hI, hC₁.gammaMap_single_old] at h1
    rw [hI, hC₂.gammaMap_single_old] at h2
    rw [hI, hC₁.gammaMap_single_old, hC₂.gammaMap_single_old] at h3
    change _ ≤ E * d ^ (homogeneity κ s + 2 - homogeneity κ u) at h1
    change _ ≤ E * d ^ (homogeneity κ s + 2 - homogeneity κ u) at h2
    change _ ≤ Ed * d ^ (homogeneity κ s + 2 - homogeneity κ u) at h3
    rw [← hs'] at h1 h2 h3
    exact ⟨h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd0 _)),
      h2.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd0 _)), h3⟩
  cases i with
  | planted p =>
      have hext := extSource_of_planted p hi
      have h1 := hbd _ hext hx1 hy1 hxy4 j (by
        change phi43DegreeF κ j < homogeneity κ p.symbol + 2
        exact hji.trans_eq rfl |>.trans_le le_rfl)
      rw [phi43IntegrationF_old_source] at h1
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd0 _)
  | old τ =>
      cases j with
      | planted p =>
          rw [hC₁.gammaMap_single_planted, hC₂.gammaMap_single_planted, sub_zero, abs_zero]
          exact mul_nonneg hC0 (Real.rpow_nonneg hd0 _)
      | old σ =>
          rw [hC₁.gammaMap_single_old, hC₂.gammaMap_single_old]
          have hσ : homogeneity κ σ < homogeneity κ τ := hji
          obtain ⟨hp₁, hp₂, hpd⟩ := key .psi .iPsi .one (extSource_psi κ) integration_old_psi'
            (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          have hpg := fun i : Fin 3 =>
            key .psi .iPsi (.x i) (extSource_psi κ) integration_old_psi'
              (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          obtain ⟨hs₁, hs₂, hsd⟩ := key .psiSq .iPsiSq .one (extSource_psiSq κ)
            integration_old_psiSq'
            (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          obtain ⟨hc₁, hc₂, hcd⟩ := key .psiCube .iPsiCube .one (extSource_psiCube κ)
            integration_old_psiCube'
            (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          have := translate_gammaMap_bound_diff N κ noise noise' Cg Cg' q q' hg hg' C C' a hA hEd
            y x
            (by simpa only [homogeneity, sub_zero] using hp₁)
            (fun i => by simpa only [homogeneity] using (hpg i).1)
            (by simpa only [homogeneity, sub_zero] using hs₁)
            (by simpa only [homogeneity, sub_zero] using hc₁)
            (by simpa only [homogeneity, sub_zero] using hp₂)
            (fun i => by simpa only [homogeneity] using (hpg i).2.1)
            (by simpa only [homogeneity, sub_zero] using hs₂)
            (by simpa only [homogeneity, sub_zero] using hc₂)
            (by simpa only [homogeneity, sub_zero] using hpd)
            (fun i => by simpa only [homogeneity] using (hpg i).2.2)
            (by simpa only [homogeneity, sub_zero] using hsd)
            (by simpa only [homogeneity, sub_zero] using hcd) τ σ hσ
          exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd0 _))

end RegularityStructures.Phi43.Restart

end

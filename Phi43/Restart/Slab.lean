/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Restart.OldGamma
public import Phi43.Restart.ExtGamma

/-!
# Near-pair `Γ`-bound of the enlarged model at level `κ + 2` on a time slab

Given the Hairer estimate `hb` for the integrals of the sources (`ExtGamma`) with constant `E`, and
the compatibility of `M'` with a translate of the canonical model, all entries of `Γ'_{yx}` of
degree `< κ + 2` obey `max (oldGammaConst (max 1 E)) E · d^{deg i - deg j}` for `d ≤ 1`:

* old symbols: the four integrated entries (`𝓘 Ψ`, `𝓘 Ψ²`, `𝓘 Ψ³`) are bounded by `E` through `hb`;
  all old entries follow (`OldGamma`);
* planted symbols of degree `< κ + 2` are `𝓘 e_d` with `deg d < κ`: `hb` again.
-/

public section

open Set

namespace RegularityStructures.Phi43.Restart

variable {κ : Kappa}

private theorem integration_old_psi :
    phi43IntegrationF (Pi.single (SymbolF.old .psi) 1) = Pi.single (SymbolF.old .iPsi) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ =>
      simp only [phi43IntegrationF]
      exact (Pi.single_eq_of_ne (fun h => phi43PlantDE_ne_psi (phi43PlantSource_symbol_mem σ)
        (SymbolF.old.inj h)) _).symm.symm

private theorem integration_old_psiSq :
    phi43IntegrationF (Pi.single (SymbolF.old .psiSq) 1) = Pi.single (SymbolF.old .iPsiSq) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ =>
      simp only [phi43IntegrationF]
      exact (Pi.single_eq_of_ne (fun h => phi43PlantDE_ne_psiSq (phi43PlantSource_symbol_mem σ)
        (SymbolF.old.inj h)) _).symm.symm

private theorem integration_old_psiCube :
    phi43IntegrationF (Pi.single (SymbolF.old .psiCube) 1) =
      Pi.single (SymbolF.old .iPsiCube) 1 := by
  funext σ
  cases σ with
  | old σ => cases σ <;> simp [phi43IntegrationF]
  | planted σ =>
      simp only [phi43IntegrationF]
      exact (Pi.single_eq_of_ne (fun h => phi43PlantDE_ne_psiCube (phi43PlantSource_symbol_mem σ)
        (SymbolF.old.inj h)) _).symm.symm

theorem extSource_psi (κ : Kappa) : ExtSource κ (.old .psi) :=
  ⟨.psi, rfl, by simp, by simp, by simp only [homogeneity]; linarith [κ.2.1]⟩

theorem extSource_psiSq (κ : Kappa) : ExtSource κ (.old .psiSq) :=
  ⟨.psiSq, rfl, by simp, by simp, by simp only [homogeneity]; linarith [κ.2.1]⟩

theorem extSource_psiCube (κ : Kappa) : ExtSource κ (.old .psiCube) :=
  ⟨.psiCube, rfl, by simp, by simp, by simp only [homogeneity]; linarith [κ.2.1]⟩

/-- A planted symbol of degree `< κ + 2` is the integral of a source in `ExtSource`. -/
theorem extSource_of_planted (p : Phi43PlantSource)
    (h : phi43DegreeF κ (.planted p) < κ.1 + 2) : ExtSource κ (.old p.symbol) := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  refine ⟨p.symbol, rfl, phi43PlantDE_ne_noise (phi43PlantSource_symbol_mem p), ?_, ?_⟩
  · cases p <;> simp [Phi43PlantSource.symbol]
  · change homogeneity κ p.symbol + 2 < κ.1 + 2 at h
    linarith

variable {N : ℕ} {M' : Model (phi43RegularityStructureF κ) parabolicSemigroup}
  {noise : CanonicalNoise} {Cg : ℝ} {q : ℕ}
  {hg : ∀ k : ℕ, k ≤ 4 → ∀ z : ParabolicSpace,
    ‖iteratedFDeriv ℝ k noise.zeta z‖ ≤ Cg * (1 + parabolicNorm z) ^ q}
  {C : RenormalisationConstants} {a : ParabolicSpace}

/-- **The `Γ`-bound of `M'` at level `κ + 2`** on the slab `(0, T']`, `T' ≤ 1`, near pairs. -/
theorem gammaBoundNearOn_kappa_add_two {E : ℝ} (hE : 0 ≤ E)
    (hC : EnlargedCompat κ ((canonicalRenormalisedModel N κ noise Cg q hg C).translate a) M')
    (hb : ∀ i, ExtSource κ i → ∀ {x y : ParabolicSpace}, x ∈ timeSlab 1 → y ∈ timeSlab 1 →
      parabolicNorm (y - x) ≤ gammaNearRadius → ∀ j,
      phi43DegreeF κ j < phi43DegreeF κ i + 2 →
      |M'.gammaMap y x (phi43IntegrationF (Pi.single i 1)) j| ≤
        E * parabolicNorm (y - x) ^ (phi43DegreeF κ i + 2 - phi43DegreeF κ j))
    {T' : ℝ} (hT' : T' ≤ 1) :
    M'.GammaBoundNearOn (κ.1 + 2) (max (oldGammaConst (max 1 E)) E) 1 (timeSlab T') := by
  have hk : 0 < κ.1 := κ.2.1
  have hk' : κ.1 < 1 / 16 := κ.2.2
  have hsub : timeSlab T' ⊆ timeSlab 1 := fun z hz => ⟨hz.1, hz.2.trans hT'⟩
  have hA : (1 : ℝ) ≤ max 1 E := le_max_left _ _
  have hC0 : 0 ≤ max (oldGammaConst (max 1 E)) E := le_trans hE (le_max_right _ _)
  have hold0 : 0 ≤ oldGammaConst (max 1 E) := oldGammaConst_nonneg (by linarith)
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
          (Pi.single s' 1) u| ≤ max 1 E * d ^ (homogeneity κ s' - homogeneity κ u) := by
    intro s s' u hext hI hs' hu
    have h1 := hb _ hext hx1 hy1 hxy4 (.old u) (by
      change homogeneity κ u < homogeneity κ s + 2
      linarith)
    rw [hI, hC.gammaMap_single_old] at h1
    change _ ≤ E * d ^ (homogeneity κ s + 2 - homogeneity κ u) at h1
    rw [← hs'] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd0 _))
  cases i with
  | planted p =>
      have hext := extSource_of_planted p hi
      have h1 := hb _ hext hx1 hy1 hxy4 j (by
        change phi43DegreeF κ j < homogeneity κ p.symbol + 2
        exact hji.trans_eq rfl |>.trans_le le_rfl)
      rw [phi43IntegrationF_old_source] at h1
      refine h1.trans ?_
      exact mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hd0 _)
  | old τ =>
      cases j with
      | planted p =>
          rw [hC.gammaMap_single_planted, abs_zero]
          exact mul_nonneg hC0 (Real.rpow_nonneg hd0 _)
      | old σ =>
          rw [hC.gammaMap_single_old]
          have hσ : homogeneity κ σ < homogeneity κ τ := hji
          have hp := key .psi .iPsi .one (extSource_psi κ) integration_old_psi
            (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          have hpg : ∀ i : Fin 3, |((canonicalRenormalisedModel N κ noise Cg q hg C).translate a).gammaMap
              y x (Pi.single .iPsi 1) (.x i)| ≤
              max 1 E * d ^ (homogeneity κ .iPsi - 1) := fun i => by
            have := key .psi .iPsi (.x i) (extSource_psi κ) integration_old_psi
              (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
            simpa only [homogeneity] using this
          have hs := key .psiSq .iPsiSq .one (extSource_psiSq κ) integration_old_psiSq
            (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          have hc := key .psiCube .iPsiCube .one (extSource_psiCube κ) integration_old_psiCube
            (by simp only [homogeneity]; ring) (by simp only [homogeneity]; linarith)
          have := translate_gammaMap_bound N κ noise Cg q hg C a hA y x
            (by simpa only [homogeneity, sub_zero] using hp) hpg
            (by simpa only [homogeneity, sub_zero] using hs)
            (by simpa only [homogeneity, sub_zero] using hc) τ σ hσ
          exact this.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hd0 _))

end RegularityStructures.Phi43.Restart

end

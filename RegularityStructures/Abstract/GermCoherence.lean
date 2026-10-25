/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Germ
public import RegularityStructures.Abstract.ModelledDistribution
public import RegularityStructures.Analysis.Semigroup.Germ

/-!
# The germ of a modelled distribution

For a model `M` and `f : E → ι → ℝ`, `Model.germ` is the family `y ↦ Π_y f(y)` seen through its
regularisations, `M.germ f y t z = (Q_t Π_y f(y))(z)`. If `f ∈ D^γ`, it is a germ
(`Model.isGerm_germ`) and it is coherent of order `γ` (`Model.isCoherent_germ`); the difference of
the germs of two models satisfies the coherence bound of the local Lipschitz estimate
(`Model.isCoherent_germ_sub`).

Source: [Hos25, proof of Theorem 4.1], [Hai14, Theorem 3.10].
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The germ `y ↦ Π_y f(y)` of a modelled distribution, through its regularisations:
`M.germ f y t z = (Q_t Π_y f(y))(z)`. -/
def germ (M : Model 𝒯 K) (f : E → ι → ℝ) (y : E) (t : ℝ) (z : E) : ℝ :=
  M.regPi y (f y) t z

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

/-- A sum over the basis vectors of degree `< γ` of a function of the degree is at most `|ι|`
times the sum over the set of degrees. -/
theorem sum_filter_deg_le_card_mul (𝒯 : RegularityStructure ι) (γ : ℝ) {h : ℝ → ℝ}
    (hh : ∀ a ∈ 𝒯.degreesBelow γ, 0 ≤ h a) :
    ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), h (𝒯.deg j) ≤
      Fintype.card ι * ∑ a ∈ 𝒯.degreesBelow γ, h a := by
  have hS : 0 ≤ ∑ a ∈ 𝒯.degreesBelow γ, h a := Finset.sum_nonneg hh
  calc ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), h (𝒯.deg j)
      ≤ ∑ _j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), ∑ a ∈ 𝒯.degreesBelow γ, h a := by
        refine Finset.sum_le_sum fun j hj => ?_
        have hmem : 𝒯.deg j ∈ 𝒯.degreesBelow γ :=
          (𝒯.mem_degreesBelow).2 ⟨j, (Finset.mem_filter.1 hj).2, rfl⟩
        exact Finset.single_le_sum hh hmem
    _ = (Finset.univ.filter (fun j => 𝒯.deg j < γ)).card * ∑ a ∈ 𝒯.degreesBelow γ, h a := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card ι * ∑ a ∈ 𝒯.degreesBelow γ, h a := by
        refine mul_le_mul_of_nonneg_right ?_ hS
        exact_mod_cast Finset.card_le_univ _

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem germ_mem (f : E → ι → ℝ) (y : E) : M.germ f y ∈ K.distributions :=
  M.regPi_mem y (f y)

theorem germ_diag (f : E → ι → ℝ) (t : ℝ) (x : E) :
    RegularisingSemigroup.diag (M.germ f) t x = M.regPi x (f x) t x :=
  rfl

/-- The coherence identity `Q_t(z, F_y − F_z) = Q_t(z, Π_z (Γ_{zy} f(y) − f(z)))`. -/
theorem germ_sub_germ (f : E → ι → ℝ) (y z : E) (t : ℝ) :
    M.germ f y t z - M.germ f z t z = M.regPi z (M.gammaMap z y (f y) - f z) t z := by
  rw [germ, germ, M.regPi_sub, M.regPi_gammaMap]

theorem measurable_diag_germ {γ : ℝ} {f : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ)
    {t : ℝ} (ht : 0 < t) : Measurable (RegularisingSemigroup.diag (M.germ f) t) := by
  have h : RegularisingSemigroup.diag (M.germ f) t = fun x => ∑ i, f x i * M.regPi x (Pi.single i 1) t x := by
    funext x
    rw [germ_diag, M.regPi_eq_sum]
  rw [h]
  refine Finset.measurable_sum _ fun i _ => ?_
  exact ((measurable_pi_apply i).comp hf.1).mul (M.measurable_diag i ht)

/-- Size of the diagonal: `|Q_t(x, Π_x f(x))| ≤ C_f C_Π ∑_{deg j < γ} t^{deg j/ℓ}`. -/
theorem abs_diag_germ_le {γ CPi Cf : ℝ} (hPi : M.PiBoundOn γ CPi univ)
    {f : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (x : E) :
    |RegularisingSemigroup.diag (M.germ f) t x| ≤
      ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), Cf * CPi * t ^ (𝒯.deg j / K.order) := by
  rw [germ_diag, M.regPi_eq_sum_filter (hf.2.1 x)]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j hj => ?_)
  have hj : 𝒯.deg j < γ := (Finset.mem_filter.1 hj).2
  rw [abs_mul, mul_assoc]
  exact mul_le_mul (hfb.1 x (mem_univ x) j hj) (hPi j hj t ht x (mem_univ x)) (abs_nonneg _)
    ((abs_nonneg _).trans (hfb.1 x (mem_univ x) j hj))

/-- `F_y = Π_y f(y)` is a germ in the sense of `RegularisingSemigroup.IsGerm`. -/
theorem isGerm_germ {γ CPi : ℝ} (hPi : M.PiBoundOn γ CPi univ) {f : E → ι → ℝ}
    (hf : f ∈ M.modelledDistributions γ) : K.IsGerm (M.germ f) where
  mem := M.germ_mem f
  measurable_diag _ ht := M.measurable_diag_germ hf ht
  bounded_diag t ht := by
    obtain ⟨Cf, hfb⟩ := hf.2.2
    exact ⟨_, M.abs_diag_germ_le hPi hf hfb ht⟩

/-- The coherence bound of `F_y = Π_y f(y)` [Hos25, proof of Theorem 4.1, step (1)]. -/
theorem isCoherent_germ {γ CPi Cf : ℝ} (hPi : M.PiBoundOn γ CPi univ) (hCPi : 0 ≤ CPi)
    {f : E → ι → ℝ} (hf : f ∈ M.modelledDistributions γ) (hfb : M.ModelledBoundOn γ Cf univ f)
    (hCf : 0 ≤ Cf) :
    K.IsCoherent (M.germ f) γ (𝒯.degreesBelow γ) (Fintype.card ι * (Cf * CPi)) := by
  intro t ht y z
  have hτ : M.gammaMap z y (f y) - f z ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ ((M.isGradedUnipotent_gammaMap z y).map_lowerSubspace (hf.2.1 y))
      (hf.2.1 z)
  rw [M.germ_sub_germ, M.regPi_eq_sum_filter hτ, mul_assoc, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun j hj => ?_)
    (sum_filter_deg_le_card_mul 𝒯 γ (h := fun a =>
      Cf * CPi * (t ^ (a / K.order) * K.scaleDist z y ^ (γ - a))) fun a _ => ?_)
  · have hj : 𝒯.deg j < γ := (Finset.mem_filter.1 hj).2
    have h1 : |(M.gammaMap z y (f y) - f z) j| ≤ Cf * K.scaleDist z y ^ (γ - 𝒯.deg j) := by
      rw [← abs_neg, Pi.sub_apply, neg_sub, ← Pi.sub_apply]
      exact hfb.2 y (mem_univ y) z (mem_univ z) j hj
    have h2 := hPi j hj t ht z (mem_univ z)
    rw [abs_mul]
    calc |(M.gammaMap z y (f y) - f z) j| * |M.regPi z (Pi.single j 1) t z|
        ≤ (Cf * K.scaleDist z y ^ (γ - 𝒯.deg j)) * (CPi * t ^ (𝒯.deg j / K.order)) :=
          mul_le_mul h1 h2 (abs_nonneg _)
            (mul_nonneg hCf (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))
      _ = Cf * CPi * (t ^ (𝒯.deg j / K.order) * K.scaleDist z y ^ (γ - 𝒯.deg j)) := by ring
  · exact mul_nonneg (mul_nonneg hCf hCPi)
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))

/-- The coherence bound for the difference of the germs of two models
(the local Lipschitz estimate of [Hos25, Theorem 4.1], [Hai14, Theorem 3.10 (3.4)]). -/
theorem isCoherent_germ_sub (M₁ M₂ : Model 𝒯 K) {γ CPi₂ CdPi Cf₁ Cdf : ℝ}
    (hPi₂ : M₂.PiBoundOn γ CPi₂ univ) (hdPi : M₁.PiDiffBoundOn M₂ γ CdPi univ)
    {f₁ f₂ : E → ι → ℝ} (hf₁ : f₁ ∈ M₁.modelledDistributions γ)
    (hf₂ : f₂ ∈ M₂.modelledDistributions γ) (hfb₁ : M₁.ModelledBoundOn γ Cf₁ univ f₁)
    (hdf : M₁.ModelledDiffBoundOn M₂ γ Cdf univ f₁ f₂) (hCf₁ : 0 ≤ Cf₁) (hCdf : 0 ≤ Cdf)
    (hCdPi : 0 ≤ CdPi) (hCPi₂ : 0 ≤ CPi₂) :
    K.IsCoherent (fun y => M₁.germ f₁ y - M₂.germ f₂ y) γ (𝒯.degreesBelow γ)
      (Fintype.card ι * (Cf₁ * CdPi + Cdf * CPi₂)) := by
  intro t ht y z
  set Δ₁ := M₁.gammaMap z y (f₁ y) - f₁ z with hΔ₁
  set Δ₂ := M₂.gammaMap z y (f₂ y) - f₂ z with hΔ₂
  have hτ₁ : Δ₁ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ ((M₁.isGradedUnipotent_gammaMap z y).map_lowerSubspace (hf₁.2.1 y))
      (hf₁.2.1 z)
  have hτ₂ : Δ₂ ∈ lowerSubspace 𝒯.deg γ :=
    Submodule.sub_mem _ ((M₂.isGradedUnipotent_gammaMap z y).map_lowerSubspace (hf₂.2.1 y))
      (hf₂.2.1 z)
  have hid : (M₁.germ f₁ y - M₂.germ f₂ y) t z - (M₁.germ f₁ z - M₂.germ f₂ z) t z =
      ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ),
        (Δ₁ j * (M₁.regPi z (Pi.single j 1) t z - M₂.regPi z (Pi.single j 1) t z) +
          (Δ₁ j - Δ₂ j) * M₂.regPi z (Pi.single j 1) t z) := by
    have e₁ := M₁.germ_sub_germ f₁ y z t
    have e₂ := M₂.germ_sub_germ f₂ y z t
    rw [M₁.regPi_eq_sum_filter hτ₁] at e₁
    rw [M₂.regPi_eq_sum_filter hτ₂] at e₂
    simp only [Pi.sub_apply]
    calc M₁.germ f₁ y t z - M₂.germ f₂ y t z - (M₁.germ f₁ z t z - M₂.germ f₂ z t z)
        = (M₁.germ f₁ y t z - M₁.germ f₁ z t z) - (M₂.germ f₂ y t z - M₂.germ f₂ z t z) := by
          ring
      _ = _ := by
          rw [e₁, e₂, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
  rw [hid, mul_assoc, Finset.mul_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  refine le_trans (Finset.sum_le_sum fun j hj => ?_)
    (sum_filter_deg_le_card_mul 𝒯 γ (h := fun a =>
      (Cf₁ * CdPi + Cdf * CPi₂) * (t ^ (a / K.order) * K.scaleDist z y ^ (γ - a)))
      fun a _ => ?_)
  · have hj : 𝒯.deg j < γ := (Finset.mem_filter.1 hj).2
    have hd : 0 ≤ K.scaleDist z y ^ (γ - 𝒯.deg j) :=
      Real.rpow_nonneg (K.scaleDist_nonneg _ _) _
    have h1 : |Δ₁ j| ≤ Cf₁ * K.scaleDist z y ^ (γ - 𝒯.deg j) := by
      rw [hΔ₁, ← abs_neg, Pi.sub_apply, neg_sub, ← Pi.sub_apply]
      exact hfb₁.2 y (mem_univ y) z (mem_univ z) j hj
    have h2 : |Δ₁ j - Δ₂ j| ≤ Cdf * K.scaleDist z y ^ (γ - 𝒯.deg j) := by
      have := hdf.2 y (mem_univ y) z (mem_univ z) j hj
      rw [← abs_neg]
      convert this using 2
      simp only [hΔ₁, hΔ₂, Pi.sub_apply]
      ring
    have h3 := hdPi j hj t ht z (mem_univ z)
    have h4 := hPi₂ j hj t ht z (mem_univ z)
    have ht' : 0 ≤ t ^ (𝒯.deg j / K.order) := Real.rpow_nonneg ht.1.le _
    calc |Δ₁ j * (M₁.regPi z (Pi.single j 1) t z - M₂.regPi z (Pi.single j 1) t z) +
          (Δ₁ j - Δ₂ j) * M₂.regPi z (Pi.single j 1) t z|
        ≤ |Δ₁ j| * |M₁.regPi z (Pi.single j 1) t z - M₂.regPi z (Pi.single j 1) t z| +
          |Δ₁ j - Δ₂ j| * |M₂.regPi z (Pi.single j 1) t z| := by
          rw [← abs_mul, ← abs_mul]
          exact abs_add_le _ _
      _ ≤ (Cf₁ * K.scaleDist z y ^ (γ - 𝒯.deg j)) * (CdPi * t ^ (𝒯.deg j / K.order)) +
          (Cdf * K.scaleDist z y ^ (γ - 𝒯.deg j)) * (CPi₂ * t ^ (𝒯.deg j / K.order)) :=
          add_le_add (mul_le_mul h1 h3 (abs_nonneg _) (mul_nonneg hCf₁ hd))
            (mul_le_mul h2 h4 (abs_nonneg _) (mul_nonneg hCdf hd))
      _ = (Cf₁ * CdPi + Cdf * CPi₂) *
          (t ^ (𝒯.deg j / K.order) * K.scaleDist z y ^ (γ - 𝒯.deg j)) := by ring
  · exact mul_nonneg (add_nonneg (mul_nonneg hCf₁ hCdPi) (mul_nonneg hCdf hCPi₂))
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg (K.scaleDist_nonneg _ _) _))

end Model

end RegularityStructures

end

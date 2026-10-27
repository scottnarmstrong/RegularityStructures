module

public import GlobalPhi43.Local.RadiusGeometry
public import GlobalPhi43.MW20.ScaledKernelSeed

public section

namespace GlobalPhi43.Local

open RegularityStructures Set
open scoped ContDiff

/-- Translated parabolic coordinate map; no fixed-cylinder invariance is implied. -/
@[expose] def parabolicMap (b : ParabolicSpace) (ℓ : ℝ) (z : ParabolicSpace) :
    ParabolicSpace := b + parabolicDilate ℓ z

/-- Independent amplitude and coordinate scale. -/
@[expose] def parabolicPullback (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) (z : ParabolicSpace) : ℝ := a*f (parabolicMap b ℓ z)

@[expose] noncomputable def parabolicTransport (b : ParabolicSpace) (ℓ : ℝ) (hℓ : ℓ ≠ 0) :
    ParabolicSpace ≃ₜ ParabolicSpace :=
  (MW20.parabolicKernelHomeomorph ℓ hℓ).trans (Homeomorph.addLeft b)

/-- Exact max-metric dilation covariance, with translations cancelled. -/
theorem pdist_parabolicMap (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x y : ParabolicSpace) :
    pdist (parabolicMap b ℓ x) (parabolicMap b ℓ y) = ℓ*pdist x y := by
  have ht : (parabolicMap b ℓ x).1-(parabolicMap b ℓ y).1 = ℓ^2*(x.1-y.1) := by
    simp only [parabolicMap,parabolicDilate,Prod.fst_add]
    ring
  have hs : (parabolicMap b ℓ x).2-(parabolicMap b ℓ y).2 = ℓ • (x.2-y.2) := by
    simp only [parabolicMap,parabolicDilate,Prod.snd_add,add_sub_add_left_eq_sub,smul_sub]
  rw [pdist,ht,hs,abs_mul,abs_of_nonneg (sq_nonneg ℓ),Real.sqrt_mul (sq_nonneg ℓ),
    Real.sqrt_sq hℓ.le,norm_smul,Real.norm_eq_abs,abs_of_pos hℓ]
  exact (mul_max_of_nonneg _ _ hℓ.le).symm

/-- Both the strict past condition and the exact radius are preserved. -/
theorem parabolicMap_mem_pastBall (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x y : ParabolicSpace) (R : ℝ) :
    parabolicMap b ℓ y ∈ pastBall (parabolicMap b ℓ x) (ℓ*R) ↔ y ∈ pastBall x R := by
  change (_ < ℓ*R ∧ _ < _) ↔ (_ < R ∧ y.1 < x.1)
  rw [pdist_parabolicMap b hℓ, mul_lt_mul_iff_right₀ hℓ]
  have ht : (parabolicMap b ℓ y).1 < (parabolicMap b ℓ x).1 ↔ y.1 < x.1 := by
    change b.1+ℓ^2*y.1 < b.1+ℓ^2*x.1 ↔ _
    rw [add_lt_add_iff_left,mul_lt_mul_iff_right₀ (sq_pos_of_pos hℓ)]
  rw [ht]

theorem parabolicMap_preimage_pastBall (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : ParabolicSpace) (R : ℝ) :
    parabolicMap b ℓ ⁻¹' pastBall (parabolicMap b ℓ x) (ℓ*R) = pastBall x R := by
  ext y
  exact parabolicMap_mem_pastBall b hℓ x y R

theorem parabolicMap_image_pastBall (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : ParabolicSpace) (R : ℝ) :
    parabolicMap b ℓ '' pastBall x R = pastBall (parabolicMap b ℓ x) (ℓ*R) := by
  rw [← parabolicMap_preimage_pastBall b hℓ x R]
  exact (parabolicTransport b ℓ hℓ.ne').surjective.image_preimage _

theorem parabolicMap_image_closure_pastBall (b : ParabolicSpace) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (x : ParabolicSpace) (R : ℝ) :
    parabolicMap b ℓ '' closure (pastBall x R) =
      closure (pastBall (parabolicMap b ℓ x) (ℓ*R)) := by
  rw [show parabolicMap b ℓ = parabolicTransport b ℓ hℓ.ne' from rfl,
    (parabolicTransport b ℓ hℓ.ne').image_closure]
  rw [show (parabolicTransport b ℓ hℓ.ne' : ParabolicSpace → ParabolicSpace) =
    parabolicMap b ℓ from rfl, parabolicMap_image_pastBall b hℓ]

/-- Smoothness is pulled back only from the actual source domain. -/
theorem parabolicPullback_contDiffOn (a : ℝ) (f : ParabolicSpace → ℝ)
    (b : ParabolicSpace) (ℓ : ℝ) {O : Set ParabolicSpace} (hf : ContDiffOn ℝ ∞ f O) :
    ContDiffOn ℝ ∞ (parabolicPullback a f b ℓ) (parabolicMap b ℓ ⁻¹' O) := by
  have hs : ContDiff ℝ ∞ (parabolicMap b ℓ) := by
    unfold parabolicMap parabolicDilate
    fun_prop
  exact contDiffOn_const.mul (hf.comp hs.contDiffOn (fun _ hx => hx))

end GlobalPhi43.Local

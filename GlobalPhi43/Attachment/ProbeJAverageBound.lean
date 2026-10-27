module

public import GlobalPhi43.Attachment.ProbeJAverageIdentity
public import GlobalPhi43.Attachment.ProbeJGaussianBound

/-! The averaged J estimate in the time-slice bound.
The model region is exactly C prime_s enlarged by the closed radius-three
max-parabolic ball. The constant depends only on kappa and N. -/

@[expose] public noncomputable section

open RegularityStructures RegularityStructures.Phi43 RegularityStructures.PDE MeasureTheory Set

namespace GlobalPhi43.Attachment

theorem probeModelWindow_torusRep (s : ℝ) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1)
    (x : Torus3) : (s+t, torusRep x) ∈ probeModelWindow s := by
  refine ⟨⟨by linarith [ht.1], by linarith [ht.2]⟩, ?_⟩
  constructor <;> intro i
  all_goals
    have hi := (AddCircle.equivIco (1 : ℝ) 0 (x i)).property
    change 0 ≤ torusRep x i ∧ torusRep x i < 0+1 at hi
    linarith [hi.1, hi.2]

/-- Constants precede the smooth noise, renormalisation constants, moderate
model, start, scale and spatial centre. No Gaussian or annular bounds are inputs. -/
theorem probeJ_average_bound (N : ℕ) (κ : Kappa) : ∃ D : ℝ, 0 < D ∧
    ∀ (f : SpaceTime → ℝ) (C : RenormalisationConstants)
      (Z : Model (phi43RegularityStructure κ) parabolicSemigroup)
      (hf : IsSmoothOnSpaceTime f), Statements.HasPhi43NoiseGrowth f →
      Statements.IsModeratePhi43ModelOf N κ f C Z →
    ∀ s t : ℝ, t ∈ Ioc (0 : ℝ) 1 →
    ‖probeJAverage N f hf s t‖ ≤
      D*(1+(Z.normOn (gamma κ)
        {y | ∃ z ∈ probeModelWindow s, Local.pdist z y ≤ 3}).toReal)^3 *
        t^((-1/2-(κ : ℝ))/2) := by
  obtain ⟨D, hD, hb⟩ := probeJ_gaussian_pairing_bound N κ
  refine ⟨D, hD, ?_⟩
  intro f C Z hf hg hZ s t ht
  have hr : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht.1
  have hr1 : Real.sqrt t ≤ 1 := (Real.sqrt_le_left zero_le_one).mpr (by simpa using ht.2)
  have hr2 : (Real.sqrt t)^2 = t := Real.sq_sqrt ht.1.le
  have hpow : (Real.sqrt t)^homogeneity κ .psi = t^((-1/2-(κ : ℝ))/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul ht.1.le]
    congr 1
    simp only [homogeneity]
    ring
  have hR : 0 ≤ D*(1+(Z.normOn (gamma κ)
      {y | ∃ z ∈ probeModelWindow s, Local.pdist z y ≤ 3}).toReal)^3 *
      t^((-1/2-(κ : ℝ))/2) :=
    mul_nonneg (mul_nonneg hD.le (pow_nonneg (by positivity) _))
      (Real.rpow_nonneg ht.1.le _)
  apply (ContinuousMap.norm_le _ hR).mpr
  intro x
  have hz := probeModelWindow_torusRep s ht x
  have hh := hb f C Z hf hg hZ s (Real.sqrt t) hr hr1 (s+t, torusRep x) hz (by simp only [hr2])
  have he := probeJAverage_eq_pairing (N := N) hf s hr hr1 (torusRep x)
  rw [hr2, torusProj_torusRep] at he
  rw [hr2, hpow, ← he] at hh
  simpa only [Real.norm_eq_abs] using hh

end GlobalPhi43.Attachment

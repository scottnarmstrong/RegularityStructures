module

public import GlobalPhi43.Attachment.Model
import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Translation invariance of the exact polynomial-growth event. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures RegularityStructures.Phi43

/-- Polynomial derivative growth is preserved under every time translation. -/
theorem noiseGrowth_time_translate {f : SpaceTime → ℝ}
    (hg : Statements.HasPhi43NoiseGrowth f) (k : ℝ) :
    Statements.HasPhi43NoiseGrowth (fun z => f (z.1 + k, z.2)) := by
  obtain ⟨Cg, q, hq⟩ := hg
  have hCg : 0 ≤ Cg := by
    have h := (norm_nonneg _).trans (hq 0 (by decide) 0)
    simpa only [parabolicNorm_zero, add_zero, one_pow, mul_one] using h
  let a : ParabolicSpace := (k, 0)
  let F := fun w : ParabolicSpace => f (w.1, torusProj w.2)
  have he : (fun w : ParabolicSpace => f (w.1 + k, torusProj w.2)) =
      fun w => F (w + a) := by
    funext w
    dsimp [F, a]
    rw [add_zero]
  refine ⟨Cg * (1 + parabolicNorm a) ^ q, q, ?_⟩
  intro n hn z
  rw [he, iteratedFDeriv_comp_add_right]
  calc _ ≤ Cg * (1 + parabolicNorm (z + a)) ^ q := hq n hn (z + a)
    _ ≤ Cg * ((1 + parabolicNorm a) * (1 + parabolicNorm z)) ^ q := by
      apply mul_le_mul_of_nonneg_left _ hCg
      apply pow_le_pow_left₀ (add_nonneg zero_le_one (parabolicNorm_nonneg (z + a)))
      have hadd := parabolicNorm_add_le z a
      have hprod := mul_nonneg (parabolicNorm_nonneg a) (parabolicNorm_nonneg z)
      nlinarith
    _ = _ := by rw [mul_pow]; ring

end GlobalPhi43.Attachment

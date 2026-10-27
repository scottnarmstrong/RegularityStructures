module

public import RegularityStructures.Analysis.Parabolic.TestFunction
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Exact recentering and scale identity for a cutoff piece. -/

public section

namespace GlobalPhi43.Attachment
open RegularityStructures

/-- A localized test at scale T is a fixed multiple of its profile at center x + S_T w
and scale T r. This is the algebraic normalization used in the large-scale partition argument. -/
theorem rescaled_piece_recenter (φ : ParabolicSpace → ℝ) {T r : ℝ}
    (hT : T ≠ 0) (hr : r ≠ 0) (x w y : ParabolicSpace) :
    rescaledTestFunction φ T x y = r ^ 5 *
      rescaledTestFunction (fun z => φ (w + parabolicDilate r z)) (T * r)
        (x + parabolicDilate T w) y := by
  have ha : w + parabolicDilate r (parabolicDilate (T * r)⁻¹
        (y - (x + parabolicDilate T w))) = parabolicDilate T⁻¹ (y - x) := by
    apply Prod.ext
    · simp only [parabolicDilate, Prod.fst_add, Prod.fst_sub]
      field_simp
      ring
    · funext i
      simp only [parabolicDilate, Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply,
        Pi.smul_apply, smul_eq_mul]
      field_simp
      ring
  unfold rescaledTestFunction
  dsimp only
  rw [ha]
  have hc : r ^ 5 * ((T * r) ^ 5)⁻¹ = (T ^ 5)⁻¹ := by
    field_simp
  rw [← mul_assoc, hc]

end GlobalPhi43.Attachment

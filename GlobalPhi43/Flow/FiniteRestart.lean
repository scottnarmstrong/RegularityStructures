module

public import GlobalPhi43.Flow.FiniteMeshEstimate
public import GlobalPhi43.Flow.LocalConsistency

public noncomputable section

open Set RegularityStructures RegularityStructures.Phi43
open scoped ENNReal NNReal

namespace GlobalPhi43.Flow

/-- Finite-horizon comparison under a supplied uniform state radius.
The common mesh and constants precede both actual lifts, the external start,
the data and the paths. The model horizon remains exactly `T + S`. -/
theorem exists_finiteRestartEstimate {κ : Kappa} {N : ℕ} (hN : 5 ≤ N)
    {η : NegExponent} (hη : (η : ℝ) ∈ Ioo (-(2 / 3 : ℝ)) (-(1 / 2 : ℝ)))
    (hκη : κ.1 < -(1 / 2 : ℝ) - η)
    (T L B : ℝ) (hT : 1 ≤ T) (hL : 1 ≤ L) (hB : 1 ≤ B) :
    ∃ h : ℝ, 0 < h ∧ ∃ K : ℝ≥0, 1 ≤ K ∧ ∃ mesh : RestartMesh T h,
      ∀ S : ℝ, 0 ≤ S → ∀ (a b : LiftData N κ) (s : Icc (0 : ℝ) S)
        (x y : C(Torus3, ℝ)) (u v : ℝ → C(Torus3, ℝ)),
        IsClassicalSolution (3 * a.constants.1 - 9 * a.constants.2)
          (shiftForcing s.val a.forcing) x u →
        IsClassicalSolution (3 * b.constants.1 - 9 * b.constants.2)
          (shiftForcing s.val b.forcing) y v →
        Statements.phi43Size κ η (T + S) a.model a.potential ≤ ENNReal.ofReal B →
        Statements.phi43Size κ η (T + S) b.model b.potential ≤ ENNReal.ofReal B →
        (∀ r ∈ Icc (0 : ℝ) T, holderBesovENorm η (u r) ≤ ENNReal.ofReal L ∧
          holderBesovENorm η (v r) ≤ ENNReal.ofReal L) →
        (⨆ r ∈ Icc (0 : ℝ) T, holderBesovENorm η (u r - v r)) ≤
          (K : ℝ≥0∞) ^ mesh.count * holderBesovENorm η (x - y) +
          restartError K mesh.count * Statements.phi43Dist κ η (T + S)
            a.model b.model a.potential b.potential := by
  obtain ⟨h, k, hh, hk, hlocal⟩ := twoDataLocalLipschitz hN hη hκη T L B hT hL hB
  let K : ℝ≥0 := ⟨k, by linarith⟩
  have hK : 1 ≤ K := hk
  obtain ⟨mesh⟩ := exists_restartMesh T h (by linarith) hh
  refine ⟨h, hh, K, hK, mesh, ?_⟩
  intro S _ a b s x y u v hu hv ha hb hstate
  have ha' := (Attachment.phi43Size_translate_le κ η T s.property.1 s.property.2
    a.model a.potential).trans ha
  have hb' := (Attachment.phi43Size_translate_le κ η T s.property.1 s.property.2
    b.model b.potential).trans hb
  have hdist := Attachment.phi43Dist_translate_le κ η T s.property.1 s.property.2
    a.model b.model a.potential b.potential
  have hstep (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t) (hth : t ≤ r + h) (htT : t ≤ T) :
      holderBesovENorm η (u t - v t) ≤ K * (holderBesovENorm η (u r - v r) +
        Statements.phi43Dist κ η (T + S) a.model b.model a.potential b.potential) := by
    have he := hlocal _ _ _ _ _ _ _ _ x y u v
      (moderateLift_time_translate a.moderate s.val)
      (moderateLift_time_translate b.moderate s.val) hu hv ha' hb' r t hr hrt hth htT
      (fun q hq => hstate q ⟨hq.1, hq.2.trans htT⟩)
    have he' : ENNReal.ofReal k = (K : ℝ≥0∞) := by
      change ENNReal.ofReal (K : ℝ) = (K : ℝ≥0∞)
      exact ENNReal.ofReal_coe_nnreal
    rw [he'] at he
    exact he.trans (mul_le_mul' le_rfl (add_le_add le_rfl hdist))
  have he := finite_mesh_estimate mesh (show (1 : ℝ≥0∞) ≤ K by exact_mod_cast hK)
    (fun t => holderBesovENorm η (u t - v t)) hstep
  refine iSup_le fun r => iSup_le fun hr => ?_
  simpa only [hu.initial, hv.initial] using he r hr

end GlobalPhi43.Flow

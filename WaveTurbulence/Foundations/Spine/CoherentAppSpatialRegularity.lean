/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppDerivative
public import WaveTurbulence.Foundations.Spine.LeafProfileHighBounds
public import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
/-! Spatial regularity of explicit coherent source approximations from the original finite input norms. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset
open scoped Topology ContDiff

theorem contDiff_coherentCouple_of_source (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (hlone : ∀ j, (univ.filter fun l : GLeaf LG.garden.tree =>
      l.1.1 = j ∧ LG.garden.IsLone l).card ≤ 1)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1))
    (A : ℕ) (H : LeafProfiles 2 P.d) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + A : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + A) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ)) :
    ContDiff ℝ A (fun k => LeafApp.coherentCouple P.δ LG H Q q q' t s k) := by
  classical
  induction A generalizing H C with
  | zero =>
    have hH := leafwiseControlled_of_high LG H C (by omega) le_rfl hc hb
    have hlim := tendstoUniformly_coherentCouple P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
      H C hH t s ht hs
    change ContDiff ℝ 0 _
    rw [contDiff_zero]
    apply hlim.continuous
    apply Filter.Eventually.frequently
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hcont := contDiff_kernelLeaves_spatial hd hL P.γ P.δ LG H C
      (fun l hl => (Complex.ofRealCLM.contDiff.comp (hc l hl)).of_le (by simp))
      (fun l hl => SNorm_mono_bound (show 0 ≤ 40 * P.d + 0 from Nat.zero_le _)
        le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl)) _ (NNReal.coe_nonneg _) (hb l hl))
      (by omega) (fun b => if b.1.1 = 0 then t else s) 0 (fun _ => 0) 0 hlone
    exact hcont.continuous
  | succ A ih =>
    have hlowC (a : ℕ) (ha' : a ≤ 40 * P.d + (A + 1)) :
        ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ a (H l.1) :=
      fun l hl => (hc l hl).of_le (by exact_mod_cast ha')
    have hlowB (a : ℕ) (ha' : a ≤ 40 * P.d + (A + 1)) :
        ∀ l ∈ inputLeaves LG.garden, SNormR a (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
      fun l hl => SNorm_mono_bound ha' le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
        _ (NNReal.coe_nonneg _) (hb l hl)
    have hH := leafwiseControlled_of_high LG H C (by omega) le_rfl hc hb
    let CD : (Fin 2 × TTree.Path) → NNReal := fun a => (P.d : NNReal) ^ (40 * P.d + 1) * C a
    have hD (l : ActualInputLeaves LG.garden) (j : Fin P.d) := singleLeafDerivative_high
      (A := 40 * P.d) hd LG.garden H C (hlowC _ (by omega)) (hlowB _ (by omega)) l j
    have hDC (l : ActualInputLeaves LG.garden) (j : Fin P.d) :
        LeafwiseControlled LG (singleLeafDerivative LG.garden H l j) CD := (hD l j).2
    have hFD (x : Mom P.d) := hasFDerivAt_coherentCouple_of_source P hsource hd hη ha hp hqq' hqp Q LG
      hsize hcoh H C hH (fun _ _ => CD) hDC (hlowC 1 (by omega)) C (hlowB 1 (by omega))
      hlone t s ht hs x
    rw [show ((A + 1 : ℕ) : ℕ∞ω) = (A : ℕ∞ω) + 1 by simp, contDiff_succ_iff_fderiv_apply]
    refine ⟨fun x => (hFD x).differentiableAt, by simp, ?_⟩
    intro v
    have he : (fun x => fderiv ℝ (fun k => LeafApp.coherentCouple P.δ LG H Q q q' t s k) x v) =
        (fun x => ∑ j : Fin P.d, (v j) • ∑ l : ActualInputLeaves LG.garden,
          LeafApp.coherentCouple P.δ LG (singleLeafDerivative LG.garden H l j) Q q q' t s x) := by
      funext x
      rw [(hFD x).fderiv, coordinateLinearMap_apply]
    rw [he]
    apply ContDiff.sum
    intro j _
    apply ContDiff.const_smul
    apply ContDiff.sum
    intro l _
    have hh := singleLeafDerivative_high (A := 40 * P.d + A) hd LG.garden H C
      (by simpa only [Nat.add_assoc] using hc) (by simpa only [Nat.add_assoc] using hb) l j
    exact ih _ (fun a => (P.d : NNReal) ^ (40 * P.d + A + 1) * C a) hh.1 hh.2

end WaveTurbulence.LGSpine

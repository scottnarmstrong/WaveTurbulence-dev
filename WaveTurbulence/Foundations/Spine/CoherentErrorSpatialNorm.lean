/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.WeightedCoherentError
public import WaveTurbulence.Foundations.Spine.CoherentAppSpatialRegularity
public import WaveTurbulence.Foundations.Spine.CoordinateDerivativeLinearity
public import WaveTurbulence.Foundations.Spine.SpatialNormFromWords
/-! Assemble the actual coherent error spatial seminorm from the corrected order-zero source gate.
The remaining budget premise is a finite numerical sum of explicit leaf costs, not a kernel estimate. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Filter Set Finset NormBridgeScratch
open scoped Topology ENNReal ContDiff

theorem coherent_error_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At { P with L := L })
    (hL : 1 ≤ P.L) (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (LG : LayeredGarden 2) (hsize : Q.size = 2 * n)
    (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (A m : ℕ) (H : LeafProfiles 2 P.d) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + 1 + A : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + 1 + A) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ))
    (hplain : LG.garden.IsPlain)
    (cost : (word : List (Fin P.d)) → LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden P.d m → (Fin 2 × TTree.Path) → NNReal)
    (hcost : ∀ word, word.length ≤ A → ∀ a c, LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hplain (leafDerivativeProfiles LG.garden H word a) c) (cost word a c))
    (E : ℝ≥0∞)
    (hbudget : ∀ word : List (Fin P.d), word.length ≤ A →
      regBound P n 1 * ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden P.d m, ENNReal.ofReal (leafSizeProduct LG (cost word a c)) ≤ E)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k => coupleLeaves P.L P.γ P.δ LG H t s k -
      LeafApp.coherentCouple P.δ LG H Q q q' t s k) ≤ E := by
  classical
  have hlone := card_lone_le_one_of_plain LG.garden hplain
  have hlowC (a : ℕ) (ha' : a ≤ 40 * P.d + 1 + A) :
      ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ a (H l.1) :=
    fun l hl => (hc l hl).of_le (by exact_mod_cast ha')
  have hlowB (a : ℕ) (ha' : a ≤ 40 * P.d + 1 + A) :
      ∀ l ∈ inputLeaves LG.garden, SNormR a (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
    fun l hl => SNorm_mono_bound ha' le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hb l hl)
  have hK := contDiff_kernelLeaves_spatial hd hL P.γ P.δ LG H C
    (fun l hl => Complex.ofRealCLM.contDiff.comp (hlowC A (by omega) l hl))
    (hlowB A (by omega)) (by omega) (fun b => if b.1.1 = 0 then t else s) 0 (fun _ => 0) 0 hlone
  have hApp := contDiff_coherentCouple_of_source P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
    hlone t s ht hs A H C (hlowC _ (by omega)) (hlowB _ (by omega))
  apply SNorm_le_of_word_enorm_bounds _ (hK.sub hApp) E
  intro word hw k
  have hK' : ContDiff ℝ word.length (fun x => coupleLeaves P.L P.γ P.δ LG H t s x) :=
    hK.of_le (by exact_mod_cast hw)
  have hA' := hApp.of_le (by exact_mod_cast hw : (word.length : ℕ∞ω) ≤ A)
  change ‖((jbr k ^ (4 * m) : ℝ) : ℂ) * wordD word
    (fun x => coupleLeaves P.L P.γ P.δ LG H t s x - LeafApp.coherentCouple P.δ LG H Q q q' t s x) k‖ₑ ≤ E
  rw [wordD_sub word _ _ hK' hA']
  exact (weighted_wordD_coherent_error_enorm_le P hsource hL hd hη ha hp hqq' hqp hn Q LG hsize hcoh
    H word C (hlowC _ (by omega)) (hlowB _ (by omega)) hlone t s ht hs hplain m
    (cost word) (hcost word hw) k).trans (hbudget word hw)

end WaveTurbulence.LGSpine

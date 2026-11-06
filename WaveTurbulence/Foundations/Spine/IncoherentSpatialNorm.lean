/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LeafwiseIncoherentPointwise
public import WaveTurbulence.Foundations.Spine.WeightedDerivativeCouple
public import WaveTurbulence.Foundations.Spine.LeafwiseKernelSpatial
public import WaveTurbulence.Foundations.Spine.SpatialNormFromWords
/-! Full high-order spatial decay for each actual incoherent regular couple. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Filter Finset NormBridgeScratch
open scoped ENNReal

theorem incoherent_SNorm_le (P : WTParams) (hsource : LeafwiseIncoherentDecayAt P)
    (hd : 1 ≤ P.d) (hL : 1 ≤ P.L) (hη : 0 ≤ P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hn : n ≤ P.N (p + 1) ^ 4)
    (Q : RegCpl) (hwf : Q.wf = true) (hsize : Q.size = 2 * n)
    (LG : LayeredGarden 2) (hQ : Q.Decodes LG.garden) (hlayer : ∀ a, LG.layer a ≤ p)
    (hq : q ≤ p) (hq' : q' ≤ p)
    (hroot : LG.layer (GNode.root LG.garden.tree 0) ≤ q)
    (hroot' : LG.layer (GNode.root LG.garden.tree 1) ≤ q')
    (hi : 1 ≤ LG.incoherency Q.links)
    (A m : ℕ) (H : LeafProfiles 2 P.d) (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ (40 * P.d + A : ℕ) (H l.1))
    (hb : ∀ l ∈ inputLeaves LG.garden, SNormR (40 * P.d + A) (40 * P.d) (H l.1) ≤
      ENNReal.ofReal (C l.1 : ℝ))
    (cost : (word : List (Fin P.d)) → LeafDerivativeChoices LG.garden word.length →
      RootWeightChoices LG.garden P.d m → (Fin 2 × TTree.Path) → NNReal)
    (hcost : ∀ word, word.length ≤ A → ∀ a c, LeafwiseControlled LG
      (rootModifiedProfiles LG.garden hQ.1.1 (leafDerivativeProfiles LG.garden H word a) c) (cost word a c))
    (E : ℝ≥0∞)
    (hbudget : ∀ word : List (Fin P.d), word.length ≤ A →
      regBound P n (LG.incoherency Q.links) * ∑ a : LeafDerivativeChoices LG.garden word.length,
        ∑ c : RootWeightChoices LG.garden P.d m, ENNReal.ofReal (leafSizeProduct LG (cost word a c)) ≤ E)
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k => coupleLeaves P.L P.γ P.δ LG H t s k) ≤ E := by
  classical
  have hlowC (a : ℕ) (ha : a ≤ 40 * P.d + A) :
      ∀ l ∈ inputLeaves LG.garden, ContDiff ℝ a (H l.1) :=
    fun l hl => (hc l hl).of_le (by exact_mod_cast ha)
  have hlowB (a : ℕ) (ha : a ≤ 40 * P.d + A) :
      ∀ l ∈ inputLeaves LG.garden, SNormR a (40 * P.d) (H l.1) ≤ ENNReal.ofReal (C l.1 : ℝ) :=
    fun l hl => SNorm_mono_bound ha le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc l hl))
      _ (NNReal.coe_nonneg _) (hb l hl)
  have hK := contDiff_kernelLeaves_spatial hd hL P.γ P.δ LG H C
    (fun l hl => Complex.ofRealCLM.contDiff.comp (hlowC A (by omega) l hl))
    (hlowB A (by omega)) (by omega) (fun b => if b.1.1 = 0 then t else s) 0 (fun _ => 0) 0
    (card_lone_le_one_of_plain LG.garden hQ.1.1)
  apply SNorm_le_of_word_enorm_bounds _ hK E
  intro word hw k
  change ‖((jbr k ^ (4 * m) : ℝ) : ℂ) * wordD word
    (fun x => coupleLeaves P.L P.γ P.δ LG H t s x) k‖ₑ ≤ E
  have he := weighted_wordD_coupleLeaves hd hL (by omega) P.γ P.δ LG hQ.1.1 H word C
    (hlowC _ (by omega)) (hlowB _ (by omega)) (cost word) (hcost word hw) t s k
  rw [he]
  apply le_trans _ (hbudget word hw)
  apply (enorm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro a _
  apply (enorm_sum_le _ _).trans
  rw [mul_sum]
  apply sum_le_sum
  intro c _
  rw [← ofReal_norm, norm_mul, norm_rootChoiceSign, one_mul, ofReal_norm]
  exact enorm_leafwise_incoherent_le P hsource hd hL hη hp hn Q hwf hsize LG hQ hlayer hq hq'
    hroot hroot' hi _ (cost word a c) (hcost word hw a c) t s ht hs k

end WaveTurbulence.LGSpine

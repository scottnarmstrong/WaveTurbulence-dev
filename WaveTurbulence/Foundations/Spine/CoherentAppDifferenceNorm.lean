/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.CoherentAppMarkedNorm
public import WaveTurbulence.Foundations.Spine.CoherentAppRemainderExpansion
public import WaveTurbulence.Foundations.Spine.LeafProfileAddControl
public import WaveTurbulence.Foundations.Spine.SelectedLeafSmallness
/-! A single coherent app's phi+R comparison in the full spatial seminorm. -/
public section
set_option autoImplicit false
namespace WaveTurbulence.LGSpine
open WaveTurbulence.Induct
open Set Finset
open scoped ENNReal

 theorem coherent_app_difference_SNorm_le (P : WTParams)
    (hsource : ∀ L ≥ P.L, LeafwiseCoherentApproximationOrder0At {P with L := L})
    (hC₁ : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hηmax : P.η ≤ 1 / 2)
    (hd : 1 ≤ P.d) (hη : 0 ≤ P.η) (ha : 0 < P.gamma1 - Real.sqrt P.η)
    {p n q q' : ℕ} (hp : p < P.D) (hqq' : q' ≤ q) (hqp : q ≤ p)
    (hn : n ≤ P.N (p + 1) ^ 4) (Q : RegCpl) (LG : LayeredGarden 2)
    (hsize : Q.size = 2 * n) (hcoh : IsCoherentCoupleAt p q q' Q LG)
    (A m : ℕ) (H₀ H₁ : LeafProfiles 2 P.d) (C₁ ε C₂ : NNReal)
    (hbase : (C₁ : ℝ) = P.C₁) (hε : 0 < (ε : ℝ)) (hεC : ε ≤ C₁) (hC₂ : (1 : ℝ) ≤ C₂)
    (h₀ : LeafwiseControlled LG H₀ (fun _ => C₁)) (h₁ : LeafwiseControlled LG H₁ (fun _ => ε))
    (C : (Fin 2 × TTree.Path) → NNReal)
    (hc : ∀ S ∈ (inputLeaves LG.garden).powerset.erase ∅, ∀ l ∈ inputLeaves LG.garden,
      ContDiff ℝ (40 * P.d + 1 + A : ℕ) (selectLeafProfiles LG.garden S H₀ H₁ l.1))
    (hb : ∀ S ∈ (inputLeaves LG.garden).powerset.erase ∅, ∀ l ∈ inputLeaves LG.garden,
      SNormR (40 * P.d + 1 + A) (40 * P.d) (selectLeafProfiles LG.garden S H₀ H₁ l.1) ≤
        ENNReal.ofReal (C l.1 : ℝ))
    (hplain : LG.garden.IsPlain) (horder : LG.garden.order = 2 * n)
    (D : ℝ) (hD : 0 ≤ D)
    (hchoice : ((inputLeaves LG.garden).card + 1 : ℝ) ^ A *
      (Fintype.card (RootWeightChoices LG.garden P.d m) : ℝ) ≤ D * 8 ^ n)
    (hcost : ∀ S ∈ (inputLeaves LG.garden).powerset.erase ∅,
      ∀ word : List (Fin P.d), word.length ≤ A →
      ∀ (a : LeafDerivativeChoices LG.garden word.length) (c : RootWeightChoices LG.garden P.d m),
        LeafwiseControlled LG
          (rootModifiedProfiles LG.garden hplain
            (leafDerivativeProfiles LG.garden (selectLeafProfiles LG.garden S H₀ H₁) word a) c)
          (relativeLeafModificationCosts LG.garden (combinedModifiedInputs LG.garden hplain word a c)
            (selectLeafBounds LG.garden S (fun _ => C₁) (fun _ => ε)) C₂))
    (t s : ℝ) (ht : t ∈ Icc (q : ℝ) (q + 1)) (hs : s ∈ Icc (q' : ℝ) (q' + 1)) :
    SNorm A (4 * m) (fun k =>
      LeafApp.coherentCouple P.δ LG (fun a x => H₀ a x + H₁ a x) Q q q' t s k -
        LeafApp.coherentCouple P.δ LG H₀ Q q q' t s k) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (inputLeaves LG.garden).card *
        (((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
          ((ε : ℝ) * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A)))))) := by
  classical
  let E : ℝ := ((2 : ℝ) ^ n * P.δ ^ n * (P.C₁ * P.C₁ ^ n) ^ 2) *
    ((ε : ℝ) * (D * 8 ^ n * (P.C₁ ^ (2 * n + 1) * (C₂ : ℝ) ^ (4 * m + A))))
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have hbaseR : 1 ≤ (C₁ : ℝ) := by simpa only [hbase] using hC₁
  have hbaseNN : 1 ≤ C₁ := by exact_mod_cast hbaseR
  have hExpansion : (fun k => LeafApp.coherentCouple P.δ LG (fun a x => H₀ a x + H₁ a x) Q q q' t s k -
      LeafApp.coherentCouple P.δ LG H₀ Q q q' t s k) =
      fun k => ∑ S ∈ (inputLeaves LG.garden).powerset.erase ∅,
        LeafApp.coherentCouple P.δ LG (selectLeafProfiles LG.garden S H₀ H₁) Q q q' t s k := by
    funext k
    exact coherentCouple_sub_eq_sum_nonempty_subsets_of_source P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh
      H₀ H₁ (fun _ => C₁) (fun _ => ε) (fun _ => C₁ + ε) h₀ h₁
      (LeafwiseControlled.add hd LG H₀ H₁ _ _ h₀ h₁) t s ht hs k
  rw [hExpansion]
  have hlone := card_lone_le_one_of_plain LG.garden hplain
  have hreg (S) (hS : S ∈ (inputLeaves LG.garden).powerset.erase ∅) :
      ContDiff ℝ A (fun k => LeafApp.coherentCouple P.δ LG (selectLeafProfiles LG.garden S H₀ H₁) Q q q' t s k) := by
    apply contDiff_coherentCouple_of_source P hsource hd hη ha hp hqq' hqp Q LG hsize hcoh hlone t s ht hs A _ C
    · intro l hl
      exact (hc S hS l hl).of_le (by exact_mod_cast (show 40 * P.d + A ≤ 40 * P.d + 1 + A by omega))
    · intro l hl
      exact SNorm_mono_bound (by omega) le_rfl _ (Complex.ofRealCLM.contDiff.comp (hc S hS l hl))
        _ (NNReal.coe_nonneg _) (hb S hS l hl)
  have hbound (S) (hS : S ∈ (inputLeaves LG.garden).powerset.erase ∅) :
      SNorm A (4 * m) (fun k => LeafApp.coherentCouple P.δ LG (selectLeafProfiles LG.garden S H₀ H₁) Q q q' t s k) ≤
        ENNReal.ofReal E := by
    have hSI : S ⊆ inputLeaves LG.garden := mem_powerset.mp (mem_erase.mp hS).2
    have hSne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr (mem_erase.mp hS).1
    have hBpos (l) (hl : l ∈ inputLeaves LG.garden) :
        0 < (selectLeafBounds LG.garden S (fun _ => C₁) (fun _ => ε) l.1 : ℝ) := by
      rw [selectLeafBounds_apply]
      split_ifs
      · exact hε
      · exact zero_lt_one.trans_le hbaseR
    have hprod := leafSizeProduct_selected_constant_le LG S hSI hSne C₁ ε hbaseNN hεC
    rw [hbase] at hprod
    exact coherent_app_marked_SNorm_le P hsource hC₁ hδ hηmax hd hη ha hp hqq' hqp hn Q LG hsize hcoh A m
      _ C (hc S hS) (hb S hS) hplain horder _ C₂ hC₂ hBpos ε D hε.le hprod hchoice (hcost S hS) t s ht hs
  apply (SNorm_finset_sum_bound _ _ (fun _ => E) hreg (fun _ _ => hE) hbound).trans
  apply ENNReal.ofReal_le_ofReal
  simp only [sum_const, nsmul_eq_mul]
  apply mul_le_mul_of_nonneg_right _ hE
  have hcard := (Finset.card_erase_le (s := (inputLeaves LG.garden).powerset) (a := (∅ : Finset (GLeaf LG.garden.tree))))
  rw [Finset.card_powerset] at hcard
  exact_mod_cast hcard

end WaveTurbulence.LGSpine

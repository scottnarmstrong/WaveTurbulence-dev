/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreePairRegularization
public import WaveTurbulence.Foundations.RegAsymp.TreeAtRebase

/-! # The actual source tree coefficient has its unconditional regularized chain limit -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set Filter ClassJR Cancel MainCoef Links
open scoped Topology

/-- The original adjacent-pair limiting integral at the rebased physical times. -/
def treeRegularizedLeading (Z : Finset Cancel.Addr) (X : RegChain) (ζ : ℤˣ) (t s : ℝ) : ℂ :=
  chainL (kD (fun j => decide (chainSig (treePairData X ζ) j ∈ Z))
    (fun j u v => treePairLimit Z X ζ j (clamp01 (u+s)) (clamp01 (v+s))))
    (chainCode X) 0 (t-s) (fun _ => 1)

/-- Tree J4 before classifying the finite limiting coefficient. The only source premise
is well-formedness; the constituent couple regularizations are proved landed inputs. -/
theorem actual_tree_regularized_limit (Z : Finset Cancel.Addr) (X : RegChain)
    (hwf : X.wf = true) (ζ : ℤˣ) {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    Tendsto (fun ε => RI ε nodeSgn Z (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)))
      (chainAtilde X ζ) t s) (𝓝[>] (0:ℝ)) (𝓝 (treeRegularizedLeading Z X ζ t s)) := by
  let σ := chainSig (treePairData X ζ)
  let ε := fun j => zetaA (σ j)
  let F := fun j α u v => treePairCoefficient X ζ j α (clamp01 (u+s)) (clamp01 (v+s))
  have hag : ChainAgr (treePairData X ζ) X ζ (rootT ζ) 0 := fun k _ => by rw [zero_add]; rfl
  have hdisj : ChainDisjF σ (treePairVariables X ζ) (chainCode X) 0 :=
    chainDisjF_of_nodup _ X ζ (rootT ζ) 0 hag (tree_chosen_nodup_at_root X ζ)
  have hNice (j : ℕ) : NiceCoef (treePairVariables X ζ j) (F j) :=
    (tree_shiftedRegCoef (regCoef_treePair Z X hwf ζ j) s).nice
  obtain ⟨BF,_,hBF⟩ := exists_treePairCoefficient_bound X hwf ζ
  have hB : ∀ j α, ∀ u ∈ Icc (0:ℝ) 1, ∀ v ∈ Icc (0:ℝ) 1, ‖F j α u v‖ ≤ BF :=
    fun j α u _ v _ => hBF j α _ (clamp01_mem _) _ (clamp01_mem _)
  have hR (j : ℕ) (_ : j < (chainCode X).size) :
      RegLim2 (fun η u v => RI η zetaA Z (treePairVariables X ζ j) (F j) u v)
        (fun u v => treePairLimit Z X ζ j (clamp01 (u+s)) (clamp01 (v+s))) :=
    (tree_shiftedRegCoef (regCoef_treePair Z X hwf ζ j) s).lim
  have hReg := tree_chain_const_regularized zetaA_pm Z (σ := σ) (ε := ε)
    (fun _ => rfl) hNice hB (chainCode X) hR hdisj
  have hVars : chainVarsF σ (treePairVariables X ζ) (chainCode X) 0 =
      ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) := by
    rw [linksAt_toJRc]
    exact chainVarsF_eq _ X ζ (rootT ζ) 0 hag
  have hsign : zetaA = nodeSgn := funext zetaA_eq
  have hEq (η : ℝ) : RI η nodeSgn Z
      (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))) (chainAtilde X ζ) t s =
      RI η zetaA Z (chainVarsF σ (treePairVariables X ζ) (chainCode X) 0)
        (fun α u _ => chainT σ ε (chainCode X) 0 F α u (fun _ => 1)) (t-s) 0 := by
    unfold RI
    rw [hVars,← hsign]
    apply congrArg (fun f : (Cancel.Addr → ℝ) → ℂ =>
      mint (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))) f 0)
    funext α
    congr 1
    unfold chainAtilde
    rw [chainT_toCancel]
    exact tree_chainT_rebase_clamp _ _ _ _ _ _ hs hst ht
  have hts : t-s ∈ Icc (0:ℝ) 1 := ⟨by linarith,by linarith⟩
  exact (hReg.lim.lim (t-s) hts 0 ⟨le_rfl,zero_le_one⟩).congr'
    (Eventually.of_forall (fun η => (hEq η).symm))

end WaveTurbulence.RegAsymp

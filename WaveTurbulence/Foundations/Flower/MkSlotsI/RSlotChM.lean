/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsI.RSlotCplM

/-! # B3s-HELPER7 WP6 (R-slot, part 5): the general kernel of an outer chain slot is common to the run class

For a `G_sb` branch `c` and a member `y` of the run class of `a`, the general slot kernel of `y` at `Φ_y.iota (.inr c)`
is the representative's `genSlotKer` at `Φ_a.iota (.inr c)` (**`member_genSlot_inr`**): both are `kerT` of the common
native chain (β's `memShape_nativeChain`) with node data read through `RSlotCh` (tree index, root test, weight layer,
lone path — δ's `memShape_chain_eq` —, core capped-flower-parent and stem tests, chain-top depth) and the common clock
pin (`member_clock`). -/

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.LFTwist
open WaveTurbulence.Flower.MkDefs WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden
open WaveTurbulence.RedSplice WaveTurbulence.VineB WaveTurbulence.VineC WaveTurbulence.Flower.MkUnits
open WaveTurbulence.Represents WaveTurbulence.VineEstS4 WaveTurbulence.Flower.Stage1W WaveTurbulence.VineAlign
  WaveTurbulence.Stage1 WaveTurbulence.Twist WaveTurbulence.Flower.Stage1WVine
open WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlots.IntCore

namespace WaveTurbulence.Flower.MkSlotsI

/-- `genT` reads the top depth only when the core is on the capped stem. -/
theorem genT_congr {w : ℕ} (N : LayeredGarden 1) (ri : Fin w) (lp : Path) (sb sb' : Prop) (rd rd' : ℕ)
    (ex : Fin w → Prop) (L : ℝ) (σ kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ) (hs : sb ↔ sb') (hrd : sb → rd = rd')
    (a : GNode N.garden.tree) (v : ℝ) :
    genT N ri lp sb rd ex L σ kSel Rs a v = genT N ri lp sb' rd' ex L σ kSel Rs a v := by
  by_cases h : sb
  · rw [hrd h, propext hs]
  · have h' : ¬ sb' := fun h' => h (hs.mpr h')
    unfold genT genD
    split_ifs with h1 h2 h3 h4 <;> first | rfl | exact absurd h3.2 h | exact absurd h4.2 h' | skip
    all_goals first | exact absurd ‹_ ∧ sb›.2 h | exact absurd ‹_ ∧ sb'›.2 h' | rfl

section Class

variable {R p : ℕ} {kind : Bool} (a : PrescribedPrimeGarden (2 * R)) (mk : Stage1Mk.MarkFn (2 * R))
  (y : UState (2 * R) (unitsSplit (sourceAssemblyMk a mk))) (hy : y ∈ sourceClass a p kind mk)
  (hG : (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.IsPlain)
  (J : Finset (Fin (2 * R)))
  (hGeoA : CapGeo (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J p)
  (hGeoY : CapGeo (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J p)
  (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hrepUP : ∀ j, ∀ b ∈ (unitBlkMk (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) j).atoms,
    fixCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J pat t s
      (a.prime.data.coreBranch a.prime.prime.1 b) = none)

include hy hG hGeoA hGeoY hrepUP in
/-- **The general kernel of an outer chain slot is common to the run class.** -/
theorem member_genSlot_inr {d : ℕ} (L γ δ : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d))
    (hstem : Stage1MKGate.StemDep σ kSel → Stage1MKGate.CleanPt J a)
    (hex : Stage1MKGate.StemDep σ kSel → ∀ j,
      (selCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J kSel j).isSome =
        (selCap (layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)) J kSel
          j).isSome)
    (c : GBranch (stSt a.prime.skeleton a.totalSigma (mk a.prime)).G.tree) (ts : Fin 2 → ℝ) (k : Mom d) :
    MkSlotsB.slotFnGWFRL y.1.data y.1.plain L γ δ
        (anchProfiles J (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) h L
          roots)
        (chainW y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) L γ δ p s J Rf dag)
        (genΘs y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs)
        (stateLayer y.1) (stateLayer_isLayering y.1)
        (fixCap (layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1)) J pat t s)
        ((memShape a mk y hy).iota y.1.plain hG (.inr c)) ts k =
      genSlotKer L γ δ p a J pat t s σ kSel Rs h roots Rf dag
        ((stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime)).iota a.prime.prime.1 hG
          (.inr c)) ts k := by
  have hcapA : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hGeoA.cap_leaf
  have hcapY : ∀ j ∈ J, (y.1.data.garden y.1.plain).tree j = TTree.leaf := hGeoY.cap_leaf
  have hrepU := MkSlotsB.hrepU_of_pat a mk J pat t s hrepUP
  set Φy := memShape a mk y hy with hΦy
  set Φa := stShape (Mole.garden_isMolecule a.prime.skeleton) a.totalSigma (mk a.prime) with hΦa
  set LGy := layeredReconstruction y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) with hLGy
  set LGa := layeredReconstruction a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
    with hLGa
  have hN := MkSlotsB.memShape_nativeChain a mk y hy hG c
  have hatt : attachedNode y.1.data y.1.plain (Φy.br c).toNode = attachedNode y.1.data y.1.plain (Φy.node c.toNode) ∧
      attachedNode a.prime.data a.prime.prime.1 (Φa.br c).toNode =
        attachedNode a.prime.data a.prime.prime.1 (Φa.node c.toNode) := by
    rw [Φy.br_node, Φa.br_node]
    exact ⟨rfl, rfl⟩
  have hri : chRI y.1.data (Φy.br c) = chRI a.prime.data (Φa.br c) := by
    have e1 := attached_tree Φy y.1.data y.1.plain c.toNode
    have e2 := attached_tree Φa a.prime.data a.prime.prime.1 c.toNode
    rw [← hatt.1] at e1
    rw [← hatt.2] at e2
    exact e1.trans e2.symm
  have hrr : chRR y.1.data (Φy.br c) ↔ chRR a.prime.data (Φa.br c) := by
    have e1 := attached_root_iff Φy y.1.data y.1.plain c.toNode
    have e2 := attached_root_iff Φa a.prime.data a.prime.prime.1 c.toNode
    rw [← hatt.1] at e1
    rw [← hatt.2] at e2
    exact e1.trans e2.symm
  have hrc : chRC y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) =
      chRC a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (Φa.br c) := by
    unfold chRC
    rw [hatt.1, hatt.2]
    exact member_rcOf a mk y hy hG J hcapA hcapY hrepU c.toNode
  have hqw : chQW y.1.data y.1.plain (stateLayer y.1) (Φy.br c) p =
      chQW a.prime.data a.prime.prime.1 (sourceLayer a) (Φa.br c) p :=
    memShape_wLay a mk y hy hG (.inr c) 0 p
  have hlp : (y.1.data.tree (Φy.br c)).lonePath = (a.prime.data.tree (Φa.br c)).lonePath := by
    rw [MkSlotsS.memShape_chain_eq a mk y hy hG c]
  have hcb := member_cfp_iff a mk y hy hG J hcapA hcapY hrepU c
  have hsb := member_coreStem a mk y hy J hcapA hcapY c
  refine (slotFnGWFRL_inr_eq y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J L σ kSel Rs γ δ _ _ _
    (Φy.br c) ts k).trans ((kerT_transport L γ δ hN ?_ ?_ ?_ ?_ ?_ ts k).trans (slotFnGWFRL_inr_eq a.prime.data
    a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J L σ kSel Rs γ δ _ _ _ (Φa.br c) ts k).symm)
  · -- profiles
    intro x h₁ h₂
    exact (anch_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY h L roots
      ⟨x, h₁⟩).trans ((node_fun_congr2 (fun N r b => h (N.layer b) r r) hN hri x h₁ h₂).trans
        (anch_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (Φa.br c) hcapA h L roots
          ⟨x, h₂⟩).symm)
  · -- node weights
    intro x h₁ h₂
    funext v
    exact (chainW_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY L γ δ p s Rf
      dag ⟨x, h₁⟩ v).trans
      ((congrFun (node_fun_congr2 (fun N (r : Fin (2 * R) × ℕ) b =>
        fwI p (fun j => frontierG (Rf j)) N (fun _ => r.1) (fun _ => r.2) b) hN
        (r₁ := (chRI y.1.data (Φy.br c), chQW y.1.data y.1.plain (stateLayer y.1) (Φy.br c) p))
        (r₂ := (chRI a.prime.data (Φa.br c), chQW a.prime.data a.prime.prime.1 (sourceLayer a) (Φa.br c) p))
        (by rw [hri, hqw]) x h₁ h₂) v).trans
      (chainW_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J (Φa.br c) hcapA L γ δ p s
        Rf dag ⟨x, h₂⟩ v).symm)
  · -- per-node factors
    intro x h₁ h₂
    funext v
    by_cases hsd : Stage1MKGate.StemDep σ kSel
    · have hc := hstem hsd
      have hexf : (fun j => (selCap LGy J kSel j).isSome = true) = (fun j => (selCap LGa J kSel j).isSome = true) :=
        funext fun j => by rw [hex hsd j]
      refine (genNode_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY L σ kSel Rs
        hGeoY.one_flower ⟨x, h₁⟩ v).trans ?_
      refine Eq.trans ?_ (genNode_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
        (Φa.br c) hcapA L σ kSel Rs hGeoA.one_flower ⟨x, h₂⟩ v).symm
      rw [hri, hexf, hlp]
      refine (genT_congr _ _ _ _ _ _ (chRD a.prime.data (Φa.br c)) _ L σ kSel Rs hsb ?_ ⟨x, h₁⟩ v).trans ?_
      · intro hs
        exact member_chainTop_depth a mk y hy hG J hcapA hcapY hc c (hsb.mp hs)
      · exact node_fun_congr2 (fun N (r : Unit) b => genT N (chRI a.prime.data (Φa.br c))
          (a.prime.data.tree (Φa.br c)).lonePath
          (OnCapStem LGa J (a.prime.data.coreBranch a.prime.prime.1 (Φa.br c)).toNode)
          (chRD a.prime.data (Φa.br c)) (fun j => (selCap LGa J kSel j).isSome = true) L σ kSel Rs b v)
          hN (rfl : () = ()) x h₁ h₂
    · obtain ⟨hσ, hk⟩ := stemDep_none hsd
      subst hσ hk
      exact (genNode_none _ _ _ _ J L Rs _ v).trans (genNode_none _ _ _ _ J L Rs _ v).symm
  · -- pins
    intro x h₁ h₂
    show fixCap LGy J pat t s (MkSlotsB.nativeBr y.1.data y.1.plain (.inr (Φy.br c)) ⟨x, h₁⟩) =
      fixCap LGa J pat t s (MkSlotsB.nativeBr a.prime.data a.prime.prime.1 (.inr (Φa.br c)) ⟨x, h₂⟩)
    refine MkSlotsB.fixCap_congr J pat t s _ _ ?_ ?_ ?_ ?_ ?_
    · show chRI y.1.data (Φy.br c) = chRI a.prime.data (Φa.br c)
      exact hri
    · exact iff_of_false (cfp_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c)
        hcapY ⟨x, h₁⟩) (cfp_nativeBr_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J
        (Φa.br c) hcapA ⟨x, h₂⟩)
    · exact (root_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) (Φy.br c) ⟨x, h₁⟩).trans
        ((and_congr Iff.rfl hrr).trans
          (root_nativeBr_ch a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (Φa.br c)
            ⟨x, h₂⟩).symm)
    · refine (par_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY
        ⟨x, h₁⟩).trans (Iff.trans ?_ (par_nativeBr_ch a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) J (Φa.br c) hcapA ⟨x, h₂⟩).symm)
      rw [hlp]
      exact and_congr Iff.rfl hcb
    · intro i
      refine (ch_nativeBr_ch y.1.data y.1.plain (stateLayer y.1) (stateLayer_isLayering y.1) J (Φy.br c) hcapY
        ⟨x, h₁⟩ i).trans (Iff.trans ?_ (ch_nativeBr_ch a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) J (Φa.br c) hcapA ⟨x, h₂⟩ i).symm)
      rw [hrc]
  · -- the clock pin status
    show (fixCap LGy J pat t s (y.1.data.coreBranch y.1.plain (Φy.br c)) = none) =
      (fixCap LGa J pat t s (a.prime.data.coreBranch a.prime.prime.1 (Φa.br c)) = none)
    rw [member_clock a mk y hy hG J hcapA hcapY pat t s hrepUP c]

end Class

end WaveTurbulence.Flower.MkSlotsI

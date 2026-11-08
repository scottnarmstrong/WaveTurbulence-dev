/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcFam
public import WaveTurbulence.Foundations.Flower.ProtWhole.ContJ
public import WaveTurbulence.Foundations.Flower.ProtPin.Pieces

/-! # PROT-CHAIN (`Pc`): the common data of a stem chain slot of a prescribed point

For a chain slot `.inr β` of the reconstruction of a prescribed point `a` (capped geometry), whose chain is not `nil`
and whose core is on the capped stem:

* `pc_size`: the chain has size `2n`, `1 ≤ n ≤ N^4`;
* `pc_shape`, `pc_amb`: the native chain is a D3 protected object (`ProtShape`, `ProtAmbient`);
* `pc_pres`, `pc_LC`: the frontier star weights are presented, the leaf profiles controlled by `b`;
* **`pc_ker`**: the general slot kernel is the protected kernel of the native chain with the pins of `objCfg`, the
  multiplier `starWeight · pcΘ` (no dagger on a chain);
* `pc_cont`: such a kernel is jointly continuous in the two clocks;
* `pc_selNative_empty`, `pc_Fsel_empty`: no selected vertex in a tree with a non-plain pattern;
* `pc_hasProtNative`: a protected chain slot carries a protected native node;
* `timeBoxGt_eq_pcBox`, `rootBox_eq_pcBox`, `pc_rpow_47`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsI
  WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo WaveTurbulence.Flower.Stage1W
  WaveTurbulence.Flower.Stage1WNoVine

namespace WaveTurbulence.Flower.MkSlotsO

theorem timeBoxGt_eq_pcBox (p q' : ℝ) : timeBoxGt p q' = pcBox p (p + 1) q' := by
  ext ts
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩
    exact ⟨h1, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩

theorem rootBox_eq_pcBox {p q' t : ℝ} (hpt : p ≤ t) :
    {ts : Fin 2 → ℝ | ts ∈ timeBoxGt p q' ∧ t ≤ ts 0} = pcBox t (p + 1) q' := by
  ext ts
  constructor
  · rintro ⟨⟨⟨⟨-, h2⟩, ⟨h3, h4⟩⟩, h5⟩, h6⟩
    exact ⟨h6, h2, h3, h4, h5⟩
  · rintro ⟨h1, h2, h3, h4, h5⟩
    exact ⟨⟨⟨⟨hpt.trans h1, h2⟩, ⟨h3, h4⟩⟩, h5⟩, h1⟩

section Slot

variable {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (β : GBranch a.prime.skeleton.tree)

/-- The native chain of `β`. -/
abbrev pcN : LayeredGarden 1 :=
  nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β

/-- The layer of the core of `β` (the lone node of the native chain). -/
abbrev pcq : ℕ := sourceLayer a (a.prime.data.coreBranch a.prime.prime.1 β).toNode

theorem pc_size {N : ℕ} (hsz : a.prime.data.size ≤ N) (hne : a.prime.data.tree β ≠ .nil) :
    ∃ n : ℕ, (a.prime.data.tree β).size = 2 * n ∧ 1 ≤ n ∧ n ≤ N := by
  obtain ⟨r, hr⟩ := chain_size_even (a.prime.data.tree β)
  have h2 : 2 ≤ (a.prime.data.tree β).size := by
    cases hX : a.prime.data.tree β with
    | nil => exact absurd hX hne
    | pair m Qr Qg inner rest => simp [RegChain.size]
  have hle : (a.prime.data.tree β).size ≤ a.prime.data.size := slotSize_le a.prime.data (.inr β)
  exact ⟨r, by omega, by omega, by omega⟩

variable {J : Finset (Fin (2 * R))} {p : ℕ}

theorem pc_shape (hG : CapGeo (recLG a) J p) (hne : a.prime.data.tree β ≠ .nil)
    (hcs : OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode) :
    ProtShape p (a.prime.data.tree β) (pcN a β) := by
  rw [pcN, pc_LG_eq]
  exact protShape_objTree hG (pc_stemChain _ _ _ _ β J hne hcs)

theorem pc_amb (hcan : IsCanonGC (p + 1) (recLG a)) : ProtAmbient p (a.prime.data.tree β) (pcN a β) := by
  rw [pcN, pc_LG_eq]
  refine ProtPin.protAmbient_objTree hcan (pcE _ _ _ _ β) ?_
  show nodeSign a.prime.skeleton.sig (inflatedPosition a.prime.skeleton a.prime.data.tree β.toNode) = _
  rw [inflatedPosition_sign]
  rfl

theorem pc_lone_layer (z : GNode (pcN a β).garden.tree) (hz : z.1.2 = (a.prime.data.tree β).lonePath) :
    (pcN a β).layer z = pcq a β := by
  have hz' : z = (chainLoneLeaf (a.prime.data.tree β) (nodeSign a.prime.skeleton.sig β.1)).toNode :=
    Subtype.ext (Prod.ext (Subsingleton.elim _ _) hz)
  rw [hz']
  show sourceLayer a (chainContextNode a.prime.data a.prime.prime.1 β _) = _
  rw [chainContextNode_lone]

theorem pc_pres (d : ℕ) (Rf : Fin (2 * R) → Option ℝ) (hRf : ∀ j r, Rf j = some r → 1 ≤ r) :
    ∀ z ∈ pc_frontS a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β p,
      IncTop.StarPresented (30 * d)
        (pc_ω (d := d) a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β Rf z)
        (frontierConst d) :=
  fun z _ => IncTop.topStar_presented _ (fun _ => gPresented_frontierG d _ (hRf _)) z

/-- The leaf profiles of the native chain. -/
abbrev pcHp {d : ℕ} (L : ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ)) :
    LeafProfiles 1 d :=
  capProfiles (pcN a β) (fun z =>
    anchProfiles J (recLG a) h L roots (chainContextNode a.prime.data a.prime.prime.1 β z).1)

theorem pc_LC {d : ℕ} (hG : CapGeo (recLG a) J p) (L : ℝ) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ)
    (roots : Fin (2 * R) → (Fin d → ℤ)) {b : ℝ} (hb1 : 1 ≤ b)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * d) (40 * d) (h q j j') ≤ ENNReal.ofReal b) :
    LeafwiseControlled (pcN a β) (pcHp a β (J := J) L h roots) (fun _ => b.toNNReal) := by
  intro ℓ _
  have e : pcHp a β (J := J) L h roots ℓ.1 =
      anchProfiles J (recLG a) h L roots (chainContextNode a.prime.data a.prime.prime.1 β ℓ.toNode).1 :=
    capProfiles_leaf _ _ ℓ
  rw [e, pc_anch_ch _ _ _ _ J β hG.cap_leaf h L roots ℓ.toNode]
  show SNormR (40 * d) (40 * d) _ ≤ ENNReal.ofReal (b.toNNReal : ℝ)
  rw [Real.coe_toNNReal b (by linarith)]
  exact hb _ (hG.layer_le _) _ _

/-- **The general slot kernel of a stem chain slot** (pins of `objCfg`, multiplier `starWeight · pcΘ`). -/
theorem pc_ker {d : ℕ} (hG : CapGeo (recLG a) J p) (hne : a.prime.data.tree β ≠ .nil)
    (hcs : OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode)
    (L γ δ : ℝ) (pat : Fin (2 * R) → FixPat) (t s : ℝ) (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ)
    (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom d → ℝ) (roots : Fin (2 * R) → (Fin d → ℤ))
    (Rf : Fin (2 * R) → Option ℝ) (dag : Option (Fin (2 * R) → Fin 3 → Mom d)) (ts : Fin 2 → ℝ) (k : Mom d) :
    genSlotKer L γ δ p a J pat t s σ kSel Rs h roots Rf dag (.inr β) ts k =
      kernelProt L γ δ (pcN a β) (pcHp a β (J := J) L h roots)
        (fun K => IncTop.starWeight (pc_frontS a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            β p) (pc_ω a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β Rf) K *
          pcΘ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β J L σ kSel Rs K)
        (fun _ => ts 0) (ts 1)
        ((objCfg (recLG a) J pat (a.prime.data.tree β) (pcu a.prime.data β)).fix (a.prime.data.tree β) s t 0)
        k (fun _ => 0) 0 := by
  set D := a.prime.data
  set hS := a.prime.prime.1
  have hSt := pc_stemChain D hS (sourceLayer a) (sourceLayer_isLayering a) β J hne hcs
  unfold genSlotKer
  rw [pc_slotFn_eq_kernelProt D hS (sourceLayer a) (sourceLayer_isLayering a) β L γ δ _ _ _ _
    (pcΘ D hS (sourceLayer a) (sourceLayer_isLayering a) β J L σ kSel Rs) ts k (fun κ => rfl)
    (pc_hlp D hS (sourceLayer a) (sourceLayer_isLayering a) β J hG hne hSt pat t s)]
  have hfix : fixNative D hS (fixCap (recLG a) J pat t s) (.inr β) =
      (objCfg (recLG a) J pat (D.tree β) (pcu D β)).fix (D.tree β) s t 0 :=
    funext fun b => pc_fixN D hS (sourceLayer a) (sourceLayer_isLayering a) β J hG hSt pat t s 0 b
  rw [hfix]
  congr 1
  funext K
  congr 1
  refine (Finset.prod_congr rfl fun z _ => ?_).trans
    (pc_fw_prod D hS (sourceLayer a) (sourceLayer_isLayering a) β p Rf K)
  exact IntGeo.chainW_eq_fwNode D hS (sourceLayer a) (sourceLayer_isLayering a) J hG.cap_leaf L γ δ p s Rf dag _ _
    (IntGeo.not_inCapNative_of_slot D hS J (.inr β) (fun q h => by cases h) z)

end Slot

end WaveTurbulence.Flower.MkSlotsO

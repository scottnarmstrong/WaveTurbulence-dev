/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcSet

/-! # PROT-CHAIN (`Pc`): the pinned stem chain slots, from D3 (`root`, `term`)

A stem chain slot `.inr β` whose native chain is pinned (`objCfg = root`: a `dRoot` skeleton root chain with the
garden root pinned at `t`; `objCfg = term`: F-H3-3, a `dParent` chain whose lone parent is pinned at `s` below the core
capped flower parent) lies in a tree with a non-plain pattern, so it carries no selection: its per-slot factor is σ's
filters (`F`) and the (empty) shells (`Fu`), its node weight the frontier star weight (no dagger on a chain). D3's
`ProtBoundAt` at `θ = η` bounds the slot kernel on `cfg.box` over the consumed lattice ball at `L^{31d+6}`, which the
slot mass absorbs (`L^{31d+6} ≤ L^{2(47d+5)}`, `HasProtNative`).

* `pcRad_ge`, `pc_Fsel_empty`, `pc_selNative_empty` (no selection in a non-plain tree);
* **`pc_d3_fam`**: the slot family at `θ = η`. -/

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

theorem pcRad_ge {w : ℕ} {L : ℝ} (hL : 0 ≤ L) (σ : Fin w → Option ℕ) (j : Fin w) : L ≤ pcRad L σ j := by
  unfold pcRad
  cases σ j with
  | none => exact le_rfl
  | some i => exact le_mul_of_one_le_left hL (one_le_pow₀ (by norm_num))

section NoSel

variable {w : ℕ} {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain) (layer : GNode (D.forest hS) → ℕ)
  (hLayer : IsLayering (D.garden hS) layer) (β : GBranch S.tree) (J : Finset (Fin w)) (pat : Fin w → FixPat)
  (kSel : Fin w → Option ℕ) (hkSel : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
  (hnp : pat (pcj D β) ≠ FixPat.plain)
include hkSel hnp

theorem pc_Fsel_empty : pcFsel D hS layer hLayer β J kSel = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun b _ hb => hnp ?_
  exact hkSel _ (MkSlotsS.selCap_spec (MkSlotsS.selCap_of_mem_selSetCap hb.2)).1

theorem pc_selNative_empty : MkSlotsS.selNative D hS layer hLayer J kSel (.inr β) = ∅ := by
  refine Finset.filter_eq_empty_iff.2 fun v hv ⟨y, _, hy⟩ => hnp ?_
  have h1 : v.1.1 = pcj D β := by
    have h := congrArg Prod.fst hy
    exact h
  have h2 := MkSlotsS.selCap_spec (MkSlotsS.selCap_of_mem_selSetCap hv)
  rw [h1] at h2
  exact hkSel _ h2.1

end NoSel

theorem pc_valid {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (β : GBranch a.prime.skeleton.tree)
    {J : Finset (Fin (2 * R))} {pat : Fin (2 * R) → FixPat}
    (hpat : CapPatValid (recLG a) J pat p) (hne : a.prime.data.tree β ≠ .nil)
    (hcs : OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode) :
    (objCfg (recLG a) J pat (a.prime.data.tree β) (pcu a.prime.data β)).Valid (a.prime.data.tree β) (pcN a β) p := by
  rw [pcN, pc_LG_eq]
  exact objCfg_valid_objTree hpat (pc_stemChain _ _ _ _ β J hne hcs)

/-- **The pinned stem chain slot family** (`objCfg = root` or `term`), from D3 at `θ = η`. -/
theorem pc_d3_fam {P : WTParams} (hD3 : ProtBoundAt P) (hη : 0 ≤ P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) (C : ℝ)
    (hC : P.C₁ ≤ C) {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R)))
    (pat : Fin (2 * R) → FixPat) (t s : ℝ) (hp : p < P.D) (hcan : IsCanonGC (p + 1) (recLG a))
    (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4) (hG : CapGeo (recLG a) J p) (hpat : CapPatValid (recLG a) J pat p)
    (hroot : ∀ j ∉ J, ∃ ℓ : GLeaf (recLG a).garden.tree, IsCapFlower (recLG a) J ℓ ∧ ℓ.1.1 = j)
    (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t)
    (kSel : Fin (2 * R) → Option ℕ) (hkSel : ∀ j, (kSel j).isSome → pat j = FixPat.plain)
    (σ : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j)
    (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb1 : 1 ≤ b)
    (hb : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
    (Rf : Fin (2 * R) → Option ℝ) (hRf : ∀ j r, Rf j = some r → 1 ≤ r)
    (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d)) (β : GBranch a.prime.skeleton.tree) (x : Fin P.d → ℤ)
    (hne : a.prime.data.tree β ≠ .nil)
    (hcs : OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode)
    (hpn : HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) (.inr β))
    (cfg : ProtCfg) (hcfg : objCfg (recLG a) J pat (a.prime.data.tree β) (pcu a.prime.data β) = cfg)
    (hcfg' : cfg = .root ∨ cfg = .term) (hr : cfg = .root → β.1.2 = [])
    (hnp : pat (pcj a.prime.data β) ≠ FixPat.plain) (Kg : ℝ) (hKg : 2 * (capCsup P.d P.η).toReal ≤ Kg) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inr β) x P.η
      (ENNReal.ofReal (Kg * genSlotMass P C b a J pat t s kSel Rs (.inr β))) := by
  set D := a.prime.data
  set hS := a.prime.prime.1
  set X := D.tree β
  set N := pcN a β
  set S := pc_frontS D hS (sourceLayer a) (sourceLayer_isLayering a) β p
  set ω := pc_ω (d := P.d) D hS (sourceLayer a) (sourceLayer_isLayering a) β Rf
  set F := pcFσ D hS (sourceLayer a) (sourceLayer_isLayering a) β J σ
  set Fu := pcFsh D hS (sourceLayer a) (sourceLayer_isLayering a) β J kSel Rs
  set q' := pcq a β
  set lo : ℝ := if cfg = .root then t else p with hlo
  have hL1 : 1 ≤ P.L := by linarith
  have hsel0 := pc_Fsel_empty D hS (sourceLayer a) (sourceLayer_isLayering a) β J pat kSel hkSel hnp
  have hsn0 := pc_selNative_empty D hS (sourceLayer a) (sourceLayer_isLayering a) β J pat kSel hkSel hnp
  have hcfgT : cfg ≠ .trace := by rcases hcfg' with rfl | rfl <;> decide
  -- the slot function
  set mD : (GNode N.garden.tree → Mom P.d) → ℂ := fun κ => IncTop.starWeight S ω κ *
    filtWeight F (fun _ => false) (fun _ => pcRad P.L σ (pcj D β)) κ *
    filtWeight Fu (fun _ => false) (fun _ => Rs (pcj D β)) κ * (((fun _ => (1 : ℝ)) κ : ℝ) : ℂ) with hmD
  set F' : (Fin 2 → ℝ) → Mom P.d → ℂ := fun ts k => kernelProt P.L P.γ P.δ N (pcHp a β (J := J) P.L h roots) mD
    (fun _ => ts 0) (ts 1) (cfg.fix X s t 0) k (fun _ => 0) 0 with hF'
  have hker : ∀ ts k, genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inr β) ts k = F' ts k := by
    intro ts k
    rw [pc_ker a β hG hne hcs P.L P.γ P.δ pat t s σ kSel Rs h roots Rf dag ts k, hcfg]
    congr 1
    funext K
    rw [pcΘ_eq D hS (sourceLayer a) (sourceLayer_isLayering a) β J P.L σ kSel Rs K, hsel0,
      Finset.prod_empty, hmD]
    push_cast
    ring
  have hm : ∀ K, ‖mD K‖ ≤ 1 * chiDNorm ^ F.card * chiDNorm ^ Fu.card * 1 := by
    intro K
    rw [hmD]
    simp only [norm_mul, Complex.ofReal_one, norm_one]
    refine mul_le_mul (mul_le_mul (mul_le_mul (pc_norm_starWeight_le _ _ _ _ β p Rf K)
      (pc_norm_filtWeight_le _ _ _ _) (norm_nonneg _) zero_le_one) (pc_norm_filtWeight_le _ _ _ _) (norm_nonneg _)
      (mul_nonneg zero_le_one (pow_nonneg chiDNorm_pos.le _))) le_rfl zero_le_one
      (mul_nonneg (mul_nonneg zero_le_one (pow_nonneg chiDNorm_pos.le _)) (pow_nonneg chiDNorm_pos.le _))
  have hF'c : ∀ k, Continuous fun ts => F' ts k := fun k =>
    ProtWhole.continuous_kernelProt_joint P.L P.γ P.δ N _ mD _ hm _ k
      (PL234.card_lone_le_of_decodesTree (decodedTree_decodes X _))
      (ProtPin.summable_coset_piece (pc_LC a β hG P.L h roots hb1 hb) hL1 k)
  -- D3
  obtain ⟨n, hn2, hn1, hnN⟩ := pc_size a β hsz hne
  have hSt := pc_stemChain D hS (sourceLayer a) (sourceLayer_isLayering a) β J hne hcs
  have hValid : cfg.Valid X N p := hcfg ▸ pc_valid a β hpat hne hcs
  have key := hD3 p hp n hnN 1 N X (pc_shape a β hG hne hcs) hn2 cfg hValid (pc_amb a β hcan) P.η
    (31 * P.d + 6) (Or.inl ⟨rfl, rfl⟩) s t hs.1 hs.2 ht.2 q' (hG.layer_le _) S ω (fun _ => frontierConst P.d)
    (pc_pres a β P.d Rf hRf) F (fun _ => pcRad P.L σ (pcj D β)) (fun _ _ => pcRad_ge (by linarith) σ _) Fu
    (fun _ => Rs (pcj D β)) (fun _ _ => hRs _) (fun _ => 1) ⟨fun _ => ⟨zero_le_one, le_rfl⟩, fun _ _ _ => rfl⟩
    (fun _ _ => rfl) (pcHp a β (J := J) P.L h roots) (fun _ => b.toNNReal) (pc_LC a β hG P.L h roots hb1 hb) 0
    (pcC0 P.L a roots β x)
  have hbox_eq : cfg.box X t p q' = pcBox lo (p + 1) q' := by
    rcases hcfg' with rfl | rfl
    · simp only [hlo, ↓reduceIte]
      exact rootBox_eq_pcBox ht.1.le
    · simp only [hlo]
      exact timeBoxGt_eq_pcBox _ _
  have hfun : (fun ts k => kernelProt P.L P.γ P.δ N (pcHp a β (J := J) P.L h roots)
      (fun κ => IncTop.starWeight S ω κ * filtWeight F (fun _ => false) (fun _ => pcRad P.L σ (pcj D β)) κ *
        filtWeight Fu (fun _ => false) (fun _ => Rs (pcj D β)) κ * (((fun _ => (1 : ℝ)) κ : ℝ) : ℂ))
      (fun _ => ts 0) (ts 1) (cfg.fix X s t (ts 0)) k (fun _ => 0) 0) = F' := by
    funext ts k
    rw [hF', ProtWhole.fix_up_indep cfg hcfgT X s t (ts 0) 0]
  rw [hbox_eq, hfun] at key
  -- the mass
  have hM := pc_genSlotMass_pos P (hC1.trans hC) hδ (by linarith) hb1 a J pat t s kSel Rs
    (fun j => lt_of_lt_of_le (by linarith) (hRs j)) β
  have hLS0 : 0 ≤ genLeaf a J b (.inr β) := by rw [pc_genLeaf_eq]; exact (pc_leaf_pos _ hb1).le
  have hmass : (∏ _z ∈ S, ENNReal.ofReal (frontierConst P.d)) * ENNReal.ofReal (P.L ^ (31 * (P.d : ℝ) + 6)) *
      regBound P n (protIncoh X N) * ENNReal.ofReal (leafSizeProduct N (fun _ => b.toNNReal)) ≤
      ENNReal.ofReal (genSlotMass P C b a J pat t s kSel Rs (.inr β)) := by
    rw [Finset.prod_const, ← pc_genLeaf_eq]
    refine pc_mass_le P hC hC1 hδ.le hL1 hηγ a J pat t s kSel Rs (.inr β) hpn
      (pc_frontS_card_le D hS (sourceLayer a) (sourceLayer_isLayering a) β p) hn1 hn2
      (Real.rpow_nonneg (by linarith) _) hLS0 ?_
    rw [hsn0, Finset.prod_empty, mul_one]
    exact pc_Lpow31 P hL1
  -- the box
  have hq'p : (q' : ℝ) ≤ p := by exact_mod_cast hG.layer_le _
  have hplo : (p : ℝ) ≤ lo := by
    rw [hlo]; split_ifs
    · exact ht.1.le
    · exact le_rfl
  have hlo1 : lo < p + 1 := by
    rw [hlo]; split_ifs
    · exact ht.2
    · linarith
  have hbox : ∀ ts ∈ genBoxAt p a J pat t s (.inr β), ts ∈ pcBoxC lo (p + 1) q' := by
    intro ts hts
    obtain ⟨⟨h1, h2, h3, h4, h5⟩, h0⟩ := pc_genBox a J pat t s hG hpat hroot ht hs β hne hcs ts hts
    rw [hlo]
    split_ifs with hc
    · exact ⟨(h0 (hr hc)).ge, h2, h3, h4, h5⟩
    · exact ⟨h1, h2, h3, h4, h5⟩
  refine pc_fam1 P hη a J pat t s σ kSel Rs h roots Rf dag β x lo q' (hq'p.trans hplo) hplo hlo1 F' hF'c hker
    hbox _ hM (key.trans hmass) _ (ENNReal.ofReal_le_ofReal ?_)
  have hM0 := hM.le
  nlinarith

end WaveTurbulence.Flower.MkSlotsO

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.PcD6F
public import WaveTurbulence.Foundations.Flower.ProtWhole.RegTarget
public import WaveTurbulence.Foundations.Flower.ProtWhole.AnnFree
public import WaveTurbulence.Foundations.Flower.ProtPin.ProtGate
public import WaveTurbulence.Foundations.Flower.MkSlots.CapObl

/-! # PROT-CHAIN (`Pc`): **`stemProtChainKind`** — the stem-protected chain slots

`MkSlotsO.IsStemProtChainSlot` (a protected chain slot that is not an off-stem root trace): a chain slot `.inr β`
with a pinned native branch and a native stem node, or with a selected native vertex. Its core is on the capped
stem and its chain is not `nil`, so its native chain is a D2b stem chain with `objCfg ∈ {none, root, term}`:

* `root` (a `dRoot` skeleton root chain, garden root at `t`) and `term` (F-H3-3: `dParent`, the lone parent at `s`
  below the core capped flower parent): D3 (`pc_d3_fam`);
* `none`: no native pin, so the slot carries a selected native vertex (an absorbed selection): D6 (`pc_d6_fam`).

No such slot is `SelAdj` (a clock of the slot is in the tree of the chain; non-plain trees carry no selection, and
the selected vertex of a plain tree is the native one, not a core). The result is unconditional: D3's
`ProtPin.protBoundGate`, D6's `ProtWhole.protAnnBoundGate_of_D3`.

* `pc_annMono` (D6 is monotone in the large constants), `pc_argSrc_tree`, `pc_hasProtNative`, `pc_core_data`;
* `pcK d η = max 1 (2 · capCsup d η)`; **`stemProtChainAt_of`** (one parameter record); **`stemProtChainKind`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open Set
open WaveTurbulence WaveTurbulence.LGSpine Finset TTree
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.MkSlots WaveTurbulence.Flower.MkSlotsI
  WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtGeo

namespace WaveTurbulence.Flower.MkSlotsO

/-- D6 is monotone in the large constants. -/
theorem pc_annMono : LargeConstantMonotone ProtAnnBoundAt := by
  intro P c₁ c₂ hC _hC₂ hδ hL hCC _hCC₂ h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 M₂ a8 s a9 a10 q' a11 a12
    S ω cω a13 F M a14 Fu Mu a15 ind a16 a17 H B a18 b₀ c₀
  rw [N_largeConstants] at hn
  exact (h p hp n hn w LG X a1 a2 pin Sel a3 a4 a5 a6 a7 M₂ a8 s a9 a10 q' a11 a12 S ω cω a13 F M a14 Fu Mu a15
    ind a16 a17 H B a18 b₀ c₀).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (regBound_largeConstants_mono P (by linarith) hCC hδ.le (by linarith) n _) zero_le) zero_le)

/-- The clocks of a chain slot are in the tree of the chain. -/
theorem pc_argSrc_tree {w : ℕ} {S : Garden w} (hS : S.IsPlain) (β β' : GBranch S.tree) (i : Fin 2)
    (h : argSrc hS (.inr β) i = .inr β') : β'.1.1 = β.1.1 := by
  fin_cases i
  · have h' : clkOfNode S β.toNode = .inr β' := h
    unfold clkOfNode nodeToSlot at h'
    by_cases hr : (β.toNode).1.2 = []
    · simp only [hr, ↓reduceDIte] at h'
      exact absurd h' (by simp)
    · simp only [hr, ↓reduceDIte] at h'
      rw [← Sum.inr_injective h']
      rfl
  · have h' : (.inr β : ClkSrc S) = .inr β' := h
    rw [Sum.inr_injective h']

/-- The constant of the stem-protected chain kind. -/
def pcK (d : ℕ) (η : ℝ) : ℝ := max 1 (2 * (capCsup d η).toReal)

section Slot

variable {R : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat)
  (t s : ℝ) (kSel σ : Fin (2 * R) → Option ℕ) (β : GBranch a.prime.skeleton.tree)

/-- A protected chain slot carries a protected native node. -/
theorem pc_hasProtNative
    (h : HasPinNative a J pat t s kSel σ (.inr β) ∨ HasSelNat a J pat t s kSel σ (.inr β)) :
    HasProtNative a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (protI (recLG a) J pat t s kSel) (.inr β) := by
  rcases h with ⟨qb, hqb⟩ | ⟨y, hy, v, hv, hvy⟩
  · refine ⟨GBranch.toNode (tree := (decodedTree (a.prime.data.tree β) (nodeSign a.prime.skeleton.sig β.1)).tree) qb,
      fun β' he => ?_, (pcB a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β qb).toNode,
      ?_, rfl⟩
    · exact pc_lone_not_branch _ _ (sourceLayer a) (sourceLayer_isLayering a) β qb
        ((pc_chain_core_iff _ _ (sourceLayer a) (sourceLayer_isLayering a) β _).mp ⟨β', he⟩)
    · refine Finset.mem_filter.2 ⟨Finset.mem_univ _, _, ⟨rfl, Or.inl rfl⟩, Or.inr ⟨_, rfl, Or.inl hqb⟩⟩
  · exact ⟨y, hy, v.toNode, Finset.mem_filter.2 ⟨Finset.mem_univ _, _, ⟨rfl, Or.inl rfl⟩, Or.inr ⟨v, rfl, Or.inr hv⟩⟩,
      hvy⟩

variable {p : ℕ}

/-- The core of a stem-protected chain slot is on the capped stem and its chain is not `nil`. -/
theorem pc_core_data (hG : CapGeo (recLG a) J p)
    (h : (HasPinNative a J pat t s kSel σ (.inr β) ∧ HasStemNative a J pat t s kSel σ (.inr β)) ∨
      HasSelNat a J pat t s kSel σ (.inr β)) :
    a.prime.data.tree β ≠ .nil ∧ OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode := by
  have key : ∀ y : GNode (decodedTree (a.prime.data.tree β) (nodeSign a.prime.skeleton.sig β.1)).tree,
      (∀ β' : GBranch a.prime.skeleton.tree, chainContextNode a.prime.data a.prime.prime.1 β y ≠
        (a.prime.data.coreBranch a.prime.prime.1 β').toNode) →
      OnCapStem (recLG a) J (chainContextNode a.prime.data a.prime.prime.1 β y) →
      a.prime.data.tree β ≠ .nil ∧ OnCapStem (recLG a) J (a.prime.data.coreBranch a.prime.prime.1 β).toNode := by
    intro y hy hst
    have hyl : y.1.2 ≠ (a.prime.data.tree β).lonePath := fun he =>
      (fun ⟨β', hβ'⟩ => hy β' hβ') ((pc_chain_core_iff _ _ (sourceLayer a) (sourceLayer_isLayering a) β y).mpr he)
    exact ⟨pc_ne_nil _ β y hyl, pc_core_stem _ _ (sourceLayer a) (sourceLayer_isLayering a) β J hG.cap_leaf y hyl hst⟩
  rcases h with ⟨-, y, hy, z, hz, hzy⟩ | ⟨y, hy, v, hv, hvy⟩
  · have hze : z = chainContextNode a.prime.data a.prime.prime.1 β y := Subtype.ext hzy
    exact key y hy (hze ▸ hz)
  · have hvs := (MkSlotsS.mem_stemSetCap_iff'.1 (MkSlotsS.selCap_spec (MkSlotsS.selCap_of_mem_selSetCap hv)).2).2.1
    have hve : v.toNode = chainContextNode a.prime.data a.prime.prime.1 β y := Subtype.ext hvy
    exact key y hy (hve ▸ hvs)

end Slot

/-- **The stem-protected chain kind at one parameter record**, from D3 and D6. -/
theorem stemProtChainAt_of {P : WTParams} (hD3 : ProtBoundAt P) (hD6 : ProtAnnBoundAt P) (hη : 0 ≤ P.η)
    (hηγ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) (hL : 2 ≤ P.L) (hC1 : 1 ≤ P.C₁) (hδ : 0 < P.δ) :
    GenSlotOnAt IsStemProtChainSlot pcK P := by
  intro C hC R p a J pat t s hp hcan hsz hJ hgeo hpat hirr ht hs kSel hkSel σ Rs hRs mkF _ _ roots h b hb1 hb
    Rf hRf _ dag s' sl _ hQ x
  have hrec : recLG a = a.layered := sourceLayer_reconstructs a
  rw [← hrec] at hcan hgeo hpat hirr
  have hroot := MkSlotsB.exists_capFlower_of_capGeo hgeo (a.prime.data.garden_plain a.prime.prime.1) hirr
    (by rw [hJ])
  have hRf1 : ∀ j r, Rf j = some r → 1 ≤ r := fun j r hr => by have := hRf j r hr; linarith
  obtain ⟨⟨⟨β, rfl⟩, hps⟩, hnRT⟩ := hQ
  have hdata : (HasPinNative a J pat t s kSel σ (.inr β) ∧ HasStemNative a J pat t s kSel σ (.inr β)) ∨
      HasSelNat a J pat t s kSel σ (.inr β) := by
    rcases hps with hpin | hsel
    · by_cases hst : HasStemNative a J pat t s kSel σ (.inr β)
      · exact Or.inl ⟨hpin, hst⟩
      · exact absurd ⟨⟨β, rfl⟩, hpin, hst⟩ hnRT
    · exact Or.inr hsel
  obtain ⟨hne, hcs⟩ := pc_core_data a J pat t s kSel σ β hgeo hdata
  have hpn := pc_hasProtNative a J pat t s kSel σ β hps
  have hSt := pc_stemChain a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β J hne hcs
  have hKg : 2 * (capCsup P.d P.η).toReal ≤ pcK P.d P.η := le_max_right _ _
  -- the selection tree of a clock
  have hclk : ∀ (i : Fin 2) (β' : GBranch a.prime.skeleton.tree), argSrc a.prime.prime.1 (.inr β) i = .inr β' →
      ∀ v ∈ selSetCap (recLG a) J kSel, v.1 = (a.prime.data.coreBranch a.prime.prime.1 β').1 →
      selCap (recLG a) J kSel (pcj a.prime.data β) = some v := by
    intro i β' hi v hv hv'
    have h1 : v.1.1 = pcj a.prime.data β := by
      rw [hv', pcj_eq]
      show (inflatedPosition a.prime.skeleton a.prime.data.tree β'.toNode).1 = _
      rw [inflatedPosition_index]
      exact pc_argSrc_tree a.prime.prime.1 β β' i hi
    rw [← h1]
    exact MkSlotsS.selCap_of_mem_selSetCap hv
  rcases pc_objCfg_cases a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β J pat with
    hc | ⟨hc, hpr, hu⟩ | ⟨hc, hpr, -⟩
  · -- `none`: an absorbed selection (D6)
    have hsel : HasSelNat a J pat t s kSel σ (.inr β) := by
      rcases hps with ⟨qb, hqb⟩ | hsel
      · exfalso
        have e := pc_fixN a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β J hgeo hSt
          pat t s 0 qb
        rw [hc] at e
        have e' := e.trans (pc_none_fix _ _ _ _ qb)
        have : (fixNative a.prime.data a.prime.prime.1 (fixCap (recLG a) J pat t s) (.inr β) qb).isSome := hqb
        rw [e'] at this
        exact absurd this (by simp)
      · exact hsel
    obtain ⟨y, hy, v, hv, hvy⟩ := hsel
    refine slotConcl_of_fam1 P C pcK a J pat t s σ kSel Rs h roots Rf dag b (.inr β) x (fun _ => ?_)
      (fun hsa => ?_)
    · exact pc_d6_fam hD6 hη hηγ hL hC1 hδ C hC a J pat t s hp hcan hsz hgeo hpat hroot ht hs kSel σ Rs hRs roots
        h b hb1 hb Rf hRf1 dag β x hne hcs hpn hc y hy v hv hvy _ hKg
    · exfalso
      obtain ⟨i, β', hi, v', hv', hv'e⟩ := hsa
      have h1 := hclk i β' hi v' hv' hv'e
      have h2 : selCap (recLG a) J kSel (pcj a.prime.data β) = some v := by
        have h3 : v.1.1 = pcj a.prime.data β := by
          have h4 := congrArg Prod.fst hvy
          exact h4
        rw [← h3]
        exact MkSlotsS.selCap_of_mem_selSetCap hv
      rw [h2] at h1
      have h5 := Option.some.inj h1
      subst h5
      exact hy β' (Subtype.ext (hvy.symm.trans hv'e))
  · -- `root`: a `dRoot` root chain (D3)
    have hnp : pat (pcj a.prime.data β) ≠ FixPat.plain := by rw [hpr]; decide
    refine slotConcl_of_fam1 P C pcK a J pat t s σ kSel Rs h roots Rf dag b (.inr β) x (fun _ => ?_)
      (fun hsa => ?_)
    · exact pc_d3_fam hD3 hη hηγ hL hC1 hδ C hC a J pat t s hp hcan hsz hgeo hpat hroot ht hs kSel hkSel σ Rs hRs
        roots h b hb1 hb Rf hRf1 dag β x hne hcs hpn .root hc (Or.inl rfl)
        (fun _ => pc_u_nil a.prime.data β hu) hnp _ hKg
    · obtain ⟨i, β', hi, v', hv', hv'e⟩ := hsa
      exact (hnp (hkSel _ (MkSlotsS.selCap_spec (hclk i β' hi v' hv' hv'e)).1)).elim
  · -- `term`: F-H3-3, a `dParent` chain (D3)
    have hnp : pat (pcj a.prime.data β) ≠ FixPat.plain := by rw [hpr]; decide
    refine slotConcl_of_fam1 P C pcK a J pat t s σ kSel Rs h roots Rf dag b (.inr β) x (fun _ => ?_)
      (fun hsa => ?_)
    · exact pc_d3_fam hD3 hη hηγ hL hC1 hδ C hC a J pat t s hp hcan hsz hgeo hpat hroot ht hs kSel hkSel σ Rs hRs
        roots h b hb1 hb Rf hRf1 dag β x hne hcs hpn .term hc (Or.inr rfl) (fun h => absurd h (by decide)) hnp _ hKg
    · obtain ⟨i, β', hi, v', hv', hv'e⟩ := hsa
      exact (hnp (hkSel _ (MkSlotsS.selCap_spec (hclk i β' hi v' hv' hv'e)).1)).elim

/-- **The stem-protected chain kind** (unconditional: D3 and D6). -/
theorem stemProtChainKind :
    ∃ K : ℕ → ℝ → ℝ, (∀ d η, 1 ≤ K d η) ∧ WTPrefix (GenSlotOnAt IsStemProtChainSlot K) := by
  refine ⟨pcK, fun d η => le_max_left _ _, ?_⟩
  have H0 := prefix_and ProtPin.protBoundGate (ProtWhole.protAnnBoundGate_of_D3 ProtPin.protBoundGate)
    ProtWhole.protBoundAt_mono pc_annMono
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, H⟩ := H0 d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1def
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg1 : 0 < g1 := by
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    have : 0 < (d : ℝ) - 1 := by linarith
    positivity
  have hg1' : g1 ≤ 1 := (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨min η₀ ((g1 / 2) ^ 2), lt_min hη₀ (by positivity), fun η hη φin hφin τs hτs φ hW => ?_⟩
  have hη1 : η ∈ Ioc 0 η₀ := ⟨hη.1, hη.2.trans (min_le_left _ _)⟩
  have hη2 : η ≤ (g1 / 2) ^ 2 := hη.2.trans (min_le_right _ _)
  obtain ⟨C₁, hC₁, ν₀, hν₀, H2⟩ := H η hη1 φin hφin τs hτs φ hW
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, H3⟩ := H2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD hτD => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, H4⟩ := H3 δ hδ D hD hτD
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact stemProtChainAt_of (H4 L hL).1 (H4 L hL).2 hη.1.le (sqrt_add_pow8_le hg1 hg1' hη.1 hη2) (le_trans hL₀ hL)
    hC₁ hδ.1

end WaveTurbulence.Flower.MkSlotsO

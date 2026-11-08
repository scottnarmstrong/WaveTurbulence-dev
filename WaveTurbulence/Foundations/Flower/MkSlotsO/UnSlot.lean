/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkSlotsO.UnMass
public import WaveTurbulence.Foundations.Flower.MkSlots.IntAsm3
public import WaveTurbulence.Foundations.Flower.MkSlotsG.Bridge

/-! # B3s-HELPER8 / UNPIN (part 6): one family per unpinned slot, at one moment weight

For an unpinned slot (`IsUnpinSlot`: not a cap pair, no pinned native branch, no selected native vertex) of the
class piece and a moment weight `θ` (`θ = η` with no loss, or `θ = 1/4` with the loss `L^{4d}`, `ThetaC`):
**`unSlot_cpl`** (a non-cap leaf pair: a centred family, localized amplitudes, every momentum) and
**`unSlot_chain`** (a chain slot: a global family, every momentum) give `SlotFam1 … θ` with mass
`Kun d θ · L^c · genSlotMass`.

Route: the kernel identification (`slotFn_cpl_eq`, `slotFn_chain_eq`), the frontier weights as INC-TOP star weights
(`IncTop.rowTopWeightR_eq_starWeight`, `topStar_presented`), the D5 targets (`unCpl_main`, `unTree_main`; trivial
objects `unCpl_triv`, `unTree_nil`), the boxes (`genBoxAt_cpl_sub`, `genBoxAt_chain_sub`) and the masses
(`genSlotMass_ge_base`, `topSet_sub_cplNodes`, `topSet_sub_treeNodes`, B3's `cplExp_le_slotNr`,
`treeExp_le_slotNr`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical ENNReal
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed WaveTurbulence.Represents
open WaveTurbulence.VineA WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.VineAlign
open WaveTurbulence.Flower.MkDefs WaveTurbulence.Flower.Stage1W WaveTurbulence.Flower.Stage1WNoVine
open WaveTurbulence.Flower.Stage1WVine WaveTurbulence.Flower.MkSlotsI

namespace WaveTurbulence.Flower.MkSlotsO

/-- Mass bookkeeping of a non-trivial object. -/
theorem un_mass_chain {K K' Pc nrp Lc X lf G : ℝ} (hK : K ≤ K') (hK0 : 0 ≤ K) (hPc : Pc ≤ nrp) (hPc0 : 0 ≤ Pc)
    (hLc : 0 ≤ Lc) (hX : 0 ≤ X) (hlf : 0 ≤ lf) (hG : X * (nrp * lf) ≤ G) :
    K * (Pc * Lc * X * lf) ≤ K' * Lc * G := by
  have hK'0 : 0 ≤ K' := hK0.trans hK
  calc K * (Pc * Lc * X * lf) ≤ K' * (nrp * Lc * X * lf) := by gcongr
    _ = K' * Lc * (X * (nrp * lf)) := by ring
    _ ≤ K' * Lc * G := by gcongr

/-- Mass bookkeeping of a trivial object. -/
theorem un_mass_triv {K K' Lc lf G : ℝ} (hK : K ≤ K') (hK0 : 0 ≤ K) (hLc : 1 ≤ Lc) (hlf : 0 ≤ lf)
    (hG : lf ≤ G) : K * lf ≤ K' * Lc * G := by
  have hK'0 : 0 ≤ K' := hK0.trans hK
  have h1 : K * lf ≤ K' * lf := mul_le_mul_of_nonneg_right hK hlf
  have h2 : lf ≤ Lc * G := by nlinarith
  calc K * lf ≤ K' * lf := h1
    _ ≤ K' * (Lc * G) := mul_le_mul_of_nonneg_left h2 hK'0
    _ = K' * Lc * G := by ring

section Slot

variable {P : WTParams} (hI : ProtDefs.FiltIncoherentDecayAt P) (hC : ProtDefs.FiltCoherentBoundAt P)
  (hd : 1 ≤ P.d) (hL : 2 ≤ P.L) (hη0 : 0 ≤ P.η) (hη4 : P.η ≤ 1 / 4) (hc1 : 1 ≤ P.C₁) (hδ : 0 ≤ P.δ)
  (hκ : P.η ^ 8 ≤ P.gamma1 - Real.sqrt P.η) {θ c : ℝ} (hθ : ThetaC P θ c) (C : ℝ) (hCC : P.C₁ ≤ C)
  {R p : ℕ} (a : PrescribedPrimeGarden (2 * R)) (J : Finset (Fin (2 * R))) (pat : Fin (2 * R) → FixPat) (t s : ℝ)
  (hp : p < P.D) (hcan : IsCanonGC (p + 1) a.layered) (hsz : a.prime.data.size ≤ P.N (p + 1) ^ 4)
  (hJ : J.card = R) (hgeo : CapGeo a.layered J p) (hpat : CapPatValid a.layered J pat p)
  (hirr : a.layered.garden.Irreducible) (ht : t ∈ Ioo (p : ℝ) (p + 1)) (hs : s ∈ Ioo (p : ℝ) t)
  (σ kSel : Fin (2 * R) → Option ℕ) (Rs : Fin (2 * R) → ℝ) (hRs : ∀ j, P.L ≤ Rs j)
  (roots : Fin (2 * R) → (Fin P.d → ℤ)) (h : ℕ → Fin (2 * R) → Fin (2 * R) → Mom P.d → ℝ) (b : ℝ) (hb : 1 ≤ b)
  (hh : ∀ q ≤ p, ∀ j j', SNormR (40 * P.d) (40 * P.d) (h q j j') ≤ ENNReal.ofReal b)
  (Rf : Fin (2 * R) → Option ℝ) (hRf : ∀ j r, Rf j = some r → P.L / 2 ≤ r)
  (dag : Option (Fin (2 * R) → Fin 3 → Mom P.d))

include hI hC hd hL hη0 hη4 hc1 hδ hκ hθ hCC hp hcan hsz hJ hgeo hpat hirr ht hs hb hh hRf in
/-- **An unpinned non-cap leaf pair**: one centred family at the moment weight `θ`. -/
theorem unSlot_cpl (q : SourcePair a.prime.skeleton) (hq : ¬ MkSlots.IsCapPair a.prime.skeleton a.prime.prime.1 J q)
    (hpin : ¬ HasPinNative a J pat t s kSel σ (.inl q)) (hselN : ¬ HasSelNat a J pat t s kSel σ (.inl q))
    (x : Fin P.d → ℤ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inl q) x θ
      (ENNReal.ofReal (Kun P.d θ * P.L ^ c * genSlotMass P C b a J pat t s kSel Rs (.inl q))) := by
  have hL1 : 1 ≤ P.L := by linarith
  have hrec : MkSlots.recLG a = a.layered := sourceLayer_reconstructs a
  have hcan' : IsCanonGC (p + 1) (MkSlots.recLG a) := by rw [hrec]; exact hcan
  have hlay : ∀ ν, sourceLayer a ν ≤ p := fun ν => Canon.layer_le_of_isCanonGC hcan' ν
  have hgeo' : CapGeo (MkSlots.recLG a) J p := by rw [hrec]; exact hgeo
  have hpat' : CapPatValid (MkSlots.recLG a) J pat p := by rw [hrec]; exact hpat
  have hcap : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hgeo'.cap_leaf
  have hroot := MkSlotsG.exists_capFlower_of_capGeo hgeo' (a.prime.data.garden_plain a.prime.prime.1)
    (by rw [hrec]; exact hirr) (by rw [hJ])
  have hcF : 1 ≤ frontierConst P.d := one_le_frontierConst P.d
  have hctrl : LeafwiseControlled (MkSlots.recLG a) (typeProfiles (MkSlots.recLG a) h) (fun _ => b.toNNReal) :=
    MkSlots.IntAsm.leafwise_of_bound (MkSlots.recLG a) p (fun z => hlay z) h b (by linarith) hh
  have hctrlN := couple_controlled a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) _ _
    hctrl q
  have hgP : ∀ j, GPresented (32 * P.d) (frontierG (d := P.d) (Rf j)) (frontierConst P.d) :=
    gPresented_frontier hL Rf hRf
  have hker : ∀ ts k, genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inl q) ts k =
      coupleLeavesTopR P.L P.γ P.δ p (cplG a.prime.data a.prime.prime.1 (fun j => frontierG (Rf j)) q)
        (cplQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q 0)
        (cplQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q 1)
        (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q)
        (RegRedLeaf.nativeCoupleProfiles a.prime.data a.prime.prime.1 (typeProfiles (MkSlots.recLG a) h) q)
        (ts 0) (ts 1) k := fun ts k => by
    unfold genSlotKer
    exact slotFn_cpl_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J P.L σ kSel Rs
      P.γ P.δ p s h roots Rf dag (fixCap (MkSlots.recLG a) J pat t s) hcap q hq (fixNative_none_of_not_pin hpin) ts k
  have hbox := genBoxAt_cpl_sub a J pat t s p hgeo' hpat' hroot ht hs q
  have hlf : 0 ≤ slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (.inl q) := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hleaf : genLeaf a J b (.inl q) = slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inl q) := by
    simp only [genLeaf, hq, ↓reduceIte, one_mul]
  have hG := genSlotMass_ge_base P (C := C) (by linarith) hb hL1 a J pat t s kSel Rs (.inl q)
    (selNative_eq_empty _ _ _ _ J kSel _ hselN)
  rw [hleaf] at hG
  have hX0 : ∀ e : ℕ, ∀ g : ℝ, 0 ≤ (C * Real.sqrt P.δ) ^ e * P.L ^ (-(P.η ^ 8) * g) := fun e g =>
    mul_nonneg (pow_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg (by linarith) _)
  have hLc0 : 0 ≤ P.L ^ c := Real.rpow_nonneg (by linarith) _
  -- the superposition of the native couple kernel
  have hsup : ∃ μ0 : ℝ≥0∞, μ0 ≤ ENNReal.ofReal (Kun P.d θ * P.L ^ c * genSlotMass P C b a J pat t s kSel Rs (.inl q)) ∧
      CenSupM θ (30 * P.d) (timeBox (clkL a p (.inl q) 0 : ℝ) (clkL a p (.inl q) 1))
        (fun ts k => coupleLeavesTopR P.L P.γ P.δ p (cplG a.prime.data a.prime.prime.1 (fun j => frontierG (Rf j)) q)
          (cplQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q 0)
          (cplQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q 1)
          (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q)
          (RegRedLeaf.nativeCoupleProfiles a.prime.data a.prime.prime.1 (typeProfiles (MkSlots.recLG a) h) q)
          (ts 0) (ts 1) k) μ0 := by
    by_cases htriv : a.prime.data.couple q = RegCpl.triv
    · have hdecT : RegCpl.triv.Decodes (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a)
          (sourceLayer_isLayering a) q).garden := by
        rw [← htriv]; exact couple_decodes _ _ _ _ q
      refine ⟨_, ?_, unCpl_triv (θ := θ) hd P.L P.γ P.δ p _ (frontierConst P.d) hcF (fun j => hgP _) _ _ _ hdecT _ _
        hctrlN _⟩
      refine ENNReal.ofReal_le_ofReal (un_mass_triv ?_ (mul_nonneg (sq_nonneg _) (profCM_spec (θ := θ) hd).1.le)
        (Real.one_le_rpow hL1 hθ.c_nonneg) hlf ?_)
      · exact (le_max_left _ _).trans (le_max_right _ _)
      · refine le_trans ?_ hG
        have hs0 : slotSize a.prime.data (.inl q) = 0 := by
          show (a.prime.data.couple q).size = 0
          rw [htriv]; rfl
        have hi0 : slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (.inl q) = 0 := by
          show (nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
            q).incoherency (a.prime.data.couple q).links = 0
          rw [htriv]; exact incoherency_triv _
        rw [hs0, hi0]
        simp only [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
        exact le_mul_of_one_le_left hlf (one_le_pow₀ hcF)
    · obtain ⟨n, hn⟩ := code_size_even (a.prime.data.couple q)
      have hn2 : (a.prime.data.couple q).size = 2 * n := by omega
      have hn1 : 1 ≤ n := by
        have := cpl_two_le _ (a.prime.data.couple_wf q) htriv
        omega
      have hnN : n ≤ P.N (p + 1) ^ 4 := by
        have h1 := slotSize_le a.prime.data (.inl q)
        have h2 : slotSize a.prime.data (.inl q) = (a.prime.data.couple q).size := rfl
        omega
      set N := nativeCoupleLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) q with hN
      set qr : Fin 2 → ℕ := ![cplQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q 0,
        cplQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q 1] with hqr
      have hcase : 1 ≤ N.incoherency (a.prime.data.couple q).links ∨
          (N.incoherency (a.prime.data.couple q).links = 0 ∧
            IsCoherentCoupleAt p (clkL a p (.inl q) 0) (clkL a p (.inl q) 1) (a.prime.data.couple q) N) := by
        by_cases hg0 : N.incoherency (a.prime.data.couple q).links = 0
        · exact Or.inr ⟨hg0, couple_coherent_at _ _ _ _ p hcan' q hg0⟩
        · exact Or.inl (Nat.one_le_iff_ne_zero.2 hg0)
      have hm := unCpl_main hI hC hd hL1 hη0 hη4 hc1 hδ hκ hθ C hCC hp hnN (a.prime.data.couple q)
        (a.prime.data.couple_wf q) hn2 hn1 N (couple_decodes _ _ _ _ q) (fun z => hlay _) _ _
        (clkLayer_le _ _ _ p hlay _) (clkLayer_le _ _ _ p hlay _) (couple_root_layer_le _ _ _ _ p hlay q 0)
        (couple_root_layer_le _ _ _ _ p hlay q 1) hcase (IncTop.topSet p N qr)
        (IncTop.topStar (cplG a.prime.data a.prime.prime.1 (fun j => frontierG (Rf j)) q))
        (fun _ => frontierConst P.d) (fun _ _ => by linarith)
        (fun z _ => IncTop.topStar_presented _ (fun j => hgP _) z) ∅ (fun _ => 0) (by simp) ∅ (fun _ => 0) (by simp)
        _ _ hctrlN _ (fun κ => norm_d5M_top_le p N qr _ (frontierConst P.d) hcF
          (fun j x => GPresented.norm_le (hgP _) (by linarith) x) _ _ _ _ κ)
      have hf : ∀ (ts : Fin 2 → ℝ) (k : Mom P.d), coupleLeavesTopR P.L P.γ P.δ p (cplG a.prime.data a.prime.prime.1 (fun j => frontierG (Rf j)) q)
          (qr 0) (qr 1) N (RegRedLeaf.nativeCoupleProfiles a.prime.data a.prime.prime.1
            (typeProfiles (MkSlots.recLG a) h) q) (ts 0) (ts 1) k =
          kernelLeavesW P.L P.γ P.δ N (RegRedLeaf.nativeCoupleProfiles a.prime.data a.prime.prime.1
            (typeProfiles (MkSlots.recLG a) h) q) (fun b => if b.1.1 = 0 then ts 0 else ts 1) 0 k (fun _ => 0) 0
            (d5M (IncTop.topSet p N qr) (IncTop.topStar (cplG a.prime.data a.prime.prime.1
              (fun j => frontierG (Rf j)) q)) ∅ (fun _ => 0) ∅ (fun _ => 0)) := by
        intro ts k
        unfold coupleLeavesTopR
        congr 1
        funext κ
        unfold d5M ProtDefs.filtWeight
        simp only [Finset.prod_empty, mul_one]
        exact IncTop.rowTopWeightR_eq_starWeight p _ N _ κ
      refine ⟨_, ?_, CenSupM.congr' hm fun ts _ k => (hf ts k).symm⟩
      refine ENNReal.ofReal_le_ofReal (un_mass_chain
        (nrp := frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inl q)) (le_max_left _ _ |>.trans (le_max_left _ _))
        ENNReal.toReal_nonneg ?_ (Finset.prod_nonneg fun _ _ => by linarith) hLc0 (hX0 _ _) hlf ?_)
      · rw [Finset.prod_const]
        refine pow_le_pow_right₀ hcF ?_
        refine (Finset.card_le_card (topSet_sub_cplNodes p N _ _)).trans ?_
        exact cplExp_le_slotNr a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p q
      · exact hG
  obtain ⟨μ0, hμ0, hsup⟩ := hsup
  obtain ⟨Λ, hcnt, wt, m, n, amp, h1, h2, h3, h4, h5, h6⟩ := hsup
  refine ⟨Λ, hcnt, wt, m, n, amp, h1, h2, fun l k => snorm_le_one_pointwise _ _ (h3 l) k, h3,
    fun _ _ => h4, fun ts hts nn _ _ _ => ?_, h6.trans hμ0⟩
  rw [hker]
  exact h5 ts (hbox hts) _

include hI hC hd hL hη0 hη4 hc1 hδ hκ hθ hCC hp hcan hsz hJ hgeo hpat hirr ht hs hRs hb hh hRf in
/-- **An unpinned chain slot**: one global family at the moment weight `θ`. -/
theorem unSlot_chain (β : GBranch a.prime.skeleton.tree)
    (hpin : ¬ HasPinNative a J pat t s kSel σ (.inr β)) (hselN : ¬ HasSelNat a J pat t s kSel σ (.inr β))
    (x : Fin P.d → ℤ) :
    SlotFam1 P (p := p) a J pat t s σ kSel Rs h roots Rf dag (.inr β) x θ
      (ENNReal.ofReal (Kun P.d θ * P.L ^ c * genSlotMass P C b a J pat t s kSel Rs (.inr β))) := by
  have hL1 : 1 ≤ P.L := by linarith
  have hrec : MkSlots.recLG a = a.layered := sourceLayer_reconstructs a
  have hcan' : IsCanonGC (p + 1) (MkSlots.recLG a) := by rw [hrec]; exact hcan
  have hlay : ∀ ν, sourceLayer a ν ≤ p := fun ν => Canon.layer_le_of_isCanonGC hcan' ν
  have hgeo' : CapGeo (MkSlots.recLG a) J p := by rw [hrec]; exact hgeo
  have hpat' : CapPatValid (MkSlots.recLG a) J pat p := by rw [hrec]; exact hpat
  have hcap : ∀ j ∈ J, (a.prime.data.garden a.prime.prime.1).tree j = TTree.leaf := hgeo'.cap_leaf
  have hroot := MkSlotsG.exists_capFlower_of_capGeo hgeo' (a.prime.data.garden_plain a.prime.prime.1)
    (by rw [hrec]; exact hirr) (by rw [hJ])
  have hcF : 1 ≤ frontierConst P.d := one_le_frontierConst P.d
  have hctrl : LeafwiseControlled (MkSlots.recLG a) (typeProfiles (MkSlots.recLG a) h) (fun _ => b.toNNReal) :=
    MkSlots.IntAsm.leafwise_of_bound (MkSlots.recLG a) p (fun z => hlay z) h b (by linarith) hh
  have hctrlN := chain_controlled a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) _ _
    hctrl β
  have hgP : ∀ j, GPresented (32 * P.d) (frontierG (d := P.d) (Rf j)) (frontierConst P.d) :=
    gPresented_frontier hL Rf hRf
  have hsel := noSelCh_of_not a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel β hselN
  set N := nativeChainLayered a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) β with hN
  set gT := treeG a.prime.data (fun j => frontierG (d := P.d) (Rf j)) β with hgT
  set qT := treeQ a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p β with hqT
  set F := chF a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J σ β with hF
  set M := chM a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) P.L σ β with hM
  set Fu := chFu a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J kSel β with hFu
  set Mu := chMu a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) Rs β with hMu
  set Hn := RegRedLeaf.nativeChainProfiles a.prime.data a.prime.prime.1 (typeProfiles (MkSlots.recLG a) h) β
    with hHn
  have hker : ∀ ts k, genSlotKer P.L P.γ P.δ p a J pat t s σ kSel Rs h roots Rf dag (.inr β) ts k =
      kernelLeavesW P.L P.γ P.δ N Hn (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
        (fun k' => rowTopWeightR p (fun _ => gT) N ![qT] k' *
          (ProtDefs.filtWeight F (fun _ => false) M k' * ProtDefs.filtWeight Fu (fun _ => false) Mu k')) :=
    fun ts k => by
      unfold genSlotKer
      exact slotFn_chain_eq a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) J P.L σ kSel Rs
        P.γ P.δ p s h roots Rf dag (fixCap (MkSlots.recLG a) J pat t s) hcap β hsel (fixNative_none_of_not_pin hpin)
        ts k
  have hqq := tree_q'_le_q a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p hlay β
  have hbox := genBoxAt_chain_sub a J pat t s p hgeo' hpat' hroot ht hs β hqq
  have hlf : 0 ≤ slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a)
      (fun _ => b.toNNReal) (.inr β) := Finset.prod_nonneg fun _ _ => NNReal.coe_nonneg _
  have hG := genSlotMass_ge_base P (C := C) (by linarith) hb hL1 a J pat t s kSel Rs (.inr β)
    (selNative_eq_empty _ _ _ _ J kSel _ hselN)
  have hleaf : genLeaf a J b (.inr β) = slotLeaf a.prime.data a.prime.prime.1 (sourceLayer a)
      (sourceLayer_isLayering a) (fun _ => b.toNNReal) (.inr β) := rfl
  rw [hleaf] at hG
  have hX0 : ∀ e : ℕ, ∀ g : ℝ, 0 ≤ (C * Real.sqrt P.δ) ^ e * P.L ^ (-(P.η ^ 8) * g) := fun e g =>
    mul_nonneg (pow_nonneg (mul_nonneg (by linarith) (Real.sqrt_nonneg _)) _) (Real.rpow_nonneg (by linarith) _)
  have hLc0 : 0 ≤ P.L ^ c := Real.rpow_nonneg (by linarith) _
  have hsup : ∃ μ0 : ℝ≥0∞, μ0 ≤ ENNReal.ofReal (Kun P.d θ * P.L ^ c * genSlotMass P C b a J pat t s kSel Rs (.inr β)) ∧
      SupM θ (30 * P.d) (closure (timeBoxGt (clkL a p (.inr β) 0 : ℝ) (clkL a p (.inr β) 1)))
        (fun ts k => kernelLeavesW P.L P.γ P.δ N Hn (fun _ => ts 0) (ts 1) k (fun _ => 0) 0
          (fun k' => rowTopWeightR p (fun _ => gT) N ![qT] k' *
            (ProtDefs.filtWeight F (fun _ => false) M k' * ProtDefs.filtWeight Fu (fun _ => false) Mu k'))) μ0 := by
    by_cases hnil : a.prime.data.tree β = RegChain.nil
    · have hdecT : RegChain.nil.DecodesTree N.garden := by
        rw [← hnil]; exact tree_decodes _ _ _ _ β
      refine ⟨_, ?_, unTree_nil (θ := θ) hd P.L P.γ P.δ p gT (frontierConst P.d) hcF (hgP _) qT N hdecT Hn
        (nativeChainB a.prime.data a.prime.prime.1 (fun _ => b.toNNReal) β) _ F M Fu Mu⟩
      refine ENNReal.ofReal_le_ofReal (un_mass_triv ?_
        (mul_nonneg (le_trans zero_le_one (one_le_multD _ _ hd)) (by linarith))
        (Real.one_le_rpow hL1 hθ.c_nonneg) hlf ?_)
      · exact (le_max_right _ _).trans (le_max_right _ _)
      · refine le_trans ?_ hG
        have hs0 : slotSize a.prime.data (.inr β) = 0 := by
          show (a.prime.data.tree β).size = 0
          rw [hnil]; rfl
        have hi0 : slotIncoh a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) (.inr β) = 0 := by
          show N.incoherency ((a.prime.data.tree β).treeLinks (N.garden.sig 0)) = 0
          rw [hnil]; exact incoherency_nil _ _
        rw [hs0, hi0]
        simp only [pow_zero, Nat.cast_zero, mul_zero, Real.rpow_zero, one_mul]
        exact le_mul_of_one_le_left hlf (one_le_pow₀ hcF)
    · obtain ⟨n, hn⟩ := chain_size_even (a.prime.data.tree β)
      have hn2 : (a.prime.data.tree β).size = 2 * n := by omega
      have hn1 : 1 ≤ n := by
        have := chain_two_le _ hnil
        omega
      have hnN : n ≤ P.N (p + 1) ^ 4 := by
        have h1 := slotSize_le a.prime.data (.inr β)
        have h2 : slotSize a.prime.data (.inr β) = (a.prime.data.tree β).size := rfl
        omega
      have hcase : 1 ≤ N.incoherency ((a.prime.data.tree β).treeLinks (N.garden.sig 0)) ∨
          (N.incoherency ((a.prime.data.tree β).treeLinks (N.garden.sig 0)) = 0 ∧
            IsCoherentTreeAt p (clkL a p (.inr β) 0) (clkL a p (.inr β) 1) (a.prime.data.tree β) N) := by
        by_cases hg0 : N.incoherency ((a.prime.data.tree β).treeLinks (N.garden.sig 0)) = 0
        · exact Or.inr ⟨hg0, tree_coherent_at _ _ _ _ p hcan' β hg0⟩
        · exact Or.inl (Nat.one_le_iff_ne_zero.2 hg0)
      have hMF : ∀ c ∈ F, P.L ≤ M c := by
        intro c _
        show P.L ≤ 2 ^ _ * P.L
        exact le_mul_of_one_le_left (by linarith) (one_le_pow₀ (by norm_num))
      have hMFu : ∀ c ∈ Fu, P.L ≤ Mu c := fun c _ => hRs _
      have hm := unTree_main hI hC hd hL1 hη0 hη4 hc1 hδ hκ hθ C hCC hp hnN (a.prime.data.tree β)
        (a.prime.data.tree_wf β) hn2 hn1 N (tree_decodes _ _ _ _ β) (tree_noFlower _ _ _ _ β)
        (fun j => tree_lone_card _ _ _ _ β j) (fun z => hlay _) _ _ hqq (clkLayer_le _ _ _ p hlay _)
        (tree_root_layer_le _ _ _ _ p hlay β) (fun z hz => tree_lone_layer _ _ _ _ β z hz) hcase
        (IncTop.topSet p N ![qT]) (IncTop.topStar (fun _ => gT)) (fun _ => frontierConst P.d) (fun _ _ => by linarith)
        (fun z _ => IncTop.topStar_presented _ (fun _ => hgP _) z) F M hMF Fu Mu hMFu Hn _ hctrlN _
        (fun κ => norm_d5M_top_le p N ![qT] (fun _ => gT) (frontierConst P.d) hcF
          (fun _ x => GPresented.norm_le (hgP _) (by linarith) x) F M Fu Mu κ)
      have hf : (fun k' => rowTopWeightR p (fun _ => gT) N ![qT] k' *
            (ProtDefs.filtWeight F (fun _ => false) M k' * ProtDefs.filtWeight Fu (fun _ => false) Mu k')) =
          d5M (IncTop.topSet p N ![qT]) (IncTop.topStar (fun _ => gT)) F M Fu Mu := by
        funext k'
        unfold d5M
        rw [IncTop.rowTopWeightR_eq_starWeight, mul_assoc]
      rw [hf]
      refine ⟨_, ?_, hm⟩
      refine ENNReal.ofReal_le_ofReal (un_mass_chain
        (nrp := frontierConst P.d ^ slotNr a.prime.data a.prime.prime.1 (.inr β)) (le_max_right _ _ |>.trans (le_max_left _ _))
        ENNReal.toReal_nonneg ?_ (Finset.prod_nonneg fun _ _ => by linarith) hLc0 (hX0 _ _) hlf ?_)
      · rw [Finset.prod_const]
        refine pow_le_pow_right₀ hcF ?_
        refine (Finset.card_le_card (topSet_sub_treeNodes p N _)).trans ?_
        exact treeExp_le_slotNr a.prime.data a.prime.prime.1 (sourceLayer a) (sourceLayer_isLayering a) p β
      · exact hG
  obtain ⟨μ0, hμ0, hsup⟩ := hsup
  obtain ⟨Λ, hcnt, wt, m, amp, h1, h2, h3, h4, h5⟩ := hsup
  refine ⟨Λ, hcnt, wt, m, fun _ => 0, amp, h1, h2, fun l k => snorm_le_one_pointwise _ _ (h3 l) k, h3,
    fun q hq => absurd hq (by simp), fun ts hts nn _ _ _ => ?_, h5.trans hμ0⟩
  rw [hker]
  exact h4 ts (hbox hts) _

end Slot

end WaveTurbulence.Flower.MkSlotsO

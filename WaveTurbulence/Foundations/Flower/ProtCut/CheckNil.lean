/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootNilCut

/-! # D2c PROT-CUT: one-pair chains — configuration forms, existence, multiplier, checks

* `PairOnly.of_cutTerm`, `PairOnly.exists_of_wf`: the pieces exist (the terminal-cut data with empty prefix).
* `kernelProt_rootTerm_cfg` ((P2), `ProtCfg.rootTerm`), `kernelProt_root0_cfg` ((P1) with `rest = nil`).
* `PairOnly.multFactors_local`: a branch-local multiplier factors.
* `PairOnly.incoherency_of_chainIn`: the incoherency indices add. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- The terminal-cut data with an empty prefix are one-pair data. -/
theorem PairOnly.of_cutTerm {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner : RegChain} (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg) :
    PairOnly LG m Qr Qg inner LGi LGr LGg :=
  ⟨C.dec, C.decI, C.sigI, C.decR, C.decG, fun z => by simpa [RegChain.lonePath] using C.layI z,
    fun z => by simpa [RegChain.lonePath] using C.layR z, fun z => by simpa [RegChain.lonePath] using C.layG z⟩

/-- **The pieces of a one-pair protected tree exist.** -/
theorem PairOnly.exists_of_wf (LG : LayeredGarden 1) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain)
    (hX : (cpair m Qr Qg inner).DecodesTree LG.garden) (hwf : (cpair m Qr Qg inner).wf = true) :
    ∃ (LGi : LayeredGarden 1) (LGr LGg : LayeredGarden 2), PairOnly LG m Qr Qg inner LGi LGr LGg := by
  obtain ⟨LGp, LGi, LGr, LGg, C⟩ := CutTermData.exists_of_wf LG .nil m Qr Qg inner hX hwf
  exact ⟨LGi, LGr, LGg, PairOnly.of_cutTerm C⟩

/-- The incoherency indices of a one-pair protected tree add (through the terminal-cut data). -/
theorem PairOnly.incoherency_of_chainIn {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2}
    {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} {p : ℕ}
    (C : CutTermData LG .nil m Qr Qg inner LGp LGi LGr LGg) (hch : ChainIn p (cpair m Qr Qg inner) LG) :
    LG.incoherency ((cpair m Qr Qg inner).treeLinks (LG.garden.sig 0)) =
      LGi.incoherency (inner.treeLinks (LGi.garden.sig 0)) + LGr.incoherency Qr.links +
        LGg.incoherency Qg.links := by
  have h := C.incoherency_cutTerm_of_chainIn hch
  have h0 : LGp.incoherency (RegChain.nil.treeLinks (LGp.garden.sig 0)) = 0 := by
    simp [RegChain.treeLinks, RegChain.linksAt, LayeredGarden.incoherency]
  rw [h0, zero_add] at h
  exact h

namespace PairOnly

variable {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg)
include D

theorem bstar_rootB {d : ℕ} (K : GNode LG.garden.tree → Mom d) :
    (fun i => extend K (aAddr .nil i)) = bstar K D.hp.rootB := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact extend_node K D.hp.rootB.toNode
  · exact extend_node K (D.hp.rootB.child j)

theorem bstar_bB {d : ℕ} (K : GNode LG.garden.tree → Mom d) :
    (fun i => extend K (bAddr .nil m inner i)) = bstar K D.hp.bB := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · have e : bAddr .nil m inner 0 = D.hp.bB.toNode.1 := by
      simp only [bAddr, RegChain.lonePath, List.nil_append, Fin.cases_zero] <;> rfl
    rw [e]
    exact extend_node K D.hp.bB.toNode
  · have e : bAddr .nil m inner j.succ = (D.hp.bB.child j).1 := by
      simp only [bAddr, RegChain.lonePath, List.nil_append, Fin.cases_succ] <;> rfl
    rw [e]
    exact extend_node K (D.hp.bB.child j)

/-- **A branch-local multiplier factors at the pair.** -/
theorem multFactors_local {d : ℕ} (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) :
    D.MultFactors (fun K => ∏ b, f b (bstar K b))
      (fun A B => f D.hp.rootB A * f D.hp.bB B)
      (fun K => ∏ x, f (D.hp.βi x) (bstar K x))
      (fun K => ∏ y, f (D.hp.βr y) (bstar K y))
      (fun K => ∏ y, f (D.hp.βg y) (bstar K y)) := by
  intro K
  simp only
  rw [D.bstar_rootB K, D.bstar_bB K, D.hp.prod_pairBranch]
  have hi : ∀ x, bstar K (D.hp.βi x) = bstar (K ∘ D.hp.ιi) x := by
    intro x; funext i; exact Fin.cases rfl (fun j => rfl) i
  have hr : ∀ y, bstar K (D.hp.βr y) = bstar (K ∘ D.hp.ιr) y := by
    intro y; funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg K (D.hp.βr_child y j)
  have hg : ∀ y, bstar K (D.hp.βg y) = bstar (K ∘ D.hp.ιg) y := by
    intro y; funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact congrArg K (D.hp.βg_child y j)
  simp only [hi, hr, hg]

end PairOnly

/-- (P2) in D3's configuration form: `ProtCfg.rootTerm` on a one-pair chain (root at `t`, terminal at `s`). -/
theorem kernelProt_rootTerm_cfg {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mi Mr Mg) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM)
    (T s' s t : ℝ) (htT : t ≤ T) (hsT : s ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.rootTerm.fix (cpair m Qr Qg inner) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          (cutPh m (LG.garden.sig 0) L γ δ k s e t *
            (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => t) s (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) t s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) t s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_rootTerm_fix]
  exact D.kernelProt_both L γ δ H hH M Mc Mi Mr Mg hM CM hMc hMi hMr hMg T s' t s htT hsT k

/-- (P1)/(trace) for a one-pair chain in D3's configuration form `ProtCfg.root` (root at `t ≤ T`). -/
theorem kernelProt_root0_cfg {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mi Mr Mg) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM)
    (T s t : ℝ) (htT : t ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s (ProtCfg.root.fix (cpair m Qr Qg inner) s t T) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU0 LG m inner T t s, cutPh m (LG.garden.sig 0) L γ δ k u e t *
            (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => t) u (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) t u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) t u y.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0)) := by
  rw [cfg_root_fix]
  exact D.kernelProt_root0 L γ δ H hH M Mc Mi Mr Mg hM CM hMc hMi hMr hMg T s t htT k

#print axioms PairOnly.kernelProt_both
#print axioms PairOnly.kernelProt_root0
#print axioms kernelProt_rootTerm_cfg
#print axioms kernelProt_root0_cfg
#print axioms PairOnly.exists_of_wf
#print axioms PairOnly.incoherency_of_chainIn
#print axioms PairOnly.multFactors_local

end WaveTurbulence.Flower.ProtCut

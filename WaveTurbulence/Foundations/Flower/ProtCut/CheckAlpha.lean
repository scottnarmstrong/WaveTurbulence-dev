/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.MultLocal

/-! # D2c PROT-CUT: the pieces of every protected object, exact-type checks and axioms (milestone MK-α)

* `cutTerm_pieces`: a protected paired tree (`ProtShape`, `w = 1`) with a nonempty lone path has its terminal cut
  (`X = appendChain Xp (pair m Qr Qg inner nil)` and `CutTermData`).
* `cap_pieces`: a protected cap couple (`w = 2`) has its paired tree (`CapData`, `ProtShape` there, same size and
  incoherency). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **The terminal cut of a protected paired tree exists.** -/
theorem cutTerm_pieces {p : ℕ} {X : RegChain} {LG : LayeredGarden 1} (h : ProtShape p X LG)
    (hne : X.lonePath ≠ []) :
    ∃ (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain),
      X = appendChain Xp (cpair m Qr Qg inner) ∧
      ∃ (LGp LGi : LayeredGarden 1) (LGr LGg : LayeredGarden 2), CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg := by
  obtain ⟨Xp, m, Qr, Qg, inner, rfl⟩ := exists_last_pair X (ne_nil_of_lonePath hne)
  exact ⟨Xp, m, Qr, Qg, inner, rfl, CutTermData.exists_of_wf LG Xp m Qr Qg inner h.2.1 h.1⟩

/-- **A protected cap couple is its paired tree times one input**, with the same protected data. -/
theorem cap_pieces {p : ℕ} {X : RegChain} {LG : LayeredGarden 2} (h : ProtShape p X LG) :
    ∃ LG1 : LayeredGarden 1, CapData X LG LG1 ∧ ProtShape p X LG1 ∧ protSize X LG = protSize X LG1 ∧
      protIncoh X LG = protIncoh X LG1 := by
  obtain ⟨LG1, D⟩ := CapData.exists_of_decodes h.2.1
  exact ⟨LG1, D, D.protShape_cap h, CapData.protSize_cap, D.protIncoh_cap⟩

/-! ### Exact-type checks -/

/-- D3's multiplier, for a protected paired tree, in `kernelProt_term_cut`. -/
example {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg) {d : ℕ}
    (S : Finset (GNode LG.garden.tree)) (hS : ∀ a ∈ S, a.1.2 ∈ (LG.garden.tree a.1.1).branching)
    (ω : GNode LG.garden.tree → IncTop.Star d → ℂ) (F Fu : Finset (GBranch LG.garden.tree))
    (M Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) :
    ∃ Mc Mp Mi Mr Mg, D.MultFactors (fun κ => IncTop.starWeight S ω κ * filtWeight F (fun _ => false) M κ *
      filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) Mc Mp Mi Mr Mg :=
  ⟨_, _, _, _, _, D.multFactors_D3 S hS ω F (fun _ => false) M Fu Mu ind hind⟩

/-- The (cut-term) of a cap couple in D3's configuration form. -/
example {LG : LayeredGarden 2} {LG1 : LayeredGarden 1}
    {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    (D : CapData (appendChain Xp (cpair m Qr Qg inner)) LG LG1)
    (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (s t T s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t T) k
        (fun _ => 0) 0 =
      (H ((0 : Fin 2), (appendChain Xp (cpair m Qr Qg inner)).lonePath) k : ℂ) *
        kernelProt L γ δ LG1 (capH H) (D.capM M) (fun _ => T) 0
          (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t T) k (fun _ => 0) 0 := by
  rw [D.kernelProt_cap, D.cfg_fix_cap]

#print axioms cutTerm_pieces
#print axioms cap_pieces
#print axioms CapData.kernelProt_cap
#print axioms kernelProt_term_cut_cap
#print axioms CutTermData.multFactors_local
#print axioms CutTermData.multFactors_local_bound
#print axioms CutTermData.multFactors_D3
#print axioms CapData.multFactors_D3_cap
#print axioms protTime_transport

end WaveTurbulence.Flower.ProtCut

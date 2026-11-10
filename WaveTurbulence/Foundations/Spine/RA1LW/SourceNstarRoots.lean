/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourceMiniRoots
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.BinaryMomentum

/-! # Literal Nstar recursion at its original selected child roots -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Reg TTree

/-- The original recursive Nstar at a consecutive pair has exactly the
same selected roots and binary kernel as the actual source root calculation. -/
theorem Nstar_pair_nil_roots {d w : ℕ} (H : Fin w × TTree.Path → Mom d → ℝ)
    (m : MiniTreeCode) (Qr Qg : RegCpl) (rest : RegChain)
    (Z : Finset (Fin w × Path)) (ζ : ℤˣ) (a : Fin w × Path) (k : Mom d) :
    LGSpine.LeafApp.chainNstar H Z (RegChain.pair m Qr Qg .nil rest) ζ a k =
    (if a∈Z then pvResonantIntegral
        (binaryMomentumFunction m.c
          (LGSpine.LeafApp.cplMstar H Z Qr (miniRedRoots m ζ a).1 (miniRedRoots m ζ a).2)
          (LGSpine.LeafApp.cplMstar H Z Qg (miniGreenRoots m ζ a).1 (miniGreenRoots m ζ a).2)) k
      else resIntegral
        (binaryMomentumFunction m.c
          (LGSpine.LeafApp.cplMstar H Z Qr (miniRedRoots m ζ a).1 (miniRedRoots m ζ a).2)
          (LGSpine.LeafApp.cplMstar H Z Qg (miniGreenRoots m ζ a).1 (miniGreenRoots m ζ a).2)) k) *
      LGSpine.LeafApp.chainNstar H Z rest (slotSign (slotSign ζ m.c) m.lone) (addrExt a [m.c,m.lone]) k := by
  classical
  have hbin (f g : Mom d → ℝ) : binaryMomentumFunction m.c f g =
      fun k₁ k₂ k₃ => f (![k₁,k₂,k₃] m.red.1)*g (![k₁,k₂,k₃] m.green.1) := by
    funext k₁ k₂ k₃
    exact binaryMomentumFunction_eq_miniTree m f g k₁ k₂ k₃
  simp only [LGSpine.LeafApp.chainNstar,RegChain.lonePath,List.append_nil,List.cons_append,List.nil_append,
    mul_one,miniRedRoots,miniGreenRoots]
  split_ifs <;> rw [hbin]

/-- Root placement preserves the literal number of source links. -/
theorem linksAt_length_eq_links {w : ℕ} (Q : RegCpl) (a b : Fin w × Path) :
    (Q.linksAt a b).length = Q.links.length := by
  rw [cpl_links_rootPlacement,List.length_map]

end WaveTurbulence.RA1Leafwise

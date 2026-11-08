/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootP3Cut

/-! # D2c PROT-CUT: (P3) in configuration form, checks and axioms -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- (P3) in D3's configuration form `ProtCfg.rootTerm` on `X = pair m Qr Qg inner rest` (`rest ≠ nil`, root at
`t ≤ T`, terminal at `s`). -/
theorem kernelProt_rootTerm_cfg3 {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode}
    {Qr Qg : RegCpl} {inner rest : RegChain} (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg)
    (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (Ms : (GNode LGs.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg Ms) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM)
    (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (hMs : ∀ K, ‖Ms K‖ ≤ CM)
    (T s' s t : ℝ) (htT : t ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.rootTerm.fix (RegChain.pair m Qr Qg inner rest) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU3 LG m inner T t s, cutPh m (LG.garden.sig 0) L γ δ k u e t *
            (kernelProt L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s' (ProtCfg.term.fix rest s t u) k
                (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => t) u (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) t u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) t u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_rootTerm_fix' m Qr Qg inner rest D.rest_ne]
  exact D.kernelProt_rootCut3 L γ δ H hH M Mc Mi Mr Mg Ms hM CM hMc hMi hMr hMg hMs T s' t s htT k

#print axioms RootData.kernelProt_rootCut3
#print axioms kernelProt_rootTerm_cfg3
#print axioms protDom_glue_free'
#print axioms lt_of_free_ancestor

end WaveTurbulence.Flower.ProtCut

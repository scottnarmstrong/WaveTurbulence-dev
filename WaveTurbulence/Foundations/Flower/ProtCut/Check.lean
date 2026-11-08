/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutExists

/-! # D2c PROT-CUT: exact-type checks and axioms of the exports -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- (cut-term) in the configuration form `ProtCfg.term.fix X s t T` consumed by D3. -/
theorem kernelProt_term_cut {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
    {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
    (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (s t T s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
            (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [termFix_eq_cfg]
  exact D.kernelProt_cutTerm L γ δ H hH M Mc Mp Mi Mr Mg hM CM hMc hMp hMi hMr hMg T s s' k

end WaveTurbulence.Flower.ProtCut

open WaveTurbulence.Flower.ProtCut in
#print axioms CutTermData.kernelProt_cutTerm
open WaveTurbulence.Flower.ProtCut in
#print axioms kernelProt_term_cut
open WaveTurbulence.Flower.ProtCut in
#print axioms CutTermData.incoherency_cutTerm_of_chainIn
open WaveTurbulence.Flower.ProtCut in
#print axioms CutTermData.exists_of_wf
open WaveTurbulence.Flower.ProtCut in
#print axioms size_cutTerm
open WaveTurbulence.Flower.ProtCut in
#print axioms protTime_pin
open WaveTurbulence.Flower.ProtCut in
#print axioms link_cancel

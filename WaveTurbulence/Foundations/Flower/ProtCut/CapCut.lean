/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CapKer
public import WaveTurbulence.Foundations.Flower.ProtCut.Check

/-! # D2c PROT-CUT: (cut-term) for every protected object

* `exists_last_pair`: a nonempty chain is `appendChain Xp (pair m Qr Qg inner nil)`.
* **`kernelProt_term_cut_cap`**: (cut-term) for a cap couple (`w = 2`): the input of the lone leaf times the
  paired-tree identity `kernelProt_term_cut` (pieces of the paired tree `LG1`, multiplier `D.capM M`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **The last pair of a chain**: a nonempty chain ends with a closing pair. -/
theorem exists_last_pair : ∀ X : RegChain, X ≠ .nil →
    ∃ (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain),
      X = appendChain Xp (cpair m Qr Qg inner)
  | .nil, h => absurd rfl h
  | .pair m Qr Qg inner .nil, _ => ⟨.nil, m, Qr, Qg, inner, rfl⟩
  | .pair m Qr Qg inner (.pair m' Qr' Qg' inner' rest'), _ => by
      obtain ⟨Xp, m'', Qr'', Qg'', inner'', h⟩ :=
        exists_last_pair (.pair m' Qr' Qg' inner' rest') (by simp)
      exact ⟨.pair m Qr Qg inner Xp, m'', Qr'', Qg'', inner'', by rw [h]; rfl⟩

/-- A protected object with a nonempty lone path has a nonempty chain. -/
theorem ne_nil_of_lonePath {X : RegChain} (h : X.lonePath ≠ []) : X ≠ .nil := by
  rintro rfl
  exact h rfl

/-- **(cut-term) for a cap couple.** `X = appendChain Xp (pair m Qr Qg inner nil)`, `LG` its cap couple, `LG1` the
paired tree (`CapData`) with its terminal-cut pieces (`CutTermData`). The cap couple's kernel with the terminal node
pinned at `s` is the lone-leaf input `H (0, X.lonePath) k` times the paired-tree (cut-term) expression. -/
theorem kernelProt_term_cut_cap {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2}
    {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    (D : CapData (appendChain Xp (cpair m Qr Qg inner)) LG LG1)
    (C : CutTermData LG1 Xp m Qr Qg inner LGp LGi LGr LGg)
    (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : C.MultFactors (D.capM M) Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM)
    (hMp : ∀ K, ‖Mp K‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM)
    (s t T s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.term.fix (appendChain Xp (cpair m Qr Qg inner)) s t T) k
        (fun _ => 0) 0 =
      (H ((0 : Fin 2), (appendChain Xp (cpair m Qr Qg inner)).lonePath) k : ℂ) *
      ((coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG1.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG1.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG1 Xp T s, cutPh m (LG1.garden.sig 0) L γ δ k s e u *
            (kernelProt L γ δ LGp (cutHp (capH H)) Mp (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi Xp m (capH H)) Mi (fun _ => u) s (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr Xp m inner (LG1.garden.sig 0) (capH H)) Mr
                    (fun y => cupR m inner (LG1.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg Xp m inner (LG1.garden.sig 0) (capH H)) Mg
                    (fun y => cupG m inner (LG1.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0)))) := by
  rw [D.kernelProt_cap, D.cfg_fix_cap]
  congr 1
  exact kernelProt_term_cut C L γ δ (capH H) (D.hH_cap L H hH) (D.capM M) Mc Mp Mi Mr Mg hM CM hMc hMp hMi hMr hMg
    s t T 0 k

end WaveTurbulence.Flower.ProtCut

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutP5P7

/-! # D2c-2 PROT-CUT: (P5) and (P7) on `kernelProt`, in D3's configuration forms

* **`kernelProt_penTerm_cfg5`** ((P5): `ProtCfg.penTerm`, nonempty interior): (cut-term) with the interior piece
  carrying `ProtCfg.term.fix inner s t u`.
* **`kernelProt_termChild_cfg`** ((P7): `ProtCfg.termChild i`): (cut-term) with the side-couple pieces carrying
  `sideFix` (the root of the side-couple tree at `bPath m inner ++ [i]` designated at `s`; `sideFix_eq_trFix`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **(P5) on `kernelProt`** (o104 Prop 7.3 (P5)): `penTerm` with a nonempty interior. The interior piece carries its
own terminal designation at `s`; (cut-term) (`kernelProt_term_cut` with code `inner`) then cuts it. -/
theorem kernelProt_penTerm_cfg5 {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
    {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
    (hin : inner.lonePath ≠ []) (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (s t T s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s' (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
            (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (ProtCfg.term.fix inner s t u)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_penTerm_fix5 Xp m Qr Qg inner hin]
  have h := D.kernelProt_cutPin (p5Fix_cutPinFix Xp m inner s) L γ δ H hH M Mc Mp Mi Mr Mg hM CM hMc hMp hMi hMr
    hMg T s' k
  rw [D.p5_βI hin s t T, D.p5_βR hin s, D.p5_βG hin s] at h
  exact h

/-- **(P7) on `kernelProt`** (o104 Prop 7.3 (P7)): `termChild i`. The side-couple pieces carry `sideFix`, the root of
the side-couple tree hanging at the child `i` of `𝔫_b` designated at `s`, its upper clock (`cupR … u s j = s`):
the root trace `Q₁^m(u, s)` (o104 Prop 7.4). -/
theorem kernelProt_termChild_cfg {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain}
    {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
    (i : Fin 3) (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mp Mi Mr Mg) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMp : ∀ K, ‖Mp K‖ ≤ CM)
    (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (s t T s' : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s'
        ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t T) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s e u *
            (kernelProt L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0
                    (sideFix (rBase m inner (LG.garden.sig 0)) (bPath m inner ++ [i]) s)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0
                    (sideFix (gBase m inner (LG.garden.sig 0)) (bPath m inner ++ [i]) s)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_termChild_fix]
  have h := D.kernelProt_cutPin (p7Fix_cutPinFix Xp m inner i s) L γ δ H hH M Mc Mp Mi Mr Mg hM CM hMc hMp hMi
    hMr hMg T s' k
  rw [D.p7_βI i s, D.p7_βR i s, D.p7_βG i s] at h
  exact h

/-- In (P7) the designated side-couple root is at its own upper clock: `cupR … u s j = s` for the tree `j` hanging at
`bPath m inner ++ [i]`. -/
theorem cupR_of_bot {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {j : Fin 2} {i : Fin 3}
    (hj : rBase m inner ζ j = bPath m inner ++ [i]) (u s : ℝ) : cupR m inner ζ u s j = s := by
  unfold cupR
  rw [if_neg]
  rw [hj]
  intro h
  have := congrArg List.length h
  simp [bPath] at this

theorem cupG_of_bot {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {j : Fin 2} {i : Fin 3}
    (hj : gBase m inner ζ j = bPath m inner ++ [i]) (u s : ℝ) : cupG m inner ζ u s j = s := by
  unfold cupG
  rw [if_neg]
  rw [hj]
  intro h
  have := congrArg List.length h
  simp [bPath] at this

end WaveTurbulence.Flower.ProtCut

open WaveTurbulence.Flower.ProtCut in
#print axioms CutTermData.protTime_cutPin
open WaveTurbulence.Flower.ProtCut in
#print axioms CutTermData.kernelProt_cutPin
open WaveTurbulence.Flower.ProtCut in
#print axioms kernelProt_penTerm_cfg5
open WaveTurbulence.Flower.ProtCut in
#print axioms kernelProt_termChild_cfg
open WaveTurbulence.Flower.ProtCut in
#print axioms sideFix_eq_trFix

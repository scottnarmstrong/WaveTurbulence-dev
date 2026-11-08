/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Root2Sw
public import WaveTurbulence.Foundations.Flower.ProtCut.T2pKer
public import WaveTurbulence.Foundations.Flower.ProtCut.SwGlueExist
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckP5P7

/-! # D2c-3 PROT-CUT: exact-type checks and axioms of the continuation's exports

* (P7) with a type-1 side couple: the side-couple piece of `kernelProt_termChild_cfg` (designation
  `sideFix (rBase …) (bPath … ++ [i]) s`, clocks `cupR … u s`) is cut by o104 Prop 7.4 (b) (`kernelProt_t1Trace`),
  with the traced root at its own clock `s` and the partner below `u`.
* D3's branch-local multipliers satisfy the multiplier hypotheses of (b), (c), (a). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- **(P7) + o104 Prop 7.4 (b)**: the red side-couple piece of (P7), when the side couple is of type 1 and its tree `j`
hangs at the child `i` of `𝔫_b` (exact type). -/
example {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {j : Fin 2} {i : Fin 3}
    (hj : rBase m inner ζ j = bPath m inner ++ [i]) {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl}
    {LGr LG₁ LG₂ LG₃ : LayeredGarden 2} (h : T1Data c Q₁ Q₂ Q₃ LGr.garden LG₁.garden LG₂.garden LG₃.garden)
    (hlA : ∀ z, LG₁.layer z = LGr.layer (h.ιA z)) (hlB : ∀ z, LG₂.layer z = LGr.layer (h.ιB z))
    (hlC : ∀ z, LG₃.layer z = LGr.layer (h.ιC z)) (L γ δ : ℝ) {d : ℕ} (Hr : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LGr.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |Hr ℓ.1 (k' + latticePoint L n)|)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (M₁ : (GNode LG₁.garden.tree → Mom d) → ℂ) (M₂ : (GNode LG₂.garden.tree → Mom d) → ℂ)
    (M₃ : (GNode LG₃.garden.tree → Mom d) → ℂ) (hM : h.MultFactors Mr Mc M₁ M₂ M₃) (CM : ℝ)
    (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hM₁ : ∀ K, ‖M₁ K‖ ≤ CM) (hM₂ : ∀ K, ‖M₂ K‖ ≤ CM) (hM₃ : ∀ K, ‖M₃ K‖ ≤ CM)
    (u s : ℝ) (k : Mom d) :
    kernelProt L γ δ LGr Hr Mr (fun y => cupR m inner ζ u s y.1.1) 0
        (sideFix (rBase m inner ζ) (bPath m inner ++ [i]) s) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 *
        ∑' e : T1E d, Mc (t1Star c L k e 0) (t1Star c L k e 1) * (t1Eps c e : ℂ) *
          ∫ u' in t1U LGr (t1sw j) (cupR m inner ζ u s (t1sw j)), t1Ph (LGr.garden.sig j) L γ δ k e s u' *
            (kernelProt L γ δ LG₁ (t1HA c Hr) M₁ (fun x => t1Clock j s u' x.1.1) 0 (fun _ => none)
                (k + latticePoint L e.1.1) (fun _ => 0) 0 *
              (kernelProt L γ δ LG₂ (t1HB Hr) M₂ (fun x => t1Clock j s u' (t1sw x.1.1)) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                kernelProt L γ δ LG₃ (t1HC c Hr) M₃ (fun x => t1Clock j s u' x.1.1) 0 (fun _ => none)
                  (k + latticePoint L e.1.2.2) (fun _ => 0) 0)) := by
  rw [sideFix_eq_trFix (rBase_injective m inner ζ) hj s]
  exact h.kernelProt_t1Trace L γ δ Hr hH Mr Mc M₁ M₂ M₃ hM CM hMc hM₁ hM₂ hM₃ (cupR m inner ζ u s) 0 j s
    (cupR_of_bot hj u s).symm.le hlA hlB hlC k

/-- D3's branch-local multiplier on a type-1 couple (exact type of `T1Data.multFactors_local`). -/
example {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {LG LG₁ LG₂ LG₃ : LayeredGarden 2}
    (h : T1Data c Q₁ Q₂ Q₃ LG.garden LG₁.garden LG₂.garden LG₃.garden) {d : ℕ}
    (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) :
    h.MultFactors (fun K => ∏ b, f b (bstar K b)) (fun A B => f (h.rt 0) A * f (h.rt 1) B)
      (fun K => ∏ x, f (h.βA x) (bstar K x)) (fun K => ∏ x, f (h.βB x) (bstar K x))
      (fun K => ∏ x, f (h.βC x) (bstar K x)) :=
  h.multFactors_local f

/-- **(P7) + o104 Prop 7.4 (a)**: the red side-couple piece of (P7), when the side couple is of type 2 with a nonempty
`+` chain and its tree `0` hangs at the child `i` of `𝔫_b` (exact type). -/
example {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {i : Fin 3}
    (hj : rBase m inner ζ 0 = bPath m inner ++ [i]) {m' : MiniTreeCode} {Qr' Qg' : RegCpl} {inner' : RegChain}
    {LGr : LayeredGarden 2} {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2}
    (D : Root2Data LGr m' Qr' Qg' inner' LGZ LGB) {LGi : LayeredGarden 1} {LGr' LGg' : LayeredGarden 2}
    (P : PairOnly LGZ m' Qr' Qg' inner' LGi LGr' LGg') (L γ δ : ℝ) {d : ℕ} (Hr : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LGr.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |Hr ℓ.1 (k' + latticePoint L n)|)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (MZ : (GNode LGZ.garden.tree → Mom d) → ℂ)
    (MB : (GNode LGB.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr' : (GNode LGr'.garden.tree → Mom d) → ℂ)
    (Mg' : (GNode LGg'.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, Mr K = MZ (K ∘ D.gd.ι₁) * MB (K ∘ D.gd.ι₂)) (hMZ : P.MultFactors MZ Mc Mi Mr' Mg') (CM : ℝ)
    (hMB : ∀ K, ‖MB K‖ ≤ CM) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr' K‖ ≤ CM)
    (hMgb : ∀ K, ‖Mg' K‖ ≤ CM) (u s : ℝ) (k : Mom d) :
    kernelProt L γ δ LGr Hr Mr (fun y => cupR m inner ζ u s y.1.1) 0
        (sideFix (rBase m inner ζ) (bPath m inner ++ [i]) s) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LGZ.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LGZ.garden.sig 0) m'.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m' d, Mc (starA m' L k e) (starB m' L k e) * (cutEps m' e : ℂ) *
          ∫ u' in root2U LGr m' inner' (cupR m inner ζ u s 0) s, cutPh m' (LGZ.garden.sig 0) L γ δ k u' e s *
            (kernelProt L γ δ LGB (t2HQ (cpair m' Qr' Qg' inner') Hr) MB
                (fun y => bClock (cupR m inner ζ u s) u' y.1.1) 0 (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m' (t2HX Hr)) Mi (fun _ => s) u' (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr' (cutHr .nil m' inner' (LGZ.garden.sig 0) (t2HX Hr)) Mr'
                    (fun y => cupR m' inner' (LGZ.garden.sig 0) s u' y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg' (cutHg .nil m' inner' (LGZ.garden.sig 0) (t2HX Hr)) Mg'
                    (fun y => cupG m' inner' (LGZ.garden.sig 0) s u' y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [sideFix_eq_trFix (rBase_injective m inner ζ) hj s]
  exact D.kernelProt_root2 P L γ δ Hr hH Mr MZ MB Mc Mi Mr' Mg' hMg hMZ CM hMB hMc hMi hMr hMgb
    (cupR m inner ζ u s) 0 s (cupR_of_bot hj u s).symm.le k

end WaveTurbulence.Flower.ProtCut

open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.decEquiv
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.prod_inputLeaves_t1
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.phase_t1
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.summand_t1Trace
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.kernelProt_t1Trace
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.exists_of_decodes
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.multFactors_local
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.multFactors_local_bound
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.protTime_t2mGlue
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.summand_t2m
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.kernelProt_t2m
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.exists_of_decodes
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.multFactors_local
open WaveTurbulence.Flower.ProtCut in
#print axioms protDom_glue_free2
open WaveTurbulence.Flower.ProtCut in
#print axioms Root2Data.protTime_root2
open WaveTurbulence.Flower.ProtCut in
#print axioms Root2Data.summand_root2
open WaveTurbulence.Flower.ProtCut in
#print axioms Root2Data.kernelProt_root2
open WaveTurbulence.Flower.ProtCut in
#print axioms Root2Data.exists_of_decodes
open WaveTurbulence.Flower.ProtCut in
#print axioms Root2Data.multFactors_local
open WaveTurbulence.Flower.ProtCut in
#print axioms Root2Data.of_decodes
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.of_decodes
open WaveTurbulence.Flower.ProtCut in
#print axioms swGarden
open WaveTurbulence.Flower.ProtCut in
#print axioms kernelProt_sw
open WaveTurbulence.Flower.ProtCut in
#print axioms protSummand_sw
open WaveTurbulence.Flower.ProtCut in
#print axioms protTime_sw
open WaveTurbulence.Flower.ProtCut in
#print axioms swDec
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.hs
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.hg
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.toRoot2
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.kernelProt_root2m
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.kernelProt_bottom
open WaveTurbulence.Flower.ProtCut in
#print axioms kernelProt_sw_back
open WaveTurbulence.Flower.ProtCut in
#print axioms protSummand_sw_back
open WaveTurbulence.Flower.ProtCut in
#print axioms T1Data.summand_t1Both
open WaveTurbulence.Flower.ProtCut in
#print axioms T2mData.summand_t2mGlue
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.toT2m
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.summand_t2p
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.kernelProt_t2p
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.exists_of_decodes
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.exists_of_decodes_nil
open WaveTurbulence.Flower.ProtCut in
#print axioms swM_local
open WaveTurbulence.Flower.ProtCut in
#print axioms SwGlueData.multFactors_local_t2p

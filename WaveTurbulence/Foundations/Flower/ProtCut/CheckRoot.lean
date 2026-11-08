/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.RootIncoh

/-! # D2c PROT-CUT: the root cut in configuration form, cap couples, checks and axioms

* `kernelProt_root_cfg`, `kernelProt_trace_cfg`: (P1)/(trace) with `ProtCfg.root.fix X s t T`,
  `ProtCfg.trace.fix X s t T` (root at `t`, resp. at the upper time `T`).
* `kernelProt_root_cap`: a cap couple with its root designated is the lone-leaf input times the root cut of its
  paired tree (lone-port time `0`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {LG LGZ LGi LGs : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
  {inner rest : RegChain}

/-- (P1) in D3's configuration form: `ProtCfg.root` (root at `t ≤ T`). -/
theorem kernelProt_root_cfg (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (Ms : (GNode LGs.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg Ms) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM)
    (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (hMs : ∀ K, ‖Ms K‖ ≤ CM)
    (T s t : ℝ) (htT : t ≤ T) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s (ProtCfg.root.fix (RegChain.pair m Qr Qg inner rest) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU LG m inner T t, cutPh m (LG.garden.sig 0) L γ δ k u e t *
            (kernelProt L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => t) u (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) t u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) t u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_root_fix]
  exact D.kernelProt_rootCut L γ δ H hH M Mc Mi Mr Mg Ms hM CM hMc hMi hMr hMg hMs T s t htT k

/-- (trace) in D3's configuration form: `ProtCfg.trace` (root at the upper time `T`). -/
theorem kernelProt_trace_cfg (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) (L γ δ : ℝ) {d : ℕ}
    (H : LeafProfiles 1 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (Ms : (GNode LGs.garden.tree → Mom d) → ℂ)
    (hM : D.MultFactors M Mc Mi Mr Mg Ms) (CM : ℝ) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM)
    (hMr : ∀ K, ‖Mr K‖ ≤ CM) (hMg : ∀ K, ‖Mg K‖ ≤ CM) (hMs : ∀ K, ‖Ms K‖ ≤ CM)
    (T s t : ℝ) (k : Mom d) :
    kernelProt L γ δ LG H M (fun _ => T) s (ProtCfg.trace.fix (RegChain.pair m Qr Qg inner rest) s t T) k
        (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LG.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LG.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in rootU LG m inner T T, cutPh m (LG.garden.sig 0) L γ δ k u e T *
            (kernelProt L γ δ LGs (rootHs m inner H) Ms (fun _ => u) s (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m H) Mi (fun _ => T) u (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr .nil m inner (LG.garden.sig 0) H) Mr
                    (fun y => cupR m inner (LG.garden.sig 0) T u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg .nil m inner (LG.garden.sig 0) H) Mg
                    (fun y => cupG m inner (LG.garden.sig 0) T u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [cfg_trace_fix]
  exact D.kernelProt_rootCut L γ δ H hH M Mc Mi Mr Mg Ms hM CM hMc hMi hMr hMg hMs T s T le_rfl k

/-- A cap couple with its root designated (`root`/`trace`): the lone-leaf input times the paired tree's root
configuration, which `kernelProt_root_cfg`/`kernelProt_trace_cfg` cut (lone-port time `0`). -/
theorem kernelProt_rootcfg_cap {X : RegChain} {LG2 : LayeredGarden 2} {LG1 : LayeredGarden 1}
    (D : CapData X LG2 LG1) (cfg : ProtCfg) (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (M : (GNode LG2.garden.tree → Mom d) → ℂ) (T s s' t : ℝ) (k : Mom d) :
    kernelProt L γ δ LG2 H M (fun _ => T) s' (cfg.fix X s t T) k (fun _ => 0) 0 =
      (H ((0 : Fin 2), X.lonePath) k : ℂ) *
        kernelProt L γ δ LG1 (capH H) (D.capM M) (fun _ => T) 0 (cfg.fix X s t T) k (fun _ => 0) 0 := by
  rw [D.kernelProt_cap, D.cfg_fix_cap]

/-! ### Exact-type check: D3's root multiplier factors -/

example (D : RootData LG m Qr Qg inner rest LGZ LGi LGs LGr LGg) {d : ℕ}
    (S : Finset (GNode LG.garden.tree)) (hS : ∀ a ∈ S, a.1.2 ∈ (LG.garden.tree a.1.1).branching)
    (ω : GNode LG.garden.tree → IncTop.Star d → ℂ) (F Fu : Finset (GBranch LG.garden.tree))
    (Mf Mu : GBranch LG.garden.tree → ℝ) :
    ∃ Mc Mi Mr Mg Ms, D.MultFactors (fun κ => IncTop.starWeight S ω κ * filtWeight F (fun _ => false) Mf κ *
      filtWeight Fu (fun _ => false) Mu κ * ((1 : ℝ) : ℂ)) Mc Mi Mr Mg Ms := by
  set f := fD3 S ω F (fun _ => false) Mf Fu Mu
  refine ⟨fun A B => f D.aR A * f D.bR B, fun K => ∏ x, f (D.gd.ofSum (.inl (D.hp.βi x))) (bstar K x),
    fun K => ∏ y, f (D.gd.ofSum (.inl (D.hp.βr y))) (bstar K y),
    fun K => ∏ y, f (D.gd.ofSum (.inl (D.hp.βg y))) (bstar K y),
    fun K => ∏ y, f (D.gd.ofSum (.inr y)) (bstar K y), fun K => ?_⟩
  have h := D.multFactors_local f K
  simp only at h ⊢
  rw [Complex.ofReal_one, mul_one, starFilt_local S hS]
  exact h

#print axioms RootData.kernelProt_rootCut
#print axioms kernelProt_root_cfg
#print axioms kernelProt_trace_cfg
#print axioms kernelProt_rootcfg_cap
#print axioms RootData.exists_of_wf
#print axioms RootData.incoherency_rootCut_of_chainIn
#print axioms RootData.multFactors_local
#print axioms size_rootCut

end WaveTurbulence.Flower.ProtCut

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.SwGlue

/-! # D2c-3 PROT-CUT: o104 Prop 7.4 (a) for couples, `ε = -` (the root of a nonempty `-` chain traced)

A couple `LG` decoded by `type2 Xp (pair m Qr Qg inner rest) Qlp` (`= type2 Xp (appendChain Z rest) Qlp`,
`Z = cpair m Qr Qg inner`): its tree `1` is the chain `X⁻` with the tree `1` of `Q_lp` at its lone position.
`SwGlueData LG Xp Z rest Qlp LGZ LGB` glues `Z` (sign `-1`) on the relabelled rest couple `swLG LGB`
(`LGB` decoded by `closeCouple Xp rest Qlp`: o104's `K_rest`, the suffix, its side couples, `Q_lp` and `X⁺`).

* `toRoot2`: the relabelled couple as a `Root2Data`;
* **`SwGlueData.kernelProt_root2m`**: `kernelProt LG … (trFix 1 σ) = ` the right side of `Root2Data.kernelProt_root2`
  for `swLG LG` (clocks `U ∘ t1sw`: the traced root has its clock `U 1`);
* **`SwGlueData.kernelProt_bottom`**: the rest-couple factor there is the ordinary `kernelProt LGB` with profiles
  `H ∘ phiB`, its tree `1` (the suffix, below `n⁻_b`) at the clock `u` and its tree `0` (the chain `X⁺`) at `U 0`
  (`bClock1`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace SwGlueData

variable {LG : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner rest : RegChain}
  {Qlp : RegCpl} {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2}
  (D : SwGlueData LG Xp (cpair m Qr Qg inner) rest Qlp LGZ LGB)
include D

/-- **The relabelled couple as a `Root2Data`.** -/
theorem toRoot2 : Root2Data (swLG LG) m Qr Qg inner LGZ (swLG LGB) :=
  ⟨D.gd, D.decX, swGarden_plain D.dec.1.1, swGarden_plain D.decB.1.1, D.hs, D.hg,
    fun z => by rw [D.layX]; rfl,
    fun z => by
      show LGB.layer (ndB z) = layerAt (swLG LG) (botAddr (cpair m Qr Qg inner).lonePath z.1)
      rw [D.layB, layerAt_sw]
      exact congrArg (layerAt LG) (phiB_sw _ z.1)⟩

/-! ### The kernel -/

/-- **o104 Prop 7.4 (a) for couples on `kernelProt`, `ε = -`**: the root of a nonempty `-` chain traced. -/
theorem kernelProt_root2m {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2}
    (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg) (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|)
    (M : (GNode LG.garden.tree → Mom d) → ℂ) (MZ : (GNode LGZ.garden.tree → Mom d) → ℂ)
    (MB : (GNode (swLG LGB).garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ)
    (hMg : ∀ K, swM M K = MZ (K ∘ D.gd.ι₁) * MB (K ∘ D.gd.ι₂)) (hMZ : P.MultFactors MZ Mc Mi Mr Mg) (CM : ℝ)
    (hMB : ∀ K, ‖MB K‖ ≤ CM) (hMc : ∀ A B, ‖Mc A B‖ ≤ CM) (hMi : ∀ K, ‖Mi K‖ ≤ CM) (hMr : ∀ K, ‖Mr K‖ ≤ CM)
    (hMgb : ∀ K, ‖Mg K‖ ≤ CM) (U : Fin 2 → ℝ) (s σ : ℝ) (hσ : σ ≤ U 1) (k : Mom d) :
    kernelProt L γ δ LG H M (fun b => U b.1.1) s (trFix 1 σ) k (fun _ => 0) 0 =
      (coupling d L γ δ : ℂ) ^ 2 * (Complex.I * ((((LGZ.garden.sig 0 : ℤˣ) : ℤ) : ℂ))) *
        (Complex.I * ((((slotSign (LGZ.garden.sig 0) m.c : ℤˣ) : ℤ) : ℂ))) *
        ∑' e : PairE m d, Mc (starA m L k e) (starB m L k e) * (cutEps m e : ℂ) *
          ∫ u in root2U (swLG LG) m inner (U 1) σ, cutPh m (LGZ.garden.sig 0) L γ δ k u e σ *
            (kernelProt L γ δ (swLG LGB) (t2HQ (cpair m Qr Qg inner) (swH H)) MB
                (fun y => bClock (fun t => U (t1sw t)) u y.1.1) s (fun _ => none) k (fun _ => 0) 0 *
              (kernelProt L γ δ LGi (cutHi .nil m (t2HX (swH H))) Mi (fun _ => σ) u (fun _ => none)
                  (k + latticePoint L e.1.1) (fun _ => 0) 0 *
                (kernelProt L γ δ LGr (cutHr .nil m inner (LGZ.garden.sig 0) (t2HX (swH H))) Mr
                    (fun y => cupR m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.1) (fun _ => 0) 0 *
                  kernelProt L γ δ LGg (cutHg .nil m inner (LGZ.garden.sig 0) (t2HX (swH H))) Mg
                    (fun y => cupG m inner (LGZ.garden.sig 0) σ u y.1.1) 0 (fun _ => none)
                    (k + latticePoint L e.1.2.2) (fun _ => 0) 0))) := by
  rw [← kernelProt_sw D.dec.1.1 L γ δ H M (fun b => U b.1.1) s (trFix 1 σ) k]
  have hfix : (fun b => trFix 1 σ (brB b) : GBranch (swLG LG).garden.tree → Option ℝ) = trFix 0 σ :=
    funext fun b => trFix_brB σ b
  rw [hfix]
  exact D.toRoot2.kernelProt_root2 P L γ δ (swH H) (hH_sw L H hH) (swM M) MZ MB Mc Mi Mr Mg hMg hMZ CM hMB hMc
    hMi hMr hMgb (fun t => U (t1sw t)) s σ hσ k

/-- **The rest-couple factor of `kernelProt_root2m` is an ordinary kernel of `LGB`.** -/
theorem kernelProt_bottom (L γ δ : ℝ) {d : ℕ} (H : LeafProfiles 2 d)
    (MB : (GNode (swLG LGB).garden.tree → Mom d) → ℂ) (U : Fin 2 → ℝ) (s u : ℝ) (k : Mom d) :
    kernelProt L γ δ (swLG LGB) (t2HQ (cpair m Qr Qg inner) (swH H)) MB
        (fun y => bClock (fun t => U (t1sw t)) u y.1.1) s (fun _ => none) k (fun _ => 0) 0 =
      kernelProt L γ δ LGB (fun a => H (phiB (cpair m Qr Qg inner).lonePath a)) (fun K => MB (K ∘ ndB))
        (fun y => bClock1 U u y.1.1) s (fun _ => none) k (fun _ => 0) 0 := by
  rw [kernelProt_sw_back D.decB.1.1]
  have e1 : (fun a : Fin 2 × Path => t2HQ (cpair m Qr Qg inner) (swH H) (t1sw a.1, a.2)) =
      fun a => H (phiB (cpair m Qr Qg inner).lonePath a) := by
    funext a
    obtain ⟨t, p⟩ := a
    fin_cases t <;> simp [t2HQ, swH, phiB, botAddr, t1sw]
  have e2 : (fun b : GBranch LGB.garden.tree => bClock (fun t => U (t1sw t)) u (brF b).1.1) =
      fun y => bClock1 U u y.1.1 := by
    funext b
    obtain ⟨⟨t, p⟩, hb⟩ := b
    fin_cases t <;> simp [brF, bClock, bClock1, t1sw]
  rw [e1, e2]

end SwGlueData

end WaveTurbulence.Flower.ProtCut

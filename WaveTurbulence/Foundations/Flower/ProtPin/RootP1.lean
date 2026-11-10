/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.RootKink
public import WaveTurbulence.Foundations.Flower.ProtPin.RootTerm

/-! # D3 PROT-PIN: (P1) — a one-pair protected tree with its root pinned at `t`, port layer `q' = p` (R176 box)

D2c's `kernelProt_root0_cfg` (via `PairOnly.of_cutTerm`) on the R176 box: the `b` node is in layer `p` (`ChainIn`), so
the time domain `rootU0` is `Ioo σ t` (`σ = ts 1 ≥ p` the port clock) and the kernel is
`Σ_e c_e ∫_{Ioo σ t} e^{iπA_e(t-u)} W_e(t, u) du` with `W_e = K_in Q_r Q_g` the pieces of `term`. `mirror_kink` bounds
it by `Σ_e |c_e| ‖W_e‖`, and `W_e` is bounded as in `term_star_perk` (`root_perk_top`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The node `𝔫_b` of a one-pair chain is in layer `p`. -/
theorem pair_b_layer {LG LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl}
    {inner : RegChain} (D : PairOnly LG m Qr Qg inner LGi LGr LGg) {p : ℕ}
    (hch : ChainIn p (cpair m Qr Qg inner) LG) : layerAt LG ((0 : Fin 1), bPath m inner) = p := by
  have hlp : (cpair m Qr Qg inner).lonePath = bPath m inner ++ [m.lone] := by
    simp [RegChain.lonePath, bPath]
  have h := hch D.hp.bB rfl (by rw [hlp]; exact List.prefix_append _ _)
    (by rw [hlp]; show bPath m inner ≠ bPath m inner ++ [m.lone]; simp)
  rw [← Links.layerAt_node] at h
  exact h

/-- The time domain of (P1) on the R176 box. -/
theorem rootU0_eq {LG : LayeredGarden 1} {m : MiniTreeCode} {inner : RegChain} {p : ℕ}
    (hlay : layerAt LG ((0 : Fin 1), bPath m inner) = p) {t T σ : ℝ} (_hpt : (p : ℝ) < t) (htp : t < p + 1)
    (hT : t ≤ T) (hσ : (p : ℝ) ≤ σ) : rootU0 LG m inner T t σ = Ioo σ t := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [rootU0, hlay, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨-, -, -, -, h5, h6⟩
    exact ⟨h6, h5⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith, by linarith, by linarith, h2, h1⟩

end WaveTurbulence.Flower.ProtPin

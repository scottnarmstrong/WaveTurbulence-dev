/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChildT2mB
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildMixT
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildIvl
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink

/-! # D3 PROT-PIN (P7): the root trace of a type-2 side couple with an empty `-` chain, partner port below `p`

o104 Prop 7.4 (c), `ε = -`, fixed case: the traced root (tree `1`, the root of `Q_lp`) is in layer `p`, pinned at `s`;
the partner `ρ'` (the root of tree `0` of `Q_lp`, the lone port of the chain tree `K_X`) is in a layer `𝔏'' < p`, so
its time ranges over the whole cell `(𝔏'', 𝔏''+1)` (`tc_t2mU_fix`). Each exceptional term is the chain tree
`K_X(y, u)` integrated against the bounded weight `t1Ph · Q₁Q₂Q₃(s, u)` over a fixed unit interval
(`tc_ivl_restr`, the tree on `timeBoxGt p 𝔏''` by `tc_tree_mixed`); the sub-couples of `Q_lp` are bounded pointwise
on the mixed box (`tc_couple_pt`), the terms summed by main's countable Minkowski (`XNorm00Restr_tsum_le`), the
incoherent root link of `Q_lp` paid by `L` (`rb_pred_le`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal
open WaveTurbulence.Induct

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem tc_t2mU_fix {LG : LayeredGarden 2} {Xp : RegChain} {q : ℕ} (hl : layerAt LG ((0 : Fin 2), Xp.lonePath) = q)
    {T : ℝ} (hT : (q : ℝ) + 1 ≤ T) : t2mU LG Xp T = Ioo (q : ℝ) (q + 1) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  ext u
  simp only [t2mU, hl, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, h2, -, -⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2, by linarith, by linarith⟩

theorem tc_t2mU_move {LG : LayeredGarden 2} {Xp : RegChain} {p : ℕ} (hl : layerAt LG ((0 : Fin 2), Xp.lonePath) = p)
    {T : ℝ} (hT : T ≤ p + 1) : t2mU LG Xp T = Ioo (p : ℝ) T := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  ext u
  simp only [t2mU, hl, Set.mem_ofPred_eq, Set.mem_Ioo]
  constructor
  · rintro ⟨h1, -, -, h4⟩
    exact ⟨h1, h4⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, by linarith, by linarith, h2⟩

/-- The constant of main's countable Minkowski on a unit cell does not depend on the cell. -/
theorem tc_cmc_eq (θ : ℝ) {r : ℕ} (q : Fin r → ℝ) :
    cutoffMultiplierConstant θ (VineEstS3.FS.cutQ q) = ENNReal.ofReal (2 ^ |θ|) * cutNormR |θ| r := by
  unfold cutoffMultiplierConstant
  congr 1
  have e : VineEstS3.FS.cutQ q = fun t => coordinateCutoff (r := r) Layered.chiUnit (t + -q) := by
    funext t
    simp only [VineEstS3.FS.cutQ, sub_eq_add_neg]
  rw [e, timeFourierNorm_translate]
  rfl

/-- The chain root of a type-2 couple with a nonempty `+` chain is a branching node. -/
theorem tc2_root0 {LG : LayeredGarden 2} {Xp : RegChain} {LGX : LayeredGarden 1} {LGQ : LayeredGarden 2}
    (D : T2mData LG Xp LGX LGQ) (hX : Xp ≠ .nil) : ([] : TTree.Path) ∈ (LG.garden.tree 0).branching := by
  rw [D.gd.tree0]
  cases Xp with
  | nil => exact absurd rfl hX
  | pair m Qr Qg inner rest => exact (mem_node3_nil _).2.2

end WaveTurbulence.Flower.ProtPin

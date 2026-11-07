/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.Transport
public import WaveTurbulence.Foundations.VineEst.VineEstS4.PieceFamily
public import WaveTurbulence.Foundations.VineEst.VineEstS4.RegionUnique
public import WaveTurbulence.Foundations.VineEst.VineEstS3.BadClauseD
public import WaveTurbulence.Foundations.Molecule.LFTwist.FamilyOutputs
public import WaveTurbulence.Foundations.VineEst.RegRedDraft.CLLocalKernel

/-! # The twisted local kernels `K^U_{(G')}` and the twist class (V5 Step 4a)

* `chainFamily B` is the core family of the pieces of a chain assembly, `startState` the state of `(G, RD, layer)`,
  `chainStart B` the chain region as a `ChainAt`.
* `stateLayer`: the layering of the output state `Bs` transported to its reconstructed garden (the reconstruction of a
  skeleton is unique, `existsUnique_decodes`), and `twistedLocalKernel Bs c` = `clLocalKernel` of the state `Bs` at the
  region `c` (the CL region data is unique, `regionData_subsingleton`).
* `ClassSection`: a finite set of (state, region) pairs reached from the start by once-per-member batches, whose
  layered gardens are exactly the class `allCoreOutputs` and pairwise distinct: one representative per garden.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS4
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS3 WaveTurbulence.Twist WaveTurbulence.LFTwist
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed TTree

variable {w : ℕ}

/-! ## The layering of a state, transported to its reconstructed garden -/

theorem exists_stateLayer {ι : Type*} (Bs : FamilyReconstruction w ι) :
    ∃ (layer : GNode (Bs.data.forest Bs.plain) → ℕ) (hL : IsLayering (Bs.data.garden Bs.plain) layer),
      layeredReconstruction Bs.data Bs.plain layer hL = Bs.layered := by
  have hg : Bs.layered.garden = Bs.data.garden Bs.plain :=
    ((Bs.data.existsUnique_decodes Bs.plain).unique Bs.decodes (Bs.data.garden_decodes Bs.plain))
  generalize Bs.layered = X at hg ⊢
  obtain ⟨g, l, hl⟩ := X
  change g = _ at hg
  subst hg
  exact ⟨l, hl, rfl⟩

/-- The layering is determined by the layered reconstruction. -/
theorem layeredReconstruction_inj {S : Garden w} (D : ReconstructionData S) (hS : S.IsPlain)
    {l₁ l₂ : GNode (D.forest hS) → ℕ} {h₁ : IsLayering (D.garden hS) l₁} {h₂ : IsLayering (D.garden hS) l₂}
    (h : layeredReconstruction D hS l₁ h₁ = layeredReconstruction D hS l₂ h₂) : l₁ = l₂ := by
  have := LayeredGarden.mk.inj h
  exact eq_of_heq this.2

/-- The layering of the state. -/
@[expose] noncomputable def stateLayer {ι : Type*} (Bs : FamilyReconstruction w ι) : GNode (Bs.data.forest Bs.plain) → ℕ :=
  Classical.choose (exists_stateLayer Bs)

theorem stateLayer_isLayering {ι : Type*} (Bs : FamilyReconstruction w ι) :
    IsLayering (Bs.data.garden Bs.plain) (stateLayer Bs) :=
  Classical.choose (Classical.choose_spec (exists_stateLayer Bs))

theorem stateLayer_spec {ι : Type*} (Bs : FamilyReconstruction w ι) :
    layeredReconstruction Bs.data Bs.plain (stateLayer Bs) (stateLayer_isLayering Bs) = Bs.layered :=
  Classical.choose_spec (Classical.choose_spec (exists_stateLayer Bs))

/-! ## The kernel of a state at a transported region -/

/-- `K^U_{(G')}` (TARGET L1733-L1740 for the twisted garden `G'` of the state `Bs`, at the region `c`). -/
@[expose] noncomputable def twistedLocalKernel {d : ℕ} {ι : Type*} (Bs : FamilyReconstruction w ι)
    (c : ChainAt Bs.skeleton Bs.family) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (base : Mom d)
    (tUpper tPositive tNegative : ℝ) (e f g h : Mom d) : ℂ :=
  clLocalKernel Bs.data Bs.plain (clRegionData Bs.skeleton c.block c.cl) L γ δ F (stateLayer Bs) (stateLayer_isLayering Bs) base
    tUpper tPositive tNegative e f g h

end WaveTurbulence.VineEstS4

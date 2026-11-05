/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.XChain.LayerCutLeafEquiv
public import WaveTurbulence.Foundations.XChain.PairingPartition
public import WaveTurbulence.Foundations.XChain.SumPartition
public import WaveTurbulence.Foundations.XChain.SubtypePartition
public import WaveTurbulence.Foundations.XChain.PartitionTransport
/-! The literal inverse partition: canonical attachment blocks and terminal pairing orbits. -/
@[expose] public section
namespace WaveTurbulence.Induct
open Finset
open scoped Classical

abbrev TerminalLeaf {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :=
  {ℓ : GLeaf LG.garden.tree // LG.layer ℓ.toNode = p}

noncomputable def terminalLeafPair {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (ℓ : TerminalLeaf LG p) : TerminalLeaf LG p :=
  ⟨LG.garden.pair ℓ.1, (LG.isLayering.2 ℓ.1).symm.trans ℓ.2⟩

theorem terminalLeafPair_involutive {w : ℕ} (LG : LayeredGarden w) (p : ℕ) :
    Function.Involutive (terminalLeafPair LG p) := fun ℓ => Subtype.ext (LG.garden.pair_pair ℓ.1)

theorem terminalLeafPair_ne_self {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hplain : LG.garden.IsPlain) (ℓ : TerminalLeaf LG p) : terminalLeafPair LG p ℓ ≠ ℓ := by
  intro he
  have hp := congrArg Subtype.val he
  exact ((LG.garden.pair_eq_iff ℓ.1).mp hp) (hplain ℓ.1)

noncomputable def layerCutPartition {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
    (hbound : ∀ a, LG.layer a ≤ p) (P : Finpartition (LG.attachNodes p)) :
    Finpartition (univ : Finset (GLeaf (layerCutForest LG p))) :=
  mapUnivPartition (layerCutLeafEquiv LG p hbound).symm
    (sumPartition (subtypePartition P)
      (pairingPartition (terminalLeafPair LG p) (terminalLeafPair_involutive LG p)))

end WaveTurbulence.Induct

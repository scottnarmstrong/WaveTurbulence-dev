/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.SpineInputs
public import WaveTurbulence.Foundations.Spine.SourceProviders

/-! The two leafwise spine inputs, from main's proved providers (`WaveTurbulence.Spine`), which use the frozen
`regularAsymptotics`. No native B2.1 copy is needed in the frozen world. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop

theorem leafCoherentInput : LeafCoherentInput := WaveTurbulence.Spine.leafwise_coherent_approximation

theorem leafDecayInput : LeafDecayInput := WaveTurbulence.Spine.leafwise_incoherent_decay

end WaveTurbulence.FlowerTop

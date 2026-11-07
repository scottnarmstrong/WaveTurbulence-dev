/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.FlowerTop.SpineInputs
public import WaveTurbulence.Foundations.FlowerTop.Port.LadderSTGate

/-! READY P5 provider against the exact FLOWERTOP interface; separate provider build world. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerTop

theorem p5LadderInput : P5LadderInput := FlowerP5.ladderFourierST_prefix

end WaveTurbulence.FlowerTop

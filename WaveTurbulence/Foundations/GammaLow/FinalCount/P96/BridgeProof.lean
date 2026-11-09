/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.Case4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.P96.BridgeC

/-! # `C4TBridge` is proved (M2 §4.8 (A2): a Y-exceptional T-type case-(4) component is a T-vine) -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount
universe u v

/-- **The T-type bridge of case (4)′.** -/
theorem c4TBridge_proved : C4TBridge.{u, v} where
  two := fun _ _ _ hS _ _ _ _ _ _ _ _ _ D4 hreg _ hroute => isTVine_of_two hS D4 hreg hroute
  one := fun _ _ _ hS _ _ _ _ _ _ _ _ _ D1 hreg _ hroute => isTVine_of_one hS D1 hreg hroute

end WaveTurbulence.GammaLow.FinalCount

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.VineAssembleIncidences
public import WaveTurbulence.Foundations.Molecule.VineRungSequences

/-! # Local incidence data for a triangle attached to a ladder and two joints

This helper records primitive dart incidences. It is not a replacement for
IsVine; the source template realization must construct the data explicitly.
-/

public section
namespace WaveTurbulence.Vine
variable {V D : Type*}

/-- Five distinct core atoms, the full rung sequence between them, and the
three exact incidence rows at the triangular end of the ladder. -/
structure SideLadderData (M : Molecule V D) (center upper lower a b : V) (n : ℕ) where
  ladder : FullRungSequence M n
  start_upper : ladder.u 0=upper
  start_lower : ladder.v 0=lower
  end_upper : ladder.u (n+1)=a
  end_lower : ladder.v (n+1)=b
  distinct : Function.Injective ![center,upper,lower,a,b]
  center_row : FourIncidences M center ![upper,upper,lower,lower]
  upper_row : FourIncidences M upper ![center,center,lower,ladder.u 1]
  lower_row : FourIncidences M lower ![center,center,upper,ladder.v 1]

end WaveTurbulence.Vine

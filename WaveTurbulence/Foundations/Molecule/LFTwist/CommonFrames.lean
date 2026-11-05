/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.CommonInflation
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationFrameMap
public import WaveTurbulence.Foundations.Molecule.LFTwist.InflationPositions

/-! # The common forest has identical inserted path frames on both sides -/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist
variable {w : ℕ} (S : Garden w) (P : CorePlacement S) (hS : S.IsPlain) (D : ReconstructionData S)

theorem common_inflationFrame_twist (j : Fin w) (p : Path) (hp : p ∈ (commonForest S P.lower j).nodes) :
    inflationFrame (branchLookup (twistReconstruction S P hS D)) (j,[]) p =
      inflationFrame (branchLookup D) (j,[]) p := by
  apply inflationFrame_map (branchLookup D) (branchLookup (twistReconstruction S P hS D)) id
    (commonForest S P.lower j) (j,[]) p hp (fun _ => rfl)
  intro q hq
  simpa only [id_eq, addrExt, List.nil_append] using common_branchLookup_twist S P hS D ⟨(j,q),hq⟩

/-- In particular, both physical hole addresses and all ordinary common-node
addresses are unchanged by transporting the source assignment. -/
theorem common_rawSourcePosition_twist (n : GNode (commonForest S P.lower)) :
    rawSourcePosition (twistReconstruction S P hS D) n.1 = rawSourcePosition D n.1 := by
  apply congrArg (addrExt (n.1.1,[]))
  exact common_inflationFrame_twist S P hS D n.1.1 n.1.2 n.2

end WaveTurbulence.LFTwist

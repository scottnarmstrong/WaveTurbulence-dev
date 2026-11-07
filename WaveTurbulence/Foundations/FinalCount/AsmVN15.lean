/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmVN14
/-! **FINALCOUNT-ASSEMBLY (VineNodeExists, part 15): `VHard` from the shape classification.**  `vhard_of_shape`: `hcls`, `hrho` are proved
(AsmVN13/14); `hconn0` (state-level joint connectivity of three-atom objects) and `hint` stay hypotheses. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

theorem vhard_of_shape {M₀ : Molecule V D₀} {crit : V → Prop} {h : HSt V D₀} {K : VineCut h.s.M} {U : Object M₀}
    (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (hnl : ∀ x : h.s.D, h.s.M.atom x ≠ h.s.M.atom (h.s.M.mate x))
    (hdeg : ∀ b ∈ h.s.M.atoms, h.s.M.deg b ≤ 4) (hMol : h.s.M.IsMolecule)
    (hint : ∀ b ∈ U.atoms, b ∈ h.s.M.atoms ∧ h.s.cls b = .eps) (hKat : K.C.atoms = U.atoms)
    (hsh : U.atoms.card = 3 ∨ ObjVine M₀ U)
    (hconn0 : ∀ K' : VineCut h.s.M, K'.C.atoms = K.C.atoms → Nonempty (DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G)
    (hcrit : ∀ a ∈ K.C.atoms, a ≠ K.C.upper → a ≠ K.C.lower → ¬ crit a) : VHard crit h K :=
  vhard_of_atoms (fun K' hat => hcls_state hA hD hnl hdeg U hint hsh K' (hat.trans hKat)) hconn0
    (hrho_of_cls hMol K (hcls_state hA hD hnl hdeg U hint hsh K hKat)) hcrit

end WaveTurbulence.FinalCountAsm

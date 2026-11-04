/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.WaveB.FrozenB2

/-!
# The held-out declarations of the Wave B tier-B2 Regular draft

Non-frozen. `waveb2-snap-final/WaveB2-Regular.lean` without its module doc, without its frozen
declarations (they come from the freeze, ruling D8, through `FrozenB2`) and without its `sorry`'d
section-4 theorems (the five frozen anchors O1–O5 and `regular_count_le`). Everything else is the
draft text, in order: `MiniTreeCode.equiv` and the seven instances the freeze holds out, which the
ported REG-STRUCT and INCOH-INST proofs were written against.
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-! ## §1 Mini-couples and mini-trees -/

/-- `MiniTreeCode ≃ Fin 3 × Fin 2`. -/
def MiniTreeCode.equiv : MiniTreeCode ≃ Fin 3 × Fin 2 :=
  ⟨fun m => (m.c, m.b), fun p => ⟨p.1, p.2⟩, fun _ => rfl, fun _ => rfl⟩

@[instance_reducible, instance] def instDecidableEqMiniTreeCode : DecidableEq MiniTreeCode :=
  MiniTreeCode.equiv.injective.decidableEq

@[instance_reducible, instance] def instFintypeMiniTreeCode : Fintype MiniTreeCode :=
  Fintype.ofEquiv _ MiniTreeCode.equiv.symm

namespace MiniTreeCode

end MiniTreeCode

/-! ## §2 Regularity in source form: operations A and B (T Def `defreg`, L826–L829) -/

namespace RawCpl

end RawCpl

@[instance_reducible, instance] def instDecidableMatchesCouple (G : Garden 2) (T : TTree × TTree)
    (P : List ((Fin 2 × Path) × (Fin 2 × Path))) : Decidable (G.MatchesCouple T P) := by
  unfold Garden.MatchesCouple
  infer_instance

@[instance_reducible, instance] def instDecidableMatchesTreeCouple (G : Garden 1) (R : RawCpl) :
    Decidable (G.MatchesTreeCouple R) := by
  unfold Garden.MatchesTreeCouple
  infer_instance

/-! ## §3 Structure data: codes of regular couples, regular chains and regular trees -/

@[instance_reducible, instance] def instDecidableDecodes (Q : RegCpl) (G : Garden 2) : Decidable (Q.Decodes G) :=
  inferInstanceAs (Decidable (G.MatchesCouple _ _))

@[instance_reducible, instance] def instDecidableMatchesPairedTree (G : Garden 1) (T : TTree) (lp : Path)
    (P : List ((Fin 1 × Path) × (Fin 1 × Path))) : Decidable (G.MatchesPairedTree T lp P) := by
  unfold Garden.MatchesPairedTree
  infer_instance

@[instance_reducible, instance] def instDecidableDecodesTree (X : RegChain) (G : Garden 1) :
    Decidable (X.DecodesTree G) :=
  inferInstanceAs (Decidable (G.MatchesPairedTree _ _ _))

/-! ## §4 Characterization obligations (statements; proofs belong to packets C1, C2)

These fix what the codes mean: decoding lands in the regular objects of T Def `defreg`, and every
regular couple (tree) has exactly one well-formed code, i.e. the structure data are functions of the
couple (T Prop `propstructure`; DH21 Props 4.5, 4.7, 4.8, Cor 4.9). The last obligation is the counting
sentence of `propstructure` (B2-CL-8). No `Classical.choose` is used: consumers quantify over pairs
`(code, carrier)` with `Decodes`. -/

/-! ## §5 Links, `𝒩^ch`, dominant codes, special subsets, coherence -/

/-! ## §6 Time factors, the principal value, momentum factors and the leading terms -/

end WaveTurbulence

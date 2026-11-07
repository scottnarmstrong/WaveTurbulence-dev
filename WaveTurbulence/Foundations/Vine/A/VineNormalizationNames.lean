/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceDiagrams
public import WaveTurbulence.Foundations.Vine.A.VineFiniteKeyChoice
/-! Fixed address words in the sigma-independent all-SG normalization. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Stage1
variable {w : ℕ} {G : Garden w}

/-- Tree index followed by the ordered child path. -/
def addressWord (a : Fin w × TTree.Path) : List ℕ := a.1.val :: a.2.map Fin.val

theorem addressWord_injective : Function.Injective (@addressWord w) := by
  intro a b h
  have he := List.cons.inj h
  exact Prod.ext (Fin.ext he.1) ((List.map_injective_iff.mpr Fin.val_injective) he.2)

/-- A PC tag and side or an LP tag, followed by the literal address word. -/
def dartAddressWord : DartAddress w → List ℕ
  | .inl (a, s) => 0 :: s.toNat :: addressWord a
  | .inr a => 1 :: addressWord a

theorem dartAddressWord_injective : Function.Injective (@dartAddressWord w) := by
  rintro (⟨a, s⟩ | a) (⟨b, t⟩ | b) h
  · have he := List.cons.inj (List.cons.inj h).2
    have hs : s = t := by
      cases s <;> cases t
      · rfl
      · exact (Nat.zero_ne_one he.1).elim
      · exact (Nat.one_ne_zero he.1).elim
      · rfl
    exact congrArg Sum.inl (Prod.ext (addressWord_injective he.2) hs)
  · exact (Nat.zero_ne_one (List.cons.inj h).1).elim
  · exact (Nat.one_ne_zero (List.cons.inj h).1).elim
  · exact congrArg Sum.inr (addressWord_injective (List.cons.inj h).2)

/-- The actual all-SG quotient name of an atom. -/
noncomputable def coarseAtomWord (G : Garden w) (v : GBranch G.tree) : List ℕ :=
  addressWord (((coarseSplice G).M.pi (coarseSplice G).hcls v).1)

/-- Untouched original atoms have distinct normalized address words. -/
theorem coarseAtomWord_inj_of_none {a b : GBranch G.tree}
    (ha : (coarseSplice G).cls a = none) (hb : (coarseSplice G).cls b = none)
    (he : coarseAtomWord G a = coarseAtomWord G b) : a = b := by
  have hp := congrArg (coarseSplice G).M.ob (Subtype.ext (addressWord_injective he))
  rw [SpMap.ob_pi, SpMap.ob_pi] at hp
  simpa only [repC, ha, hb, Option.getD_none] using hp

/-- Exactly the surviving original dart domain of the all-SG splice. -/
abbrev CoarseDart (G : Garden w) := {x : GardenDart G // ∃ y, (coarseSplice G).M.od y = x}

/-- The normalized actual dart word, only on its exact surviving domain. -/
noncomputable def coarseDartWord (G : Garden w) (x : CoarseDart G) : List ℕ :=
  dartAddressWord (dartAddress (coarseSplice G).G (spliceDartQuotient (coarseSplice G) x))

/-- Actual surviving original darts have distinct normalized words. -/
theorem coarseDartWord_injective (G : Garden w) : Function.Injective (coarseDartWord G) := by
  intro x y h
  have hd := dartAddress_injective _ (dartAddressWord_injective h)
  apply Subtype.ext
  exact (spliceDartQuotient_name _ x).symm.trans
    ((congrArg (coarseSplice G).M.od hd).trans (spliceDartQuotient_name _ y))

/-- Reversal preserves the exact surviving original-dart domain. -/
def coarseDartMate (G : Garden w) (x : CoarseDart G) : CoarseDart G :=
  ⟨G.molecule.mate x.1, by
    obtain ⟨y, hy⟩ := x.2
    exact ⟨(coarseSplice G).G.molecule.mate y,
      ((coarseSplice G).M.od_mate y).trans (congrArg G.molecule.mate hy)⟩⟩

/-- The branch-word diagram for the all-SG normalization. -/
theorem coarseAtomWord_twist (Z : TwistGroupSite G)
    (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0) (v : GBranch G.tree) :
    coarseAtomWord Z.target (Z.iso.e v) = coarseAtomWord G v := by
  apply congrArg addressWord
  exact (congrArg Subtype.val (unitSplice_pi Z (fun _ => .SG) hsel v)).trans
    (unitSpliceMolIso_address Z (fun _ => .SG) hsel _)

/-- The actual LF map on the all-SG surviving-dart domain. -/
noncomputable def coarseDartTwist (Z : TwistGroupSite G)
    (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0) (x : CoarseDart G) : CoarseDart Z.target :=
  unitSpliceRetainedDart Z (fun _ => .SG) hsel x

/-- The dart-word diagram for the all-SG normalization. -/
theorem coarseDartWord_twist (Z : TwistGroupSite G)
    (hsel : ∃ c ∈ vinesV0 G (fun _ => .SG), c.atoms = Z.S0) (x : CoarseDart G) :
    coarseDartWord Z.target (coarseDartTwist Z hsel x) = coarseDartWord G x := by
  apply congrArg dartAddressWord
  exact (congrArg (dartAddress (coarseSplice Z.target).G)
    (unitSplice_dartQuotient Z (fun _ => .SG) hsel x)).trans
      (unitSpliceMolIso_dartAddress Z (fun _ => .SG) hsel _)

end WaveTurbulence.VineA

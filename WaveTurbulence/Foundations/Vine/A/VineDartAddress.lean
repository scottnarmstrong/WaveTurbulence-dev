/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSpliceOrdered
/-! Literal address codes and equality casts for normalized garden carriers. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Mole WaveTurbulence.Twist WaveTurbulence.Stage1
variable {w : ℕ} {G H : Garden w}

/-- PC child addresses with side, or LP leaf addresses. -/
abbrev DartAddress (w : ℕ) := ((Fin w × TTree.Path) × Bool) ⊕ (Fin w × TTree.Path)

/-- A literal code for an actual garden dart; no arbitrary carrier numbering. -/
def dartAddress (G : Garden w) : GardenDart G → DartAddress w
  | .inl (c, side) => .inl (c.1.1, side)
  | .inr q => .inr q.1.1

/-- Literal dart codes distinguish darts in a garden. -/
theorem dartAddress_injective (G : Garden w) : Function.Injective (dartAddress G) := by
  rintro (⟨c, s⟩ | q) (⟨d, t⟩ | r) h
  · have he := Sum.inl.inj h
    have hc : c = d := Subtype.ext (Subtype.ext (congrArg Prod.fst he))
    have hs : s = t := congrArg Prod.snd he
    cases hc
    cases hs
    rfl
  · cases h
  · cases h
  · exact congrArg Sum.inr (Subtype.ext (Subtype.ext (Sum.inr.inj h)))

/-- Cast an actual branch along literal garden equality. -/
def gardenBranchCast (h : H = G) (v : GBranch H.tree) : GBranch G.tree := h ▸ v

theorem gardenBranchCast_val (h : H = G) (v : GBranch H.tree) :
    (gardenBranchCast h v).1 = v.1 := by cases h; rfl

/-- B1b-2 (Mk-general form of `unitSpliceMolIso_dartAddress`). -/
theorem unitSpliceMolIso_dartAddressMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (x : GardenDart (stSt G σ Mk).G) :
    dartAddress (stSt Z.target (transportPrescription Z.iso σ) Mk').G ((unitSpliceMolIsoMk Z σ hT hsel).d x) =
      dartAddress (stSt G σ Mk).G x := by
  cases x with
  | inl pc =>
    rw [unitSpliceMolIso_pcMk]
    exact congrArg (fun a => Sum.inl (a, pc.2)) (unitSpliceMolIso_addressMk Z σ hT hsel pc.1.1)
  | inr q =>
    rw [unitSpliceMolIso_lpMk]
    exact congrArg Sum.inr (unitSpliceLeafEquiv_addressMk Z σ hT hsel q.1)

/-- The actual quotient dart map fixes PC/LP tags, sides and all addresses. -/
theorem unitSpliceMolIso_dartAddress (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (x : GardenDart (stSt G σ).G) :
    dartAddress (stSt Z.target (transportPrescription Z.iso σ)).G ((unitSpliceMolIso Z σ hsel).d x) =
      dartAddress (stSt G σ).G x := unitSpliceMolIso_dartAddressMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel x

end WaveTurbulence.VineA

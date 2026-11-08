/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineUnitSplicePhase
/-! Original epsilon factors, including the exact omitted-hinge set,
transport through the actual selected simultaneous splice correspondence. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open WaveTurbulence.RedSplice WaveTurbulence.Stage1 WaveTurbulence.LGSpine
variable {w : ℕ} {G : Garden w}

/-- The original epsilon coefficient is symmetric in its two outer arguments. -/
theorem epsCoef_outer_swap {d : ℕ} (a b c : Fin d → ℤ) : epsCoef c b a = epsCoef a b c := by
  simp only [epsCoef, eq_comm, and_comm]

/-- Every child permutation fixing the middle argument preserves the original epsilon. -/
theorem epsCoef_ternary_perm {d : ℕ} (e : Fin 3 ≃ Fin 3) (he : e 1 = 1) (f : Fin 3 → (Fin d → ℤ)) :
    epsCoef (f (e 0)) (f (e 1)) (f (e 2)) = epsCoef (f 0) (f 1) (f 2) := by
  have h01 : e 0 ≠ 1 := fun h => (by decide : (0 : Fin 3) ≠ 1) (e.injective (h.trans he.symm))
  have h21 : e 2 ≠ 1 := fun h => (by decide : (2 : Fin 3) ≠ 1) (e.injective (h.trans he.symm))
  have h02 : e 0 ≠ e 2 := e.injective.ne (by decide)
  have hc : (e 0 = 0 ∧ e 2 = 2) ∨ (e 0 = 2 ∧ e 2 = 0) := by omega
  rcases hc with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · rw [h0, he, h2]
  · rw [h0, he, h2]
    exact epsCoef_outer_swap _ _ _

/-- B1b-2 (Mk-general form of `unitSplice_epsCoef`). -/
theorem unitSplice_epsCoefMk {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → (Fin d → ℤ))
    (b : GBranch (stSt G σ Mk).G.tree) :
    epsCoef ((κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) (b.child 0))
      ((κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) (b.child 1)) ((κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) (b.child 2)) =
    epsCoef (κ (((unitSpliceMolIsoMk Z σ hT hsel).e b).child 0))
      (κ (((unitSpliceMolIsoMk Z σ hT hsel).e b).child 1)) (κ (((unitSpliceMolIsoMk Z σ hT hsel).e b).child 2)) := by
  dsimp only [Function.comp_apply]
  rw [unitSpliceNodeEquiv_childMk, unitSpliceNodeEquiv_childMk, unitSpliceNodeEquiv_childMk]
  exact epsCoef_ternary_perm (unitSpliceChildEquivMk Z σ hT hsel b) (unitSpliceChildSlot_middleMk Z σ hT hsel b)
    (fun i => κ (((unitSpliceMolIsoMk Z σ hT hsel).e b).child i))

/-- Every actual retained branching epsilon factor agrees. -/
theorem unitSplice_epsCoef {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ))
    (b : GBranch (stSt G σ).G.tree) :
    epsCoef ((κ ∘ unitSpliceNodeEquiv Z σ hsel) (b.child 0))
      ((κ ∘ unitSpliceNodeEquiv Z σ hsel) (b.child 1)) ((κ ∘ unitSpliceNodeEquiv Z σ hsel) (b.child 2)) =
    epsCoef (κ (((unitSpliceMolIso Z σ hsel).e b).child 0))
      (κ (((unitSpliceMolIso Z σ hsel).e b).child 1)) (κ (((unitSpliceMolIso Z σ hsel).e b).child 2)) :=
  unitSplice_epsCoefMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel κ b

/-- B1b-2 (Mk-general form of `unitSplice_splicedEpsilon`). -/
theorem unitSplice_splicedEpsilonMk {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (CLVine G)} {Mk' : Set (CLVine Z.target)} (hT : Stage1Mk.MarkTransported Z.iso Mk Mk')
    (hsel : ∃ c ∈ vinesV0 G σ Mk, c.atoms = Z.S0) (hinges : Finset (GBranch (stSt G σ Mk).G.tree))
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree → (Fin d → ℤ)) :
    splicedEpsilon (stSt G σ Mk).G hinges (κ ∘ unitSpliceNodeEquivMk Z σ hT hsel) =
      splicedEpsilon (stSt Z.target (transportPrescription Z.iso σ) Mk').G
        (hinges.image (unitSpliceMolIsoMk Z σ hT hsel).e) κ := by
  classical
  let F := unitSpliceMolIsoMk Z σ hT hsel
  let f := fun b : GBranch (stSt Z.target (transportPrescription Z.iso σ) Mk').G.tree =>
    if b ∉ hinges.image F.e then epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)) else 1
  unfold splicedEpsilon
  simp only [Finset.prod_filter]
  trans ∏ b : GBranch (stSt G σ Mk).G.tree, f (F.e b)
  · apply Finset.prod_congr rfl
    intro b _
    have hm : F.e b ∈ hinges.image F.e ↔ b ∈ hinges := by
      constructor
      · intro h
        obtain ⟨c, hc, he⟩ := Finset.mem_image.mp h
        exact F.e.injective he ▸ hc
      · intro h
        exact Finset.mem_image.mpr ⟨b, h, rfl⟩
    dsimp only [f]
    by_cases hb : b ∈ hinges
    · have ht := hm.mpr hb
      simp only [hb, ht, not_true_eq_false, ↓reduceIte]
    · have ht : F.e b ∉ hinges.image F.e := fun h => hb (hm.mp h)
      simp only [hb, ht, not_false_eq_true, ↓reduceIte]
      exact unitSplice_epsCoefMk Z σ hT hsel κ b
  · exact F.e.prod_comp f

/-- The entire original epsilon product agrees with the actual transported hinge set. -/
theorem unitSplice_splicedEpsilon {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hinges : Finset (GBranch (stSt G σ).G.tree))
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ)) :
    splicedEpsilon (stSt G σ).G hinges (κ ∘ unitSpliceNodeEquiv Z σ hsel) =
      splicedEpsilon (stSt Z.target (transportPrescription Z.iso σ)).G
        (hinges.image (unitSpliceMolIso Z σ hsel).e) κ :=
  unitSplice_splicedEpsilonMk Z σ (Stage1Mk.markTransported_empty Z.iso) hsel hinges κ

end WaveTurbulence.VineA

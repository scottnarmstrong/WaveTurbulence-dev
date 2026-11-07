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

/-- Every actual retained branching epsilon factor agrees. -/
theorem unitSplice_epsCoef {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0)
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ))
    (b : GBranch (stSt G σ).G.tree) :
    epsCoef ((κ ∘ unitSpliceNodeEquiv Z σ hsel) (b.child 0))
      ((κ ∘ unitSpliceNodeEquiv Z σ hsel) (b.child 1)) ((κ ∘ unitSpliceNodeEquiv Z σ hsel) (b.child 2)) =
    epsCoef (κ (((unitSpliceMolIso Z σ hsel).e b).child 0))
      (κ (((unitSpliceMolIso Z σ hsel).e b).child 1)) (κ (((unitSpliceMolIso Z σ hsel).e b).child 2)) := by
  dsimp only [Function.comp_apply]
  rw [unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child, unitSpliceNodeEquiv_child]
  exact epsCoef_ternary_perm (unitSpliceChildEquiv Z σ hsel b) (unitSpliceChildSlot_middle Z σ hsel b)
    (fun i => κ (((unitSpliceMolIso Z σ hsel).e b).child i))

/-- The entire original epsilon product agrees with the actual transported hinge set. -/
theorem unitSplice_splicedEpsilon {d : ℕ} (Z : TwistGroupSite G) (σ : Prescription G)
    (hsel : ∃ c ∈ vinesV0 G σ, c.atoms = Z.S0) (hinges : Finset (GBranch (stSt G σ).G.tree))
    (κ : GNode (stSt Z.target (transportPrescription Z.iso σ)).G.tree → (Fin d → ℤ)) :
    splicedEpsilon (stSt G σ).G hinges (κ ∘ unitSpliceNodeEquiv Z σ hsel) =
      splicedEpsilon (stSt Z.target (transportPrescription Z.iso σ)).G
        (hinges.image (unitSpliceMolIso Z σ hsel).e) κ := by
  classical
  let F := unitSpliceMolIso Z σ hsel
  let f := fun b : GBranch (stSt Z.target (transportPrescription Z.iso σ)).G.tree =>
    if b ∉ hinges.image F.e then epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2)) else 1
  unfold splicedEpsilon
  simp only [Finset.prod_filter]
  trans ∏ b : GBranch (stSt G σ).G.tree, f (F.e b)
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
      exact unitSplice_epsCoef Z σ hsel κ b
  · exact F.e.prod_comp f

end WaveTurbulence.VineA

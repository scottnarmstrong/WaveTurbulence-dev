/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.LadderPhase
/-! # Product splitting of the ladder phase (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

/-- Extension of a time vector on `S` by zero. -/
def tExt (S : Finset (GBranch G.tree)) (t : S → ℝ) (a : GBranch G.tree) : ℝ :=
  if h : a ∈ S then t ⟨a, h⟩ else 0

/-- The phase factor of a single atom at time `τ`. -/
noncomputable def phaseAt (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (a : GBranch G.tree) (τ : ℝ) : ℂ :=
  Complex.exp ((Real.pi *
      (((((G.sign a.toNode : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        omegaNode G (cosetDecoration G L base z) a + D.frequency a) * τ) : ℝ) * Complex.I)

lemma ladderPhase_eq_prod (D : SplicedKernelData G d) (S : Finset (GBranch G.tree))
    (L γ δ : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) (t : S → ℝ) :
    ladderPhase D S L γ δ base z t = ∏ a ∈ S, phaseAt D L γ δ base z a (tExt S t a) := by
  unfold ladderPhase
  rw [← Finset.prod_coe_sort S (fun a => phaseAt D L γ δ base z a (tExt S t a))]
  refine Finset.prod_congr rfl (fun a _ => ?_)
  simp [phaseAt, tExt, a.2]

lemma norm_phaseAt (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) (a : GBranch G.tree) (τ : ℝ) :
    ‖phaseAt D L γ δ base z a τ‖ = 1 := Complex.norm_exp_ofReal_mul_I _

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

/-- The atoms of the interior rungs. -/
def interiorAtoms : Finset (GBranch G.tree) :=
  (Finset.univ.image fun i : Fin n => u (LadderDarts.ir i)) ∪
    (Finset.univ.image fun i : Fin n => v (LadderDarts.ir i))

include C in
omit C in
lemma interiorAtoms_subset : interiorAtoms (u := u) (v := v) ⊆ Molecule.ladderAtoms u v := by
  intro a ha
  unfold interiorAtoms at ha
  unfold Molecule.ladderAtoms
  rcases Finset.mem_union.mp ha with h | h
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)
  · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)

include C in
lemma prod_interior (F : GBranch G.tree → ℂ) :
    ∏ a ∈ interiorAtoms (u := u) (v := v), F a =
      ∏ i : Fin n, (F (u (LadderDarts.ir i)) * F (v (LadderDarts.ir i))) := by
  have hdisj : Disjoint (Finset.univ.image fun i : Fin n => u (LadderDarts.ir i))
      (Finset.univ.image fun i : Fin n => v (LadderDarts.ir i)) := by
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hb
    exact C.hne _ _ hj.symm
  have hir : Function.Injective (LadderDarts.ir (n := n)) := fun a b h => by
    apply Fin.ext; have := congrArg Fin.val h; simp [LadderDarts.ir] at this; exact this
  unfold interiorAtoms
  rw [Finset.prod_union hdisj, Finset.prod_image (fun a _ b _ h => hir (C.huinj h)),
    Finset.prod_image (fun a _ b _ h => hir (C.hvinj h)), Finset.prod_mul_distrib]


/-- The quadratic energy of the u-atom of interior rung `i` in chart coordinates. -/
noncomputable def rungAU (L : ℝ) (κ : GardenDart G → (Fin d → ℤ)) (i : Fin n) : ℝ :=
  -(2 * inner ℝ (latticePoint L (C.signs.pairs (C.chainOf κ) i).1)
        (latticePoint L (C.signs.pairs (C.chainOf κ) i).2))

/-- The (signed) energy of the v-atom of interior rung `i` in chart coordinates. -/
noncomputable def rungAV (L : ℝ) (κ : GardenDart G → (Fin d → ℤ)) (i : Fin n) : ℝ :=
  2 * inner ℝ (latticePoint L (C.signs.pairs (C.chainOf κ) i).1)
        (latticePoint L (C.signs.pairs (C.chainOf κ) i).2) +
    2 * inner ℝ (latticePoint L (C.signs.tau (C.signs.pairs (C.chainOf κ)) i 3 -
          C.signs.tau (C.signs.pairs (C.chainOf κ)) i 2))
        (latticePoint L (C.signs.qrel (C.chainOf κ) i)) +
      (((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ))) *
        ‖latticePoint L (C.signs.qrel (C.chainOf κ) i)‖ ^ 2

/-- **Factorization of the ladder phase.** In chart coordinates the phase is a unit-modulus
end factor times a product over the interior rungs, each depending on the rung pair and the flux. -/
theorem ladderPhase_factor (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (D : SplicedKernelData G d) (γ δ : ℝ)
    (z : GenDecoration G d roots 0) (t : (Molecule.ladderAtoms u v) → ℝ) :
    ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1 t =
      (∏ a ∈ Molecule.ladderAtoms u v \ interiorAtoms (u := u) (v := v),
          phaseAt D L γ δ base z.1 a (tExt _ t a)) *
        ∏ i : Fin n,
          (Complex.exp ((Real.pi * ((δ * L ^ (2 * γ) * C.rungAU L (bondIndex G z.1) i +
              D.frequency (u (LadderDarts.ir i))) * tExt _ t (u (LadderDarts.ir i))) : ℝ) * Complex.I) *
           Complex.exp ((Real.pi * ((δ * L ^ (2 * γ) * C.rungAV L (bondIndex G z.1) i +
              D.frequency (v (LadderDarts.ir i))) * tExt _ t (v (LadderDarts.ir i))) : ℝ) * Complex.I)) := by
  rw [ladderPhase_eq_prod, ← Finset.prod_sdiff (interiorAtoms_subset), C.prod_interior]
  congr 1
  refine Finset.prod_congr rfl (fun i _ => ?_)
  congr 1
  · unfold phaseAt
    congr 3
    have h := C.phase_u hP hL base roots z i
    unfold rungAU
    rw [← h]; ring
  · unfold phaseAt
    congr 3
    have h := C.phase_v hP hL base roots z i
    unfold rungAV
    rw [← h]; ring

end LadderDarts.Ctx

end WaveTurbulence.LadderDecay

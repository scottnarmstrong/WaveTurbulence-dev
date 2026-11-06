/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.RungWeight
public import WaveTurbulence.Foundations.Spine.LadderPhase
/-! # Interior rung weights at garden level (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine Finset

variable {w d : ℕ} {G : Garden w}

/-- The slot pair and kind of the gap specification at an atom. -/
noncomputable def gapSlots {a : GBranch G.tree} (f : Fin 4 → GardenDart G)
    (hd : G.molecule.dartsAt a = univ.image f) (spec : Option (LocalGapSpecification G a)) :
    Option (Fin 4 × Fin 4 × Molecule.GapKind) :=
  spec.attach.map fun q =>
    (Classical.choose (slot_of_dart a f hd q.1.first q.1.at_first),
     Classical.choose (slot_of_dart a f hd q.1.second q.1.at_second), q.1.kind)

/-- The gap indicator factor of a single atom. -/
noncomputable def gapAtomSpec {a : GBranch G.tree} (spec : Option (LocalGapSpecification G a))
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) : ℝ :=
  match spec with
  | none => 1
  | some q => if Molecule.gapKind L γ η
      (base + latticePoint L (bondIndex G z q.first) -
        (base + latticePoint L (bondIndex G z q.second))) = q.kind then 1 else 0

lemma gapAtom_eq {a : GBranch G.tree} (f : Fin 4 → GardenDart G)
    (hd : G.molecule.dartsAt a = univ.image f) (spec : Option (LocalGapSpecification G a))
    (L γ η : ℝ) (base : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    gapAtomSpec spec L γ η base z =
      gapFactor L γ η base (fun s => bondIndex G z (f s)) (gapSlots f hd spec) := by
  rcases spec with _ | q
  · rfl
  · simp only [gapAtomSpec, gapSlots, Option.attach_some, Option.map_some, gapFactor]
    generalize hk1 : Classical.choose (slot_of_dart a f hd q.first q.at_first) = kf
    generalize hk2 : Classical.choose (slot_of_dart a f hd q.second q.at_second) = ks
    have e1 : f kf = q.first := hk1 ▸ Classical.choose_spec (slot_of_dart a f hd q.first q.at_first)
    have e2 : f ks = q.second := hk2 ▸ Classical.choose_spec (slot_of_dart a f hd q.second q.at_second)
    simp only [e1, e2]

lemma gapSlots_opposite {a : GBranch G.tree} (f : Fin 4 → GardenDart G)
    (hd : G.molecule.dartsAt a = univ.image f) (spec : Option (LocalGapSpecification G a))
    (g : Fin 4 × Fin 4 × Molecule.GapKind) (hg : gapSlots f hd spec = some g) :
    G.molecule.out (f g.1) ≠ G.molecule.out (f g.2.1) := by
  rcases spec with _ | q
  · simp [gapSlots] at hg
  · simp only [gapSlots, Option.attach_some, Option.map_some, Option.some.injEq] at hg
    subst hg
    simp only
    generalize hk1 : Classical.choose (slot_of_dart a f hd q.first q.at_first) = kf
    generalize hk2 : Classical.choose (slot_of_dart a f hd q.second q.at_second) = ks
    have e1 : f kf = q.first := hk1 ▸ Classical.choose_spec (slot_of_dart a f hd q.first q.at_first)
    have e2 : f ks = q.second := hk2 ▸ Classical.choose_spec (slot_of_dart a f hd q.second q.at_second)
    rw [e1, e2]
    exact q.opposite

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

/-- Slot triple of the children of the `u` atom of interior rung `i`. -/
noncomputable def kU (d : ℕ) (i : Fin n) : Fin 3 → Fin 4 :=
  Classical.choose (children_slots (d := d) (u (LadderDarts.ir i)) (C.deg_u i) (C.LD.uDart i)
    (C.dartsAt_u i))

/-- Slot triple of the children of the `v` atom of interior rung `i`. -/
noncomputable def kV (d : ℕ) (i : Fin n) : Fin 3 → Fin 4 :=
  Classical.choose (children_slots (d := d) (v (LadderDarts.ir i)) (C.deg_v i) (C.LD.vDart i)
    (C.dartsAt_v i))

lemma kU_spec (i : Fin n) : Function.Injective (C.kU d i) ∧
    ∀ (z : GNode G.tree → (Fin d → ℤ)) (j : Fin 3),
      z ((u (LadderDarts.ir i)).child j) = bondIndex G z (C.LD.uDart i (C.kU d i j)) :=
  Classical.choose_spec (children_slots (d := d) (u (LadderDarts.ir i)) (C.deg_u i) (C.LD.uDart i)
    (C.dartsAt_u i))

lemma kV_spec (i : Fin n) : Function.Injective (C.kV d i) ∧
    ∀ (z : GNode G.tree → (Fin d → ℤ)) (j : Fin 3),
      z ((v (LadderDarts.ir i)).child j) = bondIndex G z (C.LD.vDart i (C.kV d i j)) :=
  Classical.choose_spec (children_slots (d := d) (v (LadderDarts.ir i)) (C.deg_v i) (C.LD.vDart i)
    (C.dartsAt_v i))

/-- The weight of interior rung `i` (epsilon and gap factors of both atoms) in chart coordinates. -/
noncomputable def rungW (D : SplicedKernelData G d) (L γ η : ℝ) (i : Fin n) (q : Fin d → ℤ)
    (p : Pt d) : ℝ :=
  (epsCoef (relLab C.signs i 0 (C.kU d i 0) p) (relLab C.signs i 0 (C.kU d i 1) p)
      (relLab C.signs i 0 (C.kU d i 2) p) *
    gapW L γ η C.signs i 0 (gapSlots (C.LD.uDart i) (C.dartsAt_u i)
      (D.gapSpecification (u (LadderDarts.ir i)))) p) *
  (epsCoef (relLab C.signs i (csv C.signs i q) (C.kV d i 0) p)
      (relLab C.signs i (csv C.signs i q) (C.kV d i 1) p)
      (relLab C.signs i (csv C.signs i q) (C.kV d i 2) p) *
    gapW L γ η C.signs i (csv C.signs i q) (gapSlots (C.LD.vDart i) (C.dartsAt_v i)
      (D.gapSpecification (v (LadderDarts.ir i)))) p)


include C in
/-- **Interior rung weight in chart coordinates.** -/
theorem rungW_eq (D : SplicedKernelData G d) (L γ η : ℝ) (base : Mom d)
    (zz : GNode G.tree → (Fin d → ℤ))
    (hκ : ∀ x, bondIndex G zz (G.molecule.mate x) = bondIndex G zz x)
    (hsol : C.signs.IsSol (C.chainOf (bondIndex G zz))) (i : Fin n) :
    (epsCoef (zz ((u (LadderDarts.ir i)).child 0)) (zz ((u (LadderDarts.ir i)).child 1))
        (zz ((u (LadderDarts.ir i)).child 2)) *
      gapAtomSpec (D.gapSpecification (u (LadderDarts.ir i))) L γ η base zz) *
    (epsCoef (zz ((v (LadderDarts.ir i)).child 0)) (zz ((v (LadderDarts.ir i)).child 1))
        (zz ((v (LadderDarts.ir i)).child 2)) *
      gapAtomSpec (D.gapSpecification (v (LadderDarts.ir i))) L γ η base zz) =
    C.rungW D L γ η i ((C.chainOf (bondIndex G zz)).a 0 - (C.chainOf (bondIndex G zz)).b 0)
      (C.signs.pairs (C.chainOf (bondIndex G zz)) i) := by
  have hu' := fun s => C.uSlot_chainOf (bondIndex G zz) hκ i s
  have hv' := fun s => C.vSlot_chainOf (bondIndex G zz) hκ i s
  unfold rungW
  rw [(C.kU_spec i).2 zz 0, (C.kU_spec i).2 zz 1, (C.kU_spec i).2 zz 2,
    (C.kV_spec i).2 zz 0, (C.kV_spec i).2 zz 1, (C.kV_spec i).2 zz 2,
    gapAtom_eq (C.LD.uDart i) (C.dartsAt_u i) (D.gapSpecification (u (LadderDarts.ir i))) L γ η base zz,
    gapAtom_eq (C.LD.vDart i) (C.dartsAt_v i) (D.gapSpecification (v (LadderDarts.ir i))) L γ η base zz]
  generalize C.chainOf (bondIndex G zz) = ch at hsol hu' hv' ⊢
  have hinv := C.signs.inv_pairs ch hsol
  have hu : ∀ s, bondIndex G zz (C.LD.uDart i s) =
      (C.signs.railU (ch.a 0) (C.signs.pairs ch) i.castSucc + C.signs.tau (C.signs.pairs ch) i 2) +
        (-(C.signs.tau (C.signs.pairs ch) i s)) := by
    intro s
    rw [← hu' s]
    have h2 : (C.signs.inv (ch.a 0) (ch.b 0) (C.signs.pairs ch)).uSlot i s = ch.uSlot i s := by rw [hinv]
    rw [← h2, ChainSigns.inv_uSlot]; abel
  have hv : ∀ s, bondIndex G zz (C.LD.vDart i s) =
      (C.signs.railU (ch.a 0) (C.signs.pairs ch) i.castSucc + C.signs.tau (C.signs.pairs ch) i 2) +
        (-(C.signs.tau (C.signs.pairs ch) i s) - csv C.signs i (ch.a 0 - ch.b 0) s) := by
    intro s
    rw [← hv' s]
    have h2 : (C.signs.inv (ch.a 0) (ch.b 0) (C.signs.pairs ch)).vSlot i s = ch.vSlot i s := by rw [hinv]
    rw [← h2, inv_vSlot]; abel
  congr 1
  · exact atom_factor_eq L γ η base (fun s => bondIndex G zz (C.LD.uDart i s))
      (fun s => -(C.signs.tau (C.signs.pairs ch) i s)) _ hu (C.kU d i) C.signs i 0
      (C.signs.pairs ch i) (fun s => by simp [relLab, tau_eq_tauHom]) _
  · exact atom_factor_eq L γ η base (fun s => bondIndex G zz (C.LD.vDart i s))
      (fun s => -(C.signs.tau (C.signs.pairs ch) i s) - csv C.signs i (ch.a 0 - ch.b 0) s)
      _ hv (C.kV d i) C.signs i (csv C.signs i (ch.a 0 - ch.b 0)) (C.signs.pairs ch i)
      (fun s => by simp [relLab, tau_eq_tauHom]) _


lemma sgn_ne_of_out_ne {x y : GardenDart G} (h : G.molecule.out x ≠ G.molecule.out y) :
    sgn G.molecule x ≠ sgn G.molecule y := by
  unfold sgn
  by_cases hx : G.molecule.out x = true <;> by_cases hy : G.molecule.out y = true <;> simp_all

include C in
/-- **The interior rung weight is a good sum of 36 terms.** -/
theorem rungW_goodSum (D : SplicedKernelData G d) (γ η L R : ℝ) {a b : Fin d → ℝ} (hL : 0 < L)
    (hρ : 0 ≤ L ^ (-γ + η)) (hR : L * L ^ (-γ + η) ≤ R) (i : Fin n) (q : Fin d → ℤ) :
    GoodSum L R a b ((Fin 3 × Fin 2) × (Fin 3 × Fin 2)) (C.rungW D L γ η i q) := by
  have hR0 : 0 ≤ R := le_trans (mul_nonneg hL.le hρ) hR
  have hu := atom_goodSum (a := a) (b := b) γ η hL hρ hR C.signs i 0
    (k1 := C.kU d i 0) (k2 := C.kU d i 1) (k3 := C.kU d i 2)
    (fun h => by have := (C.kU_spec i).1 h; exact absurd this (by decide))
    (fun h => by have := (C.kU_spec i).1 h; exact absurd this (by decide))
    (gapSlots (C.LD.uDart i) (C.dartsAt_u i) (D.gapSpecification (u (LadderDarts.ir i))))
    (fun g hg => by
      have := gapSlots_opposite (C.LD.uDart i) (C.dartsAt_u i) _ g hg
      exact sgn_ne_of_out_ne this)
  have hv := atom_goodSum (a := a) (b := b) γ η hL hρ hR C.signs i (csv C.signs i q)
    (k1 := C.kV d i 0) (k2 := C.kV d i 1) (k3 := C.kV d i 2)
    (fun h => by have := (C.kV_spec i).1 h; exact absurd this (by decide))
    (fun h => by have := (C.kV_spec i).1 h; exact absurd this (by decide))
    (gapSlots (C.LD.vDart i) (C.dartsAt_v i) (D.gapSpecification (v (LadderDarts.ir i))))
    (fun g hg => by
      have := gapSlots_opposite (C.LD.vDart i) (C.dartsAt_v i) _ g hg
      have h2 := sgn_ne_of_out_ne this
      rw [C.sgn_vDart, C.sgn_vDart] at h2
      show sgn G.molecule (C.LD.uDart i g.1) ≠ sgn G.molecule (C.LD.uDart i g.2.1)
      intro h; exact h2 (by rw [h]))
  exact GoodSum.mul hL.le hR0 hu hv

end LadderDarts.Ctx

end WaveTurbulence.LadderDecay

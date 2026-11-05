/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.FactorThm
/-! # The factorization identity (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums Finset

variable {w d : ℕ} {G : Garden w}

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
lemma label_outDart {roots : Fin w → (Fin d → ℤ)} (z : GenDecoration G d roots 0)
    (c : LadderDarts.Ctx.Code n) :
    bondIndex G z.1 (C.outDart c) = LadderDarts.Ctx.labOf (C.chainOf (bondIndex G z.1)) c := by
  rw [C.labOf_chainOf]
  unfold outDart
  split_ifs
  · rfl
  · exact bondIndex_sym z _

include C in
lemma eval_eq_labOf (ch : ChainLab n (Fin d → ℤ)) (hsol : C.signs.IsSol ch) (c : LadderDarts.Ctx.Code n) :
    (chainLab C.signs (ch.a 0) (ch.b 0) c).eval (C.signs.pairs ch) = LadderDarts.Ctx.labOf ch c := by
  have hinv := C.signs.inv_pairs ch hsol
  rw [chainLab_eval]
  rcases c with ⟨i, k⟩ | j | j
  · show (C.signs.inv (ch.a 0) (ch.b 0) (C.signs.pairs ch)).r i k = ch.r i k
    rw [hinv]
  · show (C.signs.inv (ch.a 0) (ch.b 0) (C.signs.pairs ch)).a j = ch.a j
    rw [hinv]
  · show (C.signs.inv (ch.a 0) (ch.b 0) (C.signs.pairs ch)).b j = ch.b j
    rw [hinv]

include C in
/-- **The factorization identity.** For decorations `z`, `zs` agreeing off the interior atoms,
the summand of `z` is the class constant times the chart product. -/
theorem weight_phase_factor (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (D : SplicedKernelData G d) (γ η δ : ℝ)
    (z zs : GenDecoration G d roots 0)
    (hag : ∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z.1 x = bondIndex G zs.1 x)
    (t : (Molecule.ladderAtoms u v) → ℝ) :
    ladderWeight D (Molecule.ladderAtoms u v) L γ η base z.1 *
        ladderPhase D (Molecule.ladderAtoms u v) L γ δ base z.1 t =
      C.classTheta D L γ η δ base roots zs t *
        (∏ c : LadderDarts.Ctx.Code n, D.edgeAmplitude (C.outDart c)
          (base + latticePoint L ((chainLab C.signs ((C.chainOf (bondIndex G zs.1)).a 0)
            ((C.chainOf (bondIndex G zs.1)).b 0) c).eval (C.signs.pairs (C.chainOf (bondIndex G z.1)))))) *
        ∏ i : Fin n, (((C.rungW D L γ η i ((C.chainOf (bondIndex G zs.1)).a 0 -
              (C.chainOf (bondIndex G zs.1)).b 0) (C.signs.pairs (C.chainOf (bondIndex G z.1)) i) : ℝ) : ℂ) *
          rungPh L (δ * L ^ (2 * γ)) (lamHom L (δ * L ^ (2 * γ)) C.signs i
            (C.signs.qrel (C.chainOf (bondIndex G zs.1)) i))
            (tExt _ t (v (LadderDarts.ir i)), tExt _ t (u (LadderDarts.ir i)))
            (C.signs.pairs (C.chainOf (bondIndex G z.1)) i)) := by
  classical
  have hsz := C.isSol_dec hP hL base roots hn z
  have hss := C.isSol_dec hP hL base roots hn zs
  have hκz := bondIndex_sym z
  have hκs := bondIndex_sym zs
  obtain ⟨ha0, hb0, -, -⟩ := C.agree_rails (bondIndex G z.1) (bondIndex G zs.1) hκz hκs hag
  have hq : ∀ i, C.signs.qrel (C.chainOf (bondIndex G z.1)) i =
      C.signs.qrel (C.chainOf (bondIndex G zs.1)) i := by
    intro i; rw [qrel_eq _ _ hsz, qrel_eq _ _ hss, ha0, hb0]
  have hagA : ∀ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, ∀ x, G.molecule.atom x = a →
      bondIndex G z.1 x = bondIndex G zs.1 x :=
    fun a ha x hx => hag x (by rw [hx]; exact (Finset.mem_sdiff.mp ha).2)
  have hEnd : ∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, atomFac D L γ η base z.1 a =
      ∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, atomFac D L γ η base zs.1 a :=
    Finset.prod_congr rfl (fun a ha => atomFac_eq_of_agree hP roots D L γ η base z zs a (hagA a ha))
  have hPh : ∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, phaseAt D L γ δ base z.1 a (tExt _ t a) =
      ∏ a ∈ Molecule.ladderAtoms u v \ intAtoms u v, phaseAt D L γ δ base zs.1 a (tExt _ t a) :=
    Finset.prod_congr rfl (fun a ha =>
      phaseAt_eq_of_agree hP hL base roots D γ δ z zs a (hagA a ha) _)
  have hOut : ∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)) =
      ∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G zs.1 x)) := by
    refine Finset.prod_congr rfl (fun x hx => ?_)
    have hx' := (Finset.mem_filter.mp hx).2
    have : G.molecule.atom x ∉ intAtoms u v := fun h => hx'.2 (C.isT_of_atom_interior x h)
    rw [hag x this]
  have hb : ∏ x ∈ G.molecule.bonds.filter (G.molecule.InGroup (Molecule.ladderAtoms u v)),
      D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)) =
      (∏ c : LadderDarts.Ctx.Code n, D.edgeAmplitude (C.outDart c)
        (base + latticePoint L (bondIndex G z.1 (C.outDart c)))) *
      ∏ x ∈ G.molecule.bonds.filter (fun x => G.molecule.InGroup (Molecule.ladderAtoms u v) x ∧ ¬ C.IsT x),
        D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)) := by
    rw [← C.prod_bonds_T (fun x => D.edgeAmplitude x (base + latticePoint L (bondIndex G z.1 x)))]
    rw [← Finset.prod_filter_mul_prod_filter_not
      (G.molecule.bonds.filter (G.molecule.InGroup (Molecule.ladderAtoms u v))) (fun x => C.IsT x)]
    simp only [Finset.filter_filter]
  have hlab : ∀ c : LadderDarts.Ctx.Code n, bondIndex G z.1 (C.outDart c) =
      (chainLab C.signs ((C.chainOf (bondIndex G zs.1)).a 0) ((C.chainOf (bondIndex G zs.1)).b 0) c).eval
        (C.signs.pairs (C.chainOf (bondIndex G z.1))) := by
    intro c
    rw [← ha0, ← hb0, C.eval_eq_labOf _ hsz, C.label_outDart z]
  rw [ladderWeight_eq_prod, C.prod_atomFac D L γ η base z.1 hκz hsz, hb,
    C.ladderPhase_factor hP hL base roots D γ δ z t]
  simp only [hlab]
  have hz : ∀ i : Fin n,
      Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) * C.rungAU L (bondIndex G z.1) i +
          D.frequency (u (LadderDarts.ir i))) * tExt _ t (u (LadderDarts.ir i))) : ℝ) : ℂ) * Complex.I) *
      Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) * C.rungAV L (bondIndex G z.1) i +
          D.frequency (v (LadderDarts.ir i))) * tExt _ t (v (LadderDarts.ir i))) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((Real.pi * ((δ * L ^ (2 * γ) * ((C.signs.sg i 2 : ℝ) + (C.signs.sg i 3 : ℝ)) *
        ‖latticePoint L (C.signs.qrel (C.chainOf (bondIndex G zs.1)) i)‖ ^ 2 +
        D.frequency (v (LadderDarts.ir i))) * tExt _ t (v (LadderDarts.ir i)) +
        D.frequency (u (LadderDarts.ir i)) * tExt _ t (u (LadderDarts.ir i))) : ℝ) : ℂ) * Complex.I) *
      rungPh L (δ * L ^ (2 * γ)) (lamHom L (δ * L ^ (2 * γ)) C.signs i
        (C.signs.qrel (C.chainOf (bondIndex G zs.1)) i))
        (tExt _ t (v (LadderDarts.ir i)), tExt _ t (u (LadderDarts.ir i)))
        (C.signs.pairs (C.chainOf (bondIndex G z.1)) i) := by
    intro i
    rw [C.rung_phase_eq L δ γ _ _ _ _ (bondIndex G z.1) i, hq i]
  have hint : (LadderDarts.Ctx.interiorAtoms (u := u) (v := v)) = intAtoms u v := rfl
  rw [hint]
  simp only [hz, Finset.prod_mul_distrib]
  rw [hEnd, hPh, hOut]
  unfold classTheta
  rw [show (C.chainOf (bondIndex G z.1)).a 0 - (C.chainOf (bondIndex G z.1)).b 0 =
    (C.chainOf (bondIndex G zs.1)).a 0 - (C.chainOf (bondIndex G zs.1)).b 0 by rw [ha0, hb0]]
  push_cast
  ring

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay

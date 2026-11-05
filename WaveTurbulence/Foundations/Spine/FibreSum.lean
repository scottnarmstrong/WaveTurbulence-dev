/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.HcutLemma
public import WaveTurbulence.Foundations.Spine.FiniteSupp
/-! # The fibre sum over a class of decorations (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.WeylSums Finset

variable {w d : ℕ} {G : Garden w}

lemma pairs_inv {n : ℕ} (S : ChainSigns n) (a0 b0 : Fin d → ℤ) (P : Fin n → Pt d) :
    S.pairs (S.inv a0 b0 P) = P :=
  congrArg (fun c => c.2.2) (S.chartEquiv.right_inv (a0, b0, P))

lemma flux_eq {n : ℕ} (S : ChainSigns n) (ch : ChainLab n (Fin d → ℤ)) (h : S.IsSol ch) :
    ∑ k, chainΔ S k (S.pairs ch k) = ch.a (Fin.last n) - ch.a 0 := by
  have hinv := S.inv_pairs ch h
  have h1 : (S.inv (ch.a 0) (ch.b 0) (S.pairs ch)).a (Fin.last n) = ch.a (Fin.last n) := by rw [hinv]
  rw [LadderDarts.Ctx.inv_a_last] at h1
  rw [← h1]
  simp only [chainΔ, AddMonoidHom.sub_apply]
  rw [add_sub_cancel_left]
  rfl

namespace LadderDarts.Ctx
variable {n : ℕ} {u v : Fin (n + 1 + 1) → GBranch G.tree} (C : LadderDarts.Ctx G.molecule u v)

include C in
/-- Two decorations agreeing off the interior atoms with the same chart pairs coincide. -/
lemma dec_ext (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (z z' : GenDecoration G d roots 0)
    (hag : ∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z.1 x = bondIndex G z'.1 x)
    (hpairs : C.signs.pairs (C.chainOf (bondIndex G z.1)) = C.signs.pairs (C.chainOf (bondIndex G z'.1))) :
    z = z' := by
  have hsz := C.isSol_dec hP hL base roots hn z
  have hsz' := C.isSol_dec hP hL base roots hn z'
  obtain ⟨ha0, hb0, -, -⟩ := C.agree_rails _ _ (bondIndex_sym z) (bondIndex_sym z') hag
  have hch : C.chainOf (bondIndex G z.1) = C.chainOf (bondIndex G z'.1) := by
    rw [← C.signs.inv_pairs _ hsz, ← C.signs.inv_pairs _ hsz', ha0, hb0, hpairs]
  apply bondIndex_injective hP hL base roots z z'
  funext x
  by_cases hx : C.IsT x
  · obtain ⟨c, hc | hc⟩ := hx
    · subst hc
      rw [← C.labOf_chainOf (bondIndex G z.1) c, ← C.labOf_chainOf (bondIndex G z'.1) c, hch]
    · subst hc
      rw [bondIndex_sym, bondIndex_sym]
      rw [← C.labOf_chainOf (bondIndex G z.1) c, ← C.labOf_chainOf (bondIndex G z'.1) c, hch]
  · exact hag x (fun h => hx (C.isT_of_atom_interior x h))


open scoped Classical in
include C in
/-- **The fibre sum.** The sum of a function of the form `θ * g(P(z))` over a class of decorations
is `θ` times the sum of `g` over the constraint set of chart pairs. -/
theorem fibre_sum (hP : G.IsPlain) {L : ℝ} (hL : L ≠ 0) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (boundary : GardenDart G → (Fin d → ℤ))
    (T : Finset ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary))
    (f : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) → ℂ)
    (hT : ∀ z, z ∉ T → f z = 0)
    (zs : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary)) (_hzs : zs ∈ T)
    (θ : ℂ) (g : (Fin n → Pt d) → ℂ) (hθ : θ ≠ 0)
    (hfac : ∀ z : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary),
      (∀ x, G.molecule.atom x ∉ intAtoms u v → bondIndex G z.1.1 x = bondIndex G zs.1.1 x) →
        f z = θ * g (C.signs.pairs (C.chainOf (bondIndex G z.1.1))))
    (SP : Fin n → Finset (Pt d)) (hgsupp : ∀ P, g P ≠ 0 → ∀ k, P k ∈ SP k) :
    ∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
        bondIndex G z.1.1 x = bondIndex G zs.1.1 x), f z =
      θ * ∑ P ∈ (Fintype.piFinset SP).filter (fun P => ∑ k, chainΔ C.signs k (P k) =
        (C.chainOf (bondIndex G zs.1.1)).a (Fin.last n) - (C.chainOf (bondIndex G zs.1.1)).a 0), g P := by
  have hsz := fun z : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) =>
    C.isSol_dec hP hL base roots hn z.1
  have e1 : ∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
        bondIndex G z.1.1 x = bondIndex G zs.1.1 x), f z =
      θ * ∑ z ∈ T.filter (fun z => ∀ x, G.molecule.atom x ∉ intAtoms u v →
        bondIndex G z.1.1 x = bondIndex G zs.1.1 x),
        g (C.signs.pairs (C.chainOf (bondIndex G z.1.1))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun z hz => hfac z (Finset.mem_filter.mp hz).2)
  rw [e1]
  congr 1
  refine Finset.sum_bij_ne_zero (fun z _ _ => C.signs.pairs (C.chainOf (bondIndex G z.1.1))) ?_ ?_ ?_ ?_
  · intro z hz hnz
    rw [Finset.mem_filter, Fintype.mem_piFinset]
    refine ⟨fun k => hgsupp _ hnz k, ?_⟩
    rw [flux_eq C.signs _ (hsz z)]
    obtain ⟨ha0, -, ha1, -⟩ := C.agree_rails _ _ (bondIndex_sym z.1) (bondIndex_sym zs.1)
      (Finset.mem_filter.mp hz).2
    rw [ha0, ha1]
  · intro z hz hnz z' hz' hnz' h
    exact Subtype.ext (C.dec_ext hP hL base roots hn z.1 z'.1
      (fun x hx => ((Finset.mem_filter.mp hz).2 x hx).trans ((Finset.mem_filter.mp hz').2 x hx).symm) h)
  · intro P hPm hgP
    rw [Finset.mem_filter] at hPm
    have hflux : ∑ k, (C.signs.tau P k 2 - C.signs.tau P k 3) =
        ∑ k, (C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G zs.1.1))) k 2 -
          C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G zs.1.1))) k 3) := by
      have h1 := hPm.2
      have h2 := flux_eq C.signs _ (hsz zs)
      have h3 : ∑ k, chainΔ C.signs k (P k) = ∑ k, (C.signs.tau P k 2 - C.signs.tau P k 3) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [chainΔ, tau_eq_tauHom]
      have h4 : ∑ k, chainΔ C.signs k (C.signs.pairs (C.chainOf (bondIndex G zs.1.1)) k) =
          ∑ k, (C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G zs.1.1))) k 2 -
            C.signs.tau (C.signs.pairs (C.chainOf (bondIndex G zs.1.1))) k 3) := by
        refine Finset.sum_congr rfl (fun k _ => ?_)
        simp [chainΔ, tau_eq_tauHom]
      rw [← h3, ← h4, h1, h2]
    obtain ⟨z'', hch, hag''⟩ := C.exists_fibre_element hP hL base roots hn zs.1 P hflux
    have hnot : ∀ x, ¬ G.molecule.InGroup (Molecule.ladderAtoms u v) x → G.molecule.atom x ∉ intAtoms u v :=
      fun x hx h => hx (C.inGroup_of_atom_interior x h)
    let zz : ↥(localLadderDecorations G (Molecule.ladderAtoms u v) roots boundary) :=
      ⟨z'', fun x hx => (hag'' x (hnot x hx)).trans (zs.2 x hx)⟩
    have hpairs : C.signs.pairs (C.chainOf (bondIndex G zz.1.1)) = P := by
      show C.signs.pairs (C.chainOf (bondIndex G z''.1)) = P
      rw [hch, pairs_inv]
    have hfz : f zz = θ * g P := by
      rw [hfac zz hag'', hpairs]
    have hzzT : zz ∈ T := by
      by_contra hcon
      have := hT zz hcon
      rw [hfz] at this
      exact mul_ne_zero hθ hgP this
    exact ⟨zz, Finset.mem_filter.mpr ⟨hzzT, hag''⟩, by rw [hpairs]; exact hgP, hpairs⟩
  · intro z hz hnz
    rfl

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay

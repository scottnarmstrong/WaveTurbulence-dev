/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.AppBConditionedDeletion
public import WaveTurbulence.Foundations.FinalCount.AppBReinsertAdmissibility
public import WaveTurbulence.Foundations.FinalCount.AppBAddedBondDecorations
import Mathlib.Tactic

/-! # Exact reinsertion parameters after fixing the full local tuple -/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.Mole
open Finset
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D]
namespace AppbRealization
variable {M : Molecule V D} {P : AppbPattern} (r : AppbRealization M P)

noncomputable def reinsertedParameters {d : ℕ} (p : AppbCountParameters M d)
    (L : ℝ) (w : Mom d) (q : Fin P.edges.length → (Fin d → ℤ))
    (a b : ℕ) (i : Fin P.edges.length) : AppbCountParameters (r.directedPostWithBond a b i) d where
  momentum := if M.atom (r.edge i).val = r.vertex a then
    appbAddedMomentum (r.vertex a) (r.vertex b) L w (q i) (r.deletionParameters p L w q).momentum
    else appbAddedMomentum (r.vertex b) (r.vertex a) L w (q i) (r.deletionParameters p L w q).momentum
  energy := if M.atom (r.edge i).val = r.vertex a then
    appbAddedEnergy (r.vertex a) (r.vertex b) L w (q i) (r.deletionParameters p L w q).energy
    else appbAddedEnergy (r.vertex b) (r.vertex a) L w (q i) (r.deletionParameters p L w q).energy
  center := Sum.elim (fun x => p.center x.val) (fun _ => p.center (r.edge i).val)
  center_mate := by
    unfold directedPostWithBond
    split_ifs
    all_goals rintro (x|t)
    · exact p.center_mate x.val
    · rfl
    · exact p.center_mate x.val
    · rfl

theorem reinserted_maps_conditioned {d : ℕ} (p : AppbCountParameters M d)
    (L γ δ : ℝ) (w : Mom d) (Adm : (D → (Fin d → ℤ)) → Prop)
    (a b : ℕ) (ha : a ∈ P.vertices) (hb : b ∈ P.vertices)
    (hka : a ∉ P.removed) (hkb : b ∉ P.removed) (i : Fin P.edges.length)
    {q : Fin P.edges.length → (Fin d → ℤ)} {κ : D → (Fin d → ℤ)}
    (hκ : κ ∈ p.decorations L γ δ w Adm) (hq : r.localLabels κ = q) :
    r.reinsertedLabels κ i ∈ (r.reinsertedParameters p L w q a b i).decorations L γ δ w
      (r.reinsertedPostAdmissibility Adm i) := by
  have hk := r.deletion_maps_conditioned p L γ δ w Adm hκ hq
  have hqi : q i = κ (r.edge i).val := (congrFun hq i).symm
  have hav := r.vertex_mem_post a ha hka
  have hbv := r.vertex_mem_post b hb hkb
  have hAdm := r.reinsertedPostAdmissibility_map Adm i κ hκ.2.2 hκ.1.1
  have hlabels : r.reinsertedLabels κ i = appbAddedLabels (r.retainedLabels κ) (q i) := by
    rw [hqi]
    rfl
  refine ⟨?_,⟨?_,?_⟩,hAdm⟩
  · change (r.directedPostWithBond a b i).IsDecoration L w
      (if M.atom (r.edge i).val = r.vertex a then
        appbAddedMomentum (r.vertex a) (r.vertex b) L w (q i) (r.deletionParameters p L w q).momentum
       else appbAddedMomentum (r.vertex b) (r.vertex a) L w (q i) (r.deletionParameters p L w q).momentum) _
    rw [hlabels]
    unfold directedPostWithBond
    split_ifs
    · exact appb_isDecoration_addBond r.post (r.vertex a) (r.vertex b) hav hbv (q i) hk.1
    · exact appb_isDecoration_addBond r.post (r.vertex b) (r.vertex a) hbv hav (q i) hk.1
  · change ∀ v ∈ (r.directedPostWithBond a b i).atoms,
      |(r.directedPostWithBond a b i).Gamma L w (r.reinsertedLabels κ i) v-
        (if M.atom (r.edge i).val = r.vertex a then
          appbAddedEnergy (r.vertex a) (r.vertex b) L w (q i) (r.deletionParameters p L w q).energy
         else appbAddedEnergy (r.vertex b) (r.vertex a) L w (q i) (r.deletionParameters p L w q).energy) v| ≤ δ⁻¹*L^(-2*γ)
    rw [hlabels]
    unfold directedPostWithBond
    split_ifs
    · exact (appb_isRestricted_addBond r.post (r.vertex a) (r.vertex b) hav hbv (q i) hk.2.1).1
    · exact (appb_isRestricted_addBond r.post (r.vertex b) (r.vertex a) hbv hav (q i) hk.2.1).1
  · rintro (x|t)
    · exact hκ.2.1.2 x.val
    · exact hκ.2.1.2 (r.edge i).val

end AppbRealization
end WaveTurbulence.Mole

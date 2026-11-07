/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmEnd1
public import WaveTurbulence.Foundations.FinalCount.AsmHmemShape
/-! **FINALCOUNT-ASSEMBLY (HendAt, part 2): the lift of M₀-chains to the state, and the F-bound of a non-first-stage vine step.**
`ancInv` (inverse of `anc` on the state atoms), `lift_connAvoid` (a chain of `M₀` avoiding the killed darts gives a chain of the state),
`HostConnF` (NAMED INPUT, owner S4-SHAPE: the joints of a non-first-stage collected object stay joined after the earlier removals, TARGET Lemma
subsetvc), `vine_F_le_of_hostConnF` (`ΔF ≤ 0` for such a vine step). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The inverse of `anc` on the state atoms (junk elsewhere). -/
noncomputable def ancInv (h : HSt V D₀) (s : V) : V :=
  if hs : ∃ c ∈ h.s.M.atoms, h.anc c = s then Classical.choose hs else s

theorem ancInv_anc {h : HSt V D₀} (hinj : ∀ c ∈ h.s.M.atoms, ∀ b ∈ h.s.M.atoms, h.anc c = h.anc b → c = b) {c : V}
    (hc : c ∈ h.s.M.atoms) : ancInv h (h.anc c) = c := by
  have hs : ∃ c' ∈ h.s.M.atoms, h.anc c' = h.anc c := ⟨c, hc, rfl⟩
  simp only [ancInv, dif_pos hs]
  exact hinj _ (Classical.choose_spec hs).1 _ hc (Classical.choose_spec hs).2

/-- **Lifting a chain of `M₀` avoiding the killed darts to the state.** -/
theorem lift_connAvoid {M₀ : Molecule V D₀} {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    {ps : List (Object M₀ × Quad D₀)}
    (hinj : ∀ c ∈ h.s.M.atoms, ∀ b ∈ h.s.M.atoms, h.anc c = h.anc b → c = b)
    (hpres : ∀ z : D₀, (∀ x : h.s.D, h.s.down x ≠ z) → ∃ p ∈ ps, z ∈ PieceKill p.1 p.2)
    (Kd : Set D₀) (hKd : KillS ps ⊆ Kd) (rel' : V → V → Prop)
    (hrel : ∀ x : h.s.D, h.s.down x ∉ Kd → M₀.mate (h.s.down x) ∉ Kd → rel' (h.s.M.atom x) (h.s.M.atom (h.s.M.mate x)))
    {s t : V} (hst : ConnAvoid M₀ Kd s t) : Relation.EqvGen rel' (ancInv h s) (ancInv h t) := by
  unfold ConnAvoid at hst
  induction hst with
  | rel s t hr =>
    obtain ⟨z, hs, ht, hz, hmz⟩ := hr
    have hex : ∃ x₀ : h.s.D, h.s.down x₀ = z := by
      by_contra hno
      push Not at hno
      obtain ⟨p, hp, hk⟩ := hpres z hno
      exact hz (hKd ⟨p, hp, hk⟩)
    obtain ⟨x₀, hx₀⟩ := hex
    have hc1 : h.anc (h.s.M.atom x₀) = s := by rw [← hs, ← hx₀, hA.atom]
    have hc2 : h.anc (h.s.M.atom (h.s.M.mate x₀)) = t := by rw [← ht, ← hx₀, hD.mate, hA.atom]
    have hs1 : ancInv h s = h.s.M.atom x₀ := by rw [← hc1]; exact ancInv_anc hinj (h.s.M.atom_mem x₀)
    have ht1 : ancInv h t = h.s.M.atom (h.s.M.mate x₀) := by rw [← hc2]; exact ancInv_anc hinj (h.s.M.atom_mem _)
    rw [hs1, ht1]
    exact Relation.EqvGen.rel _ _ (hrel x₀ (by rw [hx₀]; exact hz) (by rw [hx₀]; exact hmz))
  | refl s => exact Relation.EqvGen.refl _
  | symm s t _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans s t u _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

/-- **NAMED INPUT (owner S4-SHAPE; TARGET Lemma subsetvc, `subsetvc_simultaneous_removal_connected`, and TARGET L2128 last sentence):** after
the Step-1 vine removals along pairwise atom-disjoint collected objects `ps`, the joints of a further collected object `p` that is not a
first-stage object (CN / root-CL vine) are still joined outside the removed darts, so its removal creates no component. -/
def HostConnF (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀))
    (L γ η : ℝ) (w : Mom d) (A0 : Set (D₀ → (Fin d → ℤ))) : Prop :=
  ∀ κ ∈ A0, ∀ (ps : List (Object M₀ × Quad D₀)) (p : Object M₀ × Quad D₀), (∀ q ∈ ps, PieceData C Un L γ η w κ q) →
    PieceData C Un L γ η w κ p → p.1 ∉ Fst → (p :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) →
    ConnAvoid M₀ (KillS ps ∪ PieceKill p.1 p.2) p.1.upper p.1.lower

theorem vine_F_le_of_hostConnF [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)}
    (hHF : HostConnF M₀ C Un Fst L γ η w A0) (hκ : κ ∈ A0) {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (hD : DartRel M₀ b.s)
    {ps : List (Object M₀ × Quad D₀)} (hI : ConnData M₀ C Un Fst L γ η w κ b ps) (K : VineCut b.s.M) (U : Object M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hint : UIntact U b) (hUF : U ∉ Fst) : K.post.numComponents ≤ b.s.M.numComponents := by
  obtain ⟨hinj, hps, hpw, hrem, hpres, he1, he2, he3, hfo⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hup : M₀.atom (b.s.down K.x₁) = K.C.upper := by rw [hA.atom, K.cut_a.2.2.1, hUe _ K.a_mem]
  have hlow : M₀.atom (b.s.down K.y₁) = K.C.lower := by rw [hA.atom, K.My₁, hUe _ K.b_mem]
  have hup2 : M₀.atom (b.s.down K.x₂) = K.C.upper := by rw [hA.atom, K.Mx₂, hUe _ K.a_mem]
  have hlow2 : M₀.atom (b.s.down K.y₂) = K.C.lower := by rw [hA.atom, K.My₂, hUe _ K.b_mem]
  have hJ : (K.C.upper = U.upper ∧ K.C.lower = U.lower) ∨ (K.C.upper = U.lower ∧ K.C.lower = U.upper) := by
    rcases hUJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hup ▸ e1, hlow ▸ e2⟩
    · exact Or.inr ⟨hup ▸ e1, hlow ▸ e2⟩
  set N : Quad D₀ := (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂) with hN
  have hpd : PieceData C Un L γ η w κ (U, N) := by
    refine ⟨hU, hUD, hUJ, ?_, ?_, ?_, ?_⟩
    · show M₀.atom (b.s.down K.x₂) = M₀.atom (b.s.down K.x₁)
      rw [hA.atom, hA.atom, K.Mx₂, K.cut_a.2.2.1]
    · show M₀.atom (b.s.down K.y₂) = M₀.atom (b.s.down K.y₁)
      rw [hA.atom, hA.atom, K.My₂, K.My₁]
    · intro e
      have h1 := K.cut_a.2.2.2.2.2.1
      have h2 := K.cut_a.2.2.2.2.2.2
      rw [hA.inj e] at h1; rw [h1] at h2; cases h2
    · intro e
      have h1 := K.cut_b.2.2.2.2.2.1
      have h2 := K.cut_b.2.2.2.2.2.2
      rw [hA.inj e] at h1; rw [h1] at h2; cases h2
  have hpw' : ((U, N) :: ps).Pairwise (fun p q => Disjoint p.1.atoms q.1.atoms) := by
    refine List.pairwise_cons.2 ⟨fun q hq => ?_, hpw⟩
    refine Finset.disjoint_left.2 fun v hv hvq => ?_
    exact hrem q hq v hvq (hint v hv)
  have hconn := hHF κ hκ ps (U, N) hps hpd hUF hpw'
  set G : Finset b.s.D := {K.x₁, K.x₂, K.y₁, K.y₂} with hG
  have hGk : ∀ y ∈ G, b.s.down y ∈ PieceKill U N := by
    intro y hy
    simp only [hG, Finset.mem_insert, Finset.mem_singleton] at hy
    have hat : ∀ v ∈ K.C.atoms, v ∈ U.atoms := fun v hv => by rw [hUK]; exact hv
    rcases hy with rfl | rfl | rfl | rfl
    · exact ⟨hup ▸ hat _ K.a_mem, fun _ => Or.inl rfl⟩
    · exact ⟨hup2 ▸ hat _ K.a_mem, fun _ => Or.inr (Or.inl rfl)⟩
    · exact ⟨hlow ▸ hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inl rfl))⟩
    · exact ⟨hlow2 ▸ hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inr rfl))⟩
  have hint_not : ∀ y : b.s.D, b.s.down y ∉ KillS ps ∪ PieceKill U N → b.s.M.atom y ∉ vineInterior K := by
    intro y hy hyi
    simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hyi
    obtain ⟨hyC, hy1, hy2⟩ := hyi
    apply hy
    right
    have hz1 : M₀.atom (b.s.down y) = b.s.M.atom y := by rw [hA.atom, hUe _ hyC]
    refine ⟨by rw [hz1, hUK]; exact hyC, fun hj => ?_⟩
    rw [hz1] at hj
    exfalso
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · rcases hj with hj | hj
      · exact hy1 (hj.trans e1.symm)
      · exact hy2 (hj.trans e2.symm)
    · rcases hj with hj | hj
      · exact hy2 (hj.trans e2.symm)
      · exact hy1 (hj.trans e1.symm)
  have hr := lift_connAvoid hA hD hinj hpres (KillS ps ∪ PieceKill U N) Set.subset_union_left
    (fun s t : V => s ∉ vineInterior K ∧ t ∉ vineInterior K ∧ ∃ z, b.s.M.atom z = s ∧ b.s.M.atom (b.s.M.mate z) = t ∧ z ∉ G ∧
      b.s.M.mate z ∉ G)
    (by
      intro x hx hmx
      rw [hD.mate] at hmx
      refine ⟨hint_not x hx, hint_not _ hmx, x, rfl, rfl, fun hxG => hx (Or.inr (hGk x hxG)), fun hxG => hmx (Or.inr (hGk _ hxG))⟩)
    hconn
  have hUu : U.upper ∈ U.atoms := object_mem_of_joint U (Or.inl rfl)
  have hUl : U.lower ∈ U.atoms := object_mem_of_joint U (Or.inr rfl)
  have e1 : ancInv b U.upper = U.upper := by
    have := ancInv_anc hinj (hint _ hUu).1
    rwa [hA.eps _ (hint _ hUu).1 (hint _ hUu).2] at this
  have e2 : ancInv b U.lower = U.lower := by
    have := ancInv_anc hinj (hint _ hUl).1
    rwa [hA.eps _ (hint _ hUl).1 (hint _ hUl).2] at this
  rw [e1, e2] at hr
  refine vineCut_F_le_of_outside K (G := G) (fun z hz => hz) ?_
  unfold VineOutsideConn
  rcases hJ with ⟨j1, j2⟩ | ⟨j1, j2⟩
  · rw [j1, j2]; exact hr
  · rw [j1, j2]; exact Relation.EqvGen.symm _ _ hr

end WaveTurbulence.FinalCountAsm

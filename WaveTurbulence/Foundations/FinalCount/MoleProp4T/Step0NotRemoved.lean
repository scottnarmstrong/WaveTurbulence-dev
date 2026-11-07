/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.FinalCount.MoleProp4T.Step0Transfer
import Mathlib.Tactic

/-! # Pulling the second alternative back through a (Y2) sequence that keeps `ℓ`

If `ℓ` has no end in the chain, the (Y2) bound on `𝕄 ∖ ℓ` transports decorations to `post(𝕄 ∖ ℓ) ≅ 𝕄′ ∖ ℓ`. The multiplier
is the one witnessing the pulled-back condition, so the transported decorations extend to `𝕄′`-decorations that are LG
and satisfy `Q₁`.
-/

@[expose] public section
set_option autoImplicit false
open Finset
open scoped ENNReal
namespace WaveTurbulence.MoleProp4
variable {V D E : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E]

omit [DecidableEq V] [Fintype D] [DecidableEq D] [Fintype E] [DecidableEq E] in
/-- Large gaps along a dart relabelling. -/
theorem largeGap_relabel (M : Molecule V D) (N : Molecule V E) (f : D ≃ E) (ha : ∀ x, N.atom (f x) = M.atom x)
    (ho : ∀ x, N.out (f x) = M.out x) {d : ℕ} {L γ η : ℝ} {κ : D → (Fin d → ℤ)}
    (h : MoleProp.LargeGap M L γ η 0 κ) : MoleProp.LargeGap N L γ η 0 (MoleProp.relabelDartLabels f κ) := by
  intro y₁ y₂ h12 hdir
  obtain ⟨x₁, rfl⟩ := f.surjective y₁
  obtain ⟨x₂, rfl⟩ := f.surjective y₂
  have hkv (x : D) : Molecule.kvec L 0 (MoleProp.relabelDartLabels f κ) (f x) = Molecule.kvec L 0 κ x := by
    simp only [Molecule.kvec, MoleProp.relabelDartLabels, Equiv.coe_fn_mk, f.symm_apply_apply]
  rw [hkv, hkv]
  exact h x₁ x₂ (by rw [← ha, ← ha]; exact h12) (by rw [← ho, ← ho]; exact hdir)

namespace Y2End
variable {M : Molecule V D} {C : YChain M} (E : Y2End C)

theorem outEnd_toTwoExit_xy (e : D) (hu : M.atom e ∉ C.set) (hw : M.atom (M.mate e) ∉ C.set)
    (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2)
    (hcapN : ∀ v ∈ (MoleProp.eraseBond M e).atoms, (MoleProp.eraseBond M e).outdeg v ≤ 2 ∧
      (MoleProp.eraseBond M e).indeg v ≤ 2) :
    ((E.outEnd e hu hw).toTwoExit hcapN).x.val = (E.toTwoExit hcap).x ∧
      ((E.outEnd e hu hw).toTwoExit hcapN).y.val = (E.toTwoExit hcap).y := by
  unfold toTwoExit
  by_cases h : M.out E.x = true
  · have h' : (MoleProp.eraseBond M e).out (E.outEnd e hu hw).x = true := h
    rw [dite_eq_left_of_eq_true (eq_true h), dite_eq_left_of_eq_true (eq_true h')]
    exact ⟨rfl, rfl⟩
  · have h' : ¬ (MoleProp.eraseBond M e).out (E.outEnd e hu hw).x = true := h
    rw [dite_eq_right_of_eq_false (eq_false h), dite_eq_right_of_eq_false (eq_false h')]
    exact ⟨rfl, rfl⟩

/-- **The second alternative through a (Y2) sequence keeping `ℓ`.** -/
theorem split_second_kept (hcap : ∀ v ∈ M.atoms, M.outdeg v ≤ 2 ∧ M.indeg v ≤ 2) (e : D)
    (heY : M.atom e ∉ (E.toTwoExit hcap).Y ∧ M.atom (M.mate e) ∉ (E.toTwoExit hcap).Y)
    (hu : M.atom e ∉ C.set) (hw : M.atom (M.mate e) ∉ C.set)
    (hconnN : ∀ u ∈ M.atoms, ∀ w ∈ M.atoms, (MoleProp.eraseBond M e).SameComponent u w)
    {d : ℕ} {L γ δ η C1 K ε₂ : ℝ} (P : Finset V → ℝ)
    (Q₁ : (Degen.RetainedDart M (E.toTwoExit hcap).Y ⊕ Bool → (Fin d → ℤ)) → Prop)
    (hY2N : let T' := (E.outEnd e hu hw).toTwoExit (caps_eraseBond M e hcap);
      (∀ S ∈ MoleProp.ladderCells T'.post, T'.c ∈ S → GoodCell T'.post S) →
      ∀ Adm : (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → lgAdm (MoleProp.eraseBond M e) L γ η P κ) →
      ∀ W : ℤ → (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop,
      (∀ κ, Adm κ → (∀ x, κ ((MoleProp.eraseBond M e).mate x) = κ x) →
        ∃ g ∈ Finset.Icc (0 : ℤ) 4, MoleProp.LargeGap T'.post L γ (η / 2) 0 (T'.postLabels κ g) ∧ W g κ) →
        MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d) Adm P ≤
          ENNReal.ofReal K * ⨆ g ∈ Finset.Icc (0 : ℤ) 4,
            AFreeSupAdm T'.post d L γ δ C1 fun P' => T'.postAdm Adm W L γ (η / 2) P' g)
    (hQ₁ : ∀ P' : Finset V → ℝ,
      (∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)),
        0 ≤ P' S) →
      MoleProp.countAFree (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)) L γ δ C1 (0 : Mom d)
        (fun τ => lgAdm (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)) L γ (η / 2) P' τ ∧
          MoleProp.erasedBondAdmissibility (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)
            (fun κ0 => MoleProp.LargeGap (E.toTwoExit hcap).post L γ (η / 2) 0 κ0 ∧ Q₁ κ0) τ) P' ≤
        ENNReal.ofReal ε₂) :
    MoleProp.countAFree (MoleProp.eraseBond M e) L γ δ C1 (0 : Mom d)
      (fun κ => lgAdm (MoleProp.eraseBond M e) L γ η P κ ∧
        MoleProp.erasedBondAdmissibility M e
          (fun κ0 => MoleProp.LargeGap M L γ η 0 κ0 ∧ (E.toTwoExit hcap).pullQ L γ η Q₁ κ0) κ) P ≤
      ENNReal.ofReal K * ENNReal.ofReal ε₂ := by
  classical
  have hY := E.toTwoExit_Y hcap
  have hcapN := caps_eraseBond M e hcap
  obtain ⟨hTY, hTc, hTd⟩ := E.outEnd_toTwoExit e hu hw hcap hcapN
  obtain ⟨hTx, hTy⟩ := E.outEnd_toTwoExit_xy e hu hw hcap hcapN
  -- the good cells of `𝕄′ ∖ ℓ`
  have hgood : ∀ S ∈ MoleProp.ladderCells ((E.outEnd e hu hw).toTwoExit hcapN).post,
      ((E.outEnd e hu hw).toTwoExit hcapN).c ∈ S → GoodCell ((E.outEnd e hu hw).toTwoExit hcapN).post S := by
    intro S hS _
    have hY' : ((E.outEnd e hu hw).toTwoExit hcapN).Y = C.set := by rw [hTY, hY]
    have hz : M.atom e ∈ ((E.outEnd e hu hw).toTwoExit hcapN).post.atoms := by
      rw [TwoExit.post_atoms, hY']; exact mem_sdiff.mpr ⟨M.atom_mem e, hu⟩
    refine goodCell_of_connected_low (TwoExit.post_connected _ hconnN) hz ?_ hS
    rw [TwoExit.post_deg _ (by rw [hY']; exact hu)]
    have h1 := deg_eraseBond_add M e (M.atom e)
    have h2 := hcap _ (M.atom_mem e)
    have h3 := Mole.outdeg_add_indeg M (M.atom e)
    rw [ite_of_pos rfl] at h1
    omega
  -- the witness: the pulled-back multiplier
  let W : ℤ → (MoleProp.WithoutBondDart M e → (Fin d → ℤ)) → Prop := fun g κ'' =>
    ∃ κ : D → (Fin d → ℤ), MoleProp.LargeGap M L γ η 0 κ ∧ (∀ x, κ (M.mate x) = κ x) ∧
      (fun x : MoleProp.WithoutBondDart M e => κ x.val) = κ'' ∧
      MoleProp.LargeGap (E.toTwoExit hcap).post L γ (η / 2) 0 ((E.toTwoExit hcap).postLabels κ g) ∧
      Q₁ ((E.toTwoExit hcap).postLabels κ g)
  -- restrictions of transported labels
  let f2 := (E.toTwoExit hcap).postEraseBondEquiv e heY ((E.outEnd e hu hw).toTwoExit hcapN) hTY
  have hres : ∀ (κ : D → (Fin d → ℤ)) (g : ℤ),
      MoleProp.relabelDartLabels f2 (((E.outEnd e hu hw).toTwoExit hcapN).postLabels
        (fun x : MoleProp.WithoutBondDart M e => κ x.val) g) =
      fun z => (E.toTwoExit hcap).postLabels κ g z.val := by
    intro κ g
    funext ⟨z, hz⟩
    rcases z with w | bo
    · rfl
    · change ((E.outEnd e hu hw).toTwoExit hcapN).postLabels (fun x : MoleProp.WithoutBondDart M e => κ x.val) g
        (Sum.inr bo) = (E.toTwoExit hcap).postLabels κ g (Sum.inr bo)
      simp only [TwoExit.postLabels, Sum.elim_inr, hTx, hTy]
  have hA2 : ((E.outEnd e hu hw).toTwoExit hcapN).post.atoms =
      (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)).atoms := by
    change _ = (E.toTwoExit hcap).post.atoms
    rw [TwoExit.post_atoms, TwoExit.post_atoms, hTY]; rfl
  have ha2 : ∀ x, (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)).atom (f2 x) =
      ((E.outEnd e hu hw).toTwoExit hcapN).post.atom x := by
    rintro (w | bo)
    · rfl
    · cases bo
      · change (E.toTwoExit hcap).c = ((E.outEnd e hu hw).toTwoExit hcapN).c; exact hTc.symm
      · change (E.toTwoExit hcap).d = ((E.outEnd e hu hw).toTwoExit hcapN).d; exact hTd.symm
  have hm2 : ∀ x, (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)).mate (f2 x) =
      f2 (((E.outEnd e hu hw).toTwoExit hcapN).post.mate x) := by
    rintro (w | bo)
    · rfl
    · rfl
  have ho2 : ∀ x, (MoleProp.eraseBond (E.toTwoExit hcap).post (Sum.inl ⟨e, heY.1, heY.2⟩)).out (f2 x) =
      ((E.outEnd e hu hw).toTwoExit hcapN).post.out x := by
    rintro (w | bo)
    · rfl
    · rfl
  refine (hY2N hgood _ (fun κ h => h.1) W ?_).trans (mul_le_mul' le_rfl (iSup₂_le fun g _ => iSup₂_le
    fun P' hP' => ?_))
  · -- every admissible decoration has a witnessing multiplier
    rintro κ'' ⟨_, κ, ⟨hLG, g, hg, hLGp, hq⟩, hsym, rfl⟩ _
    refine ⟨g, hg, ?_, κ, hLG, hsym, rfl, hLGp, hq⟩
    have h1 := MoleProp.largeGap_eraseBond _ (Sum.inl ⟨e, heY.1, heY.2⟩) L γ (η / 2) 0 hLGp
    have h2 := largeGap_relabel _ _ f2.symm (fun x => by
        obtain ⟨y, rfl⟩ := f2.surjective x; rw [f2.symm_apply_apply]; exact (ha2 y).symm)
      (fun x => by obtain ⟨y, rfl⟩ := f2.surjective x; rw [f2.symm_apply_apply]; exact (ho2 y).symm) h1
    have h3 : MoleProp.relabelDartLabels f2.symm (fun z => (E.toTwoExit hcap).postLabels κ g z.val) =
        ((E.outEnd e hu hw).toTwoExit hcapN).postLabels (fun x : MoleProp.WithoutBondDart M e => κ x.val) g := by
      rw [← hres κ g]
      funext x; simp [MoleProp.relabelDartLabels]
    rw [h3] at h2
    exact h2
  · have hcells : ∀ S ∈ MoleProp.ladderCells (MoleProp.eraseBond (E.toTwoExit hcap).post
        (Sum.inl ⟨e, heY.1, heY.2⟩)), 0 ≤ P' S := by
      intro S hS
      rw [← ladderCells_eq_of_dart_equiv' _ _ f2 hA2 ha2 hm2 ho2] at hS
      exact hP' S hS
    refine le_trans ?_ (hQ₁ P' hcells)
    refine MoleProp.countAFree_le_of_dart_equiv _ _ f2 hA2 ha2 hm2 ho2 L γ δ C1 0 _ _ (fun τ h => ⟨?_, ?_⟩) P'
    · exact lgAdm_relabel _ _ f2 hA2 ha2 hm2 ho2 h.1
    · obtain ⟨_, κ'', _, _, ⟨κ, _, hsym, rfl, hLGp, hq⟩, rfl⟩ := h
      rw [hres κ g]
      exact ⟨(E.toTwoExit hcap).postLabels κ g, ⟨hLGp, hq⟩, (E.toTwoExit hcap).postLabels_mate hsym g, rfl⟩

end Y2End
end WaveTurbulence.MoleProp4

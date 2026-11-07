/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HRun
public import WaveTurbulence.Foundations.FinalCount.G3EraseSt
public import WaveTurbulence.Foundations.FinalCount.G3NoTriple
public import WaveTurbulence.Foundations.FinalCount.G3TriPull
public import WaveTurbulence.Foundations.FinalCount.G3Rel
public import WaveTurbulence.Foundations.FinalCount.G3Cyc3
/-! **FINALCOUNT-G3: Step 5 with history** and the erase lemmas for the run invariants (`HInv`, `HGap`, `DartRel`,
`EpsLe`, `NoSGTriangle`).  The history, the cut records and the ancestor map are unchanged by an erasure. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ}

/-- The state with history after erasing `v` (no cut is performed: history, records and ancestors are kept). -/
noncomputable def HSt.eraseH (h : HSt V D₀) (v : V) : HSt V D₀ := ⟨h.s.eraseSt v, h.hist, h.crec, h.anc⟩

/-- Before the deletion of the ghost neighbours. -/
def HSt.erase0H (h : HSt V D₀) (v : V) : HSt V D₀ := ⟨h.s.erase0 v, h.hist, h.crec, h.anc⟩

/-- **Step 5 with history** (R27, TARGET Remark `remtame`): erase a `ε`-atom `v` of degree `≥ 3` at which every triple has gap `0`
(zero gap and `deg ≥ 3`: the atom is tame and met as `v₃` of Operation 2 or `v` of Operation 4). -/
inductive HStep5 (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : V → HSt V D₀ → HSt V D₀ → Prop
  | erase (h : HSt V D₀) (v : V) (hv : v ∈ h.s.M.atoms) (hd : 3 ≤ h.s.M.deg v) (hε : h.s.cls v = .eps)
      (hzg : ∀ x y : h.s.D, h.s.M.atom x = v → h.s.M.atom y = v → h.s.M.out x = false → h.s.M.out y = true →
        y ≠ h.s.M.mate x → Molecule.gapAt L w (κ ∘ h.s.down) x y = 0) :
      HStep5 L w κ v h (h.eraseH v)

theorem HStep5.step {h h' : HSt V D₀} {v : V} (hs : HStep5 L w κ v h h') : Step5 h.s h'.s := by
  cases hs with
  | erase _ _ hv hd hε _ => exact Step5.erase _ _ hv hd hε

theorem HInv.eraseH {h : HSt V D₀} (hI : HInv L γ η w κ h) (v : V) : HInv L γ η w κ (h.eraseH v) where
  mem := fun a ha => hI.mem a (Finset.mem_of_mem_erase (Finset.mem_filter.1 ha).1)
  cmp := fun a ha a' ha' => hI.cmp a (Finset.mem_of_mem_erase (Finset.mem_filter.1 ha).1) a'
    (Finset.mem_of_mem_erase (Finset.mem_filter.1 ha').1)
  ok := fun a ha => hI.ok a (Finset.mem_of_mem_erase (Finset.mem_filter.1 ha).1)

theorem HGap.erase0H {h : HSt V D₀} (hG : HGap L w κ h) (hg : Good R h.s) (v : V) :
    HGap L w κ (h.erase0H v) where
  chg := by
    intro a ha hae h4'
    have haM : a ∈ h.s.M.atoms := Finset.mem_of_mem_erase ha
    have hav : a ≠ v := Finset.ne_of_mem_erase ha
    have hsum := eraseAt_dartsAt_card h.s.M v hav
    have hle := deg_le_four h.s.M (hg.1.bounds a haM)
    have h44 : (eraseAt h.s.M v).deg a = 4 := h4'
    have hm : mult h.s.M v a = 0 := by omega
    have hdeg : h.s.M.deg a = 4 := by omega
    have := hG.chg a haM hae hdeg
    show ∑ x ∈ (eraseAt h.s.M v).dartsAt a,
      (fun z => h.s.M.dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z) x.1 = 0
    refine (eraseAt_sum h.s.M v hav
      (fun z => h.s.M.dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z)).trans ?_
    rw [Finset.filter_true_of_mem]
    · exact this
    · intro x hx
      intro hxv
      have : x ∈ (h.s.M.dartsAt a).filter fun x => h.s.M.atom (h.s.M.mate x) = v :=
        Finset.mem_filter.2 ⟨hx, hxv⟩
      have h0 : ((h.s.M.dartsAt a).filter fun x => h.s.M.atom (h.s.M.mate x) = v).card = 0 := hm
      rw [Finset.card_eq_zero] at h0
      rw [h0] at this; simp at this
  dg := by
    intro a ha hac x y hx hy hox hoy
    obtain ⟨p, vis, hr, hn⟩ := hG.dg a (Finset.mem_of_mem_erase ha) hac x.1 y.1 hx hy hox hoy
    exact ⟨p, vis, hr, hn⟩

theorem HGap.eraseH {h : HSt V D₀} (hG : HGap L w κ h) (hg : Good R h.s) (v : V) :
    HGap L w κ (h.eraseH v) :=
  HGap.delSt (h := h.erase0H v) (hG.erase0H hg v) (keepE h.s v) (keepE_closed h.s v)

theorem DartRel.erase0 {M₀ : Molecule V D₀} {s : St.{u} V D₀} (h : DartRel M₀ s) (v : V) :
    DartRel M₀ (s.erase0 v) :=
  ⟨fun x => h.mate x.1, fun x => h.out x.1, fun x hx => h.eps x.1 hx⟩

theorem DartRel.eraseSt {M₀ : Molecule V D₀} {s : St.{u} V D₀} (h : DartRel M₀ s) (v : V) :
    DartRel M₀ (s.eraseSt v) :=
  DartRel.delSt (s := s.erase0 v) (h.erase0 v) _ (keepE_closed s v)

theorem EpsLe.erase0 (s : St.{u} V D₀) (v : V) : EpsLe s (s.erase0 v) := by
  intro a ha b hb hca hcb
  refine ⟨⟨Finset.mem_of_mem_erase ha, hca⟩, ⟨Finset.mem_of_mem_erase hb, hcb⟩, ?_⟩
  unfold Molecule.bondsBetween
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

theorem EpsLe.delSt' {s₁ s : St.{u} V D₀} (h : EpsLe s₁ s) (P : V → Prop) [DecidablePred P] (hP : PClosed s.M P) :
    EpsLe s₁ (s.delSt P hP) := by
  intro a ha b hb hca hcb
  have ha' := Finset.mem_filter.1 (show a ∈ s.M.atoms.filter P from ha)
  have hb' := Finset.mem_filter.1 (show b ∈ s.M.atoms.filter P from hb)
  obtain ⟨h1, h2, h3⟩ := h a ha'.1 b hb'.1 hca hcb
  refine ⟨h1, h2, le_trans ?_ h3⟩
  unfold Molecule.bondsBetween
  refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
  · intro x hx
    simp only [Finset.coe_filter, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hx
    simp only [Finset.mem_coe, Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hx
  · intro x _ y _ e; exact Subtype.ext e

theorem EpsLe.eraseSt (s : St.{u} V D₀) (v : V) : EpsLe s (s.eraseSt v) :=
  (EpsLe.erase0 s v).delSt' _ (keepE_closed s v)

theorem TriData.pullErase [Infinite V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {v : V}
    (T' : TriData (eraseAt M v)) :
    ∃ T : TriData M, (∀ j, T.a j = (T'.a j).1) ∧ ∀ j, T.b j = (T'.b j).1 := by
  obtain ⟨f, hf, hfr⟩ := exists_three_fresh M.atoms
  refine ⟨⟨T'.t, f, fun j => (T'.a j).1, fun j => (T'.b j).1, fun j => Finset.mem_of_mem_erase (T'.t_mem j),
    T'.t_inj, hfr, hf, fun j => T'.atom_a j, fun j => T'.atom_b j, fun j => T'.out_a j, fun j => T'.out_b j,
    fun j => congrArg Subtype.val (T'.mate_b j)⟩, fun _ => rfl, fun _ => rfl⟩

theorem TriData.pullRestrict [Infinite V] {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D}
    {P : V → Prop} [DecidablePred P] {hP : PClosed M P} (T' : TriData (restrictP M P hP)) :
    ∃ T : TriData M, (∀ j, T.a j = (T'.a j).1) ∧ ∀ j, T.b j = (T'.b j).1 := by
  obtain ⟨f, hf, hfr⟩ := exists_three_fresh M.atoms
  refine ⟨⟨T'.t, f, fun j => (T'.a j).1, fun j => (T'.b j).1,
    fun j => (Finset.mem_filter.1 (T'.t_mem j)).1,
    T'.t_inj, hfr, hf, fun j => T'.atom_a j, fun j => T'.atom_b j, fun j => T'.out_a j, fun j => T'.out_b j,
    fun j => congrArg Subtype.val (T'.mate_b j)⟩, fun _ => rfl, fun _ => rfl⟩

theorem NoSGTriangle.eraseSt [Infinite V] {s : St.{u} V D₀} (h : NoSGTriangle L γ η w κ s) (v : V) :
    NoSGTriangle L γ η w κ (s.eraseSt v) := by
  intro T' hT
  obtain ⟨T0, ha0, hb0⟩ := TriData.pullRestrict (M := eraseAt s.M v) (P := keepE s v) (hP := keepE_closed s v) T'
  obtain ⟨T, ha, hb⟩ := TriData.pullErase T0
  apply h T
  rw [ha, hb, ha, hb]
  rw [ha0, hb0, ha0, hb0] at *
  exact hT

end WaveTurbulence.FinalCountG3

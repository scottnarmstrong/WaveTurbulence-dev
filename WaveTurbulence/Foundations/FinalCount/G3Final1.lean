/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Init
/-! **FINALCOUNT-G3**: consequences of the invariants for the final molecule: degrees, classification, odd atoms,
and the number of imperfect components (TARGET Prop `finalmol`, L2184--L2190 via the invariant `4V-2E-2(Vα+Vβ)`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type*}

/-- The defect of an atom: `4 - d(v)` for an `ε`-atom, `2 - d(v)` for an `α`- or `β`-atom. -/
def contrib (s : St.{u} V D₀) (a : V) : ℤ := (s.cls a).base - s.M.deg a

section
variable {s : St.{u} V D₀} {R : ℕ}

theorem Good.contrib_nonneg (hg : Good R s) {a : V} (ha : a ∈ s.M.atoms) : 0 ≤ contrib s a := by
  have hle := deg_le_four s.M (hg.1.bounds a ha)
  unfold contrib
  by_cases he : s.cls a = .eps
  · rw [he]; simp only [Cls.base]; omega
  · have := (hg.1.ab a ha he).1
    rcases hc : s.cls a with _ | _ | _ | _
    · exact absurd hc he
    · simp only [Cls.base]; omega
    · simp only [Cls.base]; omega
    · exact absurd hc (hg.2 a ha)

theorem Good.sum_contrib (hg : Good R s) : ∑ a ∈ s.M.atoms, contrib s a = 2 * R := by
  unfold contrib
  rw [Finset.sum_sub_distrib]
  have h1 := hg.1.phi
  have h2 := sum_deg_eq s.M
  have h3 : ∑ a ∈ s.M.atoms, ((s.M.deg a : ℕ) : ℤ) = (Fintype.card s.D : ℤ) := by exact_mod_cast h2
  rw [h1, h3]; ring

/-- The sum of the degrees over a union of components is even (twice the number of bonds). -/
theorem even_sum_deg_closed (P : V → Prop) [DecidablePred P] (h : PClosed s.M P) :
    Even (∑ a ∈ s.M.atoms.filter P, s.M.deg a) := by
  have h1 := card_darts_eq_two_bonds (restrictP s.M P h)
  have h2 := sum_deg_eq (restrictP s.M P h)
  have h3 : ∑ a ∈ (restrictP s.M P h).atoms, (restrictP s.M P h).deg a = ∑ a ∈ s.M.atoms.filter P, s.M.deg a := by
    refine Finset.sum_congr rfl fun a ha => ?_
    exact restrictP_deg s.M P h (Finset.mem_filter.1 ha).2
  rw [← h3, h2, h1]
  exact even_two_mul _

theorem sc_refl (a : V) : s.M.SameComponent a a := Relation.EqvGen.refl _
theorem sc_symm {a b : V} (h : s.M.SameComponent a b) : s.M.SameComponent b a := Relation.EqvGen.symm _ _ h
theorem sc_trans {a b c : V} (h : s.M.SameComponent a b) (h' : s.M.SameComponent b c) :
    s.M.SameComponent a c := Relation.EqvGen.trans _ _ _ h h'

theorem pclosed_sc (r : V) : PClosed s.M (fun a => s.M.SameComponent a r) := by
  intro x hx
  have : s.M.SameComponent (s.M.atom (s.M.mate x)) (s.M.atom x) :=
    Relation.EqvGen.rel _ _ ⟨s.M.mate x, rfl, by rw [s.M.mate_mate]⟩
  exact sc_trans this hx

/-- Each component containing an atom with nonzero defect has total defect at least `2`. -/
theorem Good.class_sum_ge (hg : Good R s) {r : V} (hr : r ∈ s.M.atoms) (h0 : contrib s r ≠ 0) :
    2 ≤ ∑ b ∈ s.M.atoms.filter (fun b => s.M.SameComponent b r), contrib s b := by
  set F := s.M.atoms.filter (fun b => s.M.SameComponent b r) with hF
  have hge : contrib s r ≤ ∑ b ∈ F, contrib s b :=
    Finset.single_le_sum (f := contrib s) (fun b hb => hg.contrib_nonneg (Finset.mem_filter.1 hb).1)
      (Finset.mem_filter.2 ⟨hr, sc_refl r⟩)
  have hpos := hg.contrib_nonneg hr
  have h1 : 2 ∣ ∑ b ∈ F, (s.cls b).base := by
    refine Finset.dvd_sum fun b _ => ?_
    rcases hc : s.cls b <;> simp [Cls.base]
  have h2 : 2 ∣ ∑ b ∈ F, ((s.M.deg b : ℕ) : ℤ) := by
    have := even_sum_deg_closed (s := s) _ (pclosed_sc r)
    obtain ⟨k, hk⟩ := this
    refine ⟨k, ?_⟩
    have : ((∑ b ∈ F, s.M.deg b : ℕ) : ℤ) = (k + k : ℕ) := by rw [hk]
    push_cast at this; linarith
  have h3 : ∑ b ∈ F, contrib s b = ∑ b ∈ F, (s.cls b).base - ∑ b ∈ F, ((s.M.deg b : ℕ) : ℤ) := by
    unfold contrib; rw [Finset.sum_sub_distrib]
  have h4 : 2 ∣ ∑ b ∈ F, contrib s b := by rw [h3]; exact dvd_sub h1 h2
  obtain ⟨k, hk⟩ := h4
  omega

/-- **At most `R` imperfect components** (TARGET Prop `finalmol` L2184--L2190; DH23: exactly one for `R = 1`). -/
theorem Good.imperfect_le (hg : Good R s) :
    ∃ reps : Finset V, reps ⊆ s.M.atoms ∧ reps.card ≤ R ∧ ∀ a ∈ s.M.atoms,
      (∃ b ∈ s.M.atoms, s.M.SameComponent a b ∧ contrib s b ≠ 0) → ∃ r ∈ reps, s.M.SameComponent a r := by
  set A := s.M.atoms.filter (fun a => contrib s a ≠ 0) with hA
  set Fam := A.powerset.filter (fun S : Finset V => ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ¬ s.M.SameComponent a b) with hFam
  obtain ⟨reps, hreps, hmax⟩ := Fam.exists_max_image Finset.card
    ⟨∅, by simp [hFam]⟩
  obtain ⟨hsub, hnc⟩ := Finset.mem_filter.1 hreps
  have hsubA : reps ⊆ A := Finset.mem_powerset.1 hsub
  have hcover : ∀ a ∈ A, ∃ r ∈ reps, s.M.SameComponent a r := by
    intro a ha
    by_contra hcon
    push Not at hcon
    have haN : a ∉ reps := fun h => hcon a h (sc_refl a)
    have hmem : insert a reps ∈ Fam := by
      refine Finset.mem_filter.2 ⟨Finset.mem_powerset.2 (Finset.insert_subset ha hsubA), ?_⟩
      intro x hx y hy hxy
      rw [Finset.mem_insert] at hx hy
      rcases hx with rfl | hx <;> rcases hy with rfl | hy
      · exact absurd rfl hxy
      · exact fun h => hcon y hy h
      · exact fun h => hcon x hx (sc_symm h)
      · exact hnc x hx y hy hxy
    have := hmax _ hmem
    rw [Finset.card_insert_of_notMem haN] at this
    omega
  refine ⟨reps, fun r hr => (Finset.mem_filter.1 (hsubA hr)).1, ?_, ?_⟩
  · -- counting
    have hdisj : ∀ r ∈ reps, ∀ r' ∈ reps, r ≠ r' →
        Disjoint (s.M.atoms.filter (fun b => s.M.SameComponent b r))
          (s.M.atoms.filter (fun b => s.M.SameComponent b r')) := by
      intro r hr r' hr' hne
      rw [Finset.disjoint_left]
      intro b hb hb'
      have h1 := (Finset.mem_filter.1 hb).2
      have h2 := (Finset.mem_filter.1 hb').2
      exact hnc r hr r' hr' hne (sc_trans (sc_symm h1) h2)
    have hsum : ∑ r ∈ reps, ∑ b ∈ s.M.atoms.filter (fun b => s.M.SameComponent b r), contrib s b ≤ 2 * R := by
      rw [← Finset.sum_biUnion (fun r hr r' hr' hne => hdisj r hr r' hr' hne), ← hg.sum_contrib]
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun a ha _ => hg.contrib_nonneg ha)
      intro b hb
      obtain ⟨r, _, hr⟩ := Finset.mem_biUnion.1 hb
      exact (Finset.mem_filter.1 hr).1
    have hlow : ∑ r ∈ reps, (2 : ℤ) ≤ ∑ r ∈ reps, ∑ b ∈ s.M.atoms.filter (fun b => s.M.SameComponent b r), contrib s b := by
      refine Finset.sum_le_sum fun r hr => ?_
      have hrA := Finset.mem_filter.1 (hsubA hr)
      exact hg.class_sum_ge hrA.1 hrA.2
    simp only [Finset.sum_const, nsmul_eq_mul] at hlow
    have : (reps.card : ℤ) * 2 ≤ 2 * R := le_trans (by simpa using hlow) hsum
    omega
  · rintro a ha ⟨b, hb, hab, hbn⟩
    obtain ⟨r, hr, hbr⟩ := hcover b (Finset.mem_filter.2 ⟨hb, hbn⟩)
    exact ⟨r, hr, sc_trans hab hbr⟩

end

end WaveTurbulence.FinalCountG3

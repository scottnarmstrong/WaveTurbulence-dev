/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPin.Chain
import Mathlib.Tactic

/-! # C4a PIN-FOURIER: the paired rungs with pins inside ladders

For a set of candidate rungs `JS S` per maximal ladder (main's `CD.JS`: the unselected interior rungs of a small
ladder), the `X` rungs are those whose two atoms are both integration clocks (`rungFree`). o73 Prop 18.1 removes the
others ("force every such rung's formerly chosen larger-time vertex out of X"). The retained rungs of a ladder are
grouped into *segments* (`segN`), cut at the rungs that contain a bad pin. Inside a segment the rung maxima form a
valley on the whole contracted domain (`hval_seg`, from `rung_valley`). The ladder engine's group index is
`SegQ π0 = Σ S, Fin (m S + 1)`. -/

@[expose] public section
set_option autoImplicit false

namespace WaveTurbulence.Flower.FinalMKPin
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Ladder WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LadderDisjoint
open MeasureTheory Set Finset
open scoped Classical ENNReal

variable {w : ℕ} {G : Garden w}

/-- The rung `j` of ladder `S` contains a bad pin. -/
def badR (fix : GBranch G.tree → Option ℝ) (π0 : PF G) (S : LQ G) (j : ℕ) : Prop :=
  BadPin fix (rowN (π0.u S) j) ∨ BadPin fix (rowN (π0.v S) j)

/-- The segment index of rung `j`: the number of bad rungs before it. -/
noncomputable def segN (fix : GBranch G.tree → Option ℝ) (π0 : PF G) (S : LQ G) (j : ℕ) : ℕ :=
  ((Finset.range j).filter (badR fix π0 S)).card

/-- Both atoms of rung `j` are integration clocks. -/
def rungFree (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree)) (π0 : PF G)
    (S : LQ G) (j : ℕ) : Prop :=
  (fix (rowN (π0.u S) j) = none ∧ face (rowN (π0.u S) j) = none) ∧
    (fix (rowN (π0.v S) j) = none ∧ face (rowN (π0.v S) j) = none)

/-- The group index of the ladder engine: a ladder and a segment. -/
abbrev SegQ (π0 : PF G) : Type := Σ S : LQ G, Fin (π0.m S + 1)

/-- The `X` rungs of a segment. -/
noncomputable def JSk (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (π0 : PF G) (JS : LQ G → Finset ℕ) (q : SegQ π0) : Finset ℕ :=
  (JS q.1).filter fun j => rungFree fix face π0 q.1 j ∧ segN fix π0 q.1 j = q.2.val

noncomputable def Kq (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (π0 : PF G) (JS : LQ G → Finset ℕ) (q : SegQ π0) : ℕ := (JSk fix face π0 JS q).card

noncomputable def enumq (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (π0 : PF G) (JS : LQ G → Finset ℕ) (q : SegQ π0) : Fin (Kq fix face π0 JS q) → ℕ :=
  fun i => (JSk fix face π0 JS q).orderEmbOfFin rfl i

variable {fix : GBranch G.tree → Option ℝ} {face : GBranch G.tree → Option (GBranch G.tree)} {π0 : PF G}
  {JS : LQ G → Finset ℕ}

theorem enumq_mem (q : SegQ π0) (i : Fin (Kq fix face π0 JS q)) : enumq fix face π0 JS q i ∈ JSk fix face π0 JS q :=
  Finset.orderEmbOfFin_mem _ _ _

theorem enumq_strictMono (q : SegQ π0) : StrictMono (enumq fix face π0 JS q) :=
  ((JSk fix face π0 JS q).orderEmbOfFin rfl).strictMono

theorem enumq_spec (q : SegQ π0) (i : Fin (Kq fix face π0 JS q)) :
    enumq fix face π0 JS q i ∈ JS q.1 ∧ rungFree fix face π0 q.1 (enumq fix face π0 JS q i) ∧
      segN fix π0 q.1 (enumq fix face π0 JS q i) = q.2.val := by
  have h := enumq_mem q i
  unfold JSk at h
  rw [Finset.mem_filter] at h
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- The upper atom of a paired rung. -/
noncomputable def uaI (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (π0 : PF G) (JS : LQ G → Finset ℕ) (s : Jr (Kq fix face π0 JS)) : Iv fix face :=
  ⟨rowN (π0.u s.1.1) (enumq fix face π0 JS s.1 s.2), (enumq_spec s.1 s.2).2.1.1⟩

/-- The lower atom of a paired rung. -/
noncomputable def vaI (fix : GBranch G.tree → Option ℝ) (face : GBranch G.tree → Option (GBranch G.tree))
    (π0 : PF G) (JS : LQ G → Finset ℕ) (s : Jr (Kq fix face π0 JS)) : Iv fix face :=
  ⟨rowN (π0.v s.1.1) (enumq fix face π0 JS s.1 s.2), (enumq_spec s.1 s.2).2.1.2⟩

theorem uaI_val (s : Jr (Kq fix face π0 JS)) :
    (uaI fix face π0 JS s).1 = atomAt π0 s.1.1 true (enumq fix face π0 JS s.1 s.2) := by
  simp [uaI, atomAt]

theorem vaI_val (s : Jr (Kq fix face π0 JS)) :
    (vaI fix face π0 JS s).1 = atomAt π0 s.1.1 false (enumq fix face π0 JS s.1 s.2) := by
  simp [vaI, atomAt]

section bounds
variable (hJS : ∀ S j, j ∈ JS S → 1 ≤ j ∧ j < π0.m S)
include hJS

theorem enumq_le (q : SegQ π0) (i : Fin (Kq fix face π0 JS q)) : enumq fix face π0 JS q i ≤ π0.m q.1 :=
  (hJS _ _ (enumq_spec q i).1).2.le

theorem atomAt_enumq_inj (s s' : Jr (Kq fix face π0 JS)) (b b' : Bool)
    (h : atomAt π0 s.1.1 b (enumq fix face π0 JS s.1 s.2) = atomAt π0 s'.1.1 b' (enumq fix face π0 JS s'.1 s'.2)) :
    s = s' ∧ b = b' := by
  obtain ⟨⟨S, k⟩, i⟩ := s
  obtain ⟨⟨S', k'⟩, i'⟩ := s'
  obtain ⟨h1, h2, h3⟩ := atomAt_inj π0 S S' b b' (enumq_le hJS _ i) (enumq_le hJS _ i') h
  subst h1
  have hk : k = k' := by
    apply Fin.ext
    rw [← (enumq_spec (JS := JS) (face := face) ⟨S, k⟩ i).2.2, ← (enumq_spec (JS := JS) (face := face) ⟨S, k'⟩ i').2.2]
    exact congrArg _ h3
  subst hk
  refine ⟨?_, h2⟩
  rw [(enumq_strictMono ⟨S, k⟩).injective h3]

theorem elim_injective_I : Function.Injective (Sum.elim (uaI fix face π0 JS) (vaI fix face π0 JS)) := by
  rintro (s | s) (s' | s') h
  · have := atomAt_enumq_inj hJS s s' true true (by
      have := congrArg Subtype.val h; simpa [uaI_val] using this)
    rw [this.1]
  · have := atomAt_enumq_inj hJS s s' true false (by
      have := congrArg Subtype.val h; simpa [uaI_val, vaI_val] using this)
    simp at this
  · have := atomAt_enumq_inj hJS s s' false true (by
      have := congrArg Subtype.val h; simpa [uaI_val, vaI_val] using this)
    simp at this
  · have := atomAt_enumq_inj hJS s s' false false (by
      have := congrArg Subtype.val h; simpa [vaI_val] using this)
    rw [this.1]

end bounds

/-- Equal segment indices: no bad rung in between. -/
theorem segN_eq_noBad (S : LQ G) {i l : ℕ} (_hil : i ≤ l) (h : segN fix π0 S i = segN fix π0 S l) :
    ∀ k, i ≤ k → k < l → ¬ badR fix π0 S k := by
  intro k hik hkl hk
  have hsub : (Finset.range i).filter (badR fix π0 S) ⊂ (Finset.range l).filter (badR fix π0 S) := by
    refine Finset.ssubset_iff_of_subset (fun x hx => ?_) |>.mpr ⟨k, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢; exact ⟨by omega, hx.2⟩
    · simp only [Finset.mem_filter, Finset.mem_range]; exact ⟨hkl, hk⟩
    · simp only [Finset.mem_filter, Finset.mem_range]; omega
  have := Finset.card_lt_card hsub
  unfold segN at h
  omega

/-- **The valley property of each segment on the contracted domain.** -/
theorem hval_seg (hF : FaceOK fix face) (hJS : ∀ S j, j ∈ JS S → 1 ≤ j ∧ j < π0.m S)
    {layer : GBranch G.tree → ℕ} {rootTime : Fin w → ℝ} (τ : Iv fix face → ℝ)
    (hτ : τ ∈ Om0 (chF fix face) (lsF layer fix face) (capF layer rootTime fix face)) (q : SegQ π0) :
    NP (fun j : Fin (Kq fix face π0 JS q) =>
      max (τ (uaI fix face π0 JS ⟨q, j⟩)) (τ (vaI fix face π0 JS ⟨q, j⟩))) := by
  intro i j l hij hjl
  set e := enumq fix face π0 JS q
  have he : StrictMono e := enumq_strictMono q
  have hu : ∀ x, τ (uaI fix face π0 JS ⟨q, x⟩) = extendFixFace G fix face τ (rowN (π0.u q.1) (e x)) := fun x =>
    (extendFixFace_free τ _).symm
  have hv : ∀ x, τ (vaI fix face π0 JS ⟨q, x⟩) = extendFixFace G fix face τ (rowN (π0.v q.1) (e x)) := fun x =>
    (extendFixFace_free τ _).symm
  simp only [hu, hv]
  have hil : e i ≤ e l := (he (hij.trans hjl)).le
  have hseg : segN fix π0 q.1 (e i) = segN fix π0 q.1 (e l) := by
    rw [(enumq_spec q i).2.2, (enumq_spec q l).2.2]
  refine rung_valley (π0.ladder q.1) (extendFixFace G fix face τ) (fun a => ¬ BadPin fix a)
    (fun a p hg hch => mono_on_Om0 hF hτ hch hg) (he hij) (he hjl) (hJS _ _ (enumq_spec q l).1).2.le ?_
  intro k hik hkl
  have := segN_eq_noBad q.1 hil hseg k hik.le hkl
  unfold badR at this
  push_neg at this
  exact this

end WaveTurbulence.Flower.FinalMKPin

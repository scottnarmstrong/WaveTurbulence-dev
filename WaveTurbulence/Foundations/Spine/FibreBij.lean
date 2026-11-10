/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainMol
public import WaveTurbulence.Foundations.Spine.ChainDec
/-! # Changing the interior chain of a dart labelling (S3b LADDER-DECAY)

The glued chain labellings of two chains with the same end rails agree on all darts at atoms
that are not interior atoms of the ladder; their difference has zero signed sums at interior atoms. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {M : Molecule V D} {n : ℕ}
  {u v : Fin (n + 1 + 1) → V}

/-- The atoms of the interior rungs. -/
def intAtoms (u v : Fin (n + 1 + 1) → V) : Finset V :=
  (univ.image fun i : Fin n => u (LadderDarts.ir i)) ∪ (univ.image fun i : Fin n => v (LadderDarts.ir i))

namespace LadderDarts.Ctx
variable (C : LadderDarts.Ctx M u v)

include C in
lemma u_mem_intAtoms (j : Fin (n + 1 + 1)) :
    u j ∈ intAtoms u v ↔ j ≠ 0 ∧ j ≠ Fin.last (n + 1) := by
  unfold intAtoms
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · have := C.huinj hi
      subst this
      simp only [LadderDarts.ir, ne_eq, Fin.ext_iff]
      simp only [Fin.val_zero, Fin.val_last]
      omega
    · exact absurd hi.symm (C.hne _ _)
  · rintro ⟨h0, h1⟩
    left
    have hj0 : j.1 ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
    have hj1 : j.1 ≠ n + 1 := fun h => h1 (Fin.ext (by simp [h]))
    have hjn := j.2
    refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
    congr 1
    ext
    simp only [LadderDarts.ir]
    omega

include C in
lemma v_mem_intAtoms (j : Fin (n + 1 + 1)) :
    v j ∈ intAtoms u v ↔ j ≠ 0 ∧ j ≠ Fin.last (n + 1) := by
  unfold intAtoms
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro (⟨i, hi⟩ | ⟨i, hi⟩)
    · exact absurd hi (C.hne _ _)
    · have := C.hvinj hi
      subst this
      simp only [LadderDarts.ir, ne_eq, Fin.ext_iff]
      simp only [Fin.val_zero, Fin.val_last]
      omega
  · rintro ⟨h0, h1⟩
    right
    have hj0 : j.1 ≠ 0 := fun h => h0 (Fin.ext (by simp [h]))
    have hj1 : j.1 ≠ n + 1 := fun h => h1 (Fin.ext (by simp [h]))
    have hjn := j.2
    refine ⟨⟨j.1 - 1, by omega⟩, ?_⟩
    congr 1
    ext
    simp only [LadderDarts.ir]
    omega


variable {E : Type*} [AddCommGroup E]

include C in
/-- Chains with the same end rails glue to the same labels on all darts at non-interior atoms. -/
lemma glueT_end_eq (L L' : ChainLab n E) (ha0 : L.a 0 = L'.a 0) (hb0 : L.b 0 = L'.b 0)
    (han : L.a (Fin.last n) = L'.a (Fin.last n)) (hbn : L.b (Fin.last n) = L'.b (Fin.last n))
    (x : D) (hx : M.atom x ∉ intAtoms u v) : C.glueT L x = C.glueT L' x := by
  by_cases hT : C.IsT x
  swap
  · rw [C.glueT_of_not L x hT, C.glueT_of_not L' x hT]
  obtain ⟨c, hc | hc⟩ := hT
  · subst hc
    have key := congrArg Prod.fst (C.key_dartOf c)
    simp only at key
    rw [C.glueT_dartOf, C.glueT_dartOf]
    rcases c with ⟨i, k⟩ | p | p
    · exfalso; apply hx; rw [key]
      exact (C.u_mem_intAtoms _).mpr ⟨by simp [LadderDarts.ir, Fin.ext_iff], by
        simp [LadderDarts.ir, Fin.ext_iff]; omega⟩
    · rw [key] at hx
      have : p = 0 := by
        by_contra hp
        apply hx
        refine (C.u_mem_intAtoms _).mpr ⟨?_, ?_⟩
        · intro h; apply hp; ext; have := congrArg Fin.val h; simpa using this
        · intro h; have := congrArg Fin.val h; simp at this; omega
      subst this; exact ha0
    · rw [key] at hx
      have : p = 0 := by
        by_contra hp
        apply hx
        refine (C.v_mem_intAtoms _).mpr ⟨?_, ?_⟩
        · intro h; apply hp; ext; have := congrArg Fin.val h; simpa using this
        · intro h; have := congrArg Fin.val h; simp at this; omega
      subst this; exact hb0
  · subst hc
    have key := congrArg Prod.snd (C.key_dartOf c)
    simp only at key
    rw [C.glueT_mate_dartOf, C.glueT_mate_dartOf]
    rcases c with ⟨i, k⟩ | p | p
    · exfalso; apply hx; rw [key]
      exact (C.v_mem_intAtoms _).mpr ⟨by simp [LadderDarts.ir, Fin.ext_iff], by
        simp [LadderDarts.ir, Fin.ext_iff]; omega⟩
    · rw [key] at hx
      have : p = Fin.last n := by
        by_contra hp
        apply hx
        refine (C.u_mem_intAtoms _).mpr ⟨?_, ?_⟩
        · intro h; have := congrArg Fin.val h; simp at this
        · intro h; apply hp; ext; have := congrArg Fin.val h; simp at this; simpa using this
      subst this; exact han
    · rw [key] at hx
      have : p = Fin.last n := by
        by_contra hp
        apply hx
        refine (C.v_mem_intAtoms _).mpr ⟨?_, ?_⟩
        · intro h; have := congrArg Fin.val h; simp at this
        · intro h; apply hp; ext; have := congrArg Fin.val h; simp at this; simpa using this
      subst this; exact hbn


lemma inv_a_last (S : ChainSigns n) (a0 b0 : E) (P : Fin n → E × E) :
    (S.inv a0 b0 P).a (Fin.last n) = a0 + ∑ k, (S.tau P k 2 - S.tau P k 3) := by
  simp [ChainSigns.inv, ChainSigns.railU]

lemma inv_b_last (S : ChainSigns n) (a0 b0 : E) (P : Fin n → E × E) :
    (S.inv a0 b0 P).b (Fin.last n) =
      (S.inv a0 b0 P).a (Fin.last n) - S.epsF (Fin.last n) • (a0 - b0) := rfl

include C in
/-- A chain with the same flux has the same end rails. -/
lemma end_rails (κ : D → E) (hsol : C.signs.IsSol (C.chainOf κ)) (P : Fin n → E × E)
    (hP : ∑ k, (C.signs.tau P k 2 - C.signs.tau P k 3) =
      ∑ k, (C.signs.tau (C.signs.pairs (C.chainOf κ)) k 2 - C.signs.tau (C.signs.pairs (C.chainOf κ)) k 3)) :
    (C.signs.inv ((C.chainOf κ).a 0) ((C.chainOf κ).b 0) P).a 0 = (C.chainOf κ).a 0 ∧
    (C.signs.inv ((C.chainOf κ).a 0) ((C.chainOf κ).b 0) P).b 0 = (C.chainOf κ).b 0 ∧
    (C.signs.inv ((C.chainOf κ).a 0) ((C.chainOf κ).b 0) P).a (Fin.last n) = (C.chainOf κ).a (Fin.last n) ∧
    (C.signs.inv ((C.chainOf κ).a 0) ((C.chainOf κ).b 0) P).b (Fin.last n) = (C.chainOf κ).b (Fin.last n) := by
  have hinv := C.signs.inv_pairs (C.chainOf κ) hsol
  have hAl : (C.signs.inv ((C.chainOf κ).a 0) ((C.chainOf κ).b 0) (C.signs.pairs (C.chainOf κ))).a (Fin.last n)
      = (C.chainOf κ).a (Fin.last n) := by rw [hinv]
  have hBl : (C.signs.inv ((C.chainOf κ).a 0) ((C.chainOf κ).b 0) (C.signs.pairs (C.chainOf κ))).b (Fin.last n)
      = (C.chainOf κ).b (Fin.last n) := by rw [hinv]
  have hA : (C.chainOf κ).a (Fin.last n) = (C.chainOf κ).a 0 + ∑ k, (C.signs.tau (C.signs.pairs (C.chainOf κ)) k 2 - C.signs.tau (C.signs.pairs (C.chainOf κ)) k 3) := by
    rw [← hAl]; exact inv_a_last _ _ _ _
  have hB : (C.chainOf κ).b (Fin.last n) = (C.chainOf κ).a (Fin.last n) - C.signs.epsF (Fin.last n) • ((C.chainOf κ).a 0 - (C.chainOf κ).b 0) := by
    rw [← hBl, inv_b_last, hAl]
  refine ⟨by simp [ChainSigns.inv, ChainSigns.railU], ?_, ?_, ?_⟩
  · simp [ChainSigns.inv, ChainSigns.railU, ChainSigns.epsF]
  · rw [inv_a_last, hP, hA]
  · rw [inv_b_last, inv_a_last, hP, hB, hA]


open scoped Classical in
/-- Replace the interior chain of an `Xint` labelling. -/
noncomputable def swapChain (κ : Xint C E) (L' : {L : ChainLab n E // C.signs.IsSol L}) : Xint C E :=
  C.xintEquiv.symm ((C.xintEquiv κ).1, L')

lemma chain_swapChain (κ : Xint C E) (L' : {L : ChainLab n E // C.signs.IsSol L}) :
    (C.xintEquiv (C.swapChain κ L')).2 = L' := by
  unfold swapChain
  rw [Equiv.apply_symm_apply]

include C in
lemma swapChain_end (κ : Xint C E) (L' : {L : ChainLab n E // C.signs.IsSol L})
    (h1 : L'.1.a 0 = (C.xintEquiv κ).2.1.a 0) (h2 : L'.1.b 0 = (C.xintEquiv κ).2.1.b 0)
    (h3 : L'.1.a (Fin.last n) = (C.xintEquiv κ).2.1.a (Fin.last n))
    (h4 : L'.1.b (Fin.last n) = (C.xintEquiv κ).2.1.b (Fin.last n))
    (x : D) (hx : M.atom x ∉ intAtoms u v) : (C.swapChain κ L').1 x = κ.1 x := by
  have e1 : κ.1 x = (C.xintEquiv.symm (C.xintEquiv κ)).1 x := by rw [Equiv.symm_apply_apply]
  rw [e1]
  have e2 : ∀ L'' : {L : ChainLab n E // C.signs.IsSol L},
      (C.xintEquiv.symm ((C.xintEquiv κ).1, L'')).1 x = (C.xintEquiv κ).1.1 x + C.glueT L''.1 x :=
    fun L'' => rfl
  have e3 : (C.xintEquiv.symm (C.xintEquiv κ)).1 x =
      (C.xintEquiv κ).1.1 x + C.glueT (C.xintEquiv κ).2.1 x := rfl
  unfold swapChain
  rw [e2, e3, C.glueT_end_eq L'.1 (C.xintEquiv κ).2.1 h1 h2 h3 h4 x hx]


include C in
lemma isT_inGroup (x : D) (hx : C.IsT x) : M.InGroup (Molecule.ladderAtoms u v) x := by
  have key : ∀ c : LadderDarts.Ctx.Code n, M.atom (C.dartOf c) ∈ Molecule.ladderAtoms u v ∧
      M.atom (M.mate (C.dartOf c)) ∈ Molecule.ladderAtoms u v := by
    intro c
    have k := C.key_dartOf c
    have h1 := congrArg Prod.fst k
    have h2 := congrArg Prod.snd k
    simp only at h1 h2
    unfold Molecule.ladderAtoms
    rcases c with ⟨i, k⟩ | p | p
    · rw [h1, h2]
      exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩
    · rw [h1, h2]
      exact ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩),
        Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩
    · rw [h1, h2]
      exact ⟨Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩),
        Finset.mem_union_right _ (Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩)⟩
  obtain ⟨c, hc | hc⟩ := hx
  · subst hc; exact key c
  · subst hc
    unfold Molecule.InGroup
    rw [M.mate_mate]
    exact ⟨(key c).2, (key c).1⟩

include C in
lemma isT_of_atom_interior (x : D) (hx : M.atom x ∈ intAtoms u v) : C.IsT x := by
  unfold intAtoms at hx
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at hx
  rcases hx with ⟨i, hi⟩ | ⟨i, hi⟩
  · have hmem : x ∈ M.dartsAt (u (LadderDarts.ir i)) := by
      rw [Molecule.dartsAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi.symm⟩
    rw [C.dartsAt_u i] at hmem
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hmem
    exact C.isT_uDart i k
  · have hmem : x ∈ M.dartsAt (v (LadderDarts.ir i)) := by
      rw [Molecule.dartsAt, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hi.symm⟩
    rw [C.dartsAt_v i] at hmem
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hmem
    exact C.isT_vDart i k


include C in
/-- Labellings agreeing off the interior atoms have the same end rails. -/
lemma agree_rails (κ κ' : D → E) (hκ : ∀ x, κ (M.mate x) = κ x) (hκ' : ∀ x, κ' (M.mate x) = κ' x)
    (hag : ∀ x, M.atom x ∉ intAtoms u v → κ x = κ' x) :
    (C.chainOf κ).a 0 = (C.chainOf κ').a 0 ∧ (C.chainOf κ).b 0 = (C.chainOf κ').b 0 ∧
    (C.chainOf κ).a (Fin.last n) = (C.chainOf κ').a (Fin.last n) ∧
    (C.chainOf κ).b (Fin.last n) = (C.chainOf κ').b (Fin.last n) := by
  have hu0 : u 0 ∉ intAtoms u v := fun h => ((C.u_mem_intAtoms 0).mp h).1 rfl
  have hv0 : v 0 ∉ intAtoms u v := fun h => ((C.v_mem_intAtoms 0).mp h).1 rfl
  have hul : u (Fin.last (n + 1)) ∉ intAtoms u v := fun h => ((C.u_mem_intAtoms _).mp h).2 rfl
  have hvl : v (Fin.last (n + 1)) ∉ intAtoms u v := fun h => ((C.v_mem_intAtoms _).mp h).2 rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show κ (C.LD.ra 0) = κ' (C.LD.ra 0)
    exact hag _ (by rw [C.LD.ra_atom]; exact hu0)
  · show κ (C.LD.rc 0) = κ' (C.LD.rc 0)
    exact hag _ (by rw [C.LD.rc_atom]; exact hv0)
  · show κ (C.LD.ra (Fin.last n)) = κ' (C.LD.ra (Fin.last n))
    rw [← hκ, ← hκ']
    exact hag _ (by rw [C.LD.ra_mate]; simpa using hul)
  · show κ (C.LD.rc (Fin.last n)) = κ' (C.LD.rc (Fin.last n))
    rw [← hκ, ← hκ']
    exact hag _ (by rw [C.LD.rc_mate]; simpa using hvl)

include C in
lemma inGroup_of_atom_interior (x : D) (hx : M.atom x ∈ intAtoms u v) :
    M.InGroup (Molecule.ladderAtoms u v) x :=
  C.isT_inGroup x (C.isT_of_atom_interior x hx)

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay

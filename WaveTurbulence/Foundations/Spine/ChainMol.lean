/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.ChainAlg
public import WaveTurbulence.Foundations.WaveB.Molecules
/-! # Dart extraction from a ladder (S3b LADDER-DECAY)

From `Molecule.IsLadder u v` we choose rung darts `ru`, and rail darts `ra`, `rc`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open Finset WaveTurbulence

variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] (M : Molecule V D)

/-- Darts at `a` whose mate is at `b`. -/
def dartsTo (a b : V) : Finset D :=
  univ.filter fun x => M.atom x = a ∧ M.atom (M.mate x) = b

variable {M}

lemma mem_dartsTo {a b : V} {x : D} : x ∈ dartsTo M a b ↔ M.atom x = a ∧ M.atom (M.mate x) = b := by
  simp [dartsTo]

variable (M)

omit [DecidableEq D] in
lemma mem_bondsFilter {a b : V} {y : D} :
    y ∈ M.bonds.filter (fun x => M.ends x = s(a, b)) ↔
      M.out y = true ∧ ((M.atom y = a ∧ M.atom (M.mate y) = b) ∨
        (M.atom y = b ∧ M.atom (M.mate y) = a)) := by
  simp only [Finset.mem_filter, Molecule.bonds, Finset.mem_univ, true_and, Molecule.ends,
    Sym2.eq_iff]

lemma card_dartsTo {a b : V} (hab : a ≠ b) : (dartsTo M a b).card = M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  refine Finset.card_bij (fun x _ => if M.out x = true then x else M.mate x) ?_ ?_ ?_
  · intro x hx
    rw [mem_dartsTo] at hx
    rw [mem_bondsFilter]
    by_cases ho : M.out x = true
    · rw [if_pos ho]; exact ⟨ho, Or.inl hx⟩
    · have hm : M.out (M.mate x) = true := by
        rw [M.out_mate]; simpa using ho
      rw [if_neg ho]
      refine ⟨hm, Or.inr ⟨hx.2, ?_⟩⟩
      rw [M.mate_mate]; exact hx.1
  · intro x hx y hy hxy
    rw [mem_dartsTo] at hx hy
    by_cases hox : M.out x = true <;> by_cases hoy : M.out y = true
    · rw [if_pos hox, if_pos hoy] at hxy; exact hxy
    · rw [if_pos hox, if_neg hoy] at hxy
      exfalso; apply hab
      have e1 : M.atom y = a := hy.1
      have e2 : M.atom (M.mate y) = b := hy.2
      rw [← hxy] at e2
      rw [← hx.1, ← e2]
    · rw [if_neg hox, if_pos hoy] at hxy
      exfalso; apply hab
      have e1 : M.atom x = a := hx.1
      have e2 : M.atom (M.mate x) = b := hx.2
      rw [hxy] at e2
      rw [← hy.1, ← e2]
    · rw [if_neg hox, if_neg hoy] at hxy
      rw [← M.mate_mate x, hxy, M.mate_mate]
  · intro y hy
    rw [mem_bondsFilter] at hy
    obtain ⟨hout, h1 | h1⟩ := hy
    · exact ⟨y, mem_dartsTo.mpr h1, by rw [if_pos hout]⟩
    · have hn : M.out (M.mate y) ≠ true := by rw [M.out_mate, hout]; simp
      refine ⟨M.mate y, mem_dartsTo.mpr ⟨h1.2, ?_⟩, ?_⟩
      · rw [M.mate_mate]; exact h1.1
      · rw [if_neg hn, M.mate_mate]


/-- Chosen rung and rail darts of a ladder with `n + 2` rungs (`m = n + 1`). -/
structure LadderDarts (M : Molecule V D) {n : ℕ} (u v : Fin (n + 1 + 1) → V) where
  ru : Fin (n + 1 + 1) → Fin 2 → D
  ra : Fin (n + 1) → D
  rc : Fin (n + 1) → D
  ru_atom : ∀ j k, M.atom (ru j k) = u j
  ru_mate : ∀ j k, M.atom (M.mate (ru j k)) = v j
  ru_ne : ∀ j, ru j 0 ≠ ru j 1
  ru_all : ∀ j x, M.atom x = u j → M.atom (M.mate x) = v j → x = ru j 0 ∨ x = ru j 1
  ra_atom : ∀ p, M.atom (ra p) = u p.castSucc
  ra_mate : ∀ p, M.atom (M.mate (ra p)) = u p.succ
  ra_all : ∀ p x, M.atom x = u p.castSucc → M.atom (M.mate x) = u p.succ → x = ra p
  rc_atom : ∀ p, M.atom (rc p) = v p.castSucc
  rc_mate : ∀ p, M.atom (M.mate (rc p)) = v p.succ
  rc_all : ∀ p x, M.atom x = v p.castSucc → M.atom (M.mate x) = v p.succ → x = rc p
  out_rel : ∀ p, M.out (ra p) = true ↔ M.out (M.mate (rc p)) = true

theorem exists_ladderDarts {n : ℕ} {u v : Fin (n + 1 + 1) → V} (h : M.IsLadder u v) :
    Nonempty (LadderDarts M u v) := by
  obtain ⟨-, hinj, -, hrung, hrail⟩ := h
  have hne : ∀ j j', u j ≠ v j' := fun j j' he => by
    have := hinj (a₁ := Sum.inl j) (a₂ := Sum.inr j') he
    cases this
  have huinj : Function.Injective u := fun i j he => Sum.inl.inj (hinj (a₁ := Sum.inl i) (a₂ := Sum.inl j) he)
  have hvinj : Function.Injective v := fun i j he => Sum.inr.inj (hinj (a₁ := Sum.inr i) (a₂ := Sum.inr j) he)
  -- rungs
  have h2 : ∀ j, ∃ x y : D, x ≠ y ∧ dartsTo M (u j) (v j) = {x, y} := fun j => by
    have := card_dartsTo M (hne j j)
    rw [hrung j] at this
    exact Finset.card_eq_two.mp this
  choose x y hxy hset using h2
  -- rails
  have hcast : ∀ p : Fin (n + 1), p.castSucc ≠ p.succ := fun p he => by
    have := congrArg Fin.val he; simp at this
  have h1u : ∀ p : Fin (n + 1), ∃ a : D, dartsTo M (u p.castSucc) (u p.succ) = {a} := fun p => by
    have := card_dartsTo M (a := u p.castSucc) (b := u p.succ) (fun he => hcast p (huinj he))
    rw [(hrail p).1] at this
    exact Finset.card_eq_one.mp this
  have h1v : ∀ p : Fin (n + 1), ∃ a : D, dartsTo M (v p.castSucc) (v p.succ) = {a} := fun p => by
    have := card_dartsTo M (a := v p.castSucc) (b := v p.succ) (fun he => hcast p (hvinj he))
    rw [(hrail p).2.1] at this
    exact Finset.card_eq_one.mp this
  choose ra hra using h1u
  choose rc hrc using h1v
  have memset : ∀ {a b : V} {s : Finset D} {z : D}, dartsTo M a b = s →
      (z ∈ s ↔ M.atom z = a ∧ M.atom (M.mate z) = b) :=
    fun hs => by rw [← hs, mem_dartsTo]
  have ruAtom : ∀ (j : Fin (n + 1 + 1)) (k : Fin 2), (if k = 0 then x j else y j) ∈ dartsTo M (u j) (v j) := by
    intro j k
    rw [hset j]
    by_cases hk : k = 0 <;> simp [hk]
  refine ⟨{ ru := fun j k => if k = 0 then x j else y j, ra := ra, rc := rc,
            ru_atom := fun j k => (mem_dartsTo.mp (ruAtom j k)).1,
            ru_mate := fun j k => (mem_dartsTo.mp (ruAtom j k)).2,
            ru_ne := fun j => by simpa using hxy j,
            ru_all := ?_, ra_atom := ?_, ra_mate := ?_, ra_all := ?_,
            rc_atom := ?_, rc_mate := ?_, rc_all := ?_, out_rel := ?_ }⟩
  · intro j z h1 h2
    have : z ∈ dartsTo M (u j) (v j) := mem_dartsTo.mpr ⟨h1, h2⟩
    rw [hset j] at this
    simpa using this
  · intro p
    have : ra p ∈ dartsTo M (u p.castSucc) (u p.succ) := by rw [hra p]; simp
    exact (mem_dartsTo.mp this).1
  · intro p
    have : ra p ∈ dartsTo M (u p.castSucc) (u p.succ) := by rw [hra p]; simp
    exact (mem_dartsTo.mp this).2
  · intro p z h1 h2
    have : z ∈ dartsTo M (u p.castSucc) (u p.succ) := mem_dartsTo.mpr ⟨h1, h2⟩
    rw [hra p] at this
    simpa using this
  · intro p
    have : rc p ∈ dartsTo M (v p.castSucc) (v p.succ) := by rw [hrc p]; simp
    exact (mem_dartsTo.mp this).1
  · intro p
    have : rc p ∈ dartsTo M (v p.castSucc) (v p.succ) := by rw [hrc p]; simp
    exact (mem_dartsTo.mp this).2
  · intro p z h1 h2
    have : z ∈ dartsTo M (v p.castSucc) (v p.succ) := mem_dartsTo.mpr ⟨h1, h2⟩
    rw [hrc p] at this
    simpa using this
  · intro p
    have hdir := (hrail p).2.2
    have ra1 : ra p ∈ dartsTo M (u p.castSucc) (u p.succ) := by rw [hra p]; simp
    have rc1 : rc p ∈ dartsTo M (v p.castSucc) (v p.succ) := by rw [hrc p]; simp
    have ra1' := mem_dartsTo.mp ra1
    have rc1' := mem_dartsTo.mp rc1
    have L : M.Directed (u p.castSucc) (u p.succ) ↔ M.out (ra p) = true := by
      constructor
      · rintro ⟨z, hz, h1, h2⟩
        have : z ∈ dartsTo M (u p.castSucc) (u p.succ) := mem_dartsTo.mpr ⟨h1, h2⟩
        rw [hra p] at this
        have hz' : z = ra p := by simpa using this
        rw [← hz']; exact hz
      · intro ho; exact ⟨ra p, ho, ra1'.1, ra1'.2⟩
    have R : M.Directed (v p.succ) (v p.castSucc) ↔ M.out (M.mate (rc p)) = true := by
      constructor
      · rintro ⟨z, hz, h1, h2⟩
        have : M.mate z ∈ dartsTo M (v p.castSucc) (v p.succ) :=
          mem_dartsTo.mpr ⟨h2, by rw [M.mate_mate]; exact h1⟩
        rw [hrc p] at this
        have hz' : M.mate z = rc p := by simpa using this
        have : z = M.mate (rc p) := by rw [← hz', M.mate_mate]
        rw [← this]; exact hz
      · intro ho
        exact ⟨M.mate (rc p), ho, rc1'.2, by rw [M.mate_mate]; exact rc1'.1⟩
    rw [← L, ← R]; exact hdir


namespace LadderDarts
variable {M} {n : ℕ} {u v : Fin (n + 1 + 1) → V} (LD : LadderDarts M u v)

/-- Molecule rung index of the interior rung `i`. -/
def ir (i : Fin n) : Fin (n + 1 + 1) := ⟨i.1 + 1, by omega⟩

/-- The four darts at the u-atom of interior rung `i`: rung, rung, toward lower, toward upper. -/
def uDart (i : Fin n) : Fin 4 → D :=
  ![LD.ru (ir i) 0, LD.ru (ir i) 1, M.mate (LD.ra i.castSucc), LD.ra i.succ]

/-- The four darts at the v-atom of interior rung `i`. -/
def vDart (i : Fin n) : Fin 4 → D :=
  ![M.mate (LD.ru (ir i) 0), M.mate (LD.ru (ir i) 1), M.mate (LD.rc i.castSucc), LD.rc i.succ]

lemma castSucc_succ_eq_ir (i : Fin n) : (i.castSucc).succ = ir i := by
  ext; simp [ir]

lemma succ_castSucc_eq_ir (i : Fin n) : (i.succ).castSucc = ir i := by
  ext; simp [ir]

lemma atom_uDart (i : Fin n) (k : Fin 4) : M.atom (LD.uDart i k) = u (ir i) := by
  fin_cases k
  · exact LD.ru_atom _ _
  · exact LD.ru_atom _ _
  · show M.atom (M.mate (LD.ra i.castSucc)) = _
    rw [LD.ra_mate, castSucc_succ_eq_ir]
  · show M.atom (LD.ra i.succ) = _
    rw [LD.ra_atom, succ_castSucc_eq_ir]

lemma atom_vDart (i : Fin n) (k : Fin 4) : M.atom (LD.vDart i k) = v (ir i) := by
  fin_cases k
  · exact LD.ru_mate _ _
  · exact LD.ru_mate _ _
  · show M.atom (M.mate (LD.rc i.castSucc)) = _
    rw [LD.rc_mate, castSucc_succ_eq_ir]
  · show M.atom (LD.rc i.succ) = _
    rw [LD.rc_atom, succ_castSucc_eq_ir]


lemma sa_uDart (i : Fin n) :
    ∀ k, M.atom (M.mate (LD.uDart i k)) =
      ![v (ir i), v (ir i), u i.castSucc.castSucc, u i.succ.succ] k := by
  intro k
  fin_cases k
  · exact LD.ru_mate _ _
  · exact LD.ru_mate _ _
  · show M.atom (M.mate (M.mate (LD.ra i.castSucc))) = _
    rw [M.mate_mate, LD.ra_atom]; rfl
  · show M.atom (M.mate (LD.ra i.succ)) = _
    rw [LD.ra_mate]; rfl

lemma sa_vDart (i : Fin n) :
    ∀ k, M.atom (M.mate (LD.vDart i k)) =
      ![u (ir i), u (ir i), v i.castSucc.castSucc, v i.succ.succ] k := by
  intro k
  fin_cases k
  · show M.atom (M.mate (M.mate (LD.ru (ir i) 0))) = _
    rw [M.mate_mate]; exact LD.ru_atom _ _
  · show M.atom (M.mate (M.mate (LD.ru (ir i) 1))) = _
    rw [M.mate_mate]; exact LD.ru_atom _ _
  · show M.atom (M.mate (M.mate (LD.rc i.castSucc))) = _
    rw [M.mate_mate, LD.rc_atom]; rfl
  · show M.atom (M.mate (LD.rc i.succ)) = _
    rw [LD.rc_mate]; rfl

lemma uDart_injective (hinj : Function.Injective (Sum.elim u v)) (i : Fin n) :
    Function.Injective (LD.uDart i) := by
  have hne : ∀ j j', u j ≠ v j' := fun j j' he => by
    have := hinj (a₁ := Sum.inl j) (a₂ := Sum.inr j') he
    cases this
  have huinj : Function.Injective u := fun a b he => Sum.inl.inj (hinj (a₁ := Sum.inl a) (a₂ := Sum.inl b) he)
  have h23 : u i.castSucc.castSucc ≠ u i.succ.succ := fun he => by
    have := congrArg Fin.val (huinj he); simp at this; omega
  intro k k' h
  have hs := congrArg (fun x => M.atom (M.mate x)) h
  simp only [sa_uDart] at hs
  fin_cases k <;> fin_cases k' <;> simp at hs ⊢
  all_goals first
    | exact absurd h (LD.ru_ne _)
    | exact absurd h.symm (LD.ru_ne _)
    | exact (hne _ _ hs.symm).elim
    | exact (hne _ _ hs).elim
    | exact h23 hs
    | exact h23 hs.symm
    | skip


lemma vDart_injective (hinj : Function.Injective (Sum.elim u v)) (i : Fin n) :
    Function.Injective (LD.vDart i) := by
  have hne : ∀ j j', u j ≠ v j' := fun j j' he => by
    have := hinj (a₁ := Sum.inl j) (a₂ := Sum.inr j') he
    cases this
  have hvinj : Function.Injective v := fun a b he => Sum.inr.inj (hinj (a₁ := Sum.inr a) (a₂ := Sum.inr b) he)
  have h23 : v i.castSucc.castSucc ≠ v i.succ.succ := fun he => by
    have := congrArg Fin.val (hvinj he); simp at this; omega
  intro k k' h
  have hs := congrArg (fun x => M.atom (M.mate x)) h
  simp only [sa_vDart] at hs
  have hr : ∀ k k', M.mate (LD.ru (ir i) k) = M.mate (LD.ru (ir i) k') → LD.ru (ir i) k = LD.ru (ir i) k' :=
    fun k k' he => by rw [← M.mate_mate (LD.ru (ir i) k), he, M.mate_mate]
  fin_cases k <;> fin_cases k' <;> simp at hs ⊢
  all_goals first
    | exact absurd (hr _ _ h) (LD.ru_ne _)
    | exact absurd (hr _ _ h.symm) (LD.ru_ne _)
    | exact (hne _ _ hs).elim
    | exact (hne _ _ hs.symm).elim
    | exact h23 hs
    | exact h23 hs.symm
    | skip


/-- Package of the facts about the ambient molecule used by the chart. -/
structure Ctx (M : Molecule V D) {n : ℕ} (u v : Fin (n + 1 + 1) → V) where
  LD : LadderDarts M u v
  hinj : Function.Injective (Sum.elim u v)
  hmol : M.IsMolecule
  hdeg : ∀ w, M.deg w ≤ 4
  hat_u : ∀ j, u j ∈ M.atoms
  hat_v : ∀ j, v j ∈ M.atoms

end LadderDarts

namespace LadderDarts.Ctx
open LadderDarts
variable {M} {n : ℕ} {u v : Fin (n + 1 + 1) → V} (C : LadderDarts.Ctx M u v)

lemma dartsAt_eq_image (a : V) (f : Fin 4 → D) (hf : Function.Injective f)
    (hat : ∀ k, M.atom (f k) = a) (hdeg : M.deg a ≤ 4) :
    M.dartsAt a = univ.image f := by
  symm
  apply Finset.eq_of_subset_of_card_le
  · intro x hx
    obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hx
    simp [Molecule.dartsAt, hat]
  · rw [Finset.card_image_of_injective _ hf]
    simpa [Molecule.deg] using hdeg

lemma dartsAt_u (i : Fin n) : M.dartsAt (u (ir i)) = univ.image (C.LD.uDart i) :=
  dartsAt_eq_image _ _ (C.LD.uDart_injective C.hinj i) (C.LD.atom_uDart i) (C.hdeg _)

lemma dartsAt_v (i : Fin n) : M.dartsAt (v (ir i)) = univ.image (C.LD.vDart i) :=
  dartsAt_eq_image _ _ (C.LD.vDart_injective C.hinj i) (C.LD.atom_vDart i) (C.hdeg _)

lemma sum_dartsAt_u {G : Type*} [AddCommMonoid G] (i : Fin n) (f : D → G) :
    ∑ x ∈ M.dartsAt (u (ir i)), f x = ∑ k, f (C.LD.uDart i k) := by
  rw [C.dartsAt_u i, Finset.sum_image (fun a _ b _ h => C.LD.uDart_injective C.hinj i h)]

lemma sum_dartsAt_v {G : Type*} [AddCommMonoid G] (i : Fin n) (f : D → G) :
    ∑ x ∈ M.dartsAt (v (ir i)), f x = ∑ k, f (C.LD.vDart i k) := by
  rw [C.dartsAt_v i, Finset.sum_image (fun a _ b _ h => C.LD.vDart_injective C.hinj i h)]

lemma out_count (C : LadderDarts.Ctx M u v) (a : V) (ha : a ∈ M.atoms) (f : Fin 4 → D) (hf : Function.Injective f)
    (hd : M.dartsAt a = univ.image f) :
    (univ.filter fun k => M.out (f k) = true).card = 2 := by
  have h1 := (C.hmol.1 a ha).1
  have h2 := (C.hmol.1 a ha).2
  unfold Molecule.outdeg at h1
  unfold Molecule.indeg at h2
  rw [hd, Finset.filter_image, Finset.card_image_of_injective _ hf] at h1 h2
  have h3 : (univ.filter fun k => M.out (f k) = true).card +
      (univ.filter fun k => ¬ M.out (f k) = true).card = 4 := by
    rw [Finset.card_filter_add_card_filter_not]; simp
  have h4 : (univ.filter fun k => ¬ M.out (f k) = true) =
      univ.filter fun k => M.out (f k) = false := by
    ext k; simp
  rw [h4] at h3
  have h1' : (univ.filter fun k => M.out (f k) = true).card ≤ 2 := h1
  have h2' : (univ.filter fun k => M.out (f k) = false).card ≤ 2 := h2
  omega


end LadderDarts.Ctx

/-- The integer sign `+1` for an outgoing dart, `-1` for an incoming one. -/
def sgn (M : Molecule V D) (x : D) : ℤ := if M.out x = true then 1 else -1

lemma sgn_mate (M : Molecule V D) (x : D) : sgn M (M.mate x) = - sgn M x := by
  unfold sgn
  rw [M.out_mate]
  cases h : M.out x <;> simp

lemma sgn_eq_one {M : Molecule V D} {x : D} (h : M.out x = true) : sgn M x = 1 := by
  simp [sgn, h]

lemma sgn_eq_neg_one {M : Molecule V D} {x : D} (h : M.out x = false) : sgn M x = -1 := by
  simp [sgn, h]

theorem perm_exists : ∀ f : Fin 4 → Bool, (univ.filter (fun k => f k = true)).card = 2 →
    ∃ σ : Equiv.Perm (Fin 4), f (σ 0) = true ∧ f (σ 1) = true ∧ f (σ 2) = false ∧ f (σ 3) = false := by
  decide

namespace LadderDarts.Ctx
variable {M} {n : ℕ} {u v : Fin (n + 1 + 1) → V} (C : LadderDarts.Ctx M u v)

lemma sgn_vDart (i : Fin n) (k : Fin 4) :
    sgn M (C.LD.vDart i k) = - sgn M (C.LD.uDart i k) := by
  fin_cases k
  · exact sgn_mate M _
  · exact sgn_mate M _
  · show sgn M (M.mate (C.LD.rc i.castSucc)) = - sgn M (M.mate (C.LD.ra i.castSucc))
    rw [sgn_mate M (C.LD.ra _)]
    have := C.LD.out_rel i.castSucc
    unfold sgn
    by_cases h : M.out (C.LD.ra i.castSucc) = true
    · simp [h, this.mp h]
    · have h' : ¬ M.out (M.mate (C.LD.rc i.castSucc)) = true := fun hh => h (this.mpr hh)
      simp [h, h']
  · show sgn M (C.LD.rc i.succ) = - sgn M (C.LD.ra i.succ)
    have := C.LD.out_rel i.succ
    have hm : sgn M (M.mate (C.LD.rc i.succ)) = - sgn M (C.LD.rc i.succ) := sgn_mate M _
    unfold sgn at hm ⊢
    by_cases h : M.out (C.LD.ra i.succ) = true
    · have h2 := this.mp h
      simp only [h, h2, if_true] at hm ⊢
      linarith
    · have h2 : ¬ M.out (M.mate (C.LD.rc i.succ)) = true := fun hh => h (this.mpr hh)
      simp only [h, h2, if_false] at hm ⊢
      linarith

/-- The sign data of the interior rungs of the ladder. -/
noncomputable def signs : ChainSigns n where
  sg i k := sgn M (C.LD.uDart i k)
  σ i := Classical.choose (perm_exists (fun k => decide (M.out (C.LD.uDart i k) = true))
    (by
      have := C.out_count _ (C.hat_u (LadderDarts.ir i)) _ (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)
      simpa using this))
  plus i := by
    have := (Classical.choose_spec (perm_exists (fun k => decide (M.out (C.LD.uDart i k) = true))
      (by
        have := C.out_count _ (C.hat_u (LadderDarts.ir i)) _ (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)
        simpa using this)))
    simp only [decide_eq_true_eq] at this
    exact ⟨sgn_eq_one this.1, sgn_eq_one this.2.1⟩
  minus i := by
    have := (Classical.choose_spec (perm_exists (fun k => decide (M.out (C.LD.uDart i k) = true))
      (by
        have := C.out_count _ (C.hat_u (LadderDarts.ir i)) _ (C.LD.uDart_injective C.hinj i) (C.dartsAt_u i)
        simpa using this)))
    simp only [decide_eq_false_iff_not, Bool.not_eq_true] at this
    exact ⟨sgn_eq_neg_one this.2.2.1, sgn_eq_neg_one this.2.2.2⟩
  link i j hij := by
    have hc : j.castSucc = i.succ := by ext; simp; omega
    show sgn M (M.mate (C.LD.ra j.castSucc)) = - sgn M (C.LD.ra i.succ)
    rw [sgn_mate M, hc]


variable {E : Type*} [AddCommGroup E]

/-- Interior chain labels read off from a dart labelling. -/
def chainOf (κ : D → E) : ChainLab n E where
  r i k := κ (C.LD.ru (LadderDarts.ir i) k)
  a p := κ (C.LD.ra p)
  b p := κ (C.LD.rc p)

lemma uSlot_chainOf (κ : D → E) (hκ : ∀ x, κ (M.mate x) = κ x) (i : Fin n) (k : Fin 4) :
    (C.chainOf κ).uSlot i k = κ (C.LD.uDart i k) := by
  fin_cases k
  · rfl
  · rfl
  · show κ (C.LD.ra i.castSucc) = κ (M.mate (C.LD.ra i.castSucc)); rw [hκ]
  · rfl

lemma vSlot_chainOf (κ : D → E) (hκ : ∀ x, κ (M.mate x) = κ x) (i : Fin n) (k : Fin 4) :
    (C.chainOf κ).vSlot i k = κ (C.LD.vDart i k) := by
  fin_cases k
  · show κ (C.LD.ru (LadderDarts.ir i) 0) = κ (M.mate (C.LD.ru (LadderDarts.ir i) 0)); rw [hκ]
  · show κ (C.LD.ru (LadderDarts.ir i) 1) = κ (M.mate (C.LD.ru (LadderDarts.ir i) 1)); rw [hκ]
  · show κ (C.LD.rc i.castSucc) = κ (M.mate (C.LD.rc i.castSucc)); rw [hκ]
  · rfl

lemma isSol_chainOf (κ : D → E) (hκ : ∀ x, κ (M.mate x) = κ x)
    (hu : ∀ i, ∑ k, sgn M (C.LD.uDart i k) • κ (C.LD.uDart i k) = 0)
    (hv : ∀ i, ∑ k, sgn M (C.LD.vDart i k) • κ (C.LD.vDart i k) = 0) :
    C.signs.IsSol (C.chainOf κ) := by
  intro i
  refine ⟨?_, ?_⟩
  · simp only [signs, uSlot_chainOf C κ hκ]
    exact hu i
  · have := hv i
    simp only [sgn_vDart C, neg_smul, Finset.sum_neg_distrib, neg_eq_zero] at this
    simp only [signs, vSlot_chainOf C κ hκ]
    exact this


/-- Codes of the interior bonds: rung bonds `(i,k)`, u-rails `p`, v-rails `p`. -/
abbrev Code (n : ℕ) := (Fin n × Fin 2) ⊕ Fin (n + 1) ⊕ Fin (n + 1)

/-- The canonical dart of an interior bond (at its lower atom). -/
def dartOf : Code n → D
  | .inl (i, k) => C.LD.ru (LadderDarts.ir i) k
  | .inr (.inl p) => C.LD.ra p
  | .inr (.inr p) => C.LD.rc p

/-- The value of a chain labelling at a code. -/
def labOf (L : ChainLab n E) : Code n → E
  | .inl (i, k) => L.r i k
  | .inr (.inl p) => L.a p
  | .inr (.inr p) => L.b p

/-- The dart `x` belongs to an interior bond. -/
def IsT (x : D) : Prop := ∃ c : Code n, C.dartOf c = x ∨ M.mate (C.dartOf c) = x

lemma key_dartOf (c : Code n) : (M.atom (C.dartOf c), M.atom (M.mate (C.dartOf c))) =
    match c with
    | .inl (i, _) => (u (LadderDarts.ir i), v (LadderDarts.ir i))
    | .inr (.inl p) => (u p.castSucc, u p.succ)
    | .inr (.inr p) => (v p.castSucc, v p.succ) := by
  rcases c with ⟨i, k⟩ | p | p
  · exact Prod.ext (C.LD.ru_atom _ _) (C.LD.ru_mate _ _)
  · exact Prod.ext (C.LD.ra_atom _) (C.LD.ra_mate _)
  · exact Prod.ext (C.LD.rc_atom _) (C.LD.rc_mate _)

include C in
lemma hne (j j' : Fin (n + 1 + 1)) : u j ≠ v j' := fun he => by
  have := C.hinj (a₁ := Sum.inl j) (a₂ := Sum.inr j') he
  cases this

include C in
lemma huinj : Function.Injective u := fun a b he =>
  Sum.inl.inj (C.hinj (a₁ := Sum.inl a) (a₂ := Sum.inl b) he)

include C in
lemma hvinj : Function.Injective v := fun a b he =>
  Sum.inr.inj (C.hinj (a₁ := Sum.inr a) (a₂ := Sum.inr b) he)

lemma dartOf_injective : Function.Injective (C.dartOf (M := M)) := by
  intro c c' h
  have hk := congrArg (fun x => (M.atom x, M.atom (M.mate x))) h
  simp only [key_dartOf] at hk
  rcases c with ⟨i, k⟩ | p | p <;> rcases c' with ⟨i', k'⟩ | p' | p' <;>
    simp only [Prod.mk.injEq] at hk
  · have hi : i = i' := by
      have := C.huinj hk.1
      apply Fin.ext
      have h2 := congrArg Fin.val this
      simp [LadderDarts.ir] at h2
      exact h2
    subst hi
    have : k = k' := by
      by_contra hkk
      apply C.LD.ru_ne (LadderDarts.ir i)
      fin_cases k <;> fin_cases k' <;> simp_all [dartOf]
    rw [this]
  · exact absurd hk.2.symm (C.hne _ _)
  · exact absurd hk.1 (C.hne _ _)
  · exact absurd hk.2 (C.hne _ _)
  · have := C.huinj hk.1
    exact congrArg (fun q => Sum.inr (Sum.inl q)) (Fin.castSucc_injective _ this)
  · exact absurd hk.1 (C.hne _ _)
  · exact absurd hk.1.symm (C.hne _ _)
  · exact absurd hk.1.symm (C.hne _ _)
  · have := C.hvinj hk.1
    exact congrArg (fun q => Sum.inr (Sum.inr q)) (Fin.castSucc_injective _ this)


lemma dartOf_ne_mate (c c' : Code n) : C.dartOf c ≠ M.mate (C.dartOf c') := by
  intro h
  have hk := congrArg (fun x => (M.atom x, M.atom (M.mate x))) h
  simp only [M.mate_mate] at hk
  have e1 := key_dartOf C c
  have e2 := key_dartOf C c'
  have hk1 : M.atom (C.dartOf c) = M.atom (M.mate (C.dartOf c')) := congrArg Prod.fst hk
  have hk2 : M.atom (M.mate (C.dartOf c)) = M.atom (C.dartOf c') := congrArg Prod.snd hk
  have a1 := congrArg Prod.fst e1
  have b1 := congrArg Prod.snd e1
  have a2 := congrArg Prod.fst e2
  have b2 := congrArg Prod.snd e2
  simp only at a1 b1 a2 b2
  rcases c with ⟨i, k⟩ | p | p <;> rcases c' with ⟨i', k'⟩ | p' | p' <;> simp only at a1 b1 a2 b2 <;>
    rw [a1, b2] at hk1 <;> rw [b1, a2] at hk2
  · exact C.hne _ _ hk1
  · exact C.hne _ _ hk2.symm
  · exact C.hne _ _ hk1
  · exact C.hne _ _ hk1
  · have h3 := congrArg Fin.val (C.huinj hk1)
    have h4 := congrArg Fin.val (C.huinj hk2)
    simp only [Fin.coe_castSucc, Fin.val_succ] at h3 h4
    omega
  · exact C.hne _ _ hk1
  · exact C.hne _ _ hk2.symm
  · exact C.hne _ _ hk2.symm
  · have h3 := congrArg Fin.val (C.hvinj hk1)
    have h4 := congrArg Fin.val (C.hvinj hk2)
    simp only [Fin.coe_castSucc, Fin.val_succ] at h3 h4
    omega


lemma labOf_chainOf (κ : D → E) (c : Code n) : labOf (C.chainOf κ) c = κ (C.dartOf c) := by
  rcases c with ⟨i, k⟩ | p | p <;> rfl

lemma isT_mate (x : D) : C.IsT (M.mate x) ↔ C.IsT x := by
  have mi : ∀ a b : D, M.mate a = M.mate b → a = b := fun a b h => by
    have := congrArg M.mate h; rwa [M.mate_mate, M.mate_mate] at this
  have one : ∀ y : D, C.IsT y → C.IsT (M.mate y) := by
    rintro y ⟨c, hc | hc⟩
    · exact ⟨c, Or.inr (by rw [hc])⟩
    · exact ⟨c, Or.inl (by rw [← hc, M.mate_mate])⟩
  exact ⟨fun h => by simpa [M.mate_mate] using one _ h, one x⟩

open scoped Classical in
/-- Extension of a chain labelling by zero off the interior bonds, constant on bonds. -/
noncomputable def glueT (L : ChainLab n E) (x : D) : E :=
  if h : C.IsT x then labOf L (Classical.choose h) else 0

lemma glueT_dartOf (L : ChainLab n E) (c : Code n) : C.glueT L (C.dartOf c) = labOf L c := by
  have h : C.IsT (C.dartOf c) := ⟨c, Or.inl rfl⟩
  unfold glueT
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  rcases hs with hs | hs
  · rw [C.dartOf_injective hs]
  · exact absurd hs.symm (C.dartOf_ne_mate _ _)

lemma glueT_mate_dartOf (L : ChainLab n E) (c : Code n) :
    C.glueT L (M.mate (C.dartOf c)) = labOf L c := by
  have h : C.IsT (M.mate (C.dartOf c)) := ⟨c, Or.inr rfl⟩
  unfold glueT
  rw [dif_pos h]
  have hs := Classical.choose_spec h
  rcases hs with hs | hs
  · exact absurd hs (C.dartOf_ne_mate _ _)
  · have : C.dartOf (Classical.choose h) = C.dartOf c := by
      rw [← M.mate_mate (C.dartOf (Classical.choose h)), hs, M.mate_mate]
    rw [C.dartOf_injective this]

lemma glueT_of_not (L : ChainLab n E) (x : D) (hx : ¬ C.IsT x) : C.glueT L x = 0 := by
  unfold glueT; rw [dif_neg hx]

lemma glueT_mate (L : ChainLab n E) (x : D) : C.glueT L (M.mate x) = C.glueT L x := by
  by_cases hx : C.IsT x
  · obtain ⟨c, hc | hc⟩ := hx
    · subst hc; rw [glueT_mate_dartOf, glueT_dartOf]
    · subst hc; rw [M.mate_mate, glueT_mate_dartOf, glueT_dartOf]
  · have : ¬ C.IsT (M.mate x) := fun h => hx ((C.isT_mate x).mp h)
    rw [glueT_of_not C L _ hx, glueT_of_not C L _ this]

lemma isT_uDart (i : Fin n) (k : Fin 4) : C.IsT (C.LD.uDart i k) := by
  fin_cases k
  · exact ⟨.inl (i, 0), Or.inl rfl⟩
  · exact ⟨.inl (i, 1), Or.inl rfl⟩
  · exact ⟨.inr (.inl i.castSucc), Or.inr rfl⟩
  · exact ⟨.inr (.inl i.succ), Or.inl rfl⟩

lemma isT_vDart (i : Fin n) (k : Fin 4) : C.IsT (C.LD.vDart i k) := by
  fin_cases k
  · exact ⟨.inl (i, 0), Or.inr rfl⟩
  · exact ⟨.inl (i, 1), Or.inr rfl⟩
  · exact ⟨.inr (.inr i.castSucc), Or.inr rfl⟩
  · exact ⟨.inr (.inr i.succ), Or.inl rfl⟩

lemma glueT_uDart (L : ChainLab n E) (i : Fin n) (k : Fin 4) :
    C.glueT L (C.LD.uDart i k) = L.uSlot i k := by
  fin_cases k
  · exact C.glueT_dartOf L (.inl (i, 0))
  · exact C.glueT_dartOf L (.inl (i, 1))
  · exact C.glueT_mate_dartOf L (.inr (.inl i.castSucc))
  · exact C.glueT_dartOf L (.inr (.inl i.succ))

lemma glueT_vDart (L : ChainLab n E) (i : Fin n) (k : Fin 4) :
    C.glueT L (C.LD.vDart i k) = L.vSlot i k := by
  fin_cases k
  · exact C.glueT_mate_dartOf L (.inl (i, 0))
  · exact C.glueT_mate_dartOf L (.inl (i, 1))
  · exact C.glueT_mate_dartOf L (.inr (.inr i.castSucc))
  · exact C.glueT_dartOf L (.inr (.inr i.succ))

/-- Dart labellings constant on bonds with the interior conservation laws. -/
abbrev Xint (C : LadderDarts.Ctx M u v) (E : Type*) [AddCommGroup E] : Type _ :=
  {κ : D → E // (∀ x, κ (M.mate x) = κ x) ∧
    (∀ i, ∑ k, sgn M (C.LD.uDart i k) • κ (C.LD.uDart i k) = 0) ∧
    (∀ i, ∑ k, sgn M (C.LD.vDart i k) • κ (C.LD.vDart i k) = 0)}

/-- Dart labellings constant on bonds, vanishing on the interior bonds. -/
abbrev Uset (C : LadderDarts.Ctx M u v) (E : Type*) [AddCommGroup E] : Type _ :=
  {κ : D → E // (∀ x, κ (M.mate x) = κ x) ∧ ∀ x, C.IsT x → κ x = 0}

open scoped Classical in
/-- **The ladder chart on dart labellings.** -/
noncomputable def xintEquiv : Xint C E ≃ Uset C E × {L : ChainLab n E // C.signs.IsSol L} where
  toFun κ := (⟨fun x => if C.IsT x then 0 else κ.1 x, fun x => by
      by_cases h : C.IsT x
      · simp [h, (C.isT_mate x).mpr h]
      · have h' : ¬ C.IsT (M.mate x) := fun hh => h ((C.isT_mate x).mp hh)
        simp [h, h', κ.2.1 x], fun x hx => by simp [hx]⟩,
    ⟨C.chainOf κ.1, C.isSol_chainOf κ.1 κ.2.1 κ.2.2.1 κ.2.2.2⟩)
  invFun p := ⟨fun x => p.1.1 x + C.glueT p.2.1 x, fun x => by
      simp only [p.1.2.1 x, C.glueT_mate], by
      refine ⟨fun i => ?_, fun i => ?_⟩
      · simp only [fun k => p.1.2.2 _ (C.isT_uDart i k), zero_add, C.glueT_uDart]
        exact (p.2.2 i).1
      · simp only [fun k => p.1.2.2 _ (C.isT_vDart i k), zero_add, C.glueT_vDart]
        have := (p.2.2 i).2
        simp only [signs] at this
        simp only [C.sgn_vDart, neg_smul, Finset.sum_neg_distrib, neg_eq_zero]
        exact this⟩
  left_inv κ := by
    apply Subtype.ext
    funext x
    show (if C.IsT x then 0 else κ.1 x) + C.glueT (C.chainOf κ.1) x = κ.1 x
    by_cases hx : C.IsT x
    · rw [if_pos hx, zero_add]
      obtain ⟨c, hc | hc⟩ := hx
      · subst hc; rw [glueT_dartOf, labOf_chainOf]
      · subst hc; rw [glueT_mate_dartOf, labOf_chainOf, κ.2.1]
    · rw [if_neg hx, glueT_of_not C _ _ hx, add_zero]
  right_inv p := by
    refine Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)
    · funext x
      show (if C.IsT x then 0 else p.1.1 x + C.glueT p.2.1 x) = p.1.1 x
      by_cases hx : C.IsT x
      · rw [if_pos hx, p.1.2.2 x hx]
      · rw [if_neg hx, glueT_of_not C _ _ hx, add_zero]
    · refine ChainLab.ext ?_ ?_ ?_
      · funext i k
        show p.1.1 (C.LD.ru (LadderDarts.ir i) k) + C.glueT p.2.1 (C.LD.ru (LadderDarts.ir i) k) = _
        have hz : p.1.1 (C.LD.ru (LadderDarts.ir i) k) = 0 := p.1.2.2 _ ⟨.inl (i, k), Or.inl rfl⟩
        rw [hz]
        exact (zero_add _).trans (C.glueT_dartOf p.2.1 (.inl (i, k)))
      · funext q
        show p.1.1 (C.LD.ra q) + C.glueT p.2.1 (C.LD.ra q) = _
        have hz : p.1.1 (C.LD.ra q) = 0 := p.1.2.2 _ ⟨.inr (.inl q), Or.inl rfl⟩
        rw [hz]
        exact (zero_add _).trans (C.glueT_dartOf p.2.1 (.inr (.inl q)))
      · funext q
        show p.1.1 (C.LD.rc q) + C.glueT p.2.1 (C.LD.rc q) = _
        have hz : p.1.1 (C.LD.rc q) = 0 := p.1.2.2 _ ⟨.inr (.inr q), Or.inl rfl⟩
        rw [hz]
        exact (zero_add _).trans (C.glueT_dartOf p.2.1 (.inr (.inr q)))

end LadderDarts.Ctx
end WaveTurbulence.LadderDecay

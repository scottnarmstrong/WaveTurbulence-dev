/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL13
/-! **G3-LOWDEG (R48), part 17: loops, the molecule `unloop` and its structural invariants.**
`Molecule.unloop M` deletes the loop darts (both darts of every self-loop bond) and keeps the atoms.  Facts: the bond count drops
by the number `k` of loops, the atom set and the component structure are unchanged (`circuitRank` drops by `k`), and the
ladders (`IsLadder`, `maximalLadders`, `rho`) are unchanged (a ladder uses only bonds between distinct atoms). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
variable {V D : Type*} [DecidableEq V] [Fintype D] [DecidableEq D] {d : ℕ}

/-- The darts that are not loop darts. -/
abbrev NonLoop (M : Molecule V D) : Type _ := {x : D // M.atom x ≠ M.atom (M.mate x)}

/-- **The molecule without its loops**: the same atoms, the non-loop darts. -/
def _root_.WaveTurbulence.Molecule.unloop (M : Molecule V D) : Molecule V (NonLoop M) where
  atoms := M.atoms
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1, by rw [M.mate_mate]; exact fun h => x.2 h.symm⟩
  out := fun x => M.out x.1
  atom_mem := fun x => M.atom_mem x.1
  mate_mate := fun x => Subtype.ext (M.mate_mate x.1)
  mate_ne := fun x h => M.mate_ne x.1 (congrArg Subtype.val h)
  out_mate := fun x => M.out_mate x.1

/-- The loop bonds (represented by their outgoing darts). -/
noncomputable def _root_.WaveTurbulence.Molecule.loopBonds (M : Molecule V D) : Finset D :=
  M.bonds.filter fun x => M.atom x = M.atom (M.mate x)

theorem unloop_atoms (M : Molecule V D) : M.unloop.atoms = M.atoms := rfl

theorem unloop_bonds_card (M : Molecule V D) : M.unloop.bonds.card + M.loopBonds.card = M.bonds.card := by
  have h1 : M.unloop.bonds.card = (M.bonds.filter fun x => ¬ M.atom x = M.atom (M.mate x)).card := by
    refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
    · intro x hx
      have hx' : M.out x.1 = true := (Finset.mem_filter.1 hx).2
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hx', x.2⟩
    · intro x _ y _ e; exact Subtype.ext e
    · intro y hy
      simp only [Molecule.bonds, Finset.mem_filter, Finset.mem_univ, true_and] at hy
      refine ⟨⟨y, hy.2⟩, ?_, rfl⟩
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _, hy.1⟩
  rw [h1]; unfold Molecule.loopBonds
  rw [add_comm]; exact Finset.card_filter_add_card_filter_not (s := M.bonds) (fun x => M.atom x = M.atom (M.mate x))

theorem unloop_adj_of (M : Molecule V D) {a b : V} (h : M.unloop.Adj a b) : M.Adj a b := by
  obtain ⟨x, hx, hx'⟩ := h; exact ⟨x.1, hx, hx'⟩

theorem adj_unloop_or (M : Molecule V D) {a b : V} (h : M.Adj a b) : a = b ∨ M.unloop.Adj a b := by
  obtain ⟨x, hx, hx'⟩ := h
  by_cases e : M.atom x = M.atom (M.mate x)
  · left; rw [← hx, ← hx']; exact e
  · right; exact ⟨⟨x, e⟩, hx, hx'⟩

theorem unloop_numComponents (M : Molecule V D) : M.unloop.numComponents = M.numComponents := by
  unfold Molecule.numComponents
  refine Nat.card_congr ?_
  refine
    { toFun := Quot.lift (fun u : M.unloop.atoms => Quot.mk (fun u v : M.atoms => M.Adj u.1 v.1) (⟨u.1, u.2⟩ : M.atoms))
        (fun a b hab => Quot.sound (unloop_adj_of M hab))
      invFun := Quot.lift (fun u : M.atoms => Quot.mk (fun u v : M.unloop.atoms => M.unloop.Adj u.1 v.1) (⟨u.1, u.2⟩ : M.unloop.atoms))
        (fun a b hab => by
          rcases adj_unloop_or M hab with h | h
          · have : a = b := Subtype.ext h
            rw [this]
          · exact Quot.sound h)
      left_inv := ?_
      right_inv := ?_ }
  · intro q; induction q using Quot.ind with | _ a => rfl
  · intro q; induction q using Quot.ind with | _ a => rfl


theorem unloop_circuitRank (M : Molecule V D) : M.circuitRank = M.unloop.circuitRank + (M.loopBonds.card : ℤ) := by
  unfold Molecule.circuitRank
  rw [unloop_numComponents, unloop_atoms, ← unloop_bonds_card M]; push_cast; ring

theorem ends_ne_of {a b : V} (h : a ≠ b) {M : Molecule V D} {x : D} (hx : M.ends x = s(a, b)) :
    M.atom x ≠ M.atom (M.mate x) := by
  intro e
  unfold Molecule.ends at hx
  rw [← e] at hx
  have := Sym2.eq_iff.1 hx
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact h (h1.symm.trans h2)
  · exact h (h2.symm.trans h1)

theorem unloop_bondsBetween (M : Molecule V D) {a b : V} (h : a ≠ b) :
    M.unloop.bondsBetween a b = M.bondsBetween a b := by
  unfold Molecule.bondsBetween
  refine Finset.card_bij (fun x _ => x.1) ?_ ?_ ?_
  · intro x hx
    have h1 := Finset.mem_filter.1 hx
    refine Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h1.1 |> Finset.mem_filter.1 |>.2⟩, h1.2⟩
  · intro x _ y _ e; exact Subtype.ext e
  · intro y hy
    have h1 := Finset.mem_filter.1 hy
    have h2 := Finset.mem_filter.1 h1.1
    have hnl : M.atom y ≠ M.atom (M.mate y) := ends_ne_of h h1.2
    exact ⟨⟨y, hnl⟩, Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨Finset.mem_univ _, h2.2⟩, h1.2⟩, rfl⟩

theorem unloop_directed (M : Molecule V D) {a b : V} (h : a ≠ b) : M.unloop.Directed a b ↔ M.Directed a b := by
  constructor
  · rintro ⟨x, hx, h1, h2⟩; exact ⟨x.1, hx, h1, h2⟩
  · rintro ⟨x, hx, h1, h2⟩
    exact ⟨⟨x, by rw [h1, h2]; exact h⟩, hx, h1, h2⟩

theorem ladder_distinct {m : ℕ} {u v : Fin (m + 1) → V} (hinj : Function.Injective (Sum.elim u v)) :
    (∀ j, u j ≠ v j) ∧ (∀ j : Fin m, u j.castSucc ≠ u j.succ ∧ v j.castSucc ≠ v j.succ) := by
  refine ⟨fun j e => ?_, fun j => ⟨fun e => ?_, fun e => ?_⟩⟩
  · have := @hinj (Sum.inl j) (Sum.inr j) (by simpa using e); simp at this
  · have := @hinj (Sum.inl j.castSucc) (Sum.inl j.succ) (by simpa using e)
    simp at this; exact absurd this (Fin.castSucc_lt_succ.ne)
  · have := @hinj (Sum.inr j.castSucc) (Sum.inr j.succ) (by simpa using e)
    simp at this; exact absurd this (Fin.castSucc_lt_succ.ne)

theorem unloop_isLadder (M : Molecule V D) {m : ℕ} (u v : Fin (m + 1) → V) :
    M.unloop.IsLadder u v ↔ M.IsLadder u v := by
  unfold Molecule.IsLadder
  by_cases hinj : Function.Injective (Sum.elim u v)
  · obtain ⟨hd1, hd2⟩ := ladder_distinct hinj
    have e1 : ∀ j, M.unloop.bondsBetween (u j) (v j) = M.bondsBetween (u j) (v j) := fun j => unloop_bondsBetween M (hd1 j)
    have e2 : ∀ j : Fin m, M.unloop.bondsBetween (u j.castSucc) (u j.succ) = M.bondsBetween (u j.castSucc) (u j.succ) :=
      fun j => unloop_bondsBetween M (hd2 j).1
    have e3 : ∀ j : Fin m, M.unloop.bondsBetween (v j.castSucc) (v j.succ) = M.bondsBetween (v j.castSucc) (v j.succ) :=
      fun j => unloop_bondsBetween M (hd2 j).2
    have e4 : ∀ j : Fin m, M.unloop.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (u j.castSucc) (u j.succ) :=
      fun j => unloop_directed M (hd2 j).1
    have e5 : ∀ j : Fin m, M.unloop.Directed (v j.succ) (v j.castSucc) ↔ M.Directed (v j.succ) (v j.castSucc) :=
      fun j => unloop_directed M (hd2 j).2.symm
    simp only [e1, e2, e3, e4, e5, unloop_atoms]
  · simp [hinj]

theorem unloop_isLadderSet (M : Molecule V D) (S : Finset V) : M.unloop.IsLadderSet S ↔ M.IsLadderSet S := by
  unfold Molecule.IsLadderSet
  simp only [unloop_isLadder]

theorem unloop_maximalLadders (M : Molecule V D) : M.unloop.maximalLadders = M.maximalLadders := by
  unfold Molecule.maximalLadders
  simp only [unloop_isLadderSet, unloop_atoms]

theorem unloop_rho (M : Molecule V D) : M.unloop.rho = M.rho := by
  unfold Molecule.rho Molecule.numLadders Molecule.numFree
  simp only [unloop_maximalLadders, unloop_atoms]

/-! ### The decoration count -/

theorem mem_dartsAt' {D' : Type*} [Fintype D'] [DecidableEq D'] (M : Molecule V D') (v : V) (x : D') :
    x ∈ M.dartsAt v ↔ M.atom x = v := by simp [Molecule.dartsAt]

theorem sum_dartsAt_unloop {E : Type*} [AddCommGroup E] (M : Molecule V D) (v : V) (f : D → E)
    (hf : ∀ x, M.atom x = M.atom (M.mate x) → f (M.mate x) + f x = 0) :
    ∑ x ∈ M.dartsAt v, f x = ∑ x ∈ M.unloop.dartsAt v, f x.1 := by
  have h1 : ∑ x ∈ M.dartsAt v, f x = ∑ x ∈ (M.dartsAt v).filter (fun x => M.atom x ≠ M.atom (M.mate x)), f x +
      ∑ x ∈ (M.dartsAt v).filter (fun x => ¬ M.atom x ≠ M.atom (M.mate x)), f x :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have h2 : ∑ x ∈ (M.dartsAt v).filter (fun x => ¬ M.atom x ≠ M.atom (M.mate x)), f x = 0 := by
    have hmem : ∀ x ∈ (M.dartsAt v).filter (fun x => ¬ M.atom x ≠ M.atom (M.mate x)), M.atom x = v ∧ M.atom x = M.atom (M.mate x) := by
      intro x hx
      simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and, not_not] at hx
      exact hx
    refine Finset.sum_involution (fun x _ => M.mate x) (fun x hx => ?_) (fun x _ _ => M.mate_ne x) (fun x hx => ?_)
      (fun x _ => M.mate_mate x)
    · rw [add_comm]; exact hf x (hmem x hx).2
    · obtain ⟨h1, h2⟩ := hmem x hx
      simp only [Finset.mem_filter, Molecule.dartsAt, Finset.mem_univ, true_and, not_not, M.mate_mate]
      exact ⟨by rw [← h2]; exact h1, h2.symm⟩
  rw [h1, h2, add_zero]
  refine (Finset.sum_bij (fun x _ => x.1) ?_ ?_ ?_ ?_).symm
  · intro x hx
    have hx' : M.atom x.1 = v := (mem_dartsAt' M.unloop v x).1 hx
    exact Finset.mem_filter.2 ⟨(mem_dartsAt' M v x.1).2 hx', x.2⟩
  · intro x _ y _ e; exact Subtype.ext e
  · intro y hy
    have hy' := Finset.mem_filter.1 hy
    exact ⟨⟨y, hy'.2⟩, (mem_dartsAt' M.unloop v _).2 ((mem_dartsAt' M v y).1 hy'.1), rfl⟩
  · intro x _; rfl

theorem dartSign_mateL (M : Molecule V D) (x : D) : M.dartSign (M.mate x) = - M.dartSign x := by
  unfold Molecule.dartSign
  have := M.out_mate x
  cases h : M.out x <;> simp_all

theorem unloop_deg_le (M : Molecule V D) (v : V) : M.unloop.deg v ≤ M.deg v := by
  unfold Molecule.deg
  refine Finset.card_le_card_of_injOn (fun x => x.1) (fun x hx => ?_) (fun x _ y _ e => Subtype.ext e)
  exact (mem_dartsAt' M v x.1).2 ((mem_dartsAt' M.unloop v x).1 hx)

/-- The admissibility predicate pushed forward to the loop-free molecule. -/
def unloopAdm (M : Molecule V D) (Adm : (D → Fin d → ℤ) → Prop) : (NonLoop M → Fin d → ℤ) → Prop :=
  fun κ' => ∃ κ, Adm κ ∧ κ' = fun x => κ x.1

theorem unloop_isDecoration (M : Molecule V D) {L : ℝ} {w : Mom d} {c : V → Mom d} {κ : D → Fin d → ℤ}
    (h : M.IsDecoration L w c κ) : M.unloop.IsDecoration L w c (fun x => κ x.1) := by
  refine ⟨fun x => h.1 x.1, fun v hv => ?_⟩
  have e := h.2 v hv
  rw [sum_dartsAt_unloop M v (fun x => M.dartSign x • Molecule.kvec L w κ x) ?_] at e
  · exact e
  · intro x _
    show M.dartSign (M.mate x) • Molecule.kvec L w κ (M.mate x) + M.dartSign x • Molecule.kvec L w κ x = 0
    simp only [Molecule.kvec, dartSign_mateL, h.1 x]; simp only [neg_smul, smul_add]; abel

theorem unloop_gamma (M : Molecule V D) {L : ℝ} {w : Mom d} {κ : D → Fin d → ℤ} (hκ : ∀ x, κ (M.mate x) = κ x)
    (v : V) : M.unloop.Gamma L w (fun x => κ x.1) v = M.Gamma L w κ v := by
  unfold Molecule.Gamma
  rw [sum_dartsAt_unloop M v (fun x => M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2) ?_]
  · rfl
  · intro x _
    show M.dartSign (M.mate x) * ‖Molecule.kvec L w κ (M.mate x)‖ ^ 2 + M.dartSign x * ‖Molecule.kvec L w κ x‖ ^ 2 = 0
    simp only [Molecule.kvec, dartSign_mateL, hκ x]; ring

theorem countE_unloop_le (M : Molecule V D) (hb : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ : ℝ) (w : Mom d)
    (Adm : (D → Fin d → ℤ) → Prop)
    (hdet : ∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ → (∀ x : D, M.atom x ≠ M.atom (M.mate x) → κ₁ x = κ₂ x) → κ₁ = κ₂) :
    M.countE L γ δ w Adm ≤ M.unloop.countE L γ δ w (unloopAdm M Adm) := by
  unfold Molecule.countE
  refine iSup_le fun c => iSup_le fun hc => iSup_le fun β => iSup_le fun k0 => iSup_le fun hk0 => ?_
  have hc' : ∀ v ∈ M.unloop.atoms, M.unloop.deg v = 4 → c v = 0 := fun v hv h4 =>
    hc v hv (le_antisymm (hb v hv) (h4 ▸ unloop_deg_le M v))
  have hk0' : ∀ x : NonLoop M, (fun x : NonLoop M => k0 x.1) (M.unloop.mate x) = (fun x : NonLoop M => k0 x.1) x :=
    fun x => hk0 x.1
  refine le_trans ?_ (le_iSup_of_le c (le_iSup_of_le hc' (le_iSup_of_le β (le_iSup_of_le (fun x : NonLoop M => k0 x.1)
    (le_iSup_of_le hk0' le_rfl)))))
  set S := {κ | M.IsDecoration L w c κ ∧ M.IsRestricted L γ δ w β k0 κ ∧ Adm κ} with hS
  have hinj : Set.InjOn (fun (κ : D → Fin d → ℤ) (x : NonLoop M) => κ x.1) S := by
    intro κ₁ h₁ κ₂ h₂ e
    exact hdet κ₁ κ₂ h₁.2.2 h₂.2.2 (fun x hx => congrFun e ⟨x, hx⟩)
  rw [← hinj.encard_image]
  refine Set.encard_le_encard ?_
  rintro _ ⟨κ, hκ, rfl⟩
  refine ⟨unloop_isDecoration M hκ.1, ⟨fun v hv => ?_, fun x => hκ.2.1.2 x.1⟩, κ, hκ.2.2, rfl⟩
  rw [unloop_gamma M hκ.1.1 v]
  exact hκ.2.1.1 v hv

/-- **The molecule-level unloop deviation** (TARGET Remark `remtame` / DH23 10.5 for degenerate loops; research-fcgeom Q3):
`𝔄(M) ≤ (L^{-(d-γ)} C₁⁻¹ δ^{1/2})^k 𝔄(M.unloop)` for a molecule with `k` loops, when the admissible labels are determined by their
values off the loop darts (`hdet`, the `ε`-support: all legs of a loop atom are equal, and the root leg is fixed). -/
theorem countA_unloop_le (M : Molecule V D) (hb : ∀ a ∈ M.atoms, M.deg a ≤ 4) (L γ δ C₁ : ℝ) (hL : 0 < L) (hC : 0 < C₁)
    (hδ : 0 < δ) (w : Mom d) (Adm : (D → Fin d → ℤ) → Prop)
    (hdet : ∀ κ₁ κ₂, Adm κ₁ → Adm κ₂ → (∀ x : D, M.atom x ≠ M.atom (M.mate x) → κ₁ x = κ₂ x) → κ₁ = κ₂)
    (P : Finset V → ℝ) :
    M.countA L γ δ C₁ w Adm P ≤
      ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) ^ M.loopBonds.card) *
        M.unloop.countA L γ δ C₁ w (unloopAdm M Adm) P := by
  have hE := countE_unloop_le M hb L γ δ w Adm hdet
  unfold Molecule.countA
  rw [unloop_circuitRank, unloop_maximalLadders]
  set k := M.loopBonds.card
  set χ := M.unloop.circuitRank
  set Pr := ∏ S ∈ M.maximalLadders, Molecule.ladderWeight L γ δ (P S) ^ Molecule.ladderLength S
  have hc : 0 < C₁⁻¹ * δ ^ (1 / 2 : ℝ) := mul_pos (inv_pos.2 hC) (Real.rpow_pos_of_pos hδ _)
  have hX : L ^ (-((d : ℝ) - γ) * ((χ + k : ℤ) : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (χ + k) * Pr =
      (L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) ^ k *
        (L ^ (-((d : ℝ) - γ) * (χ : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χ * Pr) := by
    have e1 : L ^ (-((d : ℝ) - γ) * ((χ + k : ℤ) : ℝ)) = L ^ (-((d : ℝ) - γ) * (χ : ℝ)) * (L ^ (-((d : ℝ) - γ))) ^ k := by
      push_cast
      rw [mul_add, Real.rpow_add hL, Real.rpow_mul_natCast hL.le]
    have e2 : (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ (χ + k) = (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χ * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ k := by
      rw [zpow_add₀ hc.ne', zpow_natCast]
    rw [e1, e2, mul_pow]; ring
  rw [hX, ENNReal.ofReal_mul (by positivity)]
  have hE' : ((M.countE L γ δ w Adm : ℕ∞) : ℝ≥0∞) ≤ ((M.unloop.countE L γ δ w (unloopAdm M Adm) : ℕ∞) : ℝ≥0∞) :=
    ENat.toENNReal_le.2 hE
  calc (M.countE L γ δ w Adm : ℝ≥0∞) * (ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) ^ k) *
        ENNReal.ofReal (L ^ (-((d : ℝ) - γ) * (χ : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χ * Pr))
      = ENNReal.ofReal ((L ^ (-((d : ℝ) - γ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ))) ^ k) *
        ((M.countE L γ δ w Adm : ℝ≥0∞) * ENNReal.ofReal (L ^ (-((d : ℝ) - γ) * (χ : ℝ)) * (C₁⁻¹ * δ ^ (1 / 2 : ℝ)) ^ χ * Pr)) := by ring
    _ ≤ _ := by gcongr

end WaveTurbulence.FinalCountG3

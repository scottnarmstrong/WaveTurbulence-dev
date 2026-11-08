/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutPinKer

/-! # D2c-2 PROT-CUT, MK-β: (P5) and (P7) in D3's configuration forms

`X = appendChain Xp (pair m Qr Qg inner nil)`: `𝔫_a` at `Xp.lonePath`, the terminal node `𝔫_b` at
`Xp.lonePath ++ bPath m inner`. Both configurations are instances of the generalized terminal cut
`CutTermData.kernelProt_cutPin`.

* **(P5)** `ProtCfg.penTerm` with a nonempty interior (`inner.lonePath ≠ []`; the empty interior is (P4),
  `kernelProt_penTerm_cfg`): the penultimate chain node `π_j` is the terminal node of the interior, linked inside the
  pair `{𝔫_a, 𝔫_b}`. `kernelProt_penTerm_cfg5`: (cut-term) whose interior piece carries its own terminal designation
  `ProtCfg.term.fix inner s t u`, so that (cut-term) applies to it again (`kernelProt_term_cut` with code `inner`):
  `T_A[K_pre(T, u) Q₁Q₂(u, s) (T_B G)(u, s)](T, s)` of o104 (P5).
* **(P7)** `ProtCfg.termChild i`: `𝔫_b` and its child at slot `i` designated at `s`.
  `kernelProt_termChild_cfg`: (cut-term) whose side-couple pieces carry `sideFix`, the root of the side-couple tree
  hanging at `bPath m inner ++ [i]` designated at `s` (its own upper clock `cupR … u s j = s`): the root trace
  `Q₁^m(u, s)` of o104 (P7). `sideFix_eq_trFix`: this is `trFix j s` (tree `j`'s root at `s`) when tree `j` hangs
  there, and `sideFix_eq_none` otherwise. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-! ### The designations -/

/-- (P5): the interior's terminal node (the penultimate chain node) and `𝔫_b` designated at `s`. -/
def p5Fix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (s : ℝ) {T : Fin 1 → TTree} (b : GBranch T) :
    Option ℝ :=
  if b.1.2 = Xp.lonePath ++ m.c :: inner.lonePath.dropLast ∨ b.1.2 = Xp.lonePath ++ bPath m inner then some s
  else none

/-- (P7): `𝔫_b` and its child at slot `i` designated at `s`. -/
def p7Fix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (i : Fin 3) (s : ℝ) {T : Fin 1 → TTree}
    (b : GBranch T) : Option ℝ :=
  if b.1.2 = Xp.lonePath ++ bPath m inner ∨ b.1.2 = Xp.lonePath ++ (bPath m inner ++ [i]) then some s else none

/-- A side couple with the root of the tree placed at `target` (by `base`) designated at `s`. -/
def sideFix (base : Fin 2 → Path) (target : Path) (s : ℝ) {T : Fin 2 → TTree} (y : GBranch T) : Option ℝ :=
  if y.1.2 = [] ∧ base y.1.1 = target then some s else none

/-- **The root trace designation** of a couple: the root of tree `j` designated at `σ`. -/
def trFix (j : Fin 2) (σ : ℝ) {T : Fin 2 → TTree} (y : GBranch T) : Option ℝ :=
  if y.1.1 = j ∧ y.1.2 = [] then some σ else none

theorem dropLast_cons_ne {α : Type*} (a : α) {l : List α} (hl : l ≠ []) : (a :: l).dropLast = a :: l.dropLast := by
  obtain ⟨l', x, rfl⟩ := List.eq_nil_or_concat l |>.resolve_left hl
  rw [List.concat_eq_append, ← List.cons_append, List.dropLast_concat, List.dropLast_concat]

theorem cfg_penTerm_fix5 (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain)
    (hin : inner.lonePath ≠ []) (s t up : ℝ) {T : Fin 1 → TTree} :
    (ProtCfg.penTerm.fix (appendChain Xp (cpair m Qr Qg inner)) s t up : GBranch T → Option ℝ) =
      p5Fix Xp m inner s := by
  have h1 := lonePath_dropLast_cutTerm Xp m Qr Qg inner
  have h2 : (appendChain Xp (cpair m Qr Qg inner)).lonePath.dropLast.dropLast =
      Xp.lonePath ++ m.c :: inner.lonePath.dropLast := by
    rw [h1, List.dropLast_append_of_ne_nil (bPath_ne_nil m inner), bPath, List.singleton_append,
      dropLast_cons_ne _ hin]
  funext b
  unfold ProtCfg.fix ProtCfg.pins p5Fix
  rw [if_pos (Fin.val_eq_zero _), h2, h1]
  simp only [List.lookup]
  by_cases ha : b.1.2 = Xp.lonePath ++ m.c :: inner.lonePath.dropLast
  · rw [show (b.1.2 == Xp.lonePath ++ m.c :: inner.lonePath.dropLast) = true from beq_iff_eq.mpr ha,
      if_pos (Or.inl ha)]
  · rw [show (b.1.2 == Xp.lonePath ++ m.c :: inner.lonePath.dropLast) = false from beq_eq_false_iff_ne.mpr ha]
    by_cases hb : b.1.2 = Xp.lonePath ++ bPath m inner
    · rw [show (b.1.2 == Xp.lonePath ++ bPath m inner) = true from beq_iff_eq.mpr hb, if_pos (Or.inr hb)]
    · rw [show (b.1.2 == Xp.lonePath ++ bPath m inner) = false from beq_eq_false_iff_ne.mpr hb,
        if_neg (fun h => h.elim ha hb)]

theorem cfg_termChild_fix (Xp : RegChain) (m : MiniTreeCode) (Qr Qg : RegCpl) (inner : RegChain) (i : Fin 3)
    (s t up : ℝ) {T : Fin 1 → TTree} :
    ((ProtCfg.termChild i).fix (appendChain Xp (cpair m Qr Qg inner)) s t up : GBranch T → Option ℝ) =
      p7Fix Xp m inner i s := by
  have h1 := lonePath_dropLast_cutTerm Xp m Qr Qg inner
  funext b
  unfold ProtCfg.fix ProtCfg.pins p7Fix
  rw [if_pos (Fin.val_eq_zero _), h1]
  simp only [List.lookup]
  by_cases ha : b.1.2 = Xp.lonePath ++ bPath m inner
  · rw [show (b.1.2 == Xp.lonePath ++ bPath m inner) = true from beq_iff_eq.mpr ha, if_pos (Or.inl ha)]
  · rw [show (b.1.2 == Xp.lonePath ++ bPath m inner) = false from beq_eq_false_iff_ne.mpr ha]
    by_cases hb : b.1.2 = Xp.lonePath ++ bPath m inner ++ [i]
    · rw [show (b.1.2 == Xp.lonePath ++ bPath m inner ++ [i]) = true from beq_iff_eq.mpr hb,
        if_pos (Or.inr (hb.trans (List.append_assoc _ _ _)))]
    · rw [show (b.1.2 == Xp.lonePath ++ bPath m inner ++ [i]) = false from beq_eq_false_iff_ne.mpr hb,
        if_neg (fun h => h.elim ha (fun h' => hb (h'.trans (List.append_assoc _ _ _).symm)))]

theorem p5Fix_cutPinFix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (s : ℝ) {T : Fin 1 → TTree} :
    CutPinFix Xp m inner s (p5Fix Xp m inner s : GBranch T → Option ℝ) := by
  refine ⟨fun b hb => by simp [p5Fix, hb], fun b σ h => ?_⟩
  unfold p5Fix at h
  split_ifs at h with hb
  refine ⟨(Option.some.inj h).symm, ?_⟩
  rcases hb with hb | hb
  · exact ⟨m.c :: inner.lonePath.dropLast, by simp, hb⟩
  · exact ⟨bPath m inner, bPath_ne_nil m inner, hb⟩

theorem p7Fix_cutPinFix (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (i : Fin 3) (s : ℝ)
    {T : Fin 1 → TTree} : CutPinFix Xp m inner s (p7Fix Xp m inner i s : GBranch T → Option ℝ) := by
  refine ⟨fun b hb => by simp [p7Fix, hb], fun b σ h => ?_⟩
  unfold p7Fix at h
  split_ifs at h with hb
  refine ⟨(Option.some.inj h).symm, ?_⟩
  rcases hb with hb | hb
  · exact ⟨bPath m inner, bPath_ne_nil m inner, hb⟩
  · exact ⟨bPath m inner ++ [i], by simp, hb⟩

/-! ### Side-couple positions -/

theorem rBase_append_eq_iff (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) (q : Path) (i : Fin 3) :
    rBase m inner ζ j ++ q = bPath m inner ++ [i] ↔ q = [] ∧ rBase m inner ζ j = bPath m inner ++ [i] := by
  constructor
  · intro h
    rcases rBase_cases m inner ζ j with hj | hj
    · rw [hj] at h
      have := congrArg List.head? h
      simp [bPath_eq] at this
      exact absurd this (red_ne_c m)
    · rw [hj, List.append_assoc] at h
      have h' := List.append_cancel_left h
      simp only [List.singleton_append, List.cons.injEq] at h'
      rw [hj, h'.1, h'.2]
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, h⟩
    rw [List.append_nil, h]

theorem gBase_append_eq_iff (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (j : Fin 2) (q : Path) (i : Fin 3) :
    gBase m inner ζ j ++ q = bPath m inner ++ [i] ↔ q = [] ∧ gBase m inner ζ j = bPath m inner ++ [i] := by
  constructor
  · intro h
    rcases gBase_cases m inner ζ j with hj | hj
    · rw [hj] at h
      have := congrArg List.head? h
      simp [bPath_eq] at this
      exact absurd this (green_ne_c m)
    · rw [hj, List.append_assoc] at h
      have h' := List.append_cancel_left h
      simp only [List.singleton_append, List.cons.injEq] at h'
      rw [hj, h'.1, h'.2]
      exact ⟨rfl, rfl⟩
  · rintro ⟨rfl, h⟩
    rw [List.append_nil, h]

theorem rBase_injective (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    Function.Injective (rBase m inner ζ) := by
  intro j j' h
  have hne : ([m.red.1] : Path) ≠ bPath m inner ++ [m.red.2] := (bot_ne_top m inner _ _ (red_ne_c m)).symm
  by_contra hjj
  have hj' : j' = if j = 0 then 1 else 0 := by fin_cases j <;> fin_cases j' <;> simp_all
  subst hj'
  unfold rBase at h
  by_cases hs : slotSign ζ m.red.1 = 1 <;> fin_cases j <;> simp_all

theorem gBase_injective (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) :
    Function.Injective (gBase m inner ζ) := by
  intro j j' h
  have hne : ([m.green.1] : Path) ≠ bPath m inner ++ [m.green.2] := (bot_ne_top m inner _ _ (green_ne_c m)).symm
  by_contra hjj
  have hj' : j' = if j = 0 then 1 else 0 := by fin_cases j <;> fin_cases j' <;> simp_all
  subst hj'
  unfold gBase at h
  by_cases hs : slotSign ζ m.green.1 = 1 <;> fin_cases j <;> simp_all

theorem sideFix_eq_trFix {base : Fin 2 → Path} (hinj : Function.Injective base) {target : Path} {j : Fin 2}
    (hj : base j = target) (s : ℝ) {T : Fin 2 → TTree} :
    (sideFix base target s : GBranch T → Option ℝ) = trFix j s := by
  funext y
  unfold sideFix trFix
  by_cases h1 : y.1.2 = []
  · by_cases h2 : y.1.1 = j
    · rw [if_pos ⟨h1, by rw [h2, hj]⟩, if_pos ⟨h2, h1⟩]
    · rw [if_neg (fun h => h2 (hinj (h.2.trans hj.symm))), if_neg (fun h => h2 h.1)]
  · rw [if_neg (fun h => h1 h.1), if_neg (fun h => h1 h.2)]

theorem sideFix_eq_none {base : Fin 2 → Path} {target : Path} (h : ∀ j, base j ≠ target) (s : ℝ)
    {T : Fin 2 → TTree} : (sideFix base target s : GBranch T → Option ℝ) = fun _ => none := by
  funext y
  unfold sideFix
  rw [if_neg (fun h' => h y.1.1 h'.2)]

/-! ### The pieces' designations -/

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
include D

theorem βI_path (x : GBranch LGi.garden.tree) : (D.βI x).1.2 = Xp.lonePath ++ m.c :: x.1.2 := rfl

theorem βR_path (y : GBranch LGr.garden.tree) :
    (D.βR y).1.2 = Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) y.1.1 ++ y.1.2) := rfl

theorem βG_path (y : GBranch LGg.garden.tree) :
    (D.βG y).1.2 = Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) y.1.1 ++ y.1.2) := rfl

theorem interior_not_prefix (x : GBranch LGi.garden.tree) : ¬ inner.lonePath <+: x.1.2 := by
  have hx := x.2
  rw [show x.1.1 = 0 from Subsingleton.elim _ _, D.decI.1] at hx
  exact PairData.not_lonePath_prefix_of_branching hx

theorem p5_βI (hin : inner.lonePath ≠ []) (s t up : ℝ) :
    (fun x => p5Fix Xp m inner s (D.βI x)) = ProtCfg.term.fix inner s t up := by
  funext x
  unfold p5Fix ProtCfg.fix ProtCfg.pins
  rw [if_pos (Fin.val_eq_zero _), D.βI_path]
  simp only [List.lookup]
  have hb : ¬ Xp.lonePath ++ m.c :: x.1.2 = Xp.lonePath ++ bPath m inner := by
    intro h
    have h' := List.append_cancel_left h
    simp only [bPath, List.singleton_append, List.cons.injEq] at h'
    exact D.interior_not_prefix x (h'.2 ▸ List.prefix_refl _)
  by_cases ha : x.1.2 = inner.lonePath.dropLast
  · rw [if_pos (Or.inl (by rw [ha])), show (x.1.2 == inner.lonePath.dropLast) = true from beq_iff_eq.mpr ha]
  · rw [if_neg (fun h => h.elim (fun h' => ha (List.cons.inj (List.append_cancel_left h')).2) hb),
      show (x.1.2 == inner.lonePath.dropLast) = false from beq_eq_false_iff_ne.mpr ha]

omit D in
theorem notPrefix_dropLast (hin : inner.lonePath ≠ []) : ¬ inner.lonePath <+: inner.lonePath.dropLast := by
  intro h
  have := h.length_le
  rw [List.length_dropLast] at this
  have : inner.lonePath.length ≠ 0 := fun h0 => hin (List.eq_nil_of_length_eq_zero h0)
  omega

theorem p5_βR (hin : inner.lonePath ≠ []) (s : ℝ) : (fun y => p5Fix Xp m inner s (D.βR y)) = fun _ => none := by
  funext y
  unfold p5Fix
  rw [D.βR_path, if_neg]
  rintro (h | h)
  · have h' := congrArg (regionOf m inner (LG.garden.sig 0)) (List.append_cancel_left h)
    rw [regionOf_rBase, regionOf_inner m inner _ _ (notPrefix_dropLast hin)] at h'
    exact absurd h' (by simp)
  · have h' := congrArg (regionOf m inner (LG.garden.sig 0)) (List.append_cancel_left h)
    rw [regionOf_rBase, regionOf_bPath] at h'
    exact absurd h' (by simp)

theorem p5_βG (hin : inner.lonePath ≠ []) (s : ℝ) : (fun y => p5Fix Xp m inner s (D.βG y)) = fun _ => none := by
  funext y
  unfold p5Fix
  rw [D.βG_path, if_neg]
  rintro (h | h)
  · have h' := congrArg (regionOf m inner (LG.garden.sig 0)) (List.append_cancel_left h)
    rw [regionOf_gBase, regionOf_inner m inner _ _ (notPrefix_dropLast hin)] at h'
    exact absurd h' (by simp)
  · have h' := congrArg (regionOf m inner (LG.garden.sig 0)) (List.append_cancel_left h)
    rw [regionOf_gBase, regionOf_bPath] at h'
    exact absurd h' (by simp)

theorem p7_βI (i : Fin 3) (s : ℝ) : (fun x => p7Fix Xp m inner i s (D.βI x)) = fun _ => none := by
  funext x
  unfold p7Fix
  rw [D.βI_path, if_neg]
  rintro (h | h)
  · have h' := List.append_cancel_left h
    simp only [bPath, List.singleton_append, List.cons.injEq] at h'
    exact D.interior_not_prefix x (h'.2 ▸ List.prefix_refl _)
  · have h' := List.append_cancel_left h
    simp only [bPath, List.singleton_append, List.cons_append, List.cons.injEq] at h'
    exact D.interior_not_prefix x (h'.2 ▸ List.prefix_append _ _)

theorem p7_βR (i : Fin 3) (s : ℝ) :
    (fun y => p7Fix Xp m inner i s (D.βR y)) = sideFix (rBase m inner (LG.garden.sig 0)) (bPath m inner ++ [i]) s := by
  funext y
  unfold p7Fix sideFix
  rw [D.βR_path]
  have hb : ¬ Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) y.1.1 ++ y.1.2) = Xp.lonePath ++ bPath m inner := by
    intro h
    have h' := congrArg (regionOf m inner (LG.garden.sig 0)) (List.append_cancel_left h)
    rw [regionOf_rBase, regionOf_bPath] at h'
    exact absurd h' (by simp)
  by_cases h : y.1.2 = [] ∧ rBase m inner (LG.garden.sig 0) y.1.1 = bPath m inner ++ [i]
  · rw [if_pos h, if_pos (Or.inr (by rw [(rBase_append_eq_iff m inner _ _ _ i).mpr h]))]
  · rw [if_neg h, if_neg (fun h' => h'.elim hb fun h'' =>
      h ((rBase_append_eq_iff m inner _ _ _ i).mp (List.append_cancel_left h'')))]

theorem p7_βG (i : Fin 3) (s : ℝ) :
    (fun y => p7Fix Xp m inner i s (D.βG y)) = sideFix (gBase m inner (LG.garden.sig 0)) (bPath m inner ++ [i]) s := by
  funext y
  unfold p7Fix sideFix
  rw [D.βG_path]
  have hb : ¬ Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) y.1.1 ++ y.1.2) = Xp.lonePath ++ bPath m inner := by
    intro h
    have h' := congrArg (regionOf m inner (LG.garden.sig 0)) (List.append_cancel_left h)
    rw [regionOf_gBase, regionOf_bPath] at h'
    exact absurd h' (by simp)
  by_cases h : y.1.2 = [] ∧ gBase m inner (LG.garden.sig 0) y.1.1 = bPath m inner ++ [i]
  · rw [if_pos h, if_pos (Or.inr (by rw [(gBase_append_eq_iff m inner _ _ _ i).mpr h]))]
  · rw [if_neg h, if_neg (fun h' => h'.elim hb fun h'' =>
      h ((gBase_append_eq_iff m inner _ _ _ i).mp (List.append_cancel_left h'')))]

end CutTermData

end WaveTurbulence.Flower.ProtCut

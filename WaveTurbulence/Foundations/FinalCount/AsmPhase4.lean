/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmRename
public import WaveTurbulence.Foundations.FinalCount.AsmRun4
public import WaveTurbulence.Foundations.FinalCount.AsmCover2
/-! **FINALCOUNT-ASSEMBLY, phase 4: the cover of the `β`-cut phase.**  Nodes of a state `h`: `(v, x₁, x₂)` with `IsCutData v (fresh h) x₁ x₂`,
`cls v = ε`, a `β`-cut, `3 ≤ deg v`.  The class of a node is `{κ ∈ A | gap(x₁,x₂) ≠ 0}`, on which `UStep4` holds (uniformly).  A decoration of `A`
either has `NoBetaCut` at `h` (terminal piece) or lies in a node class (`isAlphaCut_congr`: the fresh name is immaterial).
`phase4_cover` is `cover_induction2` for this decomposition; the arithmetic (`hW`) and the terminal bound (`hfin`) are its hypotheses. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A canonical fresh atom name of a state. -/
noncomputable def fresh [Infinite V] (h : HSt V D₀) : V := Classical.choose (Infinite.exists_notMem_finset h.s.M.atoms)

theorem fresh_notMem [Infinite V] (h : HSt V D₀) : fresh h ∉ h.s.M.atoms :=
  Classical.choose_spec (Infinite.exists_notMem_finset h.s.M.atoms)

theorem atomRelU_mono {Adm Adm' : (D₀ → (Fin d → ℤ)) → Prop} {L : ℝ} {w : Mom d} {h : HSt V D₀}
    (hR : AtomRelU Adm L w h) (hs : ∀ k, Adm' k → Adm k) : AtomRelU Adm' L w h := by
  intro a ha q vis hc
  obtain ⟨sgn, hsgn, c₀, hr⟩ := hR a ha q vis hc
  exact ⟨sgn, hsgn, c₀, fun k0 hk => hr k0 (hs k0 hk)⟩

theorem pinned_mono {Adm Adm' : (D₀ → (Fin d → ℤ)) → Prop} {L : ℝ} {w : Mom d} {M₀ : Molecule V D₀}
    (hp : PinnedM0 Adm L w M₀) (hs : ∀ k, Adm' k → Adm k) : PinnedM0 Adm' L w M₀ :=
  fun a ha => by obtain ⟨c, hc⟩ := hp a ha; exact ⟨c, fun k0 hk => hc k0 (hs k0 hk)⟩

theorem uctx_mono {Adm Adm' : (D₀ → (Fin d → ℤ)) → Prop} {L : ℝ} {w : Mom d} {M₀ : Molecule V D₀} {Rn : ℕ} {h : HSt V D₀}
    (hc : UCtx M₀ Rn Adm L w h) (hs : ∀ k, Adm' k → Adm k) : UCtx M₀ Rn Adm' L w h :=
  ⟨hc.good, hc.anc, hc.rel, atomRelU_mono hc.atom hs⟩

/-- The class invariant of the cover. -/
def Inv4 (M₀ : Molecule V D₀) (Rn : ℕ) (Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop) (L : ℝ) (w : Mom d)
    (A0 A : Set (D₀ → (Fin d → ℤ))) (h : HSt V D₀) : Prop :=
  A ⊆ A0 ∧ (A = ∅ ∨ (UCtx M₀ Rn (fun k => k ∈ A) L w h ∧ ApPos h.s ∧ ∀ κ ∈ A, Rch κ h))

/-- The data of a phase-4 node of the state `h`. -/
def Node4 [Infinite V] (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) : Prop :=
  h.s.M.IsCutData v (fresh h) x₁ x₂ ∧ h.s.cls v = .eps ∧ ¬ h.s.M.IsAlphaCut v (fresh h) x₁ x₂ ∧ 3 ≤ h.s.M.deg v

/-- The finite set of node data. -/
noncomputable def nodes4 [Infinite V] (h : HSt V D₀) : Finset (V × h.s.D × h.s.D) :=
  (h.s.M.atoms ×ˢ ((Finset.univ : Finset h.s.D) ×ˢ (Finset.univ : Finset h.s.D))).filter fun t => Node4 h t.1 t.2.1 t.2.2

theorem nodes4_card [Infinite V] (h : HSt V D₀) :
    (nodes4 h).card ≤ h.s.M.atoms.card * Fintype.card h.s.D * Fintype.card h.s.D := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Finset.card_product, Finset.card_product]
  simp [mul_assoc]

/-- The class of a node. -/
def cls4 (L : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (x₁ x₂ : h.s.D) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧ pgap L w k (h.s.pr x₁ x₂) ≠ 0}

/-- The post state of a node. -/
noncomputable def post4 [Infinite V] (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) : HSt V D₀ := h.cut4Post v (fresh h) x₁ x₂

/-- The `j`-th node of `h` (in a fixed enumeration of `nodes4 h`). -/
noncomputable def nodeAt4 [Infinite V] (h : HSt V D₀) (j : ℕ) : Option (V × h.s.D × h.s.D) :=
  if hj : j < (nodes4 h).card then some (((nodes4 h).equivFin.symm ⟨j, hj⟩ : nodes4 h) : V × h.s.D × h.s.D) else none

noncomputable def clsAt4 [Infinite V] (L : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (j : ℕ) :
    Set (D₀ → (Fin d → ℤ)) :=
  match nodeAt4 h j with
  | some t => cls4 L w h A t.2.1 t.2.2
  | none => ∅

noncomputable def postAt4 [Infinite V] (h : HSt V D₀) (j : ℕ) : HSt V D₀ :=
  match nodeAt4 h j with
  | some t => post4 h t.1 t.2.1 t.2.2
  | none => h

theorem uStep4_node [Infinite V] {L : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {v : V} {x₁ x₂ : h.s.D}
    (hn : Node4 h v x₁ x₂) : UStep4 L w (fun k => k ∈ cls4 L w h A x₁ x₂) h (post4 h v x₁ x₂) :=
  UStep4.cut h v (fresh h) x₁ x₂ hn.1 hn.2.1 hn.2.2.1 (fun k hk => hk.2) hn.2.2.2

theorem Inv4.mono {M₀ : Molecule V D₀} {Rn : ℕ} {Rch : (D₀ → (Fin d → ℤ)) → HSt V D₀ → Prop} {L : ℝ} {w : Mom d} {A0 A B : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀}
    (hA : Inv4 M₀ Rn Rch L w A0 A h) (hB : B ⊆ A) : Inv4 M₀ Rn Rch L w A0 B h := by
  refine ⟨hB.trans hA.1, ?_⟩
  by_cases hBe : B = ∅
  · exact Or.inl hBe
  · right
    rcases hA.2 with he | ⟨hc, hap, hr⟩
    · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hB)) hBe
    · exact ⟨uctx_mono hc fun k hk => hB hk, hap, fun κ hκ => hr κ (hB hκ)⟩

theorem apPos_cutSt_beta (s : St.{u} V D₀) {v v₂ : V} {x₁ x₂ : s.D} (hs : ApPos s) :
    ApPos (s.cutSt v v₂ x₁ x₂ .beta .beta) := by
  intro a ha R kp hcl
  rw [cutSt_atoms] at ha
  rw [cutSt_cls] at hcl
  by_cases h1 : a = v₂
  · subst h1; simp at hcl
  · by_cases h2 : a = v
    · subst h2; simp [Function.update_of_ne h1] at hcl
    · rw [Function.update_of_ne h1, Function.update_of_ne h2] at hcl
      exact hs a ((Finset.mem_insert.1 ha).resolve_left h1) R kp hcl

end WaveTurbulence.FinalCountAsm

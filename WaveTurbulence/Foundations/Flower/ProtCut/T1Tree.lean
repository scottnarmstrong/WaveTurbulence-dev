/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.MultLeaf

/-! # D2c-2 PROT-CUT: a type-1 couple and its three sub-couples (o104 Prop 7.4 (b))

A couple decoded by `type1 c Q₁ Q₂ Q₃` (T853): the roots `ρ₀ = (0, [])` and `ρ₁ = (1, [])` are linked (T877);
`Q₁` sits at `(0, [0])`, `(1, [c.partner 0])`; `Q₂` at `(1, [1])`, `(0, [1])` (its `+` tree under `ρ₁`); `Q₃` at
`(0, [2])`, `(1, [c.partner 2])` (`RegCpl.pairsAt`).

* address maps `t1A c`, `t1B`, `t1C`, node maps `ιA ιB ιC`, branch maps `βA βB βC`, roots `rt t`;
* `t1Branch`: `Fin 2 ⊕ (A ⊕ (B ⊕ C))` branches `≃` branches of the couple; `prod_t1Branch`, `order_t1`, `zeta_t1`,
  `epsDec_t1`, `phaseProd_t1`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The other tree of a couple. -/
def t1sw (t : Fin 2) : Fin 2 := if t = 0 then 1 else 0

/-- The slot of tree `t` of `Q₁` under its root. -/
def slotA (c : MiniCplCode) (t : Fin 2) : Fin 3 := if t = 0 then 0 else c.partner 0

/-- The slot of tree `t` of `Q₃` under its root. -/
def slotC (c : MiniCplCode) (t : Fin 2) : Fin 3 := if t = 0 then 2 else c.partner 2

/-- Address maps of the three sub-couples. -/
def t1A (c : MiniCplCode) (x : Fin 2 × Path) : Fin 2 × Path := (x.1, slotA c x.1 :: x.2)
def t1B (x : Fin 2 × Path) : Fin 2 × Path := (t1sw x.1, 1 :: x.2)
def t1C (c : MiniCplCode) (x : Fin 2 × Path) : Fin 2 × Path := (x.1, slotC c x.1 :: x.2)

theorem t1A_hom (c : MiniCplCode) : ∀ x q, t1A c (addrExt x q) = addrExt (t1A c x) q := by
  intro x q; simp [t1A, addrExt]
theorem t1B_hom : ∀ x q, t1B (addrExt x q) = addrExt (t1B x) q := by
  intro x q; simp [t1B, addrExt]
theorem t1C_hom (c : MiniCplCode) : ∀ x q, t1C c (addrExt x q) = addrExt (t1C c x) q := by
  intro x q; simp [t1C, addrExt]

theorem t1sw_injective : Function.Injective t1sw := by
  intro a b h; fin_cases a <;> fin_cases b <;> simp_all [t1sw]

theorem t1A_injective (c : MiniCplCode) : Function.Injective (t1A c) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  simp only [t1A, Prod.mk.injEq, List.cons.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  rfl

theorem t1B_injective : Function.Injective t1B := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  simp only [t1B, Prod.mk.injEq, List.cons.injEq, true_and] at h
  rw [t1sw_injective h.1, h.2]

theorem t1C_injective (c : MiniCplCode) : Function.Injective (t1C c) := by
  rintro ⟨a, p⟩ ⟨b, q⟩ h
  simp only [t1C, Prod.mk.injEq, List.cons.injEq] at h
  obtain ⟨rfl, -, rfl⟩ := h
  rfl

theorem t1_hAB (c : MiniCplCode) (t t' : Fin 2) : ¬ (t = t1sw t' ∧ slotA c t = 1) := by
  fin_cases c <;> fin_cases t <;> fin_cases t' <;> decide

theorem t1_hAC (c : MiniCplCode) (t t' : Fin 2) : ¬ (t = t' ∧ slotA c t = slotC c t') := by
  fin_cases c <;> fin_cases t <;> fin_cases t' <;> decide

theorem t1_hBC (c : MiniCplCode) (t t' : Fin 2) : ¬ (t1sw t = t' ∧ (1 : Fin 3) = slotC c t') := by
  fin_cases c <;> fin_cases t <;> fin_cases t' <;> decide

theorem pathSign_cons' (ζ : ℤˣ) (i : Fin 3) (q : Path) : pathSign ζ (i :: q) = pathSign (slotSign ζ i) q := by
  rw [show i :: q = [i] ++ q from rfl, Comb.pathSign_append, pathSign_singleton]

/-- Every slot of every root is the head of one placement. -/
theorem t1_cover (c : MiniCplCode) (t : Fin 2) (i : Fin 3) :
    (∃ t', (t', slotA c t') = (t, i)) ∨ (∃ t', (t1sw t', (1 : Fin 3)) = (t, i)) ∨ (∃ t', (t', slotC c t') = (t, i)) := by
  fin_cases c <;> fin_cases t <;> fin_cases i <;> decide

/-- **A type-1 couple and its three sub-couples.** -/
structure T1Data (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) (G G₁ G₂ G₃ : Garden 2) : Prop where
  dec : (RegCpl.type1 c Q₁ Q₂ Q₃).Decodes G
  dec₁ : Q₁.Decodes G₁
  dec₂ : Q₂.Decodes G₂
  dec₃ : Q₃.Decodes G₃

theorem memT_node (A B C : TTree) (i : Fin 3) (q : Path) : MemT (i :: q) (.node A B C) q (![A, B, C] i) :=
  mem_node3_nodes ![A, B, C] i q

theorem tree_of_decodes {Q : RegCpl} {G' : Garden 2} (hQ : Q.Decodes G') (t : Fin 2) :
    G'.tree t = if t = 0 then Q.trees.1 else Q.trees.2 := by
  fin_cases t
  · exact hQ.2.1
  · exact hQ.2.2.1

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {G G₁ G₂ G₃ : Garden 2} (h : T1Data c Q₁ Q₂ Q₃ G G₁ G₂ G₃)
include h

theorem tree0 : G.tree 0 = .node Q₁.trees.1 Q₂.trees.2 Q₃.trees.1 := h.dec.2.1

theorem tree1 : G.tree 1 = if c = 0 then .node Q₁.trees.2 Q₂.trees.1 Q₃.trees.2
    else .node Q₃.trees.2 Q₂.trees.1 Q₁.trees.2 := h.dec.2.2.1

theorem sig : G.sig = ![1, -1] := h.dec.1.2

theorem memT_A (x : Fin 2 × Path) : MemT (t1A c x).2 (G.tree (t1A c x).1) x.2 (G₁.tree x.1) := by
  obtain ⟨t, q⟩ := x
  rw [tree_of_decodes h.dec₁]
  fin_cases t
  · show MemT (0 :: q) (G.tree 0) q _
    rw [h.tree0]; exact memT_node _ _ _ _ _
  · show MemT (c.partner 0 :: q) (G.tree 1) q _
    rw [h.tree1]
    fin_cases c <;> simp only [MiniCplCode.partner] <;> exact memT_node _ _ _ _ _

theorem memT_B (x : Fin 2 × Path) : MemT (t1B x).2 (G.tree (t1B x).1) x.2 (G₂.tree x.1) := by
  obtain ⟨t, q⟩ := x
  rw [tree_of_decodes h.dec₂]
  fin_cases t
  · show MemT (1 :: q) (G.tree 1) q _
    rw [h.tree1]
    fin_cases c <;> exact memT_node _ _ _ _ _
  · show MemT (1 :: q) (G.tree 0) q _
    rw [h.tree0]; exact memT_node _ _ _ _ _

theorem memT_C (x : Fin 2 × Path) : MemT (t1C c x).2 (G.tree (t1C c x).1) x.2 (G₃.tree x.1) := by
  obtain ⟨t, q⟩ := x
  rw [tree_of_decodes h.dec₃]
  fin_cases t
  · show MemT (2 :: q) (G.tree 0) q _
    rw [h.tree0]; exact memT_node _ _ _ _ _
  · show MemT (c.partner 2 :: q) (G.tree 1) q _
    rw [h.tree1]
    fin_cases c <;> simp only [MiniCplCode.partner] <;> exact memT_node _ _ _ _ _

/-! ### Node and branch maps -/

def ιA (z : GNode G₁.tree) : GNode G.tree := ⟨t1A c z.1, (h.memT_A z.1).1.mpr z.2⟩
def ιB (z : GNode G₂.tree) : GNode G.tree := ⟨t1B z.1, (h.memT_B z.1).1.mpr z.2⟩
def ιC (z : GNode G₃.tree) : GNode G.tree := ⟨t1C c z.1, (h.memT_C z.1).1.mpr z.2⟩

def βA (x : GBranch G₁.tree) : GBranch G.tree := ⟨t1A c x.1, (h.memT_A x.1).2.2.mpr x.2⟩
def βB (x : GBranch G₂.tree) : GBranch G.tree := ⟨t1B x.1, (h.memT_B x.1).2.2.mpr x.2⟩
def βC (x : GBranch G₃.tree) : GBranch G.tree := ⟨t1C c x.1, (h.memT_C x.1).2.2.mpr x.2⟩

theorem root_mem (t : Fin 2) : ([] : Path) ∈ (G.tree t).branching := by
  fin_cases t
  · show [] ∈ (G.tree 0).branching
    rw [h.tree0]; exact (mem_node3_nil ![_, _, _]).2.2
  · show [] ∈ (G.tree 1).branching
    rw [h.tree1]; split_ifs <;> exact (mem_node3_nil ![_, _, _]).2.2

/-- The root of tree `t`. -/
def rt (t : Fin 2) : GBranch G.tree := ⟨(t, []), h.root_mem t⟩

theorem βA_toNode (x : GBranch G₁.tree) : (h.βA x).toNode = h.ιA x.toNode := rfl
theorem βB_toNode (x : GBranch G₂.tree) : (h.βB x).toNode = h.ιB x.toNode := rfl
theorem βC_toNode (x : GBranch G₃.tree) : (h.βC x).toNode = h.ιC x.toNode := rfl

theorem βA_child (x : GBranch G₁.tree) (k : Fin 3) : (h.βA x).child k = h.ιA (x.child k) :=
  Subtype.ext (by simp [βA, ιA, GBranch.child, t1A])
theorem βB_child (x : GBranch G₂.tree) (k : Fin 3) : (h.βB x).child k = h.ιB (x.child k) :=
  Subtype.ext (by simp [βB, ιB, GBranch.child, t1B])
theorem βC_child (x : GBranch G₃.tree) (k : Fin 3) : (h.βC x).child k = h.ιC (x.child k) :=
  Subtype.ext (by simp [βC, ιC, GBranch.child, t1C])

/-! ### The branches -/

/-- **The branches of a type-1 couple**: the two roots and the branches of the three sub-couples. -/
def t1Branch : Fin 2 ⊕ (GBranch G₁.tree ⊕ (GBranch G₂.tree ⊕ GBranch G₃.tree)) → GBranch G.tree
  | .inl t => h.rt t
  | .inr (.inl x) => h.βA x
  | .inr (.inr (.inl x)) => h.βB x
  | .inr (.inr (.inr x)) => h.βC x

theorem t1Branch_injective : Function.Injective h.t1Branch := by
  intro z z' he
  have hv : (h.t1Branch z).1 = (h.t1Branch z').1 := by rw [he]
  rcases z with t | x | x | x <;> rcases z' with t' | x' | x' | x'
  · exact congrArg Sum.inl (Prod.ext_iff.mp hv).1
  · simp [t1Branch, rt, βA, t1A] at hv
  · simp [t1Branch, rt, βB, t1B] at hv
  · simp [t1Branch, rt, βC, t1C] at hv
  · simp [t1Branch, rt, βA, t1A] at hv
  · congr 2
    exact Subtype.ext (t1A_injective c hv)
  · simp only [t1Branch, βA, βB, t1A, t1B, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1, hv.2.1⟩ (t1_hAB c _ _)
  · simp only [t1Branch, βA, βC, t1A, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1, hv.2.1⟩ (t1_hAC c _ _)
  · simp [t1Branch, rt, βB, t1B] at hv
  · simp only [t1Branch, βA, βB, t1A, t1B, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1.symm, hv.2.1.symm⟩ (t1_hAB c _ _)
  · congr 3
    exact Subtype.ext (t1B_injective hv)
  · simp only [t1Branch, βB, βC, t1B, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1, hv.2.1⟩ (t1_hBC c _ _)
  · simp [t1Branch, rt, βC, t1C] at hv
  · simp only [t1Branch, βA, βC, t1A, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1.symm, hv.2.1.symm⟩ (t1_hAC c _ _)
  · simp only [t1Branch, βB, βC, t1B, t1C, Prod.mk.injEq, List.cons.injEq] at hv
    exact absurd ⟨hv.1.symm, hv.2.1.symm⟩ (t1_hBC c _ _)
  · congr 3
    exact Subtype.ext (t1C_injective c hv)

theorem t1Branch_surjective : Function.Surjective h.t1Branch := by
  rintro ⟨⟨t, p⟩, hb⟩
  rcases p with _ | ⟨i, q⟩
  · exact ⟨.inl t, rfl⟩
  rcases t1_cover c t i with ⟨t', ht'⟩ | ⟨t', ht'⟩ | ⟨t', ht'⟩
  · have e : t1A c (t', q) = (t, i :: q) := by
      simp only [t1A]; rw [Prod.mk.injEq] at ht' ⊢; exact ⟨ht'.1, by rw [ht'.2]⟩
    have hq : q ∈ (G₁.tree t').branching := (h.memT_A (t', q)).2.2.mp (by rw [e]; exact hb)
    exact ⟨.inr (.inl ⟨(t', q), hq⟩), Subtype.ext e⟩
  · have e : t1B (t', q) = (t, i :: q) := by
      simp only [t1B]; rw [Prod.mk.injEq] at ht' ⊢; exact ⟨ht'.1, by rw [ht'.2]⟩
    have hq : q ∈ (G₂.tree t').branching := (h.memT_B (t', q)).2.2.mp (by rw [e]; exact hb)
    exact ⟨.inr (.inr (.inl ⟨(t', q), hq⟩)), Subtype.ext e⟩
  · have e : t1C c (t', q) = (t, i :: q) := by
      simp only [t1C]; rw [Prod.mk.injEq] at ht' ⊢; exact ⟨ht'.1, by rw [ht'.2]⟩
    have hq : q ∈ (G₃.tree t').branching := (h.memT_C (t', q)).2.2.mp (by rw [e]; exact hb)
    exact ⟨.inr (.inr (.inr ⟨(t', q), hq⟩)), Subtype.ext e⟩

theorem t1Branch_bijective : Function.Bijective h.t1Branch := ⟨h.t1Branch_injective, h.t1Branch_surjective⟩

/-- **Products over the branches of a type-1 couple.** -/
theorem prod_t1Branch {M : Type*} [CommMonoid M] (f : GBranch G.tree → M) :
    ∏ b, f b = f (h.rt 0) * f (h.rt 1) * ((∏ x, f (h.βA x)) * ((∏ x, f (h.βB x)) * ∏ x, f (h.βC x))) := by
  rw [← (Equiv.ofBijective _ h.t1Branch_bijective).prod_comp]
  simp only [Fintype.prod_sum_type, Equiv.ofBijective_apply, Fin.prod_univ_two]
  rfl

/-! ### Signs, orders, `ζ`, `ε`, phases -/

theorem sign_ιA (z : GNode G₁.tree) : G.sign (h.ιA z) = G₁.sign z := by
  show pathSign (G.sig z.1.1) (slotA c z.1.1 :: z.1.2) = pathSign (G₁.sig z.1.1) z.1.2
  rw [pathSign_cons', h.sig, h.dec₁.1.2]
  congr 1
  obtain ⟨⟨t, q⟩, _⟩ := z
  fin_cases t <;> fin_cases c <;> simp [slotSign, slotA, MiniCplCode.partner]

theorem sign_ιB (z : GNode G₂.tree) : G.sign (h.ιB z) = G₂.sign z := by
  show pathSign (G.sig (t1sw z.1.1)) (1 :: z.1.2) = pathSign (G₂.sig z.1.1) z.1.2
  rw [pathSign_cons', h.sig, h.dec₂.1.2]
  congr 1
  obtain ⟨⟨t, q⟩, _⟩ := z
  fin_cases t <;> simp [slotSign, t1sw]

theorem sign_ιC (z : GNode G₃.tree) : G.sign (h.ιC z) = G₃.sign z := by
  show pathSign (G.sig z.1.1) (slotC c z.1.1 :: z.1.2) = pathSign (G₃.sig z.1.1) z.1.2
  rw [pathSign_cons', h.sig, h.dec₃.1.2]
  congr 1
  obtain ⟨⟨t, q⟩, _⟩ := z
  fin_cases t <;> fin_cases c <;> simp [slotSign, slotC, MiniCplCode.partner]

theorem order_t1 : G.order = G₁.order + G₂.order + G₃.order + 2 := by
  rw [← PairData.card_branch, ← PairData.card_branch, ← PairData.card_branch, ← PairData.card_branch,
    ← Fintype.card_congr (Equiv.ofBijective _ h.t1Branch_bijective)]
  simp only [Fintype.card_sum, Fintype.card_fin]
  ring

theorem sign_rt (t : Fin 2) : G.sign (h.rt t).toNode = G.sig t := by
  show pathSign (G.sig t) [] = _
  simp [pathSign]

theorem zeta_t1 : G.zeta = (Complex.I * ((G.sig 0 : ℤˣ) : ℤ)) * (Complex.I * ((G.sig 1 : ℤˣ) : ℤ)) *
    (G₁.zeta * (G₂.zeta * G₃.zeta)) := by
  unfold Garden.zeta
  rw [h.prod_t1Branch]
  simp only [βA_toNode, βB_toNode, βC_toNode, sign_ιA, sign_ιB, sign_ιC, sign_rt]

theorem epsDec_t1 {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) :
    epsDec G κ = epsCoef (κ ((h.rt 0).child 0)) (κ ((h.rt 0).child 1)) (κ ((h.rt 0).child 2)) *
      epsCoef (κ ((h.rt 1).child 0)) (κ ((h.rt 1).child 1)) (κ ((h.rt 1).child 2)) *
      (epsDec G₁ (κ ∘ h.ιA) * (epsDec G₂ (κ ∘ h.ιB) * epsDec G₃ (κ ∘ h.ιC))) := by
  unfold epsDec
  rw [h.prod_t1Branch]
  simp only [βA_child, βB_child, βC_child, Function.comp_apply]

theorem phaseProd_t1 (L γ δ : ℝ) {d : ℕ} (K : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    phaseProd L γ δ G K τ =
      Complex.exp ((Real.pi * ((G.sig 0 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G K (h.rt 0) * τ (h.rt 0) : ℝ) *
          Complex.I) *
        Complex.exp ((Real.pi * ((G.sig 1 : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G K (h.rt 1) * τ (h.rt 1) : ℝ) *
          Complex.I) *
        (phaseProd L γ δ G₁ (K ∘ h.ιA) (fun x => τ (h.βA x)) *
          (phaseProd L γ δ G₂ (K ∘ h.ιB) (fun x => τ (h.βB x)) *
            phaseProd L γ δ G₃ (K ∘ h.ιC) (fun x => τ (h.βC x)))) := by
  unfold phaseProd
  rw [h.prod_t1Branch]
  simp only [omegaNode, βA_child, βB_child, βC_child, βA_toNode, βB_toNode, βC_toNode, sign_ιA, sign_ιB,
    sign_ιC, sign_rt, Function.comp_apply]

end T1Data

end WaveTurbulence.Flower.ProtCut

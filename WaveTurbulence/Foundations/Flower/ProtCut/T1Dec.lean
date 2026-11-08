/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.T1Trace

/-! # D2c-3 PROT-CUT: decorations of a type-1 couple (o104 Prop 7.4 (b), decoration level)

A decoration of a type-1 couple `type1 c Q₁ Q₂ Q₃` with root values `0` is the same as
* an exceptional triple `y = (y₁, y₂, y₃)`, the values at the roots of the three sub-couples, with
  `y₁ - y₂ + y₃ = 0` (`T1E`: the node relation at either root), and
* decorations with root values `0` of the three sub-couples (the sub-couple values shifted by `y₁`, `y₂`, `y₃`).

`T1Data.decEquiv` is this bijection (`GenDecoration` level); the backward map is the glue `t1Glue`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

theorem t1sw_t1sw (t : Fin 2) : t1sw (t1sw t) = t := by fin_cases t <;> rfl

theorem slotA_ne_one (c : MiniCplCode) (t : Fin 2) : slotA c t ≠ 1 := by
  fin_cases c <;> fin_cases t <;> decide

theorem slotC_ne_one (c : MiniCplCode) (t : Fin 2) : slotC c t ≠ 1 := by
  fin_cases c <;> fin_cases t <;> decide

theorem slotC_ne_slotA (c : MiniCplCode) (t : Fin 2) : slotC c t ≠ slotA c t := by
  fin_cases c <;> fin_cases t <;> decide

/-- Every slot of a root is the head slot of exactly one sub-couple. -/
theorem slot_cases_t1 (c : MiniCplCode) (t : Fin 2) (i : Fin 3) : i = slotA c t ∨ i = 1 ∨ i = slotC c t := by
  fin_cases c <;> fin_cases t <;> fin_cases i <;> decide

theorem t1A_nil (c : MiniCplCode) (t : Fin 2) : t1A c (t, []) = addrExt (t, []) [slotA c t] := rfl
theorem t1B_nil (t : Fin 2) : t1B (t, []) = addrExt (t1sw t, []) [1] := rfl
theorem t1C_nil (c : MiniCplCode) (t : Fin 2) : t1C c (t, []) = addrExt (t, []) [slotC c t] := rfl

/-- **The exceptional data of a type-1 couple**: the values at the roots of the three sub-couples, related by the
node relation at the roots. -/
def T1E (d : ℕ) : Type := {y : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // y.1 - y.2.1 + y.2.2 = 0}

/-- **The glued values of a type-1 couple**: `0` at the roots, the sub-couple values shifted by `y₁`, `y₂`, `y₃`
below them. -/
def t1Glue (c : MiniCplCode) {V : Type*} [AddCommGroup V] (y₁ y₂ y₃ : V) (f₁ f₂ f₃ : Fin 2 × Path → V)
    (x : Fin 2 × Path) : V :=
  match x.2 with
  | [] => 0
  | i :: q => if i = slotA c x.1 then f₁ (x.1, q) + y₁ else if i = 1 then f₂ (t1sw x.1, q) + y₂
      else f₃ (x.1, q) + y₃

section Glue

variable (c : MiniCplCode) {V : Type*} [AddCommGroup V] (y₁ y₂ y₃ : V) (f₁ f₂ f₃ : Fin 2 × Path → V)

theorem t1Glue_nil (t : Fin 2) : t1Glue c y₁ y₂ y₃ f₁ f₂ f₃ (t, []) = 0 := rfl

theorem t1Glue_A (x : Fin 2 × Path) : t1Glue c y₁ y₂ y₃ f₁ f₂ f₃ (t1A c x) = f₁ x + y₁ := by
  obtain ⟨t, q⟩ := x
  show (if slotA c t = slotA c t then f₁ (t, q) + y₁ else _) = _
  rw [if_pos rfl]

theorem t1Glue_B (x : Fin 2 × Path) : t1Glue c y₁ y₂ y₃ f₁ f₂ f₃ (t1B x) = f₂ x + y₂ := by
  obtain ⟨t, q⟩ := x
  show (if (1 : Fin 3) = slotA c (t1sw t) then _ else if (1 : Fin 3) = 1 then f₂ (t1sw (t1sw t), q) + y₂ else _) = _
  rw [if_neg (fun e => slotA_ne_one c _ e.symm), if_pos rfl, t1sw_t1sw]

theorem t1Glue_C (x : Fin 2 × Path) : t1Glue c y₁ y₂ y₃ f₁ f₂ f₃ (t1C c x) = f₃ x + y₃ := by
  obtain ⟨t, q⟩ := x
  show (if slotC c t = slotA c t then _ else if slotC c t = 1 then _ else f₃ (t, q) + y₃) = _
  rw [if_neg (slotC_ne_slotA c t), if_neg (slotC_ne_one c t)]

/-- The node relation of the glue at a root. -/
theorem t1Glue_nodeRel (hrel : y₁ - y₂ + y₃ = 0) (h₁ : ∀ t, f₁ (t, []) = 0) (h₂ : ∀ t, f₂ (t, []) = 0)
    (h₃ : ∀ t, f₃ (t, []) = 0) (t : Fin 2) : NodeRel (t1Glue c y₁ y₂ y₃ f₁ f₂ f₃) (t, []) := by
  unfold NodeRel
  have e0 : ∀ i : Fin 3, t1Glue c y₁ y₂ y₃ f₁ f₂ f₃ (addrExt (t, []) [i]) =
      if i = slotA c t then y₁ else if i = 1 then y₂ else y₃ := by
    intro i
    show (if i = slotA c t then f₁ (t, []) + y₁ else if i = 1 then f₂ (t1sw t, []) + y₂ else f₃ (t, []) + y₃) = _
    rw [h₁, h₂, h₃, zero_add, zero_add, zero_add]
  rw [e0, e0, e0, t1Glue_nil]
  have h31 : y₃ - y₂ + y₁ = 0 := by rw [← hrel]; abel
  fin_cases c <;> fin_cases t <;> simp [slotA, MiniCplCode.partner] <;> first | exact hrel.symm | exact h31.symm

end Glue

namespace T1Data

variable {c : MiniCplCode} {Q₁ Q₂ Q₃ : RegCpl} {G G₁ G₂ G₃ : Garden 2} (h : T1Data c Q₁ Q₂ Q₃ G G₁ G₂ G₃)
include h

theorem ιA_val (z : GNode G₁.tree) : (h.ιA z).1 = t1A c z.1 := rfl
theorem ιB_val (z : GNode G₂.tree) : (h.ιB z).1 = t1B z.1 := rfl
theorem ιC_val (z : GNode G₃.tree) : (h.ιC z).1 = t1C c z.1 := rfl

section Forward

variable {V : Type*} [AddCommGroup V] {κ : GNode G.tree → V} (hκ : IsDecoration G κ)
include hκ

theorem cplDec_A : CplDec (extend κ ∘ t1A c) Q₁ (0, []) (1, []) := by
  refine (cplDec_comp (t1A_hom c) (extend κ) Q₁ _ _).mpr ?_
  have := (cplDec_of_decoration h.dec hκ).2.2.1
  simpa [t1A, slotA, addrExt] using this

theorem cplDec_B : CplDec (extend κ ∘ t1B) Q₂ (0, []) (1, []) := by
  refine (cplDec_comp t1B_hom (extend κ) Q₂ _ _).mpr ?_
  have := (cplDec_of_decoration h.dec hκ).2.2.2.1
  simpa [t1B, t1sw, addrExt] using this

theorem cplDec_C : CplDec (extend κ ∘ t1C c) Q₃ (0, []) (1, []) := by
  refine (cplDec_comp (t1C_hom c) (extend κ) Q₃ _ _).mpr ?_
  have := (cplDec_of_decoration h.dec hκ).2.2.2.2
  simpa [t1C, slotC, addrExt] using this

theorem extA (t : Fin 2) : extend κ (t1A c (t, [])) = extend κ (t1A c (0, [])) := by
  fin_cases t
  · rfl
  · exact (cplDec_root_eq _ _ _ _ (h.cplDec_A hκ)).symm

theorem extB (t : Fin 2) : extend κ (t1B (t, [])) = extend κ (t1B (0, [])) := by
  fin_cases t
  · rfl
  · exact (cplDec_root_eq _ _ _ _ (h.cplDec_B hκ)).symm

theorem extC (t : Fin 2) : extend κ (t1C c (t, [])) = extend κ (t1C c (0, [])) := by
  fin_cases t
  · rfl
  · exact (cplDec_root_eq _ _ _ _ (h.cplDec_C hκ)).symm

/-- The node relation at the root of tree `0`, with root value `0`. -/
theorem rel_of (h0 : extend κ ((0 : Fin 2), []) = 0) :
    extend κ (t1A c (0, [])) - extend κ (t1B (0, [])) + extend κ (t1C c (0, [])) = 0 := by
  have hn := (cplDec_of_decoration h.dec hκ).1
  unfold NodeRel at hn
  have e1 : addrExt ((0 : Fin 2), ([] : Path)) [0] = t1A c (0, []) := rfl
  have e2 : addrExt ((0 : Fin 2), ([] : Path)) [1] = t1B (1, []) := rfl
  have e3 : addrExt ((0 : Fin 2), ([] : Path)) [2] = t1C c (0, []) := rfl
  rw [e1, e2, e3, h.extB hκ 1, h0] at hn
  exact hn.symm

theorem isDec_A : IsDecoration G₁ (fun z => κ (h.ιA z) - extend κ (t1A c (0, []))) := by
  have h2 := (cplDec_add_const (extend κ ∘ t1A c) (-extend κ (t1A c (0, []))) Q₁ _ _).mpr (h.cplDec_A hκ)
  have h3 := isDecoration_of_cplDec h.dec₁ h2
  convert h3 using 1
  funext z
  simp only [Function.comp_apply, sub_eq_add_neg]
  rw [← h.ιA_val, extend_node]

theorem isDec_B : IsDecoration G₂ (fun z => κ (h.ιB z) - extend κ (t1B (0, []))) := by
  have h2 := (cplDec_add_const (extend κ ∘ t1B) (-extend κ (t1B (0, []))) Q₂ _ _).mpr (h.cplDec_B hκ)
  have h3 := isDecoration_of_cplDec h.dec₂ h2
  convert h3 using 1
  funext z
  simp only [Function.comp_apply, sub_eq_add_neg]
  rw [← h.ιB_val, extend_node]

theorem isDec_C : IsDecoration G₃ (fun z => κ (h.ιC z) - extend κ (t1C c (0, []))) := by
  have h2 := (cplDec_add_const (extend κ ∘ t1C c) (-extend κ (t1C c (0, []))) Q₃ _ _).mpr (h.cplDec_C hκ)
  have h3 := isDecoration_of_cplDec h.dec₃ h2
  convert h3 using 1
  funext z
  simp only [Function.comp_apply, sub_eq_add_neg]
  rw [← h.ιC_val, extend_node]

theorem rootA (j : Fin 2) : κ (h.ιA (GNode.root G₁.tree j)) - extend κ (t1A c (0, [])) = 0 := by
  rw [← extend_node κ (h.ιA _)]
  show extend κ (t1A c (j, [])) - _ = 0
  rw [h.extA hκ j]; exact sub_self _

theorem rootB (j : Fin 2) : κ (h.ιB (GNode.root G₂.tree j)) - extend κ (t1B (0, [])) = 0 := by
  rw [← extend_node κ (h.ιB _)]
  show extend κ (t1B (j, [])) - _ = 0
  rw [h.extB hκ j]; exact sub_self _

theorem rootC (j : Fin 2) : κ (h.ιC (GNode.root G₃.tree j)) - extend κ (t1C c (0, [])) = 0 := by
  rw [← extend_node κ (h.ιC _)]
  show extend κ (t1C c (j, [])) - _ = 0
  rw [h.extC hκ j]; exact sub_self _

end Forward

section Backward

variable {V : Type*} [AddCommGroup V] (y₁ y₂ y₃ : V) {κ₁ : GNode G₁.tree → V} {κ₂ : GNode G₂.tree → V}
  {κ₃ : GNode G₃.tree → V}

omit h in
theorem extend_root_zero {T : Fin 2 → TTree} {κ' : GNode T → V} (h0 : ∀ j, κ' (GNode.root T j) = 0) (t : Fin 2) :
    extend κ' (t, []) = 0 := by
  rw [show ((t, []) : Fin 2 × Path) = (GNode.root T t).1 from rfl, extend_node, h0]

/-- **The glued decoration.** -/
theorem glue_isDec (hrel : y₁ - y₂ + y₃ = 0) (hκ₁ : IsDecoration G₁ κ₁) (hκ₂ : IsDecoration G₂ κ₂)
    (hκ₃ : IsDecoration G₃ κ₃) (h₁ : ∀ j, κ₁ (GNode.root G₁.tree j) = 0) (h₂ : ∀ j, κ₂ (GNode.root G₂.tree j) = 0)
    (h₃ : ∀ j, κ₃ (GNode.root G₃.tree j) = 0) :
    IsDecoration G (fun z => t1Glue c y₁ y₂ y₃ (extend κ₁) (extend κ₂) (extend κ₃) z.1) := by
  set F := t1Glue c y₁ y₂ y₃ (extend κ₁) (extend κ₂) (extend κ₃) with hF
  have hN := t1Glue_nodeRel c y₁ y₂ y₃ (extend κ₁) (extend κ₂) (extend κ₃) hrel (extend_root_zero h₁)
    (extend_root_zero h₂) (extend_root_zero h₃)
  refine isDecoration_of_cplDec h.dec ⟨hN 0, hN 1, ?_, ?_, ?_⟩
  · have h1 := (cplDec_add_const (extend κ₁) y₁ Q₁ (0, []) (1, [])).mpr (cplDec_of_decoration h.dec₁ hκ₁)
    have h2 : CplDec (F ∘ t1A c) Q₁ (0, []) (1, []) := by
      convert h1 using 1
      funext x
      exact t1Glue_A c y₁ y₂ y₃ _ _ _ x
    have h3 := (cplDec_comp (t1A_hom c) F Q₁ _ _).mp h2
    simpa [t1A, slotA, addrExt] using h3
  · have h1 := (cplDec_add_const (extend κ₂) y₂ Q₂ (0, []) (1, [])).mpr (cplDec_of_decoration h.dec₂ hκ₂)
    have h2 : CplDec (F ∘ t1B) Q₂ (0, []) (1, []) := by
      convert h1 using 1
      funext x
      exact t1Glue_B c y₁ y₂ y₃ _ _ _ x
    have h3 := (cplDec_comp t1B_hom F Q₂ _ _).mp h2
    simpa [t1B, t1sw, addrExt] using h3
  · have h1 := (cplDec_add_const (extend κ₃) y₃ Q₃ (0, []) (1, [])).mpr (cplDec_of_decoration h.dec₃ hκ₃)
    have h2 : CplDec (F ∘ t1C c) Q₃ (0, []) (1, []) := by
      convert h1 using 1
      funext x
      exact t1Glue_C c y₁ y₂ y₃ _ _ _ x
    have h3 := (cplDec_comp (t1C_hom c) F Q₃ _ _).mp h2
    simpa [t1C, slotC, addrExt] using h3

end Backward

/-! ### The bijection -/

variable (d : ℕ)

theorem ext0 (κ : GenDecoration G d (fun _ => 0) 0) : extend κ.1 ((0 : Fin 2), []) = 0 := by
  rw [show ((0 : Fin 2), ([] : Path)) = (GNode.root G.tree 0).1 from rfl, extend_node]; exact κ.2.2.1 0

/-- **Decorations of a type-1 couple ≃ exceptional data × decorations of the three sub-couples.** -/
def decEquiv : GenDecoration G d (fun _ => 0) 0 ≃
    T1E d × (GenDecoration G₁ d (fun _ => 0) 0 ×
      (GenDecoration G₂ d (fun _ => 0) 0 × GenDecoration G₃ d (fun _ => 0) 0)) where
  toFun κ :=
    (⟨(extend κ.1 (t1A c (0, [])), extend κ.1 (t1B (0, [])), extend κ.1 (t1C c (0, []))),
        h.rel_of κ.2.1 (h.ext0 d κ)⟩,
      ⟨fun z => κ.1 (h.ιA z) - extend κ.1 (t1A c (0, [])), h.isDec_A κ.2.1, h.rootA κ.2.1,
        fun ℓ hℓ => absurd hℓ (not_flower_of_plain h.dec₁.1.1 ℓ)⟩,
      ⟨fun z => κ.1 (h.ιB z) - extend κ.1 (t1B (0, [])), h.isDec_B κ.2.1, h.rootB κ.2.1,
        fun ℓ hℓ => absurd hℓ (not_flower_of_plain h.dec₂.1.1 ℓ)⟩,
      ⟨fun z => κ.1 (h.ιC z) - extend κ.1 (t1C c (0, [])), h.isDec_C κ.2.1, h.rootC κ.2.1,
        fun ℓ hℓ => absurd hℓ (not_flower_of_plain h.dec₃.1.1 ℓ)⟩)
  invFun p :=
    ⟨fun z => t1Glue c p.1.1.1 p.1.1.2.1 p.1.1.2.2 (extend p.2.1.1) (extend p.2.2.1.1) (extend p.2.2.2.1) z.1,
      h.glue_isDec _ _ _ p.1.2 p.2.1.2.1 p.2.2.1.2.1 p.2.2.2.2.1 (PairData.genDec_root d p.2.1)
        (PairData.genDec_root d p.2.2.1) (PairData.genDec_root d p.2.2.2),
      fun j => t1Glue_nil c _ _ _ _ _ _ j,
      fun ℓ hℓ => absurd hℓ (not_flower_of_plain h.plain ℓ)⟩
  left_inv κ := by
    apply Subtype.ext
    funext z
    obtain ⟨⟨t, p⟩, hz⟩ := z
    show t1Glue c _ _ _ _ _ _ (t, p) = κ.1 ⟨(t, p), hz⟩
    rcases p with _ | ⟨i, q⟩
    · rw [t1Glue_nil]; exact (κ.2.2.1 t).symm
    · rcases slot_cases_t1 c t i with rfl | rfl | rfl
      · have hn : q ∈ (G₁.tree t).nodes := (h.memT_A (t, q)).1.mp hz
        refine (t1Glue_A c _ _ _ _ _ _ (t, q)).trans ?_
        refine (congrArg (· + _) (extend_node _ ⟨(t, q), hn⟩)).trans ?_
        exact sub_add_cancel _ _
      · have e0 : t1B (t1sw t, q) = (t, (1 : Fin 3) :: q) := by simp [t1B, t1sw_t1sw]
        have hn : q ∈ (G₂.tree (t1sw t)).nodes := (h.memT_B (t1sw t, q)).1.mp (by rw [e0]; exact hz)
        have e2 := t1Glue_B c (extend κ.1 (t1A c (0, []))) (extend κ.1 (t1B (0, []))) (extend κ.1 (t1C c (0, [])))
          (extend fun z => κ.1 (h.ιA z) - extend κ.1 (t1A c (0, [])))
          (extend fun z => κ.1 (h.ιB z) - extend κ.1 (t1B (0, [])))
          (extend fun z => κ.1 (h.ιC z) - extend κ.1 (t1C c (0, []))) (t1sw t, q)
        rw [e0] at e2
        refine e2.trans ?_
        refine (congrArg (· + _) (extend_node _ ⟨(t1sw t, q), hn⟩)).trans ?_
        refine (sub_add_cancel _ _).trans ?_
        exact congrArg κ.1 (Subtype.ext e0)
      · have hn : q ∈ (G₃.tree t).nodes := (h.memT_C (t, q)).1.mp hz
        refine (t1Glue_C c _ _ _ _ _ _ (t, q)).trans ?_
        refine (congrArg (· + _) (extend_node _ ⟨(t, q), hn⟩)).trans ?_
        exact sub_add_cancel _ _
  right_inv p := by
    obtain ⟨⟨⟨y₁, y₂, y₃⟩, hy⟩, κ₁, κ₂, κ₃⟩ := p
    set F := t1Glue c y₁ y₂ y₃ (extend κ₁.1) (extend κ₂.1) (extend κ₃.1) with hF
    have hA : extend (fun z : GNode G.tree => F z.1) (t1A c (0, [])) = y₁ := by
      rw [PairData.extend_val F (t1A c (0, [])) (h.ιA (GNode.root G₁.tree 0)).2]
      show F (t1A c (0, [])) = y₁
      rw [hF, t1Glue_A, extend_root_zero (PairData.genDec_root d κ₁), zero_add]
    have hB : extend (fun z : GNode G.tree => F z.1) (t1B (0, [])) = y₂ := by
      rw [PairData.extend_val F (t1B (0, [])) (h.ιB (GNode.root G₂.tree 0)).2]
      show F (t1B (0, [])) = y₂
      rw [hF, t1Glue_B, extend_root_zero (PairData.genDec_root d κ₂), zero_add]
    have hC : extend (fun z : GNode G.tree => F z.1) (t1C c (0, [])) = y₃ := by
      rw [PairData.extend_val F (t1C c (0, [])) (h.ιC (GNode.root G₃.tree 0)).2]
      show F (t1C c (0, [])) = y₃
      rw [hF, t1Glue_C, extend_root_zero (PairData.genDec_root d κ₃), zero_add]
    refine Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_)))
    · show (extend (fun z : GNode G.tree => F z.1) (t1A c (0, [])),
        extend (fun z : GNode G.tree => F z.1) (t1B (0, [])),
        extend (fun z : GNode G.tree => F z.1) (t1C c (0, []))) = (y₁, y₂, y₃)
      rw [hA, hB, hC]
    · funext z
      show F (h.ιA z).1 - extend (fun z : GNode G.tree => F z.1) (t1A c (0, [])) = κ₁.1 z
      rw [hA, h.ιA_val, hF, t1Glue_A, add_sub_cancel_right, extend_node]
    · funext z
      show F (h.ιB z).1 - extend (fun z : GNode G.tree => F z.1) (t1B (0, [])) = κ₂.1 z
      rw [hB, h.ιB_val, hF, t1Glue_B, add_sub_cancel_right, extend_node]
    · funext z
      show F (h.ιC z).1 - extend (fun z : GNode G.tree => F z.1) (t1C c (0, [])) = κ₃.1 z
      rw [hC, h.ιC_val, hF, t1Glue_C, add_sub_cancel_right, extend_node]

theorem decEquiv_fst (κ : GenDecoration G d (fun _ => 0) 0) :
    (h.decEquiv d κ).1.1 = (extend κ.1 (t1A c (0, [])), extend κ.1 (t1B (0, [])), extend κ.1 (t1C c (0, []))) :=
  rfl

end T1Data

end WaveTurbulence.Flower.ProtCut

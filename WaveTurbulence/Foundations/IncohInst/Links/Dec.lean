/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.AddressSigns
public import WaveTurbulence.Foundations.RegStruct.ChainAppend

/-!
# Links of branching nodes: decorations along structure codes (packet C2)

A decoration of a decoded regular couple is read along its structure code (B2 draft `RegCpl`,
`RegChain`): `CplDec f Q a b` says that `f` (values at global addresses) satisfies the node relation
`κ_𝔫 = κ_{𝔫₁} - κ_{𝔫₂} + κ_{𝔫₃}` (TARGET Def `defdec`, L639–L648) at every branching node of the
code placed with its `+` tree at `a` and `-` tree at `b`, and equal values on its leaf pairs.

* Conservation (`CplDec.root_eq`, `ChainDec.lone_eq`): the two roots of a couple carry the same value;
  a chain's root carries the value of its lone position.
* **Links** (TARGET Prop `deflink`, L874–L882; DH21 Prop 4.3, L729; FINDINGS F16): for every link
  `(𝔫, 𝔫')` of the code (B2 draft `RegCpl.linksAt`), `{x_{𝔫'}, y_{𝔫'}} = {s₁ x_𝔫, s₂ y_𝔫}` with
  `x = κ_{𝔫₁} - κ_𝔫`, `y = κ_𝔫 - κ_{𝔫₃}`, and `ζ_{𝔫'} = -s₁ s₂ ζ_𝔫` (`linkRel_of_cplDec`). This is the
  case-by-case check of DH21 Figure `BranPair.png` (the two mini-couples and six mini-trees).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- The node relation `κ_𝔫 = κ_{𝔫₁} - κ_{𝔫₂} + κ_{𝔫₃}` at the address `a` (TARGET Def `defdec`). -/
def NodeRel (f : Fin w × Path → V) (a : Fin w × Path) : Prop :=
  f a = f (addrExt a [0]) - f (addrExt a [1]) + f (addrExt a [2])

mutual
/-- `f` decorates the couple code `Q` placed with its `+` tree at `a` and its `-` tree at `b`
(node relations at its branching nodes, equal values on its leaf pairs), in the address layout of
the B2 decoding `RegCpl.pairsAt`. -/
def CplDec (f : Fin w × Path → V) : RegCpl → (Fin w × Path) → (Fin w × Path) → Prop
  | .triv, a, b => f a = f b
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    NodeRel f a ∧ NodeRel f b ∧ CplDec f Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) ∧
      CplDec f Q₂ (addrExt b [1]) (addrExt a [1]) ∧
      CplDec f Q₃ (addrExt a [2]) (addrExt b [c.partner 2])
  | .type2 Xp Xm Qlp, a, b =>
    ChainDec f Xp 1 a ∧ ChainDec f Xm (-1) b ∧
      CplDec f Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- `f` decorates the chain code `X` rooted at `a` with root sign `ζ` (lone position excluded). -/
def ChainDec (f : Fin w × Path → V) : RegChain → ℤˣ → (Fin w × Path) → Prop
  | .nil, _, _ => True
  | .pair m Qr Qg inner rest, ζ, a =>
    NodeRel f a ∧ NodeRel f (addrExt a ([m.c] ++ inner.lonePath)) ∧
      (if slotSign ζ m.red.1 = 1 then
          CplDec f Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
        else CplDec f Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ∧
      (if slotSign ζ m.green.1 = 1 then
          CplDec f Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
        else
          CplDec f Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ∧
      ChainDec f inner (slotSign ζ m.c) (addrExt a [m.c]) ∧
      ChainDec f rest (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
end

/-! ### The mini-tree tables -/

/-- The three slots of the root of a mini-tree: the chain slot, red and green. -/
theorem miniTree_local (m : MiniTreeCode) (fa fb : V) (A B : Fin 3 → V)
    (hA : fa = A 0 - A 1 + A 2) (hB : fb = B 0 - B 1 + B 2) (hc : A m.c = fb)
    (hr : A m.red.1 = B m.red.2) (hg : A m.green.1 = B m.green.2) : fa = B m.lone := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp only [MiniTreeCode.red, MiniTreeCode.green, MiniTreeCode.lone] at hc hr hg ⊢ <;>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one] at hc hr hg ⊢ <;>
    rw [hA, hc, hr, hg, hB] <;> abel

theorem red_ne_c (m : MiniTreeCode) : m.red.1 ≠ m.c := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem green_ne_c (m : MiniTreeCode) : m.green.1 ≠ m.c := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem red_ne_green (m : MiniTreeCode) : m.red.1 ≠ m.green.1 := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem red2_ne_lone (m : MiniTreeCode) : m.red.2 ≠ m.lone := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem green2_ne_lone (m : MiniTreeCode) : m.green.2 ≠ m.lone := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

theorem red2_ne_green2 (m : MiniTreeCode) : m.red.2 ≠ m.green.2 := by
  obtain ⟨c, b⟩ := m; fin_cases c <;> fin_cases b <;> decide

/-! ### Conservation -/

theorem oriented_eq {f : Fin w × Path → V} {Q : RegCpl} {x y : Fin w × Path} {p : Prop}
    [Decidable p] (hQ : ∀ a b, CplDec f Q a b → f a = f b)
    (h : if p then CplDec f Q x y else CplDec f Q y x) : f x = f y := by
  split_ifs at h
  · exact hQ _ _ h
  · exact (hQ _ _ h).symm

mutual
/-- **The two roots of a couple carry the same value.** -/
theorem cplDec_root_eq (f : Fin w × Path → V) (Q : RegCpl) (a b : Fin w × Path)
    (h : CplDec f Q a b) : f a = f b := by
  cases Q with
  | triv => exact h
  | type1 c Q₁ Q₂ Q₃ =>
    obtain ⟨ha, hb, h₁, h₂, h₃⟩ := h
    have e₁ := cplDec_root_eq f Q₁ _ _ h₁
    have e₂ := cplDec_root_eq f Q₂ _ _ h₂
    have e₃ := cplDec_root_eq f Q₃ _ _ h₃
    rw [ha, hb]
    fin_cases c <;> simp only [MiniCplCode.partner] at e₁ e₃ ⊢ <;>
      simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, Fin.mk_one, one_ne_zero] at e₁ e₃ ⊢
    · rw [e₁, e₂, e₃]
    · rw [← e₂]
      have h20 : (2 : Fin 3) - 0 = 2 := rfl
      have h22 : (2 : Fin 3) - 2 = 0 := rfl
      rw [h20] at e₁
      rw [h22] at e₃
      rw [e₁, e₃]
      abel
  | type2 Xp Xm Qlp =>
    obtain ⟨hp, hm, hl⟩ := h
    rw [chainDec_lone_eq f Xp 1 a hp, cplDec_root_eq f Qlp _ _ hl,
      ← chainDec_lone_eq f Xm (-1) b hm]
termination_by structural Q

/-- **A chain's root carries the value of its lone position.** -/
theorem chainDec_lone_eq (f : Fin w × Path → V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (h : ChainDec f X ζ a) : f a = f (addrExt a X.lonePath) := by
  cases X with
  | nil => simp [RegChain.lonePath, addrExt]
  | pair m Qr Qg inner rest =>
    obtain ⟨ha, hb, hr, hg, hi, hs⟩ := h
    have er := oriented_eq (fun x y hh => cplDec_root_eq f Qr x y hh) hr
    have eg := oriented_eq (fun x y hh => cplDec_root_eq f Qg x y hh) hg
    have ei := chainDec_lone_eq f inner _ _ hi
    have es := chainDec_lone_eq f rest _ _ hs
    rw [addrExt_append] at ei
    have key := miniTree_local m (f a) (f (addrExt a ([m.c] ++ inner.lonePath)))
      (fun i => f (addrExt a [i])) (fun i => f (addrExt a ([m.c] ++ inner.lonePath ++ [i])))
      ha (by rw [hb]; simp only [addrExt_append, List.append_assoc]) ei er eg
    rw [key, es, addrExt_append]
    simp only [RegChain.lonePath, List.append_assoc]
termination_by structural X
end

/-! ### The link relation -/

/-- `x_𝔫 = κ_{𝔫₁} - κ_𝔫` (TARGET Prop `deflink`). -/
def xv (f : Fin w × Path → V) (u : Fin w × Path) : V := f (addrExt u [0]) - f u

/-- `y_𝔫 = κ_𝔫 - κ_{𝔫₃}` (TARGET Prop `deflink`). -/
def yv (f : Fin w × Path → V) (u : Fin w × Path) : V := f u - f (addrExt u [2])

/-- The relation of a link `(u, v)` (TARGET Prop `deflink`; FINDINGS F16):
`{x_v, y_v} = {s₁ x_u, s₂ y_u}` and the signs satisfy `ζ_v = -s₁ s₂ ζ_u`. -/
def LinkRel (f : Fin w × Path → V) (σ : Fin w → ℤˣ) (u v : Fin w × Path) : Prop :=
  ∃ s₁ s₂ : ℤˣ,
    ((xv f v = (s₁ : ℤ) • xv f u ∧ yv f v = (s₂ : ℤ) • yv f u) ∨
      (xv f v = (s₁ : ℤ) • yv f u ∧ yv f v = (s₂ : ℤ) • xv f u)) ∧
    nodeSign σ v = -(s₁ * s₂) * nodeSign σ u

/-- The link of a type-1 couple: its two roots. -/
theorem linkRel_type1 (f : Fin w × Path → V) (σ : Fin w → ℤˣ) (c : MiniCplCode)
    (a b : Fin w × Path) (ha : NodeRel f a) (hb : NodeRel f b)
    (e₀ : f (addrExt a [0]) = f (addrExt b [c.partner 0])) (e₁ : f (addrExt b [1]) = f (addrExt a [1]))
    (e₂ : f (addrExt a [2]) = f (addrExt b [c.partner 2]))
    (sa : nodeSign σ a = 1) (sb : nodeSign σ b = -1) : LinkRel f σ a b := by
  unfold NodeRel at ha hb
  fin_cases c <;> simp only [MiniCplCode.partner] at e₀ e₂ <;>
    simp only [Fin.isValue, Fin.zero_eta, ↓reduceIte, Fin.mk_one, one_ne_zero] at e₀ e₂
  · refine ⟨1, 1, Or.inl ⟨?_, ?_⟩, by rw [sa, sb]; decide⟩ <;> simp only [xv, yv, Units.val_one,
      one_smul] <;> rw [hb, ← e₀, e₁, ← e₂, ha]
  · have h20 : (2 : Fin 3) - 0 = 2 := rfl
    have h22 : (2 : Fin 3) - 2 = 0 := rfl
    rw [h20] at e₀
    rw [h22] at e₂
    refine ⟨-1, -1, Or.inr ⟨?_, ?_⟩, by rw [sa, sb]; decide⟩ <;>
      simp only [xv, yv, Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hb, ← e₀, e₁, ← e₂, ha] <;> abel

/-- The link `(𝔫_a, 𝔫_b)` of a chain pair (the six mini-trees). -/
theorem linkRel_miniTree (m : MiniTreeCode) (fa fb : V) (A B : Fin 3 → V)
    (hA : fa = A 0 - A 1 + A 2) (hB : fb = B 0 - B 1 + B 2) (hc : A m.c = fb)
    (hr : A m.red.1 = B m.red.2) (hg : A m.green.1 = B m.green.2) :
    ∃ s₁ s₂ : ℤˣ, ((B 0 - fb = (s₁ : ℤ) • (A 0 - fa) ∧ fb - B 2 = (s₂ : ℤ) • (fa - A 2)) ∨
      (B 0 - fb = (s₁ : ℤ) • (fa - A 2) ∧ fb - B 2 = (s₂ : ℤ) • (A 0 - fa))) ∧
      (if m.c = 1 then s₁ * s₂ = 1 else s₁ * s₂ = -1) := by
  obtain ⟨c, b⟩ := m
  fin_cases c <;> fin_cases b <;>
    simp only [MiniTreeCode.red, MiniTreeCode.green, MiniTreeCode.lone] at hc hr hg ⊢ <;>
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.vecHead, Matrix.vecTail,
      Function.comp_apply, Fin.succ_zero_eq_one] at hc hr hg ⊢
  · refine ⟨-1, 1, Or.inl ⟨?_, ?_⟩, by decide⟩ <;>
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hA, hc, hr, hg, hB] <;> abel
  · refine ⟨-1, 1, Or.inr ⟨?_, ?_⟩, by decide⟩ <;>
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hA, hc, hr, hg, hB] <;> abel
  · refine ⟨1, 1, Or.inr ⟨?_, ?_⟩, by decide⟩ <;>
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hA, hc, hr, hg, hB] <;> abel
  · refine ⟨-1, -1, Or.inl ⟨?_, ?_⟩, by decide⟩ <;>
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hA, hc, hr, hg, hB] <;> abel
  · refine ⟨1, -1, Or.inl ⟨?_, ?_⟩, by decide⟩ <;>
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hA, hc, hr, hg, hB] <;> abel
  · refine ⟨1, -1, Or.inr ⟨?_, ?_⟩, by decide⟩ <;>
      simp only [Units.val_neg, Units.val_one, neg_smul, one_smul] <;>
      rw [hA, hc, hr, hg, hB] <;> abel

/-- The second node `𝔫_b` of a chain pair has the sign of the slot `c` under `𝔫_a`. -/
theorem nodeSign_nb (σ : Fin w → ℤˣ) (a : Fin w × Path) (c : Fin 3) (X : RegChain) :
    nodeSign σ (addrExt a ([c] ++ X.lonePath)) = slotSign (nodeSign σ a) c := by
  rw [nodeSign_addrExt, Comb.pathSign_append, pathSign_singleton, lonePath_sign]

/-- The link `(𝔫_a, 𝔫_b)` of a chain pair satisfies the link relation. -/
theorem linkRel_chain (f : Fin w × Path → V) (σ : Fin w → ℤˣ) (m : MiniTreeCode)
    (inner : RegChain) (a : Fin w × Path)
    (ha : NodeRel f a) (hb : NodeRel f (addrExt a ([m.c] ++ inner.lonePath)))
    (hc : f (addrExt a [m.c]) = f (addrExt a ([m.c] ++ inner.lonePath)))
    (hr : f (addrExt a [m.red.1]) = f (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])))
    (hg : f (addrExt a [m.green.1]) = f (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))) :
    LinkRel f σ a (addrExt a ([m.c] ++ inner.lonePath)) := by
  have hb' : f (addrExt a ([m.c] ++ inner.lonePath)) =
      f (addrExt a ([m.c] ++ inner.lonePath ++ [0])) -
        f (addrExt a ([m.c] ++ inner.lonePath ++ [1])) +
        f (addrExt a ([m.c] ++ inner.lonePath ++ [2])) := by
    rw [hb]; simp only [NodeRel, addrExt_append]
  obtain ⟨s₁, s₂, hx, hs⟩ := linkRel_miniTree m (f a) (f (addrExt a ([m.c] ++ inner.lonePath)))
    (fun i => f (addrExt a [i])) (fun i => f (addrExt a ([m.c] ++ inner.lonePath ++ [i])))
    ha hb' hc hr hg
  refine ⟨s₁, s₂, ?_, ?_⟩
  · simp only [xv, yv, addrExt_append]
    exact hx
  · rw [nodeSign_nb]
    rcases Int.units_eq_one_or (nodeSign σ a) with h | h <;> rw [h] <;>
      obtain ⟨c, b⟩ := m <;> fin_cases c <;> simp only [slotSign] at hs ⊢ <;>
      simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, ↓reduceIte,
        zero_ne_one, Fin.reduceEq] at hs ⊢ <;>
      rw [hs] <;> decide

theorem slotSign_eq_neg_one {ζ : ℤˣ} {i : Fin 3} (h : ¬ slotSign ζ i = 1) : slotSign ζ i = -1 :=
  (Int.units_eq_one_or _).resolve_left h

mutual
/-- **Every link of a decorated couple code satisfies the link relation** (TARGET Prop `deflink`). -/
theorem linkRel_of_cplDec (f : Fin w × Path → V) (σ : Fin w → ℤˣ) (Q : RegCpl)
    (a b : Fin w × Path) (h : CplDec f Q a b) (sa : nodeSign σ a = 1) (sb : nodeSign σ b = -1) :
    ∀ l ∈ Q.linksAt a b, LinkRel f σ l.1 l.2 := by
  cases Q with
  | triv => simp [RegCpl.linksAt]
  | type1 c Q₁ Q₂ Q₃ =>
    obtain ⟨ha, hb, h₁, h₂, h₃⟩ := h
    intro l hl
    simp only [RegCpl.linksAt, List.mem_cons, List.mem_append] at hl
    rcases hl with rfl | ((hl | hl) | hl)
    · exact linkRel_type1 f σ c a b ha hb (cplDec_root_eq f Q₁ _ _ h₁)
        (cplDec_root_eq f Q₂ _ _ h₂) (cplDec_root_eq f Q₃ _ _ h₃) sa sb
    · refine linkRel_of_cplDec f σ Q₁ _ _ h₁ ?_ ?_ l hl
      · rw [nodeSign_step, sa]; decide
      · rw [nodeSign_step, sb]; fin_cases c <;> decide
    · refine linkRel_of_cplDec f σ Q₂ _ _ h₂ ?_ ?_ l hl
      · rw [nodeSign_step, sb]; decide
      · rw [nodeSign_step, sa]; decide
    · refine linkRel_of_cplDec f σ Q₃ _ _ h₃ ?_ ?_ l hl
      · rw [nodeSign_step, sa]; decide
      · rw [nodeSign_step, sb]; fin_cases c <;> decide
  | type2 Xp Xm Qlp =>
    obtain ⟨hp, hm, hl'⟩ := h
    intro l hl
    simp only [RegCpl.linksAt, List.mem_append] at hl
    rcases hl with (hl | hl) | hl
    · exact linkRel_of_chainDec f σ Xp 1 a hp sa l hl
    · exact linkRel_of_chainDec f σ Xm (-1) b hm sb l hl
    · refine linkRel_of_cplDec f σ Qlp _ _ hl' ?_ ?_ l hl
      · rw [nodeSign_spine, sa]
      · rw [nodeSign_spine, sb]
termination_by structural Q

/-- Every link of a decorated chain code satisfies the link relation. -/
theorem linkRel_of_chainDec (f : Fin w × Path → V) (σ : Fin w → ℤˣ) (X : RegChain) (ζ : ℤˣ)
    (a : Fin w × Path) (h : ChainDec f X ζ a) (sa : nodeSign σ a = ζ) :
    ∀ l ∈ X.linksAt ζ a, LinkRel f σ l.1 l.2 := by
  cases X with
  | nil => simp [RegChain.linksAt]
  | pair m Qr Qg inner rest =>
    obtain ⟨ha, hb, hr, hg, hi, hs⟩ := h
    intro l hl
    simp only [RegChain.linksAt, List.mem_cons, List.mem_append] at hl
    rcases hl with rfl | (((hl | hl) | hl) | hl)
    · have er := oriented_eq (fun x y hh => cplDec_root_eq f Qr x y hh) hr
      have eg := oriented_eq (fun x y hh => cplDec_root_eq f Qg x y hh) hg
      have ei := chainDec_lone_eq f inner _ _ hi
      rw [addrExt_append] at ei
      exact linkRel_chain f σ m inner a ha hb ei er eg
    · by_cases hsr : slotSign ζ m.red.1 = 1
      · simp only [hsr, ↓reduceIte] at hr hl
        refine linkRel_of_cplDec f σ Qr _ _ hr ?_ ?_ l hl
        · rw [nodeSign_step, sa, hsr]
        · rw [nodeSign_chain_child, sa, slotSign_red, hsr]
      · simp only [hsr, ↓reduceIte] at hr hl
        refine linkRel_of_cplDec f σ Qr _ _ hr ?_ ?_ l hl
        · rw [nodeSign_chain_child, sa, slotSign_red, slotSign_eq_neg_one hsr, neg_neg]
        · rw [nodeSign_step, sa, slotSign_eq_neg_one hsr]
    · by_cases hsg : slotSign ζ m.green.1 = 1
      · simp only [hsg, ↓reduceIte] at hg hl
        refine linkRel_of_cplDec f σ Qg _ _ hg ?_ ?_ l hl
        · rw [nodeSign_step, sa, hsg]
        · rw [nodeSign_chain_child, sa, slotSign_green, hsg]
      · simp only [hsg, ↓reduceIte] at hg hl
        refine linkRel_of_cplDec f σ Qg _ _ hg ?_ ?_ l hl
        · rw [nodeSign_chain_child, sa, slotSign_green, slotSign_eq_neg_one hsg, neg_neg]
        · rw [nodeSign_step, sa, slotSign_eq_neg_one hsg]
    · exact linkRel_of_chainDec f σ inner _ _ hi (by rw [nodeSign_step, sa]) l hl
    · exact linkRel_of_chainDec f σ rest _ _ hs (by rw [nodeSign_chain_child, sa]) l hl
termination_by structural X
end

end WaveTurbulence.Links

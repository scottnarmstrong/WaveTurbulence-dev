/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.IncohInst.Links.Dec

/-!
# Locality of code decorations (packet C2)

`Under a z`: the address `z` lies in the subtree at `a`. `CplDec f Q a b` only reads `f` below `a`
and `b` (`cplDec_congr`); `ChainDec f X ζ a` only reads `f` below `a` and not strictly below the
lone position (`chainDec_congr`).
-/

@[expose] public section

namespace WaveTurbulence.Links

open TTree WaveTurbulence.Reg

variable {V : Type*} [AddCommGroup V] {w : ℕ}

/-- `z` lies in the subtree at `a` (`z = a` allowed). -/
def Under (a z : Fin w × Path) : Prop := a.1 = z.1 ∧ a.2 <+: z.2

instance (a z : Fin w × Path) : Decidable (Under a z) := inferInstanceAs (Decidable (_ ∧ _))

/-- `z` lies strictly below `a`. -/
def SUnder (a z : Fin w × Path) : Prop := Under a z ∧ z ≠ a

theorem under_refl (a : Fin w × Path) : Under a a := ⟨rfl, List.prefix_refl _⟩

theorem under_ext (a : Fin w × Path) (p : Path) : Under a (addrExt a p) :=
  ⟨rfl, List.prefix_append _ _⟩

theorem under_trans {a b c : Fin w × Path} (h₁ : Under a b) (h₂ : Under b c) : Under a c :=
  ⟨h₁.1.trans h₂.1, h₁.2.trans h₂.2⟩

theorem under_ext_iff (a : Fin w × Path) (p q : Path) :
    Under (addrExt a p) (addrExt a q) ↔ p <+: q := by
  simp only [Under, addrExt, true_and, List.prefix_append_right_inj]

/-- Two subtrees containing a common address are nested. -/
theorem under_total {x y z : Fin w × Path} (hx : Under x z) (hy : Under y z) :
    Under x y ∨ Under y x := by
  rcases le_total x.2.length y.2.length with h | h
  · exact Or.inl ⟨hx.1.trans hy.1.symm, List.prefix_of_prefix_length_le hx.2 hy.2 h⟩
  · exact Or.inr ⟨hy.1.trans hx.1.symm, List.prefix_of_prefix_length_le hy.2 hx.2 h⟩

theorem under_length {x z : Fin w × Path} (h : Under x z) : x.2.length ≤ z.2.length :=
  h.2.length_le

theorem eq_of_under_of_length {x z : Fin w × Path} (h : Under x z)
    (hl : z.2.length ≤ x.2.length) : z = x := by
  obtain ⟨h1, h2⟩ := h
  have := h2.eq_of_length (le_antisymm h2.length_le hl)
  exact Prod.ext h1.symm this.symm

/-- Subtrees at different children of the same node are disjoint. -/
theorem not_under_both {a z : Fin w × Path} {i j : Fin 3} (hij : i ≠ j) (p q : Path)
    (h₁ : Under (addrExt a (i :: p)) z) (h₂ : Under (addrExt a (j :: q)) z) : False := by
  rcases under_total h₁ h₂ with h | h
  · rw [under_ext_iff] at h
    exact hij (List.cons_prefix_cons.mp h).1
  · rw [under_ext_iff] at h
    exact hij (List.cons_prefix_cons.mp h).1.symm

theorem addrExt_cons_ne (a : Fin w × Path) (i : Fin 3) (p : Path) : addrExt a (i :: p) ≠ a := by
  intro h
  have := congrArg (fun x => x.2.length) h
  simp [addrExt] at this

theorem sunder_length {p z : Fin w × Path} (h : SUnder p z) : p.2.length < z.2.length := by
  rcases Nat.lt_or_ge p.2.length z.2.length with hl | hl
  · exact hl
  · exact absurd (eq_of_under_of_length h.1 hl) h.2

theorem not_sunder_of_length {p z : Fin w × Path} (hl : z.2.length ≤ p.2.length) :
    ¬ SUnder p z := fun h => by have := sunder_length h; omega

/-- Subtrees branching at different steps after a common path are disjoint. -/
theorem not_under_branch {a z : Fin w × Path} (p : Path) {i j : Fin 3} (hij : i ≠ j) (s t : Path)
    (h₁ : Under (addrExt a (p ++ i :: s)) z) (h₂ : Under (addrExt a (p ++ j :: t)) z) : False := by
  rcases under_total h₁ h₂ with h | h <;> rw [under_ext_iff, List.prefix_append_right_inj] at h
  · exact hij (List.cons_prefix_cons.mp h).1
  · exact hij (List.cons_prefix_cons.mp h).1.symm

theorem sunder_of_sunder_ext {p z : Fin w × Path} (q : Path) (h : SUnder (addrExt p q) z) :
    SUnder p z :=
  ⟨under_trans (under_ext p q) h.1, fun e => by
    have := sunder_length h
    subst e
    simp only [addrExt, List.length_append] at this
    omega⟩

/-! ### Locality -/

theorem nodeRel_congr {f g : Fin w × Path → V} {x : Fin w × Path} (hx : NodeRel f x)
    (hz : ∀ z, z = x ∨ z = addrExt x [0] ∨ z = addrExt x [1] ∨ z = addrExt x [2] → f z = g z) :
    NodeRel g x := by
  unfold NodeRel at *
  rw [← hz x (Or.inl rfl), ← hz _ (Or.inr (Or.inl rfl)), ← hz _ (Or.inr (Or.inr (Or.inl rfl))),
    ← hz _ (Or.inr (Or.inr (Or.inr rfl)))]
  exact hx

theorem oriented_congr {f g : Fin w × Path → V} {Q : RegCpl} {x y : Fin w × Path} {p : Prop}
    [Decidable p]
    (hQ : ∀ a b, CplDec f Q a b → (∀ z, Under a z ∨ Under b z → f z = g z) → CplDec g Q a b)
    (h : if p then CplDec f Q x y else CplDec f Q y x)
    (hfg : ∀ z, Under x z ∨ Under y z → f z = g z) :
    if p then CplDec g Q x y else CplDec g Q y x := by
  split_ifs at h ⊢
  · exact hQ _ _ h hfg
  · exact hQ _ _ h fun z hz => hfg z hz.symm

mutual
/-- `CplDec f Q a b` only reads `f` below `a` and `b`. -/
theorem cplDec_congr (f g : Fin w × Path → V) (Q : RegCpl) (a b : Fin w × Path)
    (h : CplDec f Q a b) (hfg : ∀ z, Under a z ∨ Under b z → f z = g z) : CplDec g Q a b := by
  cases Q with
  | triv => exact (hfg a (Or.inl (under_refl a))).symm.trans (h.trans (hfg b (Or.inr (under_refl b))))
  | type1 c Q₁ Q₂ Q₃ =>
    obtain ⟨ha, hb, h₁, h₂, h₃⟩ := h
    have hu : ∀ x : Fin w × Path, ∀ z, z = x ∨ z = addrExt x [0] ∨ z = addrExt x [1] ∨
        z = addrExt x [2] → Under x z := fun x z hz => by
      rcases hz with rfl | rfl | rfl | rfl
      exacts [under_refl _, under_ext _ _, under_ext _ _, under_ext _ _]
    refine ⟨nodeRel_congr ha fun z hz => hfg z (Or.inl (hu a z hz)),
      nodeRel_congr hb fun z hz => hfg z (Or.inr (hu b z hz)), ?_, ?_, ?_⟩
    · exact cplDec_congr f g Q₁ _ _ h₁ fun z hz => hfg z (hz.imp
        (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))
    · exact cplDec_congr f g Q₂ _ _ h₂ fun z hz => hfg z (hz.symm.imp
        (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))
    · exact cplDec_congr f g Q₃ _ _ h₃ fun z hz => hfg z (hz.imp
        (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))
  | type2 Xp Xm Qlp =>
    obtain ⟨hp, hm, hl⟩ := h
    refine ⟨chainDec_congr f g Xp 1 a hp fun z hz _ => hfg z (Or.inl hz),
      chainDec_congr f g Xm (-1) b hm fun z hz _ => hfg z (Or.inr hz), ?_⟩
    exact cplDec_congr f g Qlp _ _ hl fun z hz => hfg z (hz.imp
      (under_trans (under_ext _ _)) (under_trans (under_ext _ _)))
termination_by structural Q

/-- `ChainDec f X ζ a` only reads `f` below `a` and not strictly below the lone position. -/
theorem chainDec_congr (f g : Fin w × Path → V) (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path)
    (h : ChainDec f X ζ a)
    (hfg : ∀ z, Under a z → ¬ SUnder (addrExt a X.lonePath) z → f z = g z) :
    ChainDec g X ζ a := by
  cases X with
  | nil => trivial
  | pair m Qr Qg inner rest =>
    obtain ⟨ha, hb, hr, hg, hi, hs⟩ := h
    have hlp : (RegChain.pair m Qr Qg inner rest).lonePath =
        m.c :: (inner.lonePath ++ m.lone :: rest.lonePath) := by
      simp [RegChain.lonePath]
    rw [hlp] at hfg
    have hlenlp : (addrExt a (m.c :: (inner.lonePath ++ m.lone :: rest.lonePath))).2.length =
        a.2.length + inner.lonePath.length + rest.lonePath.length + 2 := by
      simp [addrExt]; omega
    have hshort : ∀ z, Under a z →
        z.2.length ≤ a.2.length + inner.lonePath.length + 2 → f z = g z := fun z hz hl =>
      hfg z hz (not_sunder_of_length (by rw [hlenlp]; omega))
    have eA : addrExt a (m.c :: (inner.lonePath ++ m.lone :: rest.lonePath)) =
        addrExt (addrExt (addrExt a [m.c]) inner.lonePath) (m.lone :: rest.lonePath) := by
      simp [addrExt_append]
    have eB : addrExt (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) rest.lonePath =
        addrExt a (m.c :: (inner.lonePath ++ m.lone :: rest.lonePath)) := by
      simp [addrExt_append]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine nodeRel_congr ha fun z hz => hshort z ?_ ?_
      · rcases hz with rfl | rfl | rfl | rfl
        exacts [under_refl _, under_ext _ _, under_ext _ _, under_ext _ _]
      · rcases hz with rfl | rfl | rfl | rfl <;>
          (try simp only [addrExt, List.length_append, List.length_cons, List.length_nil]) <;> omega
    · refine nodeRel_congr hb fun z hz => hshort z ?_ ?_
      · rcases hz with rfl | rfl | rfl | rfl
        · exact under_ext _ _
        all_goals rw [addrExt_append]; exact under_ext _ _
      · rcases hz with rfl | rfl | rfl | rfl <;>
          (try simp only [addrExt, List.length_append, List.length_cons, List.length_nil]) <;> omega
    · refine oriented_congr (fun x y hh hh' => cplDec_congr f g Qr x y hh hh') hr fun z hz => ?_
      have hz' : Under (addrExt a [m.red.1]) z ∨
          Under (addrExt a (m.c :: (inner.lonePath ++ [m.red.2]))) z := by
        simpa using hz
      refine hfg z ?_ ?_
      · rcases hz' with hz' | hz' <;> exact under_trans (under_ext _ _) hz'
      · intro hsu
        rcases hz' with hz' | hz'
        · exact not_under_branch [] (red_ne_c m) [] _ (by simpa using hz') (by simpa using hsu.1)
        · exact not_under_branch (m.c :: inner.lonePath) (red2_ne_lone m) [] rest.lonePath
            (by simpa using hz') (by simpa using hsu.1)
    · refine oriented_congr (fun x y hh hh' => cplDec_congr f g Qg x y hh hh') hg fun z hz => ?_
      have hz' : Under (addrExt a [m.green.1]) z ∨
          Under (addrExt a (m.c :: (inner.lonePath ++ [m.green.2]))) z := by
        simpa using hz
      refine hfg z ?_ ?_
      · rcases hz' with hz' | hz' <;> exact under_trans (under_ext _ _) hz'
      · intro hsu
        rcases hz' with hz' | hz'
        · exact not_under_branch [] (green_ne_c m) [] _ (by simpa using hz') (by simpa using hsu.1)
        · exact not_under_branch (m.c :: inner.lonePath) (green2_ne_lone m) [] rest.lonePath
            (by simpa using hz') (by simpa using hsu.1)
    · refine chainDec_congr f g inner _ _ hi fun z hz hn => hfg z (under_trans (under_ext _ _) hz) ?_
      intro hsu
      rw [eA] at hsu
      exact hn (sunder_of_sunder_ext _ hsu)
    · refine chainDec_congr f g rest _ _ hs fun z hz hn => hfg z ?_ ?_
      · exact under_trans (under_ext _ _) hz
      · rwa [eB] at hn
termination_by structural X
end

end WaveTurbulence.Links

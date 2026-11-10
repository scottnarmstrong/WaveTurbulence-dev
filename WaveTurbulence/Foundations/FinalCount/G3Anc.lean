/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3N12
public import WaveTurbulence.Foundations.FinalCount.G3RelRun
/-! **FINALCOUNT-G3: the ancestor map** `anc : V → V` of an `HSt` (E10): every atom of the current molecule has an
ancestor atom of `M_sub` (a cut half maps to the atom it was cut from, `ε`-atoms map to themselves), and the atom of a
dart of `M_sub` is the ancestor of the atom of the corresponding current dart. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- The ancestor relation. -/
structure AncRel (M₀ : Molecule V D₀) (s : St.{u} V D₀) (a : V → V) : Prop where
  atom : ∀ x, M₀.atom (s.down x) = a (s.M.atom x)
  mem : ∀ b ∈ s.M.atoms, a b ∈ M₀.atoms
  eps : ∀ b ∈ s.M.atoms, s.cls b = .eps → a b = b
  /-- an `ε`-atom is the only current atom with its ancestor -/
  uniq : ∀ c ∈ s.M.atoms, ∀ b ∈ s.M.atoms, s.cls b = .eps → a c = b → c = b
  inj : Function.Injective s.down
  /-- all darts of `M_sub` at an `ε`-atom are still present -/
  surj : ∀ b ∈ s.M.atoms, s.cls b = .eps → ∀ z, M₀.atom z = b → ∃ x, s.down x = z

theorem AncRel.init (M₀ : Molecule V D₀) : AncRel M₀ (St.init M₀) id :=
  ⟨fun _ => rfl, fun _ h => h, fun _ _ _ => rfl, fun _ _ _ _ _ h => h, fun _ _ h => h, fun _ _ _ z _ => ⟨z, rfl⟩⟩

variable {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V}

theorem AncRel.cutSt (h : AncRel M₀ s a) (v v₂ : V) (x₁ x₂ : s.D) (c₁ c₂ : Cls) (h₁ : c₁ ≠ .eps) (h₂ : c₂ ≠ .eps)
    (hcd : s.M.IsCutData v v₂ x₁ x₂) (a' : V → V) (ha' : ∀ b, a' b = if b = v₂ then a v else a b) :
    AncRel M₀ (s.cutSt v v₂ x₁ x₂ c₁ c₂) a' := by
  have hv₂ : v₂ ∉ s.M.atoms := hcd.2.1
  have hvm : v ∈ s.M.atoms := hcd.1
  have hne' : v₂ ≠ v := fun e => hv₂ (e ▸ hvm)
  have hE : ∀ b, b ∈ (s.cutSt v v₂ x₁ x₂ c₁ c₂).M.atoms → (s.cutSt v v₂ x₁ x₂ c₁ c₂).cls b = .eps →
      b ≠ v₂ ∧ b ≠ v ∧ b ∈ s.M.atoms ∧ s.cls b = .eps := by
    intro b hb hcl
    have hb' : b ∈ insert v₂ s.M.atoms := hb
    have e2 : b ≠ v₂ := by
      intro e; rw [e, cutSt_cls_v₂ c₁ c₂] at hcl; exact h₂ hcl
    have e1 : b ≠ v := by
      intro e; subst e; rw [cutSt_cls_v c₁ c₂ hne'] at hcl; exact h₁ hcl
    rw [cutSt_cls_other c₁ c₂ e1 e2] at hcl
    exact ⟨e2, e1, (Finset.mem_insert.1 hb').resolve_left e2, hcl⟩
  refine ⟨?_, ?_, ?_, ?_, h.inj, ?_⟩
  · intro x
    show M₀.atom (s.down x) = a' ((s.M.cut v v₂ x₁ x₂).atom x)
    rw [cut_atom s.M v v₂ x₁ x₂ x]
    split_ifs with hm
    · rw [ha', if_pos rfl, ← hm.1]; exact h.atom x
    · have hne : s.M.atom x ≠ v₂ := fun e' => hv₂ (e' ▸ s.M.atom_mem x)
      rw [ha', if_neg hne]; exact h.atom x
  · intro b hb
    have hb' : b ∈ insert v₂ s.M.atoms := hb
    rw [ha']
    split_ifs with hb2
    · exact h.mem v hvm
    · exact h.mem b ((Finset.mem_insert.1 hb').resolve_left hb2)
  · intro b hb hcl
    obtain ⟨e2, e1, hbm, hcl'⟩ := hE b hb hcl
    rw [ha', if_neg e2]
    exact h.eps b hbm hcl'
  · intro c hc b hb hcl hcb
    obtain ⟨e2, e1, hbm, hcl'⟩ := hE b hb hcl
    by_cases hc2 : c = v₂
    · subst hc2
      rw [ha', if_pos rfl] at hcb
      exact absurd (h.uniq v hvm b hbm hcl' hcb) (Ne.symm e1)
    · rw [ha', if_neg hc2] at hcb
      exact h.uniq c ((Finset.mem_insert.1 hc).resolve_left hc2) b hbm hcl' hcb
  · intro b hb hcl z hz
    obtain ⟨e2, e1, hbm, hcl'⟩ := hE b hb hcl
    exact h.surj b hbm hcl' z hz

theorem AncRel.delSt (h : AncRel M₀ s a) (P : V → Prop) [DecidablePred P] (hP : PClosed s.M P) :
    AncRel M₀ (s.delSt P hP) a :=
  ⟨fun x => h.atom x.1, fun b hb => h.mem b (Finset.mem_filter.1 hb).1,
    fun b hb hc => h.eps b (Finset.mem_filter.1 hb).1 hc,
    fun c hc b hb hcl hcb => h.uniq c (Finset.mem_filter.1 hc).1 b (Finset.mem_filter.1 hb).1 hcl hcb,
    fun x y e => Subtype.ext (h.inj e),
    fun b hb hcl z hz => by
      have hb' := Finset.mem_filter.1 hb
      obtain ⟨x, hx⟩ := h.surj b hb'.1 hcl z hz
      have hax : s.M.atom x = b := h.uniq _ (s.M.atom_mem x) b hb'.1 hcl (by rw [← h.atom x, hx, hz])
      exact ⟨⟨x, by rw [hax]; exact hb'.2⟩, hx⟩⟩

theorem AncRel.withCls (h : AncRel M₀ s a) (c : V → Cls) (hc : ∀ b ∈ s.M.atoms, (c b = .eps ↔ s.cls b = .eps)) :
    AncRel M₀ (s.withCls c) a :=
  let hc' := hc
  ⟨h.atom, h.mem, fun b hb h' => h.eps b hb ((hc b hb).1 h'),
    fun c hc b hb hcl hcb => h.uniq c hc b hb ((hc' b hb).1 hcl) hcb, h.inj,
    fun b hb hcl z hz => h.surj b hb ((hc' b hb).1 hcl) z hz⟩

theorem HStep1.anc {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStep1 L γ η w κ h h') (hr : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | vine K R' kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents h.s.M.numComponents R' kp
    have hce := Cls.ne_eps_of_isAB hab
    have h1 := hr.cutSt K.C.upper K.fa K.x₁ K.x₂ _ _ hce hce K.cut_a
      (Function.update h.anc K.fa (h.anc K.C.upper)) (fun b => by
        by_cases e : b = K.fa
        · subst e; simp
        · simp [Function.update_of_ne e, e])
    have h2 := h1.cutSt K.C.lower K.fb K.y₁ K.y₂ _ _ hce hce K.cut_b
      (Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) (fun b => by
        by_cases e : b = K.fb
        · subst e; simp [Function.update_of_ne K.fa_ne_b.symm]
        · simp [Function.update_of_ne e, e])
    exact h2.delSt _ K.closed

theorem HStep2.anc {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStep2 L γ η w κ h h') (hr : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 =>
    have c0 : (if h.s.cls (T.t 0) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have c1 : (if h.s.cls (T.t 1) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have c2 : (if h.s.cls (T.t 2) = .eps then Cls.beta else Cls.ghost) ≠ .eps := by split_ifs <;> intro h <;> cases h
    have n01 : T.t 1 ≠ T.f 0 := (T.f_ne_t 0 1).symm
    have n02 : T.t 2 ≠ T.f 0 := (T.f_ne_t 0 2).symm
    have n12 : T.t 2 ≠ T.f 1 := (T.f_ne_t 1 2).symm
    have a1 : ∀ b, (Function.update h.anc (T.f 0) (h.anc (T.t 0))) b = if b = T.f 0 then h.anc (T.t 0) else h.anc b := by
      intro b; by_cases e : b = T.f 0
      · subst e; simp
      · simp [Function.update_of_ne e, e]
    have h1 := hr.cutSt (T.t 0) (T.f 0) (T.a 0) (T.b 0) .beta _ (by simp) c0 T.cd1 _ a1
    have a2 : ∀ b, (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1))) b =
        if b = T.f 1 then (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.t 1) else
          (Function.update h.anc (T.f 0) (h.anc (T.t 0))) b := by
      intro b; by_cases e : b = T.f 1
      · subst e; simp [Function.update_of_ne n01]
      · simp [Function.update_of_ne e, e]
    have h2 := h1.cutSt (T.t 1) (T.f 1) (T.a 1) (T.b 1) .beta _ (by simp) c1 T.cd2 _ a2
    have a3 : ∀ b, (Function.update (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1)
        (h.anc (T.t 1))) (T.f 2) (h.anc (T.t 2))) b =
        if b = T.f 2 then (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1))) (T.t 2)
        else (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1))) b := by
      intro b; by_cases e : b = T.f 2
      · subst e; simp [Function.update_of_ne n02, Function.update_of_ne n12]
      · simp [Function.update_of_ne e, e]
    have h3 := h2.cutSt (T.t 2) (T.f 2) (T.a 2) (T.b 2) .beta _ (by simp) c2 T.cd3 _ a3
    have h4 := h3.delSt T.TP T.pclosed
    have h5 := h4.withCls (triCls h.s T Q kp) (fun a ha => by
      have ha' : a ∈ T.m3.atoms.filter T.TP := ha
      rw [Finset.mem_filter] at ha'
      exact (tri_cls_agree T Q kp a ha'.1 ha'.2).2.1)
    exact h5.delSt _ hcl

theorem HStep3.anc {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStep3 L γ η w κ h h') (hr : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | cut v v₂ x₁ x₂ hcd R' kp hR hkp hε hsg hsim hι h3 =>
    have hab : (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta).IsAB := by
      split_ifs <;> trivial
    exact hr.cutSt v v₂ x₁ x₂ _ _ (Cls.ne_eps_of_isAB hab) (Cls.ne_eps_of_isAB hab) hcd _ (fun b => by
      by_cases e : b = v₂
      · subst e; simp
      · simp [Function.update_of_ne e, e])

theorem HStep4.anc {L : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h h' : HSt V D₀}
    (hs : HStep4 L w κ h h') (hr : AncRel M₀ h.s h.anc) : AncRel M₀ h'.s h'.anc := by
  cases hs with
  | cut v v₂ x₁ x₂ hcd hε hβ hnz h3 =>
    exact hr.cutSt v v₂ x₁ x₂ _ _ (by simp) (by simp) hcd _ (fun b => by
      by_cases e : b = v₂
      · subst e; simp
      · simp [Function.update_of_ne e, e])

end WaveTurbulence.FinalCountG3

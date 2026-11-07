/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Hist
/-! **FINALCOUNT-G3: the record invariant `HInv`**: every `α`-atom is labelled (`IsLabel`) and carries the record of
its cut with `|gap| ∼ R` and `κ = 50 ↔ ι ≠ 0`; every `β`-atom carries the record of its cut, with nonzero gap. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- `|gap of the cut| ∼ R`. -/
def PSim (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (p : D₀ × D₀) (R : ℝ) : Prop :=
  R / 2 ≤ ‖pgap L w κ p‖ ∧ ‖pgap L w κ p‖ ≤ 2 * R

/-- The condition on one atom of class `c` with cut record `r`. -/
def AtomOK (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (c : Cls)
    (r : Option ((D₀ × D₀) × List (D₀ × D₀))) : Prop :=
  (∀ R kp, c = .alpha R kp → IsLabel L γ η R ∧ ∃ p vis, r = some (p, vis) ∧ PSim L w κ p R ∧
      (kp = 0 ∨ kp = 50) ∧ (kp = 50 ↔ IotaHit L η w κ vis p R) ∧
      Molecule.gapKind L γ η (pgap L w κ p) = .SG) ∧
  (c = .beta → ∃ p vis, r = some (p, vis) ∧ pgap L w κ p ≠ 0)

/-- The record invariant.  `mem`: the pair of a record is a recorded cut; `cmp`: two present atoms with records are either of
the same cut, or the cut of one is in the list `vis` of alive cuts of the other (the later cut sees the earlier one, since the
earlier is carried by a present atom: R38(4), re-proof of N2). -/
structure HInv (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop where
  mem : ∀ a ∈ h.s.M.atoms, ∀ p vis, h.crec a = some (p, vis) → p ∈ h.hist
  cmp : ∀ a ∈ h.s.M.atoms, ∀ a' ∈ h.s.M.atoms, ∀ p vis p' vis', h.crec a = some (p, vis) →
    h.crec a' = some (p', vis') → p = p' ∨ p ∈ vis' ∨ p' ∈ vis
  ok : ∀ a ∈ h.s.M.atoms, AtomOK L γ η w κ (h.s.cls a) (h.crec a)

theorem HInv.init (M₀ : Molecule V D₀) : HInv L γ η w κ (HSt.init M₀) where
  mem := fun a _ p vis h => by simp [HSt.init] at h
  cmp := fun a _ a' _ p vis p' vis' h => by simp [HSt.init] at h
  ok := fun a _ => ⟨fun R kp h => absurd h (by simp [HSt.init, St.init]),
    fun h => absurd h (by simp [HSt.init, St.init])⟩

theorem IsLabel.pos {R : ℝ} (h : IsLabel L γ η R) : 0 < R := by
  obtain ⟨⟨z, rfl⟩, -⟩ := h
  positivity

theorem PSim.ne_zero {p : D₀ × D₀} {R : ℝ} (h : PSim L w κ p R) (hR : 0 < R) : pgap L w κ p ≠ 0 := by
  intro e
  have := h.1
  rw [e, norm_zero] at this
  linarith

theorem gap_ne_zero_of_SG {r : Mom d} (h : Molecule.gapKind L γ η r = .SG) : r ≠ 0 := by
  intro e
  unfold Molecule.gapKind at h
  simp [e] at h

theorem gapKind_eq_of_norm_eq {r r' : Mom d} (h : ‖r‖ = ‖r'‖) :
    Molecule.gapKind L γ η r = Molecule.gapKind L γ η r' := by
  have h0 : r = 0 ↔ r' = 0 :=
    ⟨fun e => by rw [e, norm_zero] at h; exact norm_eq_zero.1 h.symm,
     fun e => by rw [e, norm_zero] at h; exact norm_eq_zero.1 h⟩
  unfold Molecule.gapKind
  simp only [h0, h]

theorem gapKind_of_twin {p q : D₀ × D₀}
    (htwin : pgap L w κ q = pgap L w κ p ∨ pgap L w κ q = -pgap L w κ p)
    (hsg : Molecule.gapKind L γ η (pgap L w κ p) = .SG) : Molecule.gapKind L γ η (pgap L w κ q) = .SG := by
  rcases htwin with h | h
  · rw [h]; exact hsg
  · rw [h, gapKind_eq_of_norm_eq (L := L) (γ := γ) (η := η) (norm_neg (pgap L w κ p))]; exact hsg

theorem AtomOK.ofAlphaOrBeta {fpos fpre : ℕ} {R : ℝ} {kp : ℕ} {p : D₀ × D₀} {vis : List (D₀ × D₀)}
    (hR : IsLabel L γ η R) (hp : PSim L w κ p R) (hkp : kp = 0 ∨ kp = 50)
    (hι : kp = 50 ↔ IotaHit L η w κ vis p R) (hsg : Molecule.gapKind L γ η (pgap L w κ p) = .SG) :
    AtomOK L γ η w κ (alphaOrBeta fpos fpre R kp) (some (p, vis)) := by
  unfold _root_.WaveTurbulence.FinalCountG3.alphaOrBeta
  split_ifs
  · refine ⟨fun R' kp' h => ?_, fun h => absurd h (by simp)⟩
    simp only [Cls.alpha.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hR, p, vis, rfl, hp, hkp, hι, hsg⟩
  · exact ⟨fun R' kp' h => absurd h (by simp), fun _ => ⟨p, vis, rfl, hp.ne_zero hR.pos⟩⟩

theorem AtomOK.beta {p : D₀ × D₀} {vis : List (D₀ × D₀)} (hp : pgap L w κ p ≠ 0) :
    AtomOK L γ η w κ .beta (some (p, vis)) :=
  ⟨fun R' kp' h => absurd h (by simp), fun _ => ⟨p, vis, rfl, hp⟩⟩

/-- Cases for the record function after a cut. -/
theorem cutRec_cases {h : HSt V D₀} {v v₂ : V} (hne : v₂ ≠ v) (r₁ r₂ : Option ((D₀ × D₀) × List (D₀ × D₀))) (a : V) :
    (a = v₂ ∧ Function.update (Function.update h.crec v r₁) v₂ r₂ a = r₂) ∨
    (a ≠ v₂ ∧ a = v ∧ Function.update (Function.update h.crec v r₁) v₂ r₂ a = r₁) ∨
    (a ≠ v₂ ∧ a ≠ v ∧ Function.update (Function.update h.crec v r₁) v₂ r₂ a = h.crec a) := by
  by_cases e2 : a = v₂
  · left; exact ⟨e2, by rw [e2, Function.update_self]⟩
  · by_cases e1 : a = v
    · right; left; exact ⟨e2, e1, by rw [Function.update_of_ne e2, e1, Function.update_self]⟩
    · right; right; exact ⟨e2, e1, by rw [Function.update_of_ne e2, Function.update_of_ne e1]⟩

theorem HInv.cut_gen {h : HSt V D₀} (hI : HInv L γ η w κ h) {v v₂ : V} (hv : v ∈ h.s.M.atoms)
    (hv₂ : v₂ ∉ h.s.M.atoms) (x₁ x₂ : h.s.D) (c₁ c₂ : Cls)
    (r₁ r₂ : Option ((D₀ × D₀) × List (D₀ × D₀))) (nh : List (D₀ × D₀)) {na : V → V}
    (h1 : AtomOK L γ η w κ c₁ r₁) (h2 : AtomOK L γ η w κ c₂ r₂)
    (m1 : ∀ p vis, r₁ = some (p, vis) → p ∈ nh)
    (m2 : ∀ p vis, r₂ = some (p, vis) → p ∈ nh) (hold : ∀ x ∈ h.hist, x ∈ nh)
    (a1 : ∀ p vis, r₁ = some (p, vis) → ∀ q ∈ h.alive, q ∈ vis)
    (a2 : ∀ p vis, r₂ = some (p, vis) → ∀ q ∈ h.alive, q ∈ vis)
    (c12 : ∀ p vis p' vis', r₁ = some (p, vis) → r₂ = some (p', vis') → p = p' ∨ p ∈ vis' ∨ p' ∈ vis) :
    HInv L γ η w κ ⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, nh, Function.update (Function.update h.crec v r₁) v₂ r₂, na⟩ where
  mem := by
    intro a ha p vis hp
    have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
    simp only at hp
    rcases cutRec_cases (h := h) hne r₁ r₂ a with ⟨-, e⟩ | ⟨-, -, e⟩ | ⟨n2, n1, e⟩
    · rw [e] at hp; exact m2 p vis hp
    · rw [e] at hp; exact m1 p vis hp
    · rw [e] at hp
      have ha' : a ∈ insert v₂ h.s.M.atoms := ha
      exact hold _ (hI.mem a ((Finset.mem_insert.1 ha').resolve_left n2) p vis hp)
  cmp := by
    intro a ha a' ha' p vis p' vis' e e'
    have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
    simp only at e e'
    have old : ∀ b, b ∈ insert v₂ h.s.M.atoms → b ≠ v₂ → b ∈ h.s.M.atoms :=
      fun b hb n2 => (Finset.mem_insert.1 hb).resolve_left n2
    have inAlive : ∀ b, b ∈ h.s.M.atoms → ∀ q vs, h.crec b = some (q, vs) → q ∈ h.alive :=
      fun b hb q vs hq => HSt.mem_alive.2 ⟨hI.mem b hb q vs hq, b, hb, vs, hq⟩
    have eqp : ∀ r : Option ((D₀ × D₀) × List (D₀ × D₀)), r = some (p, vis) → r = some (p', vis') → p = p' := by
      intro r e1 e2; rw [e1] at e2; simp only [Option.some.injEq, Prod.mk.injEq] at e2; exact e2.1
    rcases cutRec_cases (h := h) hne r₁ r₂ a with ⟨-, ea⟩ | ⟨-, -, ea⟩ | ⟨na2, na1, ea⟩ <;>
    rcases cutRec_cases (h := h) hne r₁ r₂ a' with ⟨-, eb⟩ | ⟨-, -, eb⟩ | ⟨nb2, nb1, eb⟩
    · exact Or.inl (eqp r₂ (ea.symm.trans e) (eb.symm.trans e'))
    · exact (c12 p' vis' p vis (eb.symm.trans e') (ea.symm.trans e)).elim (fun x => Or.inl x.symm) (fun x => Or.inr (x.symm))
    · rw [ea] at e; rw [eb] at e'
      exact Or.inr (Or.inr (a2 p vis e _ (inAlive a' (old a' ha' nb2) p' vis' e')))
    · exact c12 p vis p' vis' (ea.symm.trans e) (eb.symm.trans e')
    · exact Or.inl (eqp r₁ (ea.symm.trans e) (eb.symm.trans e'))
    · rw [ea] at e; rw [eb] at e'
      exact Or.inr (Or.inr (a1 p vis e _ (inAlive a' (old a' ha' nb2) p' vis' e')))
    · rw [ea] at e; rw [eb] at e'
      exact Or.inr (Or.inl (a2 p' vis' e' _ (inAlive a (old a ha na2) p vis e)))
    · rw [ea] at e; rw [eb] at e'
      exact Or.inr (Or.inl (a1 p' vis' e' _ (inAlive a (old a ha na2) p vis e)))
    · rw [ea] at e; rw [eb] at e'
      exact hI.cmp a (old a ha na2) a' (old a' ha' nb2) p vis p' vis' e e'
  ok := by
    intro a ha
    have ha' : a ∈ insert v₂ h.s.M.atoms := ha
    have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
    show AtomOK L γ η w κ ((h.s.cutSt v v₂ x₁ x₂ c₁ c₂).cls a) _
    by_cases e2 : a = v₂
    · subst e2
      rw [cutSt_cls_v₂]; simp only [Function.update_self]; exact h2
    · by_cases e1 : a = v
      · subst e1
        rw [cutSt_cls_v _ _ hne]; simp only [Function.update_of_ne hne.symm, Function.update_self]; exact h1
      · rw [cutSt_cls_other _ _ e1 e2]
        simp only [Function.update_of_ne e2, Function.update_of_ne e1]
        exact hI.ok a ((Finset.mem_insert.1 ha').resolve_left e2)

theorem HInv.delSt {h : HSt V D₀} (hI : HInv L γ η w κ h) (P : V → Prop) [DecidablePred P]
    (hP : PClosed h.s.M P) : HInv L γ η w κ ⟨h.s.delSt P hP, h.hist, h.crec, h.anc⟩ where
  mem := fun a ha => hI.mem a (Finset.mem_filter.1 ha).1
  cmp := fun a ha a' ha' => hI.cmp a (Finset.mem_filter.1 ha).1 a' (Finset.mem_filter.1 ha').1
  ok := fun a ha => hI.ok a (Finset.mem_filter.1 ha).1

theorem cmp_same {r : Option ((D₀ × D₀) × List (D₀ × D₀))} {p p' : D₀ × D₀} {vis vis' : List (D₀ × D₀)}
    (e : r = some (p, vis)) (e' : r = some (p', vis')) : p = p' ∨ p ∈ vis' ∨ p' ∈ vis := by
  rw [e] at e'; simp only [Option.some.injEq, Prod.mk.injEq] at e'; exact Or.inl e'.1

theorem mem_of_some {X p : D₀ × D₀} {V vis : List (D₀ × D₀)} {nh : List (D₀ × D₀)} (hX : X ∈ nh)
    (e : some (X, V) = some (p, vis)) : p ∈ nh := by
  simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨rfl, -⟩ := e; exact hX

theorem sub_of_some {X p : D₀ × D₀} {V vis : List (D₀ × D₀)} {A : List (D₀ × D₀)} (hA : ∀ q ∈ A, q ∈ V)
    (e : some (X, V) = some (p, vis)) : ∀ q ∈ A, q ∈ vis := by
  simp only [Option.some.injEq, Prod.mk.injEq] at e; obtain ⟨-, rfl⟩ := e; exact hA

/-- After a cut the alive cuts are among the cut and the previously alive ones. -/
theorem HSt.alive_cut_sub (h : HSt V D₀) (v v₂ : V) (x₁ x₂ : h.s.D) (c₁ c₂ : Cls) (p : D₀ × D₀)
    (vis₁ vis₂ : List (D₀ × D₀)) (na : V → V) :
    ∀ q ∈ (⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, p :: h.hist,
      Function.update (Function.update h.crec v (some (p, vis₁))) v₂ (some (p, vis₂)), na⟩ : HSt V D₀).alive,
      q ∈ p :: h.alive := by
  intro q hq
  obtain ⟨hqh, a, ha, vis, hrec⟩ := HSt.mem_alive.1 hq
  by_cases e : q = p
  · exact e ▸ List.mem_cons_self
  · refine List.mem_cons_of_mem _ (HSt.mem_alive.2 ⟨(List.mem_cons.1 hqh).resolve_left e, ?_⟩)
    have ha' : a ∈ insert v₂ h.s.M.atoms := ha
    simp only at hrec
    by_cases e2 : a = v₂
    · rw [e2, Function.update_self] at hrec
      simp only [Option.some.injEq, Prod.mk.injEq] at hrec; exact absurd hrec.1.symm e
    · rw [Function.update_of_ne e2] at hrec
      by_cases e1 : a = v
      · rw [e1, Function.update_self] at hrec
        simp only [Option.some.injEq, Prod.mk.injEq] at hrec; exact absurd hrec.1.symm e
      · rw [Function.update_of_ne e1] at hrec
        exact ⟨a, (Finset.mem_insert.1 ha').resolve_left e2, vis, hrec⟩

theorem HStep3.inv {h h' : HSt V D₀} (hs : HStep3 L γ η w κ h h') (hI : HInv L γ η w κ h) :
    HInv L γ η w κ h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 =>
    have hp : PSim L w κ (h.s.pr x₁ x₂) R := hsim
    have hnz : pgap L w κ (h.s.pr x₁ x₂) ≠ 0 := gap_ne_zero_of_SG hsg
    have hok : AtomOK L γ η w κ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
        (some (h.s.pr x₁ x₂, h.alive)) := by
      split_ifs
      · exact ⟨fun R' kp' e => by
          simp only [Cls.alpha.injEq] at e; obtain ⟨rfl, rfl⟩ := e
          exact ⟨hR, _, _, rfl, hp, hkp, hι, hsg⟩, fun e => absurd e (by simp)⟩
      · exact AtomOK.beta hnz
    exact hI.cut_gen hc.1 hc.2.1 x₁ x₂ _ _ _ _ _ hok hok
      (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
      (fun x hx => List.mem_cons_of_mem _ hx)
      (fun p vis e => sub_of_some (fun q hq => hq) e) (fun p vis e => sub_of_some (fun q hq => hq) e)
      (fun p vis p' vis' e e' => cmp_same e e')

theorem HStep4.inv {h h' : HSt V D₀} (hs : HStep4 L w κ h h') (hI : HInv L γ η w κ h) :
    HInv L γ η w κ h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 =>
    have hok : AtomOK L γ η w κ .beta (some (h.s.pr x₁ x₂, h.alive)) := AtomOK.beta hnz
    exact hI.cut_gen hc.1 hc.2.1 x₁ x₂ _ _ _ _ _ hok hok
      (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
      (fun x hx => List.mem_cons_of_mem _ hx)
      (fun p vis e => sub_of_some (fun q hq => hq) e) (fun p vis e => sub_of_some (fun q hq => hq) e)
      (fun p vis p' vis' e e' => cmp_same e e')

theorem HStep1.inv {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hI : HInv L γ η w κ h) :
    HInv L γ η w κ h' := by
  cases hs with
  | vine K R kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have hpa : PSim L w κ (h.s.pr K.x₁ K.x₂) R := ga
    have hpb : PSim L w κ (h.s.pr K.y₁ K.y₂) R := gb
    have e1 : AtomOK L γ η w κ (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp)
        (some (h.s.pr K.x₁ K.x₂, h.alive)) := AtomOK.ofAlphaOrBeta hR hpa hkp hι₁ hsg
    have e2 : AtomOK L γ η w κ (alphaOrBeta K.post.numComponents h.s.M.numComponents R kp)
        (some (h.s.pr K.y₁ K.y₂, h.s.pr K.x₁ K.x₂ :: h.alive)) :=
      AtomOK.ofAlphaOrBeta hR hpb hkp hι₂ (gapKind_of_twin htwin hsg)
    have g1 := hI.cut_gen (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a.1 K.cut_a.2.1 K.x₁ K.x₂ _ _ _ _ _ e1 e1
      (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
      (fun x hx => List.mem_cons_of_mem _ hx)
      (fun p vis e => sub_of_some (fun q hq => hq) e) (fun p vis e => sub_of_some (fun q hq => hq) e)
      (fun p vis p' vis' e e' => cmp_same e e')
    have g2 := g1.cut_gen (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) K.cut_b.1 K.cut_b.2.1 K.y₁ K.y₂ _ _ _ _ _ e2 e2
      (fun p vis e => mem_of_some List.mem_cons_self e) (fun p vis e => mem_of_some List.mem_cons_self e)
      (fun x hx => List.mem_cons_of_mem _ hx)
      (fun p vis e => sub_of_some (HSt.alive_cut_sub h _ _ _ _ _ _ _ _ _ _) e)
      (fun p vis e => sub_of_some (HSt.alive_cut_sub h _ _ _ _ _ _ _ _ _ _) e)
      (fun p vis p' vis' e e' => cmp_same e e')
    exact g2.delSt _ K.closed

theorem HStep2.inv {h h' : HSt V D₀} (hs : HStep2 L γ η w κ h h') (hI : HInv L γ η w κ h) :
    HInv L γ η w κ h' := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 =>
    have f01 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
    have f02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
    have f12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
    have c0 : ((0 : Fin 2).castSucc : Fin 3) = 0 := rfl
    have c1 : ((1 : Fin 2).castSucc : Fin 3) = 1 := rfl
    have hz0 : pgap L w κ (h.s.pr (T.a 0) (T.b 0)) ≠ 0 := gap_ne_zero_of_SG (hsg 0)
    have hz1 : pgap L w κ (h.s.pr (T.a 1) (T.b 1)) ≠ 0 := gap_ne_zero_of_SG (hsg 1)
    have hs0 : PSim L w κ (h.s.pr (T.a 0) (T.b 0)) (Q 0) := hsim 0
    have hs1 : PSim L w κ (h.s.pr (T.a 1) (T.b 1)) (Q 1) := hsim 1
    have key : ∀ a ∈ (triSt h.s T Q kp hcl).M.atoms, ∀ p vis,
        Function.update (Function.update (Function.update h.crec (T.f 0) (some (h.s.pr (T.a 0) (T.b 0), h.alive)))
          (T.f 1) (some (h.s.pr (T.a 1) (T.b 1), h.triVis1 T))) (T.f 2)
          (some (h.s.pr (T.a 2) (T.b 2), h.triVis2 T)) a = some (p, vis) →
        (a = T.f 0 ∧ h.s.cls (T.t 0) = .eps ∧ p = h.s.pr (T.a 0) (T.b 0) ∧ vis = h.alive) ∨
        (a = T.f 1 ∧ h.s.cls (T.t 1) = .eps ∧ p = h.s.pr (T.a 1) (T.b 1) ∧ vis = h.triVis1 T) ∨
        (a = T.f 2 ∧ p = h.s.pr (T.a 2) (T.b 2) ∧ vis = h.triVis2 T) ∨
        (a ∈ h.s.M.atoms ∧ h.crec a = some (p, vis)) := by
      intro a ha p vis e
      have hk : triKeep h.s T a := (Finset.mem_filter.1 ha).2
      have ha3 : a ∈ T.m3.atoms := (Finset.mem_filter.1 (Finset.mem_filter.1 ha).1).1
      rw [TriData.m3_atoms] at ha3
      simp only [Finset.mem_insert] at ha3
      rcases ha3 with rfl | rfl | rfl | hmem
      · right; right; left
        rw [Function.update_self] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        exact ⟨rfl, e.1.symm, e.2.symm⟩
      · right; left
        rw [Function.update_of_ne f12, Function.update_self] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        have : h.s.cls (T.t 1) = .eps := by
          by_contra hne; exact hk 1 hne rfl
        exact ⟨rfl, this, e.1.symm, e.2.symm⟩
      · left
        rw [Function.update_of_ne f02, Function.update_of_ne f01, Function.update_self] at e
        simp only [Option.some.injEq, Prod.mk.injEq] at e
        have : h.s.cls (T.t 0) = .eps := by
          by_contra hne; exact hk 0 hne rfl
        exact ⟨rfl, this, e.1.symm, e.2.symm⟩
      · right; right; right
        have hf : ∀ j, a ≠ T.f j := fun j e' => T.f_fresh j (e' ▸ hmem)
        rw [Function.update_of_ne (hf 2), Function.update_of_ne (hf 1), Function.update_of_ne (hf 0)] at e
        exact ⟨hmem, e⟩
    have inAlive : ∀ b, b ∈ h.s.M.atoms → ∀ q vs, h.crec b = some (q, vs) → q ∈ h.alive :=
      fun b hb q vs hq => HSt.mem_alive.2 ⟨hI.mem b hb q vs hq, b, hb, vs, hq⟩
    have hold : ∀ x ∈ h.hist, x ∈ h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist :=
      fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
    refine ⟨?_, ?_, ?_⟩
    · intro a ha p vis hp
      simp only at hp ⊢
      rcases key a ha p vis hp with ⟨-, -, rfl, -⟩ | ⟨-, -, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨hm, hr⟩
      · simp
      · simp
      · simp
      · exact hold _ (hI.mem a hm p vis hr)
    · intro a ha a' ha' p vis p' vis' e e'
      simp only at e e'
      rcases key a ha p vis e with ⟨-, h0, rfl, rfl⟩ | ⟨-, h1, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨hm, hr⟩ <;>
      rcases key a' ha' p' vis' e' with ⟨-, h0', rfl, rfl⟩ | ⟨-, h1', rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨hm', hr'⟩
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simp [HSt.triVis1, h0]))
      · exact Or.inr (Or.inl (h.triVis1_sub_triVis2 T _ (by simp [HSt.triVis1, h0])))
      · exact Or.inr (Or.inr (inAlive a' hm' _ _ hr'))
      · exact Or.inr (Or.inr (by simp [HSt.triVis1, h0']))
      · exact Or.inl rfl
      · exact Or.inr (Or.inl (by simp [HSt.triVis2, h1]))
      · exact Or.inr (Or.inr (h.alive_sub_triVis1 T _ (inAlive a' hm' _ _ hr')))
      · exact Or.inr (Or.inr (h.triVis1_sub_triVis2 T _ (by simp [HSt.triVis1, h0'])))
      · exact Or.inr (Or.inr (by simp [HSt.triVis2, h1']))
      · exact Or.inl rfl
      · exact Or.inr (Or.inr (h.triVis1_sub_triVis2 T _ (h.alive_sub_triVis1 T _ (inAlive a' hm' _ _ hr'))))
      · exact Or.inr (Or.inl (inAlive a hm _ _ hr))
      · exact Or.inr (Or.inl (h.alive_sub_triVis1 T _ (inAlive a hm _ _ hr)))
      · exact Or.inr (Or.inl (h.triVis1_sub_triVis2 T _ (h.alive_sub_triVis1 T _ (inAlive a hm _ _ hr))))
      · exact hI.cmp a hm a' hm' p vis p' vis' hr hr'
    · intro a ha
      have ha' : a ∈ T.m3.atoms.filter T.TP := (Finset.mem_filter.1 ha).1
      have ha3 : a ∈ T.m3.atoms := (Finset.mem_filter.1 ha').1
      show AtomOK L γ η w κ (triCls h.s T Q kp a) _
      rw [TriData.m3_atoms] at ha3
      simp only [Finset.mem_insert] at ha3
      rcases ha3 with e | e | e | e
      · subst e
        simp only [Function.update_self]
        rw [triCls_f2]
        split_ifs
        · exact AtomOK.beta hnz
        · exact ⟨fun _ _ x => absurd x (by simp), fun x => absurd x (by simp)⟩
      · subst e
        simp only [Function.update_of_ne f12, Function.update_self]
        rw [triCls_f1]
        split_ifs with hA hB
        · exact ⟨fun R' kp' x => by
            simp only [Cls.alpha.injEq] at x; obtain ⟨rfl, rfl⟩ := x
            exact ⟨hQ 1, _, _, rfl, hs1, hkp 1, hι₁ hA, hsg 1⟩, fun x => absurd x (by simp)⟩
        · exact AtomOK.beta hz1
        · exact ⟨fun _ _ x => absurd x (by simp), fun x => absurd x (by simp)⟩
      · subst e
        simp only [Function.update_of_ne f02, Function.update_of_ne f01, Function.update_self]
        rw [triCls_f0]
        split_ifs with hA hB
        · exact ⟨fun R' kp' x => by
            simp only [Cls.alpha.injEq] at x; obtain ⟨rfl, rfl⟩ := x
            exact ⟨hQ 0, _, _, rfl, hs0, hkp 0, hι₀ hA, hsg 0⟩, fun x => absurd x (by simp)⟩
        · exact AtomOK.beta hz0
        · exact ⟨fun _ _ x => absurd x (by simp), fun x => absurd x (by simp)⟩
      · have hf : ∀ j, a ≠ T.f j := fun j e' => T.f_fresh j (e' ▸ e)
        rw [triCls_other T Q kp hf]
        simp only [Function.update_of_ne (hf 2), Function.update_of_ne (hf 1), Function.update_of_ne (hf 0)]
        exact hI.ok a e

end WaveTurbulence.FinalCountG3

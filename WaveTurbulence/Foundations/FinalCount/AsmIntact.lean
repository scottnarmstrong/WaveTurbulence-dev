/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1
public import WaveTurbulence.Foundations.FinalCount.AsmDesig
public import WaveTurbulence.Foundations.Spine.SourcePairsCompatible
public import WaveTurbulence.Foundations.Spine.SourceObjectPairUniqueness
/-! **FINALCOUNT-ASSEMBLY (E2, intactness of collected objects).**  `UIntact U h`: every atom of the collected object `U` is a present
`ε`-atom of the state `h`.  Along the restricted Step 1 (`Reach1`) every collected object is either dartless or intact
(`collInv_of_reach1`), provided collected objects have the same designation or disjoint atom sets (S4-DISJ + F-DESIG, `SameDes`).  The removal of an intact object by a vine
cut along its own two `ContainsDart` darts at each joint leaves it dartless (`dartless_vineSt`, via `source_object_joint_pair_unique`). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- All atoms of `U` are present `ε`-atoms of `h`. -/
def UIntact {M₀ : Molecule V D₀} (U : Object M₀) (h : HSt V D₀) : Prop :=
  ∀ a ∈ U.atoms, a ∈ h.s.M.atoms ∧ h.s.cls a = .eps

theorem containsDart_inGroup {M : Molecule V D₀} (U : Object M) {z : D₀} (h : U.ContainsDart z) : M.InGroup U.atoms z := by
  unfold Object.ContainsDart at h
  rcases hs : U.shape with c | R
  · rw [hs] at h; exact h
  · rw [hs] at h; exact h.2.2

/-- A dart of the cut molecule whose atom lay in the removed set but is no longer in it was moved by one of the two cuts. -/
theorem cutMol_atom_moved {M : Molecule V D₀} (K : VineCut M) {y : D₀}
    (hin : M.atom y ∈ K.C.atoms) (hout : K.cutMol.atom y ∉ K.C.atoms) :
    (M.atom y = K.C.upper ∧ y ≠ K.x₁ ∧ y ≠ K.x₂) ∨ (M.atom y = K.C.lower ∧ y ≠ K.y₁ ∧ y ≠ K.y₂) := by
  by_cases h1 : M.atom y = K.C.upper ∧ y ≠ K.x₁ ∧ y ≠ K.x₂
  · exact Or.inl h1
  · right
    by_contra h2
    apply hout
    have e1 : K.m1.atom y = M.atom y := by
      simp only [VineCut.m1, Molecule.cut]; rw [if_neg h1]
    show (if K.m1.atom y = K.C.lower ∧ y ≠ K.y₁ ∧ y ≠ K.y₂ then K.fb else K.m1.atom y) ∈ K.C.atoms
    rw [if_neg (by rw [e1]; exact h2), e1]
    exact hin

/-- The `ContainsDart` darts of an object at a joint are the two of an oriented pair. -/
theorem cd_at_joint_eq {M : Molecule V D₀} (U : Object M) {v : V} (hv : v = U.upper ∨ v = U.lower) {p q z : D₀}
    (hpa : M.atom p = v) (hqa : M.atom q = v) (hpc : U.ContainsDart p) (hqc : U.ContainsDart q)
    (hpo : M.out p = true) (hqo : M.out q = false) (hza : M.atom z = v) (hzc : U.ContainsDart z) : z = p ∨ z = q := by
  cases hzo : M.out z
  · right
    exact (source_object_joint_pair_unique U hv (x := p) (y := z) (x' := p) (y' := q)
      ⟨hpa, hza, hpc, hzc, hpo, hzo⟩ ⟨hpa, hqa, hpc, hqc, hpo, hqo⟩).2
  · left
    exact (source_object_joint_pair_unique U hv (x := z) (y := q) (x' := p) (y' := q)
      ⟨hza, hqa, hzc, hqc, hzo, hqo⟩ ⟨hpa, hqa, hpc, hqc, hpo, hqo⟩).1

theorem m1_atom_of_ne {M : Molecule V D₀} (K : VineCut M) {w : D₀} {c : V} (hc : c ≠ K.fa) (h : K.m1.atom w = c) :
    M.atom w = c := by
  by_contra hne
  apply hne
  have : K.m1.atom w = if M.atom w = K.C.upper ∧ w ≠ K.x₁ ∧ w ≠ K.x₂ then K.fa else M.atom w := rfl
  rw [this] at h
  split_ifs at h with h1
  · exact absurd h.symm hc
  · exact h

/-- **A collected intact object that is cut along its own `ContainsDart` darts is dartless afterwards** (pointwise form). -/
theorem dartless_vineSt_key {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (K : VineCut s.M) (U : Object M₀) (hUat : U.atoms = K.C.atoms)
    (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps)
    (hdx : U.ContainsDart (s.down K.x₁) ∧ U.ContainsDart (s.down K.x₂) ∧ U.ContainsDart (s.down K.y₁) ∧
      U.ContainsDart (s.down K.y₂))
    (hUJ : (M₀.atom (s.down K.x₁) = U.upper ∧ M₀.atom (s.down K.y₁) = U.lower) ∨
      (M₀.atom (s.down K.x₁) = U.lower ∧ M₀.atom (s.down K.y₁) = U.upper))
    (y : s.D) (hP : K.cutMol.atom y ∉ K.C.atoms) (hx : U.ContainsDart (s.down y)) : False := by
  have hG := containsDart_inGroup U hx
  have hanc : ∀ y : s.D, M₀.atom (s.down y) ∈ U.atoms → s.M.atom y ∈ U.atoms := by
    intro y hy
    rw [hA.atom y] at hy
    have := hA.uniq _ (s.M.atom_mem y) _ (hint _ hy).1 (hint _ hy).2 rfl
    rw [this]; exact hy
  have hUe : ∀ b ∈ K.C.atoms, a b = b := fun b hb => by
    have hb' : b ∈ U.atoms := by rw [hUat]; exact hb
    exact hA.eps b (hint b hb').1 (hint b hb').2
  have hn : s.M.atom y ∈ K.C.atoms := by rw [← hUat]; exact hanc y hG.1
  have hup : M₀.atom (s.down K.x₁) = K.C.upper := by
    rw [hA.atom, K.cut_a.2.2.1, hUe _ K.a_mem]
  have hy1a : s.M.atom K.y₁ = K.C.lower := m1_atom_of_ne K K.fa_ne_b.symm K.cut_b.2.2.1
  have hy2a : s.M.atom K.y₂ = K.C.lower := m1_atom_of_ne K K.fa_ne_b.symm K.cut_b.2.2.2.1
  have hlow : M₀.atom (s.down K.y₁) = K.C.lower := by
    rw [hA.atom, hy1a, hUe _ K.b_mem]
  rcases cutMol_atom_moved K hn hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hv : K.C.upper = U.upper ∨ K.C.upper = U.lower := by
      rcases hUJ with ⟨e, -⟩ | ⟨e, -⟩
      · exact Or.inl (hup ▸ e)
      · exact Or.inr (hup ▸ e)
    have hza : M₀.atom (s.down y) = K.C.upper := by rw [hA.atom, h1, hUe _ K.a_mem]
    have := cd_at_joint_eq U hv (p := s.down K.x₂) (q := s.down K.x₁) (z := s.down y)
      (by rw [hA.atom, K.cut_a.2.2.2.1, hUe _ K.a_mem]) hup hdx.2.1 hdx.1
      (by rw [hD.out]; exact K.cut_a.2.2.2.2.2.2) (by rw [hD.out]; exact K.cut_a.2.2.2.2.2.1) hza hx
    rcases this with e | e
    · exact h3 (hA.inj e)
    · exact h2 (hA.inj e)
  · have hv : K.C.lower = U.upper ∨ K.C.lower = U.lower := by
      rcases hUJ with ⟨-, e⟩ | ⟨-, e⟩
      · exact Or.inr (hlow ▸ e)
      · exact Or.inl (hlow ▸ e)
    have hza : M₀.atom (s.down y) = K.C.lower := by rw [hA.atom, h1, hUe _ K.b_mem]
    have := cd_at_joint_eq U hv (p := s.down K.y₂) (q := s.down K.y₁) (z := s.down y)
      (by rw [hA.atom, hy2a, hUe _ K.b_mem]) hlow hdx.2.2.2 hdx.2.2.1
      (by rw [hD.out]; exact K.cut_b.2.2.2.2.2.2) (by rw [hD.out]; exact K.cut_b.2.2.2.2.2.1) hza hx
    rcases this with e | e
    · exact h3 (hA.inj e)
    · exact h2 (hA.inj e)

theorem dartless_vineSt {M₀ : Molecule V D₀} {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (K : VineCut s.M) (c : Cls) (U : Object M₀) (hUat : U.atoms = K.C.atoms)
    (hint : ∀ b ∈ U.atoms, b ∈ s.M.atoms ∧ s.cls b = .eps)
    (hdx : U.ContainsDart (s.down K.x₁) ∧ U.ContainsDart (s.down K.x₂) ∧ U.ContainsDart (s.down K.y₁) ∧
      U.ContainsDart (s.down K.y₂))
    (hUJ : (M₀.atom (s.down K.x₁) = U.upper ∧ M₀.atom (s.down K.y₁) = U.lower) ∨
      (M₀.atom (s.down K.x₁) = U.lower ∧ M₀.atom (s.down K.y₁) = U.upper)) :
    ∀ x : (vineSt s K c).D, ¬ U.ContainsDart ((vineSt s K c).down x) :=
  fun x hx => dartless_vineSt_key hA hD K U hUat hint hdx hUJ x.1 x.2 hx

theorem uIntact_init {M₀ : Molecule V D₀} (U : Object M₀) : UIntact U (HSt.init M₀) := fun a ha => ⟨objectAtoms_sub U ha, rfl⟩

/-- Intactness is preserved by a vine removal of an atom-disjoint object. -/
theorem uIntact_vinePost {M₀ : Molecule V D₀} {h : HSt V D₀} (K : VineCut h.s.M) (R : ℝ) (kp : ℕ) (U : Object M₀)
    (hU : UIntact U h) (hdis : Disjoint U.atoms K.C.atoms) : UIntact U (h.vinePost K R kp) := by
  intro a ha
  obtain ⟨haM, hε⟩ := hU a ha
  have haC : a ∉ K.C.atoms := fun hc => Finset.disjoint_left.mp hdis ha hc
  refine ⟨?_, ?_⟩
  · show a ∈ (restrictP K.cutMol (fun a => a ∉ K.C.atoms) K.closed).atoms
    show a ∈ (insert K.fb (insert K.fa h.s.M.atoms)).filter (fun a => a ∉ K.C.atoms)
    exact Finset.mem_filter.2 ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haM), haC⟩
  · show (vineSt h.s K _).cls a = .eps
    rw [vineSt_cls_old h.s K _ haM haC]; exact hε

/-- `AncRel` along the restricted reach. -/
theorem reach1_ancRel {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)}
    {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {h : HSt V D₀}
    (hr : Reach1 C Un Fst L γ η w κ h) : AncRel M₀ h.s h.anc := by
  induction hr with
  | refl => exact AncRel.init M₀
  | tail _ hs ih => exact hs.toC.anc ih

/-- **E2: every collected object is dartless or intact along the restricted Step 1.**  Hypothesis `hdisj`: two collected objects are
equal or atom-disjoint (S4-DISJ, with a unique designation per atom set). -/
theorem collInv_of_reach1 [Infinite V] {M₀ : Molecule V D₀} {Rn : ℕ} (hS : SubHyp Rn M₀) {C : CollData M₀}
    {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hdisj : ∀ U U' : Object M₀, Collected C (Un κ) L γ η w κ U → Collected C (Un κ) L γ η w κ U' →
      SameDes U U' ∨ Disjoint U.atoms U'.atoms)
    {h : HSt V D₀} (hr : Reach1 C Un Fst L γ η w κ h) :
    ∀ U, Collected C (Un κ) L γ η w κ U → Dartless U h ∨ UIntact U h := by
  induction hr with
  | refl => exact fun U _ => Or.inr (uIntact_init U)
  | @tail b h' hrb hs ih =>
    have hrb' : Reach1 C Un Fst L γ η w κ b := hrb
    have hA := reach1_ancRel hrb'
    have hD := (invE_of_reach hS h0 (Reach1.toAny hrb')).rel
    intro U hU
    cases hs with
    | vine K R kp hs U' hU' hUK hUD hUJ hord =>
      rcases ih U hU with hd | hi
      · exact Or.inl (fun x hx => hd x.1 hx)
      · rcases hdisj U U' hU hU' with hsd | hdis
        · exact Or.inl (dartless_vineSt hA hD K _ U (hsd.1.trans hUK) hi
            ⟨(hsd.2.1 _).2 hUD.1, (hsd.2.1 _).2 hUD.2.1, (hsd.2.1 _).2 hUD.2.2.1, (hsd.2.1 _).2 hUD.2.2.2⟩
            (by
              rcases hUJ with ⟨a, b⟩ | ⟨a, b⟩
              · exact hsd.joint_id (Or.inl ⟨a, b⟩)
              · exact hsd.joint_id (Or.inr ⟨a, b⟩)))
        · exact Or.inr (uIntact_vinePost K R kp U hi (hUK ▸ hdis))
    | triple _ hs hs3 hall _ =>
      exact Or.inl (by
        cases hs3 with
        | cut v v₂ x₁ x₂ hc R kp hR hkp hε hsg hsim hι h3 hdes => exact fun x hx => hall U hU x hx)

end WaveTurbulence.FinalCountAsm

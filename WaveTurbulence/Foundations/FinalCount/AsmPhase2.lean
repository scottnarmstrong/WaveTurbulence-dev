/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmTriPot
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3d
/-! **FINALCOUNT-ASSEMBLY, phase 2: node data, classes, the uniform step on a node class.**
A node of `h` is `(t, a, b, z, bk, al, sg, sib)`: the triangle atoms and darts (fresh names canonical, `fresh3 h`), the dyadic labels `2^{z j}`,
`kp j = 50` iff `bk j`, the alive records `al j` with signs `sg j` (for `kp = 50`), and `sib` (the second hit is the sibling cut of the same triangle). -/
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

/-- Three canonical fresh names. -/
noncomputable def fresh3 [Infinite V] (h : HSt V D₀) : Fin 3 → V :=
  Classical.choose (exists_three_fresh (V := V) h.s.M.atoms)

theorem fresh3_spec [Infinite V] (h : HSt V D₀) : Function.Injective (fresh3 h) ∧ ∀ j, fresh3 h j ∉ h.s.M.atoms :=
  Classical.choose_spec (exists_three_fresh (V := V) h.s.M.atoms)

/-- Triangle node data. -/
abbrev T2 (h : HSt V D₀) := (Fin 3 → V) × (Fin 3 → h.s.D) × (Fin 3 → h.s.D) × (Fin 2 → ℤ) × (Fin 2 → Bool) × (Fin 2 → V) ×
  (Fin 2 → Bool) × Bool

/-- A node is valid: a triangle with canonical fresh names and the state-level hypotheses of `UStep2`. -/
def Node2 [Infinite V] (L γ η : ℝ) (h : HSt V D₀) (n : T2 h) : Prop :=
  ∃ (T : TriData h.s.M) (_ : PClosed T.kept (triKeep h.s T)), T.t = n.1 ∧ T.a = n.2.1 ∧ T.b = n.2.2.1 ∧ T.f = fresh3 h ∧
    (∀ j : Fin 2, IsLabel L γ η ((2 : ℝ) ^ n.2.2.2.1 j)) ∧ (∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j)) ∧
    (∀ j : Fin 2, n.2.2.2.2.2.1 j ∈ h.s.M.atoms) ∧
    (n.2.2.2.2.1 0 = true → ∃ q vis, h.crec (n.2.2.2.2.2.1 0) = some (q, vis) ∧ q ∈ h.hist) ∧
    (n.2.2.2.2.1 1 = true → n.2.2.2.2.2.2.2 = false → ∃ q vis, h.crec (n.2.2.2.2.2.1 1) = some (q, vis) ∧ q ∈ h.hist) ∧
    (n.2.2.2.2.1 1 = true → n.2.2.2.2.2.2.2 = true → h.s.cls (n.1 0) = .eps)

/-- The hit through the alive record `a` with sign `sg`. -/
def WitnessAt (L η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) (a : V) (sg : Bool) (p : D₀ × D₀) (R : ℝ) : Prop :=
  0 < ‖pgap L w κ p + (if sg then (1 : ℝ) else -1) • pgap L w κ (qOf h a p)‖ ∧
    ‖pgap L w κ p + (if sg then (1 : ℝ) else -1) • pgap L w κ (qOf h a p)‖ ≤ L ^ (-50 * η) * R

/-- The class of a node (the `ι` clauses only for the atoms `t j` that are `ε`, as in `UStep2`). -/
def cls2 (L γ η : ℝ) (w : Mom d) (h : HSt V D₀) (A : Set (D₀ → (Fin d → ℤ))) (n : T2 h) : Set (D₀ → (Fin d → ℤ)) :=
  {k | k ∈ A ∧
    (∀ j : Fin 2, Molecule.gapKind L γ η (Molecule.gapAt L w (k ∘ h.s.down) (n.2.1 j.castSucc) (n.2.2.1 j.castSucc)) = .SG) ∧
    (∀ j : Fin 2, GapSim L w (k ∘ h.s.down) (n.2.1 j.castSucc) (n.2.2.1 j.castSucc) ((2 : ℝ) ^ n.2.2.2.1 j)) ∧
    pgap L w k (h.s.pr (n.2.1 2) (n.2.2.1 2)) ≠ 0 ∧
    (h.s.cls (n.1 0) = .eps → n.2.2.2.2.1 0 = true →
      WitnessAt L η w k h (n.2.2.2.2.2.1 0) (n.2.2.2.2.2.2.1 0) (h.s.pr (n.2.1 0) (n.2.2.1 0)) ((2 : ℝ) ^ n.2.2.2.1 0)) ∧
    (h.s.cls (n.1 0) = .eps → n.2.2.2.2.1 0 = false →
      ¬ IotaHit L η w k h.alive (h.s.pr (n.2.1 0) (n.2.2.1 0)) ((2 : ℝ) ^ n.2.2.2.1 0)) ∧
    (h.s.cls (n.1 1) = .eps → n.2.2.2.2.1 1 = true → (n.2.2.2.2.2.2.2 = false →
        WitnessAt L η w k h (n.2.2.2.2.2.1 1) (n.2.2.2.2.2.2.1 1) (h.s.pr (n.2.1 1) (n.2.2.1 1)) ((2 : ℝ) ^ n.2.2.2.1 1)) ∧
      (n.2.2.2.2.2.2.2 = true →
        0 < ‖pgap L w k (h.s.pr (n.2.1 1) (n.2.2.1 1)) + (if n.2.2.2.2.2.2.1 1 then (1 : ℝ) else -1) • pgap L w k (h.s.pr (n.2.1 0) (n.2.2.1 0))‖ ∧
        ‖pgap L w k (h.s.pr (n.2.1 1) (n.2.2.1 1)) + (if n.2.2.2.2.2.2.1 1 then (1 : ℝ) else -1) • pgap L w k (h.s.pr (n.2.1 0) (n.2.2.1 0))‖ ≤
          L ^ (-50 * η) * (2 : ℝ) ^ n.2.2.2.1 1)) ∧
    (h.s.cls (n.1 1) = .eps → n.2.2.2.2.1 1 = false →
      ¬ IotaHit L η w k (if h.s.cls (n.1 0) = .eps then h.s.pr (n.2.1 0) (n.2.2.1 0) :: h.alive else h.alive)
        (h.s.pr (n.2.1 1) (n.2.2.1 1)) ((2 : ℝ) ^ n.2.2.2.1 1))}

theorem node2_T [Infinite V] {L γ η : ℝ} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n) :
    ∃ (T : TriData h.s.M) (hcl : PClosed T.kept (triKeep h.s T)), T.t = n.1 ∧ T.a = n.2.1 ∧ T.b = n.2.2.1 ∧ T.f = fresh3 h := by
  obtain ⟨T, hcl, h1, h2, h3, h4, -⟩ := hn
  exact ⟨T, hcl, h1, h2, h3, h4⟩

/-- The labels and `kp`'s of a node. -/
noncomputable def Q2 {h : HSt V D₀} (n : T2 h) : Fin 2 → ℝ := fun j => (2 : ℝ) ^ n.2.2.2.1 j
def kp2 {h : HSt V D₀} (n : T2 h) : Fin 2 → ℕ := fun j => if n.2.2.2.2.1 j then 50 else 0

/-- The triangle and closedness proof of a node. -/
noncomputable def triOf [Infinite V] {L γ η : ℝ} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n) : TriData h.s.M :=
  Classical.choose hn

theorem triOf_cl [Infinite V] {L γ η : ℝ} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n) :
    PClosed (triOf hn).kept (triKeep h.s (triOf hn)) := Classical.choose (Classical.choose_spec hn)

/-- The post state of a node (the identity on a non-node). -/
noncomputable def post2 [Infinite V] (L γ η : ℝ) (h : HSt V D₀) (n : T2 h) : HSt V D₀ :=
  if hn : Node2 L γ η h n then h.triPost (triOf hn) (Q2 n) (kp2 n) (triOf_cl hn) else h

theorem post2_eq [Infinite V] {L γ η : ℝ} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n) :
    post2 L γ η h n = h.triPost (triOf hn) (Q2 n) (kp2 n) (triOf_cl hn) := by
  unfold post2; rw [dif_pos hn]

/-- The hypotheses of `UStep2.tri` for a triangle `T` (packaged so that both the step and `tri_excess` can be read from it). -/
structure S2Args (L γ η : ℝ) (w : Mom d) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ)
    (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)) : Prop where
  hQ : ∀ j : Fin 2, IsLabel L γ η (Q j)
  hkp : ∀ j : Fin 2, kp j = 0 ∨ kp j = 50
  hsg : ∀ k0, Adm0 k0 → ∀ j : Fin 2, Molecule.gapKind L γ η
        (Molecule.gapAt L w (k0 ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc)) = .SG
  hsim : ∀ k0, Adm0 k0 → ∀ j : Fin 2, GapSim L w (k0 ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc) (Q j)
  hnz : ∀ k0, Adm0 k0 → pgap L w k0 (h.s.pr (T.a 2) (T.b 2)) ≠ 0
  hι₀ : h.s.cls (T.t 0) = .eps → kp 0 = 50 → IotaUnif Adm0 L η w h (h.s.pr (T.a 0) (T.b 0)) (Q 0)
  hι₀' : h.s.cls (T.t 0) = .eps → kp 0 = 0 → ∀ k0, Adm0 k0 → ¬ IotaHit L η w k0 h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0)
  hι₁ : h.s.cls (T.t 1) = .eps → kp 1 = 50 → IotaUnif Adm0 L η w h (h.s.pr (T.a 1) (T.b 1)) (Q 1) ∨
        (h.s.cls (T.t 0) = .eps ∧ SibUnif Adm0 L η w (h.s.pr (T.a 0) (T.b 0)) (h.s.pr (T.a 1) (T.b 1)) (Q 1))
  hι₁' : h.s.cls (T.t 1) = .eps → kp 1 = 0 → ∀ k0, Adm0 k0 →
        ¬ IotaHit L η w k0 (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1)
  h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j)

theorem uStep2_of_args {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {h : HSt V D₀} {T : TriData h.s.M}
    {Q : Fin 2 → ℝ} {kp : Fin 2 → ℕ} {hcl : PClosed T.kept (triKeep h.s T)} (a : S2Args L γ η w Adm0 h T Q kp hcl) :
    UStep2 L γ η w Adm0 h (h.triPost T Q kp hcl) :=
  UStep2.tri h T Q kp a.hQ a.hkp (fun k hk j => a.hsg k hk j) (fun k hk j => a.hsim k hk j) hcl a.hnz a.hι₀ a.hι₀' a.hι₁ a.hι₁' a.h3

theorem s2args_node [Infinite V] {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {n : T2 h}
    (hn : Node2 L γ η h n) :
    S2Args L γ η w (fun k => k ∈ cls2 L γ η w h A n) h (triOf hn) (Q2 n) (kp2 n) (triOf_cl hn) := by
  obtain ⟨hcl0, ht, ha, hb, hf, hlab, h3, hal, hb0, hb1, hb2⟩ := Classical.choose_spec hn
  change (triOf hn).t = _ at ht
  change (triOf hn).a = _ at ha
  change (triOf hn).b = _ at hb
  change (∀ j, h.s.cls ((triOf hn).t j) = .eps → 3 ≤ h.s.M.deg ((triOf hn).t j)) at h3
  have hk0 : ∀ j : Fin 2, ((if n.2.2.2.2.1 j then 50 else 0 : ℕ) = 50 ↔ n.2.2.2.2.1 j = true) := fun j => by
    cases n.2.2.2.2.1 j <;> simp
  have hk1 : ∀ j : Fin 2, ((if n.2.2.2.2.1 j then 50 else 0 : ℕ) = 0 ↔ n.2.2.2.2.1 j = false) := fun j => by
    cases n.2.2.2.2.1 j <;> simp
  have hq : ∀ (a : V) (p : D₀ × D₀) (q : D₀ × D₀) (vis), h.crec a = some (q, vis) → qOf h a p = q := fun a p q vis hc => by
    simp [qOf, hc]
  have hsgn : ∀ sg : Bool, ((if sg then (1 : ℝ) else -1) = 1 ∨ (if sg then (1 : ℝ) else -1) = -1) := fun sg => by cases sg <;> simp
  have hε : ∀ j, h.s.cls ((triOf hn).t j) = .eps → h.s.cls (n.1 j) = .eps := fun j e => by rw [← ht]; exact e
  refine ⟨hlab, (fun j => by cases n.2.2.2.2.1 j <;> simp [kp2]), ?_, ?_, ?_, ?_, ?_, ?_, ?_, h3⟩
  · intro k hk j; rw [ha, hb]; exact hk.2.1 j
  · intro k hk j; rw [ha, hb]; exact hk.2.2.1 j
  · intro k hk; rw [ha, hb]; exact hk.2.2.2.1
  · intro he h50
    have hb0' := (hk0 0).1 h50
    obtain ⟨q, vis, hcr, hqh⟩ := hb0 hb0'
    refine ⟨q, hqh, ⟨n.2.2.2.2.2.1 0, hal 0, vis, hcr⟩, if n.2.2.2.2.2.2.1 0 then 1 else -1, hsgn _, fun k hk => ?_⟩
    have := hk.2.2.2.2.1 (hε 0 he) hb0'
    unfold WitnessAt at this
    rw [hq _ _ q vis hcr] at this
    rw [ha, hb]; exact this
  · intro he h0 k hk
    have := hk.2.2.2.2.2.1 (hε 0 he) ((hk1 0).1 h0)
    rw [ha, hb]; exact this
  · intro he h50
    have hb1' := (hk0 1).1 h50
    by_cases hs : n.2.2.2.2.2.2.2 = true
    · right
      refine ⟨?_, if n.2.2.2.2.2.2.1 1 then 1 else -1, hsgn _, fun k hk => ?_⟩
      · have := hb2 hb1' hs
        rw [ht]; exact this
      · have := (hk.2.2.2.2.2.2.1 (hε 1 he) hb1').2 hs
        rw [ha, hb]; exact this
    · left
      have hs' : n.2.2.2.2.2.2.2 = false := by simpa using hs
      obtain ⟨q, vis, hcr, hqh⟩ := hb1 hb1' hs'
      refine ⟨q, hqh, ⟨n.2.2.2.2.2.1 1, hal 1, vis, hcr⟩, if n.2.2.2.2.2.2.1 1 then 1 else -1, hsgn _, fun k hk => ?_⟩
      have := ((hk.2.2.2.2.2.2.1 (hε 1 he) hb1').1 hs')
      unfold WitnessAt at this
      rw [hq _ _ q vis hcr] at this
      rw [ha, hb]; exact this
  · intro he h0 k hk
    have := hk.2.2.2.2.2.2.2 (hε 1 he) ((hk1 1).1 h0)
    unfold HSt.triVis1
    rw [ht, ha, hb]; exact this

theorem uStep2_node [Infinite V] {L γ η : ℝ} {w : Mom d} {h : HSt V D₀} {A : Set (D₀ → (Fin d → ℤ))} {n : T2 h}
    (hn : Node2 L γ η h n) : UStep2 L γ η w (fun k => k ∈ cls2 L γ η w h A n) h (post2 L γ η h n) := by
  rw [post2_eq hn]; exact uStep2_of_args (s2args_node hn)

end WaveTurbulence.FinalCountAsm

/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.Ports
public import WaveTurbulence.Foundations.Molecule.SkeletonDraft.PortOverlap

/-! # A uniform four-port representation retaining every source edge

Root vertices use port 0; their three other ports are explicitly inactive
identities. Branch vertices use all four ordered ports. The padding is an
exact embedding of the actual source port matching, not a graph quotient.
-/

@[expose] public section
namespace WaveTurbulence.Reg.Skeleton

abbrev Vertex {w : ℕ} (G : Garden w) := Fin w ⊕ GBranch G.tree
abbrev UniformPort {w : ℕ} (G : Garden w) := Vertex G × Fin 4

def padPort {w : ℕ} (G : Garden w) : Port G → UniformPort G
  | .inl j => (.inl j,0)
  | .inr (b,i) => (.inr b,i)

def unpadPort {w : ℕ} (G : Garden w) : UniformPort G → Option (Port G)
  | (.inl j,i) => if i = 0 then some (.inl j) else none
  | (.inr b,i) => some (.inr (b,i))

theorem unpadPort_padPort {w : ℕ} (G : Garden w) (p : Port G) :
    unpadPort G (padPort G p) = some p := by cases p <;> simp [padPort,unpadPort]

theorem padPort_of_unpad {w : ℕ} (G : Garden w) (p : UniformPort G) (q : Port G)
    (h : unpadPort G p = some q) : padPort G q = p := by
  obtain ⟨v,i⟩ := p
  cases v with
  | inl j =>
    by_cases hi : i = 0
    · subst i
      simp only [unpadPort,ite_true,Option.some.injEq] at h
      subst q
      rfl
    · simp [unpadPort,hi] at h
  | inr b =>
    simp only [unpadPort,Option.some.injEq] at h
    subst q
    rfl

theorem padPort_injective {w : ℕ} (G : Garden w) : Function.Injective (padPort G) := by
  intro p q h
  have he := congrArg (unpadPort G) h
  rw [unpadPort_padPort,unpadPort_padPort] at he
  exact Option.some.inj he

/-- The original port matching, extended by the explicitly inactive root ports. -/
def uniformMate {w : ℕ} (G : Garden w) (p : UniformPort G) : UniformPort G :=
  match unpadPort G p with
  | none => p
  | some q => padPort G (portMate G q)

theorem uniformMate_padPort {w : ℕ} (G : Garden w) (p : Port G) :
    uniformMate G (padPort G p) = padPort G (portMate G p) := by
  simp only [uniformMate,unpadPort_padPort]

/-- The uniform graph retains exact source matching involutivity. -/
theorem uniformMate_involutive {w : ℕ} (G : Garden w) : Function.Involutive (uniformMate G) := by
  intro p
  cases h : unpadPort G p with
  | none => simp only [uniformMate,h]
  | some q =>
    have he := padPort_of_unpad G p q h
    rw [← he,uniformMate_padPort,uniformMate_padPort,portMate_involutive G]

/-- Every genuine source port remains active in an ordinary garden. -/
theorem uniformMate_ne_padPort {w : ℕ} (G : Garden w) (hG : G.IsPlain) (p : Port G) :
    uniformMate G (padPort G p) ≠ padPort G p := by
  rw [uniformMate_padPort]
  intro he
  exact portMate_ne G hG p (padPort_injective G he)

/-- The extra root ports carry the identity matching, by definition. -/
theorem uniformMate_root_inactive {w : ℕ} (G : Garden w) (j : Fin w) (i : Fin 4) (hi : i ≠ 0) :
    uniformMate G (.inl j,i) = (.inl j,i) := by
  simp [uniformMate,unpadPort,hi]

/-- A root cannot be one endpoint of a three-bond mini piece. -/
theorem not_threeBonds_root {w : ℕ} (G : Garden w) (j : Fin w) (v : Vertex G)
    (hv : v ≠ .inl j) : ¬ ThreeBonds (uniformMate G) (.inl j) v := by
  have hs : portsTo (uniformMate G) (.inl j) v ⊆ {0} := by
    intro i hi
    by_contra hn
    have hi0 : i ≠ 0 := by simpa only [Finset.mem_singleton] using hn
    have he := (Finset.mem_filter.mp hi).2
    rw [uniformMate_root_inactive G j i hi0] at he
    exact hv he.symm
  have hc := Finset.card_le_card hs
  simp only [Finset.card_singleton] at hc
  unfold ThreeBonds
  omega

end WaveTurbulence.Reg.Skeleton

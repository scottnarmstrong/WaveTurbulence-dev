/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.StemSel

/-! # B2b-2 MK-MARK: the fine protected set `Π` on addresses and its transport

`Π = protI LG J pat t s kSel` is the closed unit neighbourhood of the seeds of `Π₀` together with the selected
capped-stem vertices (`SeedSel = SeedAt ∨ SelAt`; `mem_protI_iff`). `prot_transport_gen` is Lemma 2⁺(a) on gardens
for an abstract seed predicate (the proof of `prot_transport` with the seeds abstracted), and `protSel_transport`
instantiates it for `Π`: if `Π` avoids `R` and the capped stems avoid `R`, then `Π'` avoids `R'` and the
correspondence maps `Π ∖ R` onto `Π' ∖ R'`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg.Skeleton

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

/-- Protected addresses for an abstract seed predicate: nodes within distance one of a seed. -/
def ProtG (LG : LayeredGarden w) (Seed : Address w → Prop) (z : Address w) : Prop :=
  NodeAt LG z ∧ ∃ σ : Address w, NearAt z σ ∧ Seed σ

/-- The seeds of `Π`: those of `Π₀` and the selected capped-stem vertices. -/
def SeedSel (LG : LayeredGarden w) (J : Finset (Fin w)) (pat : Fin w → FixPat) (kSel : Fin w → Option ℕ)
    (σ : Address w) : Prop :=
  SeedAt LG J pat σ ∨ SelAt LG J kSel σ

/-- **`Π` on addresses.** -/
theorem mem_protI_iff {LG : LayeredGarden w} {J : Finset (Fin w)} (pat : Fin w → FixPat) (t s : ℝ)
    (kSel : Fin w → Option ℕ) (a : GNode LG.garden.tree) :
    a ∈ protI LG J pat t s kSel ↔ ProtG LG (SeedSel LG J pat kSel) a.1 := by
  unfold protI protectedSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨σ, hn, hσ⟩
    refine ⟨a.2, σ.1, hn, ?_⟩
    rcases hσ with h | ⟨b, rfl, hf | hsel⟩
    · exact Or.inl ⟨σ.2, Or.inl h⟩
    · exact Or.inl ⟨b.toNode.2, Or.inr ⟨b.2, (fixCap_isSome_iff pat t s b).mp hf⟩⟩
    · exact Or.inr ⟨b, hsel, rfl⟩
  · rintro ⟨-, σ, hn, hσ | ⟨b, hb, rfl⟩⟩
    · obtain ⟨hnode, hσ⟩ := hσ
      refine ⟨⟨σ, hnode⟩, hn, ?_⟩
      rcases hσ with h | ⟨hb, hf⟩
      · exact Or.inl h
      · exact Or.inr ⟨⟨σ, hb⟩, rfl, Or.inl ((fixCap_isSome_iff pat t s ⟨σ, hb⟩).mpr hf)⟩
    · exact ⟨b.toNode, hn, Or.inr ⟨b, rfl, Or.inr hb⟩⟩

/-! ## Generic transport of a protected set -/

section Gen
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} {Seed Seed' : Address w → Prop}

/-- Protected addresses off the region correspond (one direction). -/
theorem OutIso.protG (I : OutIso LG LG' R R') (hSn : ∀ σ, Seed σ → NodeAt LG σ)
    (hS : ∀ σ, NodeAt LG σ → σ ∉ R → (Seed' (I.f σ) ↔ Seed σ)) (hp : ∀ z ∈ R, ¬ ProtG LG Seed z)
    {z : Address w} (hn : NodeAt LG z) (hz : z ∉ R) : ProtG LG Seed z → ProtG LG' Seed' (I.f z) := by
  rintro ⟨-, σ, hnear, hσ⟩
  have hσn := hSn σ hσ
  have hσR : σ ∉ R := fun h => hp _ h ⟨hσn, σ, nearAt_refl σ, hσ⟩
  have hfσ := (hS σ hσn hσR).mpr hσ
  refine ⟨(I.node z hn hz).1, ?_⟩
  rcases nearAt_cases hnear with he | ⟨i, he⟩ | ⟨i, he⟩
  · subst he
    exact ⟨I.f z, nearAt_refl _, hfσ⟩
  · have e : I.f σ = addrExt (I.f z) [i] := by
      rw [he]
      exact I.child z i hn hz (he ▸ hσn) (he ▸ hσR)
    refine ⟨I.f σ, ?_, hfσ⟩
    rw [e]
    exact nearAt_parent_child _ _
  · have e : I.f z = addrExt (I.f σ) [i] := by
      rw [he]
      exact I.child σ i hσn hσR (he ▸ hn) (he ▸ hz)
    refine ⟨I.f σ, ?_, hfσ⟩
    rw [e]
    exact nearAt_child_parent _ _

/-- **Lemma 2⁺(a) on gardens, abstract seeds.** -/
theorem prot_transport_gen (I : OutIso LG LG' R R') (I' : OutIso LG' LG R' R)
    (hinv : ∀ z', NodeAt LG' z' → z' ∉ R' → I.f (I'.f z') = z')
    (hinv' : ∀ z, NodeAt LG z → z ∉ R → I'.f (I.f z) = z)
    (hSn : ∀ σ, Seed σ → NodeAt LG σ) (hSn' : ∀ σ', Seed' σ' → NodeAt LG' σ')
    (hS : ∀ σ, NodeAt LG σ → σ ∉ R → (Seed' (I.f σ) ↔ Seed σ)) (hS0' : ∀ σ' ∈ R', ¬ Seed' σ')
    (hp : ∀ z ∈ R, ¬ ProtG LG Seed z) :
    (∀ z' ∈ R', ¬ ProtG LG' Seed' z') ∧
      ∀ z, NodeAt LG z → z ∉ R → (ProtG LG' Seed' (I.f z) ↔ ProtG LG Seed z) := by
  have hpull : ∀ σ', NodeAt LG' σ' → σ' ∉ R' → (Seed (I'.f σ') ↔ Seed' σ') := by
    intro σ' hn' hR'σ
    obtain ⟨hn, hRσ⟩ := I'.node σ' hn' hR'σ
    rw [← hS _ hn hRσ, hinv σ' hn' hR'σ]
  have hp' : ∀ z' ∈ R', ¬ ProtG LG' Seed' z' := by
    rintro z' hz' ⟨hn', σ', hnear, hσ'⟩
    have hσR' : σ' ∉ R' := fun h => hS0' _ h hσ'
    have hσn' := hSn' σ' hσ'
    have hσ := (hpull σ' hσn' hσR').mpr hσ'
    rcases nearAt_cases hnear with he | ⟨i, he⟩ | ⟨i, he⟩
    · subst he
      exact hσR' hz'
    · have hne : σ'.2 ≠ [] := by rw [he]; simp [addrExt]
      have hpar : (σ'.1, σ'.2.dropLast) = z' := by rw [he]; simp [addrExt]
      have hR2 := (I'.parentR σ' hσn' hσR' hne).mp (by rw [hpar]; exact hz')
      obtain ⟨hσn, -⟩ := I'.node σ' hσn' hσR'
      have hne2 : (I'.f σ').2 ≠ [] := fun h => hne ((I'.root σ' hσn' hσR').mp h)
      have hz := addrExt_parent hne2
      refine hp _ hR2 ⟨nodeAt_of_branchAt (branchAt_of_child (i := (I'.f σ').2.getLast hne2)
        (by rw [← hz]; exact hσn)), I'.f σ', ?_, hσ⟩
      conv_rhs => rw [hz]
      exact nearAt_parent_child _ _
    · have hc := (I'.childR σ' i hσn' hσR').mp ⟨by rw [← he]; exact hn', by rw [← he]; exact hz'⟩
      exact hp _ hc.2 ⟨hc.1, I'.f σ', nearAt_child_parent _ _, hσ⟩
  refine ⟨hp', fun z hn hz => ⟨fun h' => ?_, fun h => I.protG hSn hS hp hn hz h⟩⟩
  obtain ⟨hn', hz'⟩ := I.node z hn hz
  have h2 := I'.protG hSn' hpull hp' hn' hz' h'
  rwa [hinv' z hn hz] at h2

end Gen

/-! ## The fine protected set -/

section Fine
variable {LG LG' : LayeredGarden w} {R R' : Set (Address w)} {J : Finset (Fin w)} {pat : Fin w → FixPat}
  (kSel : Fin w → Option ℕ)

theorem protAt_protG {z : Address w} (h : ProtAt LG J pat z) : ProtG LG (SeedSel LG J pat kSel) z :=
  ⟨h.1, h.2.choose, h.2.choose_spec.1, Or.inl h.2.choose_spec.2⟩

/-- **Lemma 2⁺(a) on gardens for `Π`.** If `Π(LG)` and the capped stems of `LG` avoid `R`, then `Π(LG')` and
the capped stems of `LG'` avoid `R'`, and the correspondence maps `Π(LG) ∖ R` onto `Π(LG') ∖ R'`. -/
theorem protSel_transport (I : OutIso LG LG' R R') (I' : OutIso LG' LG R' R)
    (hinv : ∀ z', NodeAt LG' z' → z' ∉ R' → I.f (I'.f z') = z')
    (hinv' : ∀ z, NodeAt LG z → z ∉ R → I'.f (I.f z) = z) (hR : RegionOK LG R) (hR' : RegionOK LG' R')
    (hp : ∀ z ∈ R, ¬ ProtG LG (SeedSel LG J pat kSel) z) (hs : StemAvoid LG J R) :
    (∀ z' ∈ R', ¬ ProtG LG' (SeedSel LG' J pat kSel) z') ∧
      (∀ z, NodeAt LG z → z ∉ R → (ProtG LG' (SeedSel LG' J pat kSel) (I.f z) ↔ ProtG LG (SeedSel LG J pat kSel) z)) ∧
      StemAvoid LG' J R' := by
  have hp0 : NoProtIn LG J pat R := fun z hz h => hp z hz (protAt_protG kSel h)
  have hs0' := noSeed' I' hR hR' hp0
  obtain ⟨-, hstem, -, hs'⟩ := I.stem_transport I' hinv hR hR' hs
  have hsel : ∀ σ, NodeAt LG σ → σ ∉ R → (SelAt LG' J kSel (I.f σ) ↔ SelAt LG J kSel σ) := by
    intro σ hn hz
    constructor
    · intro h
      have h0 := (selAt_congr hstem kSel _).mp h
      obtain ⟨j, hj⟩ := selAt_capStem LG J h0
      obtain ⟨ℓ, hℓ, hb⟩ := ((hstem j _).mpr hj).2.2.1
      have e1 : I'.f (I.f σ) = I.f σ := I'.stem_fix hs' hℓ _ hb
      have e : I.f σ = σ := e1.symm.trans (hinv' σ hn hz)
      rwa [e] at h0
    · intro h
      obtain ⟨j, hj⟩ := selAt_capStem LG J h
      obtain ⟨ℓ, hℓ, hb⟩ := hj.2.2.1
      rw [I.stem_fix hs hℓ σ hb]
      exact (selAt_congr hstem kSel σ).mpr h
  have hsel0' : ∀ σ' ∈ R', ¬ SelAt LG' J kSel σ' := by
    intro σ' hσ' h
    obtain ⟨j, hj⟩ := selAt_capStem LG' J h
    obtain ⟨ℓ, hℓ, hb⟩ := hj.2.2.1
    exact hs' ℓ hℓ σ' hb hσ'
  obtain ⟨h1, h2⟩ := prot_transport_gen I I' hinv hinv'
    (fun σ h => Or.elim h (fun h => h.1) (nodeAt_of_selAt LG J))
    (fun σ h => Or.elim h (fun h => h.1) (nodeAt_of_selAt LG' J))
    (fun σ hn hz => or_congr (I.seed hR hR' hp0 hs0' hn hz) (hsel σ hn hz))
    (fun σ' hσ' h => Or.elim h (hs0' σ' hσ') (hsel0' σ' hσ')) hp
  exact ⟨h1, h2, hs'⟩

end Fine

end WaveTurbulence.Flower.MkMark

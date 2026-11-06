/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.Selection
/-! # Proof of the ladder selection claim (S3c) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.CoarseSpliced
open WaveTurbulence WaveTurbulence.LGSpine Finset
open scoped Classical

theorem selection_claim : SelectionClaim := by
  intro R G layer hinges hmol hconn hatoms A
  set 𝓜 := G.molecule.maximalLadders with h𝓜
  have hdisj : ∀ S S' : {S // S ∈ 𝓜}, S ≠ S' → Disjoint S.1 S'.1 := fun S S' h =>
    WaveTurbulence.LadderDisjoint.maximalLadders_pairwiseDisjoint G.molecule hmol S.2 S'.2
      (fun e => h (Subtype.ext e))
  let toL : {S // S ∈ 𝓜} → Lad G := fun S => ⟨A.length S, A.upper S, A.lower S⟩
  let l₀ : List (Lad G) := (Finset.univ : Finset {S // S ∈ 𝓜}).toList.map toL
  have hatomsL : ∀ S, (toL S).atoms = S.1 := fun S => A.atoms S
  have hPw : Lad.Pw l₀ := by
    unfold Lad.Pw
    rw [List.pairwise_map]
    refine (Finset.nodup_toList _).imp ?_
    intro S S' hne
    rw [hatomsL, hatomsL]
    exact hdisj S S' hne
  have hAll : Lad.AllL l₀ := by
    intro ℓ hℓ
    obtain ⟨S, -, rfl⟩ := List.mem_map.mp hℓ
    exact A.ladder S
  -- numbers for the initial list
  have hcardS : ∀ S : {S // S ∈ 𝓜}, 2 * A.length S + 2 = S.1.card := by
    intro S
    have := card_ladderAtoms_ladder (A.ladder S)
    rw [A.atoms S] at this
    omega
  have hTS0 : Lad.TS l₀ = ∑ S : {S // S ∈ 𝓜}, S.1.card := by
    unfold Lad.TS
    rw [List.map_map]
    have : (fun ℓ : Lad G => 2 * ℓ.1 + 2) ∘ toL = fun S => S.1.card := by
      funext S; exact hcardS S
    rw [this]
    exact Finset.sum_map_toList _ _
  have hIS0 : Lad.IS layer l₀ = A.totalIncoherency layer := by
    unfold Lad.IS SourceMaximalLadderDataC.totalIncoherency
    rw [List.map_map]
    exact Finset.sum_map_toList _ (Lad.inc layer ∘ toL)
  have hlen0 : l₀.length = G.molecule.numLadders := by
    simp only [l₀, List.length_map, Finset.length_toList, Finset.card_univ, Fintype.card_coe]
    rfl
  have hsubatoms : ∀ S ∈ 𝓜, S ⊆ G.molecule.atoms := by
    intro S hS
    simp only [h𝓜, Molecule.maximalLadders, Finset.mem_filter, Finset.mem_powerset] at hS
    exact hS.1
  have hn : Lad.TS l₀ + G.molecule.numFree = G.order := by
    rw [hTS0, ← hatoms]
    have hsum : ∑ S : {S // S ∈ 𝓜}, S.1.card = ∑ S ∈ 𝓜, S.card := Finset.sum_coe_sort 𝓜 (fun S => S.card)
    rw [hsum]
    have hbi : (𝓜.biUnion id).card = ∑ S ∈ 𝓜, S.card := by
      rw [Finset.card_biUnion]
      · simp
      · intro S hS S' hS' hne
        exact WaveTurbulence.LadderDisjoint.maximalLadders_pairwiseDisjoint G.molecule hmol hS hS' hne
    rw [← hbi]
    unfold Molecule.numFree
    have h1 : 𝓜.biUnion id = G.molecule.atoms.filter (fun v => ¬ ∀ S ∈ 𝓜, v ∉ S) := by
      ext v
      simp only [Finset.mem_biUnion, id, Finset.mem_filter]
      constructor
      · rintro ⟨S, hS, hv⟩
        exact ⟨hsubatoms S hS hv, fun h => h S hS hv⟩
      · rintro ⟨-, h⟩
        push Not at h
        exact h
    rw [h1]
    have hh := Finset.card_filter_add_card_filter_not (s := G.molecule.atoms)
      (fun v => ¬ ∀ S ∈ 𝓜, v ∉ S)
    simp only [not_not] at hh
    convert hh using 3
    ext v
    simp [h𝓜]
  obtain ⟨l', hP', hL', hD', hS', hT', hI', hN'⟩ := Lad.remove_atoms layer hinges l₀ hPw hAll
  have hq : G.molecule.numLadders ≤ G.molecule.rho := by unfold Molecule.rho; omega
  have hf : G.molecule.numFree ≤ G.molecule.rho := by unfold Molecule.rho; omega
  have hrho : G.molecule.rho = G.molecule.numLadders + G.molecule.numFree := rfl
  let F : SelData G hinges :=
    { ι := Fin l'.length
      m := fun i => (l'[i.1]).1
      u := fun i => (l'[i.1]).2.1
      v := fun i => (l'[i.1]).2.2
      ladder := fun i => hL' _ (List.getElem_mem _)
      disj := by
        intro i j hij
        have hp := List.pairwise_iff_getElem.mp hP'
        rcases lt_or_gt_of_ne (fun h => hij (Fin.ext h)) with h | h
        · exact hp i.1 j.1 i.2 j.2 h
        · exact (hp j.1 i.1 j.2 i.2 h).symm
      hing := fun i => hD' _ (List.getElem_mem _) }
  have hsumI : ∑ i : Fin l'.length, sourceLadderIncoherency G layer (F.u i) (F.v i) = Lad.IS layer l' := by
    unfold Lad.IS
    exact Fin.sum_univ_fun_getElem l' (Lad.inc layer)
  have hsumT : ∑ i : Fin l'.length, (2 * F.m i + 2) = Lad.TS l' := by
    unfold Lad.TS
    exact Fin.sum_univ_fun_getElem l' (fun ℓ => 2 * ℓ.1 + 2)
  refine ⟨F, ?_, ?_, ?_⟩
  · rw [hsumI, ← hIS0]
    omega
  · show Fintype.card (Fin l'.length) ≤ _
    rw [Fintype.card_fin]
    omega
  · show G.order - ∑ i : Fin l'.length, (2 * F.m i + 2) + Fintype.card (Fin l'.length) ≤ _
    rw [hsumT, Fintype.card_fin]
    omega

end WaveTurbulence.CoarseSpliced

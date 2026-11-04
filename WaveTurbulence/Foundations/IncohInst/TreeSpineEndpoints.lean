/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.LayerReg.Spine

/-! # The source root and lone-parent links along the regular tree spine -/

public section
namespace WaveTurbulence.IncohInst
open WaveTurbulence.Reg WaveTurbulence.Links TTree

variable {w : ℕ}

/-- The final top-level spine link, computed from the actual regular-chain code. -/
@[expose] def lastSpineLink {w : ℕ} : RegChain → (Fin w × Path) →
    Option ((Fin w × Path) × (Fin w × Path))
  | .nil, _ => none
  | .pair m _ _ inner .nil, a => some (a, addrExt a ([m.c] ++ inner.lonePath))
  | .pair m _ _ inner rest@(.pair ..), a =>
      lastSpineLink rest (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))

/-- The last computed pair is one of C4's proved source spine links. -/
theorem lastSpineLink_mem {w : ℕ} (X : RegChain) (a : Fin w × Path)
    {l : (Fin w × Path) × (Fin w × Path)} (h : lastSpineLink X a = some l) :
    l ∈ spineLinks X a := by
  cases X with
  | nil => simp [lastSpineLink] at h
  | pair m Qr Qg inner rest =>
    cases rest with
    | nil =>
      simp only [lastSpineLink, Option.some.injEq] at h
      rw [← h]
      exact List.mem_cons_self
    | pair m' Qr' Qg' inner' rest' =>
      simp only [lastSpineLink] at h
      exact List.mem_cons_of_mem _ (lastSpineLink_mem (.pair m' Qr' Qg' inner' rest') _ h)

/-- The second endpoint of the final spine link is the parent of the source lone leaf. -/
theorem lastSpineLink_parent {w : ℕ} (X : RegChain) (a : Fin w × Path)
    {l : (Fin w × Path) × (Fin w × Path)} (h : lastSpineLink X a = some l) :
    ∃ i : Fin 3, addrExt a X.lonePath = addrExt l.2 [i] := by
  cases X with
  | nil => simp [lastSpineLink] at h
  | pair m Qr Qg inner rest =>
    cases rest with
    | nil =>
      simp only [lastSpineLink, Option.some.injEq] at h
      rw [← h]
      refine ⟨m.lone, ?_⟩
      simp [RegChain.lonePath, addrExt, List.append_assoc]
    | pair m' Qr' Qg' inner' rest' =>
      simp only [lastSpineLink] at h
      obtain ⟨i, hi⟩ := lastSpineLink_parent (.pair m' Qr' Qg' inner' rest') _ h
      refine ⟨i, ?_⟩
      simpa only [RegChain.lonePath, addrExt_append, List.append_assoc] using hi

/-- Every selected spine pair is ordered below the root and above the lone leaf. -/
theorem spineLink_under (X : RegChain) (a : Fin w × Path)
    {l : (Fin w × Path) × (Fin w × Path)} (h : l ∈ spineLinks X a) :
    Under a l.1 ∧ Under l.1 l.2 ∧ Under l.2 (addrExt a X.lonePath) := by
  cases X with
  | nil => simp only [spineLinks, List.not_mem_nil] at h
  | pair m Qr Qg inner rest =>
    simp only [spineLinks, List.mem_cons] at h
    rcases h with rfl | h
    · refine ⟨under_refl _, under_ext _ _, ?_⟩
      rw [chain_lonePath_eq]
      simpa only [addrExt_append, List.append_assoc] using
        (under_ext (addrExt a ([m.c] ++ inner.lonePath)) ([m.lone] ++ rest.lonePath))
    · obtain ⟨ha, hb, hc⟩ := spineLink_under rest _ h
      refine ⟨under_trans (under_ext _ _) ha, hb, ?_⟩
      rwa [chain_lonePath_eq]

/-- The last spine pair exists for every nontrivial regular chain. -/
theorem lastSpineLink_exists (X : RegChain) (hX : X ≠ .nil) (a : Fin w × Path) :
    ∃ l, lastSpineLink X a = some l := by
  cases X with
  | nil => exact False.elim (hX rfl)
  | pair m Qr Qg inner rest =>
    cases rest with
    | nil => exact ⟨(a, addrExt a ([m.c] ++ inner.lonePath)), by simp only [lastSpineLink]⟩
    | pair m' Qr' Qg' inner' rest' =>
      simpa only [lastSpineLink] using
        lastSpineLink_exists (.pair m' Qr' Qg' inner' rest') (by simp) _

/-- The first endpoint of every spine link is an actual spine position. -/
theorem spineLink_fst_mem (X : RegChain) (a : Fin w × Path)
    {l : (Fin w × Path) × (Fin w × Path)} (h : l ∈ spineLinks X a) :
    l.1 ∈ spinePos X a := by
  cases X with
  | nil => simp only [spineLinks, List.not_mem_nil] at h
  | pair m Qr Qg inner rest =>
    simp only [spineLinks, List.mem_cons] at h
    rcases h with rfl | h
    · exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (spineLink_fst_mem rest _ h)

/-- Every spine link points strictly downward; this is source path geometry. -/
theorem spineLink_length_lt (X : RegChain) (a : Fin w × Path)
    {l : (Fin w × Path) × (Fin w × Path)} (h : l ∈ spineLinks X a) :
    l.1.2.length < l.2.2.length := by
  cases X with
  | nil => simp only [spineLinks, List.not_mem_nil] at h
  | pair m Qr Qg inner rest =>
    simp only [spineLinks, List.mem_cons] at h
    rcases h with rfl | h
    · simp [addrExt]
    · exact spineLink_length_lt rest _ h

end WaveTurbulence.IncohInst

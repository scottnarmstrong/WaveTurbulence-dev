/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegStruct.StructureTypeSeparation

/-! # Injective address transport into a pair of incomparable rooted subtrees -/

@[expose] public section
namespace WaveTurbulence.Reg
open TTree

/-- Embed the two original trees below their specified rooted frame. -/
def frameAddress {w : ℕ} (a b : Fin w × Path) (z : Fin 2 × Path) : Fin w × Path :=
  if z.1 = 0 then addrExt a z.2 else addrExt b z.2

/-- Global extension commutes with frame transport. -/
theorem frameAddress_respects {w : ℕ} (a b : Fin w × Path) : ∀ z p, frameAddress a b (addrExt z p) = addrExt (frameAddress a b z) p := by
  intro z p
  obtain ⟨j,q⟩ := z
  fin_cases j <;> simp [frameAddress,addrExt, List.append_assoc]

/-- The two canonical roots map to the specified frame roots. -/
theorem frameAddress_roots {w : ℕ} (a b : Fin w × Path) :
    frameAddress a b (0,[]) = a ∧ frameAddress a b (1,[]) = b := by
  simp [frameAddress,addrExt]

/-- Incomparable roots give a globally injective address transport. -/
theorem frameAddress_injective {w : ℕ} (a b : Fin w × Path) (hab : IncompAddr a b) :
    Function.Injective (frameAddress a b) := by
  rintro ⟨j,p⟩ ⟨k,q⟩ h
  fin_cases j <;> fin_cases k
  · have he : addrExt a p = addrExt a q := by simpa [frameAddress] using h
    have hp := congrArg Prod.snd he
    exact Prod.ext rfl (List.append_cancel_left hp)
  · have he : addrExt a p = addrExt b q := by simpa [frameAddress] using h
    have hb : Below b (addrExt a p) := he ▸ below_extend b q
    exact ((below_comparable (below_extend a p) hb).elim hab.1 hab.2).elim
  · have he : addrExt b p = addrExt a q := by simpa [frameAddress] using h
    have hb : Below a (addrExt b p) := he ▸ below_extend a q
    exact ((below_comparable hb (below_extend b p)).elim hab.1 hab.2).elim
  · have he : addrExt b p = addrExt b q := by simpa [frameAddress] using h
    have hp := congrArg Prod.snd he
    exact Prod.ext rfl (List.append_cancel_left hp)

/-- Pair lists transport literally into their chosen global frame. -/
theorem pairsAt_frameAddress {w : ℕ} (C : RegCpl) (a b : Fin w × Path) :
    C.pairsAt a b = C.raw.2.map (fun p => (frameAddress a b p.1,frameAddress a b p.2)) := by
  have he := couple_pairsAt_map C (frameAddress a b) (frameAddress_respects a b) (0,[]) (1,[])
  rw [(frameAddress_roots a b).1,(frameAddress_roots a b).2] at he
  exact he

/-- Unordered pair membership transports through the same literal address map. -/
theorem symmPairs_frameAddress_mem {w : ℕ} (C : RegCpl) (a b : Fin w × Path)
    (p : (Fin 2 × Path) × (Fin 2 × Path)) (hp : p ∈ symmPairs C.raw.2) :
    (frameAddress a b p.1,frameAddress a b p.2) ∈ symmPairs (C.pairsAt a b) := by
  rw [mem_symmPairs_iff] at hp ⊢
  rw [pairsAt_frameAddress]
  rcases hp with hp | hp
  · exact Or.inl (List.mem_map.mpr ⟨p,hp,rfl⟩)
  · exact Or.inr (List.mem_map.mpr ⟨p.swap,hp,rfl⟩)

end WaveTurbulence.Reg

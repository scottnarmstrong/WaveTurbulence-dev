/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Molecule.LayerRegDraft.Replace

/-! # ZP-SURJ: relocation of placed regular codes (links, pairs, node sets)

If `ρ` commutes with address extension on a region `P` closed under extension, then the links and pairs of a code
placed at `(ρ a, ρ b)` are the `ρ`-images of those placed at `(a, b)`.
-/

@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links

variable {w w' : ℕ}

section Map
variable (P : Fin w × Path → Prop) (ρ : Fin w × Path → Fin w' × Path)
  (hP : ∀ x q, P x → P (addrExt x q)) (hρ : ∀ x q, P x → ρ (addrExt x q) = addrExt (ρ x) q)

include hP hρ

mutual
theorem cpl_links_map (Q : RegCpl) (a b : Fin w × Path) (ha : P a) (hb : P b) :
    Q.linksAt (ρ a) (ρ b) = (Q.linksAt a b).map (fun l => (ρ l.1, ρ l.2)) := by
  cases Q with
  | triv => simp [RegCpl.linksAt]
  | type1 c Q₁ Q₂ Q₃ =>
    have h1 := cpl_links_map Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (hP _ _ ha) (hP _ _ hb)
    have h2 := cpl_links_map Q₂ (addrExt b [1]) (addrExt a [1]) (hP _ _ hb) (hP _ _ ha)
    have h3 := cpl_links_map Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (hP _ _ ha) (hP _ _ hb)
    simp only [hρ a _ ha, hρ b _ hb] at h1 h2 h3
    simp only [RegCpl.linksAt, List.map_cons, List.map_append, h1, h2, h3]
  | type2 Xp Xm Qlp =>
    have h1 := chain_links_map Xp 1 a ha
    have h2 := chain_links_map Xm (-1) b hb
    have h3 := cpl_links_map Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) (hP _ _ ha) (hP _ _ hb)
    simp only [hρ a _ ha, hρ b _ hb] at h3
    simp only [RegCpl.linksAt, List.map_append, h1, h2, h3]
termination_by structural Q

theorem chain_links_map (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a) :
    X.linksAt ζ (ρ a) = (X.linksAt ζ a).map (fun l => (ρ l.1, ρ l.2)) := by
  cases X with
  | nil => simp [RegChain.linksAt]
  | pair m Qr Qg inner rest =>
    have hi := chain_links_map inner (slotSign ζ m.c) (addrExt a [m.c]) (hP _ _ ha)
    have hr := chain_links_map rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (hP _ _ ha)
    have hr1 := cpl_links_map Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      (hP _ _ ha) (hP _ _ ha)
    have hr2 := cpl_links_map Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
      (hP _ _ ha) (hP _ _ ha)
    have hg1 := cpl_links_map Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      (hP _ _ ha) (hP _ _ ha)
    have hg2 := cpl_links_map Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
      (hP _ _ ha) (hP _ _ ha)
    simp only [hρ a _ ha] at hi hr hr1 hr2 hg1 hg2
    simp only [RegChain.linksAt, List.map_cons, List.map_append, hi, hr, apply_ite (List.map _)]
    rw [hρ a _ ha]
    split_ifs <;> simp only [hr1, hr2, hg1, hg2]
termination_by structural X
end

mutual
theorem cpl_pairs_map (Q : RegCpl) (a b : Fin w × Path) (ha : P a) (hb : P b) :
    Q.pairsAt (ρ a) (ρ b) = (Q.pairsAt a b).map (fun l => (ρ l.1, ρ l.2)) := by
  cases Q with
  | triv => simp [RegCpl.pairsAt]
  | type1 c Q₁ Q₂ Q₃ =>
    have h1 := cpl_pairs_map Q₁ (addrExt a [0]) (addrExt b [c.partner 0]) (hP _ _ ha) (hP _ _ hb)
    have h2 := cpl_pairs_map Q₂ (addrExt b [1]) (addrExt a [1]) (hP _ _ hb) (hP _ _ ha)
    have h3 := cpl_pairs_map Q₃ (addrExt a [2]) (addrExt b [c.partner 2]) (hP _ _ ha) (hP _ _ hb)
    simp only [hρ a _ ha, hρ b _ hb] at h1 h2 h3
    simp only [RegCpl.pairsAt, List.map_cons, List.map_append, h1, h2, h3]
  | type2 Xp Xm Qlp =>
    have h1 := chain_pairs_map Xp 1 a ha
    have h2 := chain_pairs_map Xm (-1) b hb
    have h3 := cpl_pairs_map Qlp (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) (hP _ _ ha) (hP _ _ hb)
    simp only [hρ a _ ha, hρ b _ hb] at h3
    simp only [RegCpl.pairsAt, List.map_append, h1, h2, h3]
termination_by structural Q

theorem chain_pairs_map (X : RegChain) (ζ : ℤˣ) (a : Fin w × Path) (ha : P a) :
    X.pairsAt ζ (ρ a) = (X.pairsAt ζ a).map (fun l => (ρ l.1, ρ l.2)) := by
  cases X with
  | nil => simp [RegChain.pairsAt]
  | pair m Qr Qg inner rest =>
    have hi := chain_pairs_map inner (slotSign ζ m.c) (addrExt a [m.c]) (hP _ _ ha)
    have hr := chain_pairs_map rest (slotSign (slotSign ζ m.c) m.lone)
      (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) (hP _ _ ha)
    have hr1 := cpl_pairs_map Qr (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      (hP _ _ ha) (hP _ _ ha)
    have hr2 := cpl_pairs_map Qr (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
      (hP _ _ ha) (hP _ _ ha)
    have hg1 := cpl_pairs_map Qg (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      (hP _ _ ha) (hP _ _ ha)
    have hg2 := cpl_pairs_map Qg (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
      (hP _ _ ha) (hP _ _ ha)
    simp only [hρ a _ ha] at hi hr hr1 hr2 hg1 hg2
    simp only [RegChain.pairsAt, List.map_cons, List.map_append, hi, hr, apply_ite (List.map _)]
    split_ifs <;> simp only [hr1, hr2, hg1, hg2]
termination_by structural X
end

end Map
end WaveTurbulence.ZpSurj

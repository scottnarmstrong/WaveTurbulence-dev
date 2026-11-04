/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.TreeClockSelection

/-! # The four actual clocks when root and lone-parent links differ -/

public section
noncomputable section
open scoped Classical
namespace WaveTurbulence.IncohInst
open Incoh Links TTree Reg

/-- A longer source spine selects its first and last links, with all four endpoints in order. -/
@[expose] def twoLinkClockSelection {G : Garden 1} (m : MiniTreeCode) (Qr Qg : RegCpl)
    (inner rest : RegChain) (hr : rest ≠ .nil)
    (hX : (RegChain.pair m Qr Qg inner rest).DecodesTree G) : TreeClockSelection hX := by
  let X := RegChain.pair m Qr Qg inner rest
  let a : Fin 1 × Path := (0, [])
  let l₀ := firstSpineLink m inner a
  have h₀ : l₀ ∈ spineLinks X a := firstSpineLink_mem _ _ _ _ _ _
  let hex := lastSpineLink_exists rest hr (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
  let l₁ := Classical.choose hex
  have hlast := Classical.choose_spec hex
  have h₁rest := lastSpineLink_mem rest _ hlast
  have h₁ : l₁ ∈ spineLinks X a := List.mem_cons_of_mem _ h₁rest
  have hmid := lastSpine_after_firstPartner m inner rest a hlast
  have hlen₀ := spineLink_length_lt X a h₀
  have hlen₁ := spineLink_length_lt X a h₁
  have hne : spineLinkIndex hX l₀ h₀ ≠ spineLinkIndex hX l₁ h₁ := by
    intro he
    have hl : l₀ = l₁ := (get_spineLinkIndex hX l₀ h₀).symm.trans
      (he ▸ get_spineLinkIndex hX l₁ h₁)
    have hh := congrArg (fun l => l.1.2.length) hl
    have hm : l₀.2.2.length < l₁.1.2.length := hmid.2
    omega
  let v : Fin 2 ↪ Fin (X.treeLinks (G.sig 0)).length :=
    ⟨![spineLinkIndex hX l₀ h₀, spineLinkIndex hX l₁ h₁], by
      intro i j he
      fin_cases i <;> fin_cases j
      · rfl
      · exact False.elim (hne he)
      · exact False.elim (hne he.symm)
      · rfl⟩
  let S := selectedClocksOfLinks v
  have he (j : Fin 4) : selectedTreeAddress hX S j = ![l₀.1, l₀.2, l₁.1, l₁.2] j := by
    rw [selectedTreeAddress_ofLinks]
    fin_cases j
    · exact treeLinkBranch_spineLinkIndex hX l₀ h₀ 0
    · exact treeLinkBranch_spineLinkIndex hX l₀ h₀ 1
    · exact treeLinkBranch_spineLinkIndex hX l₁ h₁ 0
    · exact treeLinkBranch_spineLinkIndex hX l₁ h₁ 1
  refine ⟨2, Or.inr rfl, S, ?_, ?_, ?_⟩
  · rw [he]
    rfl
  · obtain ⟨i, hi⟩ := lastSpineLink_parent rest _ hlast
    refine ⟨i, ?_⟩
    rw [he]
    change addrExt a X.lonePath = addrExt l₁.2 [i]
    rw [chain_lonePath_eq]
    exact hi
  · intro j
    fin_cases j
    · simp only [he]
      exact ⟨(spineLink_under X a h₀).2.1, hlen₀⟩
    · simp only [he]
      exact hmid
    · simp only [he]
      exact ⟨(spineLink_under X a h₁).2.1, hlen₁⟩

end WaveTurbulence.IncohInst

/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulenceVineParam.VineParamNormalizedBaseMatching
public import WaveTurbulenceVineParam.VineParamPhysicalIsoSupport
import Mathlib.Tactic

/-! # Exact directed source graph of a normalized base certificate -/

public section
namespace WaveTurbulence.Vine.Param
open Finset

/-- The source support pins the normalized certificate to the exact atom range. -/
theorem normalized_support_atom_count {X : VineType} {p : Fin (baseProfileCount X)}
    (C : NormalizedVineCertificate X) (H : NormalizedBaseSupport p C) :
    C.shape.n+1=X.template.n := by
  rw [H.shape_eq]
  exact normalizedBaseShape_atoms X

/-- Source-selected actual endpoint counts produce a complete directed
atom/bond isomorphism from the concrete normalized chart graph. -/
theorem normalized_base_graph_iso {X : VineType} {p : Fin (baseProfileCount X)}
    (C : NormalizedVineCertificate X) (H : NormalizedBaseSupport p C)
    {m : ℕ} (A : Fin m → Fin X.template.n × Fin X.template.n)
    (hU : ((List.ofFn (fun e => ((A e).1.1,(A e).2.1)) : List (ℕ×ℕ)) : Multiset (ℕ×ℕ)).map
      (fun e => s(e.1,e.2))=(X.template.bonds.map (fun e => s(e.1,e.2)) : Multiset (Sym2 ℕ)))
    (hp : baseProfileCounts X p=List.ofFn (fun i =>
      (List.ofFn (fun e => ((A e).1.1,(A e).2.1))).count (baseBundlePair X i))) :
    ∃ I : DirectedGraphIso C.matrix.ends A,∀ v,(I.atom v).1=v.1 := by
  obtain ⟨σ,hσ⟩ := normalized_base_bond_matching C H (fun e => ((A e).1.1,(A e).2.1)) hU hp
  let atom : Fin (C.shape.n+1) ≃ Fin X.template.n := finCongr (normalized_support_atom_count C H)
  refine ⟨{ atom := atom,edge := σ.symm,endpoints := ?_ },fun _ => rfl⟩
  intro e
  have h := hσ (σ.symm e)
  rw [σ.apply_symm_apply] at h
  apply Prod.ext
  · exact Fin.ext (congrArg Prod.fst h).symm
  · exact Fin.ext (congrArg Prod.snd h).symm

end WaveTurbulence.Vine.Param

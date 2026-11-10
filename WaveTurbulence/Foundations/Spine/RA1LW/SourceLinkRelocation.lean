/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.SourceParameterRelocation
public import WaveTurbulence.Foundations.IncohInst.Links.Param

/-! # Original link lists under root-preserving address embeddings -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open Links Reg TTree

variable {w w' : ℕ}

mutual
/-- Link addresses commute with every map preserving path extension. -/
theorem cpl_linksAt_map (e : Fin w × Path → Fin w' × Path)
    (he : ∀ a p, e (addrExt a p) = addrExt (e a) p) :
    (Q : RegCpl) → (a b : Fin w × Path) →
    Q.linksAt (e a) (e b) = (Q.linksAt a b).map (fun l => (e l.1,e l.2))
  | .triv, _,_ => rfl
  | .type1 c Q₁ Q₂ Q₃, a,b => by
    simp only [RegCpl.linksAt,List.map_cons,List.map_append,
      ← he,cpl_linksAt_map e he Q₁,cpl_linksAt_map e he Q₂,cpl_linksAt_map e he Q₃]
  | .type2 Xp Xm Qlp, a,b => by
    simp only [RegCpl.linksAt,List.map_append,← he,
      chain_linksAt_map e he Xp,chain_linksAt_map e he Xm,cpl_linksAt_map e he Qlp]
termination_by structural Q => Q

/-- The corresponding identity for original chain links retains their sign. -/
theorem chain_linksAt_map (e : Fin w × Path → Fin w' × Path)
    (he : ∀ a p, e (addrExt a p) = addrExt (e a) p) :
    (X : RegChain) → (ζ : ℤˣ) → (a : Fin w × Path) →
    X.linksAt ζ (e a) = (X.linksAt ζ a).map (fun l => (e l.1,e l.2))
  | .nil, _,_ => rfl
  | .pair m Qr Qg inner rest, ζ,a => by
    simp only [RegChain.linksAt,List.map_cons,List.map_append,apply_ite,
      ← he,cpl_linksAt_map e he Qr,cpl_linksAt_map e he Qg,
      chain_linksAt_map e he inner,chain_linksAt_map e he rest]
termination_by structural X => X
end

/-- Embed the two canonical source trees above independent original roots. -/
@[expose] def rootPlacement (a b : Fin w × Path) (z : Fin 2 × Path) : Fin w × Path :=
  addrExt (if z.1=0 then a else b) z.2

/-- The embedding retains every original path extension. -/
theorem rootPlacement_ext (a b : Fin w × Path) (z : Fin 2 × Path) (p : Path) :
    rootPlacement a b (addrExt z p) = addrExt (rootPlacement a b z) p := by
  simp only [rootPlacement,addrExt,List.append_assoc]
  rfl

/-- Independent source roots give an injective embedding of the two trees. -/
theorem rootPlacement_injective {a b : Fin w × Path} (hab : Indep a b) :
    Function.Injective (rootPlacement a b) := by
  intro z z' he
  rcases z with ⟨i,p⟩
  rcases z' with ⟨j,q⟩
  fin_cases i <;> fin_cases j
  · change addrExt a p = addrExt a q at he
    exact congrArg (fun p => ((0:Fin 2),p))
      (List.append_cancel_left (congrArg Prod.snd he))
  · change addrExt a p = addrExt b q at he
    exact (hab.not_both (under_ext a p) (he.symm ▸ under_ext b q)).elim
  · change addrExt b p = addrExt a q at he
    exact (hab.not_both (under_ext a q) (he ▸ under_ext b p)).elim
  · change addrExt b p = addrExt b q at he
    exact congrArg (fun p => ((1:Fin 2),p))
      (List.append_cancel_left (congrArg Prod.snd he))

/-- Literal link placement is the canonical link list under this embedding. -/
theorem cpl_links_rootPlacement (Q : RegCpl) (a b : Fin w × Path) :
    Q.linksAt a b = Q.links.map (fun l => (rootPlacement a b l.1,rootPlacement a b l.2)) := by
  have hh := cpl_linksAt_map (rootPlacement a b) (rootPlacement_ext a b) Q (0,[]) (1,[])
  simpa [rootPlacement,addrExt,RegCpl.links] using hh

/-- The original source leaf kernel at any independent placement equals
its canonical kernel with the pulled-back original parameters. -/
theorem cplLeafProduct_rootPlacement {V : Type*} [AddCommGroup V]
    (F : Fin w × Path → V → ℂ) (θ : Fin w × Path → V × V) (Q : RegCpl)
    (a b : Fin w × Path) (r : V) (hab : Indep a b) :
    cplLeafProduct F θ Q a b r =
    cplLeafProduct (fun z => F (rootPlacement a b z)) (fun z => θ (rootPlacement a b z)) Q (0,[]) (1,[]) r := by
  apply cplLeafProduct_relocate F (fun z => F (rootPlacement a b z)) θ _ Q a b (0,[]) (1,[]) r hab indep_roots
  · intro p
    simp [rootPlacement,addrExt]
  · intro p
    simp [rootPlacement,addrExt]

end WaveTurbulence.RA1Leafwise

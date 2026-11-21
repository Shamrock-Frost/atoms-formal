import Atoms.Diagrammatic.Rewriting.InftyCategory
import Atoms.Diagrammatic.Suspension.Hom

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram Simplicial

universe u v

namespace Atoms.Diagrammatic.Layered.RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]
  {hS : S.WellFormed} {X : DiagSet.{u}} (I : S.Interp hS X)

theorem RewriteChain.globularClass_eq (hX : IsInftyCategory 2 X) {d d' : Diagram S.Pt S.Ed S.Ce}
    (p : S.RewriteChain d d') {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q') (hsrc' : d'.source ≠ [])
    {x y : X.Vertex} {f g : X.Edge x y}
    (ep : Equivalent (I.pathRound d.source (S.isPath_source_of_target hq))
      (cellRound f.cell))
    (eq : Equivalent (I.pathRound q (S.isPath_target hS.1 hq))
      (cellRound g.cell))
    (hu : HasRoundType (I.toInterp.roundDiagram hS.1 hq hsrc).toPastingDiagram
      (I.pathRound d.source (S.isPath_source_of_target hq))
      (I.pathRound q (S.isPath_target hS.1 hq)))
    (hu' : HasRoundType (I.toInterp.roundDiagram hS.1 hq' hsrc').toPastingDiagram
      (I.pathRound d.source (S.isPath_source_of_target hq))
      (I.pathRound q (S.isPath_target hS.1 hq))) :
    globularClass hX ep eq (I.toInterp.roundDiagram hS.1 hq hsrc) hu =
      globularClass hX ep eq (I.toInterp.roundDiagram hS.1 hq' hsrc') hu' :=
  (globularClass_eq_iff hX ep eq _ _ hu hu').2 (p.equivalent_roundDiagram I
    (I.isEquivalence_rel_of_isInftyCategory hX le_rfl) hq hsrc hq' hsrc')

theorem RewriteChain.π₀_mk_eq (hX : IsInftyCategory 2 X) {d d' : Diagram S.Pt S.Ed S.Ce}
    (p : S.RewriteChain d d') {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q') (hsrc' : d'.source ≠ [])
    {x y : X.Vertex} {f g : X.Edge x y}
    (ep : Equivalent (I.pathRound d.source (S.isPath_source_of_target hq))
      (cellRound f.cell))
    (eq : Equivalent (I.pathRound q (S.isPath_target hS.1 hq))
      (cellRound g.cell))
    (hu : HasRoundType (I.toInterp.roundDiagram hS.1 hq hsrc).toPastingDiagram
      (I.pathRound d.source (S.isPath_source_of_target hq))
      (I.pathRound q (S.isPath_target hS.1 hq)))
    (hu' : HasRoundType (I.toInterp.roundDiagram hS.1 hq' hsrc').toPastingDiagram
      (I.pathRound d.source (S.isPath_source_of_target hq))
      (I.pathRound q (S.isPath_target hS.1 hq))) :
    SSet.π₀.mk (DiagSet.vertexEquivSSet _
        (((bipointedHom.obj (X.bipoint x y)).bipointedHomVerticesEquiv
          ((X.bipointedHomVerticesEquiv x y).symm f)
          ((X.bipointedHomVerticesEquiv x y).symm g)).symm
        (globularEdge hX ep eq (I.toInterp.roundDiagram hS.1 hq hsrc) hu))) =
      SSet.π₀.mk (DiagSet.vertexEquivSSet _
        (((bipointedHom.obj (X.bipoint x y)).bipointedHomVerticesEquiv
          ((X.bipointedHomVerticesEquiv x y).symm f)
          ((X.bipointedHomVerticesEquiv x y).symm g)).symm
        (globularEdge hX ep eq (I.toInterp.roundDiagram hS.1 hq' hsrc') hu'))) := by
  have hZ : IsInftyCategory 1 (bipointedHom.obj (X.bipoint x y)) :=
    isInftyCategory_bipointedHom (n := 1) hX
  apply ((bipointedHom.obj (X.bipoint x y)).bipointedHomπ₀Equiv hZ _ _).injective
  exact (DiagSet.bipointedHomπ₀Equiv_mk hZ _ _ _).trans
    ((p.globularClass_eq I hX hq hsrc hq' hsrc' ep eq hu hu').trans
      (DiagSet.bipointedHomπ₀Equiv_mk hZ _ _ _).symm)

theorem RewriteChain.globularClass_eq_id (hX : IsInftyCategory 2 X) {d : Diagram S.Pt S.Ed S.Ce}
    (p : S.RewriteChain d ⟨d.source, []⟩) (hq : S.target d = some d.source) (hsrc : d.source ≠ [])
    {x y : X.Vertex} {f : X.Edge x y}
    (ef : Equivalent (I.pathRound d.source (S.isPath_source_of_target hq))
      (cellRound f.cell))
    (hu : HasRoundType (I.toInterp.roundDiagram hS.1 hq hsrc).toPastingDiagram
      (I.pathRound d.source (S.isPath_source_of_target hq))
      (I.pathRound d.source (S.isPath_source_of_target hq))) :
    globularClass hX ef ef (I.toInterp.roundDiagram hS.1 hq hsrc) hu = 𝟙 _ := by
  have hq' : S.target ⟨d.source, []⟩ = some d.source :=
    S.target_mk_of_targetFrom (S.isPath_source_of_target hq) rfl
  refine (p.globularClass_eq I hX hq hsrc hq' hsrc ef ef hu
    (I.toInterp.hasRoundType_roundDiagram hS.1 hq' hsrc)).trans
    (globularClass_eq_id_of_equivalent hX ef _ _ (equivalent_of_equiv (PastingDiagram.equiv_of_eq
      (I.toInterp.diagram_unit_singleton hsrc))))

end Atoms.Diagrammatic.Layered.RelSignature

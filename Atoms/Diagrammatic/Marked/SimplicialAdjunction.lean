import Atoms.Diagrammatic.Marked.Basic
import Atoms.Diagrammatic.SimplicialAdjunction
import Atoms.Homotopical.Marked.SiteFunctor
import Atoms.Homotopical.Simplicial.Stratified
import Atoms.Shape.SimplexFace

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

theorem simplexFunctor_preservesMarking :
    Homotopical.MarkingData.PreservesMarking simplexMarking atomMarking simplexFunctor where
  markable n hn := by
    change 0 < (simplexFunctor.obj n).dimension
    rw [simplexFunctor_obj, dimension_atomSimplex]
    exact hn
  degenerate {m n} p hp := by
    obtain ⟨hp, hni⟩ := hp
    have := isSplitEpi_of_epi p
    exact .of_degeneracy ⟨isCollapseHom_of_isSplitEpi _,
      fun h => hni (isIso_of_reflects_iso p simplexFunctor)⟩

noncomputable def StratifiedSSet.toMarkedDiagSet : StratifiedSSet.{u} ⥤ MarkedDiagSet.{u} :=
  MarkedPresheaf.extendAlong simplexFunctor_preservesMarking

def MarkedDiagSet.toStratifiedSSet : MarkedDiagSet.{u} ⥤ StratifiedSSet.{u} :=
  MarkedPresheaf.restrictAlong simplexFunctor_preservesMarking

noncomputable def stratifiedMarkedDiagSetAdj :
    StratifiedSSet.toMarkedDiagSet.{u} ⊣ MarkedDiagSet.toStratifiedSSet.{u} :=
  MarkedPresheaf.extendAlongAdjunction simplexFunctor_preservesMarking

def toStratifiedSSetForgetIso :
    MarkedDiagSet.toStratifiedSSet.{u} ⋙ Homotopical.MarkedPresheaf.forget ≅
      Homotopical.MarkedPresheaf.forget ⋙ DiagSet.toSSet.{u} :=
  MarkedPresheaf.restrictAlongCompForgetIso simplexFunctor_preservesMarking

theorem mem_marked_toStratifiedSSet_iff (X : MarkedDiagSet.{u}) (n : SimplexCategory)
    (x : (MarkedDiagSet.toStratifiedSSet.obj X).underlying.obj (Opposite.op n)) :
    x ∈ (MarkedDiagSet.toStratifiedSSet.obj X).marked n ↔
      (toStratifiedSSetForgetIso.app X).hom.app (Opposite.op n) x ∈
        X.marked (simplexFunctor.obj n) := by
  refine (MarkedPresheaf.mem_marked_restrictAlong_iff _ X n x).trans
    ⟨And.right, fun h => ⟨?_, h⟩⟩
  have h0 : 0 < (simplexFunctor.obj n).dimension := X.markable _ _ h
  rw [simplexFunctor_obj, dimension_atomSimplex] at h0
  exact h0

noncomputable def toMarkedDiagSetForgetIso :
    StratifiedSSet.toMarkedDiagSet.{u} ⋙ Homotopical.MarkedPresheaf.forget ≅
      Homotopical.MarkedPresheaf.forget ⋙ SSet.toDiagSet.{u} :=
  MarkedPresheaf.extendAlongCompForgetIso simplexFunctor_preservesMarking sSetDiagSetAdj

instance preservesMonomorphisms_toMarkedDiagSet :
    StratifiedSSet.toMarkedDiagSet.{u}.PreservesMonomorphisms :=
  MarkedPresheaf.preservesMonomorphisms_extendAlong simplexFunctor_preservesMarking sSetDiagSetAdj

noncomputable def flatCompToMarkedDiagSetIso :
    Homotopical.MarkedPresheaf.flat simplexMarking ⋙ StratifiedSSet.toMarkedDiagSet.{u} ≅
      SSet.toDiagSet.{u} ⋙ Homotopical.MarkedPresheaf.flat atomMarking :=
  MarkedPresheaf.flatCompExtendAlongIso simplexFunctor_preservesMarking sSetDiagSetAdj

noncomputable def sharpCompToStratifiedSSetIso :
    Homotopical.MarkedPresheaf.sharp atomMarking ⋙ MarkedDiagSet.toStratifiedSSet.{u} ≅
      DiagSet.toSSet.{u} ⋙ Homotopical.MarkedPresheaf.sharp simplexMarking :=
  MarkedPresheaf.sharpCompRestrictAlongIso simplexFunctor_preservesMarking

end Atoms.Diagrammatic

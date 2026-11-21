import Atoms.Diagrammatic.FinalObjectComparison
import Atoms.Diagrammatic.Limits.ConeZigzag
import Atoms.Homotopical.Simplicial.EquivalenceZigzag

open CategoryTheory Limits Simplicial MonoidalCategory MonoidalClosed HomotopicalAlgebra
open Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

variable {X : DiagSet.{u}}

structure ConeComparisonData (hX : IsInftyCategory 1 X) (S : SSet.{u})
    (d : SSet.toDiagSet.obj S ⟶ X) where
  model : MarkedSSet.{u}
  isFibrant_model : IsFibrant model
  toModel : X ⟶ faceNerveRight.obj model
  weakEquivalence_toModel : WeakEquivalence ((DiagSet.toInfty 1).map toModel)

namespace ConeComparisonData

variable {hX : IsInftyCategory 1 X} {S : SSet.{u}} {d : SSet.toDiagSet.obj S ⟶ X}
  (D : ConeComparisonData hX S d)

theorem isInftyCategory_model : IsInftyCategory 1 (faceNerveRight.obj D.model) :=
  have := D.isFibrant_model
  isInftyCategory_faceNerveRight_obj D.model

private theorem weakEquivalence_toSSet_map_toModel :
    WeakEquivalence (DiagSet.toSSet.map D.toModel) := by
  have : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2 hX
  have : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj D.model)) :=
    (isFibrant_infty_iff 1 _).2 D.isInftyCategory_model
  have := D.weakEquivalence_toModel
  exact isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant
    ((DiagSet.toInfty 1).map D.toModel)

private theorem diagramPoint_comp_ihom_map_toModel :
    SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) ≫
        (ihom S).map (DiagSet.toSSet.map D.toModel) =
      SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map (d ≫ D.toModel)) :=
  (SSet.diagramPoint_comp_ihom_map (DiagSet.toSSet.map D.toModel) _).trans
    (congrArg SSet.diagramPoint ((Category.assoc _ _ _).trans
      (congrArg (_ ≫ ·) (DiagSet.toSSet.map_comp d D.toModel).symm)))

noncomputable def zigzag (α : Bool) :
    SSet.EquivalenceZigzag (DiagSet.toSSet.obj (coneObject α d))
      (SSet.commaObject α (SSet.constDiagram S (DiagSet.toSSet.obj X))
        (SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d))) where
  left := DiagSet.toSSet.obj (coneObject α (d ≫ D.toModel))
  mid := markedCommaObject α S (d ≫ D.toModel)
  right := SSet.commaObject α
    (SSet.constDiagram S (DiagSet.toSSet.obj (faceNerveRight.obj D.model)))
    (SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map (d ≫ D.toModel)))
  sourceToLeft := DiagSet.toSSet.map (coneObjectMap α d D.toModel)
  midToLeft := markedCommaToConeObject α S (d ≫ D.toModel)
  midToRight := markedCommaToCommaObject α S (d ≫ D.toModel)
  targetToRight := SSet.commaObjectMap α (DiagSet.toSSet.map D.toModel)
    ((ihom S).map (DiagSet.toSSet.map D.toModel))
    (SSet.constDiagram_comp_ihom_map (DiagSet.toSSet.map D.toModel) S)
    D.diagramPoint_comp_ihom_map_toModel
  quasicategory_source :=
    quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 (isInftyCategory_coneObject α d hX))
  quasicategory_left := quasicategory_toSSet_obj _
    ((isFibrant_infty_iff 1 _).2 (isInftyCategory_coneObject α _ D.isInftyCategory_model))
  quasicategory_mid :=
    have := D.isFibrant_model
    quasicategory_markedCommaObject α S _
  quasicategory_right :=
    have : (DiagSet.toSSet.obj (faceNerveRight.obj D.model)).Quasicategory :=
      quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 D.isInftyCategory_model)
    inferInstance
  quasicategory_target :=
    have : (DiagSet.toSSet.obj X).Quasicategory :=
      quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 hX)
    inferInstance
  weakEquivalence_sourceToLeft :=
    have := D.weakEquivalence_toModel
    weakEquivalence_toSSet_map_coneObjectMap α hX D.isInftyCategory_model d D.toModel
  weakEquivalence_midToLeft :=
    have := D.isFibrant_model
    weakEquivalence_markedCommaToConeObject α S _
  weakEquivalence_midToRight :=
    have := D.isFibrant_model
    weakEquivalence_markedCommaToCommaObject α S _
  weakEquivalence_targetToRight :=
    have := D.isFibrant_model
    have := D.weakEquivalence_toModel
    have : (DiagSet.toSSet.obj X).Quasicategory :=
      quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 hX)
    have : (DiagSet.toSSet.obj (faceNerveRight.obj D.model)).Quasicategory :=
      quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 D.isInftyCategory_model)
    have := D.weakEquivalence_toSSet_map_toModel
    have := weakEquivalence_ihom_map_toSSet_map S hX D.toModel
    SSet.modelCategoryJoyal.weakEquivalence_commaObjectMap α _ _ _ _

def Related (c : (coneObject true d).Vertex)
    (cS : (SSet.commaCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌) : Prop :=
  (D.zigzag true).Related ((coneObject true d).vertexEquivSSet c) cS

def RelatedCocone (c : (coneObject false d).Vertex)
    (cS : (SSet.commaCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌) : Prop :=
  (D.zigzag false).Related ((coneObject false d).vertexEquivSSet c) cS

theorem exists_related_simplicial (c : (coneObject true d).Vertex) :
    ∃ cS, D.Related c cS :=
  (D.zigzag true).exists_related_right _

theorem exists_related_native
    (cS : (SSet.commaCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌) :
    ∃ c, D.Related c cS :=
  (D.zigzag true).exists_related_left cS

theorem exists_relatedCocone_simplicial (c : (coneObject false d).Vertex) :
    ∃ cS, D.RelatedCocone c cS :=
  (D.zigzag false).exists_related_right _

theorem exists_relatedCocone_native
    (cS : (SSet.commaCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌) :
    ∃ c, D.RelatedCocone c cS :=
  (D.zigzag false).exists_related_left cS

theorem isoVertices_apex_of_related (α : Bool)
    {x : (DiagSet.toSSet.obj (coneObject α d)) _⦋0⦌}
    {y : (SSet.commaObject α (SSet.constDiagram S (DiagSet.toSSet.obj X))
      (SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d))) _⦋0⦌}
    (h : (D.zigzag α).Related x y) :
    SSet.IsoVertices ((DiagSet.toSSet.map (coneObjectπ α d)).app _ x)
      ((SSet.commaObjectπ α _ _).app _ y) := by
  have : (DiagSet.toSSet.obj X).Quasicategory :=
    quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 hX)
  have : (DiagSet.toSSet.obj (faceNerveRight.obj D.model)).Quasicategory :=
    quasicategory_toSSet_obj _ ((isFibrant_infty_iff 1 _).2 D.isInftyCategory_model)
  have := D.weakEquivalence_toSSet_map_toModel
  exact (D.zigzag α).isoVertices_of_related (DiagSet.toSSet.map D.toModel)
    (faceNerveRightComparison.app D.model) (DiagSet.toSSet.map (coneObjectπ α d))
    (DiagSet.toSSet.map (coneObjectπ α (d ≫ D.toModel))) (SSet.commaObjectπ α _ _)
    (SSet.commaObjectπ α _ _) (SSet.commaObjectπ α _ _)
    ((DiagSet.toSSet.map_comp _ _).symm.trans ((congrArg DiagSet.toSSet.map
      (coneObjectMap_π α d D.toModel)).trans (DiagSet.toSSet.map_comp _ _)))
    (markedCommaToConeObject_π α S _) (markedCommaToCommaObject_π α S _)
    (SSet.commaObjectMap_π α _ _ (SSet.constDiagram_comp_ihom_map (DiagSet.toSSet.map D.toModel) S)
      D.diagramPoint_comp_ihom_map_toModel) h

theorem isLimitCone_iff_of_related {c : (coneObject true d).Vertex}
    {cS : (SSet.commaCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌}
    (h : D.Related c cS) :
    IsLimitCone true d c ↔
      SSet.IsLimitCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) cS :=
  (DiagSet.isFinalObject_iff_isFinal (isInftyCategory_coneObject true d hX) c).trans
    ((D.zigzag true).isFinal_iff_of_related h)

theorem isColimitCone_iff_of_relatedCocone {c : (coneObject false d).Vertex}
    {cS : (SSet.commaCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌}
    (h : D.RelatedCocone c cS) :
    IsLimitCone false d c ↔
      SSet.IsColimitCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) cS :=
  (DiagSet.isInitialObject_iff_isInitialObject (isInftyCategory_coneObject false d hX) c).trans
    ((D.zigzag false).isInitialObject_iff_of_related h)

end ConeComparisonData

noncomputable def coneComparison (hX : IsInftyCategory 1 X) (S : SSet.{u})
    (d : SSet.toDiagSet.obj S ⟶ X) : ConeComparisonData hX S d where
  model := (exists_weakEquivalence_faceNerveRight X).choose
  isFibrant_model := (exists_weakEquivalence_faceNerveRight X).choose_spec.choose
  toModel := (exists_weakEquivalence_faceNerveRight X).choose_spec.choose_spec.choose
  weakEquivalence_toModel :=
    (exists_weakEquivalence_faceNerveRight X).choose_spec.choose_spec.choose_spec.1

theorem isLimitCone_iff_simplicial (hX : IsInftyCategory 1 X) (S : SSet.{u})
    (d : SSet.toDiagSet.obj S ⟶ X) (c : (coneObject true d).Vertex)
    (cS : (SSet.commaCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌)
    (hc : (coneComparison hX S d).Related c cS) :
    IsLimitCone true d c ↔
      SSet.IsLimitCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) cS :=
  (coneComparison hX S d).isLimitCone_iff_of_related hc

theorem isColimitCone_iff_simplicial (hX : IsInftyCategory 1 X) (S : SSet.{u})
    (d : SSet.toDiagSet.obj S ⟶ X) (c : (coneObject false d).Vertex)
    (cS : (SSet.commaCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d)) _⦋0⦌)
    (hc : (coneComparison hX S d).RelatedCocone c cS) :
    IsLimitCone false d c ↔
      SSet.IsColimitCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) cS :=
  (coneComparison hX S d).isColimitCone_iff_of_relatedCocone hc

theorem exists_isLimitCone_iff_simplicial (hX : IsInftyCategory 1 X) (S : SSet.{u})
    (d : SSet.toDiagSet.obj S ⟶ X) :
    (∃ c, IsLimitCone true d c) ↔
      ∃ cS, SSet.IsLimitCone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) cS :=
  ⟨fun ⟨c, hc⟩ ↦ ((coneComparison hX S d).exists_related_simplicial c).imp fun cS h ↦
      (isLimitCone_iff_simplicial hX S d c cS h).1 hc,
    fun ⟨cS, hcS⟩ ↦ ((coneComparison hX S d).exists_related_native cS).imp fun c h ↦
      (isLimitCone_iff_simplicial hX S d c cS h).2 hcS⟩

theorem exists_isColimitCone_iff_simplicial (hX : IsInftyCategory 1 X) (S : SSet.{u})
    (d : SSet.toDiagSet.obj S ⟶ X) :
    (∃ c, IsLimitCone false d c) ↔
      ∃ cS, SSet.IsColimitCocone (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) cS :=
  ⟨fun ⟨c, hc⟩ ↦ ((coneComparison hX S d).exists_relatedCocone_simplicial c).imp fun cS h ↦
      (isColimitCone_iff_simplicial hX S d c cS h).1 hc,
    fun ⟨cS, hcS⟩ ↦ ((coneComparison hX S d).exists_relatedCocone_native cS).imp fun c h ↦
      (isColimitCone_iff_simplicial hX S d c cS h).2 hcS⟩

end Atoms.Diagrammatic

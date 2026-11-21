import Atoms.Diagrammatic.GrayCylinder.Exact
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.Equivalence
import Atoms.TestCategory.CylinderTest
import Atoms.TestCategory.Localizer.ModelStructure
import Atoms.TestCategory.Presheaf.Transport

open CategoryTheory Limits MorphismProperty Atoms.Shape Atoms.Diagrammatic HomotopicalAlgebra

universe u

namespace Atoms.TestCategory

def BasicLocalizer.wDiagSet (𝒲 : BasicLocalizer.{u}) : MorphismProperty DiagSet.{u} :=
  (𝒲.wPsh (AsSmall.{u} Atom)).inverseImage DiagSet.asSmall

theorem BasicLocalizer.wDiagSet_iff (𝒲 : BasicLocalizer.{u}) {X Y : DiagSet.{u}} (f : X ⟶ Y) :
    𝒲.wDiagSet f ↔ 𝒲.wPsh (AsSmall.{u} Atom) (DiagSet.asSmall.map f) :=
  Iff.rfl

theorem BasicLocalizer.wDiagSet_eq_wPsh (𝒲 : BasicLocalizer.{0}) :
    𝒲.wDiagSet = 𝒲.wPsh Atom := by
  rw [𝒲.wPsh_eq_inverseImage_presheafEquivalence (AsSmall.equiv : Atom ≌ AsSmall.{0} Atom)]
  rfl

end Atoms.TestCategory

namespace Atoms.Diagrammatic

noncomputable abbrev smallGrayCylinder : ExactCylinder.{u} ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u) :=
  grayExactCylinder.{u}.transport DiagSet.asSmallEquivalence

end Atoms.Diagrammatic

namespace Atoms.TestCategory.BasicLocalizer

theorem wDiagSet_uliftYoneda_map (𝒲 : BasicLocalizer.{u}) {a b : Atom} (f : a ⟶ b) :
    𝒲.wDiagSet (uliftYoneda.{u}.map f) :=
  ((𝒲.wPsh _).arrow_mk_iso_iff (Arrow.isoMk (DiagSet.asSmallBallIso a)
    (DiagSet.asSmallBallIso b) rfl)).2
    (𝒲.wPsh_yoneda_map _ (AsSmall.up.map f))

theorem wDiagSet_grayCylinderContraction_app_ball (𝒲 : BasicLocalizer.{u}) (U : Atom) :
    𝒲.wDiagSet (grayExactCylinder.{u}.contraction.app (ball U)) := by
  change 𝒲.wDiagSet (grayCylinderContraction.app (ball U))
  rw [grayCylinderContraction_app_ball, 𝒲.wDiagSet_iff, Functor.map_comp]
  exact (𝒲.wPsh _).comp_mem _ _ (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _
    inferInstance) (𝒲.wDiagSet_uliftYoneda_map _)

private theorem wPsh_smallGrayCylinder_contraction_app_yoneda (𝒲 : BasicLocalizer.{u})
    (a : AsSmall.{u} Atom) :
    𝒲.wPsh _ (smallGrayCylinder.{u}.contraction.app (yoneda.obj a)) :=
  (𝒲.wPsh _).comp_mem _ _ (𝒲.wDiagSet_grayCylinderContraction_app_ball (AsSmall.down.obj a))
    (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ inferInstance)

theorem cylinderCompatibleWith_smallGrayCylinder (𝒲 : BasicLocalizer.{u}) :
    CylinderCompatibleWith ((AsSmall.{u} Atom)ᵒᵖ ⥤ Type u) (𝒲.wPsh (AsSmall.{u} Atom))
      smallGrayCylinder.{u} :=
  𝒲.cylinderCompatibleWith_of_forall_yoneda smallGrayCylinder
    𝒲.wPsh_smallGrayCylinder_contraction_app_yoneda

instance isTest_asSmallAtom (𝒲 : BasicLocalizer.{u}) : 𝒲.IsTest (AsSmall.{u} Atom) :=
  𝒲.isTest_of_forall_yoneda 𝒲.aspherical_asSmallAtom smallGrayCylinder
    𝒲.wPsh_smallGrayCylinder_contraction_app_yoneda

instance isALocalizer_wDiagSet (𝒲 : BasicLocalizer.{u}) : Homotopical.IsALocalizer 𝒲.wDiagSet :=
  Homotopical.IsALocalizer.inverseImage_asSmall_functor (V := 𝒲.wPsh (AsSmall.{u} Atom))

theorem cylinderCompatibleWith_wDiagSet_grayExactCylinder (𝒲 : BasicLocalizer.{u}) :
    CylinderCompatibleWith DiagSet.{u} 𝒲.wDiagSet grayExactCylinder.{u} := fun X ↦ by
  let e := DiagSet.asSmallEquivalence.{u}
  have h : 𝒲.wDiagSet (grayExactCylinder.contraction.app (e.inverse.obj (e.functor.obj X))) :=
    MorphismProperty.of_postcomp (𝒲.wPsh _) _ _
      (isomorphisms_le_of_containsIdentities (𝒲.wPsh _) _ (e.counitIso.app _).isIso_hom)
      (𝒲.cylinderCompatibleWith_smallGrayCylinder (e.functor.obj X))
  exact (𝒲.wDiagSet.arrow_mk_iso_iff (Arrow.isoMk (grayExactCylinder.I.mapIso (e.unitIso.app X))
    (e.unitIso.app X) (grayExactCylinder.contraction.naturality _))).2 h

theorem wPsh_grayCylinderContraction_app_ball (𝒲 : BasicLocalizer.{0})
    (U : Atom) : 𝒲.wPsh Atom (grayExactCylinder.contraction.app (ball U)) :=
  𝒲.wDiagSet_eq_wPsh ▸ 𝒲.wDiagSet_grayCylinderContraction_app_ball U

theorem cylinderCompatibleWith_grayExactCylinder (𝒲 : BasicLocalizer.{0}) :
    HomotopicalAlgebra.CylinderCompatibleWith (Atomᵒᵖ ⥤ Type) (𝒲.wPsh Atom) grayExactCylinder :=
  𝒲.wDiagSet_eq_wPsh ▸ 𝒲.cylinderCompatibleWith_wDiagSet_grayExactCylinder

instance atom_isTest (𝒲 : BasicLocalizer.{0}) : 𝒲.IsTest Atom :=
  (𝒲.isTest_iff_of_equivalence AsSmall.equiv).2 inferInstance

theorem isAccessibleALocalizer_wDiagSet (𝒲 : BasicLocalizer.{u}) (hW : 𝒲.IsAccessible) :
    Homotopical.IsAccessibleALocalizer 𝒲.wDiagSet :=
  have := 𝒲.isAccessibleALocalizer_wPsh (AsSmall.{u} Atom) hW
  Homotopical.IsAccessibleALocalizer.inverseImage_asSmall_functor
    (V := 𝒲.wPsh (AsSmall.{u} Atom))

theorem exists_generators_wDiagSet (𝒲 : BasicLocalizer.{u})
    (𝕀 : HomotopicalAlgebra.ExactCylinder.{u} DiagSet.{u}) (hW : 𝒲.IsAccessible)
    (hI : HomotopicalAlgebra.CylinderCompatibleWith DiagSet.{u} 𝒲.wDiagSet 𝕀) :
    ∃ S : MorphismProperty DiagSet.{u},
      MorphismProperty.IsSmall.{u} S ∧ S ≤ MorphismProperty.monomorphisms DiagSet.{u} ∧
        𝕀.weakEquivalences S = 𝒲.wDiagSet :=
  (𝒲.isAccessibleALocalizer_wDiagSet hW).exists_weakEquivalences_eq 𝕀 hI

theorem exists_generators_grayExactCylinder (𝒲 : BasicLocalizer.{0})
    (hW : 𝒲.IsAccessible) :
    ∃ S : MorphismProperty DiagSet.{0},
      MorphismProperty.IsSmall.{0} S ∧ S ≤ MorphismProperty.monomorphisms DiagSet.{0} ∧
        grayExactCylinder.weakEquivalences S = 𝒲.wPsh Atom :=
  𝒲.exists_generators_of_isLocalTest Atom grayExactCylinder hW
    𝒲.cylinderCompatibleWith_grayExactCylinder

end Atoms.TestCategory.BasicLocalizer

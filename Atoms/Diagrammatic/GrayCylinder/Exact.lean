import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Atoms.Diagrammatic.GrayCylinder.Sphere
import Atoms.Homotopical.Cylinder.ModelStructure

open CategoryTheory Limits Opposite Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape HomotopicalAlgebra

universe u

namespace Atoms.Diagrammatic

theorem injective_grayCylinderEndpoint_app (ε : Bool) (X : DiagSet.{u}) (T : Atomᵒᵖ) :
    Function.Injective (((grayCylinderEndpoint ε).app X).app T) := by
  refine Function.LeftInverse.injective (g := (grayCylinderContraction.app X).app T) fun x => ?_
  have h := NatTrans.congr_app (grayCylinderEndpoint_grayCylinderContraction ε) X
  have h' := congr_fun (congrArg (fun f : X ⟶ X => (f.app T : X.obj T → X.obj T)) h) x
  simpa using h'

def globeOneSeparator : DiagSet.{u} where
  obj T := T.unop.ogp → ULift.{u} (globe.{0} 1)
  map f := ↾(fun φ => φ ∘ f.unop)
  map_id _ := rfl
  map_comp _ _ := rfl

def grayFirstCoordinate (X : DiagSet.{u}) : X ⟶ grayCylinder.op ⋙ globeOneSeparator.{u} where
  app U := ↾(fun _ z => ⟨((cylAtomIso U.unop).inv z).1⟩)
  naturality U V g := by
    ext x
    funext z
    exact congrArg ULift.up (congrArg Prod.fst (symm_grayCylinder_map_apply g.unop z)).symm

noncomputable def grayCylinderSeparator (X : DiagSet.{u}) :
    grayCylinderFunctor.obj X ⟶ globeOneSeparator :=
  (grayCylinderFunctor.obj X).descOfIsLeftKanExtension (grayCylinderUnit X) globeOneSeparator
    (grayFirstCoordinate X)

theorem grayCylinderSeparator_app_grayCylinderUnit_app (X : DiagSet.{u}) (U : Atomᵒᵖ)
    (x : X.obj U) :
    (grayCylinderSeparator X).app (op (grayCylinder.obj U.unop)) ((grayCylinderUnit X).app U x) =
      (grayFirstCoordinate X).app U x :=
  ConcreteCategory.congr_hom
    ((grayCylinderFunctor.obj X).descOfIsLeftKanExtension_fac_app (grayCylinderUnit X)
      globeOneSeparator (grayFirstCoordinate X) U) x

theorem grayCylinderSeparator_app_grayCylinderEndpoint_app (ε : Bool) (X : DiagSet.{u})
    (T : Atomᵒᵖ) (x : X.obj T) (t : T.unop.ogp) :
    (grayCylinderSeparator X).app T (((grayCylinderEndpoint ε).app X).app T x) t =
      ⟨SuspCarrier.pole ε⟩ := by
  change (grayCylinderSeparator X).app T ((grayCylinderFunctor.obj X).map
    ((grayEndpoint ε).app T.unop).op ((grayCylinderUnit X).app T x)) t = _
  rw [NatTrans.naturality_apply, grayCylinderSeparator_app_grayCylinderUnit_app]
  exact congrArg ULift.up (congrArg Prod.fst (symm_grayEndpoint_apply ε T.unop t))

theorem grayCylinderEndpoint_app_false_ne_true (X : DiagSet.{u}) (T : Atomᵒᵖ) (x y : X.obj T) :
    ((grayCylinderEndpoint false).app X).app T x ≠ ((grayCylinderEndpoint true).app X).app T y :=
  fun h => by
    have h' := congrArg (fun w => (grayCylinderSeparator X).app T w T.unop.top) h
    have e := (grayCylinderSeparator_app_grayCylinderEndpoint_app false X T x T.unop.top).symm.trans
      (h'.trans (grayCylinderSeparator_app_grayCylinderEndpoint_app true X T y T.unop.top))
    nomatch congrArg ULift.down e

instance mono_grayCylinderEndpoints (X : DiagSet.{u}) :
    Mono (Limits.coprod.desc ((grayCylinderEndpoint false).app X)
      ((grayCylinderEndpoint true).app X)) := by
  have e : Limits.coprod.desc ((grayCylinderEndpoint false).app X)
      ((grayCylinderEndpoint true).app X) =
      (FunctorToTypes.binaryCoproductIso X X).hom ≫ FunctorToTypes.coprod.desc
        ((grayCylinderEndpoint false).app X) ((grayCylinderEndpoint true).app X) := by
    ext1
    · rw [coprod.inl_desc, ← Category.assoc]
      erw [FunctorToTypes.inl_comp_binaryCoproductIso_hom]
      rfl
    · rw [coprod.inr_desc, ← Category.assoc]
      erw [FunctorToTypes.inr_comp_binaryCoproductIso_hom]
      rfl
  have hm : Mono (FunctorToTypes.coprod.desc ((grayCylinderEndpoint false).app X)
      ((grayCylinderEndpoint true).app X)) := by
    rw [NatTrans.mono_iff_mono_app]
    intro T
    rw [mono_iff_injective]
    rintro (x | x) (y | y) h
    · rw [injective_grayCylinderEndpoint_app false X T h]
    · exact (grayCylinderEndpoint_app_false_ne_true X T x y h).elim
    · exact (grayCylinderEndpoint_app_false_ne_true X T y x h.symm).elim
    · rw [injective_grayCylinderEndpoint_app true X T h]
  rw [e]
  exact mono_comp _ _

end Atoms.Diagrammatic

open CategoryTheory Limits Atoms.Shape

namespace Atoms.Diagrammatic

theorem sphereInclusions_le_inverseImage_grayCylinderFunctor :
    sphereInclusions ≤
      (MorphismProperty.monomorphisms DiagSet.{u}).inverseImage grayCylinderFunctor :=
  (MorphismProperty.ofHoms_le_iff _ _).2 mono_grayCylinderFunctor_map_sphereInclusion

theorem mono_grayCylinderFunctor_map {X Y : DiagSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (grayCylinderFunctor.map f) := by
  have hf : MorphismProperty.monomorphisms DiagSet.{u} f :=
    MorphismProperty.monomorphisms.infer_property f
  rw [monomorphisms_eq_saturation_sphereInclusions] at hf
  exact MorphismProperty.saturation_le _ _ sphereInclusions_le_inverseImage_grayCylinderFunctor f hf

noncomputable def grayExactCylinder : HomotopicalAlgebra.ExactCylinder.{u} (Atomᵒᵖ ⥤ Type u) where
  I := grayCylinderFunctor
  endpoint := grayCylinderEndpoint
  contraction := grayCylinderContraction
  endpoint_contraction := grayCylinderEndpoint_grayCylinderContraction
  mono_endpoints := mono_grayCylinderEndpoints
  preservesMonomorphisms := ⟨fun f _ ↦ mono_grayCylinderFunctor_map f⟩

theorem exists_exactCylinder_yoneda_iso_grayCylinder :
    ∃ (𝕀 : HomotopicalAlgebra.ExactCylinder.{u} (Atomᵒᵖ ⥤ Type u))
      (e : uliftYoneda.{u} ⋙ 𝕀.I ≅ grayCylinder ⋙ uliftYoneda.{u}),
      ∀ (ε : Bool) (U : Atom),
        (𝕀.endpoint ε).app (ball U) ≫ e.hom.app U =
          uliftYoneda.{u}.map ((grayEndpoint ε).app U) :=
  ⟨grayExactCylinder, grayCylinderFunctorYonedaIso, grayCylinderEndpoint_app_ball⟩

end Atoms.Diagrammatic

import Atoms.Diagrammatic.ClosedSubpresheaf
import Atoms.Diagrammatic.GrayCylinder.Functor

open CategoryTheory Limits Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

noncomputable def cylinderLift (U : Atom) (x : U.ogp) {T : Atom}
    (f : T ⟶ grayCylinder.obj U) (h : ∀ t, ((cylAtomIso U).inv (f t)).2 ≤ x) :
    T ⟶ grayCylinder.obj (Atom.ofClosure U x) :=
  liftOfIsInclusionHom _
    (isInclusionHom_grayCylinder_map _ (Atom.isInclusionHom_closureIncl U x)) f
    (exists_grayCylinder_map_closureIncl_eq U x f h)

theorem cylinderLift_comp_grayCylinder_map (U : Atom) (x : U.ogp) {T : Atom}
    (f : T ⟶ grayCylinder.obj U) (h : ∀ t, ((cylAtomIso U).inv (f t)).2 ≤ x) :
    cylinderLift U x f h ≫ grayCylinder.map (Atom.closureIncl U x) = f :=
  liftOfIsInclusionHom_comp _ _ _ _

private theorem range_le_closedSubpresheaf_cylinderSubset (U : Atom) (S : LowerSet U.ogp) (x : S) :
    Subfunctor.range (uliftYoneda.{u}.map (grayCylinder.map (Atom.closureIncl U x.1))) ≤
      closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S) := by
  rintro ⟨T⟩ _ ⟨⟨g⟩, rfl⟩
  exact comp_grayCylinder_map_closureIncl_mem U S x g

def cylinderCocone (U : Atom) (S : LowerSet U.ogp) :
    Limits.Cocone (principalDiagram U S ⋙ grayCylinder ⋙ uliftYoneda.{u}) where
  pt := (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).toFunctor
  ι :=
    { app x := Subfunctor.lift (uliftYoneda.{u}.map (grayCylinder.map (Atom.closureIncl U x.1)))
        (range_le_closedSubpresheaf_cylinderSubset U S x)
      naturality _ _ f :=
        (cancel_mono (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).ι).1 <|
          ((Category.assoc _ _ _).trans <| (congrArg (_ ≫ ·) (Subfunctor.lift_ι _ _)).trans <|
            (uliftYoneda.{u}.map_comp _ _).symm.trans <| congrArg uliftYoneda.{u}.map <|
              (grayCylinder.map_comp _ _).symm.trans <|
                congrArg grayCylinder.map (principalMap_comp_closureIncl U (leOfHom f))).trans
          ((Subfunctor.lift_ι _ _).symm.trans (congrArg (· ≫ _) (Category.comp_id _).symm)) }

theorem cylinderCocone_ι_app_comp_ι (U : Atom) (S : LowerSet U.ogp) (x : S) :
    (cylinderCocone U S).ι.app x ≫
        (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).ι =
      uliftYoneda.{u}.map (grayCylinder.map (Atom.closureIncl U x.1)) :=
  rfl

theorem ιColimitType_eq_ιColimitType_cylinderLift (U : Atom) (S : LowerSet U.ogp)
    (T : Atom) (x y : S) (g : T ⟶ grayCylinder.obj (Atom.ofClosure U x.1))
    (f : T ⟶ grayCylinder.obj U) (hy : ((cylAtomIso U).inv (f T.top)).2 = y.1)
    (hgf : g ≫ grayCylinder.map (Atom.closureIncl U x.1) = f) :
    ((principalDiagram U S ⋙ grayCylinder ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType x ⟨g⟩ =
      ((principalDiagram U S ⋙ grayCylinder ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType y
        ⟨cylinderLift U y.1 f fun t => hy ▸ snd_symm_le_snd_symm_top f t⟩ := by
  subst hgf
  have hzx : y.1 ≤ x.1 :=
    hy ▸ (congrArg (fun p : grayProduct (globe 1) U.ogp => p.2 ≤ x.1)
      (symm_grayCylinder_map_apply (Atom.closureIncl U x.1) (g T.top))).mpr
      (closureIncl_mem_closure U x.1 _)
  refine (Functor.ιColimitType_eq_iff _ _ _).2
    (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ ⟨homOfLE hzx, ?_⟩))
  change ULift.up g = ULift.up (cylinderLift U y.1 (g ≫ grayCylinder.map (Atom.closureIncl U x.1))
    (fun t => hy ▸ snd_symm_le_snd_symm_top _ t) ≫
      grayCylinder.map (principalMap U (leOfHom (homOfLE hzx))))
  have := mono_of_isInclusionHom _
    (isInclusionHom_grayCylinder_map _ (Atom.isInclusionHom_closureIncl U x.1))
  refine congrArg ULift.up ((cancel_mono (grayCylinder.map (Atom.closureIncl U x.1))).1 ?_)
  rw [Category.assoc, ← grayCylinder.map_comp, principalMap_comp_closureIncl,
    cylinderLift_comp_grayCylinder_map]

theorem bijective_descColimitType_cylinderCocone (U : Atom) (S : LowerSet U.ogp)
    (T : Atomᵒᵖ) :
    Function.Bijective (Functor.descColimitType _
      ((Functor.coconeTypesEquiv _).symm
        (((evaluation Atomᵒᵖ (Type u)).obj T).mapCocone (cylinderCocone U S)))) := by
  induction T with | op T => ?_
  refine ⟨fun a b hab => ?_, ?_⟩
  · obtain ⟨x, ⟨g⟩, rfl⟩ := Functor.ιColimitType_jointly_surjective _ a
    obtain ⟨y, ⟨g'⟩, rfl⟩ := Functor.ιColimitType_jointly_surjective _ b
    change T ⟶ grayCylinder.obj (Atom.ofClosure U x.1) at g
    change T ⟶ grayCylinder.obj (Atom.ofClosure U y.1) at g'
    change (⟨⟨g ≫ grayCylinder.map (Atom.closureIncl U x.1)⟩,
        comp_grayCylinder_map_closureIncl_mem U S x g⟩ :
        (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).obj (op T)) =
      ⟨⟨g' ≫ grayCylinder.map (Atom.closureIncl U y.1)⟩,
        comp_grayCylinder_map_closureIncl_mem U S y g'⟩ at hab
    have h : g ≫ grayCylinder.map (Atom.closureIncl U x.1) =
        g' ≫ grayCylinder.map (Atom.closureIncl U y.1) :=
      congrArg ULift.down (Subtype.mk.inj hab)
    let z : S := ⟨_, (mem_cylinderSubset_iff U S _).1
      (comp_grayCylinder_map_closureIncl_mem U S y g' T.top)⟩
    have e1 := ιColimitType_eq_ιColimitType_cylinderLift U S T x z g
      (g' ≫ grayCylinder.map (Atom.closureIncl U y.1)) rfl h
    have e2 := ιColimitType_eq_ιColimitType_cylinderLift U S T y z g'
      (g' ≫ grayCylinder.map (Atom.closureIncl U y.1)) rfl rfl
    exact e1.trans e2.symm
  · intro p
    change (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).obj (op T) at p
    obtain ⟨⟨f⟩, hf⟩ := p
    change T ⟶ grayCylinder.obj U at f
    have hf' : ∀ t, f t ∈ cylinderSubset U S :=
      (mem_closedSubpresheaf_iff.{u} (grayCylinder.obj U) (cylinderSubset U S) f).1 hf
    refine ⟨((principalDiagram U S ⋙ grayCylinder ⋙ uliftYoneda.{u}) ⋙
        (evaluation Atomᵒᵖ (Type u)).obj (op T)).ιColimitType
      ⟨((cylAtomIso U).inv (f T.top)).2, (mem_cylinderSubset_iff U S _).1 (hf' _)⟩
      ⟨cylinderLift U _ f (snd_symm_le_snd_symm_top f)⟩, ?_⟩
    exact Subtype.ext (congrArg ULift.up
      (cylinderLift_comp_grayCylinder_map U _ f (snd_symm_le_snd_symm_top f)))

noncomputable def isColimitCylinderCocone (U : Atom) (S : LowerSet U.ogp) :
    Limits.IsColimit (cylinderCocone.{u} U S) :=
  evaluationJointlyReflectsColimits _ fun T => Nonempty.some <|
    (Types.isColimit_iff_coconeTypesIsColimit _).2
      ⟨bijective_descColimitType_cylinderCocone U S T⟩

noncomputable def cylinderDiagramIso (U : Atom) (S : LowerSet U.ogp) :
    (principalDiagram U S ⋙ uliftYoneda.{u}) ⋙ grayCylinderFunctor ≅
      principalDiagram U S ⋙ grayCylinder ⋙ uliftYoneda.{u} :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (principalDiagram U S) grayCylinderFunctorYonedaIso

noncomputable def isColimitGrayCylinderFunctorMapCocone (U : Atom) (S : LowerSet U.ogp) :
    Limits.IsColimit ((Cocone.precompose (cylinderDiagramIso.{u} U S).inv).obj
      (grayCylinderFunctor.mapCocone (principalCocone U S))) :=
  (IsColimit.precomposeHomEquiv (cylinderDiagramIso U S).symm _).symm
    (isColimitOfPreserves grayCylinderFunctor (isColimitPrincipalCocone U S))

noncomputable def grayCylinderFunctorClosedSubpresheafIso (U : Atom) (S : LowerSet U.ogp) :
    grayCylinderFunctor.{u}.obj (closedSubpresheaf U S).toFunctor ≅
      (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).toFunctor :=
  (isColimitGrayCylinderFunctorMapCocone U S).coconePointUniqueUpToIso
    (isColimitCylinderCocone U S)

theorem grayCylinderFunctor_map_closedSubpresheaf_ι (U : Atom) (S : LowerSet U.ogp) :
    grayCylinderFunctor.{u}.map (closedSubpresheaf U S).ι =
      (grayCylinderFunctorClosedSubpresheafIso U S).hom ≫
        (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).ι ≫
          (grayCylinderFunctorYonedaIso.app U).inv := by
  refine (isColimitGrayCylinderFunctorMapCocone U S).hom_ext fun x => ?_
  have h1 : ((Cocone.precompose (cylinderDiagramIso U S).inv).obj
      (grayCylinderFunctor.mapCocone (principalCocone U S))).ι.app x ≫
        (grayCylinderFunctorClosedSubpresheafIso U S).hom = (cylinderCocone U S).ι.app x :=
    IsColimit.comp_coconePointUniqueUpToIso_hom _ _ x
  have h2 : ((Cocone.precompose (cylinderDiagramIso U S).inv).obj
      (grayCylinderFunctor.mapCocone (principalCocone U S))).ι.app x =
        (grayCylinderFunctorYonedaIso.app (Atom.ofClosure U x.1)).inv ≫
          grayCylinderFunctor.map ((principalCocone U S).ι.app x) := by
    simp [cylinderDiagramIso]
    rfl
  have h3 : grayCylinderFunctor.map ((principalCocone U S).ι.app x) ≫
      grayCylinderFunctor.map (closedSubpresheaf U S).ι =
        grayCylinderFunctor.map (uliftYoneda.{u}.map (Atom.closureIncl U x.1)) :=
    (grayCylinderFunctor.map_comp _ _).symm.trans
      (congrArg grayCylinderFunctor.map (principalCocone_ι_app_comp_ι U S x))
  have h4 : (grayCylinderFunctorYonedaIso.app (Atom.ofClosure U x.1)).inv ≫
      grayCylinderFunctor.map (uliftYoneda.{u}.map (Atom.closureIncl U x.1)) =
        uliftYoneda.{u}.map (grayCylinder.map (Atom.closureIncl U x.1)) ≫
          (grayCylinderFunctorYonedaIso.app U).inv :=
    (grayCylinderFunctorYonedaIso.inv.naturality (Atom.closureIncl U x.1)).symm
  exact (congrArg (· ≫ grayCylinderFunctor.map (closedSubpresheaf U S).ι) h2).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h3).trans (h4.trans
      ((congrArg (· ≫ (grayCylinderFunctorYonedaIso.app U).inv)
        ((cylinderCocone_ι_app_comp_ι U S x).symm.trans
          (congrArg (· ≫ (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).ι)
            h1.symm))).trans
        ((Category.assoc _ _ _).trans (Category.assoc _ _ _))))))

theorem mono_grayCylinderFunctor_map_closedSubpresheaf_ι (U : Atom)
    (S : LowerSet U.ogp) :
    Mono (grayCylinderFunctor.{u}.map (closedSubpresheaf U S).ι) := by
  rw [grayCylinderFunctor_map_closedSubpresheaf_ι U S]
  have h1 : Mono (grayCylinderFunctorClosedSubpresheafIso U S).hom := inferInstance
  have h2 : Mono (closedSubpresheaf (grayCylinder.obj U) (cylinderSubset U S)).ι := inferInstance
  have h3 : Mono (grayCylinderFunctorYonedaIso.app U).inv := inferInstance
  exact mono_comp' h1 (mono_comp' h2 h3)

instance mono_grayCylinderFunctor_map_sphereInclusion (U : Atom) :
    Mono (grayCylinderFunctor.map (sphereInclusion.{u} U)) := by
  have key : ∀ B : Subfunctor (ball U), closedSubpresheaf U (U.ogp.bdryFull ⊤) = B →
      Mono (grayCylinderFunctor.map B.ι) := by
    rintro B rfl
    exact mono_grayCylinderFunctor_map_closedSubpresheaf_ι U (U.ogp.bdryFull ⊤)
  exact key _ (closedSubpresheaf_univ_erase_top U)

end Atoms.Diagrammatic

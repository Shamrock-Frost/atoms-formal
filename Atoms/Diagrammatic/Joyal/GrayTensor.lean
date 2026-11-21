import Atoms.Diagrammatic.GrayTensor
import Atoms.Diagrammatic.Joyal.Comparison
import Atoms.Shape.GrayTensorMonoidal

open CategoryTheory Limits Opposite Simplicial
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe u

namespace Atoms.Diagrammatic

theorem rdcFaceNerve_map_atomGrayProductIso_hom_fst (U V : Atom) :
    rdcFaceNerve.{u}.map (atomGrayProductIso U V).hom ≫
        (rdcFaceNerveGrayProductIso _ _).hom ≫ prod.fst =
      rdcFaceNerve.map (atomToRDCpx.map (Atom.grayTensorFst U V)) := by
  refine MarkedPresheaf.hom_ext ?_
  rw [Functor.map_comp, forget_map_rdcFaceNerveGrayProductIso_hom_fst]
  exact nerveMap_functor_eq (X := ULift.{u} (Atom.grayTensor U V).ogp) (Y := ULift.{u} U.ogp)
    (f := fun z => ULift.up ((Atom.grayTensorIso U V).inv z.down).1)
    (g := fun z => ULift.up (Atom.grayTensorFst U V z.down))
    (fun _ _ h => ((isMorphism (Atom.grayTensorIso U V).inv).monotone h).1)
    (fun _ _ h => (Atom.isMap (Atom.grayTensorFst U V)).monotone h)
    fun z => ULift.ext _ _ (Atom.grayTensorFst_apply U V z.down).symm

theorem rdcFaceNerve_map_atomGrayProductIso_hom_snd (U V : Atom) :
    rdcFaceNerve.{u}.map (atomGrayProductIso U V).hom ≫
        (rdcFaceNerveGrayProductIso _ _).hom ≫ prod.snd =
      rdcFaceNerve.map (atomToRDCpx.map (Atom.grayTensorSnd U V)) := by
  refine MarkedPresheaf.hom_ext ?_
  rw [Functor.map_comp, forget_map_rdcFaceNerveGrayProductIso_hom_snd]
  exact nerveMap_functor_eq (X := ULift.{u} (Atom.grayTensor U V).ogp) (Y := ULift.{u} V.ogp)
    (f := fun z => ULift.up ((Atom.grayTensorIso U V).inv z.down).2)
    (g := fun z => ULift.up (Atom.grayTensorSnd U V z.down))
    (fun _ _ h => ((isMorphism (Atom.grayTensorIso U V).inv).monotone h).2)
    (fun _ _ h => (Atom.isMap (Atom.grayTensorSnd U V)).monotone h)
    fun z => ULift.ext _ _ (Atom.grayTensorSnd_apply U V z.down).symm

noncomputable def faceNerveGrayTensorBallIso (U V : Atom) :
    faceNerve.{u}.obj (grayTensor (ball U) (ball V)) ≅
      faceNerve.obj (ball U) ⨯ faceNerve.obj (ball V) :=
  faceNerve.mapIso (grayTensorBallIso U V) ≪≫ yonedaCompFaceNerveIso.app (Atom.grayTensor U V) ≪≫
    rdcFaceNerve.mapIso (atomGrayProductIso U V) ≪≫ rdcFaceNerveGrayProductIso _ _ ≪≫
      prod.mapIso (yonedaCompFaceNerveIso.app U).symm (yonedaCompFaceNerveIso.app V).symm

theorem faceNerveGrayTensorBallIso_hom_fst (U V : Atom) :
    (faceNerveGrayTensorBallIso.{u} U V).hom ≫ prod.fst =
      faceNerve.map ((grayTensorBallIso U V).hom ≫
        uliftYoneda.map (Atom.grayTensorFst U V)) := by
  simp only [faceNerveGrayTensorBallIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    prod.mapIso_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, prod.map_fst]
  rw [reassoc_of% rdcFaceNerve_map_atomGrayProductIso_hom_fst, faceNerve.map_comp]
  congr 1
  have h := yonedaCompFaceNerveIso.{u}.hom.naturality (Atom.grayTensorFst U V)
  simp only [Functor.comp_map] at h
  rw [← reassoc_of% h, Iso.hom_inv_id_app]
  exact Category.comp_id _

theorem faceNerveGrayTensorBallIso_hom_snd (U V : Atom) :
    (faceNerveGrayTensorBallIso.{u} U V).hom ≫ prod.snd =
      faceNerve.map ((grayTensorBallIso U V).hom ≫
        uliftYoneda.map (Atom.grayTensorSnd U V)) := by
  simp only [faceNerveGrayTensorBallIso, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom,
    prod.mapIso_hom, Iso.symm_hom, Iso.app_inv, Category.assoc, prod.map_snd]
  rw [reassoc_of% rdcFaceNerve_map_atomGrayProductIso_hom_snd, faceNerve.map_comp]
  congr 1
  have h := yonedaCompFaceNerveIso.{u}.hom.naturality (Atom.grayTensorSnd U V)
  simp only [Functor.comp_map] at h
  rw [← reassoc_of% h, Iso.hom_inv_id_app]
  exact Category.comp_id _

theorem faceNerveGrayTensorBallIso_hom_naturality {U V U' V' : Atom} (f : U ⟶ U') (g : V ⟶ V') :
    faceNerve.map (grayTensorBifunctor.map (Prod.mkHom (uliftYoneda.{u}.map f)
        (uliftYoneda.{u}.map g))) ≫ (faceNerveGrayTensorBallIso U' V').hom =
      (faceNerveGrayTensorBallIso U V).hom ≫
        prod.map (faceNerve.map (uliftYoneda.{u}.map f))
          (faceNerve.map (uliftYoneda.{u}.map g)) := by
  have hT : grayTensorBifunctor.map (Prod.mkHom (uliftYoneda.{u}.map f)
      (uliftYoneda.{u}.map g)) ≫ (grayTensorBallIso U' V').hom =
      (grayTensorBallIso U V).hom ≫ uliftYoneda.map (Atom.grayTensorMap f g) :=
    grayTensorYonedaIso.{u}.hom.naturality (X := (U, V)) (Y := (U', V')) (f, g)
  refine prod.hom_ext ?_ ?_
  · rw [Category.assoc, Category.assoc, prod.map_fst, faceNerveGrayTensorBallIso_hom_fst,
      reassoc_of% faceNerveGrayTensorBallIso_hom_fst, ← faceNerve.map_comp, ← faceNerve.map_comp,
      reassoc_of% hT, Category.assoc, ← uliftYoneda.map_comp, ← uliftYoneda.map_comp,
      Atom.grayTensorMap_comp_grayTensorFst]
  · rw [Category.assoc, Category.assoc, prod.map_snd, faceNerveGrayTensorBallIso_hom_snd,
      reassoc_of% faceNerveGrayTensorBallIso_hom_snd, ← faceNerve.map_comp, ← faceNerve.map_comp,
      reassoc_of% hT, Category.assoc, ← uliftYoneda.map_comp, ← uliftYoneda.map_comp,
      Atom.grayTensorMap_comp_grayTensorSnd]

@[simps] noncomputable def markedProd : MarkedSSet.{u} × MarkedSSet.{u} ⥤ MarkedSSet.{u} where
  obj p := p.1 ⨯ p.2
  map f := prod.map f.1 f.2

noncomputable def faceNerveGrayTensorYonedaIso :
    (uliftYoneda.{u}.prod uliftYoneda.{u}) ⋙ grayTensorBifunctor ⋙ faceNerve ≅
      (uliftYoneda.{u}.prod uliftYoneda.{u}) ⋙ (faceNerve.prod faceNerve) ⋙ markedProd :=
  NatIso.ofComponents (fun p => faceNerveGrayTensorBallIso p.1 p.2) fun {_ _} fg =>
    faceNerveGrayTensorBallIso_hom_naturality fg.1 fg.2

noncomputable def faceNerveProdLeftIso (X : DiagSet.{u}) :
    (Functor.curry.obj ((faceNerve.prod faceNerve) ⋙ markedProd)).obj X ≅
      faceNerve ⋙ prod.functor.obj (faceNerve.obj X) :=
  NatIso.ofComponents (fun _ => Iso.refl _) fun {Y Y'} g => by
    change prod.map (faceNerve.map (𝟙 X)) (faceNerve.map g) ≫
        𝟙 (faceNerve.obj X ⨯ faceNerve.obj Y') =
      𝟙 (faceNerve.obj X ⨯ faceNerve.obj Y) ≫ prod.map (𝟙 _) (faceNerve.map g)
    simp

noncomputable def faceNerveProdRightIso (Y : DiagSet.{u}) :
    Functor.curry.obj ((faceNerve.prod faceNerve) ⋙ markedProd) ⋙ (evaluation _ _).obj Y ≅
      faceNerve ⋙ prod.functor.obj (faceNerve.obj Y) :=
  NatIso.ofComponents (fun _ => prod.braiding _ _) fun {X X'} g => by
    change prod.map (faceNerve.map g) (faceNerve.map (𝟙 Y)) ≫
        (prod.braiding (faceNerve.obj X') (faceNerve.obj Y)).hom =
      (prod.braiding (faceNerve.obj X) (faceNerve.obj Y)).hom ≫ prod.map (𝟙 _) (faceNerve.map g)
    refine prod.hom_ext ?_ ?_ <;> simp

instance preservesColimits_curry_grayTensor_faceNerve :
    PreservesColimitsOfSize.{0, u} (Functor.curry.obj (grayTensorBifunctor.{u} ⋙ faceNerve)) :=
  preservesColimits_of_evaluation _ fun Y =>
    inferInstanceAs (PreservesColimitsOfSize.{0, u} (grayTensorRight Y ⋙ faceNerve))

instance preservesColimits_curry_faceNerve_prod :
    PreservesColimitsOfSize.{0, u}
      (Functor.curry.obj ((faceNerve.{u}.prod faceNerve) ⋙ markedProd)) :=
  preservesColimits_of_evaluation _ fun Y =>
    preservesColimits_of_natIso (faceNerveProdRightIso Y).symm

noncomputable abbrev faceNerveGrayTensorCurry : DiagSet.{u} ⥤ DiagSet.{u} ⥤ MarkedSSet.{u} :=
  Functor.curry.obj (grayTensorBifunctor ⋙ faceNerve)

noncomputable abbrev faceNerveProdCurry : DiagSet.{u} ⥤ DiagSet.{u} ⥤ MarkedSSet.{u} :=
  Functor.curry.obj ((faceNerve.prod faceNerve) ⋙ markedProd)

instance preservesColimits_flip_yoneda_faceNerveGrayTensorCurry :
    PreservesColimitsOfSize.{0, u} (uliftYoneda.{u} ⋙ faceNerveGrayTensorCurry).flip :=
  preservesColimits_of_evaluation _ fun U =>
    inferInstanceAs (PreservesColimitsOfSize.{0, u} (grayTensorLeft (ball U) ⋙ faceNerve))

instance preservesColimits_flip_yoneda_faceNerveProdCurry :
    PreservesColimitsOfSize.{0, u} (uliftYoneda.{u} ⋙ faceNerveProdCurry).flip :=
  preservesColimits_of_evaluation _ fun U =>
    preservesColimits_of_natIso (faceNerveProdLeftIso (ball U)).symm

noncomputable def faceNerveGrayTensorYonedaFlipIso :
    uliftYoneda.{u} ⋙ (uliftYoneda.{u} ⋙ faceNerveGrayTensorCurry).flip ≅
      uliftYoneda.{u} ⋙ (uliftYoneda.{u} ⋙ faceNerveProdCurry).flip :=
  NatIso.ofComponents (fun V => NatIso.ofComponents (fun U => faceNerveGrayTensorBallIso U V)
    fun {U U'} f => by
      have h := faceNerveGrayTensorBallIso_hom_naturality.{u} f (𝟙 V)
      rw [uliftYoneda.map_id] at h
      exact h)
    fun {V V'} g => by
      refine NatTrans.ext (funext fun U => ?_)
      have h := faceNerveGrayTensorBallIso_hom_naturality.{u} (𝟙 U) g
      rw [uliftYoneda.map_id] at h
      exact h

noncomputable def faceNerveGrayTensorYonedaLeftIso :
    uliftYoneda.{u} ⋙ faceNerveGrayTensorCurry ≅ uliftYoneda.{u} ⋙ faceNerveProdCurry :=
  Functor.flipping.functor.mapIso
    (isoOfPreservesColimits _ _ faceNerveGrayTensorYonedaFlipIso)

instance preservesColimits_faceNerveGrayTensorCurry_evaluation (Y : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (faceNerveGrayTensorCurry.{u} ⋙ (evaluation _ _).obj Y) :=
  inferInstanceAs (PreservesColimitsOfSize.{0, u} (grayTensorRight Y ⋙ faceNerve))

instance preservesColimits_faceNerveProdCurry_evaluation (Y : DiagSet.{u}) :
    PreservesColimitsOfSize.{0, u} (faceNerveProdCurry.{u} ⋙ (evaluation _ _).obj Y) :=
  preservesColimits_of_natIso (faceNerveProdRightIso Y).symm

noncomputable def faceNerveGrayTensorEvalIso (Y : DiagSet.{u}) :
    faceNerveGrayTensorCurry.{u} ⋙ (evaluation _ _).obj Y ≅
      faceNerveProdCurry ⋙ (evaluation _ _).obj Y :=
  isoOfPreservesColimits _ _ (NatIso.ofComponents
    (fun U => (faceNerveGrayTensorYonedaLeftIso.app U).app Y)
    fun f => congr_app (faceNerveGrayTensorYonedaLeftIso.hom.naturality f) Y)

theorem faceNerveGrayTensorEvalIso_hom_app_ball (Y : DiagSet.{u}) (U : Atom) :
    (faceNerveGrayTensorEvalIso Y).hom.app (uliftYoneda.obj U) =
      (faceNerveGrayTensorYonedaLeftIso.hom.app U).app Y :=
  isoOfPreservesColimits_hom_app _ _ _ U

theorem faceNerveGrayTensorYonedaLeftIso_hom_app_app (U V : Atom) :
    (faceNerveGrayTensorYonedaLeftIso.{u}.hom.app U).app (ball V) =
      (faceNerveGrayTensorBallIso U V).hom :=
  congr_app (isoOfPreservesColimits_hom_app _ _ faceNerveGrayTensorYonedaFlipIso V) U

noncomputable def faceNerveGrayTensorCurryIso : faceNerveGrayTensorCurry.{u} ≅ faceNerveProdCurry :=
  NatIso.ofComponents (fun X => NatIso.ofComponents (fun Y => (faceNerveGrayTensorEvalIso Y).app X)
    fun {Y Y'} g => by
      have h : Functor.whiskerLeft faceNerveGrayTensorCurry ((evaluation _ _).map g) ≫
          (faceNerveGrayTensorEvalIso Y').hom =
          (faceNerveGrayTensorEvalIso Y).hom ≫
            Functor.whiskerLeft faceNerveProdCurry ((evaluation _ _).map g) :=
        hom_ext_of_preservesColimits fun U => by
          simp only [NatTrans.comp_app, Functor.whiskerLeft_app, evaluation_map_app,
            faceNerveGrayTensorEvalIso_hom_app_ball]
          exact (faceNerveGrayTensorYonedaLeftIso.hom.app U).naturality g
      exact congr_app h X)
    fun {X X'} f => NatTrans.ext (funext fun Y => (faceNerveGrayTensorEvalIso Y).hom.naturality f)

noncomputable def faceNerveGrayTensorIso :
    grayTensorBifunctor.{u} ⋙ faceNerve ≅ (faceNerve.prod faceNerve) ⋙ markedProd :=
  eqToIso (Functor.uncurry_obj_curry_obj _).symm ≪≫
    Functor.uncurry.mapIso faceNerveGrayTensorCurryIso ≪≫
      eqToIso (Functor.uncurry_obj_curry_obj _)

theorem faceNerveGrayTensorIso_hom_app_ball (U V : Atom) :
    faceNerveGrayTensorIso.{u}.hom.app (ball U, ball V) = (faceNerveGrayTensorBallIso U V).hom := by
  simp only [faceNerveGrayTensorIso, faceNerveGrayTensorCurryIso, Iso.trans_hom, eqToIso.hom,
    NatTrans.comp_app, eqToHom_app, Functor.mapIso_hom, Functor.uncurry_map_app,
    NatIso.ofComponents_hom_app, eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (faceNerveGrayTensorEvalIso_hom_app_ball (ball V) U).trans
    (faceNerveGrayTensorYonedaLeftIso_hom_app_app U V)

theorem faceNerveGrayTensorIso_hom_fst (U V : Atom) :
    faceNerveGrayTensorIso.{u}.hom.app (ball U, ball V) ≫ prod.fst =
      faceNerve.map ((grayTensorBallIso U V).hom ≫
        uliftYoneda.map (Atom.grayTensorFst U V)) := by
  rw [faceNerveGrayTensorIso_hom_app_ball]
  exact faceNerveGrayTensorBallIso_hom_fst U V

theorem faceNerveGrayTensorIso_hom_snd (U V : Atom) :
    faceNerveGrayTensorIso.{u}.hom.app (ball U, ball V) ≫ prod.snd =
      faceNerve.map ((grayTensorBallIso U V).hom ≫
        uliftYoneda.map (Atom.grayTensorSnd U V)) := by
  rw [faceNerveGrayTensorIso_hom_app_ball]
  exact faceNerveGrayTensorBallIso_hom_snd U V

private theorem grayTensorBifunctor_faceNerve_hom_ext
    {G : DiagSet.{u} × DiagSet.{u} ⥤ MarkedSSet.{u}} {α β : grayTensorBifunctor ⋙ faceNerve ⟶ G}
    (h : ∀ U V : Atom, α.app (ball U, ball V) = β.app (ball U, ball V)) : α = β := by
  have hl (U : Atom) (Y : DiagSet.{u}) : α.app (ball U, Y) = β.app (ball U, Y) := by
    have : PreservesColimitsOfSize.{0, u}
        (Prod.sectR (ball.{u} U) DiagSet.{u} ⋙ grayTensorBifunctor ⋙ faceNerve) :=
      inferInstanceAs (PreservesColimitsOfSize.{0, u} (grayTensorLeft (ball U) ⋙ faceNerve))
    exact congr_app (hom_ext_of_preservesColimits (α := Functor.whiskerLeft (Prod.sectR _ _) α)
      (β := Functor.whiskerLeft (Prod.sectR _ _) β) fun V => h U V) Y
  refine NatTrans.ext (funext fun ⟨X, Y⟩ => ?_)
  have : PreservesColimitsOfSize.{0, u}
      (Prod.sectL DiagSet.{u} Y ⋙ grayTensorBifunctor ⋙ faceNerve) :=
    inferInstanceAs (PreservesColimitsOfSize.{0, u} (grayTensorRight Y ⋙ faceNerve))
  exact congr_app (hom_ext_of_preservesColimits (α := Functor.whiskerLeft (Prod.sectL _ Y) α)
    (β := Functor.whiskerLeft (Prod.sectL _ Y) β) fun U => hl U Y) X

theorem faceNerveGrayTensorIso_hom_app_fst (X Y : DiagSet.{u}) :
    faceNerveGrayTensorIso.{u}.hom.app (X, Y) ≫ prod.fst = faceNerve.map (grayTensorFst X Y) := by
  let p : (faceNerve.prod faceNerve) ⋙ markedProd.{u} ⟶
      CategoryTheory.Prod.fst DiagSet.{u} DiagSet.{u} ⋙ faceNerve :=
    { app _ := prod.fst
      naturality _ _ f := prod.map_fst _ _ }
  let q : grayTensorBifunctor.{u} ⟶ CategoryTheory.Prod.fst DiagSet.{u} DiagSet.{u} :=
    { app Z := grayTensorFst Z.1 Z.2
      naturality _ _ f := grayTensorBifunctor_map_grayTensorFst f.1 f.2 }
  refine congr_app (grayTensorBifunctor_faceNerve_hom_ext (α := faceNerveGrayTensorIso.hom ≫ p)
    (β := Functor.whiskerRight q faceNerve) fun U V => ?_) (X, Y)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, p, q, grayTensorFst_ball]
  rw [faceNerveGrayTensorIso_hom_fst]
  rfl

theorem faceNerveGrayTensorIso_hom_app_snd (X Y : DiagSet.{u}) :
    faceNerveGrayTensorIso.{u}.hom.app (X, Y) ≫ prod.snd = faceNerve.map (grayTensorSnd X Y) := by
  let p : (faceNerve.prod faceNerve) ⋙ markedProd.{u} ⟶
      CategoryTheory.Prod.snd DiagSet.{u} DiagSet.{u} ⋙ faceNerve :=
    { app _ := prod.snd
      naturality _ _ f := prod.map_snd _ _ }
  let q : grayTensorBifunctor.{u} ⟶ CategoryTheory.Prod.snd DiagSet.{u} DiagSet.{u} :=
    { app Z := grayTensorSnd Z.1 Z.2
      naturality _ _ f := grayTensorBifunctor_map_grayTensorSnd f.1 f.2 }
  refine congr_app (grayTensorBifunctor_faceNerve_hom_ext (α := faceNerveGrayTensorIso.hom ≫ p)
    (β := Functor.whiskerRight q faceNerve) fun U V => ?_) (X, Y)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, p, q, grayTensorSnd_ball]
  rw [faceNerveGrayTensorIso_hom_snd]
  rfl

theorem faceNerveGrayTensorIso_hom_app (A B : DiagSet.{u}) :
    faceNerveGrayTensorIso.hom.app (A, B) =
      prod.lift (faceNerve.map (grayTensorFst A B)) (faceNerve.map (grayTensorSnd A B)) :=
  prod.hom_ext ((faceNerveGrayTensorIso_hom_app_fst A B).trans (prod.lift_fst _ _).symm)
    ((faceNerveGrayTensorIso_hom_app_snd A B).trans (prod.lift_snd _ _).symm)

noncomputable def faceNerveAdjunction :=
  (DiagSet.Infty.flatForgetAdjunction.{u} 1).comp
    MarkedDiagSet.Coinductive.markedFaceNerveAdjunction.{u}

open Atoms.Homotopical.MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal in
theorem isQuillen_faceNerveAdjunction : faceNerveAdjunction.{u}.IsQuillen :=
  (isQuillen_flatForgetAdjunction 1).comp isQuillen_markedFaceNerveAdjunction

open Atoms.Homotopical.MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal in
theorem isQuillenEquivalence_faceNerveAdjunction :
    faceNerveAdjunction.{u}.IsQuillenEquivalence := by
  obtain ⟨l, hl⟩ := exists_weakEquivalence_faceNerve_toDiagSet.{u}
  have h :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.{u}.of_natTrans_weakEquivalence
    (adj' := DiagSet.Infty.sSetDiagSetAdj.comp faceNerveAdjunction)
    (isQuillen_sSetDiagSetAdj.comp isQuillen_faceNerveAdjunction) l fun K _ => hl K
  exact isQuillen_faceNerveAdjunction.isQuillenEquivalence_of_comp
    isQuillenEquivalence_sSetDiagSetAdj h

end Atoms.Diagrammatic

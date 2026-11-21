import Atoms.Diagrammatic.Adjunction.Transformation
import Atoms.ForMathlib.CategoryTheory.EqToHom

open CategoryTheory Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {X Y : DiagSet.{u}}

private theorem homMk_app_comp_homMk_app {S Q : X ⟶ Y} (α : Transformation S Q)
    (β : Transformation Q S) (h : OneTruncation.globeHomMk α ≫ OneTruncation.globeHomMk β = 𝟙 _)
    (x : X.Vertex) :
    OneTruncation.globeHomMk (α.app x) ≫ OneTruncation.globeHomMk (β.app x) = 𝟙 _ := by
  have hev {P R : X ⟶ Y} (γ : Transformation P R) :
      Arrow.mk ((oneTruncation.map (grayHomEval x Y)).toFunctor.map (OneTruncation.globeHomMk γ)) =
        Arrow.mk (OneTruncation.globeHomMk (γ.app x)) :=
    (congrArg Arrow.mk (oneTruncation_map_map_globeHomMk _ _)).trans
      (OneTruncation.arrowMk_globeHomMk_eq _ _ rfl)
  refine (Arrow.mk_inj _ _).1 ((Arrow.mk_comp_eq_mk_comp (hev α) (hev β)).symm.trans
    ((congrArg Arrow.mk (((oneTruncation.map (grayHomEval x Y)).toFunctor.map_comp _ _).symm.trans
      ((congrArg (oneTruncation.map (grayHomEval x Y)).toFunctor.map h).trans
        ((oneTruncation.map (grayHomEval x Y)).toFunctor.map_id _)))).trans ?_))
  exact congrArg (fun z => Arrow.mk (𝟙 (OneTruncation.mk z))) (grayHomEval_app_diagramVertex x S)

structure HomotopyAdjunction (F : X ⟶ Y) (G : Y ⟶ X) where
  unit : Transformation (𝟙 X) (F ≫ G)
  counit : Transformation (G ≫ F) (𝟙 Y)
  left_triangle :
    eqToHom (by simp) ≫ OneTruncation.globeHomMk (unit.whiskerRight F) ≫ eqToHom (by simp) ≫
      OneTruncation.globeHomMk (counit.whiskerLeft F) ≫ eqToHom (by simp) =
    𝟙 (OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex F))
  right_triangle :
    eqToHom (by simp) ≫ OneTruncation.globeHomMk (unit.whiskerLeft G) ≫ eqToHom (by simp) ≫
      OneTruncation.globeHomMk (counit.whiskerRight G) ≫ eqToHom (by simp) =
    𝟙 (OneTruncation.mk (X := (grayHomRight Y).obj X) (diagramVertex G))

namespace HomotopyAdjunction

variable {F : X ⟶ Y} {G : Y ⟶ X}

private theorem left_triangle_app (a : HomotopyAdjunction F G) (x : X.Vertex) :
    OneTruncation.globeHomMk ((a.unit.app x).map F) ≫
      OneTruncation.globeHomMk (a.counit.app (x.map F)) = 𝟙 _ :=
  (congrArg₂ (fun (e : Y.Edge (x.map F)
      (x.map (F ≫ G ≫ F)))
    (e' : Y.Edge (x.map (F ≫ G ≫ F)) (x.map F)) =>
      OneTruncation.globeHomMk e ≫ OneTruncation.globeHomMk e')
    (a.unit.app_whiskerRight F x) (a.counit.app_whiskerLeft F x)).symm.trans
    (homMk_app_comp_homMk_app (S := F) (Q := F ≫ G ≫ F) (a.unit.whiskerRight F)
      (a.counit.whiskerLeft F)
      ((eqToHom_comp_comp_eqToHom_comp_comp_eqToHom _ _ _ _ _).symm.trans a.left_triangle) x)

private theorem right_triangle_app (a : HomotopyAdjunction F G) (y : Y.Vertex) :
    OneTruncation.globeHomMk (a.unit.app (y.map G)) ≫
      OneTruncation.globeHomMk ((a.counit.app y).map G) = 𝟙 _ :=
  (congrArg₂ (fun (e : X.Edge (y.map G)
      (y.map (G ≫ F ≫ G)))
    (e' : X.Edge (y.map (G ≫ F ≫ G)) (y.map G)) =>
      OneTruncation.globeHomMk e ≫ OneTruncation.globeHomMk e')
    (a.unit.app_whiskerLeft G y) (a.counit.app_whiskerRight G y)).symm.trans
    (homMk_app_comp_homMk_app (S := G) (Q := G ≫ F ≫ G) (a.unit.whiskerLeft G)
      (a.counit.whiskerRight G)
      ((eqToHom_comp_comp_eqToHom_comp_comp_eqToHom _ _ _ _ _).symm.trans a.right_triangle) y)

noncomputable def toOneTruncation (a : HomotopyAdjunction F G) :
    (oneTruncation.map F).toFunctor ⊣ (oneTruncation.map G).toFunctor :=
  Adjunction.mkOfUnitCounit
    { unit := OneTruncation.mkNatTrans (fun x => OneTruncation.globeHomMk (a.unit.app x))
        fun _ _ e => by
          have he := OneTruncation.homMk_eq_globeHomMk e
          exact (congrArg (· ≫ _) he).trans
            (((a.unit.naturality (X.edgeEquivSSet.symm e)).trans (congrArg (_ ≫ ·)
          ((congrArg (oneTruncation.map G).toFunctor.map
            (oneTruncation_map_map_globeHomMk F (X.edgeEquivSSet.symm e))).trans
              (oneTruncation_map_map_globeHomMk G _)).symm)).trans
                (congrArg (fun k => _ ≫
                  ((oneTruncation.map F).toFunctor ⋙ (oneTruncation.map G).toFunctor).map k)
                    he.symm))
      counit := OneTruncation.mkNatTrans (fun y => OneTruncation.globeHomMk (a.counit.app y))
        fun _ _ e => by
          have he := OneTruncation.homMk_eq_globeHomMk e
          have hn := (congrArg (· ≫ OneTruncation.globeHomMk (a.counit.app _))
            ((congrArg (oneTruncation.map F).toFunctor.map
              (oneTruncation_map_map_globeHomMk G (Y.edgeEquivSSet.symm e))).trans
                (oneTruncation_map_map_globeHomMk F _))).trans
                  (a.counit.naturality (Y.edgeEquivSSet.symm e))
          exact ((congrArg (fun k =>
            ((oneTruncation.map G).toFunctor ⋙ (oneTruncation.map F).toFunctor).map k ≫ _)
              he).trans hn).trans (congrArg (_ ≫ ·) he.symm)
      left_triangle := OneTruncation.natTrans_ext fun x =>
        (congrArg₂ (· ≫ ·) (oneTruncation_map_map_globeHomMk F (a.unit.app x))
          (Category.id_comp _)).trans (a.left_triangle_app x)
      right_triangle := OneTruncation.natTrans_ext fun y =>
        (congrArg (_ ≫ ·) ((Category.id_comp _).trans
          (oneTruncation_map_map_globeHomMk G (a.counit.app y)))).trans (a.right_triangle_app y) }

theorem toOneTruncation_unit_app_mk (a : HomotopyAdjunction F G) (x : X.Vertex) :
    a.toOneTruncation.unit.app (OneTruncation.mk x) = OneTruncation.globeHomMk (a.unit.app x) :=
  rfl

noncomputable def homotopy (hX : IsInftyCategory 1 X) (hY : IsInftyCategory 1 Y)
    (a : HomotopyAdjunction F G) : homotopyFunctor hX.1 hY.1 F ⊣ homotopyFunctor hY.1 hX.1 G :=
  have := isEquivalence_toHomotopyCategory hX
  have := isEquivalence_toHomotopyCategory hY
  (((OneTruncation.toHomotopyCategory hX).asEquivalence.symm.toAdjunction.comp
    a.toOneTruncation).comp (OneTruncation.toHomotopyCategory hY).asEquivalence.toAdjunction
    |>.ofNatIsoLeft (Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _
      (eqToIso (OneTruncation.toHomotopyCategory_naturality hX hY F)) ≪≫
        (OneTruncation.toHomotopyCategory hX).asEquivalence.invFunIdAssoc _)
    |>.ofNatIsoRight (Functor.isoWhiskerLeft _
      (eqToIso (OneTruncation.toHomotopyCategory_naturality hY hX G)) ≪≫
        (OneTruncation.toHomotopyCategory hY).asEquivalence.invFunIdAssoc _))

end HomotopyAdjunction

private theorem homMk_comp_homMk_eq_id {S : X ⟶ Y} {α β : Transformation S S}
    (hα : α = Transformation.refl S) (hβ : β = Transformation.refl S) :
    OneTruncation.globeHomMk α ≫ OneTruncation.globeHomMk β = 𝟙 _ := by
  subst hα hβ
  exact (congrArg (· ≫ _) (OneTruncation.globeHomMk_id _)).trans
    ((Category.id_comp _).trans (OneTruncation.globeHomMk_id _))

noncomputable def HomotopyAdjunction.id (X : DiagSet.{u}) : HomotopyAdjunction (𝟙 X) (𝟙 X) where
  unit := Transformation.refl (𝟙 X)
  counit := Transformation.refl (𝟙 X)
  left_triangle := (eqToHom_comp_comp_eqToHom_comp_comp_eqToHom _ _ _ _ _).trans
    (homMk_comp_homMk_eq_id (Transformation.whiskerRight_refl _ _)
      (Transformation.whiskerLeft_refl _ _))
  right_triangle := (eqToHom_comp_comp_eqToHom_comp_comp_eqToHom _ _ _ _ _).trans
    (homMk_comp_homMk_eq_id (Transformation.whiskerLeft_refl _ _)
      (Transformation.whiskerRight_refl _ _))

private theorem globeHomMk_eq_eqToHom {P Q : X ⟶ Y} (η : Transformation P Q) (h : P = Q)
    (hη : η.toMap = grayTensorSnd (ball.{u} (atomSimplex 1)) X ≫ P) :
    OneTruncation.globeHomMk η = eqToHom (congrArg
      (fun F : X ⟶ Y => OneTruncation.mk (X := (grayHomRight X).obj Y) (diagramVertex F)) h) := by
  subst h
  have h : η = Transformation.refl P :=
    Transformation.ext (hη.trans (Transformation.toMap_refl P).symm)
  subst h
  exact OneTruncation.globeHomMk_id _

noncomputable def HomotopyAdjunction.ofRetraction (i : X ⟶ Y) (ρ : Y ⟶ X) (hρ : i ≫ ρ = 𝟙 X)
    (ε : Transformation (ρ ≫ i) (𝟙 Y))
    (hi : (grayTensorLeft _).map i ≫ ε.toMap = grayTensorSnd (ball.{u} (atomSimplex 1)) X ≫ i)
    (hε : ε.toMap ≫ ρ = grayTensorSnd (ball.{u} (atomSimplex 1)) Y ≫ ρ) :
    HomotopyAdjunction i ρ where
  unit := Transformation.ofMap (grayTensorSnd (ball.{u} (atomSimplex 1)) X)
    (by rw [grayTensorRight_map_grayTensorSnd, Category.comp_id])
    (by rw [grayTensorRight_map_grayTensorSnd, hρ, Category.comp_id])
  counit := ε
  left_triangle := by
    rw [globeHomMk_eq_eqToHom (Transformation.whiskerRight _ i) (by rw [hρ])
        (by rw [Transformation.toMap_whiskerRight, Transformation.toMap_ofMap, Category.id_comp]),
      globeHomMk_eq_eqToHom (Transformation.whiskerLeft i ε)
        (by rw [← Category.assoc, hρ, Category.id_comp, Category.comp_id])
        (by rw [Transformation.toMap_whiskerLeft, hi, ← Category.assoc i, hρ, Category.id_comp])]
    simp only [eqToHom_trans, eqToHom_refl]
  right_triangle := by
    rw [globeHomMk_eq_eqToHom (Transformation.whiskerLeft ρ _) (by rw [hρ])
        (by rw [Transformation.toMap_whiskerLeft, Transformation.toMap_ofMap,
          grayTensorLeft_map_grayTensorSnd, Category.comp_id]),
      globeHomMk_eq_eqToHom (Transformation.whiskerRight ε ρ)
        (by rw [Category.assoc, hρ, Category.comp_id, Category.id_comp])
        (by rw [Transformation.toMap_whiskerRight, hε, Category.assoc, hρ, Category.comp_id])]
    simp only [eqToHom_trans, eqToHom_refl]

end Atoms.Diagrammatic

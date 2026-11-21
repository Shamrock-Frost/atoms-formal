import Atoms.Diagrammatic.Limits.Cone
import Atoms.Diagrammatic.Suspension.Hom

open CategoryTheory Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {K X Y Z : DiagSet.{u}}

instance isIso_grayTensorFst_ballAtomSimplexZero (T : DiagSet.{u}) :
    IsIso (grayTensorFst T (ball.{u} atomPoint)) := by
  have : IsIso (isTerminalBallAtomPoint.from (ball.{u} atomPoint)) :=
    isIso_of_isTerminal isTerminalBallAtomPoint isTerminalBallAtomPoint _
  have : IsIso (X := ((T, ball.{u} atomPoint) : DiagSet.{u} × DiagSet.{u}))
      (Y := (T, ball.{u} atomPoint)) (𝟙 T, isTerminalBallAtomPoint.from _) :=
    (isIso_prod_iff _ _).2 ⟨inferInstance, inferInstance⟩
  exact inferInstanceAs (IsIso (grayTensorBifunctor.map _ ≫ _))

instance isIso_grayTensorFst_ballAtomSimplex_zero (T : DiagSet.{u}) :
    IsIso (grayTensorFst T (ball.{u} (atomSimplex 0))) :=
  isIso_grayTensorFst_ballAtomSimplexZero T

private noncomputable def grayTensorRightPointIso :
    grayTensorRight (ball.{u} atomPoint) ≅ 𝟭 DiagSet.{u} :=
  NatIso.ofComponents (fun T => @asIso _ _ _ _ _ (isIso_grayTensorFst_ballAtomSimplexZero T))
    fun f => grayTensorRight_map_grayTensorFst f _

noncomputable def grayHomRightPointIso :
    grayHomRight (ball.{u} atomPoint) ≅ 𝟭 DiagSet.{u} :=
  conjugateIsoEquiv (grayTensorRightAdjunction _) Adjunction.id grayTensorRightPointIso.symm

theorem homEquiv_comp_grayHomRightPointIso_hom_app {T A : DiagSet.{u}}
    (F : grayTensor T (ball.{u} atomPoint) ⟶ A) :
    (grayTensorRightAdjunction _).homEquiv T A F ≫ grayHomRightPointIso.hom.app A =
      inv (grayTensorFst T _) ≫ F := by
  have e : grayHomRightPointIso.hom.app A =
      inv (grayTensorFst _ _) ≫ (grayTensorRightAdjunction _).counit.app A :=
    conjugateEquiv_adjunction_id (grayTensorRightAdjunction _) grayTensorRightPointIso.inv A
  rw [e, IsIso.eq_inv_comp, ← grayTensorRight_map_grayTensorFst_assoc, IsIso.hom_inv_id_assoc]
  exact ((grayTensorRightAdjunction _).homEquiv_counit T A _).symm.trans
    (Equiv.symm_apply_apply _ _)

noncomputable def grayHomBoundaryFan (A : DiagSet.{u}) : BinaryFan A A :=
  BinaryFan.mk
    ((grayHomRestrict (coprod.inl : ball.{u} atomPoint ⟶ intervalBoundary)).app A ≫
      grayHomRightPointIso.hom.app A)
    ((grayHomRestrict (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary)).app A ≫
      grayHomRightPointIso.hom.app A)

private theorem homEquiv_comp_grayHomRestrict_comp {T A : DiagSet.{u}}
    (i : ball.{u} atomPoint ⟶ intervalBoundary) (F : grayTensor T intervalBoundary ⟶ A) :
    (grayTensorRightAdjunction _).homEquiv T A F ≫ (grayHomRestrict i).app A ≫
        grayHomRightPointIso.hom.app A =
      inv (grayTensorFst T _) ≫ (grayTensorLeft T).map i ≫ F := by
  rw [← Category.assoc, homEquiv_comp_grayHomRestrict, homEquiv_comp_grayHomRightPointIso_hom_app]

private theorem homEquiv_comp_grayHomBoundaryFan_fst {T A : DiagSet.{u}}
    (F : grayTensor T intervalBoundary ⟶ A) :
    (grayTensorRightAdjunction _).homEquiv T A F ≫ (grayHomBoundaryFan A).fst =
      inv (grayTensorFst T _) ≫
        (grayTensorLeft T).map (coprod.inl : ball.{u} atomPoint ⟶ intervalBoundary) ≫ F :=
  homEquiv_comp_grayHomRestrict_comp _ F

private theorem homEquiv_comp_grayHomBoundaryFan_snd {T A : DiagSet.{u}}
    (F : grayTensor T intervalBoundary ⟶ A) :
    (grayTensorRightAdjunction _).homEquiv T A F ≫ (grayHomBoundaryFan A).snd =
      inv (grayTensorFst T _) ≫
        (grayTensorLeft T).map (coprod.inr : ball.{u} atomPoint ⟶ intervalBoundary) ≫ F :=
  homEquiv_comp_grayHomRestrict_comp _ F

@[reassoc]
theorem boundaryHom_comp_grayHomBoundaryFan_fst (f g : X ⟶ Z) :
    boundaryHom f g ≫ (grayHomBoundaryFan Z).fst = f := by
  rw [boundaryHom, homEquiv_comp_grayHomBoundaryFan_fst, grayTensorBoundaryDesc_inl,
    IsIso.inv_hom_id_assoc]

@[reassoc]
theorem boundaryHom_comp_grayHomBoundaryFan_snd (f g : X ⟶ Z) :
    boundaryHom f g ≫ (grayHomBoundaryFan Z).snd = g := by
  rw [boundaryHom, homEquiv_comp_grayHomBoundaryFan_snd, grayTensorBoundaryDesc_inr,
    IsIso.inv_hom_id_assoc]

noncomputable def isLimitGrayHomBoundaryFan (A : DiagSet.{u}) : IsLimit (grayHomBoundaryFan A) :=
  BinaryFan.IsLimit.mk _ boundaryHom boundaryHom_comp_grayHomBoundaryFan_fst
    boundaryHom_comp_grayHomBoundaryFan_snd fun {T} f g m hf hg => by
      obtain ⟨F, rfl⟩ := ((grayTensorRightAdjunction _).homEquiv T A).surjective m
      rw [boundaryHom]
      congr 1
      refine grayTensor_coprod_hom_ext T ?_ ?_
      · rw [grayTensorBoundaryDesc_inl, ← (homEquiv_comp_grayHomBoundaryFan_fst F).symm.trans hf,
          IsIso.hom_inv_id_assoc]
      · rw [grayTensorBoundaryDesc_inr, ← (homEquiv_comp_grayHomBoundaryFan_snd F).symm.trans hg,
          IsIso.hom_inv_id_assoc]

private theorem inv_grayTensorFst_comp_endpoints (x y : X.Vertex)
    (i : ball.{u} atomPoint ⟶ intervalBoundary) :
    inv (grayTensorFst (ball.{u} atomPoint) _) ≫ (grayTensorLeft _).map i ≫
        grayTensorSnd _ _ ≫ coprod.desc (vertexHom x) (vertexHom y) =
      isTerminalBallAtomPoint.from _ ≫ i ≫ coprod.desc (vertexHom x) (vertexHom y) := by
  rw [← Category.assoc ((grayTensorLeft _).map i), grayTensorLeft_map_grayTensorSnd,
    Category.assoc, ← Category.assoc (inv _)]
  exact congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _)

theorem DiagSet.endpointsPoint_comp_grayHomBoundaryFan_fst (x y : X.Vertex) :
    X.endpointsPoint x y ≫ (grayHomBoundaryFan X).fst =
      isTerminalBallAtomPoint.from _ ≫ vertexHom x := by
  rw [DiagSet.endpointsPoint_eq_homEquiv, homEquiv_comp_grayHomBoundaryFan_fst,
    inv_grayTensorFst_comp_endpoints, coprod.inl_desc]

theorem DiagSet.endpointsPoint_comp_grayHomBoundaryFan_snd (x y : X.Vertex) :
    X.endpointsPoint x y ≫ (grayHomBoundaryFan X).snd =
      isTerminalBallAtomPoint.from _ ≫ vertexHom y := by
  rw [DiagSet.endpointsPoint_eq_homEquiv, homEquiv_comp_grayHomBoundaryFan_snd,
    inv_grayTensorFst_comp_endpoints, coprod.inr_desc]

@[reassoc]
theorem coneObjectBase_comp_grayHomBoundaryFan_fst (α : Bool) (d : K ⟶ X) :
    coneObjectBase α d ≫ (grayHomBoundaryFan _).fst =
      cond α (constDiagram K X) (isTerminalBallAtomPoint.from X ≫ diagramPoint d) :=
  boundaryHom_comp_grayHomBoundaryFan_fst _ _

@[reassoc]
theorem coneObjectBase_comp_grayHomBoundaryFan_snd (α : Bool) (d : K ⟶ X) :
    coneObjectBase α d ≫ (grayHomBoundaryFan _).snd =
      cond α (isTerminalBallAtomPoint.from X ≫ diagramPoint d) (constDiagram K X) :=
  boundaryHom_comp_grayHomBoundaryFan_snd _ _

private noncomputable def isLimitBipointGrayHomBoundary (A : DiagSet.{u})
    (v w : ((grayHomRight intervalBoundary.{u}).obj A).Vertex) :
    IsLimit (BinaryFan.mk (DiagSet.bipointMap (grayHomBoundaryFan A).fst v w)
      (DiagSet.bipointMap (grayHomBoundaryFan A).snd v w)) :=
  have : ReflectsLimit (pair (A.bipoint (v.map (grayHomBoundaryFan A).fst)
      (w.map (grayHomBoundaryFan A).fst))
      (A.bipoint (v.map (grayHomBoundaryFan A).snd)
        (w.map (grayHomBoundaryFan A).snd)))
      (Under.forget pointPair.{u}) := inferInstance
  isLimitOfReflects (Under.forget _)
    ((isLimitMapConeBinaryFanEquiv _ _ _).2 (isLimitGrayHomBoundaryFan A))

noncomputable def bipointedHomBoundaryIso (A : DiagSet.{u})
    (v w : ((grayHomRight intervalBoundary.{u}).obj A).Vertex) :
    bipointedHom.obj (((grayHomRight intervalBoundary.{u}).obj A).bipoint v w) ≅
      bipointedHom.obj (A.bipoint (v.map (grayHomBoundaryFan A).fst)
          (w.map (grayHomBoundaryFan A).fst)) ⨯
        bipointedHom.obj (A.bipoint (v.map (grayHomBoundaryFan A).snd)
          (w.map (grayHomBoundaryFan A).snd)) :=
  have := bipointedSuspensionAdjunction.{u}.rightAdjoint_preservesLimits
  IsLimit.conePointUniqueUpToIso ((isLimitMapConeBinaryFanEquiv bipointedHom _ _).1
    (isLimitOfPreserves bipointedHom (isLimitBipointGrayHomBoundary A v w))) (limit.isLimit _)

@[reassoc]
theorem bipointedHomBoundaryIso_hom_fst (A : DiagSet.{u})
    (v w : ((grayHomRight intervalBoundary.{u}).obj A).Vertex) :
    (bipointedHomBoundaryIso A v w).hom ≫ prod.fst =
      bipointedHom.map (DiagSet.bipointMap (grayHomBoundaryFan A).fst v w) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ (limit.isLimit _) (⟨WalkingPair.left⟩ : Discrete _)

@[reassoc]
theorem bipointedHomBoundaryIso_hom_snd (A : DiagSet.{u})
    (v w : ((grayHomRight intervalBoundary.{u}).obj A).Vertex) :
    (bipointedHomBoundaryIso A v w).hom ≫ prod.snd =
      bipointedHom.map (DiagSet.bipointMap (grayHomBoundaryFan A).snd v w) :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ (limit.isLimit _) (⟨WalkingPair.right⟩ : Discrete _)

end Atoms.Diagrammatic

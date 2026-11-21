import Atoms.Diagrammatic.FinalObject
import Atoms.Diagrammatic.Joyal.GrayTensorModel

open CategoryTheory Limits Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

variable {K X Y Z : DiagSet.{u}}

@[reassoc]
theorem grayTensorRight_map_grayTensorFst {A A' : DiagSet.{u}} (f : A ⟶ A') (B : DiagSet.{u}) :
    (grayTensorRight B).map f ≫ grayTensorFst A' B = grayTensorFst A B ≫ f := by
  rw [grayTensorRight_map_eq, grayTensorFst, grayTensorFst, Category.assoc,
    ← GrayDiagSet.rightUnitor_naturality, ← Category.assoc, ← Category.assoc, ← Functor.map_comp,
    ← Functor.map_comp, prod_comp, prod_comp]
  simp only [Category.id_comp, Category.comp_id]

noncomputable def constDiagram (K X : DiagSet.{u}) : X ⟶ (grayHomRight K).obj X :=
  (grayTensorRightAdjunction K).homEquiv X X (grayTensorFst X K)

theorem grayHomRightCellEquiv_constDiagram (U : Atom) (x : diagram X U) :
    grayHomRightCellEquiv K X U ((constDiagram K X).app (op U) x) =
      grayTensorFst (ball.{u} U) K ≫ uliftYonedaEquiv.symm x :=
  (grayHomRightCellEquiv_homEquiv_app K X X _ U x).trans (grayTensorRight_map_grayTensorFst _ _)

@[reassoc]
theorem constDiagram_naturality (K : DiagSet.{u}) (F : X ⟶ Y) :
    F ≫ constDiagram K Y = constDiagram K X ≫ (grayHomRight K).map F := by
  rw [constDiagram, constDiagram, ← Adjunction.homEquiv_naturality_left,
    ← Adjunction.homEquiv_naturality_right, grayTensorRight_map_grayTensorFst]

noncomputable def diagramPoint (d : K ⟶ X) : ball.{u} atomPoint ⟶ (grayHomRight K).obj X :=
  (grayTensorRightAdjunction K).homEquiv _ X (grayTensorSnd (ball.{u} atomPoint) K ≫ d)

@[reassoc]
theorem diagramPoint_comp (d : K ⟶ X) (F : X ⟶ Y) :
    diagramPoint d ≫ (grayHomRight K).map F = diagramPoint (d ≫ F) := by
  rw [diagramPoint, diagramPoint, ← Adjunction.homEquiv_naturality_right, Category.assoc]

theorem comp_diagramPoint {T V X : DiagSet.{u}} (b : T ⟶ ball.{u} atomPoint) (f : V ⟶ X) :
    b ≫ diagramPoint f = (grayTensorRightAdjunction V).homEquiv T X (grayTensorSnd T V ≫ f) := by
  rw [diagramPoint, ← Adjunction.homEquiv_naturality_left, ← Category.assoc,
    grayTensorRight_map_grayTensorSnd]

noncomputable def diagramVertex (d : K ⟶ X) : ((grayHomRight K).obj X).Vertex :=
  uliftYonedaEquiv (X := atomPoint) (F := (grayHomRight K).obj X)
    (isTerminalBallAtomPoint.from (ball.{u} atomPoint) ≫ diagramPoint d)

theorem vertexHom_comp_diagramPoint (d : K ⟶ X) (l : X.Vertex) :
    vertexHom l ≫ isTerminalBallAtomPoint.from X ≫ diagramPoint d =
      vertexHom (diagramVertex d) := by
  refine Eq.trans ?_ (Equiv.symm_apply_apply (uliftYonedaEquiv (X := atomPoint)) _).symm
  rw [← Category.assoc]
  exact congrArg (· ≫ diagramPoint d) (isTerminalBallAtomPoint.hom_ext _ _)

noncomputable def isColimitGrayTensorBoundary (C : DiagSet.{u}) :
    IsColimit (BinaryCofan.mk ((grayTensorLeft C).map (coprod.inl (X := ball.{u} atomPoint)
      (Y := ball atomPoint))) ((grayTensorLeft C).map coprod.inr)) :=
  isColimitMapCoconeBinaryCofanEquiv _ _ _
    (isColimitOfPreserves (grayTensorLeft C) (coprodIsCoprod _ _))

noncomputable def grayTensorBoundaryDesc (C : DiagSet.{u})
    (f g : grayTensor C (ball.{u} atomPoint) ⟶ Z) : grayTensor C intervalBoundary.{u} ⟶ Z :=
  (isColimitGrayTensorBoundary C).desc (BinaryCofan.mk f g)

@[reassoc]
theorem grayTensorBoundaryDesc_inl (C : DiagSet.{u})
    (f g : grayTensor C (ball.{u} atomPoint) ⟶ Z) :
    (grayTensorLeft C).map coprod.inl ≫ grayTensorBoundaryDesc C f g = f :=
  (isColimitGrayTensorBoundary C).fac (BinaryCofan.mk f g) ⟨WalkingPair.left⟩

@[reassoc]
theorem grayTensorBoundaryDesc_inr (C : DiagSet.{u})
    (f g : grayTensor C (ball.{u} atomPoint) ⟶ Z) :
    (grayTensorLeft C).map coprod.inr ≫ grayTensorBoundaryDesc C f g = g :=
  (isColimitGrayTensorBoundary C).fac (BinaryCofan.mk f g) ⟨WalkingPair.right⟩

noncomputable def boundaryHom (f g : X ⟶ Z) : X ⟶ (grayHomRight intervalBoundary.{u}).obj Z :=
  (grayTensorRightAdjunction _).homEquiv X Z
    (grayTensorBoundaryDesc X (grayTensorFst X _ ≫ f) (grayTensorFst X _ ≫ g))

@[reassoc]
theorem comp_boundaryHom {W : DiagSet.{u}} (h : W ⟶ X) (f g : X ⟶ Z) :
    h ≫ boundaryHom f g = boundaryHom (h ≫ f) (h ≫ g) := by
  rw [boundaryHom, boundaryHom, ← Adjunction.homEquiv_naturality_left]
  congr 1
  refine grayTensor_coprod_hom_ext W ?_ ?_ <;>
    simp only [← Category.assoc, grayTensorLeft_map_comp_grayTensorRight_map] <;>
    simp only [Category.assoc, grayTensorBoundaryDesc_inl, grayTensorBoundaryDesc_inr,
      grayTensorRight_map_grayTensorFst_assoc]

@[reassoc]
theorem boundaryHom_comp (f g : X ⟶ Z) {Z' : DiagSet.{u}} (h : Z ⟶ Z') :
    boundaryHom f g ≫ (grayHomRight intervalBoundary.{u}).map h =
      boundaryHom (f ≫ h) (g ≫ h) := by
  rw [boundaryHom, boundaryHom, ← Adjunction.homEquiv_naturality_right]
  congr 1
  refine grayTensor_coprod_hom_ext X ?_ ?_ <;>
    simp only [grayTensorBoundaryDesc_inl_assoc, grayTensorBoundaryDesc_inr_assoc,
      grayTensorBoundaryDesc_inl, grayTensorBoundaryDesc_inr, Category.assoc]

theorem vertexHom_comp_boundaryHom (f g : X ⟶ Z) (l : X.Vertex) :
    vertexHom l ≫ boundaryHom f g = isTerminalBallAtomPoint.from _ ≫
      Z.endpointsPoint (l.map f) (l.map g) := by
  rw [comp_boundaryHom, vertexHom_comp, vertexHom_comp, DiagSet.endpointsPoint_eq_homEquiv,
    ← Adjunction.homEquiv_naturality_left, boundaryHom, ← Category.assoc,
    grayTensorRight_map_grayTensorSnd]
  congr 1
  have e : grayTensorFst (ball.{u} atomPoint) (ball atomPoint) =
      grayTensorSnd _ _ := isTerminalBallAtomPoint.hom_ext _ _
  refine grayTensor_coprod_hom_ext _ ?_ ?_ <;>
    simp only [grayTensorBoundaryDesc_inl, grayTensorBoundaryDesc_inr, e,
      reassoc_of% grayTensorLeft_map_grayTensorSnd, coprod.inl_desc, coprod.inr_desc]

noncomputable def coneObjectBase (α : Bool) (d : K ⟶ X) :
    X ⟶ (grayHomRight intervalBoundary.{u}).obj ((grayHomRight K).obj X) :=
  boundaryHom (cond α (constDiagram K X) (isTerminalBallAtomPoint.from X ≫ diagramPoint d))
    (cond α (isTerminalBallAtomPoint.from X ≫ diagramPoint d) (constDiagram K X))

theorem vertexHom_comp_coneObjectBase (α : Bool) (d : K ⟶ X) (l : X.Vertex) :
    vertexHom l ≫ coneObjectBase α d = isTerminalBallAtomPoint.from _ ≫
      ((grayHomRight K).obj X).endpointsPoint
        (cond α (l.map (constDiagram K X)) (diagramVertex d))
        (cond α (diagramVertex d) (l.map (constDiagram K X))) := by
  have e : l.map (isTerminalBallAtomPoint.from X ≫ diagramPoint d) =
      diagramVertex d := by
    have h := (vertexHom_comp l (isTerminalBallAtomPoint.from X ≫ diagramPoint d)).symm.trans
      (vertexHom_comp_diagramPoint d l)
    exact (uliftYonedaEquiv (X := atomPoint) (F := (grayHomRight K).obj X)).symm.injective h
  rw [coneObjectBase, vertexHom_comp_boundaryHom]
  cases α <;> simp only [cond, e]

noncomputable def coneObject (α : Bool) (d : K ⟶ X) : DiagSet.{u} :=
  pullback ((grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)) (coneObjectBase α d)

noncomputable def coneObjectι (α : Bool) (d : K ⟶ X) :
    coneObject α d ⟶ (grayHomRight (ball.{u} (atomSimplex 1))).obj ((grayHomRight K).obj X) :=
  pullback.fst _ _

noncomputable def coneObjectπ (α : Bool) (d : K ⟶ X) : coneObject α d ⟶ X :=
  pullback.snd _ _

theorem isPullback_coneObject (α : Bool) (d : K ⟶ X) :
    IsPullback (coneObjectι α d) (coneObjectπ α d)
      ((grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)) (coneObjectBase α d) :=
  IsPullback.of_hasPullback _ _

noncomputable def coneObjectHomEquiv (α : Bool) (d : K ⟶ X) (T : DiagSet.{u}) :
    (T ⟶ coneObject α d) ≃
      {p : (T ⟶ X) × (grayTensor T (ball.{u} (atomSimplex 1)) ⟶ (grayHomRight K).obj X) //
        (grayTensorLeft T).map intervalBoundaryι ≫ p.2 = grayTensorBoundaryDesc T
          (grayTensorFst T _ ≫ p.1 ≫
            cond α (constDiagram K X) (isTerminalBallAtomPoint.from X ≫ diagramPoint d))
          (grayTensorFst T _ ≫ p.1 ≫
            cond α (isTerminalBallAtomPoint.from X ≫ diagramPoint d) (constDiagram K X))} :=
  have key (t : T ⟶ X) (s : T ⟶ (grayHomRight (ball.{u} (atomSimplex 1))).obj
      ((grayHomRight K).obj X)) :
      s ≫ (grayHomRestrict intervalBoundaryι).app _ = t ≫ coneObjectBase α d ↔
        (grayTensorLeft T).map intervalBoundaryι ≫
            ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv T
              ((grayHomRight K).obj X)).symm s =
          grayTensorBoundaryDesc T
            (grayTensorFst T _ ≫ t ≫
              cond α (constDiagram K X) (isTerminalBallAtomPoint.from X ≫ diagramPoint d))
            (grayTensorFst T _ ≫ t ≫
              cond α (isTerminalBallAtomPoint.from X ≫ diagramPoint d) (constDiagram K X)) := by
    rw [coneObjectBase, comp_boundaryHom, boundaryHom, ← Equiv.apply_symm_apply
      ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv _ _) s,
      homEquiv_comp_grayHomRestrict, Equiv.apply_symm_apply, Equiv.apply_eq_iff_eq]
  { toFun g := ⟨(g ≫ coneObjectπ α d,
        ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv T
              ((grayHomRight K).obj X)).symm (g ≫ coneObjectι α d)),
      (key _ _).1 (by rw [Category.assoc, Category.assoc, (isPullback_coneObject α d).w])⟩
    invFun p := pullback.lift ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv T
      ((grayHomRight K).obj X) p.1.2) p.1.1
      ((key _ _).2 (by rw [Equiv.symm_apply_apply]; exact p.2))
    left_inv g := pullback.hom_ext (by
        rw [pullback.lift_fst, Equiv.apply_symm_apply]
        rfl)
      (pullback.lift_snd _ _ _)
    right_inv p := Subtype.ext (Prod.ext (pullback.lift_snd _ _ _)
      (by
        change ((grayTensorRightAdjunction (ball.{u} (atomSimplex 1))).homEquiv T
              ((grayHomRight K).obj X)).symm (pullback.lift _ _ _ ≫
          pullback.fst _ _) = _
        rw [pullback.lift_fst, Equiv.symm_apply_apply])) }

theorem fibration_coneObjectπ (α : Bool) (d : K ⟶ X) (hX : IsInftyCategory 1 X) :
    HomotopicalAlgebra.Fibration ((DiagSet.toInfty 1).map (coneObjectπ α d)) := by
  have := fibration_toInfty_one_grayHomRestrict intervalBoundaryι
    (isInftyCategory_grayHomRight K hX)
  have h : IsPullback (C := DiagSet.Infty.{u} 1) ((DiagSet.toInfty 1).map (coneObjectι α d))
      ((DiagSet.toInfty 1).map (coneObjectπ α d))
      ((DiagSet.toInfty 1).map ((grayHomRestrict intervalBoundaryι).app ((grayHomRight K).obj X)))
      ((DiagSet.toInfty 1).map (coneObjectBase α d)) :=
    isPullback_coneObject α d
  rw [HomotopicalAlgebra.fibration_iff]
  exact MorphismProperty.of_isPullback h ((HomotopicalAlgebra.fibration_iff _).1 inferInstance)

theorem isInftyCategory_coneObject (α : Bool) (d : K ⟶ X) (hX : IsInftyCategory 1 X) :
    IsInftyCategory 1 (coneObject α d) := by
  have := (isFibrant_infty_iff 1 ((DiagSet.toInfty 1).obj X)).2 hX
  have := fibration_coneObjectπ α d hX
  exact (isFibrant_infty_iff 1 ((DiagSet.toInfty 1).obj (coneObject α d))).1
    (HomotopicalAlgebra.isFibrant_of_fibration ((DiagSet.toInfty 1).map (coneObjectπ α d)))

noncomputable abbrev coneObjectFibre (α : Bool) (d : K ⟶ X) (l : X.Vertex) :
    DiagSet.{u} :=
  (((grayHomRight K).obj X).mappingSpace
    (cond α (l.map (constDiagram K X)) (diagramVertex d))
    (cond α (diagramVertex d) (l.map (constDiagram K X)))).toFunctor

noncomputable def coneObjectFibreι (α : Bool) (d : K ⟶ X) (l : X.Vertex) :
    coneObjectFibre α d l ⟶ coneObject α d :=
  pullback.lift (Subfunctor.ι _) (isTerminalBallAtomPoint.from _ ≫ vertexHom l) <| by
    rw [(DiagSet.isPullback_mappingSpace _ _).w, Category.assoc, vertexHom_comp_coneObjectBase,
      ← Category.assoc]
    exact congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _)

theorem isPullback_mappingSpace_coneObject (α : Bool) (d : K ⟶ X)
    (l : X.Vertex) :
    IsPullback (coneObjectFibreι α d l) (isTerminalBallAtomPoint.from _)
      (coneObjectπ α d) (vertexHom l) := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (isPullback_coneObject α d)
  refine (DiagSet.isPullback_mappingSpace _ _).of_iso (Iso.refl _) (Iso.refl _)
    (isTerminalBallAtomPoint.uniqueUpToIso isTerminalBallAtomPoint) (Iso.refl _) ?_
    (isTerminalBallAtomPoint.hom_ext _ _) (by simp) ?_
  · exact (Category.comp_id _).trans
      ((pullback.lift_fst _ _ _).symm.trans (Category.id_comp _).symm)
  · rw [Iso.refl_hom, Category.comp_id, vertexHom_comp_coneObjectBase, ← Category.assoc,
      isTerminalBallAtomPoint.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]

theorem vertexHom_injective : Function.Injective (vertexHom (X := X)) :=
  Equiv.injective _

theorem vertexHom_uliftYonedaEquiv (f : ball.{u} atomPoint ⟶ X) :
    vertexHom (uliftYonedaEquiv (X := atomPoint) (F := X) f) = f :=
  Equiv.symm_apply_apply _ _

noncomputable def coneObjectFibreVerticesEquiv (α : Bool) (d : K ⟶ X)
    (l : X.Vertex) :
    {v : (coneObject α d).Vertex //
      v.map (coneObjectπ α d) = l} ≃
      (coneObjectFibre α d l).Vertex where
  toFun v := uliftYonedaEquiv (X := atomPoint) (F := coneObjectFibre α d l)
    ((isPullback_mappingSpace_coneObject α d l).lift (vertexHom v.1) (𝟙 _)
      (by rw [vertexHom_comp, v.2, Category.id_comp]))
  invFun w := ⟨w.map (coneObjectFibreι α d l), vertexHom_injective <| by
    rw [← vertexHom_comp, ← vertexHom_comp, Category.assoc,
      (isPullback_mappingSpace_coneObject α d l).w,
      ← Category.assoc, isTerminalBallAtomPoint.hom_ext (_ ≫ _) (𝟙 _), Category.id_comp]⟩
  left_inv v := Subtype.ext <| vertexHom_injective <|
    (vertexHom_comp _ (coneObjectFibreι α d l)).symm.trans <| by
      rw [vertexHom_uliftYonedaEquiv, IsPullback.lift_fst]
  right_inv w := @vertexHom_injective (coneObjectFibre α d l) _ _ <| by
    rw [vertexHom_uliftYonedaEquiv]
    refine (isPullback_mappingSpace_coneObject α d l).hom_ext ?_
      (isTerminalBallAtomPoint.hom_ext _ _)
    rw [IsPullback.lift_fst, vertexHom_comp]

noncomputable def coneObjectVerticesEquiv (α : Bool) (d : K ⟶ X) :
    (coneObject α d).Vertex ≃ Σ l : X.Vertex,
      ((grayHomRight K).obj X).Edge
        (cond α (l.map (constDiagram K X)) (diagramVertex d))
        (cond α (diagramVertex d) (l.map (constDiagram K X))) :=
  (Equiv.sigmaFiberEquiv (DiagSet.Vertex.map (coneObjectπ α d))).symm.trans
    (Equiv.sigmaCongrRight fun l =>
      (coneObjectFibreVerticesEquiv α d l).trans
        (DiagSet.mappingSpaceVerticesEquiv _ _))

@[simp]
theorem coneObjectVerticesEquiv_fst (α : Bool) (d : K ⟶ X)
    (v : (coneObject α d).Vertex) :
    (coneObjectVerticesEquiv α d v).1 = v.map (coneObjectπ α d) :=
  rfl

theorem coneObjectBase_comp (α : Bool) (d : K ⟶ X) (F : X ⟶ Y) :
    coneObjectBase α d ≫ (grayHomRight intervalBoundary.{u}).map ((grayHomRight K).map F) =
      F ≫ coneObjectBase α (d ≫ F) := by
  have hc := constDiagram_naturality K F
  have hd : (isTerminalBallAtomPoint.from X ≫ diagramPoint d) ≫ (grayHomRight K).map F =
      F ≫ isTerminalBallAtomPoint.from Y ≫ diagramPoint (d ≫ F) := by
    rw [Category.assoc, diagramPoint_comp, ← Category.assoc]
    exact congrArg (· ≫ _) (isTerminalBallAtomPoint.hom_ext _ _)
  rw [coneObjectBase, coneObjectBase, boundaryHom_comp, comp_boundaryHom]
  cases α <;> simp only [cond, hc, hd]

noncomputable def coneObjectMap (α : Bool) (d : K ⟶ X) (F : X ⟶ Y) :
    coneObject α d ⟶ coneObject α (d ≫ F) :=
  pullback.map _ _ _ _ ((grayHomRight (ball.{u} (atomSimplex 1))).map ((grayHomRight K).map F)) F
    ((grayHomRight intervalBoundary.{u}).map ((grayHomRight K).map F))
    ((grayHomRestrict intervalBoundaryι).naturality _).symm (coneObjectBase_comp α d F)

@[reassoc (attr := simp)]
theorem coneObjectMap_π (α : Bool) (d : K ⟶ X) (F : X ⟶ Y) :
    coneObjectMap α d F ≫ coneObjectπ α (d ≫ F) = coneObjectπ α d ≫ F :=
  pullback.lift_snd _ _ _

@[reassoc (attr := simp)]
theorem coneObjectMap_ι (α : Bool) (d : K ⟶ X) (F : X ⟶ Y) :
    coneObjectMap α d F ≫ coneObjectι α (d ≫ F) =
      coneObjectι α d ≫
        (grayHomRight (ball.{u} (atomSimplex 1))).map ((grayHomRight K).map F) :=
  pullback.lift_fst _ _ _

theorem coneObject_hom_ext {α : Bool} {d : K ⟶ X} {T : DiagSet.{u}} {f g : T ⟶ coneObject α d}
    (h₁ : f ≫ coneObjectι α d = g ≫ coneObjectι α d)
    (h₂ : f ≫ coneObjectπ α d = g ≫ coneObjectπ α d) : f = g :=
  pullback.hom_ext h₁ h₂

@[reassoc (attr := simp)]
theorem eqToHom_coneObjectι {α : Bool} {d d' : K ⟶ X} (h : d = d') :
    eqToHom (congrArg (coneObject α) h) ≫ coneObjectι α d' = coneObjectι α d := by
  subst h
  exact Category.id_comp _

@[reassoc (attr := simp)]
theorem eqToHom_coneObjectπ {α : Bool} {d d' : K ⟶ X} (h : d = d') :
    eqToHom (congrArg (coneObject α) h) ≫ coneObjectπ α d' = coneObjectπ α d := by
  subst h
  exact Category.id_comp _

theorem coneObjectMap_id (α : Bool) (d : K ⟶ X) :
    coneObjectMap α d (𝟙 X) = eqToHom (congrArg (coneObject α) (Category.comp_id d).symm) :=
  coneObject_hom_ext (by simp) (by simp)

theorem coneObjectMap_comp (α : Bool) (d : K ⟶ X) (F : X ⟶ Y) (G : Y ⟶ Z) :
    coneObjectMap α d (F ≫ G) ≫ eqToHom (congrArg (coneObject α) (Category.assoc d F G).symm) =
      coneObjectMap α d F ≫ coneObjectMap α (d ≫ F) G :=
  coneObject_hom_ext (by simp) (by simp)

def IsLimitCone (α : Bool) (d : K ⟶ X) (c : (coneObject α d).Vertex) : Prop :=
  (coneObject α d).HasContractibleHoms α c

instance isIso_coneObjectπ_empty (α : Bool) : IsIso (coneObjectπ α (initial.to X)) := by
  have hT := isTerminalGrayHomRightInitial X
  have h (B : DiagSet.{u}) : IsTerminal ((grayHomRight B).obj ((grayHomRight (⊥_ _)).obj X)) :=
    have := (grayTensorRightAdjunction B).rightAdjoint_preservesLimits
    hT.isTerminalObj (grayHomRight B) _
  have : IsIso ((grayHomRestrict intervalBoundaryι).app ((grayHomRight (⊥_ _)).obj X)) :=
    isIso_of_isTerminal (h _) (h _) _
  exact (isPullback_coneObject α (initial.to X)).isIso_snd_of_isIso

theorem isLimitCone_empty_iff (α : Bool) (hX : IsInftyCategory 1 X)
    (c : (coneObject α (initial.to X)).Vertex) :
    IsLimitCone α (initial.to X) c ↔
      X.HasContractibleHoms α (c.map (coneObjectπ α (initial.to X))) := by
  have : HomotopicalAlgebra.WeakEquivalence
      ((DiagSet.toInfty 1).map (coneObjectπ α (initial.to X))) :=
    (HomotopicalAlgebra.weakEquivalence_iff _).2
      ((HomotopicalAlgebra.weakEquivalences _).of_isIso _)
  exact (DiagSet.hasContractibleHoms_map_iff (isInftyCategory_coneObject α _ hX) hX _ α c).symm

theorem IsLimitCone.isEquivalence_edge {α : Bool} {d : K ⟶ X} (hX : IsInftyCategory 1 X)
    {c c' : (coneObject α d).Vertex} (hc : IsLimitCone α d c) (hc' : IsLimitCone α d c')
    (e : (coneObject α d).Edge c c') : IsEquivalence (coneObject α d) e.cell :=
  DiagSet.isEquivalence_of_hasContractibleHoms (isInftyCategory_coneObject α d hX) α hc hc' e

end Atoms.Diagrammatic

import Atoms.Diagrammatic.Joyal.GrayHomComparison

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra MonoidalCategory
open CartesianMonoidalCategory Simplicial
open Atoms.Homotopical Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian SSet.modelCategoryJoyal

variable (S : SSet.{u})

private noncomputable def faceNerveFlatTensorAdjunction :=
  (MarkedPresheaf.flatForgetAdjunction edgeMarking).comp
    (ihom.adjunction (faceNerve.obj (SSet.toDiagSet.obj S)))

private noncomputable def tensorLeftFaceNerveAdjunction :=
  (ihom.adjunction S).comp faceNerveSSetAdjunction.{u}

private theorem isQuillen_faceNerveFlatTensorAdjunction :
    (faceNerveFlatTensorAdjunction S).IsQuillen :=
  Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.comp
    (MarkedSSet.isQuillen_ihomAdjunction (faceNerve.obj (SSet.toDiagSet.obj S)))

private theorem isQuillen_tensorLeftFaceNerveAdjunction :
    (tensorLeftFaceNerveAdjunction S).IsQuillen :=
  (isQuillen_ihomAdjunction S).comp isQuillen_faceNerveSSetAdjunction

private noncomputable def faceNerveTensorLeftFlat :
    MonoidalCategory.tensorLeft S ⋙ SSet.toDiagSet ⋙ faceNerve ⟶
      MarkedPresheaf.flat edgeMarking ⋙
        MonoidalCategory.tensorLeft (faceNerve.obj (SSet.toDiagSet.obj S)) where
  app K := lift (faceNerve.map (SSet.toDiagSet.map (fst S K)))
    (faceNerve.map (SSet.toDiagSet.map (snd S K)) ≫ faceNerveToDiagSetFlat.app K)
  naturality K K' k := by
    have hk : (MonoidalCategory.tensorLeft S).map k = S ◁ k := rfl
    have hk' : (MonoidalCategory.tensorLeft (faceNerve.obj (SSet.toDiagSet.obj S))).map
        ((MarkedPresheaf.flat edgeMarking).map k) = _ ◁ (MarkedPresheaf.flat edgeMarking).map k :=
      rfl
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp only [Functor.comp_map, Category.assoc, lift_fst, hk, hk', whiskerLeft_fst,
        ← Functor.map_comp]
    · simp only [Functor.comp_map, Category.assoc, lift_snd, hk, hk', whiskerLeft_snd,
        lift_snd_assoc]
      rw [← Functor.map_comp_assoc, ← Functor.map_comp, whiskerLeft_snd, Functor.map_comp,
        Functor.map_comp_assoc]
      exact congrArg (_ ≫ ·) (faceNerveToDiagSetFlat.naturality k)

private theorem weakEquivalence_faceNerveTensorLeftFlat_app (K : SSet.{u}) :
    WeakEquivalence ((faceNerveTensorLeftFlat S).app K) := by
  have := weakEquivalence_faceNerveToDiagSetFlat_app S
  have := weakEquivalence_faceNerveToDiagSetFlat_app (S ⊗ K)
  have := MarkedSSet.weakEquivalence_tensorHom (faceNerveToDiagSetFlat.app S)
    (𝟙 ((MarkedPresheaf.flat edgeMarking).obj K))
  have h₁ : (SSet.flatTensorIso S K).hom ≫ fst _ _ =
      (MarkedPresheaf.flat edgeMarking).map (fst S K) := MarkedPresheaf.hom_ext rfl
  have h₂ : (SSet.flatTensorIso S K).hom ≫ snd _ _ =
      (MarkedPresheaf.flat edgeMarking).map (snd S K) := MarkedPresheaf.hom_ext rfl
  have e : (faceNerveTensorLeftFlat S).app K ≫ (faceNerveToDiagSetFlat.app S ⊗ₘ
      𝟙 ((MarkedPresheaf.flat edgeMarking).obj K)) =
      faceNerveToDiagSetFlat.app (S ⊗ K) ≫ (SSet.flatTensorIso S K).hom := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · simp only [faceNerveTensorLeftFlat, Category.assoc, tensorHom_fst, lift_fst_assoc, h₁]
      exact faceNerveToDiagSetFlat.naturality (fst S K)
    · simp only [faceNerveTensorLeftFlat, Category.assoc, tensorHom_snd, lift_snd, h₂,
        Category.comp_id]
      exact faceNerveToDiagSetFlat.naturality (snd S K)
  have : WeakEquivalence ((faceNerveTensorLeftFlat S).app K ≫ (faceNerveToDiagSetFlat.app S ⊗ₘ
      𝟙 ((MarkedPresheaf.flat edgeMarking).obj K))) := by
    rw [e]
    infer_instance
  exact weakEquivalence_of_postcomp _ (faceNerveToDiagSetFlat.app S ⊗ₘ
    𝟙 ((MarkedPresheaf.flat edgeMarking).obj K))

noncomputable def markedExponentialComparison :
    ihom (faceNerve.obj (SSet.toDiagSet.obj S)) ⋙ MarkedPresheaf.forget (D := edgeMarking) ⟶
      faceNerveRight ⋙ DiagSet.toSSet ⋙ ihom S :=
  conjugateEquiv (faceNerveFlatTensorAdjunction S) (tensorLeftFaceNerveAdjunction S)
    (faceNerveTensorLeftFlat S)

theorem weakEquivalence_markedExponentialComparison_app (C : MarkedSSet.{u}) [IsFibrant C] :
    WeakEquivalence ((markedExponentialComparison S).app C) :=
  (isQuillen_faceNerveFlatTensorAdjunction S).weakEquivalence_conjugateEquiv_app
    (isQuillen_tensorLeftFaceNerveAdjunction S) (faceNerveTensorLeftFlat S)
    (fun K _ => weakEquivalence_faceNerveTensorLeftFlat_app S K) C

private theorem homEquiv_curry_comp_markedExponentialComparison_app {K : SSet.{u}}
    {C : MarkedSSet.{u}}
    (g : faceNerve.obj (SSet.toDiagSet.obj S) ⊗ (MarkedPresheaf.flat edgeMarking).obj K ⟶ C) :
    (MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv K _ (MonoidalClosed.curry g) ≫
        (markedExponentialComparison S).app C =
      MonoidalClosed.curry (faceNerveSSetAdjunction.homEquiv (S ⊗ K) C
        ((faceNerveTensorLeftFlat S).app K ≫ g)) := by
  have h := homEquiv_conjugateEquiv_app (faceNerveFlatTensorAdjunction S)
    (tensorLeftFaceNerveAdjunction S) (faceNerveTensorLeftFlat S) (c := K) g
  have h₁ := congrArg (fun e => e K C g) (Adjunction.comp_homEquiv
    (MarkedPresheaf.flatForgetAdjunction edgeMarking)
    (ihom.adjunction (faceNerve.obj (SSet.toDiagSet.obj S))))
  have h₂ := congrArg (fun e => e K C ((faceNerveTensorLeftFlat S).app K ≫ g))
    (Adjunction.comp_homEquiv (ihom.adjunction S) faceNerveSSetAdjunction.{u})
  exact (congrArg (· ≫ (markedExponentialComparison S).app C) h₁.symm).trans
    (h.symm.trans h₂)

noncomputable def markedConstDiagram (C : MarkedSSet.{u}) :
    C ⟶ (ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C :=
  MonoidalClosed.curry (snd _ C)

noncomputable def markedDiagramPoint {C : MarkedSSet.{u}}
    (d : SSet.toDiagSet.obj S ⟶ faceNerveRight.obj C) :
    𝟙_ SSet.{u} ⟶ (MarkedPresheaf.forget (D := edgeMarking)).obj
      ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C) :=
  (MarkedPresheaf.flatForgetAdjunction edgeMarking).homEquiv (𝟙_ SSet.{u}) _
    (MonoidalClosed.curry (fst _ _ ≫ (faceNerveAdjunction.homEquiv _ C).symm d))

theorem markedConstDiagram_comp_markedExponentialComparison_app (C : MarkedSSet.{u}) :
    (MarkedPresheaf.forget (D := edgeMarking)).map (markedConstDiagram S C) ≫
        (markedExponentialComparison S).app C =
      faceNerveRightComparison.app C ≫
        SSet.constDiagram S (DiagSet.toSSet.obj (faceNerveRight.obj C)) := by
  let adj := MarkedPresheaf.flatForgetAdjunction edgeMarking
  let A : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj C
  let ε : (MarkedPresheaf.flat edgeMarking).obj A ⟶ C := adj.counit.app C
  have hε : adj.homEquiv A C ε = 𝟙 A :=
    (adj.homEquiv_unit _ _ _).trans (adj.right_triangle_components C)
  have h₁ : (MarkedPresheaf.forget (D := edgeMarking)).map (markedConstDiagram S C) =
      adj.homEquiv A _ (MonoidalClosed.curry
        (snd (faceNerve.obj (SSet.toDiagSet.obj S)) _ ≫ ε)) :=
    ((congrArg (adj.homEquiv A _) ((congrArg MonoidalClosed.curry
      (whiskerLeft_snd _ ε).symm).trans (MonoidalClosed.curry_natural_left _ _))).trans
        ((adj.homEquiv_naturality_right _ _).trans
          ((congrArg (· ≫ _) hε).trans (Category.id_comp _)))).symm
  have e : (faceNerveTensorLeftFlat S).app A ≫
      snd (faceNerve.obj (SSet.toDiagSet.obj S)) _ ≫ ε =
      (SSet.toDiagSet ⋙ faceNerve).map (snd S A) ≫ faceNerveToDiagSetFlat.app A ≫ ε :=
    (lift_snd_assoc _ _ _).trans (Category.assoc _ _ _)
  have h₂ : faceNerveSSetAdjunction.homEquiv (S ⊗ A) C ((faceNerveTensorLeftFlat S).app A ≫
      snd (faceNerve.obj (SSet.toDiagSet.obj S)) _ ≫ ε) =
      snd S A ≫ faceNerveRightComparison.app C :=
    (congrArg (faceNerveSSetAdjunction.homEquiv (S ⊗ A) C) e).trans
      ((faceNerveSSetAdjunction.homEquiv_naturality_left (snd S A) _).trans
        (congrArg (snd S A ≫ ·) ((homEquiv_conjugateEquiv_app adj faceNerveSSetAdjunction.{u}
          faceNerveToDiagSetFlat ε).trans ((congrArg (· ≫ _) hε).trans (Category.id_comp _)))))
  exact (congrArg (· ≫ _) h₁).trans
    ((homEquiv_curry_comp_markedExponentialComparison_app S _).trans
      ((congrArg MonoidalClosed.curry h₂).trans ((congrArg MonoidalClosed.curry
        (whiskerLeft_snd _ _).symm).trans (MonoidalClosed.curry_natural_left _ _))))

theorem markedDiagramPoint_comp_markedExponentialComparison_app {C : MarkedSSet.{u}}
    (d : SSet.toDiagSet.obj S ⟶ faceNerveRight.obj C) :
    markedDiagramPoint S d ≫ (markedExponentialComparison S).app C =
      SSet.diagramPoint (sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d) := by
  let m : faceNerve.obj (SSet.toDiagSet.obj S) ⟶ C :=
    (faceNerveAdjunction.homEquiv (SSet.toDiagSet.obj S) C).symm d
  have e : (faceNerveTensorLeftFlat S).app (𝟙_ SSet.{u}) ≫
      fst (faceNerve.obj (SSet.toDiagSet.obj S)) _ ≫ m =
      (SSet.toDiagSet ⋙ faceNerve).map (fst S (𝟙_ SSet.{u})) ≫ m := lift_fst_assoc _ _ _
  have h : faceNerveSSetAdjunction.homEquiv S C m =
      sSetDiagSetAdj.unit.app S ≫ DiagSet.toSSet.map d :=
    (congrArg (fun e => e S C m) (Adjunction.comp_homEquiv DiagSet.Infty.sSetDiagSetAdj
      faceNerveAdjunction.{u})).trans ((congrArg (DiagSet.Infty.sSetDiagSetAdj.homEquiv S _)
        (Equiv.apply_symm_apply _ d)).trans (Adjunction.homEquiv_unit _ _ _ _))
  exact (homEquiv_curry_comp_markedExponentialComparison_app S _).trans
    (congrArg MonoidalClosed.curry ((congrArg (faceNerveSSetAdjunction.homEquiv _ C) e).trans
      ((faceNerveSSetAdjunction.homEquiv_naturality_left (fst S (𝟙_ SSet.{u})) m).trans
        (congrArg (fst S (𝟙_ SSet.{u}) ≫ ·) h))))

private theorem faceNerveRight_map_markedConstDiagram_comp (C : MarkedSSet.{u}) :
    faceNerveRight.map (markedConstDiagram S C) ≫
        (grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C =
      constDiagram (SSet.toDiagSet.obj S) (faceNerveRight.obj C) := by
  let adj : faceNerve.{u} ⊣ faceNerveRight := faceNerveAdjunction
  let Y : DiagSet.{u} := faceNerveRight.obj C
  let ε : faceNerve.obj Y ⟶ C := adj.counit.app C
  have hε : adj.homEquiv Y C ε = 𝟙 Y :=
    (adj.homEquiv_unit _ _ _).trans (adj.right_triangle_components C)
  have h₁ : faceNerveRight.map (markedConstDiagram S C) =
      adj.homEquiv Y _ (MonoidalClosed.curry
        (snd (faceNerve.obj (SSet.toDiagSet.obj S)) _ ≫ ε)) :=
    ((congrArg (adj.homEquiv Y _) ((congrArg MonoidalClosed.curry
      (whiskerLeft_snd _ ε).symm).trans (MonoidalClosed.curry_natural_left _ _))).trans
        ((adj.homEquiv_naturality_right _ _).trans
          ((congrArg (· ≫ _) hε).trans (Category.id_comp _)))).symm
  have h₂ : adj.homEquiv _ C (lift (faceNerve.map (grayTensorSnd Y (SSet.toDiagSet.obj S)))
      (faceNerve.map (grayTensorFst Y (SSet.toDiagSet.obj S))) ≫
        snd (faceNerve.obj (SSet.toDiagSet.obj S)) _ ≫ ε) =
      grayTensorFst Y (SSet.toDiagSet.obj S) :=
    (congrArg (adj.homEquiv _ C) (lift_snd_assoc _ _ _)).trans
      ((adj.homEquiv_naturality_left _ ε).trans
        ((congrArg (_ ≫ ·) hε).trans (Category.comp_id _)))
  exact (congrArg (· ≫ _) h₁).trans
    ((homEquiv_curry_comp_grayHomRightFaceNerveIso_hom_app (SSet.toDiagSet.obj S) _).trans
      (congrArg ((grayTensorRightAdjunction (SSet.toDiagSet.obj S)).homEquiv Y Y) h₂))

theorem markedConstDiagram_comp_faceNerveRightComparison_app (C : MarkedSSet.{u}) :
    (MarkedPresheaf.forget (D := edgeMarking)).map (markedConstDiagram S C) ≫
        faceNerveRightComparison.app _ ≫ DiagSet.toSSet.map
          ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C) =
      faceNerveRightComparison.app C ≫
        DiagSet.toSSet.map (constDiagram (SSet.toDiagSet.obj S) (faceNerveRight.obj C)) :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (faceNerveRightComparison.naturality (markedConstDiagram S C))).trans
      ((Category.assoc _ _ _).trans (congrArg (faceNerveRightComparison.app C ≫ ·)
        ((DiagSet.toSSet.map_comp _ _).symm.trans
          (congrArg DiagSet.toSSet.map (faceNerveRight_map_markedConstDiagram_comp S C))))))

theorem markedDiagramPoint_comp_faceNerveRightComparison_app {C : MarkedSSet.{u}}
    (d : SSet.toDiagSet.obj S ⟶ faceNerveRight.obj C) :
    markedDiagramPoint S d ≫ faceNerveRightComparison.app _ ≫ DiagSet.toSSet.map
        ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C) =
      isTerminalToSSetBallAtomPoint.from _ ≫ DiagSet.toSSet.map (diagramPoint d) := by
  let adj : faceNerve.{u} ⊣ faceNerveRight := faceNerveAdjunction
  let K : DiagSet.{u} := SSet.toDiagSet.obj S
  let T : DiagSet.{u} := SSet.toDiagSet.obj (𝟙_ SSet.{u})
  let m : faceNerve.obj K ⟶ C := (adj.homEquiv K C).symm d
  let b : T ⟶ ball.{u} atomPoint := isTerminalBallAtomPoint.from T
  have h₁ : markedDiagramPoint S d ≫ faceNerveRightComparison.app _ =
      sSetDiagSetAdj.homEquiv (𝟙_ SSet.{u}) _ (adj.homEquiv T _
        (MonoidalClosed.curry (fst (faceNerve.obj K) (faceNerve.obj T) ≫ m))) :=
    (homEquiv_conjugateEquiv_app (MarkedPresheaf.flatForgetAdjunction edgeMarking)
      faceNerveSSetAdjunction.{u} faceNerveToDiagSetFlat
      (MonoidalClosed.curry (fst (faceNerve.obj K) _ ≫ m))).symm.trans
      ((congrArg (fun e => e (𝟙_ SSet.{u}) _ (faceNerveToDiagSetFlat.app (𝟙_ SSet.{u}) ≫
          MonoidalClosed.curry (fst (faceNerve.obj K) _ ≫ m)))
        (Adjunction.comp_homEquiv DiagSet.Infty.sSetDiagSetAdj faceNerveAdjunction.{u})).trans
        (congrArg (fun w => sSetDiagSetAdj.homEquiv (𝟙_ SSet.{u}) _ (adj.homEquiv T _ w))
          ((MonoidalClosed.curry_natural_left _ _).symm.trans
            (congrArg MonoidalClosed.curry (whiskerLeft_fst_assoc _ _ _)))))
  have h₂ : adj.homEquiv T _ (MonoidalClosed.curry (fst (faceNerve.obj K) (faceNerve.obj T) ≫ m)) ≫
      (grayHomRightFaceNerveIso K).hom.app C = b ≫ diagramPoint d :=
    (homEquiv_curry_comp_grayHomRightFaceNerveIso_hom_app K _).trans
      ((congrArg ((grayTensorRightAdjunction K).homEquiv T _)
        ((congrArg (adj.homEquiv _ C) (lift_fst_assoc _ _ _)).trans
          ((adj.homEquiv_naturality_left _ m).trans
            (congrArg (grayTensorSnd T K ≫ ·) (Equiv.apply_symm_apply _ d))))).trans
        (comp_diagramPoint b d).symm)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
    ((sSetDiagSetAdj.homEquiv_naturality_right _ _).symm.trans
      ((congrArg (sSetDiagSetAdj.homEquiv (𝟙_ SSet.{u}) _) h₂).trans
        ((sSetDiagSetAdj.homEquiv_naturality_right b (diagramPoint d)).trans
          (congrArg (· ≫ DiagSet.toSSet.map (diagramPoint d))
            (isTerminalToSSetBallAtomPoint.hom_ext _ _))))))

theorem faceNerveRightComparison_app_comp_grayHomEvalVertex (s : S _⦋0⦌) (C : MarkedSSet.{u}) :
    faceNerveRightComparison.app ((ihom (faceNerve.obj (SSet.toDiagSet.obj S))).obj C) ≫
        DiagSet.toSSet.map ((grayHomRightFaceNerveIso (SSet.toDiagSet.obj S)).hom.app C ≫
          grayHomEvalVertex s (faceNerveRight.obj C)) =
      (markedExponentialComparison S).app C ≫
        SSet.evalVertex s (DiagSet.toSSet.obj (faceNerveRight.obj C)) := by
  let adj := MarkedPresheaf.flatForgetAdjunction edgeMarking
  let K := SSet.toDiagSet.obj S
  let E := (ihom (faceNerve.obj K)).obj C
  let A : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj E
  let LA := SSet.toDiagSet.obj A
  let g : faceNerve.obj K ⊗ (MarkedPresheaf.flat edgeMarking).obj A ⟶ C :=
    MonoidalClosed.uncurry ((adj.homEquiv A E).symm (𝟙 A))
  have hg : adj.homEquiv A E (MonoidalClosed.curry g) = 𝟙 A := by
    rw [MonoidalClosed.curry_uncurry, Equiv.apply_symm_apply]
  let t : A ⟶ S := SSet.stdSimplex.isTerminalObj₀.from A ≫ SSet.yonedaEquiv.symm s
  let i : ball.{u} atomPoint ⟶ K :=
    pointIsoToDiagSetStdSimplex.hom ≫ SSet.toDiagSet.map (SSet.yonedaEquiv.symm s)
  have ht : inv (grayTensorFst LA (ball.{u} atomPoint)) ≫ grayTensorSnd LA _ ≫ i =
      SSet.toDiagSet.map t := by
    have h : inv (grayTensorFst LA (ball.{u} atomPoint)) ≫ grayTensorSnd LA _ ≫
        pointIsoToDiagSetStdSimplex.hom =
          SSet.toDiagSet.map (SSet.stdSimplex.isTerminalObj₀.from A) :=
      (Category.assoc _ _ _).symm.trans
        ((Iso.eq_comp_inv _).1 (isTerminalBallAtomPoint.hom_ext _ _))
    rw [Functor.map_comp, ← h]
    simp only [i, Category.assoc]
  have e : faceNerve.map (inv (grayTensorFst LA (ball.{u} atomPoint)) ≫
        (grayTensorLeft LA).map i) ≫
      lift (faceNerve.map (grayTensorSnd LA K)) (faceNerve.map (grayTensorFst LA K)) ≫
        (faceNerve.obj K ◁ faceNerveToDiagSetFlat.app A) =
      (SSet.toDiagSet ⋙ faceNerve).map (lift t (𝟙 A)) ≫ (faceNerveTensorLeftFlat S).app A := by
    refine CartesianMonoidalCategory.hom_ext _ _ ?_ ?_
    · rw [Category.assoc, Category.assoc, whiskerLeft_fst, lift_fst, ← Functor.map_comp,
        Category.assoc, grayTensorLeft_map_grayTensorSnd, ht, faceNerveTensorLeftFlat,
        Category.assoc, lift_fst, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp,
        lift_fst]
    · rw [Category.assoc, Category.assoc, whiskerLeft_snd, lift_snd_assoc,
        ← Functor.map_comp_assoc, Category.assoc, grayTensorLeft_map_eq,
        grayTensorBifunctor_map_grayTensorFst, Category.comp_id, IsIso.inv_hom_id,
        faceNerve.map_id, Category.id_comp, faceNerveTensorLeftFlat, Category.assoc, lift_snd,
        Functor.comp_map,
        ← Functor.map_comp_assoc, ← Functor.map_comp, lift_snd, SSet.toDiagSet.map_id,
        faceNerve.map_id, Category.id_comp]
  have h₁ : adj.homEquiv A E (MonoidalClosed.curry g) ≫ faceNerveRightComparison.app E =
      sSetDiagSetAdj.homEquiv A _ (faceNerveAdjunction.homEquiv LA E
        (faceNerveToDiagSetFlat.app A ≫ MonoidalClosed.curry g)) :=
    (homEquiv_conjugateEquiv_app adj faceNerveSSetAdjunction faceNerveToDiagSetFlat
      (MonoidalClosed.curry g)).symm.trans (congrArg
        (fun e => e A E (faceNerveToDiagSetFlat.app A ≫ MonoidalClosed.curry g))
        (Adjunction.comp_homEquiv DiagSet.Infty.sSetDiagSetAdj faceNerveAdjunction.{u}))
  have hL : adj.homEquiv A E (MonoidalClosed.curry g) ≫ faceNerveRightComparison.app E ≫
      DiagSet.toSSet.map ((grayHomRightFaceNerveIso K).hom.app C ≫
        grayHomEvalVertex s (faceNerveRight.obj C)) =
      sSetDiagSetAdj.homEquiv A _ (faceNerveAdjunction.homEquiv LA C
        ((SSet.toDiagSet ⋙ faceNerve).map (lift t (𝟙 A)) ≫ (faceNerveTensorLeftFlat S).app A ≫
          g)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h₁).trans
      ((sSetDiagSetAdj.homEquiv_naturality_right _ _).symm.trans
        (congrArg (sSetDiagSetAdj.homEquiv A _) ?_)))
    have h₂ : faceNerveAdjunction.homEquiv LA E
          (faceNerveToDiagSetFlat.app A ≫ MonoidalClosed.curry g) =
        faceNerveAdjunction.homEquiv LA E
          (MonoidalClosed.curry ((faceNerve.obj K ◁ faceNerveToDiagSetFlat.app A) ≫ g)) :=
      congrArg _ (MonoidalClosed.curry_natural_left _ _).symm
    have h₃ := homEquiv_curry_comp_grayHomRightFaceNerveIso_hom_app K (T := LA)
      ((faceNerve.obj K ◁ faceNerveToDiagSetFlat.app A) ≫ g)
    have h₄ (F : grayTensor LA K ⟶ faceNerveRight.obj C) :
        (grayTensorRightAdjunction K).homEquiv LA _ F ≫ grayHomEvalVertex s (faceNerveRight.obj C) =
          inv (grayTensorFst LA (ball.{u} atomPoint)) ≫ (grayTensorLeft LA).map i ≫ F := by
      rw [grayHomEvalVertex, ← Category.assoc, homEquiv_comp_grayHomRestrict,
        homEquiv_comp_grayHomRightPointIso_hom_app]
    exact (congrArg (· ≫ _) h₂).trans ((Category.assoc _ _ _).symm.trans
      ((congrArg (· ≫ _) h₃).trans ((h₄ _).trans ((Category.assoc _ _ _).symm.trans
        ((faceNerveAdjunction.homEquiv_naturality_left _ _).symm.trans
          (congrArg _ ((reassoc_of% e) g)))))))
  have hR : adj.homEquiv A E (MonoidalClosed.curry g) ≫ (markedExponentialComparison S).app C ≫
        SSet.evalVertex s (DiagSet.toSSet.obj (faceNerveRight.obj C)) =
      sSetDiagSetAdj.homEquiv A _ (faceNerveAdjunction.homEquiv LA C
        ((SSet.toDiagSet ⋙ faceNerve).map (lift t (𝟙 A)) ≫ (faceNerveTensorLeftFlat S).app A ≫
          g)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
      (homEquiv_curry_comp_markedExponentialComparison_app S g)).trans
        ((SSet.comp_evalVertex s _).trans ?_))
    refine (congrArg (_ ≫ ·) (MonoidalClosed.uncurry_curry _)).trans
      ((faceNerveSSetAdjunction.homEquiv_naturality_left _ _).symm.trans ?_)
    exact congrArg (fun e => e A C ((SSet.toDiagSet ⋙ faceNerve).map (lift t (𝟙 A)) ≫
      (faceNerveTensorLeftFlat S).app A ≫ g))
      (Adjunction.comp_homEquiv DiagSet.Infty.sSetDiagSetAdj faceNerveAdjunction.{u})
  have h := hL.trans hR.symm
  rwa [hg, Category.id_comp, Category.id_comp] at h

end Atoms.Diagrammatic

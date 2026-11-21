import Atoms.Diagrammatic.Fibration.CartesianArrowFibration
import Atoms.Diagrammatic.Fibration.RelativeReplacement
import Atoms.Homotopical.Simplicial.FullSubcomplex
import Atoms.Homotopical.Simplicial.CartesianMappingSpace
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.CartesianArrow

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra Atoms.Shape Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open SSet.modelCategoryJoyal MarkedSSet.modelCategoryCartesian

theorem DiagSet.isCartesianEdge_map_iff_of_weakEquivalence {E S E' S' : DiagSet.{u}}
    (p : E ⟶ S) (p' : E' ⟶ S') (a : E ⟶ E') (b : S ⟶ S')
    (h : a ≫ p' = p ≫ b)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    [Fibration ((DiagSet.toInfty 1).map p')] [IsFibrant ((DiagSet.toInfty 1).obj S')]
    [WeakEquivalence ((DiagSet.toInfty 1).map a)]
    [WeakEquivalence ((DiagSet.toInfty 1).map b)] {x y : E.Vertex} (e : E.Edge x y) :
    DiagSet.IsCartesianEdge p' (e.map a) ↔ DiagSet.IsCartesianEdge p e := by
  have : IsFibrant ((DiagSet.toInfty 1).obj E) := isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have : IsFibrant ((DiagSet.toInfty 1).obj E') :=
    isFibrant_of_fibration ((DiagSet.toInfty 1).map p')
  have : (DiagSet.toSSet.obj E).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj E) inferInstance
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have : (DiagSet.toSSet.obj E').Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj E') inferInstance
  have : (DiagSet.toSSet.obj S').Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S') inferInstance
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  have : SSet.InnerFibration (DiagSet.toSSet.map p') :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p') inferInstance
  have : WeakEquivalence (DiagSet.toSSet.map a) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map a)
  have : WeakEquivalence (DiagSet.toSSet.map b) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map b)
  rw [DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration,
    DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration,
    DiagSet.yonedaEquiv_symm_edgeEquivSSet_map]
  exact SSet.modelCategoryJoyal.isCartesianEdge_comp_iff_of_weakEquivalence
    (DiagSet.toSSet.map a) (DiagSet.toSSet.map b)
    ((DiagSet.toSSet.map_comp a p').symm.trans
      ((congrArg DiagSet.toSSet.map h).trans (DiagSet.toSSet.map_comp p b))) _

private theorem isCartesianEdge_grayArrowVertexEquiv_of_invStruct {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    {x y : (DiagSet.toSSet.obj
      ((grayHomRight markedInterval.{u}.underlying).obj E)) _⦋0⦌}
    (e : SSet.Edge x y) (he : Nonempty e.InvStruct)
    (hx : DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E x))) :
    DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E y)) := by
  have hE : IsInftyCategory 1 E := isInftyCategory_of_isFibrant 1
    ((DiagSet.toInfty 1).obj E) (isFibrant_of_fibration ((DiagSet.toInfty 1).map p))
  have hA := isInftyCategory_grayHomRight markedInterval.{u}.underlying hE
  let e' := ((grayHomRight markedInterval.{u}.underlying).obj E).edgeEquivSSet.symm e
  have hi : IsEquivalence ((grayHomRight markedInterval.{u}.underlying).obj E) e'.cell := by
    apply (isEquivalence_map_iso_iff atomSimplexOneIsoGlobe _).1
    have hs : ((grayHomRight markedInterval.{u}.underlying).obj E).map
        atomSimplexOneIsoGlobe.hom.op e'.cell = e.edge :=
      (DiagSet.edgeEquivSSet_edge e').symm.trans (congrArg SSet.Edge.edge
        (((grayHomRight markedInterval.{u}.underlying).obj E).edgeEquivSSet.apply_symm_apply e))
    rw [hs]
    exact isEquivalence_of_invStruct hA e he
  exact (DiagSet.isCartesianEdge_grayArrowVertex_iff_of_isEquivalence p e' hi).1 hx

private theorem isCartesianEdge_grayArrowVertexEquiv_iff_map {E S E' S' : DiagSet.{u}}
    (p : E ⟶ S) (p' : E' ⟶ S') (a : E ⟶ E') (b : S ⟶ S')
    (h : a ≫ p' = p ≫ b)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    [Fibration ((DiagSet.toInfty 1).map p')] [IsFibrant ((DiagSet.toInfty 1).obj S')]
    [WeakEquivalence ((DiagSet.toInfty 1).map a)]
    [WeakEquivalence ((DiagSet.toInfty 1).map b)]
    (x : ((grayHomRight markedInterval.{u}.underlying).obj E).Vertex) :
    DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E x)) ↔
      DiagSet.IsCartesianEdge p' (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E'
        (DiagSet.Vertex.map ((grayHomRight markedInterval.{u}.underlying).map a) x))) := by
  have hc := DiagSet.isCartesianEdge_map_iff_of_weakEquivalence p p' a b h
    (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E x))
  have hm := DiagSet.grayArrowVertexEquiv_map a x
  exact hc.symm.trans (DiagSet.isCartesianEdge_congr p' hm.symm)

private theorem exists_weakEquivalence_toSSet_cartesianArrow_restriction {E S E' S' : DiagSet.{u}}
    (p : E ⟶ S) (p' : E' ⟶ S') (a : E ⟶ E') (b : S ⟶ S')
    (h : a ≫ p' = p ≫ b)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    [Fibration ((DiagSet.toInfty 1).map p')] [IsFibrant ((DiagSet.toInfty 1).obj S')]
    [WeakEquivalence ((DiagSet.toInfty 1).map a)]
    [WeakEquivalence ((DiagSet.toInfty 1).map b)] :
    let X := (grayHomRight markedInterval.{u}.underlying).obj E
    let Y := (grayHomRight markedInterval.{u}.underlying).obj E'
    let P := fun z : X.Vertex => DiagSet.IsCartesianEdge p
      (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E z))
    let Q := fun z : Y.Vertex => DiagSet.IsCartesianEdge p'
      (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E' z))
    ∃ g : DiagSet.toSSet.obj (X.fullSubpresheaf P).toFunctor ⟶
        DiagSet.toSSet.obj (Y.fullSubpresheaf Q).toFunctor,
      WeakEquivalence g ∧ g ≫ DiagSet.toSSet.map (Y.fullSubpresheaf Q).ι =
        DiagSet.toSSet.map (X.fullSubpresheaf P).ι ≫
          DiagSet.toSSet.map ((grayHomRight markedInterval.{u}.underlying).map a) := by
  dsimp only
  let X := (grayHomRight markedInterval.{u}.underlying).obj E
  let Y := (grayHomRight markedInterval.{u}.underlying).obj E'
  let P := fun z : X.Vertex => DiagSet.IsCartesianEdge p
    (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E z))
  let Q := fun z : Y.Vertex => DiagSet.IsCartesianEdge p'
    (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E' z))
  have hE := isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have hE' := isFibrant_of_fibration ((DiagSet.toInfty 1).map p')
  have hX : IsFibrant ((DiagSet.toInfty 1).obj X) := (isFibrant_infty_iff 1 _).2
    (isInftyCategory_grayHomRight _ ((isFibrant_infty_iff 1 _).1 hE))
  have hY : IsFibrant ((DiagSet.toInfty 1).obj Y) := (isFibrant_infty_iff 1 _).2
    (isInftyCategory_grayHomRight _ ((isFibrant_infty_iff 1 _).1 hE'))
  have : (DiagSet.toSSet.obj X).Quasicategory := quasicategory_toSSet_obj X hX
  have : (DiagSet.toSSet.obj Y).Quasicategory := quasicategory_toSSet_obj Y hY
  let f : DiagSet.toSSet.obj X ⟶ DiagSet.toSSet.obj Y :=
    DiagSet.toSSet.map ((grayHomRight markedInterval.{u}.underlying).map a)
  have : WeakEquivalence f := by
    let q := isQuillen_sSetDiagSetAdj.comp
      (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one markedInterval.{u}.underlying)
    exact q.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map a)
  have hpq (x : (DiagSet.toSSet.obj X) _⦋0⦌) : P x ↔ Q (f.app (op ⦋0⦌) x) := by
    exact isCartesianEdge_grayArrowVertexEquiv_iff_map p p' a b h x
  let g := SSet.fullSubcomplexMap f P Q (fun x => (hpq x).1)
  have : WeakEquivalence g := weakEquivalence_fullSubcomplex_map f P Q hpq
    (fun e he => isCartesianEdge_grayArrowVertexEquiv_of_invStruct p' e he) g rfl
  refine ⟨(DiagSet.toSSetFullSubpresheafIso X P).hom ≫ g ≫
    (DiagSet.toSSetFullSubpresheafIso Y Q).inv, ?_, ?_⟩
  · have hpi : WeakEquivalence (DiagSet.toSSetFullSubpresheafIso X P).hom := by infer_instance
    have hqi : WeakEquivalence (DiagSet.toSSetFullSubpresheafIso Y Q).inv := by infer_instance
    apply (weakEquivalence_iff _).2
    exact (weakEquivalences SSet.{u}).comp_mem _ _ hpi.mem
      ((weakEquivalences SSet.{u}).comp_mem _ _ (mem_weakEquivalences g) hqi.mem)
  · rfl

private theorem weakEquivalence_toSSet_map_mapArrowRight {E S E' S' A B : DiagSet.{u}}
    (j : A ⟶ B) [Mono j] (p : E ⟶ S) (p' : E' ⟶ S')
    (a : E ⟶ E') (b : S ⟶ S') (h : a ≫ p' = p ≫ b)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    [Fibration ((DiagSet.toInfty 1).map p')] [IsFibrant ((DiagSet.toInfty 1).obj S')]
    [WeakEquivalence ((DiagSet.toInfty 1).map a)]
    [WeakEquivalence ((DiagSet.toInfty 1).map b)] :
    WeakEquivalence (DiagSet.toSSet.map
      (Functor.PullbackObjObj.mapArrowRight (f₁ := Arrow.mk j)
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor j p)
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor j p')
          (Arrow.homMk' a b h)).right) := by
  let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor j p
  let Q' := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor j p'
  let t := Functor.PullbackObjObj.mapArrowRight (f₁ := Arrow.mk j) Q Q'
    (Arrow.homMk' a b h)
  have hE := isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have hE' := isFibrant_of_fibration ((DiagSet.toInfty 1).map p')
  have hf (T Y : DiagSet.{u}) [IsFibrant ((DiagSet.toInfty 1).obj Y)] :
      IsFibrant (DiagSet.toSSet.obj ((grayHomRightBifunctor.obj (op T)).obj Y)) :=
    (isQuillen_sSetDiagSetAdj.comp
      (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one T)).isFibrant_obj
        ((DiagSet.toInfty 1).obj Y)
  have hw (T : DiagSet.{u}) {Y Z : DiagSet.{u}} (f : Y ⟶ Z)
      [IsFibrant ((DiagSet.toInfty 1).obj Y)] [IsFibrant ((DiagSet.toInfty 1).obj Z)]
      [WeakEquivalence ((DiagSet.toInfty 1).map f)] :
      WeakEquivalence (DiagSet.toSSet.map ((grayHomRight T).map f)) :=
    (isQuillen_sSetDiagSetAdj.comp
      (DiagSet.Infty.isQuillen_grayTensorRightAdjunction_one T)).weakEquivalence_map_of_isFibrant
        ((DiagSet.toInfty 1).map f)
  have := hf A E
  have := hf A E'
  have := hf A S
  have := hf A S'
  let wE : DiagSet.toSSet.obj ((grayHomRight B).obj S) ⟶
      DiagSet.toSSet.obj ((grayHomRight B).obj S') :=
    DiagSet.toSSet.map ((grayHomRight B).map b)
  let wB : DiagSet.toSSet.obj ((grayHomRight A).obj S) ⟶
      DiagSet.toSSet.obj ((grayHomRight A).obj S') :=
    DiagSet.toSSet.map ((grayHomRight A).map b)
  let wA : DiagSet.toSSet.obj ((grayHomRight A).obj E) ⟶
      DiagSet.toSSet.obj ((grayHomRight A).obj E') :=
    DiagSet.toSSet.map ((grayHomRight A).map a)
  have hwe : WeakEquivalence wE := hw B b
  have hwb : WeakEquivalence wB := hw A b
  have hwa : WeakEquivalence wA := hw A a
  have hr (Y : DiagSet.{u}) [IsFibrant ((DiagSet.toInfty 1).obj Y)] :
      Fibration (DiagSet.toSSet.map ((grayHomRightBifunctor.map j.op).app Y)) := by
    have hi : IsInftyCategory 1 Y :=
      isInftyCategory_of_isFibrant 1 ((DiagSet.toInfty 1).obj Y) inferInstance
    have := fibration_toInfty_one_grayHomRestrict j hi
    exact isQuillen_sSetDiagSetAdj.fibration_map ((DiagSet.toInfty 1).map
      ((grayHomRestrict j).app Y))
  have := hr S
  have := hr S'
  refine @CategoryTheory.IsPullback.weakEquivalence_map_of_fibration SSet.{u} _ _
    _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (DiagSet.toSSet.map_isPullback Q.isPullback).flip
    (DiagSet.toSSet.map_isPullback Q'.isPullback).flip _ _ _ _ _ _
      wE wB wA (DiagSet.toSSet.map t.right) ?_ ?_ ?_ ?_ hwe hwb hwa
  · exact (DiagSet.toSSet.map_comp _ _).symm.trans
      ((congrArg DiagSet.toSSet.map ((grayHomRestrict j).naturality b).symm).trans
        (DiagSet.toSSet.map_comp _ _))
  · exact (DiagSet.toSSet.map_comp _ _).symm.trans
      ((congrArg DiagSet.toSSet.map ((grayHomRight A).map_comp p b).symm).trans
        ((congrArg (fun f => DiagSet.toSSet.map ((grayHomRight A).map f)) h.symm).trans
          ((congrArg DiagSet.toSSet.map ((grayHomRight A).map_comp a p')).trans
            (DiagSet.toSSet.map_comp _ _))))
  · simp only [t, Functor.PullbackObjObj.mapArrowRight_right, ← Functor.map_comp,
      IsPullback.lift_snd]
    exact DiagSet.toSSet.map_comp _ _
  · simp only [t, Functor.PullbackObjObj.mapArrowRight_right, ← Functor.map_comp,
      IsPullback.lift_fst]
    exact DiagSet.toSSet.map_comp _ _

private theorem DiagSet.weakEquivalence_cartesianArrows_iff_of_weakEquivalence
    {E S E' S' : DiagSet.{u}} (p : E ⟶ S) (p' : E' ⟶ S')
    (a : E ⟶ E') (b : S ⟶ S') (h : a ≫ p' = p ≫ b)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    [Fibration ((DiagSet.toInfty 1).map p')] [IsFibrant ((DiagSet.toInfty 1).obj S')]
    [WeakEquivalence ((DiagSet.toInfty 1).map a)]
    [WeakEquivalence ((DiagSet.toInfty 1).map b)] :
    WeakEquivalence (DiagSet.toSSet.map
      ((DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E)
        (fun z => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv E z)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p).π)) ↔
    WeakEquivalence (DiagSet.toSSet.map
      ((DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E')
        (fun z => DiagSet.IsCartesianEdge p' (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv E' z)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p').π)) := by
  let i := (MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex.{u} true)
  let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor i p
  let Q' := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor i p'
  let t := Functor.PullbackObjObj.mapArrowRight (f₁ := Arrow.mk i) Q Q'
    (Arrow.homMk' a b h)
  have : Mono i := isTerminalBallAtomPoint.mono_from i
  have ht : WeakEquivalence (DiagSet.toSSet.map t.right) :=
    weakEquivalence_toSSet_map_mapArrowRight i p p' a b h
  obtain ⟨g, hg, hi⟩ := exists_weakEquivalence_toSSet_cartesianArrow_restriction p p' a b h
  let X := DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E)
    (fun z => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E z)))
  let Y := DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E')
    (fun z => DiagSet.IsCartesianEdge p' (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv E' z)))
  have hw : DiagSet.toSSet.map Q.π ≫ DiagSet.toSSet.map t.right =
      DiagSet.toSSet.map ((grayHomRight markedInterval.{u}.underlying).map a) ≫
        DiagSet.toSSet.map Q'.π :=
    (DiagSet.toSSet.map_comp _ _).symm.trans
      ((congrArg DiagSet.toSSet.map t.w.symm).trans (DiagSet.toSSet.map_comp _ _))
  have fac : DiagSet.toSSet.map (X.ι ≫ Q.π) ≫ DiagSet.toSSet.map t.right =
      g ≫ DiagSet.toSSet.map (Y.ι ≫ Q'.π) := by
    calc
      _ = (DiagSet.toSSet.map X.ι ≫ DiagSet.toSSet.map Q.π) ≫
          DiagSet.toSSet.map t.right := congrArg (fun f => f ≫ DiagSet.toSSet.map t.right)
            (DiagSet.toSSet.map_comp X.ι Q.π)
      _ = DiagSet.toSSet.map X.ι ≫ (DiagSet.toSSet.map Q.π ≫
          DiagSet.toSSet.map t.right) := Category.assoc _ _ _
      _ = DiagSet.toSSet.map X.ι ≫
          (DiagSet.toSSet.map ((grayHomRight markedInterval.{u}.underlying).map a) ≫
            DiagSet.toSSet.map Q'.π) := congrArg (fun f => DiagSet.toSSet.map X.ι ≫ f) hw
      _ = (g ≫ DiagSet.toSSet.map Y.ι) ≫ DiagSet.toSSet.map Q'.π :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ DiagSet.toSSet.map Q'.π) hi.symm)
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun f => g ≫ f) (DiagSet.toSSet.map_comp Y.ι Q'.π).symm)
  constructor
  · intro hp
    have hc : WeakEquivalence
        (DiagSet.toSSet.map (X.ι ≫ Q.π) ≫ DiagSet.toSSet.map t.right) := by infer_instance
    have hc' : WeakEquivalence (g ≫ DiagSet.toSSet.map (Y.ι ≫ Q'.π)) := fac ▸ hc
    exact weakEquivalence_of_precomp g (DiagSet.toSSet.map (Y.ι ≫ Q'.π))
  · intro hp
    have hc : WeakEquivalence (g ≫ DiagSet.toSSet.map (Y.ι ≫ Q'.π)) := by infer_instance
    have hc' : WeakEquivalence
        (DiagSet.toSSet.map (X.ι ≫ Q.π) ≫ DiagSet.toSSet.map t.right) := fac.symm ▸ hc
    exact weakEquivalence_of_postcomp (DiagSet.toSSet.map (X.ι ≫ Q.π))
      (DiagSet.toSSet.map t.right)

private theorem isCartesianEdge_grayHomSimplicialComparison_iff {C D : MarkedSSet.{u}} (c : C ⟶ D)
    [IsFibrant C] [IsFibrant D] [Fibration c]
    (b : Δ[0] ⟶ (ihom Δ[1]).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)) :
    DiagSet.IsCartesianEdge (faceNerveRight.map c) (DiagSet.Edge.ofCell
      (DiagSet.grayArrowVertexEquiv (faceNerveRight.obj C) (SSet.yonedaEquiv
        (b ≫ (grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
          ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app
            (faceNerveRight.obj C)))))) ↔
      SSet.IsCartesianEdge ((MarkedPresheaf.forget (D := edgeMarking)).map c)
        (SSet.ihomPointEquiv Δ[1] _ b) := by
  have hG (A : MarkedSSet.{u}) [IsFibrant A] :
      IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj A)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj A
  have hf (A : MarkedSSet.{u}) [IsFibrant A] :
      IsFibrant ((MarkedPresheaf.forget (D := edgeMarking)).obj A) :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj A
  have hc : Fibration ((DiagSet.toInfty 1).map (faceNerveRight.map c)) :=
    isQuillen_faceNerveAdjunction.fibration_map c
  have : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj D)) := hG D
  have : SSet.Quasicategory ((faceNerveRight ⋙ DiagSet.toSSet).obj C) :=
    quasicategory_toSSet_obj (faceNerveRight.obj C) (hG C)
  have : SSet.Quasicategory ((faceNerveRight ⋙ DiagSet.toSSet).obj D) :=
    quasicategory_toSSet_obj (faceNerveRight.obj D) (hG D)
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj C) :=
    (isFibrant_iff_quasicategory _).1 (hf C)
  have : SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj D) :=
    (isFibrant_iff_quasicategory _).1 (hf D)
  have hfc : Fibration ((MarkedPresheaf.forget (D := edgeMarking)).map c) :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.fibration_map c
  have : SSet.Isofibration ((MarkedPresheaf.forget (D := edgeMarking)).map c) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).1 hfc
  have : SSet.InnerFibration ((MarkedPresheaf.forget (D := edgeMarking)).map c) := inferInstance
  have : SSet.InnerFibration ((faceNerveRight ⋙ DiagSet.toSSet).map c) :=
    innerFibration_toSSet_map (faceNerveRight.map c) hc
  have : WeakEquivalence (faceNerveRightComparison.app C) :=
    weakEquivalence_faceNerveRightComparison_app C
  have : WeakEquivalence (faceNerveRightComparison.app D) :=
    weakEquivalence_faceNerveRightComparison_app D
  rw [DiagSet.isCartesianEdge_iff_isCartesianEdge_toSSet_of_fibration,
    DiagSet.grayArrowVertexEquiv_comparison]
  exact SSet.modelCategoryJoyal.isCartesianEdge_comp_iff_of_weakEquivalence
    (faceNerveRightComparison.app C) (faceNerveRightComparison.app D)
    (faceNerveRightComparison.naturality c).symm (SSet.ihomPointEquiv Δ[1] _ b)

private theorem DiagSet.exists_weakEquivalence_cartesianArrowComparison {C D : MarkedSSet.{u}}
    (c : C ⟶ D) [IsFibrant C] [IsFibrant D] [Fibration c] :
    let X : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj C
    let Y := (grayHomRight markedInterval.{u}.underlying).obj (faceNerveRight.obj C)
    let P := fun e => SSet.IsCartesianEdge ((MarkedPresheaf.forget (D := edgeMarking)).map c)
      (SSet.ihomPointEquiv Δ[1] X (SSet.yonedaEquiv.symm e))
    let Q := fun z : Y.Vertex => DiagSet.IsCartesianEdge (faceNerveRight.map c)
      (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv (faceNerveRight.obj C) z))
    ∃ g : (((ihom Δ[1]).obj X).fullSubcomplex P : SSet.{u}) ⟶
        DiagSet.toSSet.obj (Y.fullSubpresheaf Q).toFunctor,
      WeakEquivalence g ∧ g ≫ DiagSet.toSSet.map (Y.fullSubpresheaf Q).ι =
        (((ihom Δ[1]).obj X).fullSubcomplex P).ι ≫
          ((grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
            ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app
              (faceNerveRight.obj C))) := by
  dsimp only
  let X : SSet.{u} := (MarkedPresheaf.forget (D := edgeMarking)).obj C
  let Y := (grayHomRight markedInterval.{u}.underlying).obj (faceNerveRight.obj C)
  let P := fun e => SSet.IsCartesianEdge ((MarkedPresheaf.forget (D := edgeMarking)).map c)
    (SSet.ihomPointEquiv Δ[1] X (SSet.yonedaEquiv.symm e))
  let Q := fun z : Y.Vertex => DiagSet.IsCartesianEdge (faceNerveRight.map c)
    (DiagSet.Edge.ofCell (DiagSet.grayArrowVertexEquiv (faceNerveRight.obj C) z))
  let f : (ihom Δ[1]).obj X ⟶ DiagSet.toSSet.obj Y :=
    (grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
      ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app (faceNerveRight.obj C))
  have hC : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj C
  have : (DiagSet.toSSet.obj Y).Quasicategory := quasicategory_toSSet_obj Y
    ((isFibrant_infty_iff 1 _).2 (isInftyCategory_grayHomRight _
      ((isFibrant_infty_iff 1 _).1 hC)))
  have : X.Quasicategory := (isFibrant_iff_quasicategory _).1
    (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj C)
  have : IsIso ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app
      (faceNerveRight.obj C)) := by
    change IsIso ((grayHomRightBifunctor.map markedIntervalVertexArrowIso.inv.right.op).app _)
    infer_instance
  have hi : WeakEquivalence (DiagSet.toSSet.map
      ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app (faceNerveRight.obj C))) :=
    (weakEquivalence_iff _).2 ((weakEquivalences SSet.{u}).of_isIso _)
  have hf : WeakEquivalence f := (weakEquivalence_iff _).2
    ((weakEquivalences SSet.{u}).comp_mem _ _
      (weakEquivalence_grayHomSimplicialComparison_app (Δ[1] : SSet.{u}) C).mem hi.mem)
  have hpq (x : ((ihom Δ[1]).obj X) _⦋0⦌) : P x ↔ Q (f.app (op ⦋0⦌) x) := by
    have h := isCartesianEdge_grayHomSimplicialComparison_iff c (SSet.yonedaEquiv.symm x)
    simp only [SSet.yonedaEquiv_comp] at h
    have hx : SSet.yonedaEquiv (SSet.yonedaEquiv.symm x) = x := Equiv.apply_symm_apply _ x
    rw [hx] at h
    exact h.symm
  have hc : Fibration ((DiagSet.toInfty 1).map (faceNerveRight.map c)) :=
    isQuillen_faceNerveAdjunction.fibration_map c
  have hD : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj D)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj D
  let g := SSet.fullSubcomplexMap f P Q (fun x => (hpq x).1)
  have hg : WeakEquivalence g := weakEquivalence_fullSubcomplex_map f P Q hpq
    (fun e he => isCartesianEdge_grayArrowVertexEquiv_of_invStruct (faceNerveRight.map c) e he)
    g rfl
  refine ⟨g ≫ (DiagSet.toSSetFullSubpresheafIso Y Q).inv, ?_, ?_⟩
  · have hi : WeakEquivalence (DiagSet.toSSetFullSubpresheafIso Y Q).inv := by infer_instance
    exact (weakEquivalence_iff _).2
      ((weakEquivalences SSet.{u}).comp_mem _ _ hg.mem hi.mem)
  · rfl

private theorem DiagSet.weakEquivalence_cartesianArrowComparison_iff {C D : MarkedSSet.{u}}
    (c : C ⟶ D) [IsFibrant C] [IsFibrant D] [Fibration c] :
    WeakEquivalence
      ((((ihom Δ[1]).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)).fullSubcomplex
        (fun e => SSet.IsCartesianEdge ((MarkedPresheaf.forget (D := edgeMarking)).map c)
          (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm e)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
          (SSet.stdSimplex.δ (0 : Fin 2))
          ((MarkedPresheaf.forget (D := edgeMarking)).map c)).π) ↔
    WeakEquivalence (DiagSet.toSSet.map
      ((DiagSet.fullSubpresheaf
        ((grayHomRight markedInterval.{u}.underlying).obj (faceNerveRight.obj C))
        (fun z => DiagSet.IsCartesianEdge (faceNerveRight.map c) (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv (faceNerveRight.obj C) z)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true))
          (faceNerveRight.map c)).π)) := by
  let Q := Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
    ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true))
    (faceNerveRight.map c)
  let T := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
    (SSet.stdSimplex.δ (0 : Fin 2)) ((MarkedPresheaf.forget (D := edgeMarking)).map c)
  let X := ((ihom Δ[1]).obj ((MarkedPresheaf.forget (D := edgeMarking)).obj C)).fullSubcomplex
    (fun e => SSet.IsCartesianEdge ((MarkedPresheaf.forget (D := edgeMarking)).map c)
      (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm e)))
  let Y := DiagSet.fullSubpresheaf
    ((grayHomRight markedInterval.{u}.underlying).obj (faceNerveRight.obj C))
    (fun z => DiagSet.IsCartesianEdge (faceNerveRight.map c) (DiagSet.Edge.ofCell
      (DiagSet.grayArrowVertexEquiv (faceNerveRight.obj C) z)))
  obtain ⟨g, hg, hi⟩ := DiagSet.exists_weakEquivalence_cartesianArrowComparison c
  have hb : WeakEquivalence (arrowLeibnizComparison c) := weakEquivalence_arrowLeibnizComparison c
  have fac : (X.ι ≫ T.π) ≫ arrowLeibnizComparison c =
      g ≫ DiagSet.toSSet.map (Y.ι ≫ Q.π) := by
    calc
      _ = X.ι ≫ (T.π ≫ arrowLeibnizComparison c) := Category.assoc _ _ _
      _ = X.ι ≫ (((grayHomSimplicialComparison Δ[1]).app C ≫ DiagSet.toSSet.map
          ((grayHomRestrict markedIntervalVertexArrowIso.inv.right).app
            (faceNerveRight.obj C))) ≫ DiagSet.toSSet.map Q.π) :=
        congrArg (fun f => X.ι ≫ f) (pullbackObjObjπ_comp_arrowLeibnizComparison c)
      _ = (g ≫ DiagSet.toSSet.map Y.ι) ≫ DiagSet.toSSet.map Q.π :=
        (Category.assoc _ _ _).symm.trans
          (congrArg (fun f => f ≫ DiagSet.toSSet.map Q.π) hi.symm)
      _ = _ := (Category.assoc _ _ _).trans
        (congrArg (fun f => g ≫ f) (DiagSet.toSSet.map_comp Y.ι Q.π).symm)
  constructor
  · intro hp
    have hc : WeakEquivalence ((X.ι ≫ T.π) ≫ arrowLeibnizComparison c) := by infer_instance
    have hc' : WeakEquivalence (g ≫ DiagSet.toSSet.map (Y.ι ≫ Q.π)) := fac ▸ hc
    exact weakEquivalence_of_precomp g (DiagSet.toSSet.map (Y.ι ≫ Q.π))
  · intro hp
    have hc : WeakEquivalence (g ≫ DiagSet.toSSet.map (Y.ι ≫ Q.π)) := by infer_instance
    have hc' : WeakEquivalence ((X.ι ≫ T.π) ≫ arrowLeibnizComparison c) := fac.symm ▸ hc
    exact weakEquivalence_of_postcomp (X.ι ≫ T.π) (arrowLeibnizComparison c)

private theorem DiagSet.exists_weakEquivalence_simplicialCartesianArrowRestriction
    {X B : SSet.{u}} [X.Quasicategory] [B.Quasicategory] (q : X ⟶ B) [SSet.InnerFibration q]
    {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (a : X ⟶ DiagSet.toSSet.obj E) (b : B ⟶ DiagSet.toSSet.obj S)
    (h : a ≫ DiagSet.toSSet.map p = q ≫ b) [WeakEquivalence a] [WeakEquivalence b] :
    let P := fun e => SSet.IsCartesianEdge q
      (SSet.ihomPointEquiv Δ[1] X (SSet.yonedaEquiv.symm e))
    let Q := fun e => SSet.IsCartesianEdge (DiagSet.toSSet.map p)
      (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm e))
    ∃ g : (((ihom Δ[1]).obj X).fullSubcomplex P : SSet.{u}) ⟶
        (((ihom Δ[1]).obj (DiagSet.toSSet.obj E)).fullSubcomplex Q : SSet.{u}),
      WeakEquivalence g ∧ g ≫ (((ihom Δ[1]).obj (DiagSet.toSSet.obj E)).fullSubcomplex Q).ι =
        (((ihom Δ[1]).obj X).fullSubcomplex P).ι ≫ (ihom Δ[1]).map a := by
  dsimp only
  have hE := isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have hX : IsFibrant X := (isFibrant_iff_quasicategory X).2 inferInstance
  have hRE : IsFibrant (DiagSet.toSSet.obj E) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj E)
  have : (DiagSet.toSSet.obj E).Quasicategory := quasicategory_toSSet_obj E hE
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  let P := fun e => SSet.IsCartesianEdge q
    (SSet.ihomPointEquiv Δ[1] X (SSet.yonedaEquiv.symm e))
  let Q := fun e => SSet.IsCartesianEdge (DiagSet.toSSet.map p)
    (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm e))
  have hf : WeakEquivalence ((ihom Δ[1]).map a) :=
    SSet.modelCategoryJoyal.weakEquivalence_ihom_map Δ[1] a
  have hpq (x : ((ihom Δ[1]).obj X) _⦋0⦌) : P x ↔ Q (((ihom Δ[1]).map a).app _ x) := by
    have hc := SSet.modelCategoryJoyal.isCartesianEdge_comp_iff_of_weakEquivalence a b h
      (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm x))
    dsimp only [P, Q]
    rw [← SSet.yonedaEquiv_symm_comp, SSet.ihomPointEquiv_comp_ihom_map]
    exact hc.symm
  let g := SSet.fullSubcomplexMap ((ihom Δ[1]).map a) P Q (fun x => (hpq x).1)
  refine ⟨g, ?_, rfl⟩
  exact weakEquivalence_fullSubcomplex_map ((ihom Δ[1]).map a) P Q hpq
    (fun e he => SSet.isCartesianEdge_of_invStruct_ihom (DiagSet.toSSet.map p) e he) g rfl

private theorem DiagSet.weakEquivalence_simplicialCartesianArrows_iff
    {X B : SSet.{u}} [X.Quasicategory] [B.Quasicategory] (q : X ⟶ B) [SSet.InnerFibration q]
    {E S : DiagSet.{u}} (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (a : X ⟶ DiagSet.toSSet.obj E) (b : B ⟶ DiagSet.toSSet.obj S)
    (h : a ≫ DiagSet.toSSet.map p = q ≫ b) [WeakEquivalence a] [WeakEquivalence b] :
    WeakEquivalence
      ((((ihom Δ[1]).obj X).fullSubcomplex (fun e => SSet.IsCartesianEdge q
        (SSet.ihomPointEquiv Δ[1] X (SSet.yonedaEquiv.symm e)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
          (SSet.stdSimplex.δ (0 : Fin 2)) q).π) ↔
    WeakEquivalence
      ((((ihom Δ[1]).obj (DiagSet.toSSet.obj E)).fullSubcomplex
        (fun e => SSet.IsCartesianEdge (DiagSet.toSSet.map p)
          (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm e)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom
          (SSet.stdSimplex.δ (0 : Fin 2)) (DiagSet.toSSet.map p)).π) := by
  let i := SSet.stdSimplex.δ (0 : Fin 2)
  let Q := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i q
  let Q' := Functor.PullbackObjObj.ofHasPullback MonoidalClosed.internalHom i
    (DiagSet.toSSet.map p)
  let t := Functor.PullbackObjObj.mapArrowRight (f₁ := Arrow.mk i) Q Q'
    (Arrow.homMk' a b h)
  have hE := isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have : (DiagSet.toSSet.obj E).Quasicategory := quasicategory_toSSet_obj E hE
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have hf (K Y : SSet.{u}) [Y.Quasicategory] :
      IsFibrant ((MonoidalClosed.internalHom.obj (op K)).obj Y) :=
    (isFibrant_iff_quasicategory _).2
      (inferInstanceAs (((ihom K).obj Y).Quasicategory))
  have hX : IsFibrant X := (isFibrant_iff_quasicategory X).2 inferInstance
  have hB : IsFibrant B := (isFibrant_iff_quasicategory B).2 inferInstance
  have hRE : IsFibrant (DiagSet.toSSet.obj E) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj E)
  have hRS : IsFibrant (DiagSet.toSSet.obj S) :=
    isQuillen_sSetDiagSetAdj.isFibrant_obj ((DiagSet.toInfty 1).obj S)
  have := hf Δ[0] X
  have := hf Δ[0] B
  have := hf Δ[0] (DiagSet.toSSet.obj E)
  have := hf Δ[0] (DiagSet.toSSet.obj S)
  have hr (Y : SSet.{u}) [Y.Quasicategory] :
      Fibration ((MonoidalClosed.internalHom.map i.op).app Y) := by
    have : ((MonoidalClosed.internalHom.obj (op Δ[1])).obj Y).Quasicategory :=
      inferInstanceAs (((ihom Δ[1]).obj Y).Quasicategory)
    have : ((MonoidalClosed.internalHom.obj (op Δ[0])).obj Y).Quasicategory :=
      inferInstanceAs (((ihom Δ[0]).obj Y).Quasicategory)
    exact (SSet.modelCategoryJoyal.fibration_iff_isofibration _).2
      (SSet.isofibration_pullbackObjObjπ (terminal.from Y) i
        (Functor.PullbackObjObj.ofIsTerminal _ _ _ terminalIsTerminal))
  have := hr B
  have := hr (DiagSet.toSSet.obj S)
  have hwe : WeakEquivalence ((ihom Δ[1]).map b) :=
    SSet.modelCategoryJoyal.weakEquivalence_ihom_map Δ[1] b
  have hwb : WeakEquivalence ((ihom Δ[0]).map b) :=
    SSet.modelCategoryJoyal.weakEquivalence_ihom_map Δ[0] b
  have hwa : WeakEquivalence ((ihom Δ[0]).map a) :=
    SSet.modelCategoryJoyal.weakEquivalence_ihom_map Δ[0] a
  have ht : WeakEquivalence t.right := by
    refine @CategoryTheory.IsPullback.weakEquivalence_map_of_fibration SSet.{u} _ _
      _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q.isPullback.flip Q'.isPullback.flip _ _ _ _ _ _
      ((ihom Δ[1]).map b) ((ihom Δ[0]).map b) ((ihom Δ[0]).map a) t.right
      ?_ ?_ ?_ ?_ hwe hwb hwa
    · exact ((MonoidalClosed.internalHom.map i.op).naturality b).symm
    · exact ((ihom Δ[0]).map_comp q b).symm.trans
        ((congrArg (fun f => (ihom Δ[0]).map f) h.symm).trans
          ((ihom Δ[0]).map_comp a (DiagSet.toSSet.map p)))
    · simp only [t, Functor.PullbackObjObj.mapArrowRight_right, IsPullback.lift_snd]
      rfl
    · simp only [t, Functor.PullbackObjObj.mapArrowRight_right, IsPullback.lift_fst]
      rfl
  obtain ⟨g, hg, hi⟩ :=
    DiagSet.exists_weakEquivalence_simplicialCartesianArrowRestriction q p a b h
  let U := ((ihom Δ[1]).obj X).fullSubcomplex (fun e => SSet.IsCartesianEdge q
    (SSet.ihomPointEquiv Δ[1] X (SSet.yonedaEquiv.symm e)))
  let V := ((ihom Δ[1]).obj (DiagSet.toSSet.obj E)).fullSubcomplex
    (fun e => SSet.IsCartesianEdge (DiagSet.toSSet.map p)
      (SSet.ihomPointEquiv Δ[1] _ (SSet.yonedaEquiv.symm e)))
  have fac : (U.ι ≫ Q.π) ≫ t.right = g ≫ (V.ι ≫ Q'.π) := by
    calc
      _ = U.ι ≫ (Q.π ≫ t.right) := Category.assoc _ _ _
      _ = U.ι ≫ ((ihom Δ[1]).map a ≫ Q'.π) := congrArg (fun f => U.ι ≫ f) t.w.symm
      _ = (g ≫ V.ι) ≫ Q'.π := (Category.assoc _ _ _).symm.trans
        (congrArg (fun f => f ≫ Q'.π) hi.symm)
      _ = _ := Category.assoc _ _ _
  constructor
  · intro hp
    have hc : WeakEquivalence ((U.ι ≫ Q.π) ≫ t.right) := by infer_instance
    have hc' : WeakEquivalence (g ≫ (V.ι ≫ Q'.π)) := fac ▸ hc
    exact weakEquivalence_of_precomp g (V.ι ≫ Q'.π)
  · intro hp
    have hc : WeakEquivalence (g ≫ (V.ι ≫ Q'.π)) := by infer_instance
    have hc' : WeakEquivalence ((U.ι ≫ Q.π) ≫ t.right) := fac.symm ▸ hc
    exact weakEquivalence_of_postcomp (U.ι ≫ Q.π) t.right

theorem DiagSet.weakEquivalence_toSSet_cartesianArrows {E S : DiagSet.{u}} (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    WeakEquivalence (DiagSet.toSSet.map
      ((DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E)
        (fun z => DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
          (DiagSet.grayArrowVertexEquiv E z)))).ι ≫
        (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
          ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p).π)) := by
  obtain ⟨C, D, hC, hD, c, hc, a, b, ha, hb, h⟩ :=
    DiagSet.exists_relative_faceNerveReplacement p
  have hGC : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj C)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj C
  have hGD : IsFibrant ((DiagSet.toInfty 1).obj (faceNerveRight.obj D)) :=
    isQuillen_faceNerveAdjunction.isFibrant_obj D
  have hGc : Fibration ((DiagSet.toInfty 1).map (faceNerveRight.map c)) :=
    isQuillen_faceNerveAdjunction.fibration_map c
  apply (DiagSet.weakEquivalence_cartesianArrows_iff_of_weakEquivalence
    p (faceNerveRight.map c) a b h).2
  apply (DiagSet.weakEquivalence_cartesianArrowComparison_iff c).1
  have hQ (Z : MarkedSSet.{u}) [IsFibrant Z] :
      SSet.Quasicategory ((MarkedPresheaf.forget (D := edgeMarking)).obj Z) :=
    (isFibrant_iff_quasicategory _).1
      (Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.isFibrant_obj Z)
  have := hQ C
  have := hQ D
  have : Fibration ((MarkedPresheaf.forget (D := edgeMarking)).map c) :=
    Atoms.Homotopical.isQuillenEquivalence_flatForgetAdjunction.toIsQuillen.fibration_map c
  have : SSet.Isofibration ((MarkedPresheaf.forget (D := edgeMarking)).map c) :=
    (SSet.modelCategoryJoyal.fibration_iff_isofibration _).1 inferInstance
  have := weakEquivalence_faceNerveRightComparison_app C
  have := weakEquivalence_faceNerveRightComparison_app D
  apply (DiagSet.weakEquivalence_simplicialCartesianArrows_iff
    ((MarkedPresheaf.forget (D := edgeMarking)).map c) (faceNerveRight.map c)
    (faceNerveRightComparison.app C) (faceNerveRightComparison.app D)
    (faceNerveRightComparison.naturality c).symm).2
  have hE := isFibrant_of_fibration ((DiagSet.toInfty 1).map p)
  have : (DiagSet.toSSet.obj E).Quasicategory := quasicategory_toSSet_obj E hE
  have : (DiagSet.toSSet.obj S).Quasicategory :=
    quasicategory_toSSet_obj ((DiagSet.toInfty 1).obj S) inferInstance
  have : SSet.InnerFibration (DiagSet.toSSet.map p) :=
    innerFibration_toSSet_map ((DiagSet.toInfty 1).map p) inferInstance
  have : WeakEquivalence (DiagSet.toSSet.map a) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map a)
  have : WeakEquivalence (DiagSet.toSSet.map b) :=
    isQuillen_sSetDiagSetAdj.weakEquivalence_map_of_isFibrant ((DiagSet.toInfty 1).map b)
  apply (DiagSet.weakEquivalence_simplicialCartesianArrows_iff (DiagSet.toSSet.map p)
    (faceNerveRight.map c) (DiagSet.toSSet.map a) (DiagSet.toSSet.map b)
    ((DiagSet.toSSet.map_comp _ _).symm.trans
      ((congrArg DiagSet.toSSet.map h).trans (DiagSet.toSSet.map_comp _ _)))).1
  have : SSet.IsCartesianFibration (DiagSet.toSSet.map p) :=
    (DiagSet.isCartesianFibration_iff_toSSet p).1 inferInstance
  exact weakEquivalence_of_rlp_I (SSet.rlp_I_cartesianArrows (DiagSet.toSSet.map p))

theorem DiagSet.rlp_monomorphisms_forget_cartesianArrow {E S : DiagSet.{u}} (p : E ⟶ S)
    [DiagSet.IsCartesianFibration p] [IsFibrant ((DiagSet.toInfty 1).obj S)] :
    (MorphismProperty.monomorphisms DiagSet.{u}).rlp
      ((MarkedPresheaf.forget (D := atomMarking)).map
        (Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
          (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)).π) := by
  let g := (DiagSet.fullSubpresheaf ((grayHomRight markedInterval.{u}.underlying).obj E)
    (fun z ↦ DiagSet.IsCartesianEdge p (DiagSet.Edge.ofCell
      (DiagSet.grayArrowVertexEquiv E z)))).ι ≫
    (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
      ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p).π
  have : Fibration ((DiagSet.toInfty 1).map g) := DiagSet.fibration_cartesianArrows p
  have : IsFibrant ((DiagSet.toInfty 1).obj
      (Functor.PullbackObjObj.ofHasPullback grayHomRightBifunctor.{u}
        ((MarkedPresheaf.forget (D := atomMarking)).map (markedIntervalVertex true)) p).pt) :=
    DiagSet.isFibrant_cartesianArrowTarget p
  have : WeakEquivalence (DiagSet.toSSet.map g) :=
    DiagSet.weakEquivalence_toSSet_cartesianArrows p
  have : Fibration (DiagSet.toSSet.map g) :=
    isQuillen_sSetDiagSetAdj.fibration_map ((DiagSet.toInfty 1).map g)
  have hg : SSet.modelCategoryQuillen.I.rlp (DiagSet.toSSet.map g) := by
    rw [← SSet.rlp_monomorphisms]
    change (cofibrations SSet.{u}).rlp (DiagSet.toSSet.map g)
    rw [cofibrations_rlp, mem_trivialFibrations_iff]
    exact ⟨inferInstance, inferInstance⟩
  have hg' := rlp_monomorphisms_of_rlp_I_toSSet_map g hg
  intro K L m hm
  exact (HasLiftingProperty.iff_of_arrow_iso_right m
    (Arrow.isoMk (DiagSet.forgetMarkedHomRightIso p)
      (DiagSet.forgetMarkedLeibnizTargetIso p)
      (DiagSet.forget_map_markedLeibniz_π p).symm)).2 (hg' m hm)

theorem DiagSet.hasLiftingProperty_pushoutProduct_flat_map_cartesianMarkedHom
    {E S : DiagSet.{u}} (p : E ⟶ S) [DiagSet.IsCartesianFibration p]
    [IsFibrant ((DiagSet.toInfty 1).obj S)] {K L : DiagSet.{u}} (m : K ⟶ L) [Mono m] :
    HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false))
      ((MarkedPresheaf.flat atomMarking).map m) (markedIntervalVertex.{u} true)).ι
      (DiagSet.cartesianMarkedHom p) := by
  let M := Functor.PullbackObjObj.ofHasPullback markedHomRightBifunctor.{u}
    (markedIntervalVertex true) (DiagSet.cartesianMarkedHom p)
  apply (markedTensorRightParametrizedAdjunction.hasLiftingProperty_iff
    (Functor.PushoutObjObj.ofHasPushout _ ((MarkedPresheaf.flat atomMarking).map m)
      (markedIntervalVertex true)).flip M).2
  apply ((MarkedPresheaf.flatForgetAdjunction atomMarking).hasLiftingProperty_iff m M.π).2
  exact DiagSet.rlp_monomorphisms_forget_cartesianArrow p m
    (MorphismProperty.monomorphisms.infer_property m)

end Atoms.Diagrammatic

import Atoms.Diagrammatic.Fibration.CartesianMarking
import Atoms.Diagrammatic.Marked.GrayMapOver
import Atoms.Homotopical.Simplicial.CartesianYoneda

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra Simplicial Atoms.Shape
  Atoms.Homotopical

universe u

namespace Atoms.Diagrammatic

open MarkedPresheaf (forget)

variable {E S : DiagSet.{u}}

noncomputable def DiagSet.sharpSliceAtId (S : DiagSet.{u}) (b : S.Vertex) :
    markedTensorUnit.{u} ⟶ (MarkedPresheaf.sharp atomMarking).obj (S.sliceAt b) :=
  (MarkedPresheaf.forgetSharpAdjunction atomMarking).homEquiv markedTensorUnit _ (S.sliceAtId b)

theorem DiagSet.forget_map_sharpSliceAtId_comp (S : DiagSet.{u}) (b : S.Vertex) :
    forget.map (S.sharpSliceAtId b ≫ (MarkedPresheaf.sharp atomMarking).map (S.sliceAtProj b)) =
      uliftYonedaEquiv.symm b :=
  S.sliceAtId_comp_sliceAtProj b

noncomputable def DiagSet.cartesianFunOver (p : E ⟶ S) (b : S.Vertex) : DiagSet.{u} :=
  markedGrayMapOver ((MarkedPresheaf.sharp atomMarking).map (S.sliceAtProj b))
    (DiagSet.cartesianMarkedHom p)

theorem DiagSet.forall_mem_marked_cartesianMarked_iff (p : E ⟶ S) {X : DiagSet.{u}}
    (f : X ⟶ E) :
    (∀ (U : Atom) (x : diagram X U), 0 < U.dimension →
        f.app (op U) x ∈ (DiagSet.cartesianMarked p).marked U) ↔
      ∀ ⦃x y : X.Vertex⦄ (e : X.Edge x y),
        IsDegenerate E (e.map f).cell ∨ DiagSet.IsCartesianEdge p (e.map f) := by
  refine ⟨fun h x y e ↦ ?_, fun h U x hU ↦ ?_⟩
  · have h1 : 0 < (atomGlobe 1).dimension := by rw [dimension_atomGlobe]; exact Nat.one_pos
    rcases (DiagSet.mem_marked_cartesianMarked p _ _).1 (h _ e.cell h1) with hd | hlt | hc
    · exact Or.inl hd
    · rw [dimension_atomGlobe] at hlt
      exact absurd hlt (lt_irrefl 1)
    · exact Or.inr ((DiagSet.isCartesianCell_iff_isCartesianEdge p (e.map f)).1 hc)
  · refine (DiagSet.mem_marked_cartesianMarked p U _).2 ?_
    rcases Nat.lt_or_ge 1 U.dimension with hlt | hle
    · exact Or.inr (Or.inl hlt)
    obtain ⟨i⟩ := nonempty_iso_atomGlobe_of_dimension_eq_one (le_antisymm hle hU)
    have hc : ((DiagSet.Edge.ofCell (X.map i.hom.op x)).map f).cell =
        E.map i.hom.op (f.app (op U) x) :=
      (DiagSet.Edge.map_cell _ f).trans (NatTrans.naturality_apply f i.hom.op x)
    rcases h (DiagSet.Edge.ofCell (X.map i.hom.op x)) with hd | he
    · exact Or.inl ((isDegenerate_map_iso_iff i _).1 (hc ▸ hd))
    · exact Or.inr (Or.inr ⟨i, (DiagSet.isCartesianEdge_congr p hc).1 he⟩)

theorem DiagSet.isCartesianFunctor_sliceAtProj_iff (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (b : S.Vertex) (f : S.sliceAt b ⟶ E) :
    DiagSet.IsCartesianFunctor (S.sliceAtProj b) p f ↔
      f ≫ p = S.sliceAtProj b ∧
        ∀ (U : Atom) (x : diagram (S.sliceAt b) U), 0 < U.dimension →
          f.app (op U) x ∈ (DiagSet.cartesianMarked p).marked U := by
  refine and_congr_right fun _ ↦ ?_
  rw [DiagSet.forall_mem_marked_cartesianMarked_iff]
  refine ⟨fun h x y e ↦ Or.inr (h e (DiagSet.isCartesianEdge_sliceAtProj b e)),
    fun h x y e _ ↦ ?_⟩
  rcases h e with hd | he
  · obtain ⟨v, hv⟩ := DiagSet.exists_id_cell_eq_of_isDegenerate hd
    exact (DiagSet.isCartesianEdge_congr p hv).1 (DiagSet.isCartesianEdge_id v)
  · exact he

noncomputable def DiagSet.cartesianFunOverVertexEquiv (p : E ⟶ S) (b : S.Vertex) :
    (DiagSet.cartesianFunOver p b).Vertex ≃
      {f : S.sliceAt b ⟶ E // f ≫ p = S.sliceAtProj b ∧
        ∀ (U : Atom) (x : diagram (S.sliceAt b) U), 0 < U.dimension →
          f.app (op U) x ∈ (DiagSet.cartesianMarked p).marked U} :=
  (markedGrayMapOverVertexEquiv ((MarkedPresheaf.sharp atomMarking).map (S.sliceAtProj b))
    (DiagSet.cartesianMarkedHom p)).trans
    { toFun := fun f ↦ ⟨forget.map f.1, congrArg (fun g ↦ forget.map g) f.2, fun U x hU ↦
        MarkedPresheaf.map_mem_marked f.1 ((MarkedPresheaf.mem_marked_sharp _ _ U x).2 hU)⟩
      invFun := fun f ↦ ⟨MarkedPresheaf.homMk f.1 fun U x hx ↦ f.2.2 U x
        ((MarkedPresheaf.mem_marked_sharp _ _ U x).1 hx), MarkedPresheaf.hom_ext f.2.1⟩
      left_inv := fun _ ↦ Subtype.ext (MarkedPresheaf.hom_ext rfl)
      right_inv := fun _ ↦ rfl }

noncomputable def DiagSet.cartesianFunctorVertexEquiv (p : E ⟶ S)
    [Fibration ((DiagSet.toInfty 1).map p)] [IsFibrant ((DiagSet.toInfty 1).obj S)]
    (b : S.Vertex) :
    (DiagSet.cartesianFunOver p b).Vertex ≃
      {f : S.sliceAt b ⟶ E // DiagSet.IsCartesianFunctor (S.sliceAtProj b) p f} :=
  (DiagSet.cartesianFunOverVertexEquiv p b).trans
    (Equiv.subtypeEquivRight fun f ↦ (DiagSet.isCartesianFunctor_sliceAtProj_iff p b f).symm)

noncomputable def DiagSet.cartesianYonedaEval (p : E ⟶ S) (b : S.Vertex) :
    DiagSet.cartesianFunOver p b ⟶ pullback p (uliftYonedaEquiv.symm b) :=
  markedGrayMapOverRestrict (S.sharpSliceAtId b)
      ((MarkedPresheaf.sharp atomMarking).map (S.sliceAtProj b)) (DiagSet.cartesianMarkedHom p) ≫
    (markedGrayMapOverUnitIso _ (DiagSet.cartesianMarkedHom p) ≪≫
      pullback.congrHom rfl (S.forget_map_sharpSliceAtId_comp b)).hom

theorem DiagSet.rlp_monomorphisms_cartesianYonedaEval_of_hasLiftingProperty (p : E ⟶ S)
    (b : S.Vertex)
    (h : ∀ ⦃K L : DiagSet.{u}⦄ (m : K ⟶ L) [Mono m],
      HasLiftingProperty (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false))
          ((MarkedPresheaf.flat atomMarking).map m) (S.sharpSliceAtId b)).ι
        (DiagSet.cartesianMarkedHom p)) :
    (monomorphisms DiagSet.{u}).rlp (DiagSet.cartesianYonedaEval p b) :=
  (monomorphisms DiagSet.{u}).rlp.comp_mem _ _
    (fun _ _ m hm ↦
      have : Mono m := hm
      hasLiftingProperty_markedGrayMapOverRestrict _ _ _ m (h m))
    (MorphismProperty.rlp_of_isIso _
      (markedGrayMapOverUnitIso _ (DiagSet.cartesianMarkedHom p) ≪≫
        pullback.congrHom rfl (S.forget_map_sharpSliceAtId_comp b)).hom)

open SSet.modelCategoryJoyal in
theorem DiagSet.cartesianFunOver_comparison_of_rlp (p : E ⟶ S)
    [SSet.IsCartesianFibration (DiagSet.toSSet.map p)] (b : S.Vertex)
    (h : (monomorphisms DiagSet.{u}).rlp (DiagSet.cartesianYonedaEval p b)) :
    ∃ f : DiagSet.toSSet.obj (DiagSet.cartesianFunOver p b) ⟶
        SSet.cartesianFunOver (DiagSet.toSSet.map p) (S.vertexEquivSSet b),
      WeakEquivalence f ∧
        f ≫ SSet.cartesianYonedaEval (DiagSet.toSSet.map p) (S.vertexEquivSSet b) =
          DiagSet.toSSet.map (DiagSet.cartesianYonedaEval p b) ≫
            (DiagSet.toSSetFiberIso p b).hom := by
  have hq : SSet.modelCategoryQuillen.I.rlp
      (DiagSet.toSSet.map (DiagSet.cartesianYonedaEval p b) ≫
        (DiagSet.toSSetFiberIso p b).hom) := by
    exact SSet.modelCategoryQuillen.I.rlp.comp_mem _ _ (rlp_I_toSSet_map_of_rlp_monomorphisms h)
      (MorphismProperty.rlp_of_isIso _ _)
  have hev := SSet.trivialFibration_cartesianYoneda (DiagSet.toSSet.map p) (S.vertexEquivSSet b)
  rw [← SSet.rlp_monomorphisms] at hev
  have hlift := hev (initial.to (DiagSet.toSSet.obj (DiagSet.cartesianFunOver p b)))
    (monomorphisms.infer_property _)
  have sq : CommSq (initial.to _) (initial.to (DiagSet.toSSet.obj (DiagSet.cartesianFunOver p b)))
      (SSet.cartesianYonedaEval (DiagSet.toSSet.map p) (S.vertexEquivSSet b))
      (DiagSet.toSSet.map (DiagSet.cartesianYonedaEval p b) ≫ (DiagSet.toSSetFiberIso p b).hom) :=
    ⟨initialIsInitial.hom_ext _ _⟩
  refine ⟨sq.lift, ?_, sq.fac_right⟩
  have h₁ : WeakEquivalence (SSet.cartesianYonedaEval (DiagSet.toSSet.map p)
      (S.vertexEquivSSet b)) :=
    weakEquivalence_of_rlp_I (SSet.trivialFibration_cartesianYoneda _ _)
  have h₂ : WeakEquivalence (sq.lift ≫ SSet.cartesianYonedaEval (DiagSet.toSSet.map p)
      (S.vertexEquivSSet b)) := by
    rw [sq.fac_right]
    exact weakEquivalence_of_rlp_I hq
  exact weakEquivalence_of_postcomp_of_fac (f := sq.lift)
    (g := SSet.cartesianYonedaEval (DiagSet.toSSet.map p) (S.vertexEquivSSet b)) rfl

end Atoms.Diagrammatic

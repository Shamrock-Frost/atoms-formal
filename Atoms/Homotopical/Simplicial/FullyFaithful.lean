import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Cisinski.PathObject
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.MappingSpaceMap
import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Atoms.Homotopical.Simplicial.CartesianMappingSpace
import Atoms.Homotopical.Simplicial.CommaLimit
import Atoms.Homotopical.Simplicial.FibrewiseEquivalence

open CategoryTheory Limits Simplicial HomotopicalAlgebra MorphismProperty
  CartesianMonoidalCategory Atoms.Homotopical

universe u

namespace SSet

open modelCategoryJoyal

def IsFullyFaithful {X Y : SSet.{u}} (f : X ⟶ Y) : Prop :=
  ∀ x y : X _⦋0⦌, WeakEquivalence (mappingSpaceMap f x y)

namespace modelCategoryJoyal

private lemma rlp_I_iff {X Y : SSet.{u}} (f : X ⟶ Y) :
    modelCategoryQuillen.I.rlp f ↔ Fibration f ∧ WeakEquivalence f := by
  rw [← rlp_monomorphisms]
  change (cofibrations SSet.{u}).rlp _ ↔ _
  rw [cofibrations_rlp, mem_trivialFibrations_iff]

private lemma weakEquivalence_mappingSpaceMap_of_eq_id {X : SSet.{u}} (g : X ⟶ X) (hg : g = 𝟙 X)
    (x y : X _⦋0⦌) : WeakEquivalence (mappingSpaceMap g x y) := by
  subst hg
  rw [mappingSpaceMap_id]
  exact (inferInstance : WeakEquivalence (𝟙 (mappingSpace X x y)))

theorem isFullyFaithful_of_weakEquivalence {X Y : SSet.{u}} [X.Quasicategory] [Y.Quasicategory]
    (f : X ⟶ Y) [WeakEquivalence f] : IsFullyFaithful f := by
  have : IsFibrant X := (isFibrant_iff_quasicategory X).2 inferInstance
  have : IsFibrant Y := (isFibrant_iff_quasicategory Y).2 inferInstance
  obtain ⟨h⟩ : Nonempty (FibrantBrownFactorization f) := inferInstance
  intro x y
  have hp := (rlp_I_iff h.p).2 ⟨inferInstance, inferInstance⟩
  have hr := (rlp_I_iff h.r).2 ⟨inferInstance, inferInstance⟩
  have := ((rlp_I_iff _).1 (trivialFibration_mappingSpaceMap hp (h.i.app _ x) (h.i.app _ y))).2
  have := ((rlp_I_iff _).1 (trivialFibration_mappingSpaceMap hr (h.i.app _ x) (h.i.app _ y))).2
  have : WeakEquivalence (mappingSpaceMap h.i x y ≫ mappingSpaceMap h.r _ _) := by
    rw [← mappingSpaceMap_comp]
    exact weakEquivalence_mappingSpaceMap_of_eq_id _ h.i_r x y
  have := weakEquivalence_of_postcomp (mappingSpaceMap h.i x y) (mappingSpaceMap h.r _ _)
  have key : WeakEquivalence (mappingSpaceMap (h.i ≫ h.p) x y) := by
    rw [mappingSpaceMap_comp]
    exact (inferInstance : WeakEquivalence (mappingSpaceMap h.i x y ≫ mappingSpaceMap h.p _ _))
  rwa [h.fac] at key

end modelCategoryJoyal

section EssSurj

private lemma yonedaEquiv_symm_comp_lift_eq (B : SSet.{u}) (y : B _⦋0⦌) (ε : Bool) :
    yonedaEquiv.symm (cond ε coherentIso.x₁ coherentIso.x₀) ≫
        lift (𝟙 coherentIso.{u}) (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm y) =
      yonedaEquiv.symm y ≫ lift (terminal.from B ≫ joyalPoint ε) (𝟙 B) := by
  have hj : joyalPoint ε = (terminalIsoIsTerminal stdSimplex.isTerminalObj₀).hom ≫
      yonedaEquiv.symm (cond ε coherentIso.x₁ coherentIso.x₀) := rfl
  ext1
  · simp only [lift_fst, Category.comp_id, Category.assoc]
    rw [hj, ← Category.assoc, ← Category.assoc]
    exact (Category.id_comp _).symm.trans
      (congrArg (· ≫ _) (stdSimplex.isTerminalObj₀.hom_ext _ _))
  · simp

private lemma nonempty_iso_of_elementaryHomotopy {A B : SSet.{u}} {u v : A ⟶ B}
    (h : joyalInterval.cylinder.ElementaryHomotopy u v) (y : A _⦋0⦌) :
    Nonempty ((Truncated.HomotopyCategory.mk (u.app _ y) : hoFunctor.obj B) ≅
      Truncated.HomotopyCategory.mk (v.app _ y)) := by
  obtain ⟨k, h₀, h₁⟩ := h
  let φ : coherentIso.{u} ⟶ B :=
    lift (𝟙 _) (stdSimplex.isTerminalObj₀.from _ ≫ yonedaEquiv.symm y) ≫ k
  have hφ (ε : Bool) (w : A ⟶ B) (hw : (joyalInterval.cylinder.endpoint ε).app A ≫ k = w) :
      φ.app _ (cond ε coherentIso.x₁ coherentIso.x₀) = w.app _ y := by
    have hw' : lift (terminal.from A ≫ joyalPoint ε) (𝟙 A) ≫ k = w := hw
    have h' : yonedaEquiv.symm (cond ε coherentIso.x₁ coherentIso.x₀) ≫ φ =
        yonedaEquiv.symm y ≫ w :=
      (Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ k) (yonedaEquiv_symm_comp_lift_eq A y ε)).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) hw')))
    exact (congrArg (fun z ↦ φ.app _ z) (yonedaEquiv.apply_symm_apply _)).symm.trans
      ((yonedaEquiv_comp _ _).symm.trans ((congrArg yonedaEquiv h').trans
        ((yonedaEquiv_comp _ _).trans
          (congrArg (fun z ↦ w.app _ z) (yonedaEquiv.apply_symm_apply _)))))
  have := (coherentIso.invStructHom.map φ).isIso_homMk
  exact ⟨eqToIso (congrArg _ (hφ false u h₀).symm) ≪≫
    asIso (Truncated.HomotopyCategory.homMk (coherentIso.hom.map φ)) ≪≫
      eqToIso (congrArg _ (hφ true v h₁))⟩

theorem isoVertices_of_homotopic {A B : SSet.{u}} {u v : A ⟶ B}
    (h : joyalInterval.cylinder.Homotopic u v) (y : A _⦋0⦌) :
    IsoVertices (u.app _ y) (v.app _ y) := by
  induction h with
  | rel _ _ h => exact nonempty_iso_of_elementaryHomotopy h y
  | refl => exact ⟨Iso.refl _⟩
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ih' => exact ih.trans ih'

theorem modelCategoryJoyal.essSurj_of_weakEquivalence {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (f : X ⟶ Y) [WeakEquivalence f] : (hoFunctor.map f).toFunctor.EssSurj := by
  have hX := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    X).1 ((isFibrant_iff_quasicategory X).2 inferInstance)
  have hY := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    Y).1 ((isFibrant_iff_quasicategory Y).2 inferInstance)
  obtain ⟨g, -, hg⟩ := joyalInterval.cylinder.exists_homotopy_inverse_of_weakEquivalences _ hX hY f
    ((weakEquivalence_iff f).1 ‹_›)
  refine ⟨fun b ↦ ?_⟩
  obtain ⟨y, rfl⟩ := Truncated.HomotopyCategory.mk_surjective b
  exact ⟨Truncated.HomotopyCategory.mk (g.app _ y), isoVertices_of_homotopic hg y⟩

end EssSurj

section Converse

open MonoidalCategory MonoidalClosed

open private fatJoinHomEquiv fatJoinHomEquiv_arrow fatJoinRightUnderCommaConeAdjunction swapIso
  from Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FatJoin
open private boundaryPushoutObjObj
  from Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FinalObject

private theorem commaConeIsoFatSlice_inv_commaConeArrow {K X Y : SSet.{u}} (d : K ⟶ X)
    (g : Y ⟶ (fatSlice K).obj (Under.mk d)) :
    g ≫ (commaConeIsoFatSlice d).inv ≫ commaConeArrow d =
      curry (curry ((swapIso K Δ[1] Y).hom ≫ fatJoinCyl Y K ≫
        (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm g).right)) := by
  have hU : (fatJoinRightUnderCommaConeAdjunction K).homEquiv Y (Under.mk d)
      (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm g) =
        g ≫ (Adjunction.rightAdjointUniq (fatJoinRightUnderAdjunction K)
          (fatJoinRightUnderCommaConeAdjunction K)).hom.app (Under.mk d) := by
    apply ((fatJoinRightUnderCommaConeAdjunction K).homEquiv Y (Under.mk d)).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_naturality_left_symm,
      Adjunction.homEquiv_symm_rightAdjointUniq_hom_app, Adjunction.homEquiv_counit]
  have hπ := congrArg (fun k : Y ⟶ commaCone d ↦ k ≫ commaConeArrow d) hU
  have he : (fatJoinRightUnderCommaConeAdjunction K).homEquiv Y (Under.mk d) =
      fatJoinHomEquiv Y (Under.mk d) :=
    congrFun (congrFun (Adjunction.mkOfHomEquiv_homEquiv _) Y) (Under.mk d)
  have hφ := congrArg (fun k : Y ⟶ commaCone d ↦ k ≫ commaConeArrow d)
    (congrFun (congrArg DFunLike.coe he) (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm g))
  exact ((Category.assoc _ _ _).symm.trans hπ.symm).trans
    (hφ.trans (fatJoinHomEquiv_arrow Y (Under.mk d) _))

private theorem sliceToCommaCone_naturality_arrow {K X Y : SSet.{u}} {d : K ⟶ X} {d' : K ⟶ Y}
    (k : Under.mk d ⟶ Under.mk d') :
    (slice K).map k ≫ sliceToCommaCone d' ≫ commaConeArrow d' =
      sliceToCommaCone d ≫ commaConeArrow d ≫ (ihom Δ[1]).map ((ihom K).map k.right) := by
  have h1 := commaConeIsoFatSlice_inv_commaConeArrow d'
    ((slice K).map k ≫ (sliceToFatSlice K).app (Under.mk d'))
  have h2 := commaConeIsoFatSlice_inv_commaConeArrow d ((sliceToFatSlice K).app (Under.mk d))
  have hn : ((fatJoinRightUnderAdjunction K).homEquiv _ _).symm
      ((slice K).map k ≫ (sliceToFatSlice K).app (Under.mk d')) =
        ((fatJoinRightUnderAdjunction K).homEquiv _ _).symm
          ((sliceToFatSlice K).app (Under.mk d)) ≫ k := by
    rw [(sliceToFatSlice K).naturality k]
    exact Adjunction.homEquiv_naturality_right_symm _ _ _
  calc _ = ((slice K).map k ≫ (sliceToFatSlice K).app (Under.mk d')) ≫
        (commaConeIsoFatSlice d').inv ≫ commaConeArrow d' := by
          simp only [sliceToCommaCone, Category.assoc]
    _ = curry (curry ((swapIso K Δ[1] _).hom ≫ fatJoinCyl _ K ≫
        (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm
          ((sliceToFatSlice K).app (Under.mk d))).right ≫ k.right)) := by
          rw [h1, hn, Under.comp_right]
          rfl
    _ = curry (curry ((swapIso K Δ[1] _).hom ≫ fatJoinCyl _ K ≫
        (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm
          ((sliceToFatSlice K).app (Under.mk d))).right)) ≫
            (ihom Δ[1]).map ((ihom K).map k.right) := by
          generalize (((fatJoinRightUnderAdjunction K).homEquiv _ _).symm
            ((sliceToFatSlice K).app (Under.mk d))).right = r
          rw [← curry_natural_right, ← curry_natural_right, Category.assoc]
          exact congrArg (fun z ↦ curry (curry ((swapIso K Δ[1] _).hom ≫ z)))
            (Category.assoc _ _ _).symm
    _ = _ := by
          rw [← h2]
          simp only [sliceToCommaCone, Category.assoc]

open private sectionInterval from Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.FatJoin in
private lemma lift_id_comp_fatJoinCylToJoin (t : Δ[1] ⟶ (Δ[0] ⊗ Δ[0] : SSet.{u})) :
    lift (𝟙 Δ[1]) t ≫ fatJoinCylToJoin Δ[0] Δ[0] = (stdSimplexJoinIso 0 0).inv := by
  have hs : sectionInterval 0 0 = 𝟙 ⦋1⦌ := by
    ext i : 3
    fin_cases i <;> rfl
  rw [← fatJoinStdSimplexSection_fatJoinToJoin 0 0, fatJoinStdSimplexSection, Category.assoc,
    fatJoinCyl_fatJoinToJoin]
  refine congrArg (· ≫ _) ?_
  ext1
  · rw [lift_fst, lift_fst, hs]
    exact (CategoryTheory.Functor.map_id _ _).symm
  · ext1 <;> exact stdSimplex.isTerminalObj₀.hom_ext _ _

theorem ihomPointEquiv_sliceToCommaCone_arrow_evalVertex {K X : SSet.{u}} (d : K ⟶ X)
    (k : K _⦋0⦌) (w : Δ[0] ⟶ (slice K).obj (Under.mk d)) :
    ihomPointEquiv Δ[1] X (w ≫ sliceToCommaCone d ≫ commaConeArrow d ≫
        (ihom Δ[1]).map (evalVertex k X)) =
      (stdSimplexJoinIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (yonedaEquiv.symm k) ≫
        (((joinRightUnderAdjunction K).homEquiv _ _).symm w).right := by
  have hw : w ≫ (sliceToFatSlice K).app (Under.mk d) =
      (fatJoinRightUnderAdjunction K).homEquiv _ _ ((fatJoinToJoinUnder K).app Δ[0] ≫
        ((joinRightUnderAdjunction K).homEquiv _ _).symm w) := by
    apply ((fatJoinRightUnderAdjunction K).homEquiv _ _).symm.injective
    rw [Equiv.symm_apply_apply, Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc,
      sliceToFatSlice, conjugateEquiv_counit, NatTrans.naturality_assoc,
      ← Adjunction.homEquiv_counit]
  have h := commaConeIsoFatSlice_inv_commaConeArrow d (w ≫ (sliceToFatSlice K).app (Under.mk d))
  rw [hw, Equiv.symm_apply_apply, Under.comp_right, ← hw, fatJoinToJoinUnder_app] at h
  replace h := h.trans (congrArg (fun z ↦ curry (curry ((swapIso K Δ[1] Δ[0]).hom ≫ z)))
    (fatJoinCyl_fatJoinToJoin_assoc Δ[0] K _))
  have key (c : join Δ[0] K ⟶ X) : lift (𝟙 Δ[1]) (stdSimplex.isTerminalObj₀.from Δ[1]) ≫
      lift (stdSimplex.isTerminalObj₀.from (Δ[1] ⊗ Δ[0]) ≫ yonedaEquiv.symm k)
        (𝟙 (Δ[1] ⊗ Δ[0])) ≫ (swapIso K Δ[1] Δ[0]).hom ≫ fatJoinCylToJoin Δ[0] K ≫ c =
      (stdSimplexJoinIso 0 0).inv ≫ joinMap (𝟙 Δ[0]) (yonedaEquiv.symm k) ≫ c := by
    rw [← lift_id_comp_fatJoinCylToJoin (lift (stdSimplex.isTerminalObj₀.from Δ[1])
      (stdSimplex.isTerminalObj₀.from Δ[1])), Category.assoc,
      ← whiskerLeft_tensorHom_fatJoinCylToJoin_assoc]
    simp only [← Category.assoc]
    refine congrArg (· ≫ c) (congrArg (· ≫ fatJoinCylToJoin Δ[0] K) ?_)
    ext1
    · simp [swapIso]
    · ext1
      · exact stdSimplex.isTerminalObj₀.hom_ext _ _
      · simp [swapIso]
  generalize (((joinRightUnderAdjunction K).homEquiv _ _).symm w).right = c at h ⊢
  have e : w ≫ sliceToCommaCone d ≫ commaConeArrow d ≫ (ihom Δ[1]).map (evalVertex k X) =
      curry (curry ((swapIso K Δ[1] Δ[0]).hom ≫ fatJoinCylToJoin Δ[0] K ≫ c) ≫
        evalVertex k X) := by
    rw [curry_natural_right, ← h]
    simp only [sliceToCommaCone, Category.assoc]
  rw [ihomPointEquiv_apply, e, uncurry_curry, comp_evalVertex, uncurry_curry]
  exact key c

private lemma ihomStdSimplexZeroIso_naturality {X Y : SSet.{u}} (p : X ⟶ Y) :
    (ihom Δ[0]).map p ≫ (ihomStdSimplexZeroIso Y).hom = (ihomStdSimplexZeroIso X).hom ≫ p := by
  have h : (ihomStdSimplexZeroIso X).inv ≫ (ihom Δ[0]).map p =
      p ≫ (ihomStdSimplexZeroIso Y).inv := constDiagram_comp_ihom_map p Δ[0]
  rw [← Iso.inv_comp_eq, ← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]

private lemma mappingSpaceIsoOfIso_hom_fst {X Y : SSet.{u}} (e : X ≅ Y) {x y : X _⦋0⦌}
    {x' y' : Y _⦋0⦌} (hx : e.hom.app _ x = x') (hy : e.hom.app _ y = y') :
    (mappingSpaceIsoOfIso e hx hy).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ (ihom Δ[1]).map e.hom :=
  IsPullback.isoPullback_hom_fst _

private lemma commaConeFibreIsoMappingSpace_hom_fst {K X : SSet.{u}} (d : K ⟶ X) (a : X _⦋0⦌) :
    (commaConeFibreIsoMappingSpace d a).hom ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ commaConeArrow d :=
  IsPullback.isoPullback_hom_fst _

private lemma sliceAtFibreToMappingSpace_fst (X : SSet.{u}) (x y : X _⦋0⦌) :
    sliceAtFibreToMappingSpace X x y ≫ pullback.fst _ _ =
      pullback.fst _ _ ≫ sliceToCommaCone (yonedaEquiv.symm y) ≫
        commaConeArrow (yonedaEquiv.symm y) ≫ (ihom Δ[1]).map (ihomStdSimplexZeroIso X).hom := by
  refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) (mappingSpaceIsoOfIso_hom_fst _ _ _)).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
        (commaConeFibreIsoMappingSpace_hom_fst _ _)))))).trans ?_)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ _) (pullback.lift_fst _ _ _)))).trans ((Category.assoc _ _ _).trans
      (Category.assoc _ _ _)))

theorem sliceAtFiberMap_sliceAtFibreToMappingSpace {X Y : SSet.{u}} (p : X ⟶ Y)
    (x y : X _⦋0⦌) :
    sliceAtFiberMap p (rfl : p.app _ x = _) (rfl : p.app _ y = _) ≫
        sliceAtFibreToMappingSpace Y _ _ =
      sliceAtFibreToMappingSpace X x y ≫ mappingSpaceMap p x y := by
  have hk := sliceToCommaCone_naturality_arrow (Under.homMk p
    ((yonedaEquiv_symm_comp y p).trans (congrArg yonedaEquiv.symm rfl)) :
      Under.mk (yonedaEquiv.symm y) ⟶ Under.mk (yonedaEquiv.symm (p.app _ y)))
  have L : (sliceAtFiberMap p (rfl : p.app _ x = _) (rfl : p.app _ y = _) ≫
      sliceAtFibreToMappingSpace Y _ _) ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ sliceToCommaCone (yonedaEquiv.symm y) ≫
          commaConeArrow (yonedaEquiv.symm y) ≫ (ihom Δ[1]).map ((ihom Δ[0]).map p) ≫
            (ihom Δ[1]).map (ihomStdSimplexZeroIso Y).hom :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (sliceAtFibreToMappingSpace_fst Y _ _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) (pullback.lift_fst _ _ _)).trans
        ((Category.assoc _ _ _).trans (congrArg (pullback.fst _ _ ≫ ·) ((reassoc_of% hk) _))))))
  have R : (sliceAtFibreToMappingSpace X x y ≫ mappingSpaceMap p x y) ≫ pullback.fst _ _ =
        pullback.fst _ _ ≫ sliceToCommaCone (yonedaEquiv.symm y) ≫
          commaConeArrow (yonedaEquiv.symm y) ≫ (ihom Δ[1]).map (ihomStdSimplexZeroIso X).hom ≫
            (ihom Δ[1]).map p :=
    (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (mappingSpaceMap_fst p x y)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (sliceAtFibreToMappingSpace_fst X x y)).trans
        ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans
          (congrArg (_ ≫ ·) (Category.assoc _ _ _))))))))
  have N : (ihom Δ[1]).map ((ihom Δ[0]).map p) ≫ (ihom Δ[1]).map (ihomStdSimplexZeroIso Y).hom =
      (ihom Δ[1]).map (ihomStdSimplexZeroIso X).hom ≫ (ihom Δ[1]).map p :=
    (CategoryTheory.Functor.map_comp _ _ _).symm.trans ((congrArg _
      (ihomStdSimplexZeroIso_naturality p)).trans (CategoryTheory.Functor.map_comp _ _ _))
  exact mappingSpace_hom_ext (L.trans ((congrArg (fun g ↦ pullback.fst _ _ ≫
    sliceToCommaCone (yonedaEquiv.symm y) ≫ commaConeArrow (yonedaEquiv.symm y) ≫ g) N).trans
      R.symm))

namespace modelCategoryJoyal

private lemma weakEquivalence_sliceAtFiberMap {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] {p : X ⟶ Y} (hp : IsFullyFaithful p) (x y : X _⦋0⦌) :
    WeakEquivalence (sliceAtFiberMap p (rfl : p.app _ x = _) (rfl : p.app _ y = _)) := by
  have := weakEquivalence_sliceAtFibreToMappingSpace (X := X) x y
  have := weakEquivalence_sliceAtFibreToMappingSpace (X := Y) (p.app _ x) (p.app _ y)
  have := hp x y
  have : WeakEquivalence (sliceAtFiberMap p (rfl : p.app _ x = _) (rfl : p.app _ y = _) ≫
      sliceAtFibreToMappingSpace Y _ _) := by
    rw [sliceAtFiberMap_sliceAtFibreToMappingSpace]
    infer_instance
  exact weakEquivalence_of_postcomp _ (sliceAtFibreToMappingSpace Y _ _)

private lemma trivialFibration_leibnizSlice_of_isFullyFaithful {X Y : SSet.{u}}
    [X.Quasicategory] [Y.Quasicategory] (p : X ⟶ Y) [InnerFibration p] (hp : IsFullyFaithful p)
    (y : X _⦋0⦌) : modelCategoryQuillen.I.rlp
      (leibnizSlice (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι p (yonedaEquiv.symm y)) := by
  let j := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  let e : Δ[0] ⟶ X := yonedaEquiv.symm y
  refine trivialFibration_of_rightFibrations_of_fiber (rightFibrations_leibnizSlice j p e)
    fun g ↦ ?_
  let x := (pullback.fst _ _ ≫ sliceπ (Under.mk (j ≫ e))).app _ g
  have : IsIso (sliceπ (Under.mk (j ≫ e))) := isIso_sliceπ_of_isEmpty _
  have : IsIso (sliceπ (Under.mk (j ≫ e ≫ p))) := isIso_sliceπ_of_isEmpty _
  have hQ : IsPullback (pullback.fst _ _ ≫ sliceπ (Under.mk (j ≫ e))) (pullback.snd _ _) p
      (sliceπ (Under.mk (e ≫ p))) :=
    IsPullback.of_iso (IsPullback.of_hasPullback _ _) (Iso.refl _)
      (asIso (sliceπ (Under.mk (j ≫ e)))) (Iso.refl _) (asIso (sliceπ (Under.mk (j ≫ e ≫ p))))
      (Category.id_comp _).symm (Category.id_comp _).symm
      (slice_map_sliceπ (Under.homMk p (by simp) : Under.mk (j ≫ e) ⟶ Under.mk (j ≫ e ≫ p)))
      ((sliceRes_sliceπ _ _).trans (Category.id_comp _).symm)
  have hec : e ≫ p = yonedaEquiv.symm (p.app _ y) := yonedaEquiv_symm_comp y p
  have hxb : yonedaEquiv.symm x ≫ p = yonedaEquiv.symm (p.app _ x) := yonedaEquiv_symm_comp x p
  let τ : Under.mk (yonedaEquiv.symm (p.app _ y)) ⟶ Under.mk (e ≫ p) :=
    Under.homMk (𝟙 Y) ((Category.comp_id _).trans hec.symm)
  have hτ : (slice Δ[0]).map τ ≫ sliceπ (Under.mk (e ≫ p)) = sliceAtπ Y (p.app _ y) :=
    (slice_map_sliceπ τ).trans (Category.comp_id _)
  let β := hQ.lift (pullback.snd (sliceAtπ Y (p.app _ y)) (yonedaEquiv.symm (p.app _ x)) ≫
      yonedaEquiv.symm x) (pullback.fst _ _ ≫ (slice Δ[0]).map τ)
    (by rw [Category.assoc, Category.assoc, hτ, pullback.condition, hxb])
  have hb : IsPullback β (pullback.snd _ _) (pullback.fst _ _ ≫ sliceπ (Under.mk (j ≫ e)))
      (yonedaEquiv.symm x) := by
    have hs : IsPullback (pullback.fst (sliceAtπ Y (p.app _ y))
        (yonedaEquiv.symm (p.app _ x)) ≫ (slice Δ[0]).map τ)
        (pullback.snd _ _) (sliceπ (Under.mk (e ≫ p))) (yonedaEquiv.symm x ≫ p) :=
      IsPullback.of_iso (IsPullback.of_hasPullback _ _) (Iso.refl _)
        ((slice Δ[0]).mapIso (Under.isoMk (Iso.refl Y) ((Category.comp_id _).trans hec.symm)))
        (Iso.refl _) (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm
        ((Category.comp_id _).trans hτ.symm) (by
          rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp, hxb])
    exact IsPullback.of_right (by rwa [hQ.lift_snd]) (hQ.lift_fst _ _ _) hQ.flip
  have ht : IsPullback (pullback.fst (sliceAtπ X y) (yonedaEquiv.symm x))
      (sliceAtFiberMap p (rfl : p.app _ x = _) (rfl : p.app _ y = _)) (leibnizSlice j p e) β := by
    refine IsPullback.of_bot ?_ ?_ hb
    · rw [sliceAtFiberMap, pullback.lift_snd, Category.comp_id, leibnizSlice_fst_sliceπ]
      exact IsPullback.of_hasPullback _ _
    · apply hQ.hom_ext
      · rw [Category.assoc, leibnizSlice_fst_sliceπ, Category.assoc, hQ.lift_fst,
          sliceAtFiberMap, pullback.lift_snd_assoc, Category.comp_id]
        exact pullback.condition
      · rw [Category.assoc, leibnizSlice_snd, Category.assoc, hQ.lift_snd, sliceAtFiberMap,
          pullback.lift_fst_assoc, Category.assoc, ← CategoryTheory.Functor.map_comp]
        exact congrArg (_ ≫ (slice Δ[0]).map ·) (Under.UnderMorphism.ext (Category.comp_id p).symm)
  clear_value β
  obtain ⟨g', hg'⟩ : ∃ g', g' ≫ β = yonedaEquiv.symm g :=
    ⟨_, hb.lift_fst _ (𝟙 _) ((yonedaEquiv_symm_comp _ _).trans (Category.id_comp _).symm)⟩
  have := weakEquivalence_sliceAtFiberMap hp x y
  have := fibration_sliceAtFiberMap p (rfl : p.app _ x = _) (rfl : p.app _ y = _)
  have hc : pullback.fst (leibnizSlice j p e) (yonedaEquiv.symm g) ≫ leibnizSlice j p e =
      (pullback.snd (leibnizSlice j p e) (yonedaEquiv.symm g) ≫ g') ≫ β :=
    pullback.condition.trans ((congrArg (pullback.snd _ _ ≫ ·) hg'.symm).trans
      (Category.assoc _ _ _).symm)
  have hk : IsPullback (ht.lift _ _ hc ≫ pullback.fst (sliceAtπ X y) (yonedaEquiv.symm x))
      (pullback.snd (leibnizSlice j p e) (yonedaEquiv.symm g)) (leibnizSlice j p e) (g' ≫ β) := by
    exact (congrArg₂ (fun a b ↦ IsPullback a (pullback.snd (leibnizSlice j p e)
      (yonedaEquiv.symm g)) (leibnizSlice j p e) b) (ht.lift_fst _ _ hc) hg').mpr
        (IsPullback.of_hasPullback _ _)
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (IsPullback.of_right hk (ht.lift_snd _ _ hc) ht)
    ((rlp_I_iff _).2 ⟨inferInstance, inferInstance⟩)

private lemma exists_app_eq_of_essSurj {X Y : SSet.{u}} [Y.Quasicategory] (p : X ⟶ Y)
    [Isofibration p] (he : (hoFunctor.map p).toFunctor.EssSurj) (y : Y _⦋0⦌) :
    ∃ x : X _⦋0⦌, p.app _ x = y := by
  obtain ⟨x', ⟨i⟩⟩ := he.mem_essImage (Truncated.HomotopyCategory.mk y)
  obtain ⟨x, rfl⟩ := Truncated.HomotopyCategory.mk_surjective x'
  obtain ⟨g, hg⟩ := Truncated.HomotopyCategory.homMk_surjective
    (A := (truncation 2).obj Y) (x := p.app _ x) (y := y) i.hom
  have : IsIso (Truncated.HomotopyCategory.homMk g) := hg ▸ Iso.isIso_hom i
  obtain ⟨x₁, f, -, hf⟩ := Isofibration.exists_lift x g ((isIso_homMk_iff g).1 this)
  exact ⟨x₁, (f.map p).tgt_eq.symm.trans ((congrArg _ hf).trans g.tgt_eq)⟩

theorem trivialFibration_of_isFullyFaithful_of_essSurj {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (p : X ⟶ Y) [Fibration p] (hp : IsFullyFaithful p)
    (he : (hoFunctor.map p).toFunctor.EssSurj) : modelCategoryQuillen.I.rlp p := by
  have := (fibration_iff_isofibration p).1 inferInstance
  rintro A B _ ⟨n⟩
  refine ⟨fun {a b} sq ↦ ?_⟩
  cases n with
  | zero =>
    obtain ⟨x₁, hx₁⟩ := exists_app_eq_of_essSurj p he (yonedaEquiv b)
    have h₀ : IsInitial (∂Δ[0] : SSet.{u}) := by
      rw [boundary_zero]
      exact Subcomplex.isInitialBot
    exact ⟨⟨⟨yonedaEquiv.symm x₁, h₀.hom_ext _ _, by
      rw [yonedaEquiv_symm_comp, hx₁, Equiv.symm_apply_apply]⟩⟩⟩
  | succ n =>
    let sq' := boundaryPushoutObjObj.{u} n
    let e := joinInclRight _ _ ≫ sq'.inr ≫ a
    have h := trivialFibration_leibnizSlice_of_isFullyFaithful p hp (yonedaEquiv e)
    rw [Equiv.symm_apply_apply] at h
    have hw : CommSq a sq'.ι p ((stdSimplexJoinIso n 0).hom ≫ b) := ⟨by
      rw [sq.w]
      exact (congrArg (_ ≫ ·) (Iso.inv_hom_id_assoc _ _)).symm.trans (Category.assoc _ _ _).symm⟩
    obtain ⟨l⟩ := ((hasLiftingProperty_leibnizSlice_iff sq' p e).1 (h _ ⟨n⟩) hw rfl).exists_lift
    exact ⟨⟨⟨(stdSimplexJoinIso n 0).inv ≫ l.l, (Category.assoc _ _ _).symm.trans l.fac_left,
      (Category.assoc _ _ _).trans ((congrArg _ l.fac_right).trans (Iso.inv_hom_id_assoc _ _))⟩⟩⟩

private lemma weakEquivalence_mappingSpaceMap_iff_of_comp_eq {A B C : SSet.{u}} (h : A ⟶ B)
    {p : B ⟶ C} (hp : modelCategoryQuillen.I.rlp p) {w : A ⟶ C} (hw : h ≫ p = w)
    (x y : A _⦋0⦌) :
    WeakEquivalence (mappingSpaceMap w x y) ↔ WeakEquivalence (mappingSpaceMap h x y) := by
  subst hw
  rw [mappingSpaceMap_comp]
  have := ((rlp_I_iff _).1 (trivialFibration_mappingSpaceMap hp (h.app _ x) (h.app _ y))).2
  exact weakEquivalence_postcomp_iff (mappingSpaceMap h x y) (mappingSpaceMap p _ _)

private lemma isFullyFaithful_of_homotopic {A B : SSet.{u}} [B.Quasicategory] {u v : A ⟶ B}
    (h : joyalInterval.cylinder.Homotopic u v) (hu : IsFullyFaithful u) : IsFullyFaithful v := by
  have hB := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    B).1 ((isFibrant_iff_quasicategory B).2 inferInstance)
  obtain ⟨k, h₀, h₁⟩ :=
    (joyalInterval.cylinder.homotopic_iff_elementaryHomotopy_of_isFibrant _ hB _ _).1 h
  have : PreservesColimitsOfSize.{0, u} joyalInterval.{u}.cylinder.I :=
    preservesColimitsOfSize_shrink _
  have := Presheaf.isLeftAdjoint_of_preservesColimits.{u} joyalInterval.{u}.cylinder.I
  let adj := Adjunction.ofIsLeftAdjoint joyalInterval.{u}.cylinder.I
  have hπ (ε : Bool) : modelCategoryQuillen.I.rlp
      ((joyalInterval.cylinder.pathEndpoint adj ε).app B) := by
    rw [← rlp_monomorphisms]
    exact joyalInterval.cylinder.rlp_monomorphisms_pathEndpoint_app adj _ hB ε
  have hH (ε : Bool) : adj.homEquiv A B k ≫ (joyalInterval.cylinder.pathEndpoint adj ε).app B =
      (joyalInterval.cylinder.endpoint ε).app A ≫ k := by
    rw [ExactCylinder.comp_pathEndpoint_app, Equiv.symm_apply_apply]
  intro x y
  exact (weakEquivalence_mappingSpaceMap_iff_of_comp_eq _ (hπ true) ((hH true).trans h₁) x y).2
    ((weakEquivalence_mappingSpaceMap_iff_of_comp_eq _ (hπ false) ((hH false).trans h₀) x y).1
      (hu x y))

theorem weakEquivalence_of_isFullyFaithful_of_essSurj {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (f : X ⟶ Y) (hf : IsFullyFaithful f)
    (he : (hoFunctor.map f).toFunctor.EssSurj) : WeakEquivalence f := by
  have : IsFibrant X := (isFibrant_iff_quasicategory X).2 inferInstance
  have : IsFibrant Y := (isFibrant_iff_quasicategory Y).2 inferInstance
  let φ := factorizationData (trivialCofibrations SSet.{u}) (fibrations SSet.{u}) f
  have : IsFibrant φ.Z := isFibrant_of_fibration φ.p
  have : φ.Z.Quasicategory := (isFibrant_iff_quasicategory φ.Z).1 inferInstance
  have hX := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    X).1 ‹_›
  have hZ := (ExactCylinder.modelCategory.isFibrant_iff _ _ innerHornInclusions_le_monomorphisms
    φ.Z).1 ‹_›
  obtain ⟨g, -, hg⟩ := joyalInterval.cylinder.exists_homotopy_inverse_of_weakEquivalences _ hX hZ
    φ.i ((weakEquivalence_iff φ.i).1 inferInstance)
  have hi := isFullyFaithful_of_weakEquivalence φ.i
  have hgi : IsFullyFaithful (g ≫ φ.i) :=
    isFullyFaithful_of_homotopic (Relation.EqvGen.symm _ _ hg) fun x y ↦ by
      rw [mappingSpaceMap_id]
      exact (inferInstance : WeakEquivalence (𝟙 (mappingSpace φ.Z x y)))
  have hg' : IsFullyFaithful g := fun x y ↦ by
    have := hi (g.app _ x) (g.app _ y)
    have h := hgi x y
    rw [mappingSpaceMap_comp] at h
    exact (weakEquivalence_postcomp_iff _ (mappingSpaceMap φ.i _ _)).1 h
  have hp : IsFullyFaithful φ.p := by
    refine isFullyFaithful_of_homotopic (u := g ≫ f) ?_ fun x y ↦ ?_
    · have := joyalInterval.cylinder.homotopic_comp hg φ.p
      rwa [Category.assoc, φ.fac, Category.id_comp] at this
    · have := hg' x y
      have := hf (g.app _ x) (g.app _ y)
      rw [mappingSpaceMap_comp]
      exact (inferInstance : WeakEquivalence (mappingSpaceMap g x y ≫ mappingSpaceMap f _ _))
  have hpe : (hoFunctor.map φ.p).toFunctor.EssSurj := ⟨fun b ↦ by
    obtain ⟨a, ⟨e⟩⟩ := he.mem_essImage b
    refine ⟨(hoFunctor.map φ.i).toFunctor.obj a, ⟨?_ ≪≫ e⟩⟩
    exact eqToIso (congrArg (fun F : hoFunctor.obj X ⟶ hoFunctor.obj Y ↦ F.toFunctor.obj a)
      ((hoFunctor.map_comp φ.i φ.p).symm.trans (congrArg _ φ.fac)))⟩
  have := ((rlp_I_iff φ.p).1 (trivialFibration_of_isFullyFaithful_of_essSurj φ.p hp hpe)).2
  rw [← φ.fac]
  infer_instance

theorem weakEquivalence_iff_isFullyFaithful_and_essSurj {X Y : SSet.{u}} [X.Quasicategory]
    [Y.Quasicategory] (f : X ⟶ Y) :
    WeakEquivalence f ↔ IsFullyFaithful f ∧ (hoFunctor.map f).toFunctor.EssSurj :=
  ⟨fun _ ↦ ⟨isFullyFaithful_of_weakEquivalence f, essSurj_of_weakEquivalence f⟩,
    fun h ↦ weakEquivalence_of_isFullyFaithful_of_essSurj f h.1 h.2⟩

end modelCategoryJoyal

end Converse

end SSet

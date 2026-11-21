import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Frame
import Atoms.Homotopical.Simplicial.CartesianMonoidal
import Atoms.Homotopical.Simplicial.CartesianOver
import Mathlib.CategoryTheory.LiftingProperties.PushoutProduct

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty
open MonoidalCategory CartesianMonoidalCategory MonoidalClosed

universe u

namespace Atoms.Homotopical

private def markedCoreFunctor : MarkedSSet.{u} ⥤ SSet.{u} where
  obj C := (MarkedSSet.markedCore C).toFunctor
  map {C D} f :=
    { app n := ↾fun s => ⟨(MarkedPresheaf.forget.map f).app n s.1, fun g => by
        rw [← NatTrans.naturality_apply]
        exact MarkedPresheaf.map_mem_marked f (s.2 g)⟩
      naturality _ _ g := by
        ext s
        apply Subtype.ext
        change (MarkedPresheaf.forget.map f).app _ (C.underlying.map g s.1) =
          D.underlying.map g ((MarkedPresheaf.forget.map f).app _ s.1)
        exact NatTrans.naturality_apply (MarkedPresheaf.forget.map f) g s.1 }
  map_id _ := by ext n s; rfl
  map_comp _ _ := by ext n s; rfl

private noncomputable def sharpCoreAdjunction :
    MarkedPresheaf.sharp edgeMarking ⊣ markedCoreFunctor.{u} :=
  Adjunction.mkOfHomEquiv
    { homEquiv K C :=
        { toFun f :=
            { app n := ↾fun s => ⟨(MarkedPresheaf.forget.map f).app n s, fun g => by
                exact (congrArg (· ∈ C.marked ⦋1⦌)
                  (NatTrans.naturality_apply (MarkedPresheaf.forget.map f) g.op s)).mp
                    (MarkedPresheaf.map_mem_marked f
                      ((MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl))⟩
              naturality _ _ g := by
                ext s
                apply Subtype.ext
                change (MarkedPresheaf.forget.map f).app _ (K.map g s) =
                  C.underlying.map g ((MarkedPresheaf.forget.map f).app _ s)
                exact NatTrans.naturality_apply (MarkedPresheaf.forget.map f) g s }
          invFun g := MarkedPresheaf.homMk (g ≫ (MarkedSSet.markedCore C).ι) fun ⟨n⟩ s hs => by
            obtain rfl : n = 1 :=
              MarkedSSet.len_eq_one_of_mem_marked _ hs
            have h := (g.app _ s).2 (𝟙 ⦋1⦌)
            change (g.app _ s).1 ∈ C.marked ⦋1⦌
            exact (congrArg (· ∈ C.marked ⦋1⦌)
              (C.underlying.map_id_apply (op ⦋1⦌) (g.app _ s).1)).mp h
          left_inv f := MarkedPresheaf.hom_ext rfl
          right_inv g := by ext n s; rfl }
      homEquiv_naturality_left_symm _ _ := MarkedPresheaf.hom_ext rfl
      homEquiv_naturality_right _ _ := by ext n s; rfl }

instance preservesColimits_sharp :
    PreservesColimitsOfSize.{u, u} (MarkedPresheaf.sharp.{u} edgeMarking) :=
  sharpCoreAdjunction.leftAdjoint_preservesColimits

private noncomputable def markedHomSwap (A B C : MarkedSSet.{u}) :
    (A ⟶ (ihom B).obj C) ≃ (B ⟶ (ihom A).obj C) where
  toFun f := curry ((β_ A B).hom ≫ uncurry f)
  invFun g := curry ((β_ B A).hom ≫ uncurry g)
  left_inv f := by
    dsimp only
    rw [uncurry_curry, SymmetricCategory.symmetry_assoc, curry_uncurry]
  right_inv g := by
    dsimp only
    rw [uncurry_curry, SymmetricCategory.symmetry_assoc, curry_uncurry]

private lemma markedHomSwap_comp_pre {A B B' C : MarkedSSet.{u}}
    (f : A ⟶ (ihom B).obj C) (i : B' ⟶ B) :
    markedHomSwap A B' C (f ≫ (pre i).app C) = i ≫ markedHomSwap A B C f := by
  change curry ((β_ A B').hom ≫ uncurry (f ≫ (pre i).app C)) =
    i ≫ curry ((β_ A B).hom ≫ uncurry f)
  rw [uncurry_pre_app, ← curry_natural_left,
    BraidedCategory.braiding_naturality_right_assoc]

private lemma markedHomSwap_comp {A A' B C : MarkedSSet.{u}} (j : A' ⟶ A)
    (f : A ⟶ (ihom B).obj C) :
    markedHomSwap A' B C (j ≫ f) = markedHomSwap A B C f ≫ (pre j).app C := by
  change curry ((β_ A' B).hom ≫ uncurry (j ≫ f)) =
    curry ((β_ A B).hom ≫ uncurry f) ≫ (pre j).app C
  rw [uncurry_natural_left, curry_pre_app,
    BraidedCategory.braiding_naturality_left_assoc]

noncomputable def markedPowerSimplicialObject (C : MarkedSSet.{u}) :
    SimplicialObject MarkedSSet.{u} :=
  SSet.stdSimplex.op ⋙ (MarkedPresheaf.sharp edgeMarking).op ⋙ internalHom.flip.obj C

private noncomputable def markedPowerFunctionComplexIso (C : MarkedSSet.{u}) :
    SimplicialObject.functionComplexFunctor (markedPowerSimplicialObject C) ≅
      internalHom.flip.obj C ⋙ markedCoreFunctor :=
  NatIso.ofComponents (fun A => NatIso.ofComponents (fun n =>
    ((markedHomSwap A.unop ((MarkedPresheaf.sharp edgeMarking).obj
      (SSet.stdSimplex.obj n.unop)) C).trans
        ((sharpCoreAdjunction.homEquiv _ _).trans SSet.yonedaEquiv)).toIso)
    (fun {m n} g => by
      ext f
      exact (congrArg SSet.yonedaEquiv (congrArg (sharpCoreAdjunction.homEquiv _ _)
        (markedHomSwap_comp_pre f
          ((MarkedPresheaf.sharp edgeMarking).map (SSet.stdSimplex.map g.unop))))).trans
        ((congrArg SSet.yonedaEquiv
          (sharpCoreAdjunction.homEquiv_naturality_left _ _)).trans
            (SSet.yonedaEquiv_naturality _ _).symm))) (fun j => by
      ext n f
      exact (congrArg SSet.yonedaEquiv
        (congrArg (sharpCoreAdjunction.homEquiv _ _) (markedHomSwap_comp j.unop f))).trans
          (congrArg SSet.yonedaEquiv (sharpCoreAdjunction.homEquiv_naturality_right _ _)))

open MarkedSSet.modelCategoryCartesian in
private theorem rlp_monomorphisms_pre (C : MarkedSSet.{u}) [IsFibrant C]
    {A B : MarkedSSet.{u}} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] :
    (monomorphisms MarkedSSet).rlp ((pre j).app C) := by
  intro K L i hi
  have : Mono i := hi
  have : Mono j := (cofibration_iff j).1 inferInstance
  have : Mono (CategoryTheory.Arrow.mk j).hom := ‹Mono j›
  have : Mono (CategoryTheory.Arrow.mk i).hom := ‹Mono i›
  have : WeakEquivalence (CategoryTheory.Arrow.mk j).hom := ‹WeakEquivalence j›
  have : Cofibration (CategoryTheory.Arrow.mk j □ CategoryTheory.Arrow.mk i).hom :=
    (cofibration_iff _).2 (MarkedSSet.mono_pushoutProduct _ _)
  have : WeakEquivalence (CategoryTheory.Arrow.mk j □ CategoryTheory.Arrow.mk i).hom :=
    MarkedSSet.weakEquivalence_pushoutProduct _ _ (Or.inl inferInstance)
  have : Fibration (terminal.from C) := inferInstance
  exact (Arrow.PushoutProduct.hasLiftingProperty_mk_isTerminal_iff
    (f := j) (g := i) (terminalIsTerminal (C := MarkedSSet.{u}))).1
      (inferInstanceAs (HasLiftingProperty
        (CategoryTheory.Arrow.mk j □ CategoryTheory.Arrow.mk i).hom (terminal.from C)))

open MarkedSSet.modelCategoryCartesian in
theorem isReedyFibrant_markedPowerSimplicialObject (C : MarkedSSet.{u}) [IsFibrant C] :
    (markedPowerSimplicialObject C).IsReedyFibrant := by
  refine SimplicialObject.isReedyFibrant_of_rlp_I fun A B j hj => ?_
  rw [mem_trivialCofibrations_iff] at hj
  obtain ⟨_, _⟩ := hj
  let e := markedPowerFunctionComplexIso C
  refine (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (e.app (op B))
    (e.app (op A)) (e.hom.naturality j.op).symm)).2 ?_
  rw [← SSet.rlp_monomorphisms]
  intro K L i hi
  have : Mono i := hi
  have := (MarkedPresheaf.forgetSharpAdjunction edgeMarking).rightAdjoint_preservesLimits
  have : Mono ((MarkedPresheaf.sharp edgeMarking).map i) := inferInstance
  exact (sharpCoreAdjunction.hasLiftingProperty_iff i ((pre j).app C)).1
    (rlp_monomorphisms_pre C j _ (monomorphisms.infer_property _))

open MarkedSSet.modelCategoryCartesian in
private theorem weakEquivalence_pre (C : MarkedSSet.{u}) [IsFibrant C]
    {A B : MarkedSSet.{u}} (f : A ⟶ B) [WeakEquivalence f] :
    WeakEquivalence ((pre f).app C) := by
  have (W : MarkedSSet.{u}) : IsCofibrant W := by
    rw [isCofibrant_iff, cofibration_iff]
    exact monomorphisms.infer_property _
  have : IsFibrant (op A) := (SimplicialObject.isFibrant_op_iff A).2 inferInstance
  have : IsFibrant (op B) := (SimplicialObject.isFibrant_op_iff B).2 inferInstance
  refine (weakEquivalence_iff _).2
    ((internalHom.flip.obj C).map_mem_of_fibrant (weakEquivalences MarkedSSet) ?_ f.op)
  intro X Y p hX hY hp hw
  have : IsFibrant X := hX
  have : IsFibrant Y := hY
  have : Cofibration p.unop := (cofibration_unop_iff p).2 hp
  have : WeakEquivalence p.unop := (weakEquivalences_unop_iff p).2 hw
  have ht : trivialFibrations MarkedSSet ((pre p.unop).app C) := by
    rw [← cofibrations_rlp]
    intro K L i hi
    exact rlp_monomorphisms_pre C p.unop i ((cofibration_iff i).1 ((cofibration_iff i).2 hi))
  exact ht.2

private def simplexContraction (n : ℕ) : Δ[1] ⊗ Δ[n] ⟶ (Δ[n] : SSet.{u}) where
  app m := ↾fun s => SSet.stdSimplex.objMk
    ⟨fun i => if SSet.stdSimplex.asOrderHom s.1 i = 0 then 0
      else SSet.stdSimplex.asOrderHom s.2 i, fun i j hij => by
        dsimp only
        split_ifs with hi hj hj
        · exact le_rfl
        · exact Fin.zero_le _
        · exact False.elim (hi (le_antisymm
            ((SSet.stdSimplex.asOrderHom s.1).monotone hij |>.trans_eq hj) (Fin.zero_le _)))
        · exact (SSet.stdSimplex.asOrderHom s.2).monotone hij⟩
  naturality _ _ _ := by ext s; rfl

open MarkedSSet.modelCategoryCartesian in
private theorem weakEquivalence_sharp_simplex_projection (n : ℕ) :
    WeakEquivalence ((MarkedPresheaf.sharp edgeMarking).map
      (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}))) := by
  let P := (MarkedPresheaf.sharp edgeMarking).obj (Δ[n] : SSet.{u})
  let p := (MarkedPresheaf.sharp edgeMarking).map
    (SSet.stdSimplex.isTerminalObj₀.from (Δ[n] : SSet.{u}))
  let s := (MarkedPresheaf.sharp edgeMarking).map
    (SSet.stdSimplex.map (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))
  let H : sharpEdgeProd.obj P ⟶ P := edgeHomMk (simplexContraction n)
    (fun _ _ => (MarkedPresheaf.mem_marked_sharp _ _ _ _).2 rfl)
  refine weakEquivalence_of_sharpEdgeHomotopy p s ?_ H (a := 1) (b := 0) ?_ ?_
  · apply MarkedPresheaf.hom_ext
    exact SSet.stdSimplex.isTerminalObj₀.hom_ext _ _
  · apply MarkedPresheaf.hom_ext
    ext m z
    apply SSet.stdSimplex.ext
    intro i
    change (if (1 : Fin 2) = 0 then 0 else SSet.stdSimplex.asOrderHom z i) = _
    exact if_neg (by decide)
  · apply MarkedPresheaf.hom_ext
    ext m z
    apply SSet.stdSimplex.ext
    intro i
    change (if (0 : Fin 2) = 0 then 0 else SSet.stdSimplex.asOrderHom z i) = 0
    rfl

open MarkedSSet.modelCategoryCartesian in
private theorem weakEquivalence_sharp_simplex_map {m n : SimplexCategory} (f : m ⟶ n) :
    WeakEquivalence ((MarkedPresheaf.sharp edgeMarking).map (SSet.stdSimplex.map f)) := by
  have := weakEquivalence_sharp_simplex_projection m.len
  have := weakEquivalence_sharp_simplex_projection n.len
  apply weakEquivalence_of_postcomp_of_fac
    (g := (MarkedPresheaf.sharp edgeMarking).map
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj n)))
    (fg := (MarkedPresheaf.sharp edgeMarking).map
      (SSet.stdSimplex.isTerminalObj₀.from (SSet.stdSimplex.obj m)))
  exact ((MarkedPresheaf.sharp edgeMarking).map_comp _ _).symm.trans
    (congrArg (MarkedPresheaf.sharp edgeMarking).map
      (SSet.stdSimplex.isTerminalObj₀.hom_ext _ _))

private noncomputable def markedPowerZeroIso (C : MarkedSSet.{u}) :
    (markedPowerSimplicialObject C) _⦋0⦌ ≅ C := by
  have := (MarkedPresheaf.forgetSharpAdjunction edgeMarking).rightAdjoint_preservesLimits
  let e := (SSet.stdSimplex.isTerminalObj₀.isTerminalObj
    (MarkedPresheaf.sharp.{u} edgeMarking)).uniqueUpToIso isTerminalTensorUnit
  exact (internalHom.flip.obj C).mapIso e.symm.op ≪≫ unitIsoSelf C

open MarkedSSet.modelCategoryCartesian in
noncomputable def markedSimplicialFrame (C : MarkedSSet.{u}) [IsFibrant C] :
    SimplicialFrame C where
  obj := markedPowerSimplicialObject C
  iso := markedPowerZeroIso C
  isReedyFibrant := isReedyFibrant_markedPowerSimplicialObject C
  isHomotopicallyConstant m n f := by
    have := weakEquivalence_sharp_simplex_map f
    exact weakEquivalence_pre C
      ((MarkedPresheaf.sharp edgeMarking).map (SSet.stdSimplex.map f))

noncomputable def markedPowerSimplicialObjectMap {C C' : MarkedSSet.{u}} (c : C ⟶ C') :
    markedPowerSimplicialObject C ⟶ markedPowerSimplicialObject C' :=
  Functor.whiskerLeft (SSet.stdSimplex.op ⋙ (MarkedPresheaf.sharp edgeMarking).op)
    (internalHom.flip.map c)

open MarkedSSet.modelCategoryCartesian in
theorem markedPowerSimplicialObjectMap_app_zero {C C' : MarkedSSet.{u}} [IsFibrant C]
    [IsFibrant C'] (c : C ⟶ C') :
    (markedPowerSimplicialObjectMap c).app (op ⦋0⦌) ≫ (markedSimplicialFrame C').iso.hom =
      (markedSimplicialFrame C).iso.hom ≫ c := by
  have := (MarkedPresheaf.forgetSharpAdjunction edgeMarking).rightAdjoint_preservesLimits
  let e := (SSet.stdSimplex.isTerminalObj₀.isTerminalObj
    (MarkedPresheaf.sharp.{u} edgeMarking)).uniqueUpToIso isTerminalTensorUnit
  have h₁ := (internalHom.flip.map c).naturality e.inv.op
  have h₂ : (ihom (𝟙_ MarkedSSet.{u})).map c ≫ (unitIsoSelf C').hom = (unitIsoSelf C).hom ≫ c :=
    unitNatIso.inv.naturality c
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (unitIsoSelf C').hom) h₁.symm).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans (Category.assoc _ _ _).symm)))

end Atoms.Homotopical

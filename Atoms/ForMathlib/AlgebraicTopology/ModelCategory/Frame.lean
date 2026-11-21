import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.BrownLemma
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.ForMathlib.AlgebraicTopology.SimplicialObject.FunctionComplex
import Mathlib.AlgebraicTopology.ModelCategory.Opposite
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasLimits C]

namespace CategoryTheory.SimplicialObject

def IsReedyFibrant (Y : SimplicialObject C) : Prop :=
  ∀ n, Fibration (Y.matchingMap n)

def IsHomotopicallyConstant (Y : SimplicialObject C) : Prop :=
  ∀ ⦃m n : SimplexCategory⦄ (f : m ⟶ n), WeakEquivalence (Y.map f.op)

theorem IsReedyFibrant.rlp_I_functionComplex_map {Y : SimplicialObject C} (hY : Y.IsReedyFibrant)
    {A B : C} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] :
    SSet.modelCategoryQuillen.I.rlp ((SimplicialObject.functionComplexFunctor Y).map j.op) := by
  intro K L i hi
  obtain ⟨n⟩ := hi
  have := hY n
  exact (SimplicialObject.hasLiftingProperty_matchingMap_iff _ j n).1 inferInstance

theorem IsReedyFibrant.rlp_I_pullback_snd {Y : SimplicialObject C} (hY : Y.IsReedyFibrant)
    {A B : C} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] {P : SSet.{v}}
    (x : P ⟶ (SimplicialObject.functionComplexFunctor Y).obj (op A)) :
    SSet.modelCategoryQuillen.I.rlp
      (pullback.snd ((SimplicialObject.functionComplexFunctor Y).map j.op) x) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) (hY.rlp_I_functionComplex_map j)

theorem IsReedyFibrant.fibration_cotensorFunctor_map_unop {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) {K L : SSet.{v}} (i : K ⟶ L) [Mono i] :
    Fibration ((SimplicialObject.cotensorFunctor Y).map i).unop := by
  rw [fibration_iff, ← trivialCofibrations_rlp]
  intro A B j hj
  rw [mem_trivialCofibrations_iff] at hj
  obtain ⟨_, _⟩ := hj
  rw [SimplicialObject.hasLiftingProperty_cotensor_map_iff]
  have h := hY.rlp_I_functionComplex_map j
  rw [← SSet.rlp_monomorphisms] at h
  exact h i (MorphismProperty.monomorphisms.infer_property i)

omit [HasLimits C] in
theorem isFibrant_op_iff (A : C) : IsFibrant (op A) ↔ IsCofibrant A :=
  (isFibrant_iff_of_isTerminal (initial.to A).op initialIsInitial.op).trans (fibration_op_iff _)

omit [HasLimits C] in
theorem isCofibrant_op_iff (A : C) : IsCofibrant (op A) ↔ IsFibrant A :=
  (isCofibrant_iff_of_isInitial (terminal.from A).op terminalIsTerminal.op).trans
    (cofibration_op_iff _)

theorem IsReedyFibrant.functionComplexFunctor_map_mem {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) (W : MorphismProperty SSet.{v}) [W.HasTwoOutOfThreeProperty]
    [W.ContainsIdentities] (hW : SSet.modelCategoryQuillen.I.rlp ≤ W) {A B : C} [IsCofibrant A]
    [IsCofibrant B] (f : A ⟶ B) [WeakEquivalence f] :
    W ((SimplicialObject.functionComplexFunctor Y).map f.op) := by
  have : IsFibrant (op A) := (isFibrant_op_iff A).2 inferInstance
  have : IsFibrant (op B) := (isFibrant_op_iff B).2 inferInstance
  refine (SimplicialObject.functionComplexFunctor Y).map_mem_of_fibrant W
    (fun X Z p _ _ _ _ ↦ ?_) f.op
  exact hW _ (hY.rlp_I_functionComplex_map p.unop)

theorem isReedyFibrant_of_rlp_I {Y : SimplicialObject C}
    (hY : ∀ ⦃A B : C⦄ (j : A ⟶ B), trivialCofibrations C j →
      SSet.modelCategoryQuillen.I.rlp ((SimplicialObject.functionComplexFunctor Y).map j.op)) :
    Y.IsReedyFibrant := by
  intro n
  rw [HomotopicalAlgebra.fibration_iff, ← trivialCofibrations_rlp]
  intro A B j hj
  rw [hasLiftingProperty_matchingMap_iff]
  exact hY j hj _ ⟨n⟩

theorem IsReedyFibrant.isFibrant_obj {Y : SimplicialObject C} (hY : Y.IsReedyFibrant)
    (n : SimplexCategoryᵒᵖ) : IsFibrant (Y.obj n) := by
  have hI : IsInitial ((⊥ : (Δ[n.unop.len] : SSet.{v}).Subcomplex) : SSet.{v}) :=
    SSet.Subcomplex.isInitialBot
  have := hY.fibration_cotensorFunctor_map_unop (⊥ : (Δ[n.unop.len] : SSet.{v}).Subcomplex).ι
  have : IsFibrant (cotensor Δ[n.unop.len] Y) :=
    (isFibrant_iff_of_isTerminal _ (hI.isInitialObj (cotensorFunctor Y)).unop).2 this
  exact isFibrant_of_fibration (cotensorStdSimplexIso Y n.unop.len).inv

theorem IsReedyFibrant.rlp_monomorphisms_functionComplex_map {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) {A B : C} (j : A ⟶ B) [Cofibration j] [WeakEquivalence j] :
    (MorphismProperty.monomorphisms SSet.{v}).rlp
      ((SimplicialObject.functionComplexFunctor Y).map j.op) := by
  rw [SSet.rlp_monomorphisms]
  exact hY.rlp_I_functionComplex_map j

end CategoryTheory.SimplicialObject

namespace HomotopicalAlgebra

structure SimplicialFrame (X : C) where
  obj : SimplicialObject C
  iso : obj _⦋0⦌ ≅ X
  isReedyFibrant : obj.IsReedyFibrant
  isHomotopicallyConstant : obj.IsHomotopicallyConstant

theorem SimplicialFrame.isFibrant {X : C} (Y : SimplicialFrame X) : IsFibrant X := by
  have : IsFibrant (Y.obj _⦋0⦌) :=
    (isFibrant_iff_of_isTerminal _ Y.obj.isTerminalMatchingObjectZero).2 (Y.isReedyFibrant 0)
  exact isFibrant_of_fibration Y.iso.inv

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction

universe w

variable {D : Type w} [Category.{v} D] [ModelCategory D] [HasLimits D]
  {F : C ⥤ D} {G : D ⥤ C} {adj : F ⊣ G}

theorem IsQuillen.isReedyFibrant_whiskerRight (h : adj.IsQuillen)
    {Y : SimplicialObject D} (hY : Y.IsReedyFibrant) : SimplicialObject.IsReedyFibrant (Y ⋙ G) := by
  refine SimplicialObject.isReedyFibrant_of_rlp_I fun A B j hj ↦ ?_
  have hj' := h.trivialCofibrations_le j hj
  rw [MorphismProperty.inverseImage_iff, mem_trivialCofibrations_iff] at hj'
  obtain ⟨_, _⟩ := hj'
  let e := adj.functionComplexWhiskerRightIso Y
  exact (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk (e.app (Opposite.op B))
    (e.app (Opposite.op A)) (e.hom.naturality j.op).symm)).2
      (hY.rlp_I_functionComplex_map (F.map j))

def IsQuillen.mapSimplicialFrame (h : adj.IsQuillen) {X : D} (Y : SimplicialFrame X) :
    SimplicialFrame (G.obj X) where
  obj := Y.obj ⋙ G
  iso := G.mapIso Y.iso
  isReedyFibrant := h.isReedyFibrant_whiskerRight Y.isReedyFibrant
  isHomotopicallyConstant m n f := by
    have := Y.isReedyFibrant.isFibrant_obj (Opposite.op m)
    have := Y.isReedyFibrant.isFibrant_obj (Opposite.op n)
    have := Y.isHomotopicallyConstant f
    exact h.weakEquivalence_map_of_isFibrant (Y.obj.map f.op)

end CategoryTheory.Adjunction

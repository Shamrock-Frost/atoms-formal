import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Frame
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Quillen
import Atoms.Homotopical.Simplicial.Diagonal

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra MorphismProperty

universe v u

variable {C : Type u} [Category.{v} C] [ModelCategory C]

namespace CategoryTheory.SimplicialObject

variable [HasLimits C]

theorem IsReedyFibrant.kanWeak_functionComplex_map {Y : SimplicialObject C}
    (hY : Y.IsReedyFibrant) {A B : C} [IsCofibrant A] [IsCofibrant B] (f : A ⟶ B)
    [WeakEquivalence f] :
    Atoms.Homotopical.kanWeak ((SimplicialObject.functionComplexFunctor Y).map f.op) :=
  hY.functionComplexFunctor_map_mem Atoms.Homotopical.kanWeak (fun _ _ p hp ↦
    Atoms.Homotopical.isALocalizer_kanWeak.rlp_monomorphisms_le _
      (by rwa [SSet.rlp_monomorphisms])) f

omit [HasLimits C] in
theorem IsReedyFibrant.kanWeak_functionComplex_map_op [HasColimits C]
    {A : SimplicialObject Cᵒᵖ} (hA : A.IsReedyFibrant) {Z Z' : C} [IsFibrant Z] [IsFibrant Z']
    (g : Z ⟶ Z') [WeakEquivalence g] :
    Atoms.Homotopical.kanWeak ((SimplicialObject.functionComplexFunctor A).map g.op.op) :=
  have : IsCofibrant (op Z) := (isCofibrant_op_iff Z).2 inferInstance
  have : IsCofibrant (op Z') := (isCofibrant_op_iff Z').2 inferInstance
  hA.kanWeak_functionComplex_map g.op

end CategoryTheory.SimplicialObject

namespace HomotopicalAlgebra

open SimplicialObject

variable [HasLimits C] [HasColimits C]

theorem kanWeak_toDiag_cotensorSide {A₀ X : C} (A : SimplicialFrame (op A₀))
    (Y : SimplicialFrame X) :
    Atoms.Homotopical.kanWeak (SSet.toDiag (doubleFunctionComplex A.obj Y.obj)) :=
  SSet.kanWeak_toDiag _ fun m n g ↦
    have := Y.isReedyFibrant.isFibrant_obj (op m)
    have := Y.isReedyFibrant.isFibrant_obj (op n)
    have := Y.isHomotopicallyConstant g
    A.isReedyFibrant.kanWeak_functionComplex_map_op (Y.obj.map g.op)

theorem kanWeak_toDiag_functionComplexSide {A₀ X : C} (A : SimplicialFrame (op A₀))
    (Y : SimplicialFrame X) :
    Atoms.Homotopical.kanWeak
      (SSet.toDiag (SSet.transpose.obj (doubleFunctionComplex A.obj Y.obj))) := by
  refine SSet.kanWeak_toDiag _ fun m n g ↦ ?_
  let e := transposeDoubleFunctionComplexIso A.obj Y.obj
  refine (MorphismProperty.arrow_mk_iso_iff _
    (Arrow.isoMk (e.app _) (e.app _) (e.hom.naturality g.op).symm)).2 ?_
  have : IsCofibrant (unop (A.obj.obj (op m))) :=
    (isFibrant_op_iff _).1 (A.isReedyFibrant.isFibrant_obj (op m))
  have : IsCofibrant (unop (A.obj.obj (op n))) :=
    (isFibrant_op_iff _).1 (A.isReedyFibrant.isFibrant_obj (op n))
  have := A.isHomotopicallyConstant g
  exact Y.isReedyFibrant.kanWeak_functionComplex_map (A.obj.map g.op).unop

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction

variable {F : SSet.{v} ⥤ C} {G : C ⥤ SSet.{v}}

open SSet.modelCategoryQuillen

private lemma IsQuillen.rlp_I_map {adj : F ⊣ G} (h : adj.IsQuillen) {Z Z' : C} (p : Z ⟶ Z')
    (hp : trivialFibrations C p) : SSet.modelCategoryQuillen.I.rlp (G.map p) := by
  rw [← SSet.rlp_monomorphisms]
  intro K L i hi
  rw [mem_trivialFibrations_iff] at hp
  obtain ⟨_, _⟩ := hp
  have : Cofibration (F.map i) := (HomotopicalAlgebra.cofibration_iff _).2 (h.cofibrations_le _ hi)
  exact (adj.hasLiftingProperty_iff i p).1 inferInstance

def IsQuillen.cosimplicialFrame [HasColimits C] {adj : F ⊣ G} (h : adj.IsQuillen) :
    SimplicialFrame (Opposite.op (F.obj Δ[0])) where
  obj := (SSet.stdSimplex ⋙ F).op
  iso := Iso.refl _
  isReedyFibrant := SimplicialObject.isReedyFibrant_of_rlp_I fun _ _ j hj ↦
    (MorphismProperty.arrow_mk_iso_iff _ (Arrow.isoMk
      (adj.functionComplexStdSimplexIso.app _) (adj.functionComplexStdSimplexIso.app _)
      (adj.functionComplexStdSimplexIso.hom.naturality j.unop).symm)).2 (h.rlp_I_map j.unop hj)
  isHomotopicallyConstant m n f := by
    have (K : SSet.{v}) : IsCofibrant K := cofibration_of_mono _
    have : WeakEquivalence (SSet.stdSimplex.{v}.map f) :=
      (weakEquivalence_iff _).2 (Atoms.Homotopical.kanWeak_yoneda_map f)
    have := h.weakEquivalence_map (SSet.stdSimplex.{v}.map f)
    exact inferInstanceAs (WeakEquivalence (F.map (SSet.stdSimplex.map f)).op)

end CategoryTheory.Adjunction

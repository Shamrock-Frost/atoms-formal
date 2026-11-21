import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Frame
import Atoms.ForMathlib.AlgebraicTopology.ModelCategory.Over

open CategoryTheory Limits Opposite Simplicial HomotopicalAlgebra

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasLimits C] {S : C}

private def underFunctionComplexForget (Y : SimplicialObject (Under S)) (A : Under S) :
    Y.functionComplex A ⟶ functionComplex (Y ⋙ Under.forget S) A.right where
  app _ := ↾fun f => f.right
  naturality _ _ _ := rfl

theorem isReedyFibrant_of_under_forget (Y : SimplicialObject (Under S))
    (hY : IsReedyFibrant (Y ⋙ Under.forget S)) : Y.IsReedyFibrant := by
  refine isReedyFibrant_of_rlp_I fun A B j hj K L i hi => ?_
  rw [mem_trivialCofibrations_iff] at hj
  obtain ⟨_, _⟩ := hj
  let hp : HasLiftingProperty i
      ((functionComplexFunctor (Y ⋙ Under.forget S)).map j.right.op) :=
    hY.rlp_I_functionComplex_map j.right i hi
  constructor
  intro a b h
  let a' := a ≫ underFunctionComplexForget Y B
  let b' := b ≫ underFunctionComplexForget Y A
  have h' : CommSq a' i ((functionComplexFunctor (Y ⋙ Under.forget S)).map j.right.op) b' := by
    constructor
    ext n s
    exact congrArg Under.Hom.right (ConcreteCategory.congr_hom (NatTrans.congr_app h.w n) s)
  let _ : h'.HasLift := hp.sq_hasLift h'
  let l := h'.lift
  have hr : l ≫ ((functionComplexFunctor (Y ⋙ Under.forget S)).map j.right.op) = b' :=
    h'.fac_right
  let l' : L ⟶ Y.functionComplex B :=
    { app n := ↾fun s => Under.homMk (l.app n s) (by
        have he : j.right ≫ l.app n s = (b.app n s).right :=
          ConcreteCategory.congr_hom (NatTrans.congr_app hr n) s
        exact (congrArg (· ≫ l.app n s) (Under.w j).symm).trans
          ((Category.assoc _ _ _).trans
            ((congrArg (A.hom ≫ ·) he).trans (Under.w (b.app n s)))))
      naturality m n g := by
        ext s
        apply Under.UnderMorphism.ext
        exact ConcreteCategory.congr_hom (l.naturality g) s }
  refine ⟨⟨l', ?_, ?_⟩⟩
  · ext n s
    apply Under.UnderMorphism.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app h'.fac_left n) s
  · ext n s
    apply Under.UnderMorphism.ext
    exact ConcreteCategory.congr_hom (NatTrans.congr_app hr n) s

def degeneracyCoaugmentation (Y : SimplicialObject C) :
    (Functor.const SimplexCategoryᵒᵖ).obj (Y _⦋0⦌) ⟶ Y where
  app n := Y.map (SimplexCategory.const n.unop ⦋0⦌ 0).op
  naturality m n g := by
    change 𝟙 _ ≫ Y.map _ = Y.map _ ≫ Y.map g
    rw [Category.id_comp, ← Functor.map_comp]
    congr 1

def underSimplicialObject (Y : SimplicialObject C) (f : S ⟶ Y _⦋0⦌) :
    SimplicialObject (Under S) where
  obj n := Under.mk (f ≫ (degeneracyCoaugmentation Y).app n)
  map g := Under.homMk (Y.map g) (by
    change (f ≫ (degeneracyCoaugmentation Y).app _) ≫ Y.map g =
      f ≫ (degeneracyCoaugmentation Y).app _
    have h := (degeneracyCoaugmentation Y).naturality g
    change 𝟙 (Y _⦋0⦌) ≫ _ = _ at h
    rw [Category.id_comp] at h
    exact (Category.assoc _ _ _).trans (congrArg (f ≫ ·) h.symm))
  map_id n := Under.UnderMorphism.ext (Y.map_id n)
  map_comp g h := Under.UnderMorphism.ext (Y.map_comp g h)

def underSimplicialObjectMap {Y Y' : SimplicialObject C} (ψ : Y ⟶ Y') {f : S ⟶ Y _⦋0⦌}
    {f' : S ⟶ Y' _⦋0⦌} (h : f ≫ ψ.app (op ⦋0⦌) = f') :
    Y.underSimplicialObject f ⟶ Y'.underSimplicialObject f' where
  app n := Under.homMk (ψ.app n) (by
    subst h
    change (f ≫ Y.map _) ≫ ψ.app n = (f ≫ ψ.app _) ≫ Y'.map _
    rw [Category.assoc, Category.assoc, ψ.naturality])
  naturality m n g := Under.UnderMorphism.ext (ψ.naturality g)

end CategoryTheory.SimplicialObject

namespace HomotopicalAlgebra

variable {C : Type u} [Category.{v} C] [ModelCategory C] [HasLimits C] {S X : C}

def SimplicialFrame.under (Y : SimplicialFrame X) (f : S ⟶ X) :
    SimplicialFrame (Under.mk f) where
  obj := Y.obj.underSimplicialObject (f ≫ Y.iso.inv)
  iso := Under.isoMk Y.iso (by
    change ((f ≫ Y.iso.inv) ≫ Y.obj.map _) ≫ Y.iso.hom = f
    have h : (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op = 𝟙 _ := Subsingleton.elim _ _
    rw [h, Y.obj.map_id, Category.comp_id, Category.assoc, Y.iso.inv_hom_id,
      Category.comp_id])
  isReedyFibrant := SimplicialObject.isReedyFibrant_of_under_forget _ Y.isReedyFibrant
  isHomotopicallyConstant m n g := by
    rw [weakEquivalences_under_iff]
    exact Y.isHomotopicallyConstant g

variable {X' : C}

def SimplicialFrame.underMap (Y : SimplicialFrame X) (Y' : SimplicialFrame X') {ζ : X ⟶ X'}
    (ψ : Y.obj ⟶ Y'.obj) (hψ : ψ.app (op ⦋0⦌) ≫ Y'.iso.hom = Y.iso.hom ≫ ζ) {f : S ⟶ X}
    {f' : S ⟶ X'} (h : f ≫ ζ = f') : (Y.under f).obj ⟶ (Y'.under f').obj :=
  SimplicialObject.underSimplicialObjectMap ψ (by
    rw [← h, Category.assoc, Category.assoc]
    congr 1
    rw [Iso.eq_comp_inv, Category.assoc, hψ, Iso.inv_hom_id_assoc])

theorem SimplicialFrame.underMap_app_zero (Y : SimplicialFrame X) (Y' : SimplicialFrame X')
    {ζ : X ⟶ X'} (ψ : Y.obj ⟶ Y'.obj)
    (hψ : ψ.app (op ⦋0⦌) ≫ Y'.iso.hom = Y.iso.hom ≫ ζ) {f : S ⟶ X} {f' : S ⟶ X'}
    (h : f ≫ ζ = f') :
    (Y.underMap Y' ψ hψ h).app (op ⦋0⦌) ≫ (Y'.under f').iso.hom =
      (Y.under f).iso.hom ≫ Under.homMk (U := Under.mk f) (V := Under.mk f') ζ h :=
  Under.UnderMorphism.ext hψ

end HomotopicalAlgebra

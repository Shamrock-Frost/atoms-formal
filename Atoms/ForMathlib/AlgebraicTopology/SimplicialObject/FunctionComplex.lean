import Atoms.ForMathlib.AlgebraicTopology.SimplicialSet.Bisimplicial
import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.Limits.Presheaf

open CategoryTheory Limits Opposite Simplicial

universe v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

def functionComplex (Y : SimplicialObject C) (A : C) : SSet.{v} :=
  Y ⋙ coyoneda.obj (op A)

theorem functionComplex_obj (Y : SimplicialObject C) (A : C) (n : SimplexCategoryᵒᵖ) :
    (Y.functionComplex A).obj n = (A ⟶ Y.obj n) :=
  rfl

@[simp]
theorem functionComplex_map (Y : SimplicialObject C) (A : C) {m n : SimplexCategoryᵒᵖ}
    (f : m ⟶ n) (x : (Y.functionComplex A).obj m) :
    (Y.functionComplex A).map f x = x ≫ Y.map f :=
  rfl

@[simps obj]
def functionComplexFunctor (Y : SimplicialObject C) : Cᵒᵖ ⥤ SSet.{v} where
  obj A := Y.functionComplex A.unop
  map j := Functor.whiskerLeft Y (coyoneda.map j)

@[simp]
theorem functionComplexFunctor_map_app (Y : SimplicialObject C) {A B : Cᵒᵖ} (j : A ⟶ B)
    (n : SimplexCategoryᵒᵖ) (x : (Y.functionComplex A.unop).obj n) :
    ((Y.functionComplexFunctor.map j).app n) x = j.unop ≫ x :=
  rfl

section Cotensor

variable [HasLimits C]

instance (Y : SimplicialObject C) : uliftYoneda.{v}.HasPointwiseLeftKanExtension Y.rightOp :=
  have : HasColimitsOfSize.{0, v} Cᵒᵖ := hasColimitsOfSizeShrink.{0, v, v, v} _
  inferInstance

noncomputable def cotensorFunctor (Y : SimplicialObject C) : SSet.{v} ⥤ Cᵒᵖ :=
  Functor.pointwiseLeftKanExtension uliftYoneda.{v} Y.rightOp

noncomputable def cotensor (K : SSet.{v}) (Y : SimplicialObject C) : C :=
  ((cotensorFunctor Y).obj K).unop

theorem cotensor_eq (K : SSet.{v}) (Y : SimplicialObject C) :
    cotensor K Y = (colimit (CostructuredArrow.proj uliftYoneda.{v} K ⋙ Y.rightOp)).unop :=
  rfl

instance (Y : SimplicialObject C) : (cotensorFunctor Y).IsLeftKanExtension
    (Functor.pointwiseLeftKanExtensionUnit uliftYoneda.{v} Y.rightOp) :=
  inferInstanceAs ((Functor.pointwiseLeftKanExtension uliftYoneda.{v} Y.rightOp).IsLeftKanExtension
    (Functor.pointwiseLeftKanExtensionUnit uliftYoneda.{v} Y.rightOp))

noncomputable def functionComplexFunctorIso (Y : SimplicialObject C) :
    Presheaf.restrictedULiftYoneda.{0} Y.rightOp ≅ functionComplexFunctor Y :=
  NatIso.ofComponents (fun _ ↦ NatIso.ofComponents (fun _ ↦
    (Equiv.ulift.trans (opEquiv _ _)).toIso) (fun _ ↦ rfl)) (fun _ ↦ rfl)

noncomputable def cotensorAdjunction (Y : SimplicialObject C) :
    cotensorFunctor Y ⊣ functionComplexFunctor Y :=
  (Presheaf.uliftYonedaAdjunction.{0} (cotensorFunctor Y)
    (Functor.pointwiseLeftKanExtensionUnit uliftYoneda.{v} Y.rightOp)).ofNatIsoRight
    (functionComplexFunctorIso Y)

instance (Y : SimplicialObject C) : PreservesColimitsOfSize.{v, v} (cotensorFunctor Y) :=
  (cotensorAdjunction Y).leftAdjoint_preservesColimits

noncomputable def cotensorStdSimplexIso (Y : SimplicialObject C) (n : ℕ) :
    cotensor Δ[n] Y ≅ Y _⦋n⦌ :=
  have : IsIso (Functor.pointwiseLeftKanExtensionUnit uliftYoneda.{v} Y.rightOp) :=
    Presheaf.isIso_of_isLeftKanExtension.{0} (cotensorFunctor Y) _
  (asIso ((Functor.pointwiseLeftKanExtensionUnit uliftYoneda.{v} Y.rightOp).app ⦋n⦌)).unop

noncomputable def matchingObject (Y : SimplicialObject C) (n : ℕ) : C :=
  cotensor (∂Δ[n] : SSet.{v}) Y

noncomputable def matchingMap (Y : SimplicialObject C) (n : ℕ) :
    Y _⦋n⦌ ⟶ Y.matchingObject n :=
  (cotensorStdSimplexIso Y n).inv ≫ ((cotensorFunctor Y).map (SSet.boundary.{v} n).ι).unop

noncomputable def isTerminalMatchingObjectZero (Y : SimplicialObject C) :
    IsTerminal (Y.matchingObject 0) :=
  have hI : IsInitial (∂Δ[0] : SSet.{v}) := by
    rw [SSet.boundary_zero]
    exact SSet.Subcomplex.isInitialBot
  (hI.isInitialObj (cotensorFunctor Y)).unop

theorem hasLiftingProperty_cotensor_map_iff (Y : SimplicialObject C)
    {A B : C} (j : A ⟶ B) {K L : SSet.{v}} (i : K ⟶ L) :
    HasLiftingProperty j ((cotensorFunctor Y).map i).unop ↔
      HasLiftingProperty i ((functionComplexFunctor Y).map j.op) := by
  rw [← (cotensorAdjunction Y).hasLiftingProperty_iff, HasLiftingProperty.iff_unop,
    Quiver.Hom.unop_op]

theorem hasLiftingProperty_matchingMap_iff (Y : SimplicialObject C) {A B : C} (j : A ⟶ B)
    (n : ℕ) :
    HasLiftingProperty j (Y.matchingMap n) ↔
      HasLiftingProperty (SSet.boundary.{v} n).ι ((functionComplexFunctor Y).map j.op) := by
  rw [← hasLiftingProperty_cotensor_map_iff]
  exact HasLiftingProperty.iff_of_arrow_iso_right j
    (Arrow.isoMk (cotensorStdSimplexIso Y n).symm (Iso.refl _) (Category.comp_id _).symm)

end Cotensor

end CategoryTheory.SimplicialObject

namespace HomotopicalAlgebra

open SimplicialObject

variable {C : Type u} [Category.{v} C]

def doubleFunctionComplex (A : SimplicialObject Cᵒᵖ) (Y : SimplicialObject C) :
    SimplicialObject SSet.{v} :=
  Y ⋙ opOp C ⋙ A.functionComplexFunctor

theorem doubleFunctionComplex_obj (A : SimplicialObject Cᵒᵖ) (Y : SimplicialObject C)
    (b : SimplexCategoryᵒᵖ) :
    (doubleFunctionComplex A Y).obj b = A.functionComplex (op (Y.obj b)) :=
  rfl

@[simp]
theorem doubleFunctionComplex_map_app_apply (A : SimplicialObject Cᵒᵖ) (Y : SimplicialObject C)
    {b b' : SimplexCategoryᵒᵖ} (g : b ⟶ b') (a : SimplexCategoryᵒᵖ)
    (x : ((doubleFunctionComplex A Y).obj b).obj a) :
    (((doubleFunctionComplex A Y).map g).app a x).unop = x.unop ≫ Y.map g :=
  rfl

def transposeDoubleFunctionComplexIso (A : SimplicialObject Cᵒᵖ) (Y : SimplicialObject C) :
    SSet.transpose.obj (doubleFunctionComplex A Y) ≅ A ⋙ Y.functionComplexFunctor :=
  NatIso.ofComponents (fun a ↦ NatIso.ofComponents (fun b ↦ (opEquiv _ _).toIso) fun g ↦ by
    ext x
    rfl) fun g ↦ by
      ext b x
      rfl

theorem transposeDoubleFunctionComplexIso_hom_app_app_apply (A : SimplicialObject Cᵒᵖ)
    (Y : SimplicialObject C) (a b : SimplexCategoryᵒᵖ)
    (x : ((SSet.transpose.obj (doubleFunctionComplex A Y)).obj a).obj b) :
    ((transposeDoubleFunctionComplexIso A Y).hom.app a).app b x = x.unop :=
  rfl

theorem transposeDoubleFunctionComplexIso_inv_app_app_apply (A : SimplicialObject Cᵒᵖ)
    (Y : SimplicialObject C) (a b : SimplexCategoryᵒᵖ)
    (x : (Y.functionComplex (unop (A.obj a))).obj b) :
    ((transposeDoubleFunctionComplexIso A Y).inv.app a).app b x = x.op :=
  rfl

end HomotopicalAlgebra

namespace CategoryTheory.Adjunction

variable {C : Type u} [Category.{v} C] {F : SSet.{v} ⥤ C} {G : C ⥤ SSet.{v}}

def functionComplexStdSimplexIso (adj : F ⊣ G) :
    opOp C ⋙ SimplicialObject.functionComplexFunctor (SSet.stdSimplex ⋙ F).op ≅ G :=
  NatIso.ofComponents (fun Z ↦ NatIso.ofComponents (fun n ↦
    ((opEquiv _ _).trans ((adj.homEquiv _ _).trans SSet.yonedaEquiv)).toIso) fun g ↦ by
      ext x
      exact (congrArg SSet.yonedaEquiv (adj.homEquiv_naturality_left _ _)).trans
        (SSet.yonedaEquiv_naturality _ _).symm) fun k ↦ by
    ext n x
    exact congrArg SSet.yonedaEquiv (adj.homEquiv_naturality_right _ _)

theorem functionComplexStdSimplexIso_hom_app_app_apply (adj : F ⊣ G) (Z : C)
    (n : SimplexCategoryᵒᵖ)
    (x : ((opOp C ⋙ SimplicialObject.functionComplexFunctor (SSet.stdSimplex ⋙ F).op).obj Z).obj
      n) :
    (adj.functionComplexStdSimplexIso.hom.app Z).app n x =
      SSet.yonedaEquiv (adj.homEquiv _ _ x.unop) :=
  rfl

theorem functionComplexStdSimplexIso_inv_app_app_apply (adj : F ⊣ G) (Z : C)
    (n : SimplexCategoryᵒᵖ) (x : (G.obj Z).obj n) :
    (adj.functionComplexStdSimplexIso.inv.app Z).app n x =
      ((adj.homEquiv _ _).symm (SSet.yonedaEquiv.symm x)).op :=
  rfl

end CategoryTheory.Adjunction

namespace CategoryTheory.Adjunction

universe w

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]
  {F : C ⥤ D} {G : D ⥤ C}

def functionComplexWhiskerRightIso (adj : F ⊣ G) (Y : SimplicialObject D) :
    SimplicialObject.functionComplexFunctor (Y ⋙ G) ≅
      F.op ⋙ SimplicialObject.functionComplexFunctor Y :=
  NatIso.ofComponents (fun A ↦ NatIso.ofComponents (fun n ↦
    (adj.homEquiv A.unop (Y.obj n)).symm.toIso) (fun g ↦ by
      ext x
      exact adj.homEquiv_naturality_right_symm _ _)) (fun j ↦ by
    ext n x
    exact adj.homEquiv_naturality_left_symm _ _)

end CategoryTheory.Adjunction

import Atoms.Homotopical.Localizer.Basic
import Atoms.Homotopical.Cellular.Model
import Mathlib.CategoryTheory.Presentable.Adjunction
import Mathlib.CategoryTheory.Adjunction.Evaluation

open CategoryTheory Limits MorphismProperty

namespace Atoms.Homotopical

universe v

variable (A : Type v) [SmallCategory A] (I : Type v) [SmallCategory I]

@[simps]
noncomputable def initialArrow (D : Type*) [Category D] [HasInitial D] : D ⥤ Arrow D where
  obj X := Arrow.mk (initial.to X)
  map f := Arrow.homMk (𝟙 _) f (by simp)

def projectiveGenerators : MorphismProperty (I ⥤ Aᵒᵖ ⥤ Type v) :=
  MorphismProperty.ofHoms fun p : I × CellularIndex A ↦
    (evaluationLeftAdjoint (Aᵒᵖ ⥤ Type v) p.1).map p.2.subfunctor.ι

instance isSmall_projectiveGenerators : (projectiveGenerators A I).IsSmall.{v} :=
  MorphismProperty.isSmall_ofHoms _

variable {A} in
instance isLocallyPresentable_diagram : IsLocallyPresentable.{v} (I ⥤ Aᵒᵖ ⥤ Type v) :=
  Equivalence.isLocallyPresentable
    ((opOpEquivalence I).congrLeft : (Iᵒᵖᵒᵖ ⥤ Aᵒᵖ ⥤ Type v) ≌ (I ⥤ Aᵒᵖ ⥤ Type v))

def projectiveCofibrations : MorphismProperty (I ⥤ Aᵒᵖ ⥤ Type v) :=
  (projectiveGenerators A I).rlp.llp

noncomputable def projectiveFactorization :
    (projectiveGenerators A I).rlp.llp.FunctorialFactorizationData
      (projectiveGenerators A I).rlp :=
  MorphismProperty.functorialFactorizationData _ _

noncomputable def projectiveReplacement : (I ⥤ Aᵒᵖ ⥤ Type v) ⥤ (I ⥤ Aᵒᵖ ⥤ Type v) :=
  initialArrow _ ⋙ (projectiveFactorization A I).Z

noncomputable def projectiveReplacementπ : projectiveReplacement A I ⟶ 𝟭 _ :=
  Functor.whiskerLeft (initialArrow _) (projectiveFactorization A I).p

variable {A}

noncomputable def hocolimComparison {I J : Type v} [SmallCategory I] [SmallCategory J]
    (u : I ⥤ J) (X : Aᵒᵖ ⥤ Type v) :
    colimit ((projectiveReplacement A I).obj
        (u ⋙ (projectiveReplacement A J).obj ((Functor.const J).obj X))) ⟶
      colimit ((projectiveReplacement A J).obj ((Functor.const J).obj X)) :=
  colimMap ((projectiveReplacementπ A I).app _) ≫ colimit.pre _ u

def catWeakEquivalences (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) : MorphismProperty Cat.{v, v} :=
  fun _ _ u ↦ V (hocolimComparison u.toFunctor (⊤_ (Aᵒᵖ ⥤ Type v)))

abbrev representablesOver (X : Aᵒᵖ ⥤ Type v) : CostructuredArrow yoneda X ⥤ Aᵒᵖ ⥤ Type v :=
  CostructuredArrow.proj yoneda X ⋙ yoneda

noncomputable def regularizationMap (X : Aᵒᵖ ⥤ Type v) :
    colimit ((projectiveReplacement A (CostructuredArrow yoneda X)).obj (representablesOver X)) ⟶
      X :=
  colimMap ((projectiveReplacementπ A _).app _) ≫ colimit.desc _ (Presheaf.tautologicalCocone X)

theorem ι_regularizationMap (X : Aᵒᵖ ⥤ Type v) (c : CostructuredArrow yoneda X) :
    colimit.ι ((projectiveReplacement A _).obj (representablesOver X)) c ≫ regularizationMap X =
      ((projectiveReplacementπ A _).app (representablesOver X)).app c ≫ c.hom := by
  simp [regularizationMap, Presheaf.tautologicalCocone]

def IsRegular (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) (X : Aᵒᵖ ⥤ Type v) : Prop :=
  V (regularizationMap X)

class IsRegularALocalizer (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) : Prop where
  isRegular (X : Aᵒᵖ ⥤ Type v) : IsRegular V X

def regularCompletion (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) :
    MorphismProperty (Aᵒᵖ ⥤ Type v) :=
  generatedALocalizer (V ⊔ MorphismProperty.ofHoms fun X : Aᵒᵖ ⥤ Type v ↦ regularizationMap X)

class IsTestALocalizer (V : MorphismProperty (Aᵒᵖ ⥤ Type v)) : Prop
    extends IsALocalizer V, IsRegularALocalizer V where
  terminal_from_yoneda : ∀ a : A, V (terminal.from (yoneda.obj a))

end Atoms.Homotopical

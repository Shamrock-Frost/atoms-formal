import Atoms.ForMathlib.CategoryTheory.Elements
import Atoms.ForMathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

namespace CategoryTheory

open Limits Opposite

universe u

namespace NatTrans

section Extension

variable {A : Type u} [SmallCategory A] {K X : Aᵒᵖ ⥤ Type u} (i : K ⟶ X)

def MemRangeElement (p : (X.Elements)ᵒᵖ) : Prop :=
  ∃ y : K.obj p.unop.1, i.app p.unop.1 y = p.unop.2

variable {i}

theorem memRangeElement_of_hom {p q : (X.Elements)ᵒᵖ} (f : p ⟶ q)
    (hq : MemRangeElement i q) : MemRangeElement i p :=
  ⟨K.map f.unop.1 hq.choose, by
    rw [NatTrans.naturality_apply, hq.choose_spec]
    exact f.unop.2⟩

noncomputable def rangeElementLift (p : (X.Elements)ᵒᵖ) (hp : MemRangeElement i p) :
    (K.Elements)ᵒᵖ :=
  op ⟨p.unop.1, hp.choose⟩

noncomputable def rangeElementLiftHom [Mono i] {p q : (X.Elements)ᵒᵖ} (f : p ⟶ q)
    (hp : MemRangeElement i p) (hq : MemRangeElement i q) :
    rangeElementLift p hp ⟶ rangeElementLift q hq :=
  (CategoryOfElements.homMk (rangeElementLift q hq).unop (rangeElementLift p hp).unop f.unop.1
    (injective_of_mono (i.app _) (by
      change i.app _ (K.map f.unop.1 hq.choose) = i.app _ hp.choose
      rw [NatTrans.naturality_apply, hq.choose_spec, hp.choose_spec]
      exact f.unop.2))).op

theorem rangeElementLiftHom_id [Mono i] (p : (X.Elements)ᵒᵖ) (hp : MemRangeElement i p) :
    rangeElementLiftHom (𝟙 p) hp hp = 𝟙 _ :=
  Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

theorem rangeElementLiftHom_comp [Mono i] {p q r : (X.Elements)ᵒᵖ} (f : p ⟶ q) (g : q ⟶ r)
    (hp : MemRangeElement i p) (hq : MemRangeElement i q) (hr : MemRangeElement i r) :
    rangeElementLiftHom (f ≫ g) hp hr =
      rangeElementLiftHom f hp hq ≫ rangeElementLiftHom g hq hr :=
  Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

variable (i) {C : Type*} [Category C] [HasTerminal C] (u : (K.Elements)ᵒᵖ ⥤ C)

open Classical in
noncomputable def extendElementsObj (p : (X.Elements)ᵒᵖ) : C :=
  if hp : MemRangeElement i p then u.obj (rangeElementLift p hp) else ⊤_ C

theorem extendElementsObj_of_mem {p : (X.Elements)ᵒᵖ} (hp : MemRangeElement i p) :
    extendElementsObj i u p = u.obj (rangeElementLift p hp) :=
  dif_pos hp

theorem extendElementsObj_of_not_mem {p : (X.Elements)ᵒᵖ} (hp : ¬MemRangeElement i p) :
    extendElementsObj i u p = ⊤_ C :=
  dif_neg hp

theorem hom_ext_extendElementsObj_of_not_mem {Y : C} {p : (X.Elements)ᵒᵖ}
    (hp : ¬MemRangeElement i p) (a b : Y ⟶ extendElementsObj i u p) : a = b := by
  rw [← cancel_mono (eqToHom (extendElementsObj_of_not_mem i u hp))]
  exact terminal.hom_ext _ _

open Classical in
noncomputable def extendElementsMap [Mono i] {p q : (X.Elements)ᵒᵖ} (f : p ⟶ q) :
    extendElementsObj i u p ⟶ extendElementsObj i u q :=
  if hq : MemRangeElement i q then
    eqToHom (extendElementsObj_of_mem i u (memRangeElement_of_hom f hq)) ≫
      u.map (rangeElementLiftHom f _ hq) ≫ eqToHom (extendElementsObj_of_mem i u hq).symm
  else terminal.from _ ≫ eqToHom (extendElementsObj_of_not_mem i u hq).symm

theorem extendElementsMap_of_mem [Mono i] {p q : (X.Elements)ᵒᵖ} (f : p ⟶ q)
    (hp : MemRangeElement i p) (hq : MemRangeElement i q) :
    extendElementsMap i u f = eqToHom (extendElementsObj_of_mem i u hp) ≫
      u.map (rangeElementLiftHom f hp hq) ≫ eqToHom (extendElementsObj_of_mem i u hq).symm :=
  dif_pos hq

variable [Mono i]

noncomputable def extendElementsFunctor : (X.Elements)ᵒᵖ ⥤ C where
  obj := extendElementsObj i u
  map := extendElementsMap i u
  map_id p := by
    by_cases hp : MemRangeElement i p
    · rw [extendElementsMap_of_mem i u _ hp hp, rangeElementLiftHom_id, u.map_id]
      simp
    · exact hom_ext_extendElementsObj_of_not_mem i u hp _ _
  map_comp {p q r} f g := by
    by_cases hr : MemRangeElement i r
    · have hq := memRangeElement_of_hom g hr
      have hp := memRangeElement_of_hom f hq
      rw [extendElementsMap_of_mem i u _ hp hr, extendElementsMap_of_mem i u _ hp hq,
        extendElementsMap_of_mem i u _ hq hr, rangeElementLiftHom_comp f g hp hq hr, u.map_comp]
      simp
    · exact hom_ext_extendElementsObj_of_not_mem i u hr _ _

theorem rangeElementLift_mapElements (p : (K.Elements)ᵒᵖ)
    (hp : MemRangeElement i ((NatTrans.mapElements i).op.obj p)) :
    (hp.choose : K.obj p.unop.1) = p.unop.2 :=
  injective_of_mono (i.app _) hp.choose_spec

theorem mapElements_op_comp_extendElementsFunctor :
    (NatTrans.mapElements i).op ⋙ extendElementsFunctor i u = u := by
  have hmem : ∀ p : (K.Elements)ᵒᵖ, MemRangeElement i ((NatTrans.mapElements i).op.obj p) :=
    fun p => ⟨p.unop.2, rfl⟩
  have hobj : ∀ p : (K.Elements)ᵒᵖ,
      ((NatTrans.mapElements i).op ⋙ extendElementsFunctor i u).obj p = u.obj p := fun p => by
    change extendElementsObj i u _ = _
    rw [extendElementsObj_of_mem i u (hmem p)]
    exact congrArg (fun y => u.obj (op ⟨p.unop.1, y⟩)) (rangeElementLift_mapElements i p _)
  refine CategoryTheory.Functor.ext hobj fun p q f => ?_
  change extendElementsMap i u _ = _
  have key := CategoryOfElements.map_eq_of_unop_val_eq u
    (rangeElementLift_mapElements i p (hmem p)).symm
    (rangeElementLift_mapElements i q (hmem q)).symm f
    (rangeElementLiftHom ((NatTrans.mapElements i).op.map f) (hmem p) (hmem q)) rfl
  rw [extendElementsMap_of_mem i u _ (hmem p) (hmem q)]
  erw [key]
  exact eqToHom_comp_comp_eqToHom_eq _ _ _ _ _ _ _

end Extension

end NatTrans

end CategoryTheory

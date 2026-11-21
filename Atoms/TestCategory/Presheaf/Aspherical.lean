import Atoms.ForMathlib.CategoryTheory.Limits.FunctorToTypes
import Atoms.TestCategory.BasicLocalizer.Homotopy
import Mathlib.CategoryTheory.Limits.Types.Limits

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

private def elementsYonedaToOver (A : Type u) [SmallCategory A] (a : A) :
    ((yoneda.obj a).Elements)ᵒᵖ ⥤ Over a where
  obj X := Over.mk (X.unop.2 : unop X.unop.1 ⟶ a)
  map {X Y} f := Over.homMk f.unop.val.unop (CategoryOfElements.map_snd f.unop)
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

private def overToElementsYoneda (A : Type u) [SmallCategory A] (a : A) :
    Over a ⥤ ((yoneda.obj a).Elements)ᵒᵖ where
  obj U := op ((yoneda.obj a).elementsMk (op U.left) U.hom)
  map {U V} g := (CategoryOfElements.homMk ((yoneda.obj a).elementsMk (op V.left) V.hom)
    ((yoneda.obj a).elementsMk (op U.left) U.hom) g.left.op (Over.w g)).op
  map_id _ := rfl
  map_comp _ _ := rfl

def elementsYonedaCatIso (A : Type u) [SmallCategory A] (a : A) :
    (elementsFunctor A).obj (yoneda.obj a) ≅ Cat.of (Over a) where
  hom := (elementsYonedaToOver A a).toCatHom
  inv := (overToElementsYoneda A a).toCatHom
  hom_inv_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)
  inv_hom_id := Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)

def elementsYonedaFunctorIso (A : Type u) [SmallCategory A] :
    yoneda ⋙ elementsFunctor A ≅ Over.mapFunctor A :=
  NatIso.ofComponents (fun a => elementsYonedaCatIso A a) fun _ =>
    Cat.Hom.ext (Functor.hext (fun _ => rfl) fun _ _ _ => heq_of_eq rfl)

noncomputable def elementsTerminalHom (A : Type u) [SmallCategory A] :
    (elementsFunctor A).obj (⊤_ (Aᵒᵖ ⥤ Type u)) ⟶ Cat.of A :=
  Cat.Hom.ofFunctor (elementsTerminalEquivalence A).functor

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A]

def PshAspherical (X : Aᵒᵖ ⥤ Type u) : Prop := 𝒲.Aspherical ((elementsFunctor A).obj X)

instance hasTerminal_elementsFunctor_obj_yoneda (a : A) :
    HasTerminal ((elementsFunctor A).obj (yoneda.obj a)) :=
  IsTerminal.hasTerminal (C := ((yoneda.obj a).Elements)ᵒᵖ) (Functor.Elements.isInitial a).op

theorem pshAspherical_yoneda (a : A) : 𝒲.PshAspherical A (yoneda.obj a) :=
  𝒲.terminal_aspherical _

theorem wPsh_yoneda_map {a b : A} (f : a ⟶ b) : 𝒲.wPsh A (yoneda.map f) :=
  𝒲.W_of_aspherical_of_hasTerminal _ (𝒲.pshAspherical_yoneda A a)

theorem W_elementsTerminalHom : 𝒲.W (elementsTerminalHom A) :=
  have : (elementsTerminalHom A).toFunctor.IsEquivalence :=
    (elementsTerminalEquivalence A).isEquivalence_functor
  𝒲.W_of_isEquivalence _

theorem pshAspherical_iff_wPsh_terminal_from (hA : 𝒲.Aspherical (Cat.of A))
    (X : Aᵒᵖ ⥤ Type u) : 𝒲.PshAspherical A X ↔ 𝒲.wPsh A (terminal.from X) :=
  𝒲.aspherical_iff_W ((elementsFunctor A).map (terminal.from X))
    ((𝒲.aspherical_iff_of_W _ (𝒲.W_elementsTerminalHom A)).2 hA)

theorem pshAspherical_iff_of_iso {X Y : Aᵒᵖ ⥤ Type u} (e : X ≅ Y) :
    𝒲.PshAspherical A X ↔ 𝒲.PshAspherical A Y :=
  ⟨𝒲.aspherical_of_equivalence (Cat.equivOfIso ((elementsFunctor A).mapIso e)),
    𝒲.aspherical_of_equivalence (Cat.equivOfIso ((elementsFunctor A).mapIso e.symm))⟩

theorem wPsh_of_pshAspherical {X Y : Aᵒᵖ ⥤ Type u} (f : X ⟶ Y) (hX : 𝒲.PshAspherical A X)
    (hY : 𝒲.PshAspherical A Y) : 𝒲.wPsh A f := by
  have e : terminal.from ((elementsFunctor A).obj X) =
      (elementsFunctor A).map f ≫ terminal.from _ := terminal.hom_ext _ _
  unfold PshAspherical Aspherical at hX hY
  rw [e] at hX
  exact 𝒲.W.of_postcomp _ _ hY hX

theorem W_elementsFunctor_map_iff {B : Type u} [SmallCategory B] {P Q : Bᵒᵖ ⥤ Type u}
    (g : P ⟶ Q) :
    𝒲.W ((elementsFunctor B).map g) ↔ 𝒲.W (CostructuredArrow.map (S := yoneda) g).toCatHom := by
  exact 𝒲.W_iff_of_isEquivalence_of_iso (C₁ := (elementsFunctor B).obj P)
    (C₂ := (elementsFunctor B).obj Q) (CategoryOfElements.toCostructuredArrow P).toCatHom
    (CategoryOfElements.toCostructuredArrow Q).toCatHom
    (CategoryOfElements.costructuredArrowYonedaEquivalence P).isEquivalence_functor
    (CategoryOfElements.costructuredArrowYonedaEquivalence Q).isEquivalence_functor _ _
    (eqToIso (CategoryOfElements.costructuredArrow_yoneda_equivalence_naturality g).symm)

theorem pshAspherical_iff_aspherical_costructuredArrow {B : Type u} [SmallCategory B]
    (P : Bᵒᵖ ⥤ Type u) :
    𝒲.PshAspherical B P ↔ 𝒲.Aspherical (Cat.of (CostructuredArrow yoneda P)) :=
  𝒲.aspherical_iff_of_equivalence (CategoryOfElements.costructuredArrowYonedaEquivalence P)

end BasicLocalizer

end Atoms.TestCategory

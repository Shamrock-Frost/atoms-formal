import Atoms.ForMathlib.CategoryTheory.Grothendieck
import Atoms.TestCategory.BasicLocalizer.Homotopy

open CategoryTheory Limits

namespace Atoms.TestCategory

universe u

namespace BasicLocalizer

variable (𝒲 : BasicLocalizer.{u}) {I : Type u} [SmallCategory I]

theorem W_grothendieckFiberToSlice (F : I ⥤ Cat.{u, u}) (i : I) :
    𝒲.W (Grothendieck.fiberToSlice F i).toCatHom :=
  𝒲.W_of_adjunction_right (u := (Grothendieck.sliceToFiber F i).toCatHom)
    (v := (Grothendieck.fiberToSlice F i).toCatHom) (Grothendieck.sliceAdjunction F i)

theorem aspherical_costructuredArrow_forget_iff (F : I ⥤ Cat.{u, u}) (i : I) :
    𝒲.Aspherical (Cat.of (CostructuredArrow (Grothendieck.forget F) i)) ↔
      𝒲.Aspherical (F.obj i) := by
  have hv := 𝒲.W_grothendieckFiberToSlice F i
  have e : terminal.from (Cat.of ↥(F.obj i)) =
      (Grothendieck.fiberToSlice F i).toCatHom ≫ terminal.from _ := terminal.hom_ext _ _
  unfold Aspherical
  change _ ↔ 𝒲.W (terminal.from (Cat.of ↥(F.obj i)))
  rw [e]
  exact ⟨fun h => 𝒲.W.comp_mem _ _ hv h, fun h => 𝒲.W.of_precomp _ _ hv h⟩

theorem W_grothendieckMap {F G : I ⥤ Cat.{u, u}} (α : F ⟶ G) (h : ∀ i, 𝒲.W (α.app i)) :
    𝒲.W (Grothendieck.map α).toCatHom := by
  refine 𝒲.quillenA (Grothendieck.map α).toCatHom (Grothendieck.forget G).toCatHom
    fun (i : I) => ?_
  have hF := 𝒲.W_grothendieckFiberToSlice F i
  have hαG : 𝒲.W ((α.app i : Cat.of ↥(F.obj i) ⟶ Cat.of ↥(G.obj i)) ≫
      (Grothendieck.fiberToSlice G i).toCatHom) :=
    𝒲.W.comp_mem _ _ (h i) (𝒲.W_grothendieckFiberToSlice G i)
  have hcomp : 𝒲.W ((Grothendieck.fiberToSlice F i).toCatHom ≫
      (CostructuredArrow.pre (Grothendieck.map α) (Grothendieck.forget G) i).toCatHom) :=
    (𝒲.W_iff_of_natTrans (u := (Grothendieck.fiberToSlice F i).toCatHom ≫
      (CostructuredArrow.pre (Grothendieck.map α) (Grothendieck.forget G) i).toCatHom)
      (v := (α.app i : Cat.of ↥(F.obj i) ⟶ Cat.of ↥(G.obj i)) ≫
        (Grothendieck.fiberToSlice G i).toCatHom)
      (Grothendieck.fiberToSliceMapComp α i)).2 hαG
  exact 𝒲.W.of_precomp _ _ hF hcomp

theorem W_grothendieckMap_of_type {J : Type} [SmallCategory J] {F G : J ⥤ Cat.{u, u}}
    (α : F ⟶ G) (h : ∀ j, 𝒲.W (α.app j)) : 𝒲.W (Grothendieck.map α).toCatHom := by
  let e : AsSmall.{u} J ≌ J := AsSmall.equiv.symm
  have hpre : ∀ H : J ⥤ Cat.{u, u}, 𝒲.W (Grothendieck.pre H e.functor).toCatHom := fun H =>
    have : (Grothendieck.pre H e.functor).toCatHom.toFunctor.IsEquivalence :=
      (Grothendieck.preEquivalence H e).isEquivalence_functor
    𝒲.W_of_isEquivalence _
  have hcomp : 𝒲.W (Grothendieck.pre F e.functor ⋙ Grothendieck.map α).toCatHom := by
    rw [Grothendieck.pre_comp_map]
    exact 𝒲.W.comp_mem _ _ (𝒲.W_grothendieckMap _ fun j => h _) (hpre G)
  exact 𝒲.W.of_precomp _ _ (hpre F) hcomp

end BasicLocalizer

namespace BasicLocalizer

theorem W_grothendieck_terminal_inclusion {B : Type u} [SmallCategory B]
    (𝒲 : BasicLocalizer.{u}) (F : B ⥤ Cat.{u, u}) (b : B) (hb : IsTerminal b) :
    𝒲.W (Grothendieck.ι F b).toCatHom := by
  have : (CostructuredArrow.proj (Grothendieck.forget F) b).IsEquivalence :=
    { full := ⟨fun {X Y} m => ⟨CostructuredArrow.homMk m (hb.hom_ext _ _), rfl⟩⟩
      essSurj := ⟨fun Z => ⟨CostructuredArrow.mk (hb.from _), ⟨Iso.refl _⟩⟩⟩ }
  have : (CostructuredArrow.proj (Grothendieck.forget F) b).toCatHom.toFunctor.IsEquivalence :=
    this
  have hproj : 𝒲.W (CostructuredArrow.proj (Grothendieck.forget F) b).toCatHom :=
    𝒲.W_of_isEquivalence _
  exact 𝒲.W.comp_mem _ _ (𝒲.W_grothendieckFiberToSlice F b) hproj

end BasicLocalizer

namespace BasicLocalizer

def CatDiagramLocallyConstant {B : Type u} [SmallCategory B]
    (𝒲 : BasicLocalizer.{u}) (F : B ⥤ Cat.{u, u}) : Prop :=
  ∀ ⦃b c : B⦄ (f : b ⟶ c), 𝒲.W (F.map f)

def CommaLocallyConstant {A B : Type u} [SmallCategory A] [SmallCategory B]
    (𝒲 : BasicLocalizer.{u}) (u : A ⥤ B) : Prop :=
  ∀ ⦃b c : B⦄ (f : b ⟶ c), 𝒲.W (CostructuredArrow.map (S := u) f).toCatHom

theorem catDiagramLocallyConstant_pre {B D : Type u} [SmallCategory B] [SmallCategory D]
    (𝒲 : BasicLocalizer.{u}) (F : B ⥤ Cat.{u, u}) (v : D ⥤ B)
    (h : 𝒲.CatDiagramLocallyConstant F) : 𝒲.CatDiagramLocallyConstant (v ⋙ F) :=
  fun _ _ f => h (v.map f)

theorem W_grothendieck_inclusion {B : Type u} [SmallCategory B] [HasTerminal B]
    (𝒲 : BasicLocalizer.{u}) (F : B ⥤ Cat.{u, u})
    (h : 𝒲.CatDiagramLocallyConstant F) (b : B) :
    𝒲.W (Grothendieck.ι F b).toCatHom := by
  let f : b ⟶ ⊤_ B := terminal.from b
  have hf : 𝒲.W (F.map f) := h f
  have ht : 𝒲.W (Grothendieck.ι F (⊤_ B)).toCatHom :=
    𝒲.W_grothendieck_terminal_inclusion F (⊤_ B) terminalIsTerminal
  have hcomp : 𝒲.W (F.map f ≫ (Grothendieck.ι F (⊤_ B)).toCatHom) :=
    𝒲.W.comp_mem _ _ hf ht
  exact (𝒲.W_iff_of_natTrans (Grothendieck.ιNatTrans (F := F) f)).2 hcomp

theorem W_grothendieck_pre_of_hasTerminal {B D : Type u} [SmallCategory B] [SmallCategory D]
    [HasTerminal B] [HasTerminal D]
    (𝒲 : BasicLocalizer.{u}) (F : B ⥤ Cat.{u, u}) (hF : 𝒲.CatDiagramLocallyConstant F)
    (v : D ⥤ B) : 𝒲.W (Grothendieck.pre F v).toCatHom := by
  have h₁ := 𝒲.W_grothendieck_inclusion (v ⋙ F) (𝒲.catDiagramLocallyConstant_pre F v hF) (⊤_ D)
  have h₂ := 𝒲.W_grothendieck_inclusion F hF (v.obj (⊤_ D))
  have h₃ := (𝒲.W_iff_of_natTrans
    (u := (Grothendieck.ι (v ⋙ F) (⊤_ D)).toCatHom ≫ (Grothendieck.pre F v).toCatHom)
    (v := (Grothendieck.ι F (v.obj (⊤_ D))).toCatHom) (Grothendieck.ιCompPreHom F v (⊤_ D))).2 h₂
  exact 𝒲.W.of_precomp _ _ h₁ h₃

end BasicLocalizer

end Atoms.TestCategory

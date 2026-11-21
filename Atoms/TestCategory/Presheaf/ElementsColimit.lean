import Atoms.ForMathlib.CategoryTheory.Elements
import Atoms.TestCategory.BasicLocalizer.Opposite
import Mathlib.CategoryTheory.Grothendieck

open CategoryTheory Limits Opposite

namespace Atoms.TestCategory

universe u

variable (𝒲 : BasicLocalizer.{u}) (A : Type u) [SmallCategory A] {I : Type u} [SmallCategory I]

section Comparison

variable {A}

def grothendieckElement {F : I ⥤ Aᵒᵖ ⥤ Type u} (X : Grothendieck (F ⋙ elementsFunctor A)) :
    (F.obj X.base).Elements :=
  unop X.fiber

def grothendieckHomVal {F : I ⥤ Aᵒᵖ ⥤ Type u} {X Y : Grothendieck (F ⋙ elementsFunctor A)}
    (f : X ⟶ Y) : (grothendieckElement Y).1 ⟶ (grothendieckElement X).1 :=
  (unop f.fiber).val

theorem grothendieckHomVal_snd {F : I ⥤ Aᵒᵖ ⥤ Type u}
    {X Y : Grothendieck (F ⋙ elementsFunctor A)} (f : X ⟶ Y) :
    (F.obj Y.base).map (grothendieckHomVal f) (grothendieckElement Y).2 =
      (F.map f.base).app _ (grothendieckElement X).2 :=
  (unop f.fiber).2

theorem grothendieckHomVal_id {F : I ⥤ Aᵒᵖ ⥤ Type u}
    (X : Grothendieck (F ⋙ elementsFunctor A)) : grothendieckHomVal (𝟙 X) = 𝟙 _ := by
  have h : ((F ⋙ elementsFunctor A).map (𝟙 X.base)).toFunctor.obj X.fiber = X.fiber :=
    congrArg (fun Φ : (F ⋙ elementsFunctor A).obj X.base ⟶ (F ⋙ elementsFunctor A).obj X.base =>
      Φ.toFunctor.obj X.fiber) ((F ⋙ elementsFunctor A).map_id X.base)
  exact (CategoryOfElements.eqToHom_unop_val (F := F.obj X.base) h).trans (eqToHom_refl _ _)

theorem grothendieckHomVal_comp {F : I ⥤ Aᵒᵖ ⥤ Type u}
    {X Y Z : Grothendieck (F ⋙ elementsFunctor A)} (f : X ⟶ Y) (g : Y ⟶ Z) :
    grothendieckHomVal (f ≫ g) = grothendieckHomVal g ≫ grothendieckHomVal f := by
  have e : grothendieckHomVal (f ≫ g) =
      (grothendieckHomVal g ≫ grothendieckHomVal f) ≫ 𝟙 _ :=
    congrArg (fun t => (grothendieckHomVal g ≫ grothendieckHomVal f) ≫ t)
      ((CategoryOfElements.eqToHom_unop_val (F := F.obj Z.base) _).trans (eqToHom_refl _ _))
  rw [e, Category.comp_id]

theorem grothendieck_hom_ext {F : I ⥤ Aᵒᵖ ⥤ Type u}
    {X Y : Grothendieck (F ⋙ elementsFunctor A)} {f g : X ⟶ Y} (hb : f.base = g.base)
    (hv : grothendieckHomVal f = grothendieckHomVal g) : f = g := by
  obtain ⟨b, φ⟩ := f
  obtain ⟨b', φ'⟩ := g
  subst hb
  congr 1
  exact Quiver.Hom.unop_inj (Subtype.ext hv)

theorem grothendieckHomVal_map {F G : I ⥤ Aᵒᵖ ⥤ Type u} (χ : F ⟶ G)
    {X Y : Grothendieck (F ⋙ elementsFunctor A)} (φ : X ⟶ Y) :
    grothendieckHomVal ((Grothendieck.map (Functor.whiskerRight χ (elementsFunctor A))).map φ) =
      grothendieckHomVal φ := by
  have e : grothendieckHomVal
      ((Grothendieck.map (Functor.whiskerRight χ (elementsFunctor A))).map φ) =
      grothendieckHomVal φ ≫ (unop ((eqToHom
        ((Functor.whiskerRight χ (elementsFunctor A)).naturality φ.base).symm).toNatTrans.app
          X.fiber)).val := rfl
  have hq : ((Functor.whiskerRight χ (elementsFunctor A)).app X.base ≫
      (G ⋙ elementsFunctor A).map φ.base).toFunctor.obj X.fiber =
      ((F ⋙ elementsFunctor A).map φ.base ≫
        (Functor.whiskerRight χ (elementsFunctor A)).app Y.base).toFunctor.obj X.fiber :=
    congrArg (fun Φ : (F ⋙ elementsFunctor A).obj X.base ⟶
        (G ⋙ elementsFunctor A).obj Y.base => Φ.toFunctor.obj X.fiber)
      ((Functor.whiskerRight χ (elementsFunctor A)).naturality φ.base).symm
  have h1 : (unop (eqToHom hq)).val = 𝟙 _ :=
    (CategoryOfElements.eqToHom_unop_val (F := G.obj Y.base) hq).trans (eqToHom_refl _ _)
  rw [e, Cat.eqToHom_app]
  exact (congrArg (fun t => grothendieckHomVal φ ≫ t) h1).trans (Category.comp_id _)

variable (A) in
def elementsColimitComparisonFunctor (F : I ⥤ Aᵒᵖ ⥤ Type u) (c : Cocone F) :
    Grothendieck (F ⋙ elementsFunctor A) ⥤ (c.pt.Elements)ᵒᵖ where
  obj X := op ⟨(grothendieckElement X).1, (c.ι.app X.base).app _ (grothendieckElement X).2⟩
  map {X Y} f := (CategoryOfElements.homMk
    ⟨(grothendieckElement Y).1, (c.ι.app Y.base).app _ (grothendieckElement Y).2⟩
    ⟨(grothendieckElement X).1, (c.ι.app X.base).app _ (grothendieckElement X).2⟩
    (grothendieckHomVal f) (by
    dsimp only
    rw [← NatTrans.naturality_apply, grothendieckHomVal_snd]
    exact congrArg (fun φ : F.obj X.base ⟶ c.pt => φ.app _ (grothendieckElement X).2)
      (c.w f.base))).op
  map_id X := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (grothendieckHomVal_id X))
  map_comp f g :=
    Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (grothendieckHomVal_comp f g))

end Comparison

def elementsColimitComparison (F : I ⥤ Aᵒᵖ ⥤ Type u) (c : Cocone F) :
    Cat.of (Grothendieck (F ⋙ elementsFunctor A)) ⟶ (elementsFunctor A).obj c.pt :=
  (elementsColimitComparisonFunctor A F c).toCatHom

theorem elementsColimitComparison_naturality {F G : I ⥤ Aᵒᵖ ⥤ Type u} (χ : F ⟶ G)
    (cF : Cocone F) (cG : Cocone G) (f : cF.pt ⟶ cG.pt)
    (hf : ∀ i, cF.ι.app i ≫ f = χ.app i ≫ cG.ι.app i) :
    (Grothendieck.map (Functor.whiskerRight χ (elementsFunctor A))).toCatHom ≫
        elementsColimitComparison A G cG =
      elementsColimitComparison A F cF ≫ (elementsFunctor A).map f := by
  have hobj : ∀ X : Grothendieck (F ⋙ elementsFunctor A),
      (elementsColimitComparisonFunctor A G cG).obj
          ((Grothendieck.map (Functor.whiskerRight χ (elementsFunctor A))).obj X) =
        ((elementsFunctor A).map f).toFunctor.obj
          ((elementsColimitComparisonFunctor A F cF).obj X) := fun X => by
    have h := congrArg (fun φ : F.obj X.base ⟶ cG.pt =>
      φ.app (grothendieckElement X).1 (grothendieckElement X).2) (hf X.base)
    change op (⟨(grothendieckElement X).1, (cG.ι.app X.base).app _
        ((χ.app X.base).app _ (grothendieckElement X).2)⟩ : cG.pt.Elements) =
      op ⟨(grothendieckElement X).1, f.app _ ((cF.ι.app X.base).app _ (grothendieckElement X).2)⟩
    exact congrArg (fun t => op (⟨(grothendieckElement X).1, t⟩ : cG.pt.Elements)) h.symm
  refine Cat.Hom.ext (Functor.ext hobj fun X Y φ => ?_)
  refine Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ ?_)
  have e1 : (eqToHom (hobj X)).unop.val = 𝟙 _ :=
    (CategoryOfElements.eqToHom_unop_val (hobj X)).trans (eqToHom_refl _ _)
  have e2 : (eqToHom (hobj Y).symm).unop.val = 𝟙 _ :=
    (CategoryOfElements.eqToHom_unop_val (hobj Y).symm).trans (eqToHom_refl _ _)
  change grothendieckHomVal
      ((Grothendieck.map (Functor.whiskerRight χ (elementsFunctor A))).map φ) =
    ((eqToHom (hobj Y).symm).unop.val ≫ grothendieckHomVal φ) ≫ (eqToHom (hobj X)).unop.val
  rw [e1, e2]
  exact (grothendieckHomVal_map χ φ).trans
    ((Category.comp_id _).trans (Category.id_comp _)).symm

def colimitFiberFunctor (F : I ⥤ Aᵒᵖ ⥤ Type u) (c : Cocone F) (a : A)
    (s : c.pt.obj (op a)) : I ⥤ Type u where
  obj i := {x : (F.obj i).obj (op a) // (c.ι.app i).app (op a) x = s}
  map {i j} k := ↾fun x => ⟨(F.map k).app (op a) x.1, by
    exact (congrArg (fun φ : F.obj i ⟶ c.pt => φ.app (op a) x.1) (c.w k)).trans x.2⟩
  map_id i := by ext x; simp
  map_comp _ _ := by ext x; simp

section CoSlice

variable (F : I ⥤ Aᵒᵖ ⥤ Type u) (c : Cocone F) (a : A) (s : c.pt.obj (op a))

def colimitFiberBase : (elementsFunctor A).obj c.pt := op (⟨op a, s⟩ : c.pt.Elements)

variable {A F c a s}

def coSliceVal
    (b : StructuredArrow (colimitFiberBase A F c a s) (elementsColimitComparison A F c).toFunctor) :
    (grothendieckElement b.right).1 ⟶ op a :=
  (unop b.hom).val

theorem coSliceVal_snd
    (b : StructuredArrow (colimitFiberBase A F c a s) (elementsColimitComparison A F c).toFunctor) :
    c.pt.map (coSliceVal b) ((c.ι.app b.right.base).app _ (grothendieckElement b.right).2) = s :=
  (unop b.hom).2

theorem coSliceVal_w
    {b b' : StructuredArrow (colimitFiberBase A F c a s)
      (elementsColimitComparison A F c).toFunctor}
    (φ : b ⟶ b') : grothendieckHomVal φ.right ≫ coSliceVal b = coSliceVal b' :=
  congrArg (fun t => (unop t).val) (StructuredArrow.w φ)

variable (A F c a s)

def fiberToCoSlice : (colimitFiberFunctor A F c a s).Elements ⥤
    StructuredArrow (colimitFiberBase A F c a s) (elementsColimitComparison A F c).toFunctor where
  obj p := StructuredArrow.mk
    (Y := (⟨p.1, op (⟨op a, p.2.1⟩ : (F.obj p.1).Elements)⟩ :
      Grothendieck (F ⋙ elementsFunctor A)))
    (CategoryOfElements.homMk ⟨op a, (c.ι.app p.1).app (op a) p.2.1⟩ ⟨op a, s⟩ (𝟙 _)
      (by simp [p.2.2])).op
  map {p q} φ := StructuredArrow.homMk
    (⟨φ.1, (CategoryOfElements.homMk ⟨op a, q.2.1⟩ ⟨op a, (F.map φ.1).app (op a) p.2.1⟩ (𝟙 _)
      (by
        have h := congrArg Subtype.val φ.2
        change (F.map φ.1).app (op a) p.2.1 = q.2.1 at h
        rw [h]
        simp)).op⟩ : Grothendieck.Hom _ _)
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.comp_id _)))
  map_id p := by
    refine StructuredArrow.hom_ext _ _ (grothendieck_hom_ext rfl ?_)
    exact (grothendieckHomVal_id (F := F)
      (⟨p.1, op (⟨op a, p.2.1⟩ : (F.obj p.1).Elements)⟩ : Grothendieck _)).symm
  map_comp φ ψ := by
    refine StructuredArrow.hom_ext _ _ (grothendieck_hom_ext rfl ?_)
    exact ((grothendieckHomVal_comp (F := F) _ _).trans (Category.id_comp _)).symm

def coSliceToFiber :
    StructuredArrow (colimitFiberBase A F c a s) (elementsColimitComparison A F c).toFunctor ⥤
      (colimitFiberFunctor A F c a s).Elements where
  obj b := ⟨b.right.base, ⟨(F.obj b.right.base).map (coSliceVal b) (grothendieckElement b.right).2,
    by rw [NatTrans.naturality_apply]; exact coSliceVal_snd b⟩⟩
  map {b b'} φ := ⟨φ.right.base, Subtype.ext (by
    change (F.map φ.right.base).app (op a)
        ((F.obj b.right.base).map (coSliceVal b) (grothendieckElement b.right).2) =
      (F.obj b'.right.base).map (coSliceVal b') (grothendieckElement b'.right).2
    rw [NatTrans.naturality_apply, ← grothendieckHomVal_snd φ.right, ← coSliceVal_w φ,
      Functor.map_comp_apply])⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def fiberToCoSliceHomEquiv (p : (colimitFiberFunctor A F c a s).Elements)
    (b : StructuredArrow (colimitFiberBase A F c a s) (elementsColimitComparison A F c).toFunctor) :
    ((fiberToCoSlice A F c a s).obj p ⟶ b) ≃ (p ⟶ (coSliceToFiber A F c a s).obj b) where
  toFun φ := ⟨φ.right.base, Subtype.ext (by
    have hv : grothendieckHomVal φ.right = coSliceVal b :=
      (Category.comp_id _).symm.trans (coSliceVal_w φ)
    change (F.map φ.right.base).app (op a) p.2.1 =
      (F.obj b.right.base).map (coSliceVal b) (grothendieckElement b.right).2
    rw [← hv]
    exact (grothendieckHomVal_snd φ.right).symm)⟩
  invFun ψ := StructuredArrow.homMk
    (⟨ψ.1, (CategoryOfElements.homMk (grothendieckElement b.right)
      ⟨op a, (F.map ψ.1).app (op a) p.2.1⟩ (coSliceVal b)
      (congrArg Subtype.val ψ.2).symm).op⟩ : Grothendieck.Hom _ _)
    (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ (Category.comp_id _)))
  left_inv φ := by
    refine StructuredArrow.hom_ext _ _ (grothendieck_hom_ext rfl ?_)
    exact ((Category.comp_id _).symm.trans (coSliceVal_w φ)).symm
  right_inv _ := rfl

def fiberToCoSliceAdjunction : fiberToCoSlice A F c a s ⊣ coSliceToFiber A F c a s :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fiberToCoSliceHomEquiv A F c a s
      homEquiv_naturality_left_symm := fun _ _ => by
        refine StructuredArrow.hom_ext _ _ (grothendieck_hom_ext rfl ?_)
        exact ((grothendieckHomVal_comp (F := F) _ _).trans (Category.comp_id _)).symm
      homEquiv_naturality_right := fun _ _ => rfl }

end CoSlice

namespace BasicLocalizer

theorem aspherical_structuredArrow_elementsColimitComparison
    (F : I ⥤ Aᵒᵖ ⥤ Type u) (c : Cocone F) (a : A) (s : c.pt.obj (op a))
    (h : 𝒲.Aspherical (Cat.of (colimitFiberFunctor A F c a s).Elements)) :
    𝒲.Aspherical (Cat.of (StructuredArrow (colimitFiberBase A F c a s)
      (elementsColimitComparison A F c).toFunctor)) :=
  (𝒲.aspherical_iff_of_W _ (𝒲.W_of_adjunction (v := (coSliceToFiber A F c a s).toCatHom)
    (fiberToCoSliceAdjunction A F c a s))).1 h

theorem W_elementsColimitComparison (F : I ⥤ Aᵒᵖ ⥤ Type u) (c : Cocone F)
    (h : ∀ (a : A) (s : c.pt.obj (op a)),
      𝒲.Aspherical (Cat.of (colimitFiberFunctor A F c a s).Elements)) :
    𝒲.W (elementsColimitComparison A F c) :=
  𝒲.W_of_forall_aspherical_structuredArrow _ fun b => by
    obtain ⟨⟨⟨a⟩, s⟩⟩ := b
    exact 𝒲.aspherical_structuredArrow_elementsColimitComparison A F c a s (h a s)

end BasicLocalizer

end Atoms.TestCategory

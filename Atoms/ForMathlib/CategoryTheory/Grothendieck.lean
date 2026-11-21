import Atoms.ForMathlib.CategoryTheory.Category.Cat.Limit
import Atoms.ForMathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Grothendieck

universe v₂ u₂ v₁ u₁ v u

namespace CategoryTheory.Grothendieck

open Limits

variable {C : Type u} [Category.{v} C] {F : C ⥤ Cat.{v₂, u₂}}

theorem toTransport_comp_ι_map {i : C} (Z : Grothendieck F) (b : Z.base ⟶ i) {y : ↥(F.obj i)}
    (φ : (F.map b).toFunctor.obj Z.fiber ⟶ y) :
    Z.toTransport b ≫ (ι F i).map φ = (⟨b, φ⟩ : Z ⟶ (ι F i).obj y) :=
  Grothendieck.ext _ _ (Category.comp_id b) (by
    change eqToHom _ ≫ (eqToHom _ ≫ (F.map (𝟙 i)).toFunctor.map
      (𝟙 ((F.map b).toFunctor.obj Z.fiber)) ≫ (eqToHom _ ≫ φ)) = φ
    rw [(F.map (𝟙 i)).toFunctor.map_id, Category.id_comp]
    have key : ∀ {a b c : ↥(F.obj i)} (p : a = b) (q : b = c) (r : c = a) {e : ↥(F.obj i)}
        (ψ : a ⟶ e), eqToHom p ≫ eqToHom q ≫ eqToHom r ≫ ψ = ψ := by
      intros
      subst_vars
      simp
    exact key _ _ _ φ)

def natTransMk {E : Type u₁} [Category.{v₁} E] {G H : Grothendieck F ⥤ E}
    (app : ∀ X, G.obj X ⟶ H.obj X)
    (fiber : ∀ (c : C) {x y : ↥(F.obj c)} (φ : x ⟶ y),
      G.map ((ι F c).map φ) ≫ app ⟨c, y⟩ = app ⟨c, x⟩ ≫ H.map ((ι F c).map φ))
    (base : ∀ {c c' : C} (b : c ⟶ c') (x : ↥(F.obj c)),
      G.map ((ιNatTrans b).app x) ≫ app _ = app ⟨c, x⟩ ≫ H.map ((ιNatTrans b).app x)) :
    G ⟶ H where
  app := app
  naturality := by
    rintro X ⟨j, y⟩ ⟨b, φ⟩
    have h : X.toTransport b ≫ (ι F j).map φ = ⟨b, φ⟩ := toTransport_comp_ι_map X b φ
    exact (congrArg (G.map · ≫ app ⟨j, y⟩) h.symm).trans <|
      (congrArg (· ≫ app ⟨j, y⟩) (G.map_comp _ _)).trans <| (Category.assoc _ _ _).trans <|
      (congrArg (G.map (X.toTransport b) ≫ ·) (fiber j φ)).trans <|
      (Category.assoc _ _ _).symm.trans <|
      (congrArg (· ≫ H.map ((ι F j).map φ)) (base b X.fiber)).trans <|
      (Category.assoc _ _ _).trans <| (congrArg (app X ≫ ·) (H.map_comp _ _).symm).trans <|
      congrArg (app X ≫ H.map ·) h

variable {D : Type u₁} [Category.{v₁} D]

def ιCompPreHom (F : C ⥤ Cat.{v₂, u₂}) (v : D ⥤ C) (d : D) :
    ι (v ⋙ F) d ⋙ pre F v ⟶ ι F (v.obj d) where
  app x := 𝟙 _
  naturality x y f := by
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact Grothendieck.ext _ _ (v.map_id d) (eqToHom_trans_assoc _ _ _)

section Slice

variable {I : Type u} [SmallCategory I]

def fiberToSlice (F : I ⥤ Cat.{u, u}) (i : I) :
    ↥(F.obj i) ⥤ CostructuredArrow (Grothendieck.forget F) i where
  obj x := CostructuredArrow.mk (Y := (Grothendieck.ι F i).obj x) (𝟙 i)
  map g := CostructuredArrow.homMk ((Grothendieck.ι F i).map g) (Category.comp_id _)
  map_id x := CostructuredArrow.hom_ext _ _ ((Grothendieck.ι F i).map_id x)
  map_comp g h := CostructuredArrow.hom_ext _ _ ((Grothendieck.ι F i).map_comp g h)

def sliceBase {F : I ⥤ Cat.{u, u}} {i : I}
    (X : CostructuredArrow (Grothendieck.forget F) i) : X.left.base ⟶ i :=
  X.hom

theorem fiberToSlice_base_eq (F : I ⥤ Cat.{u, u}) (i : I)
    {X : CostructuredArrow (Grothendieck.forget F) i} {y : ↥(F.obj i)}
    (m : X ⟶ (fiberToSlice F i).obj y) : m.left.base = sliceBase X :=
  (Category.comp_id _).symm.trans (CostructuredArrow.w m)

def sliceHomEquiv (F : I ⥤ Cat.{u, u}) (i : I)
    (X : CostructuredArrow (Grothendieck.forget F) i) (y : ↥(F.obj i)) :
    ((F.map (sliceBase X)).toFunctor.obj X.left.fiber ⟶ y) ≃
      (X ⟶ (fiberToSlice F i).obj y) where
  toFun φ := CostructuredArrow.homMk
    (⟨sliceBase X, φ⟩ : X.left ⟶ (Grothendieck.ι F i).obj y) (Category.comp_id _)
  invFun m := eqToHom (by rw [fiberToSlice_base_eq F i m]; rfl) ≫ m.left.fiber
  left_inv φ := Category.id_comp φ
  right_inv m := by
    have hb := fiberToSlice_base_eq F i m
    rcases m with ⟨⟨b', φ'⟩, r, w⟩
    change b' = sliceBase X at hb
    subst hb
    exact CostructuredArrow.hom_ext _ _
      (Grothendieck.ext _ _ rfl ((Category.id_comp _).trans (Category.id_comp _)))

def sliceToFiber (F : I ⥤ Cat.{u, u}) (i : I) :
    CostructuredArrow (Grothendieck.forget F) i ⥤ ↥(F.obj i) :=
  Adjunction.leftAdjointOfEquiv (G := fiberToSlice F i)
    (F_obj := fun X => (F.map (sliceBase X)).toFunctor.obj X.left.fiber)
    (sliceHomEquiv F i) fun X _ _ g h => CostructuredArrow.hom_ext _ _
      ((Grothendieck.toTransport_comp_ι_map X.left _ (h ≫ g)).symm.trans
        (((congrArg (X.left.toTransport (sliceBase X) ≫ ·)
          ((Grothendieck.ι F i).map_comp h g)).trans (Category.assoc _ _ _).symm).trans
          (congrArg (· ≫ (Grothendieck.ι F i).map g)
            (Grothendieck.toTransport_comp_ι_map X.left _ h))))

def sliceAdjunction (F : I ⥤ Cat.{u, u}) (i : I) :
    sliceToFiber F i ⊣ fiberToSlice F i :=
  Adjunction.adjunctionOfEquivLeft _ _

def fiberToSliceMapComp {F G : I ⥤ Cat.{u, u}} (α : F ⟶ G) (i : I) :
    fiberToSlice F i ⋙
        CostructuredArrow.pre (Grothendieck.map α) (Grothendieck.forget G) i ⟶
      (α.app i).toFunctor ⋙ fiberToSlice G i where
  app x := CostructuredArrow.homMk ((Grothendieck.ιCompMap α i).hom.app x)
    (Category.comp_id _)
  naturality _ _ g :=
    CostructuredArrow.hom_ext _ _ ((Grothendieck.ιCompMap α i).hom.naturality g)

end Slice

section Restriction

variable {B D : Type u} [SmallCategory B] [SmallCategory D]

theorem isPullback_pre (F : B ⥤ Cat.{u, u}) (v : D ⥤ B) :
    IsPullback (Grothendieck.pre F v).toCatHom (Grothendieck.forget (v ⋙ F)).toCatHom
      (Grothendieck.forget F).toCatHom v.toCatHom := by
  refine Cat.isPullback_of_elementwise rfl ?_ ?_ ?_ ?_
  · rintro ⟨d₁, x₁⟩ ⟨d₂, x₂⟩ h₁ h₂
    change d₁ = d₂ at h₂
    subst h₂
    change (⟨v.obj d₁, x₁⟩ : Grothendieck F) = ⟨v.obj d₁, x₂⟩ at h₁
    cases h₁
    rfl
  · rintro ⟨b, x⟩ d (e : b = v.obj d)
    subst e
    exact ⟨⟨d, x⟩, rfl, rfl⟩
  · rintro p₁ p₂ ⟨b₁, f₁⟩ ⟨b₂, f₂⟩ h₁ (h₂ : b₁ = b₂)
    subst h₂
    change (⟨v.map b₁, f₁⟩ : (Grothendieck.pre F v).obj p₁ ⟶ (Grothendieck.pre F v).obj p₂) =
      ⟨v.map b₁, f₂⟩ at h₁
    cases h₁
    rfl
  · rintro p₁ p₂ ⟨a, φ⟩ β e
    change a = eqToHom rfl ≫ v.map β ≫ eqToHom rfl at e
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at e
    subst e
    exact ⟨⟨β, φ⟩, rfl, rfl⟩

end Restriction

section Span

variable {E : Type u} [Category.{v} E] {X Y Z : Cat.{v₂, u₂}} {f : X ⟶ Y} {g : X ⟶ Z}
  (m₀ : ↥X ⥤ E) (m₁ : ↥Y ⥤ E) (m₂ : ↥Z ⥤ E)

def spanFiberFunctor : (c : WalkingSpan) → ↥((span f g).obj c) ⥤ E
  | .zero => m₀
  | .left => m₁
  | .right => m₂

variable (γ₁ : m₀ ⟶ f.toFunctor ⋙ m₁) (γ₂ : m₀ ⟶ g.toFunctor ⋙ m₂)

def spanFiberTrans : {c c' : WalkingSpan} → (e : c ⟶ c') →
    (spanFiberFunctor m₀ m₁ m₂ c ⟶ ((span f g).map e).toFunctor ⋙ spanFiberFunctor m₀ m₁ m₂ c')
  | _, _, .id _ => 𝟙 _
  | _, _, .init .left => γ₁
  | _, _, .init .right => γ₂

def spanFunctorFrom : Grothendieck (span f g) ⥤ E :=
  functorFrom (spanFiberFunctor m₀ m₁ m₂) (spanFiberTrans m₀ m₁ m₂ γ₁ γ₂) (fun _ => rfl) (by
    rintro c₁ c₂ c₃ (_ | (_ | _)) (_ | (_ | _)) <;>
    first
    | exact ((Category.id_comp _).trans (Category.comp_id _)).symm
    | exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (Category.comp_id _).symm))

theorem spanFunctorFrom_map_ι (c : WalkingSpan) {x y : ↥((span f g).obj c)} (φ : x ⟶ y) :
    (spanFunctorFrom m₀ m₁ m₂ γ₁ γ₂).map ((ι (span f g) c).map φ) =
      (spanFiberFunctor m₀ m₁ m₂ c).map φ := by
  change 𝟙 _ ≫ (spanFiberFunctor m₀ m₁ m₂ c).map (𝟙 _ ≫ φ) = _
  rw [Category.id_comp, Category.id_comp]

theorem spanFunctorFrom_map_fst (x : ↥X) :
    (spanFunctorFrom m₀ m₁ m₂ γ₁ γ₂).map ((ιNatTrans (F := span f g) WalkingSpan.Hom.fst).app x) =
      γ₁.app x :=
  (congrArg (γ₁.app x ≫ ·) (m₁.map_id _)).trans (Category.comp_id _)

theorem spanFunctorFrom_map_snd (x : ↥X) :
    (spanFunctorFrom m₀ m₁ m₂ γ₁ γ₂).map ((ιNatTrans (F := span f g) WalkingSpan.Hom.snd).app x) =
      γ₂.app x :=
  (congrArg (γ₂.app x ≫ ·) (m₂.map_id _)).trans (Category.comp_id _)

theorem ι_right_comp_spanFunctorFrom :
    ι (span f g) .right ⋙ spanFunctorFrom m₀ m₁ m₂ γ₁ γ₂ = m₂ :=
  Functor.ext (fun _ => rfl) (fun x y φ => by
    change 𝟙 _ ≫ m₂.map (𝟙 _ ≫ φ) = 𝟙 _ ≫ m₂.map φ ≫ 𝟙 _
    simp only [Category.id_comp, Category.comp_id]
    exact congrArg m₂.map (Category.id_comp φ))

def spanNatTransMk {G H : Grothendieck (span f g) ⥤ E} (app : ∀ W, G.obj W ⟶ H.obj W)
    (fiber : ∀ (c : WalkingSpan) {x y : ↥((span f g).obj c)} (φ : x ⟶ y),
      G.map ((ι (span f g) c).map φ) ≫ app ⟨c, y⟩ = app ⟨c, x⟩ ≫ H.map ((ι (span f g) c).map φ))
    (fst : ∀ x : ↥X, G.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.fst).app x) ≫ app _ =
      app ⟨.zero, x⟩ ≫ H.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.fst).app x))
    (snd : ∀ x : ↥X, G.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.snd).app x) ≫ app _ =
      app ⟨.zero, x⟩ ≫ H.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.snd).app x)) :
    G ⟶ H :=
  natTransMk app fiber (by
    rintro c _ (_ | (_ | _)) x
    · exact (congrArg (· ≫ app _) (G.map_id _)).trans <| (Category.id_comp _).trans <|
        (Category.comp_id _).symm.trans (congrArg (app _ ≫ ·) (H.map_id _).symm)
    · exact fst x
    · exact snd x)

theorem spanFunctor_ext {G H : Grothendieck (span f g) ⥤ E} (hobj : ∀ W, G.obj W = H.obj W)
    (fiber : ∀ (c : WalkingSpan) {x y : ↥((span f g).obj c)} (φ : x ⟶ y),
      G.map ((ι (span f g) c).map φ) ≫ eqToHom (hobj ⟨c, y⟩) =
        eqToHom (hobj ⟨c, x⟩) ≫ H.map ((ι (span f g) c).map φ))
    (fst : ∀ x : ↥X, G.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.fst).app x) ≫
      eqToHom (hobj _) =
        eqToHom (hobj ⟨.zero, x⟩) ≫ H.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.fst).app x))
    (snd : ∀ x : ↥X, G.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.snd).app x) ≫
      eqToHom (hobj _) =
        eqToHom (hobj ⟨.zero, x⟩) ≫ H.map ((ιNatTrans (F := span f g) WalkingSpan.Hom.snd).app x)) :
    G = H :=
  Functor.ext hobj fun _ W' φ => ((comp_eqToHom_iff (hobj W') _ _).1
    ((spanNatTransMk (fun W => eqToHom (hobj W)) fiber fst snd).naturality φ)).trans
    (Category.assoc _ _ _)

end Span

end CategoryTheory.Grothendieck

namespace CategoryTheory

open Opposite

def prodElementsFunctor {A B : Type u} [SmallCategory A] [SmallCategory B]
    (X : (A × B)ᵒᵖ ⥤ Type u) :
    Grothendieck (prodCurry X ⋙ Functor.elementsFunctor) ⥤ X.Elements where
  obj t := ⟨op (t.fiber.1.unop, t.base.unop), t.fiber.2⟩
  map {t u} f := CategoryOfElements.homMk _ _
    (op (CategoryTheory.Prod.mkHom f.fiber.val.unop f.base.unop))
    ((CategoryTheory.Prod.map_op_mkHom_apply X _ _ _).trans f.fiber.2)
  map_id t := by
    obtain ⟨b, ⟨a, x⟩⟩ := t
    have hval : (Grothendieck.Hom.fiber
        (𝟙 (⟨b, ⟨a, x⟩⟩ : Grothendieck (prodCurry X ⋙ Functor.elementsFunctor)))).val =
        𝟙 a := by
      let hh : ((prodCurry X ⋙ Functor.elementsFunctor).map (𝟙 b)).toFunctor.obj
          ⟨a, x⟩ = (⟨a, x⟩ : ((prodCurry X).obj b).Elements) :=
        congrArg (fun m : (prodCurry X ⋙ Functor.elementsFunctor).obj b ⟶
          (prodCurry X ⋙ Functor.elementsFunctor).obj b => m.toFunctor.obj ⟨a, x⟩)
          ((prodCurry X ⋙ Functor.elementsFunctor).map_id b)
      change (eqToHom hh).val = 𝟙 a
      exact (CategoryOfElements.eqToHom_val hh).trans (by
        have he : congrArg (fun z : ((prodCurry X).obj b).Elements => z.1) hh = rfl :=
          Subsingleton.elim _ _
        rw [he]
        rfl)
    apply CategoryOfElements.ext
    dsimp only [CategoryOfElements.homMk]
    simp only [Grothendieck.id_base]
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.Prod.hom_ext
    · rw [hval]
      change (𝟙 a).unop = 𝟙 a.unop
      rfl
    · rfl
  map_comp := by
    intro t u v f g
    let F := prodCurry X ⋙ Functor.elementsFunctor
    let hobj : (F.map (f.base ≫ g.base)).toFunctor.obj t.fiber =
        (F.map g.base).toFunctor.obj ((F.map f.base).toFunctor.obj t.fiber) := by
      exact congrArg (fun m : F.obj t.base ⟶ F.obj v.base =>
        m.toFunctor.obj t.fiber) (F.map_comp f.base g.base)
    have hid : (eqToHom hobj).val = 𝟙 t.fiber.1 := by
      exact (CategoryOfElements.eqToHom_val hobj).trans (by
        have he : congrArg (fun z : ((prodCurry X).obj v.base).Elements => z.1)
            hobj = rfl := Subsingleton.elim _ _
        rw [he]
        rfl)
    have hval : (f ≫ g).fiber.val = f.fiber.val ≫ g.fiber.val := by
      have hc := congrArg Subtype.val (Grothendieck.comp_fiber f g)
      have hmap : ((F.map g.base).toFunctor.map f.fiber).val = f.fiber.val := by
        cases f.fiber
        rfl
      have he : 𝟙 t.fiber.1 ≫ f.fiber.val = f.fiber.val := by
        change 𝟙 ((F.map f.base).toFunctor.obj t.fiber).1 ≫ f.fiber.val = f.fiber.val
        exact Category.id_comp _
      have hmiddle : (eqToHom hobj).val ≫
          ((F.map g.base).toFunctor.map f.fiber).val ≫ g.fiber.val =
          f.fiber.val ≫ g.fiber.val := by
        rw [hid, hmap]
        exact (Category.assoc _ _ _).symm.trans
          (congrArg (fun m => m ≫ g.fiber.val) he)
      exact hc.trans hmiddle
    apply CategoryOfElements.ext
    dsimp only [CategoryOfElements.homMk]
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.Prod.hom_ext
    · rw [hval]
      rfl
    · rfl

instance prodElementsFunctor_isEquivalence {A B : Type u} [SmallCategory A] [SmallCategory B]
    (X : (A × B)ᵒᵖ ⥤ Type u) : (prodElementsFunctor X).IsEquivalence where
  essSurj :=
    { mem_essImage z := by
        let t : Grothendieck (prodCurry X ⋙ Functor.elementsFunctor) :=
          ⟨op z.1.unop.2, ⟨op z.1.unop.1, z.2⟩⟩
        exact ⟨t, ⟨Iso.refl z⟩⟩ }
  faithful :=
    { map_injective {t u} f g h := by
        have hb : f.base = g.base := by
          have hv := congrArg (fun k : (prodElementsFunctor X).obj t ⟶
            (prodElementsFunctor X).obj u => k.val.unop.2) h
          exact Quiver.Hom.unop_inj hv
        cases f with
        | mk fb ff =>
        cases g with
        | mk gb gf =>
        dsimp at hb
        subst gb
        congr 1
        apply CategoryOfElements.ext
        have hv := congrArg (fun k : (prodElementsFunctor X).obj t ⟶
          (prodElementsFunctor X).obj u => k.val.unop.1) h
        exact Quiver.Hom.unop_inj hv }
  full :=
    { map_surjective {t u} h := by
        refine ⟨{ base := op h.val.unop.2, fiber := ?_ }, ?_⟩
        · exact CategoryOfElements.homMk _ _ (op h.val.unop.1)
            ((CategoryTheory.Prod.map_op_mkHom_apply X _ _ _).symm.trans h.2)
        · apply CategoryOfElements.ext
          rfl }

def prodElementsFunctorNaturality {A B : Type u}
    [SmallCategory A] [SmallCategory B]
    {X Y : (A × B)ᵒᵖ ⥤ Type u} (φ : X ⟶ Y) :
    prodElementsFunctor X ⋙ NatTrans.mapElements φ ≅
      Grothendieck.map
        (Functor.whiskerRight (prodCurryMap φ) Functor.elementsFunctor) ⋙
          prodElementsFunctor Y :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro t u f
    change (prodElementsFunctor X ⋙ NatTrans.mapElements φ).map f ≫ 𝟙 _ =
      𝟙 _ ≫ (Grothendieck.map
        (Functor.whiskerRight (prodCurryMap φ) Functor.elementsFunctor) ⋙
          prodElementsFunctor Y).map f
    rw [Category.comp_id, Category.id_comp]
    apply CategoryOfElements.ext
    dsimp only [CategoryOfElements.homMk]
    apply Quiver.Hom.unop_inj
    apply CategoryTheory.Prod.hom_ext
    · let α := Functor.whiskerRight (prodCurryMap φ) Functor.elementsFunctor
      let hobj := congrArg (fun m :
          (prodCurry X ⋙ Functor.elementsFunctor).obj t.base ⟶
            (prodCurry Y ⋙ Functor.elementsFunctor).obj u.base =>
          m.toFunctor.obj t.fiber) (α.naturality f.base).symm
      have hid : ((eqToHom (α.naturality f.base).symm).toNatTrans.app
          t.fiber).val = 𝟙 t.fiber.1 := by
        rw [Cat.eqToHom_app]
        exact (CategoryOfElements.eqToHom_val hobj).trans (by
          have he : congrArg (fun z : ((prodCurry Y).obj u.base).Elements => z.1)
              hobj = rfl := Subsingleton.elim _ _
          rw [he]
          rfl)
      have hmap : ((α.app u.base).toFunctor.map f.fiber).val = f.fiber.val := by
        cases f.fiber
        rfl
      have hval : ((Grothendieck.map α).map f).fiber.val = f.fiber.val := by
        rw [Grothendieck.map_map]
        change ((eqToHom (α.naturality f.base).symm).toNatTrans.app t.fiber).val ≫
          ((α.app u.base).toFunctor.map f.fiber).val = f.fiber.val
        rw [hid, hmap]
        exact Category.id_comp _
      change f.fiber.val.unop = ((Grothendieck.map α).map f).fiber.val.unop
      rw [hval]
      rfl
    · rfl)

end CategoryTheory

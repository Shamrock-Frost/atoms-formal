import Atoms.ForMathlib.CategoryTheory.Comma.Over.Basic
import Atoms.ForMathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Elements

namespace CategoryTheory

open Limits Opposite

universe w w₁ v₁ v₂ v₃ u₁ u₂ u₃

namespace CategoryOfElements

variable {C : Type u₁} [Category.{v₁} C] {F : C ⥤ Type w}

@[simp]
theorem eqToHom_val {x y : F.Elements} (h : x = y) :
    (eqToHom h).val = eqToHom (congrArg Sigma.fst h) :=
  eqToHom_map (π F) h

theorem eqToHom_unop_val {x y : (F.Elements)ᵒᵖ} (h : x = y) :
    (eqToHom h).unop.val = eqToHom (congrArg (fun z => z.unop.1) h).symm := by
  rw [eqToHom_unop, eqToHom_val]

theorem map_eqToHom_snd {x y : F.Elements} (h : x = y) :
    F.map (eqToHom (congrArg Sigma.fst h)) x.2 = y.2 := by
  subst h
  simp

theorem map_eq_of_unop_val_eq {D : Type u₃} [Category.{v₃} D] (v : (F.Elements)ᵒᵖ ⥤ D)
    {a b : C} {y y' : F.obj a} {z z' : F.obj b} (hy : y = y') (hz : z = z')
    (f : (op ⟨a, y⟩ : (F.Elements)ᵒᵖ) ⟶ op ⟨b, z⟩)
    (f' : (op ⟨a, y'⟩ : (F.Elements)ᵒᵖ) ⟶ op ⟨b, z'⟩) (h : f.unop.1 = f'.unop.1) :
    v.map f' = eqToHom (by rw [hy]) ≫ v.map f ≫ eqToHom (by rw [hz]) := by
  subst hy hz
  obtain rfl : f = f' := Quiver.Hom.unop_inj (Subtype.ext h)
  simp

theorem op_hom_ext {X : Cᵒᵖ ⥤ Type w} {p q : (X.Elements)ᵒᵖ} {f g : p ⟶ q}
    (h : f.unop.1.unop = g.unop.1.unop) : f = g :=
  Quiver.Hom.unop_inj (ext _ _ _ (Quiver.Hom.unop_inj h))

def opHomMk {X : Cᵒᵖ ⥤ Type w} {p q : (X.Elements)ᵒᵖ} (α : p.unop.1.unop ⟶ q.unop.1.unop)
    (h : X.map α.op q.unop.2 = p.unop.2) : p ⟶ q :=
  (homMk q.unop p.unop α.op h).op

section AsSmall

variable {C : Type u₁} [Category.{v₁} C] (X : Cᵒᵖ ⥤ Type w)

def asSmallFunctor :
    (AsSmall.down.op ⋙ X : (AsSmall.{w₁} C)ᵒᵖ ⥤ Type w).Elements ⥤ X.Elements where
  obj p := ⟨op (AsSmall.down.obj (unop p.1)), p.2⟩
  map g := ⟨(AsSmall.down.map g.1.unop).op, g.2⟩

def asSmallInverse :
    X.Elements ⥤ (AsSmall.down.op ⋙ X : (AsSmall.{w₁} C)ᵒᵖ ⥤ Type w).Elements where
  obj p := ⟨op (AsSmall.up.obj (unop p.1)), p.2⟩
  map g := ⟨(AsSmall.up.map g.1.unop).op, g.2⟩

end AsSmall

end CategoryOfElements

namespace Functor

variable {I : Type w} [SmallCategory I]

abbrev FreeOnElementsObj (G : I ⥤ Type w) (j : I) : Type w :=
  Σ e : (Σ i, G.obj i), e.1 ⟶ j

abbrev freeOnElements (G : I ⥤ Type w) : I ⥤ Type w where
  obj j := FreeOnElementsObj G j
  map k := ↾fun (p : FreeOnElementsObj G _) => (⟨p.1, p.2 ≫ k⟩ : FreeOnElementsObj G _)
  map_id _ := ConcreteCategory.hom_ext _ _ fun (p : FreeOnElementsObj G _) =>
    show (⟨p.1, p.2 ≫ 𝟙 _⟩ : FreeOnElementsObj G _) = p from
      Sigma.ext rfl (heq_of_eq (Category.comp_id p.2))
  map_comp k k' := ConcreteCategory.hom_ext _ _ fun (p : FreeOnElementsObj G _) =>
    show (⟨p.1, p.2 ≫ k ≫ k'⟩ : FreeOnElementsObj G _) = ⟨p.1, (p.2 ≫ k) ≫ k'⟩ from
      Sigma.ext rfl (heq_of_eq (Category.assoc p.2 k k').symm)

def freeOnElementsπ (G : I ⥤ Type w) : freeOnElements G ⟶ G where
  app j := ↾fun (p : FreeOnElementsObj G j) => G.map p.2 p.1.2
  naturality _ _ k := ConcreteCategory.hom_ext _ _ fun (p : FreeOnElementsObj G _) =>
    Functor.map_comp_apply G p.2 k p.1.2

theorem freeOnElementsπ_surjective (G : I ⥤ Type w) (j : I) :
    Function.Surjective ((freeOnElementsπ G).app j) := fun x =>
  ⟨(⟨⟨j, x⟩, 𝟙 j⟩ : FreeOnElementsObj G j), Functor.map_id_apply G j x⟩

end Functor

variable {A : Type u₁} [Category.{v₁} A]

namespace Functor

variable (D : A ⥤ Cat.{v₂, u₂}) (C : Type u₃) [Category.{v₃} C]

def nerve : Aᵒᵖ ⥤ Type (max u₂ v₂ u₃ v₃) where
  obj a := D.obj a.unop ⥤ C
  map f := TypeCat.ofHom fun G ↦ (D.map f.unop).toFunctor ⋙ G
  map_id a := by
    ext G
    simp [Functor.id_comp]
  map_comp f g := by
    ext G
    simp [Functor.assoc]

@[simp]
theorem nerve_map_apply {a b : Aᵒᵖ} (f : a ⟶ b) (G : D.obj a.unop ⥤ C) :
    (D.nerve C).map f G = (D.map f.unop).toFunctor ⋙ G :=
  rfl

variable {C} {C' : Type u₃} [Category.{v₃} C']

def nerveMap (F : C ⥤ C') : D.nerve C ⟶ D.nerve C' where
  app _ := TypeCat.ofHom fun G ↦ G ⋙ F

@[simp]
theorem nerveMap_app_apply (F : C ⥤ C') (a : Aᵒᵖ) (G : D.obj a.unop ⥤ C) :
    (D.nerveMap F).app a G = G ⋙ F :=
  rfl

end Functor

namespace Functor

variable {D : A ⥤ Cat.{v₂, u₂}} {t : ∀ a, D.obj a}

section

variable (t) (C : Type u₃) [Category.{v₃} C]

theorem nerve_elements_obj_eq {x y : ((D.nerve C).Elements)ᵒᵖ} (f : x ⟶ y) :
    x.unop.2.obj (t x.unop.1.unop) =
      y.unop.2.obj ((D.map f.unop.val.unop).toFunctor.obj (t x.unop.1.unop)) :=
  congrArg (fun G : D.obj x.unop.1.unop ⥤ C ↦ G.obj (t x.unop.1.unop)) f.unop.2.symm

end

variable (ht : ∀ a, IsTerminal (t a)) (C : Type u₃) [Category.{v₃} C] {C' : Type u₃}
  [Category.{v₃} C']

private theorem eqToHom_comp_map_from_id {a : A} (G : D.obj a ⥤ C)
    (e : G.obj (t a) = G.obj ((D.map (𝟙 a)).toFunctor.obj (t a))) :
    eqToHom e ≫ G.map ((ht a).from ((D.map (𝟙 a)).toFunctor.obj (t a))) = 𝟙 _ := by
  rw [(ht a).hom_ext ((ht a).from _) (eqToHom (by rw [D.map_id]; rfl)), eqToHom_map,
    eqToHom_trans, eqToHom_refl]

private theorem eqToHom_comp_map_from_comp {a b c : A} (u : a ⟶ b) (v : b ⟶ c)
    {F : D.obj a ⥤ C} {G : D.obj b ⥤ C} {H : D.obj c ⥤ C} (hG : (D.map v).toFunctor ⋙ H = G)
    (hF : (D.map u).toFunctor ⋙ G = F)
    (e : F.obj (t a) = H.obj ((D.map (u ≫ v)).toFunctor.obj (t a)))
    (e₁ : F.obj (t a) = G.obj ((D.map u).toFunctor.obj (t a)))
    (e₂ : G.obj (t b) = H.obj ((D.map v).toFunctor.obj (t b))) :
    eqToHom e ≫ H.map ((ht c).from ((D.map (u ≫ v)).toFunctor.obj (t a))) =
      (eqToHom e₁ ≫ G.map ((ht b).from ((D.map u).toFunctor.obj (t a)))) ≫
        eqToHom e₂ ≫ H.map ((ht c).from ((D.map v).toFunctor.obj (t b))) := by
  subst hG hF
  rw [(ht c).hom_ext ((ht c).from ((D.map (u ≫ v)).toFunctor.obj (t a)))
    (eqToHom (by rw [D.map_comp]; rfl) ≫ (D.map v).toFunctor.map ((ht b).from _) ≫
      (ht c).from _)]
  simp only [eqToHom_refl, Category.id_comp, Functor.comp_map, Functor.map_comp, eqToHom_map,
    eqToHom_trans_assoc]

def nerveEvalTerminal : ((D.nerve C).Elements)ᵒᵖ ⥤ C where
  obj x := x.unop.2.obj (t x.unop.1.unop)
  map {x y} f := eqToHom (nerve_elements_obj_eq t C f) ≫
    y.unop.2.map ((ht _).from ((D.map f.unop.val.unop).toFunctor.obj (t x.unop.1.unop)))
  map_id x := eqToHom_comp_map_from_id ht C x.unop.2 _
  map_comp f g := eqToHom_comp_map_from_comp ht C _ _ g.unop.2 f.unop.2 _ _ _

@[simp]
theorem nerveEvalTerminal_obj (x : ((D.nerve C).Elements)ᵒᵖ) :
    (nerveEvalTerminal ht C).obj x = x.unop.2.obj (t x.unop.1.unop) :=
  rfl

private theorem map_eqToHom_comp_map {I : Type u₂} [Category.{v₂} I] (F : C ⥤ C') (G : I ⥤ C)
    {x : C} {i j : I} (e : x = G.obj i) (e' : F.obj x = (G ⋙ F).obj i) (k : i ⟶ j)
    (h₁ : F.obj x = F.obj x) (h₂ : F.obj (G.obj j) = F.obj (G.obj j)) :
    F.map (eqToHom e ≫ G.map k) = eqToHom h₁ ≫ (eqToHom e' ≫ (G ⋙ F).map k) ≫ eqToHom h₂ := by
  subst e
  simp

theorem nerveEvalTerminal_comp (F : C ⥤ C') :
    nerveEvalTerminal ht C ⋙ F =
      (NatTrans.mapElements (D.nerveMap F)).op ⋙ nerveEvalTerminal ht C' :=
  Functor.ext (fun _ ↦ rfl) (fun _ _ _ ↦ map_eqToHom_comp_map C F _ _ _ _ _ _)

end Functor

namespace NatTrans

variable {D : A ⥤ Cat.{v₂, u₂}} {C : Type u₃} [Category.{v₃} C]
  {P : Aᵒᵖ ⥤ Type (max u₂ v₂ u₃ v₃)} (φ : P ⟶ D.nerve C) (c : C)

@[ext]
structure OverLift (a : Aᵒᵖ) where
  elt : P.obj a
  lift : D.obj a.unop ⥤ Over c
  w : φ.app a elt = lift ⋙ Over.forget c

def overLifts : Aᵒᵖ ⥤ Type (max u₂ v₂ u₃ v₃) where
  obj a := φ.OverLift c a
  map f := TypeCat.ofHom fun q ↦
    ⟨P.map f q.elt, (D.map f.unop).toFunctor ⋙ q.lift,
      (NatTrans.naturality_apply φ f q.elt).trans (congrArg (fun G ↦ (D.nerve C).map f G) q.w)⟩
  map_id a := by
    ext q
    · simp
    · simp [Functor.id_comp]
  map_comp f g := by
    ext q
    · simp
    · simp [Functor.assoc]

@[simp]
theorem overLifts_map_apply_elt {a b : Aᵒᵖ} (f : a ⟶ b) (q : φ.OverLift c a) :
    ((φ.overLifts c).map f q).elt = P.map f q.elt :=
  rfl

@[simp]
theorem overLifts_map_apply_lift {a b : Aᵒᵖ} (f : a ⟶ b) (q : φ.OverLift c a) :
    ((φ.overLifts c).map f q).lift = (D.map f.unop).toFunctor ⋙ q.lift :=
  rfl

variable {t : ∀ a, D.obj a} (ht : ∀ a, IsTerminal (t a))

theorem OverLift.evalTerminal_eq {φ : P ⟶ D.nerve C} {c : C} {a : Aᵒᵖ} (q : φ.OverLift c a) :
    ((mapElements φ).op ⋙ Functor.nerveEvalTerminal ht C).obj (op ⟨a, q.elt⟩) =
      (q.lift.obj (t a.unop)).left :=
  congrArg (fun K : D.obj a.unop ⥤ C ↦ K.obj (t a.unop)) q.w

def toOverLifts :
    CostructuredArrow ((mapElements φ).op ⋙ Functor.nerveEvalTerminal ht C) c ⥤
      ((φ.overLifts c).Elements)ᵒᵖ where
  obj X := op ⟨X.left.unop.1, ⟨X.left.unop.2, (ht _).overLift (φ.app _ X.left.unop.2) X.hom, rfl⟩⟩
  map {X Y} m := (CategoryOfElements.homMk (F := φ.overLifts c) _ _ m.left.unop.val (by
    exact OverLift.ext m.left.unop.2
      ((ht _).comp_overLift (ht _) (D.map m.left.unop.val.unop).toFunctor
        ((NatTrans.naturality_apply φ _ _).symm.trans
          (congrArg (fun p ↦ φ.app _ p) m.left.unop.2))
        X.hom Y.hom _ _ (CostructuredArrow.w m)))).op
  map_id _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)
  map_comp _ _ := Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl)

def ofOverLifts :
    ((φ.overLifts c).Elements)ᵒᵖ ⥤
      CostructuredArrow ((mapElements φ).op ⋙ Functor.nerveEvalTerminal ht C) c where
  obj Z := CostructuredArrow.mk (Y := op ⟨Z.unop.1, Z.unop.2.elt⟩)
    (eqToHom (Z.unop.2.evalTerminal_eq ht) ≫ (Z.unop.2.lift.obj (t Z.unop.1.unop)).hom)
  map {Z Z'} m := by
    exact CostructuredArrow.homMk
      (CategoryOfElements.homMk (F := P) ⟨Z'.unop.1, Z'.unop.2.elt⟩ ⟨Z.unop.1, Z.unop.2.elt⟩
        m.unop.val (congrArg OverLift.elt m.unop.2)).op
      (Over.eqToHom_comp_map_comp_eqToHom_comp_hom (D.map m.unop.val.unop).toFunctor
        (congrArg OverLift.lift m.unop.2) Z.unop.2.w Z'.unop.2.w _ _)
  map_id _ := CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl))
  map_comp _ _ :=
    CostructuredArrow.hom_ext _ _ (Quiver.Hom.unop_inj (CategoryOfElements.ext _ _ _ rfl))

theorem toOverLifts_comp_ofOverLifts : φ.toOverLifts c ht ⋙ φ.ofOverLifts c ht = 𝟭 _ :=
  Functor.ext_of_comp_faithful (CostructuredArrow.proj _ _)
    (fun X ↦ congrArg
      (CostructuredArrow.mk (S := (mapElements φ).op ⋙ Functor.nerveEvalTerminal ht C) (T := c)
        (Y := X.left)) ((Category.id_comp _).trans ((ht _).overLift_obj_self_hom _ X.hom)))
    (Functor.ext_of_comp_faithful (CategoryOfElements.π _).op (fun _ ↦ rfl) rfl)

theorem ofOverLifts_comp_toOverLifts : φ.ofOverLifts c ht ⋙ φ.toOverLifts c ht = 𝟭 _ :=
  Functor.ext_of_comp_faithful (CategoryOfElements.π _).op
    (fun Z ↦ congrArg op (Sigma.ext rfl (heq_of_eq
      (OverLift.ext rfl ((ht _).overLift_eqToHom_comp_hom Z.unop.2.w)))))
    rfl

def overLiftsEquivalence :
    CostructuredArrow ((mapElements φ).op ⋙ Functor.nerveEvalTerminal ht C) c ≌
      ((φ.overLifts c).Elements)ᵒᵖ :=
  Equivalence.mk (φ.toOverLifts c ht) (φ.ofOverLifts c ht)
    (eqToIso (φ.toOverLifts_comp_ofOverLifts c ht).symm)
    (eqToIso (φ.ofOverLifts_comp_toOverLifts c ht))

end NatTrans

namespace Functor

variable (D : A ⥤ Cat.{v₂, u₂}) (C : Type u₃) [Category.{v₃} C] (c : C)

def nerveOverLiftsIso : NatTrans.overLifts (𝟙 (D.nerve C)) c ≅ D.nerve (Over c) :=
  NatIso.ofComponents (fun _ ↦ Equiv.toIso
    { toFun q := q.lift
      invFun G := ⟨G ⋙ Over.forget c, G, rfl⟩
      left_inv q := NatTrans.OverLift.ext q.w.symm rfl
      right_inv _ := rfl }) (fun _ ↦ rfl)

variable {D} {t : ∀ a, D.obj a} (ht : ∀ a, IsTerminal (t a))

def nerveOverEquivalence :
    CostructuredArrow (nerveEvalTerminal ht C) c ≌ ((D.nerve (Over c)).Elements)ᵒᵖ :=
  (NatTrans.overLiftsEquivalence (𝟙 (D.nerve C)) c ht).trans
    (Cat.equivOfIso (Functor.elementsFunctor.mapIso (D.nerveOverLiftsIso C c))).op

end Functor

section

universe w' u

namespace Functor

variable {A : Type u} [SmallCategory A]

@[simps]
def elementSliceFunctor (X : Aᵒᵖ ⥤ Type u) {a : Aᵒᵖ} (x : X.obj a) :
    Over a.unop ⥤ (X.Elements)ᵒᵖ where
  obj f := op ⟨op f.left, X.map f.hom.op x⟩
  map {f f'} g := (CategoryOfElements.homMk ⟨op f'.left, X.map f'.hom.op x⟩
    ⟨op f.left, X.map f.hom.op x⟩ g.left.op (by
      rw [← Functor.map_comp_apply, ← op_comp, Over.w])).op
  map_id _ := rfl
  map_comp _ _ := rfl

theorem elementSliceFunctor_eq_map_comp (X : Aᵒᵖ ⥤ Type u) {a b : Aᵒᵖ} (g : a ⟶ b)
    (x : X.obj a) :
    elementSliceFunctor X (X.map g x) = Over.map g.unop ⋙ elementSliceFunctor X x :=
  Functor.ext_of_comp_faithful (CategoryOfElements.π _).op (fun f => by simp) rfl

theorem elementSliceFunctor_naturality {X Y : Aᵒᵖ ⥤ Type u} (α : X ⟶ Y) {a : Aᵒᵖ}
    (x : X.obj a) :
    elementSliceFunctor Y (α.app a x) = elementSliceFunctor X x ⋙ (NatTrans.mapElements α).op :=
  Functor.ext_of_comp_faithful (CategoryOfElements.π _).op
    (fun _ => congrArg op (Sigma.ext rfl (heq_of_eq (NatTrans.naturality_apply α _ x).symm))) rfl

end Functor

section Decomposition

variable {A : Type u} [SmallCategory A] {X : Aᵒᵖ ⥤ Type u} {I : Type w} [Category.{w'} I] {t : I}

@[simps obj]
def liftElements (ht : IsTerminal t) (G : I ⥤ A) (x : X.obj (op (G.obj t))) :
    I ⥤ (X.Elements)ᵒᵖ where
  obj c := op ⟨op (G.obj c), X.map (G.map (ht.from c)).op x⟩
  map {c c'} g := Quiver.Hom.op ⟨(G.map g).op, by
    change X.map (G.map g).op (X.map (G.map (ht.from c')).op x) = _
    rw [← Functor.map_comp_apply, ← op_comp, ← G.map_comp, ht.comp_from g]⟩
  map_id c := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    change (G.map (𝟙 c)).op = 𝟙 _
    simp
  map_comp f g := by
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    change (G.map (f ≫ g)).op = (G.map g).op ≫ (G.map f).op
    simp

variable (t) in
def decomposeElements (F : I ⥤ (X.Elements)ᵒᵖ) : Σ G : I ⥤ A, X.obj (op (G.obj t)) :=
  ⟨F ⋙ (CategoryOfElements.π X).leftOp, (F.obj t).unop.2⟩

def elementsLiftEquiv (ht : IsTerminal t) :
    (I ⥤ (X.Elements)ᵒᵖ) ≃ Σ G : I ⥤ A, X.obj (op (G.obj t)) where
  toFun := decomposeElements t
  invFun p := liftElements ht p.1 p.2
  left_inv F := by
    have hobj : ∀ c, (liftElements ht (decomposeElements t F).1
        (decomposeElements t F).2).obj c = F.obj c := fun c => by
      change op (⟨_, _⟩ : X.Elements) = op (unop (F.obj c))
      congr 1
      exact Sigma.ext rfl (heq_of_eq (F.map (ht.from c)).unop.2)
    refine CategoryTheory.Functor.ext hobj ?_
    intro c c' g
    apply Quiver.Hom.unop_inj
    apply CategoryOfElements.ext
    simp only [unop_comp, CategoryOfElements.comp_val, CategoryOfElements.eqToHom_unop_val]
    erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  right_inv p := by
    obtain ⟨G, x⟩ := p
    refine Sigma.ext rfl (heq_of_eq ?_)
    change X.map (G.map (ht.from t)).op x = x
    rw [ht.from_self]
    simp

end Decomposition

end

end CategoryTheory

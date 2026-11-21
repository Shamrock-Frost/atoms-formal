import Mathlib.CategoryTheory.Comma.Over.Basic

namespace CategoryTheory

open Limits

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {I : Type u₁} [Category.{v₁} I] {J : Type u₂} [Category.{v₂} J]
  {C : Type u₃} [Category.{v₃} C] {c : C}

namespace Limits.IsTerminal

variable {t : I} (ht : IsTerminal t)

def overLift (G : I ⥤ C) (g : G.obj t ⟶ c) : I ⥤ Over c where
  obj s := Over.mk (G.map (ht.from s) ≫ g)
  map {s s'} f := Over.homMk (G.map f) (by
    dsimp only [Over.mk_hom]
    rw [← Category.assoc, ← G.map_comp, ht.comp_from])

@[simp]
theorem overLift_obj_hom (G : I ⥤ C) (g : G.obj t ⟶ c) (s : I) :
    ((ht.overLift G g).obj s).hom = G.map (ht.from s) ≫ g :=
  rfl

@[simp]
theorem overLift_map_left (G : I ⥤ C) (g : G.obj t ⟶ c) {s s' : I} (f : s ⟶ s') :
    ((ht.overLift G g).map f).left = G.map f :=
  rfl

@[simp]
theorem overLift_comp_forget (G : I ⥤ C) (g : G.obj t ⟶ c) :
    ht.overLift G g ⋙ Over.forget c = G :=
  rfl

theorem overLift_obj_self_hom (G : I ⥤ C) (g : G.obj t ⟶ c) :
    ((ht.overLift G g).obj t).hom = g := by
  rw [overLift_obj_hom, ht.from_self, G.map_id, Category.id_comp]

theorem overLift_forget (H : I ⥤ Over c) :
    ht.overLift (H ⋙ Over.forget c) (H.obj t).hom = H := by
  refine Functor.ext (fun s ↦ ?_) (fun s s' f ↦ ?_)
  · change Over.mk ((H.map (ht.from s)).left ≫ (H.obj t).hom) = H.obj s
    rw [Over.w]
    rfl
  · ext
    rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

theorem overLift_eqToHom_comp_hom {H : I ⥤ C} {G : I ⥤ Over c} (hH : H = G ⋙ Over.forget c) :
    ht.overLift H (eqToHom (congrArg (fun K : I ⥤ C ↦ K.obj t) hH) ≫ (G.obj t).hom) = G := by
  subst hH
  exact (congrArg (ht.overLift (G ⋙ Over.forget c)) (Category.id_comp (G.obj t).hom)).trans
    (ht.overLift_forget G)

theorem comp_overLift {s : J} (hs : IsTerminal s) (θ : I ⥤ J) {G : I ⥤ C} {G' : J ⥤ C}
    (hG : θ ⋙ G' = G) (g : G.obj t ⟶ c) (g' : G'.obj s ⟶ c) (e : G.obj t = G'.obj (θ.obj t))
    (k : θ.obj t ⟶ s) (hg : (eqToHom e ≫ G'.map k) ≫ g' = g) :
    θ ⋙ hs.overLift G' g' = ht.overLift G g := by
  subst hG hg
  refine Functor.ext (fun x ↦ ?_) (fun x y f ↦ ?_)
  · simp only [Functor.comp_obj, overLift, Functor.comp_map, eqToHom_refl, Category.id_comp,
      ← Category.assoc, ← G'.map_comp]
    rw [hs.hom_ext (θ.map (ht.from x) ≫ k) (hs.from _)]
  · ext
    rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left]
    exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

end Limits.IsTerminal

namespace Over

def mkIdIsTerminal (X : C) : IsTerminal (Over.mk (𝟙 X)) :=
  IsTerminal.ofUniqueHom (fun f ↦ Over.homMk f.hom) (fun f m ↦ by
    ext
    simpa using Over.w m)

@[simp]
theorem mkIdIsTerminal_from {X : C} (f : Over X) : (mkIdIsTerminal X).from f = Over.homMk f.hom :=
  rfl

theorem eqToHom_comp_map_comp_eqToHom_comp_hom (θ : I ⥤ J) {G : I ⥤ Over c} {G' : J ⥤ Over c}
    (hG : θ ⋙ G' = G) {H : I ⥤ C} {H' : J ⥤ C} (hH : H = G ⋙ Over.forget c)
    (hH' : H' = G' ⋙ Over.forget c) {x : I} {y : J} (e : H.obj x = H'.obj (θ.obj x))
    (k : θ.obj x ⟶ y) :
    (eqToHom e ≫ H'.map k) ≫ eqToHom (congrArg (fun K : J ⥤ C ↦ K.obj y) hH') ≫
        (G'.obj y).hom =
      eqToHom (congrArg (fun K : I ⥤ C ↦ K.obj x) hH) ≫ (G.obj x).hom := by
  subst hG hH hH'
  change (𝟙 _ ≫ (G'.map k).left) ≫ 𝟙 _ ≫ (G'.obj y).hom = 𝟙 _ ≫ (G'.obj (θ.obj x)).hom
  rw [Category.id_comp, Category.id_comp, Category.id_comp, Over.w]

theorem iteratedSliceForward_comp_iteratedSliceBackward (f : Over c) :
    iteratedSliceForward f ⋙ iteratedSliceBackward f = 𝟭 (Over f) := by
  have key : ∀ (l : C) (k : l ⟶ f.left) (h : l ⟶ c) (hw : k ≫ f.hom = h),
      Over.mk (Over.homMk k : Over.mk (k ≫ f.hom) ⟶ f) =
        Over.mk (Over.homMk k hw : Over.mk h ⟶ f) := by
    rintro l k h rfl
    rfl
  have hobj : ∀ α : Over f, (iteratedSliceForward f ⋙ iteratedSliceBackward f).obj α =
      (𝟭 (Over f)).obj α := fun α =>
    key α.left.left α.hom.left α.left.hom (Over.w α.hom)
  refine Functor.ext hobj (fun α β g => ?_)
  ext
  simp only [Over.comp_left, Over.eqToHom_left]
  exact (Category.comp_id _).symm.trans (Category.id_comp _).symm

section Small

universe u

variable {A : Type u} [SmallCategory A]

theorem map_obj_mk {a b c : A} (f : a ⟶ b) (g : b ⟶ c) :
    (Over.map g).obj (Over.mk f) = Over.mk (f ≫ g) :=
  rfl

theorem map_hom_obj_mk_id {a : A} (f : Over a) :
    (Over.map f.hom).obj (Over.mk (𝟙 f.left)) = f := by
  rw [map_obj_mk, Category.id_comp]
  rfl

end Small

end Over

namespace Under

@[simps!]
def iteratedSliceBackward (f : Under c) : Under f.right ⥤ Under f where
  obj g := Under.mk (Y := Under.mk (f.hom ≫ g.hom)) (Under.homMk g.hom)
  map φ := Under.homMk (Under.homMk φ.right (by simp)) (by ext; simp)

theorem post_forget_comp_iteratedSliceBackward (f : Under c) :
    Under.post (X := f) (Under.forget c) ⋙ iteratedSliceBackward f = 𝟭 (Under f) := by
  refine Functor.ext (fun k => ?_) (fun k k' φ => ?_)
  · refine StructuredArrow.obj_ext _ _
      (StructuredArrow.obj_ext _ _ rfl ((Category.comp_id (f.hom ≫ k.hom.right)).trans
        (Under.w k.hom))) ?_
    ext
    simp only [Functor.id_map, Under.comp_right, Under.eqToHom_right]
    exact Category.comp_id k.hom.right
  · ext
    simp only [Functor.id_map, Under.comp_right, Under.eqToHom_right]
    exact ((Category.id_comp (φ.right.right ≫ 𝟙 _)).trans (Category.comp_id φ.right.right)).symm

theorem iteratedSliceBackward_comp_post_forget (f : Under c) :
    iteratedSliceBackward f ⋙ Under.post (X := f) (Under.forget c) = 𝟭 (Under f.right) :=
  rfl

end Under

namespace Functor

class IsParametricRightAdjoint {C : Type u₁} [Category.{v₁} C] {E : Type u₂}
    [Category.{v₂} E] (F : C ⥤ E) : Prop where
  isRightAdjoint_post (X : C) : (Over.post (X := X) F).IsRightAdjoint

end Functor

end CategoryTheory

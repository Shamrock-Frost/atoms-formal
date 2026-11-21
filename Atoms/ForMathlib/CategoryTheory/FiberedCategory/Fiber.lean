import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.FiberedCategory.Fiber

namespace CategoryTheory.Functor.Fiber

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

section Basic

variable {𝒳 : Type u₁} [Category.{v₁} 𝒳] {𝒮 : Type u₂} [Category.{v₂} 𝒮] {p : 𝒳 ⥤ 𝒮} {S : 𝒮}

theorem obj_fiberInclusion_obj (a : Fiber p S) : p.obj (fiberInclusion.obj a) = S :=
  a.2

theorem map_fiberInclusion_map {a b : Fiber p S} (φ : a ⟶ b) :
    p.map (fiberInclusion.map φ) =
      eqToHom ((obj_fiberInclusion_obj a).trans (obj_fiberInclusion_obj b).symm) := by
  rw [IsHomLift.fac' p (𝟙 S) (fiberInclusion.map φ)]
  simp

end Basic

section Slice

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

@[simps!]
def toCostructuredArrow (u : A ⥤ B) (b : B) : Fiber u b ⥤ CostructuredArrow u b where
  obj a := CostructuredArrow.mk (Y := fiberInclusion.obj a) (eqToHom (obj_fiberInclusion_obj a))
  map φ := CostructuredArrow.homMk (fiberInclusion.map φ) (by simp [map_fiberInclusion_map])

variable {u : A ⥤ B} {a : A} {y : Under (u.obj a)}

theorem obj_right_fiberInclusion_obj_underPost (z : Fiber (Under.post u) y) :
    u.obj (fiberInclusion.obj z).right = y.right :=
  congrArg Under.right (obj_fiberInclusion_obj z)

theorem map_hom_fiberInclusion_obj_underPost (z : Fiber (Under.post u) y) :
    u.map (fiberInclusion.obj z).hom ≫ eqToHom (obj_right_fiberInclusion_obj_underPost z) =
      y.hom := by
  have := Under.w (eqToHom (obj_fiberInclusion_obj z))
  rw [Under.eqToHom_right] at this
  exact this

theorem map_right_fiberInclusion_map_underPost {z z' : Fiber (Under.post u) y} (ψ : z ⟶ z') :
    u.map (fiberInclusion.map ψ).right = eqToHom ((obj_right_fiberInclusion_obj_underPost z).trans
      (obj_right_fiberInclusion_obj_underPost z').symm) := by
  have := congrArg Under.Hom.right (map_fiberInclusion_map ψ)
  rw [Under.eqToHom_right] at this
  exact this

instance isHomLift_right_fiberInclusion_map_underPost {z z' : Fiber (Under.post u) y}
    (ψ : z ⟶ z') : u.IsHomLift (𝟙 y.right) (fiberInclusion.map ψ).right :=
  IsHomLift.of_fac _ _ _ (obj_right_fiberInclusion_obj_underPost z)
    (obj_right_fiberInclusion_obj_underPost z')
    (by rw [map_right_fiberInclusion_map_underPost ψ]; simp)

theorem isHomLift_underPost_of_isHomLift_right {z z' : Fiber (Under.post u) y}
    (k : fiberInclusion.obj z ⟶ fiberInclusion.obj z') [u.IsHomLift (𝟙 y.right) k.right] :
    (Under.post u).IsHomLift (𝟙 y) k := by
  have hk : (Under.post u).map k =
      eqToHom ((obj_fiberInclusion_obj z).trans (obj_fiberInclusion_obj z').symm) := by
    ext
    rw [Under.eqToHom_right]
    exact (IsHomLift.fac' u (𝟙 y.right) k.right).trans
      (by simp only [Category.id_comp, eqToHom_trans]; rfl)
  exact IsHomLift.of_fac' _ _ _ (obj_fiberInclusion_obj z) (obj_fiberInclusion_obj z')
    (by rw [hk]; simp)

variable (u y) in
def underPostToStructuredArrow :
    Fiber (Under.post (X := a) u) y ⥤
      StructuredArrow (CostructuredArrow.mk y.hom) (toCostructuredArrow u y.right) where
  obj z := StructuredArrow.mk (Y := Fiber.mk (obj_right_fiberInclusion_obj_underPost z))
    (CostructuredArrow.homMk (fiberInclusion.obj z).hom (map_hom_fiberInclusion_obj_underPost z))
  map ψ := StructuredArrow.homMk (Fiber.homMk u y.right (fiberInclusion.map ψ).right) (by
    ext
    exact Under.w (fiberInclusion.map ψ))

instance isEquivalence_underPostToStructuredArrow :
    (underPostToStructuredArrow u y).IsEquivalence where
  faithful := ⟨fun {_ _} _ _ h => Fiber.hom_ext (Under.UnderMorphism.ext
    (congrArg (fun φ => fiberInclusion.map (CommaMorphism.right φ)) h))⟩
  full := ⟨fun {z z'} φ => by
    let k : fiberInclusion.obj z ⟶ fiberInclusion.obj z' :=
      Under.homMk (fiberInclusion.map φ.right) (congrArg CommaMorphism.left (StructuredArrow.w φ))
    have : u.IsHomLift (𝟙 y.right) k.right :=
      inferInstanceAs (u.IsHomLift (𝟙 y.right) (fiberInclusion.map φ.right))
    have := isHomLift_underPost_of_isHomLift_right k
    exact ⟨Fiber.homMk (Under.post u) y k, rfl⟩⟩
  essSurj := ⟨fun s => by
    have h : (Under.post u).obj (Under.mk s.hom.left) = y := by
      refine StructuredArrow.obj_ext _ _ (obj_fiberInclusion_obj s.right) ?_
      have := CostructuredArrow.w s.hom
      simp only [toCostructuredArrow_obj_hom, CostructuredArrow.mk_hom_eq_self] at this
      exact this
    exact ⟨Fiber.mk h, ⟨Iso.refl _⟩⟩⟩

end Slice

section Square

variable {A' : Type u₁} [Category.{v₁} A'] {A : Type u₂} [Category.{v₂} A]
  {B' : Type u₃} [Category.{v₃} B'] {B : Type u₄} [Category.{v₄} B]

def mapOfSquare (w : A' ⥤ A) (u' : A' ⥤ B') (u : A ⥤ B) (v : B' ⥤ B) (h : w ⋙ u = u' ⋙ v)
    (b' : B') : Fiber u' b' ⥤ Fiber u (v.obj b') :=
  inducedFunctor (F := fiberInclusion ⋙ w) (by
    rw [Functor.assoc, h, ← Functor.assoc, fiberInclusion_comp_eq_const]
    exact Functor.ext (fun _ => rfl) (fun _ _ _ => by simp))

variable (w : A' ⥤ A) (u' : A' ⥤ B') (u : A ⥤ B) (v : B' ⥤ B) (h : w ⋙ u = u' ⋙ v) (b' : B')

@[simp]
theorem fiberInclusion_obj_mapOfSquare_obj (a : Fiber u' b') :
    fiberInclusion.obj ((mapOfSquare w u' u v h b').obj a) = w.obj (fiberInclusion.obj a) :=
  rfl

@[simp]
theorem fiberInclusion_map_mapOfSquare_map {a₁ a₂ : Fiber u' b'} (φ : a₁ ⟶ a₂) :
    fiberInclusion.map ((mapOfSquare w u' u v h b').map φ) = w.map (fiberInclusion.map φ) :=
  rfl

end Square

end CategoryTheory.Functor.Fiber

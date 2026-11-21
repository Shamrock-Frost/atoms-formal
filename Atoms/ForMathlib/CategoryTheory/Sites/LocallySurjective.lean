import Mathlib.CategoryTheory.Comma.Over.Pullback
import Mathlib.CategoryTheory.Sites.LocallySurjective

universe w v u

namespace CategoryTheory

open Opposite Limits

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

theorem Presheaf.isLocallySurjective_of_isPullback
    {B' A' B A : Cᵒᵖ ⥤ Type w} {t : B' ⟶ B} {l : B' ⟶ A'} {r : B ⟶ A} {b : A' ⟶ A}
    (h : IsPullback t l r b) [Presheaf.IsLocallySurjective J r] :
    Presheaf.IsLocallySurjective J l where
  imageSieve_mem {c} a := by
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J r (b.app (op c) a))
    rintro d f ⟨x, hx⟩
    obtain ⟨y, -, hy⟩ := Types.exists_of_isPullback (h.map ((evaluation Cᵒᵖ (Type w)).obj (op d)))
      x (A'.map f.op a) (hx.trans (NatTrans.naturality_apply b f.op a).symm)
    exact ⟨y, hy⟩

instance Presheaf.isLocallySurjective_pullback_map_left {X Y : Cᵒᵖ ⥤ Type w} (f : X ⟶ Y)
    {W₀ W : Over Y} (i : W₀ ⟶ W) [Presheaf.IsLocallySurjective J i.left] :
    Presheaf.IsLocallySurjective J ((Over.pullback f).map i).left := by
  have s : IsPullback (pullback.snd W₀.hom f) (pullback.fst W₀.hom f) f (i.left ≫ W.hom) := by
    rw [Over.w i]
    exact (IsPullback.of_hasPullback W₀.hom f).flip
  exact isLocallySurjective_of_isPullback (IsPullback.of_right (h₁₂ := pullback.snd W.hom f)
    (by simpa only [Over.pullback_map_left, pullback.lift_snd] using s)
    (by simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback W.hom f).flip).flip

theorem Presieve.IsSeparated.hom_ext {P A B : Cᵒᵖ ⥤ Type w} (hP : IsSeparated J P) (m : B ⟶ A)
    [Presheaf.IsLocallySurjective J m] {u v : A ⟶ P} (h : m ≫ u = m ≫ v) : u = v := by
  ext c a
  refine (hP _ (Presheaf.imageSieve_mem J m a)).ext ?_
  rintro d f ⟨t, ht⟩
  change P.map f.op (u.app c a) = P.map f.op (v.app c a)
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply, ← ht]
  exact congrArg (fun φ : B ⟶ P => φ.app (op d) t) h

end CategoryTheory

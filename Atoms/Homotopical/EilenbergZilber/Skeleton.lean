import Atoms.ForMathlib.CategoryTheory.Subfunctor.Union
import Atoms.Homotopical.EilenbergZilber.Lemma

open CategoryTheory Limits Opposite

namespace Atoms.Homotopical.EZCategory

universe w v u

section Skeleton

variable {A : Type u} [Category.{v} A] [EZCategory A]

def skeletonSubfunctor (n : ℕ) (X : Aᵒᵖ ⥤ Type w) : Subfunctor X where
  obj a := {x | ∃ (b : A) (f : a.unop ⟶ b) (y : X.obj (op b)), deg b ≤ n ∧ X.map f.op y = x}
  map {a a'} g := by
    rintro _ ⟨b, f, y, hb, rfl⟩
    exact ⟨b, g.unop ≫ f, y, hb, by rw [op_comp, Functor.map_comp_apply, Quiver.Hom.op_unop]⟩

variable {n : ℕ} {X : Aᵒᵖ ⥤ Type w}

theorem mem_skeletonSubfunctor_iff {a : A} (x : X.obj (op a)) :
    x ∈ (skeletonSubfunctor n X).obj (op a) ↔
      ∃ (b : A) (f : a ⟶ b) (y : X.obj (op b)), deg b ≤ n ∧ X.map f.op y = x :=
  Iff.rfl

theorem map_mem_skeletonSubfunctor {a b : A} (f : a ⟶ b) (y : X.obj (op b)) (hb : deg b ≤ n) :
    X.map f.op y ∈ (skeletonSubfunctor n X).obj (op a) :=
  ⟨b, f, y, hb, rfl⟩

theorem mem_skeletonSubfunctor_iff_of_isNondegenerate {a : A} {x : X.obj (op a)}
    (hx : IsNondegenerate X x) : x ∈ (skeletonSubfunctor n X).obj (op a) ↔ deg a ≤ n := by
  refine ⟨?_, fun h ↦ by simpa using map_mem_skeletonSubfunctor (𝟙 a) x h⟩
  rintro ⟨b, f, y, hb, rfl⟩
  obtain ⟨c, p, i, hp, hi, rfl⟩ := exists_factorization f
  have : IsIso p := hx p hp ⟨X.map i.op y, by rw [← Functor.map_comp_apply, ← op_comp]⟩
  exact (deg_eq_of_iso (asIso p)).trans_le ((deg_le_of_mono i hi).trans hb)

theorem map_mem_skeletonSubfunctor_iff_of_isSplitEpi {a b : A} (p : a ⟶ b) [IsSplitEpi p]
    (y : X.obj (op b)) :
    X.map p.op y ∈ (skeletonSubfunctor n X).obj (op a) ↔
      y ∈ (skeletonSubfunctor n X).obj (op b) := by
  refine ⟨fun h ↦ ?_, fun h ↦ (skeletonSubfunctor n X).map p.op h⟩
  have h' : X.map (section_ p).op (X.map p.op y) ∈ (skeletonSubfunctor n X).obj (op b) :=
    (skeletonSubfunctor n X).map (section_ p).op h
  rwa [← Functor.map_comp_apply, ← op_comp, IsSplitEpi.id, op_id, Functor.map_id_apply] at h'

theorem skeletonSubfunctor_monotone (X : Aᵒᵖ ⥤ Type w) :
    Monotone fun n : ℕ ↦ skeletonSubfunctor n X := by
  rintro m n hmn a _ ⟨b, f, y, hb, rfl⟩
  exact ⟨b, f, y, hb.trans hmn, rfl⟩

theorem iSup_skeletonSubfunctor (X : Aᵒᵖ ⥤ Type w) : ⨆ n : ℕ, skeletonSubfunctor n X = ⊤ := by
  refine eq_top_iff.2 fun a x _ ↦ ?_
  rw [Subfunctor.iSup_obj, Set.mem_iUnion]
  exact ⟨deg a.unop, by
    simpa using map_mem_skeletonSubfunctor (n := deg a.unop) (𝟙 a.unop) x le_rfl⟩

theorem range_skeletonSubfunctor_ι_comp_le {Y : Aᵒᵖ ⥤ Type w} (φ : X ⟶ Y) :
    Subfunctor.range ((skeletonSubfunctor n X).ι ≫ φ) ≤ skeletonSubfunctor n Y := by
  rintro a _ ⟨⟨_, b, f, y, hb, rfl⟩, rfl⟩
  exact ⟨b, f, φ.app _ y, hb, (NatTrans.naturality_apply φ f.op y).symm⟩

variable (n) in
@[simps]
def skeleton : (Aᵒᵖ ⥤ Type w) ⥤ (Aᵒᵖ ⥤ Type w) where
  obj X := (skeletonSubfunctor n X).toFunctor
  map φ := Subfunctor.lift _ (range_skeletonSubfunctor_ι_comp_le φ)

variable (A) in
@[simps]
def skeletonDiagram : ℕ ⥤ (Aᵒᵖ ⥤ Type w) ⥤ (Aᵒᵖ ⥤ Type w) where
  obj n := skeleton n
  map {m n} h :=
    { app X := Subfunctor.homOfLe (skeletonSubfunctor_monotone X (leOfHom h)) }

variable (A) in
@[simps]
def skeletonCocone : Cocone (skeletonDiagram.{w} A) where
  pt := 𝟭 _
  ι := { app n := { app X := (skeletonSubfunctor n X).ι } }

variable (A) in
noncomputable def isColimitSkeletonCocone : IsColimit (skeletonCocone.{w} A) :=
  evaluationJointlyReflectsColimits _ fun X ↦
    IsColimit.ofIsoColimit (isColimitOfPreserves (Subfunctor.toFunctorFunctor X)
      (Preorder.colimitCoconeOfIsLUB (skeletonSubfunctor_monotone X).functor (pt := ⊤)
        (by rw [← iSup_skeletonSubfunctor X]; exact isLUB_iSup)).isColimit)
      (Cocone.ext (@asIso _ _ _ _ (⊤ : Subfunctor X).ι
        ((Subfunctor.eq_top_iff_isIso _).1 rfl)))

end Skeleton

end Atoms.Homotopical.EZCategory

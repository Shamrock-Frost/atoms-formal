import Atoms.Diagrammatic.Vertex
import Atoms.ForMathlib.AlgebraicTopology.Quasicategory.FullSubcomplex

open CategoryTheory Opposite Simplicial Atoms.Shape

universe u

namespace Atoms.Diagrammatic

def DiagSet.fullSubpresheaf (X : DiagSet.{u}) (P : X.Vertex → Prop) : Subfunctor X where
  obj U := {x | ∀ v : atomPoint ⟶ U.unop, P (X.map v.op x)}
  map g x hx v := by
    have h := hx (v ≫ g.unop)
    rwa [op_comp, Quiver.Hom.op_unop, Functor.map_comp_apply] at h

theorem DiagSet.mem_fullSubpresheaf_iff (X : DiagSet.{u}) (P : X.Vertex → Prop)
    {U : Atom} (x : diagram X U) :
    x ∈ (X.fullSubpresheaf P).obj (op U) ↔
      ∀ v : atomPoint ⟶ U, P (X.map v.op x) := Iff.rfl

@[simp] theorem DiagSet.mem_fullSubpresheaf_vertex_iff (X : DiagSet.{u})
    (P : X.Vertex → Prop) (x : X.Vertex) :
    x ∈ (X.fullSubpresheaf P).obj (op atomPoint) ↔ P x := by
  constructor
  · intro h
    simpa using h (𝟙 atomPoint)
  · intro hx v
    have hv : v = 𝟙 atomPoint := isTerminalAtomPoint.hom_ext _ _
    simpa only [hv, op_id, Functor.map_id_apply] using hx

theorem DiagSet.hasLiftingProperty_fullSubpresheaf_ι {X A B : DiagSet.{u}}
    (P : X.Vertex → Prop) (j : A ⟶ B)
    (h : ∀ b : B ⟶ X, (∀ x : A.Vertex, P (b.app _ (j.app _ x))) →
      ∀ y : B.Vertex, P (b.app _ y)) :
    HasLiftingProperty j (X.fullSubpresheaf P).ι := by
  constructor
  intro a b sq
  have hb : ∀ y : B.Vertex, P (b.app _ y) := h b fun x => by
    have hx := (DiagSet.mem_fullSubpresheaf_vertex_iff X P _).1
      (a.app (op atomPoint) x).property
    have he := ConcreteCategory.congr_hom (NatTrans.congr_app sq.w (op atomPoint)) x
    exact he ▸ hx
  have hf : Subfunctor.range b ≤ X.fullSubpresheaf P := by
    intro U z hz
    obtain ⟨y, rfl⟩ := hz
    intro v
    rw [← NatTrans.naturality_apply]
    exact hb _
  exact CommSq.HasLift.mk' {
    l := Subfunctor.lift b hf
    fac_left := (cancel_mono (X.fullSubpresheaf P).ι).1
      ((Category.assoc _ _ _).trans ((congrArg (j ≫ ·) (Subfunctor.lift_ι b hf)).trans
        sq.w.symm))
    fac_right := Subfunctor.lift_ι b hf }

theorem DiagSet.hasLiftingProperty_fullSubpresheaf_ι_of_surjective {X A B : DiagSet.{u}}
    (P : X.Vertex → Prop) (j : A ⟶ B)
    (hj : Function.Surjective (j.app (op atomPoint))) :
    HasLiftingProperty j (X.fullSubpresheaf P).ι :=
  DiagSet.hasLiftingProperty_fullSubpresheaf_ι P j fun b hb y => by
    obtain ⟨x, rfl⟩ := hj y
    exact hb x

private theorem mem_fullSubpresheaf_iff_mem_fullSubcomplex (X : DiagSet.{u}) (P : X.Vertex → Prop)
    (n : SimplexCategoryᵒᵖ) (x : (DiagSet.toSSet.obj X).obj n) :
    x ∈ (X.fullSubpresheaf P).obj (simplexFunctor.op.obj n) ↔
      x ∈ ((DiagSet.toSSet.obj X).fullSubcomplex (fun v ↦ P (X.vertexEquivSSet.symm v))).obj n := by
  constructor
  · intro hx i
    exact hx (simplexFunctor.map (SimplexCategory.const ⦋0⦌ n.unop i))
  · intro hx f
    obtain ⟨g, hg⟩ := simplexFunctor.map_surjective
      (X := ⦋0⦌) (Y := n.unop) (atomSimplexZeroIsoPoint.hom ≫ f)
    have h : f = atomSimplexZeroIsoPoint.inv ≫ simplexFunctor.map g := by
      exact (Iso.eq_inv_comp atomSimplexZeroIsoPoint).2 hg.symm
    rw [h, SimplexCategory.eq_const_of_zero g]
    exact hx _

def DiagSet.toSSetFullSubpresheafIso (X : DiagSet.{u}) (P : X.Vertex → Prop) :
    DiagSet.toSSet.obj (X.fullSubpresheaf P).toFunctor ≅
      ((DiagSet.toSSet.obj X).fullSubcomplex (fun v ↦ P (X.vertexEquivSSet.symm v)) : SSet.{u}) :=
  NatIso.ofComponents (fun n ↦ Equiv.toIso
    { toFun := fun x ↦
        ⟨x.val, (mem_fullSubpresheaf_iff_mem_fullSubcomplex X P n x.val).1 x.property⟩
      invFun := fun x ↦
        ⟨x.val, (mem_fullSubpresheaf_iff_mem_fullSubcomplex X P n x.val).2 x.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }) (by intros; rfl)

theorem DiagSet.toSSetFullSubpresheafIso_hom_comp_ι (X : DiagSet.{u}) (P : X.Vertex → Prop) :
    (DiagSet.toSSetFullSubpresheafIso X P).hom ≫
        ((DiagSet.toSSet.obj X).fullSubcomplex (fun v ↦ P (X.vertexEquivSSet.symm v))).ι =
      DiagSet.toSSet.map (X.fullSubpresheaf P).ι := rfl

end Atoms.Diagrammatic

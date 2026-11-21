import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.AlgebraicTopology.SimplicialSet.CategoryWithFibrations
import Mathlib.AlgebraicTopology.SimplicialSet.PiZero
import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
import Mathlib.CategoryTheory.Adjunction.Limits

open CategoryTheory Limits Simplicial HomotopicalAlgebra Opposite MorphismProperty

universe u

namespace SSet

open SimplexCategory in
private theorem toPt_comp {m m' : SimplexCategory} (θ : m' ⟶ m) :
    θ ≫ SimplexCategory.const m ⦋0⦌ 0 = SimplexCategory.const m' ⦋0⦌ 0 := by
  ext i
  exact congrArg Fin.val (Subsingleton.elim (α := Fin 1) _ _)

private noncomputable def boundaryOneApp (X : SSet.{u}) (a b : X _⦋0⦌) (m : SimplexCategoryᵒᵖ)
    (s : (∂Δ[1] : SSet.{u}).obj m) : X.obj m :=
  X.map (SimplexCategory.const m.unop ⦋0⦌ 0).op
    (if stdSimplex.asOrderHom s.1 0 = 0 then a else b)

private theorem boundary_const {m : SimplexCategoryᵒᵖ} (s : (∂Δ[1] : SSet.{u}).obj m)
    (i j : Fin (m.unop.len + 1)) : stdSimplex.asOrderHom s.1 i = stdSimplex.asOrderHom s.1 j := by
  by_contra h
  apply s.2
  intro k
  by_cases hk : k = stdSimplex.asOrderHom s.1 i
  · exact ⟨i, hk.symm⟩
  · refine ⟨j, ?_⟩
    have h1 := (stdSimplex.asOrderHom s.1 i).isLt
    have h2 := (stdSimplex.asOrderHom s.1 j).isLt
    have h3 := k.isLt
    rw [Fin.ext_iff] at h hk ⊢
    omega

private theorem asOrderHom_map_zero {m m' : SimplexCategoryᵒᵖ} (θ : m ⟶ m')
    (s : (∂Δ[1] : SSet.{u}).obj m) :
    stdSimplex.asOrderHom (((∂Δ[1] : SSet.{u}).map θ s).1) 0 = stdSimplex.asOrderHom s.1 0 :=
  boundary_const s _ _

private noncomputable def componentsBoundaryOneDesc (X : SSet.{u}) (a b : X _⦋0⦌) :
    (∂Δ[1] : SSet.{u}) ⟶ X where
  app m := TypeCat.ofHom (boundaryOneApp X a b m)
  naturality m m' θ := by
    ext s
    change boundaryOneApp X a b m' ((∂Δ[1] : SSet.{u}).map θ s) =
      X.map θ (boundaryOneApp X a b m s)
    have h := congrArg Quiver.Hom.op (toPt_comp θ.unop)
    rw [op_comp, Quiver.Hom.op_unop] at h
    rw [boundaryOneApp, boundaryOneApp, asOrderHom_map_zero, ← Functor.map_comp_apply, h]

private theorem const_zero_eq_id : SimplexCategory.const ⦋0⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ := by
  ext i
  exact congrArg Fin.val (Subsingleton.elim (α := Fin 1) _ _)

private theorem componentsBoundaryOneDesc_ι (X : SSet.{u}) (a b : X _⦋0⦌) (i : Fin 2) :
    yonedaEquiv (boundary.ι i ≫ componentsBoundaryOneDesc X a b) =
      if SimplexCategory.δ i 0 = 0 then a else b
    := by
  have h : stdSimplex.asOrderHom (yonedaEquiv (boundary.ι.{u} i : _ ⟶ (∂Δ[1] : SSet))).1 0 =
      SimplexCategory.δ i 0 := rfl
  rw [yonedaEquiv_comp]
  change boundaryOneApp X a b _ _ = _
  rw [boundaryOneApp, h]
  change X.map (SimplexCategory.const ⦋0⦌ ⦋0⦌ 0).op _ = _
  rw [const_zero_eq_id, op_id, CategoryTheory.Functor.map_id]
  rfl

theorem nonempty_edge_of_rlp_monomorphisms {A B : SSet.{u}} {g : A ⟶ B}
    (hg : (MorphismProperty.monomorphisms SSet.{u}).rlp g) {a b : A _⦋0⦌}
    (e : Edge (g.app _ a) (g.app _ b)) : Nonempty (Edge a b) := by
  have := hg (boundary.{u} 1).ι (MorphismProperty.monomorphisms.infer_property _)
  have sq : CommSq (componentsBoundaryOneDesc A a b)
      (boundary.{u} 1).ι g (yonedaEquiv.symm e.edge) :=
    ⟨boundary.hom_ext fun i => yonedaEquiv.injective (by
      rw [← Category.assoc, yonedaEquiv_comp, componentsBoundaryOneDesc_ι, boundary.ι_ι_assoc]
      change _ = yonedaEquiv (stdSimplex.map (SimplexCategory.δ i) ≫ yonedaEquiv.symm e.edge)
      rw [yonedaEquiv_symm_naturality_left, Equiv.apply_symm_apply]
      fin_cases i
      · rw [if_neg (by decide)]
        exact e.tgt_eq.symm
      · rw [if_pos (by decide)]
        exact e.src_eq.symm)⟩
  have := this.sq_hasLift sq
  have key (i : Fin 2) : A.map (SimplexCategory.δ i).op (yonedaEquiv sq.lift) =
      if SimplexCategory.δ i 0 = 0 then a else b := by
    rw [yonedaEquiv_naturality, ← componentsBoundaryOneDesc_ι]
    congr 1
    have h := congrArg (boundary.ι i ≫ ·) sq.fac_left
    simp only [← Category.assoc, boundary.ι_ι] at h
    exact h
  exact ⟨Edge.mk (yonedaEquiv sq.lift) ((key 1).trans (if_pos (by decide)))
    ((key 0).trans (if_neg (by decide)))⟩

private theorem exists_app_eq_of_rlp_monomorphisms {A B : SSet.{u}} {g : A ⟶ B}
    (hg : (MorphismProperty.monomorphisms SSet.{u}).rlp g) (b : B _⦋0⦌) :
    ∃ a : A _⦋0⦌, g.app _ a = b := by
  let i := (⊥ : (Δ[0] : SSet.{u}).Subcomplex).ι
  have := hg i (MorphismProperty.monomorphisms.infer_property i)
  have sq : CommSq (Subcomplex.isInitialBot.to A) i g (yonedaEquiv.symm b) :=
    ⟨Subcomplex.isInitialBot.hom_ext _ _⟩
  exact ⟨yonedaEquiv sq.lift, by rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]⟩

theorem bijective_mapπ₀_of_rlp_monomorphisms {A B : SSet.{u}} {g : A ⟶ B}
    (hg : (MorphismProperty.monomorphisms SSet.{u}).rlp g) : Function.Bijective (mapπ₀ g) := by
  have hs := exists_app_eq_of_rlp_monomorphisms hg
  have key : ∀ u v : B _⦋0⦌, Relation.EqvGen π₀Rel u v → ∀ a b : A _⦋0⦌, g.app _ a = u →
      g.app _ b = v → π₀.mk a = π₀.mk b := by
    intro u v h
    induction h with
    | rel u v huv =>
      rintro a b rfl rfl
      obtain ⟨e⟩ := huv
      obtain ⟨e'⟩ := nonempty_edge_of_rlp_monomorphisms hg e
      exact π₀.sound e'
    | refl u =>
      rintro a b rfl hb
      have e : Edge (g.app _ a) (g.app _ b) := by
        rw [hb]
        exact Edge.id _
      obtain ⟨e'⟩ := nonempty_edge_of_rlp_monomorphisms hg e
      exact π₀.sound e'
    | symm u v _ ih => exact fun a b ha hb => (ih b a hb ha).symm
    | trans u v w _ _ ih₁ ih₂ =>
      intro a b ha hb
      obtain ⟨c, hc⟩ := hs v
      exact (ih₁ a c ha hc).trans (ih₂ c b hc hb)
  refine ⟨fun p q hpq => ?_, fun q => ?_⟩
  · obtain ⟨a, rfl⟩ := π₀.mk_surjective p
    obtain ⟨b, rfl⟩ := π₀.mk_surjective q
    rw [mapπ₀_mk, mapπ₀_mk] at hpq
    have h : Relation.EqvGen (π₀Rel (X := B)) (g.app _ a) (g.app _ b) := (π₀.mk_eq_mk_iff _ _).1 hpq
    exact key _ _ h a b rfl rfl
  · obtain ⟨b, rfl⟩ := π₀.mk_surjective q
    obtain ⟨a, rfl⟩ := hs b
    exact ⟨π₀.mk a, mapπ₀_mk g a⟩

instance preservesColimits_π₀Functor : PreservesColimitsOfSize.{u, u} π₀Functor.{u} := by
  let D := parallelPair
    (SSet.evaluation.{u}.map (SimplexCategory.δ (1 : Fin 2)).op)
    (SSet.evaluation.map (SimplexCategory.δ (0 : Fin 2)).op)
  have : PreservesColimitsOfSize.{u, u} D.flip :=
    preservesColimits_of_evaluation _ fun j => by
      cases j <;> exact inferInstanceAs
        (PreservesColimitsOfSize.{u, u} (SSet.evaluation.obj _))
  have : PreservesColimitsOfSize.{u, u} (colim : (WalkingParallelPair ⥤ Type u) ⥤ Type u) :=
    colimConstAdj.leftAdjoint_preservesColimits
  exact preservesColimits_of_natIso
    ((colimitIsoFlipCompColim D).symm ≪≫
      (colimit.isColimit D).coconePointUniqueUpToIso isColimitCoforkπ₀Functor)

end SSet

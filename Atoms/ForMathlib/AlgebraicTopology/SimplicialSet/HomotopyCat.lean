import Mathlib.AlgebraicTopology.SimplicialSet.HomotopyCat
import Mathlib.AlgebraicTopology.SimplicialSet.Op

open CategoryTheory Simplicial

universe u

namespace SSet.Truncated.HomotopyCategory

theorem functor_ext_of_arrowMk {S : SSet} {D : Type*} [Category* D]
    {F G : SSet.Truncated.HomotopyCategory ((SSet.truncation 2).obj S) ⥤ D}
    (h : ∀ ⦃x y : S _⦋0⦌⦄ (e : SSet.Edge x y),
      Arrow.mk (F.map (homMk e.toTruncated)) = Arrow.mk (G.map (homMk e.toTruncated))) :
    F = G := by
  refine functor_ext (fun x => congrArg Arrow.left (h (SSet.Edge.id (X := S) x)))
    fun x y e => ?_
  obtain ⟨_, _, he⟩ := (Arrow.mk_eq_mk_iff _ _).1 (h (SSet.Edge.ofTruncated e))
  exact he

variable {X : SSet.{u}}

private def edgeUnop {x y : X.op _⦋0⦌} (e : SSet.Edge x y) :
    SSet.Edge (opObjEquiv y) (opObjEquiv x) :=
  SSet.Edge.mk (opObjEquiv e.edge)
    (by rw [δ_opObjEquiv]; exact congrArg opObjEquiv e.tgt_eq)
    (by rw [δ_opObjEquiv]; exact congrArg opObjEquiv e.src_eq)

private def edgeOp {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    SSet.Edge (X := X.op) (opObjEquiv.symm y) (opObjEquiv.symm x) :=
  SSet.Edge.mk (opObjEquiv.symm e.edge)
    (by rw [op_δ]; exact congrArg opObjEquiv.symm e.tgt_eq)
    (by rw [op_δ]; exact congrArg opObjEquiv.symm e.src_eq)

private def compStructUnop {x₀ x₁ x₂ : X.op _⦋0⦌} {e₀₁ : SSet.Edge x₀ x₁}
    {e₁₂ : SSet.Edge x₁ x₂} {e₀₂ : SSet.Edge x₀ x₂} (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    SSet.Edge.CompStruct (edgeUnop e₁₂) (edgeUnop e₀₁) (edgeUnop e₀₂) :=
  SSet.Edge.CompStruct.mk (opObjEquiv h.simplex)
    (by rw [δ_opObjEquiv]; exact congrArg opObjEquiv h.d₀)
    (by rw [δ_opObjEquiv]; exact congrArg opObjEquiv h.d₂)
    (by rw [δ_opObjEquiv]; exact congrArg opObjEquiv h.d₁)

private def compStructOp {x₀ x₁ x₂ : X _⦋0⦌} {e₀₁ : SSet.Edge x₀ x₁}
    {e₁₂ : SSet.Edge x₁ x₂} {e₀₂ : SSet.Edge x₀ x₂} (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    SSet.Edge.CompStruct (edgeOp e₁₂) (edgeOp e₀₁) (edgeOp e₀₂) :=
  SSet.Edge.CompStruct.mk (opObjEquiv.symm h.simplex)
    (by rw [op_δ]; exact congrArg opObjEquiv.symm h.d₀)
    (by rw [op_δ]; exact congrArg opObjEquiv.symm h.d₂)
    (by rw [op_δ]; exact congrArg opObjEquiv.symm h.d₁)

private noncomputable def opFunctorHo :
    HomotopyCategory ((SSet.truncation 2).obj X.op) ⥤
      (HomotopyCategory ((SSet.truncation 2).obj X))ᵒᵖ :=
  lift (fun x ↦ Opposite.op (mk (V := (SSet.truncation 2).obj X)
      (opObjEquiv (X := X) (n := Opposite.op ⦋0⦌) x)))
    (fun e ↦ (homMk (edgeUnop (X := X) (SSet.Edge.ofTruncated (X := X.op) e)).toTruncated).op)
    (fun (x : X.op _⦋0⦌) ↦ by
      have h : edgeUnop (SSet.Edge.id x) = SSet.Edge.id (opObjEquiv x) :=
        SSet.Edge.ext (by rw [SSet.Edge.id_edge, σ_opObjEquiv]; rfl)
      refine (congrArg (fun e ↦ (homMk e.toTruncated).op) h).trans ?_
      rw [SSet.Edge.toTruncated_id]
      exact congrArg Quiver.Hom.op (homMk_id (V := (SSet.truncation 2).obj X) (opObjEquiv x)))
    (fun h ↦ by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op
        (homMk_comp_homMk (compStructUnop (X := X)
          (SSet.Edge.CompStruct.ofTruncated (X := X.op) h)).toTruncated))

private noncomputable def opFunctorHoInv :
    HomotopyCategory ((SSet.truncation 2).obj X) ⥤
      (HomotopyCategory ((SSet.truncation 2).obj X.op))ᵒᵖ :=
  lift (fun x ↦ Opposite.op (mk (V := (SSet.truncation 2).obj X.op)
      ((opObjEquiv (X := X) (n := Opposite.op ⦋0⦌)).symm x)))
    (fun e ↦ (homMk (edgeOp (X := X) (SSet.Edge.ofTruncated (X := X) e)).toTruncated).op)
    (fun (x : X _⦋0⦌) ↦ by
      have h : edgeOp (SSet.Edge.id x) = SSet.Edge.id (X := X.op) (opObjEquiv.symm x) :=
        SSet.Edge.ext (by rw [SSet.Edge.id_edge, op_σ]; rfl)
      refine (congrArg (fun e ↦ (homMk e.toTruncated).op) h).trans ?_
      rw [SSet.Edge.toTruncated_id]
      exact congrArg Quiver.Hom.op
        (homMk_id (V := (SSet.truncation 2).obj X.op) (opObjEquiv.symm x)))
    (fun h ↦ by
      rw [← op_comp]
      exact congrArg Quiver.Hom.op
        (homMk_comp_homMk (compStructOp (X := X)
          (SSet.Edge.CompStruct.ofTruncated (X := X) h)).toTruncated))

private lemma opFunctorHo_map_homMk {x y : X.op _⦋0⦌} (e : SSet.Edge x y) :
    opFunctorHo.map (homMk e.toTruncated) = (homMk (edgeUnop e).toTruncated).op :=
  Category.id_comp _

private lemma opFunctorHoInv_map_homMk {x y : X _⦋0⦌} (e : SSet.Edge x y) :
    opFunctorHoInv.map (homMk e.toTruncated) = (homMk (edgeOp e).toTruncated).op :=
  Category.id_comp _

private lemma opFunctorHo_comp_leftOp :
    opFunctorHo (X := X) ⋙ (opFunctorHoInv (X := X)).leftOp = 𝟭 _ :=
  functor_ext_of_arrowMk fun _ _ e ↦ by
    have h : (opFunctorHo ⋙ opFunctorHoInv.leftOp).map (homMk e.toTruncated) =
        homMk (edgeOp (edgeUnop e)).toTruncated := by
      rw [Functor.comp_map, opFunctorHo_map_homMk]
      exact congrArg Quiver.Hom.unop (opFunctorHoInv_map_homMk (edgeUnop e))
    exact (congrArg Arrow.mk h).trans (congr_arrowMk_homMk _ _ rfl)

private lemma leftOp_comp_opFunctorHo :
    (opFunctorHoInv (X := X)).leftOp ⋙ opFunctorHo (X := X) = 𝟭 _ := by
  have h : ((opFunctorHoInv (X := X)).leftOp ⋙ opFunctorHo (X := X)).unop = 𝟭 _ :=
    functor_ext_of_arrowMk fun _ _ e ↦ by
      have h : (opFunctorHoInv.leftOp ⋙ opFunctorHo).unop.map (homMk e.toTruncated) =
          homMk (edgeUnop (edgeOp e)).toTruncated := by
        rw [Functor.unop_map, Functor.comp_map, Functor.leftOp_map, Quiver.Hom.unop_op,
          opFunctorHoInv_map_homMk]
        exact congrArg Quiver.Hom.unop (opFunctorHo_map_homMk (edgeOp e))
      exact (congrArg Arrow.mk h).trans (congr_arrowMk_homMk _ _ rfl)
  exact (congrArg Functor.op h).trans rfl

noncomputable def opEquivalence (X : SSet.{u}) :
    HomotopyCategory ((SSet.truncation 2).obj X.op) ≌
      (HomotopyCategory ((SSet.truncation 2).obj X))ᵒᵖ :=
  CategoryTheory.Equivalence.mk opFunctorHo (opFunctorHoInv (X := X)).leftOp
    (eqToIso opFunctorHo_comp_leftOp.symm) (eqToIso leftOp_comp_opFunctorHo)

@[simp]
theorem opEquivalence_functor_obj (X : SSet.{u}) (x : X.op _⦋0⦌) :
    (opEquivalence X).functor.obj (mk x) = Opposite.op (mk (opObjEquiv x)) :=
  rfl

theorem opEquivalence_functor_map_homMk {x y : X.op _⦋0⦌} (e : SSet.Edge x y)
    (e' : SSet.Edge (opObjEquiv y) (opObjEquiv x)) (h : e'.edge = opObjEquiv e.edge) :
    (opEquivalence X).functor.map (homMk e) = (homMk e').op := by
  obtain rfl : e' = edgeUnop e := SSet.Edge.ext h
  exact opFunctorHo_map_homMk e

end SSet.Truncated.HomotopyCategory

namespace SSet

def IsoVertices {X : SSet.{u}} (x y : X _⦋0⦌) : Prop :=
  Nonempty ((Truncated.HomotopyCategory.mk x : hoFunctor.obj X) ≅
    Truncated.HomotopyCategory.mk y)

theorem IsoVertices.symm {X : SSet.{u}} {x y : X _⦋0⦌} (h : IsoVertices x y) :
    IsoVertices y x :=
  ⟨h.some.symm⟩

theorem IsoVertices.trans {X : SSet.{u}} {x y z : X _⦋0⦌} (h : IsoVertices x y)
    (h' : IsoVertices y z) : IsoVertices x z :=
  ⟨h.some ≪≫ h'.some⟩

theorem IsoVertices.map {X Y : SSet.{u}} (f : X ⟶ Y) {x y : X _⦋0⦌} (h : IsoVertices x y) :
    IsoVertices (f.app _ x) (f.app _ y) :=
  ⟨(hoFunctor.map f).toFunctor.mapIso h.some⟩

end SSet

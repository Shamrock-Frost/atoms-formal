import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
import Atoms.ForMathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackObjObj
import Atoms.Diagrammatic.GrayTensor.HornModel
import Atoms.Diagrammatic.Marked.Horn
import Atoms.Diagrammatic.Marked.HornLike
import Atoms.Diagrammatic.Marked.GrayTensor
import Atoms.Shape.Rigidity

open CategoryTheory Limits Opposite Atoms.Shape Atoms.Molecule Atoms.Molecule.OGP
open Atoms.Homotopical (MarkedPresheaf)

universe u

namespace Atoms.Diagrammatic

theorem nonempty_arrowIso_of_forget {X Y X' Y' : MarkedDiagSet.{u}} (i : X ⟶ Y)
    (j : X' ⟶ Y')
    (hi : ∀ (V : Atom) (x : X.underlying.obj (op V)),
      (MarkedPresheaf.forget.map i).app (op V) x ∈ Y.marked V → x ∈ X.marked V)
    (hj : ∀ (V : Atom) (x : X'.underlying.obj (op V)),
      (MarkedPresheaf.forget.map j).app (op V) x ∈ Y'.marked V → x ∈ X'.marked V)
    (E : Arrow.mk (MarkedPresheaf.forget.map i) ≅ Arrow.mk (MarkedPresheaf.forget.map j))
    (hE : ∀ (V : Atom) (y : Y.underlying.obj (op V)),
      y ∈ Y.marked V ↔ E.hom.right.app (op V) y ∈ Y'.marked V) :
    Nonempty (Arrow.mk i ≅ Arrow.mk j) := by
  have hw (V : Atom) (x : X.underlying.obj (op V)) :
      E.hom.right.app (op V) ((MarkedPresheaf.forget.map i).app (op V) x) =
        (MarkedPresheaf.forget.map j).app (op V) (E.hom.left.app (op V) x) :=
    (congrFun (congrArg (fun φ => (NatTrans.app φ (op V) : _ → _)) E.hom.w) x).symm
  refine ⟨Arrow.isoMk (markedIsoMk (Arrow.leftFunc.mapIso E) fun V x => ⟨fun hx => ?_,
    fun hx => ?_⟩) (markedIsoMk (Arrow.rightFunc.mapIso E) hE) (MarkedPresheaf.hom_ext ?_)⟩
  · exact hj V _ ((hw V x) ▸ (hE V _).1 (MarkedPresheaf.map_mem_marked i hx))
  · exact hi V x ((hE V _).2 ((hw V x).symm ▸ MarkedPresheaf.map_mem_marked j hx))
  rw [Functor.map_comp, Functor.map_comp]
  exact E.hom.w

theorem iso_ball_ext {X : DiagSet.{u}} {W : Atom} (e₁ e₂ : X ≅ ball.{u} W) : e₁ = e₂ := by
  have h : uliftYoneda.{u}.preimageIso (e₁.symm ≪≫ e₂) = Iso.refl W := Atom.iso_eq _ _
  have h' : e₁.inv ≫ e₂.hom = 𝟙 _ := by
    rw [← uliftYoneda.{u}.map_preimage (e₁.inv ≫ e₂.hom)]
    exact (congrArg (fun e => uliftYoneda.{u}.map e.hom) h).trans (uliftYoneda.{u}.map_id W)
  exact Iso.ext (((Iso.inv_comp_eq e₁).1 h').trans (Category.comp_id _)).symm

theorem mem_marked_source_of_markedHornInclusion (m : MarkedHornData) {V : Atom}
    (x : m.source.underlying.obj (op V))
    (hx : (MarkedPresheaf.forget.map (markedHornInclusion.{u} m)).app (op V) x ∈
      m.target.marked V) :
    x ∈ m.source.marked V := by
  refine (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ?_
  rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hx with hd | ⟨a, ha, him, hd⟩
  · exact Or.inl (isDegenerate_of_isDegenerate_app (closedSubpresheaf m.atom m.hornSet).ι
      (isDegenerate_app (closedSubpresheafUnivIso m.atom).hom hd))
  · have hax : a ∈ m.hornSet := apply_top_eq_of_map_eq x.1.down him ▸ x.2 V.top
    refine Or.inr ⟨a, ?_, him, hd⟩
    rcases m.mem_targetMarking_iff.1 ha with rfl | ⟨-, rfl⟩ | ha
    · exact absurd rfl ((m.atom.mem_bdryFull_top_iff _).1 (m.mem_hornSet_iff.1 hax).1)
    · exact absurd rfl (m.mem_hornSet_iff.1 hax).2
    · exact ha

noncomputable def tensorBallIso (h : MarkedHornData) (V : Atom) :
    grayTensor h.target.underlying (ball.{u} V) ≅ ball.{u} (Atom.grayTensor h.atom V) :=
  ((Functor.curry.obj grayTensorBifunctor.{u}).mapIso (closedSubpresheafUnivIso h.atom)).app
    (ball V) ≪≫ grayTensorBallIso h.atom V

theorem tensorBallIso_hom_app (h : MarkedHornData) (V : Atom) {T A B : Atom}
    (f : T ⟶ Atom.grayTensor A B) (c : h.target.underlying.obj (op A))
    (d : (ball.{u} V).obj (op B)) :
    (tensorBallIso h V).hom.app (op T) ((grayTensor _ _).map f.op (grayTensorCell c d)) =
      ULift.up (f ≫ Atom.grayTensorMap c.1.down d.down) := by
  rw [NatTrans.naturality_apply]
  change (ball _).map f.op ((grayTensorBallIso h.atom V).hom.app _
    ((grayTensorBifunctor.map ((closedSubpresheafUnivIso h.atom).hom, 𝟙 (ball V))).app _
      (grayTensorCell c d))) = _
  have h1 := grayTensorCell_naturality (X := h.target.underlying) (X' := ball.{u} h.atom)
    (Y := ball.{u} V) (Y' := ball.{u} V) (closedSubpresheafUnivIso h.atom).hom (𝟙 _) c d
  exact (congrArg (fun z => (ball _).map f.op ((grayTensorBallIso h.atom V).hom.app _ z)) h1).trans
    (congrArg ((ball _).map f.op) (grayTensorBallIso_hom_app_grayTensorCell c.1.down d.down))

theorem nonempty_forget_arrowIso (pseudo : Bool) (h h' : MarkedHornData) (V : Atom)
    (hh' : h'.toHornData = h.toHornData.grayTensorRight V) {M : Set V.ogp}
    {hM : ∀ z ∈ M, 0 < grade ℕ z}
    (f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM)
    (hf₂ : MarkedPresheaf.forget.map f₂ = sphereInclusion V) :
    Nonempty (Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} pseudo)) (markedHornInclusion.{u} h) f₂).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u} h'))) := by
  have e₁ := Functor.PushoutObjObj.mapArrowIso (G₁ := MarkedPresheaf.forget)
    (G₂ := MarkedPresheaf.forget) (G₃ := MarkedPresheaf.forget)
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} pseudo))
      (markedHornInclusion.{u} h) f₂)
    (Functor.PushoutObjObj.ofHasPushout _ _ _)
    (F' := Functor.curry.obj grayTensorBifunctor.{u}) (Iso.refl _)
  rw [hf₂] at e₁
  have e₂ := Functor.PushoutObjObj.ι_iso_of_iso_left (f₂ := Arrow.mk (sphereInclusion.{u} V))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) h.forgetArrowIso
  obtain ⟨e₃⟩ := nonempty_arrowIso_pushoutProduct_hornInclusion_sphereInclusion.{u} h.toHornData V
  rw [← hh'] at e₃
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ h'.forgetArrowIso.symm⟩

end Atoms.Diagrammatic

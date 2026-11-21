import Atoms.Diagrammatic.Joyal.FaceNerveAtom
import Atoms.Diagrammatic.Marked.HornLike
import Atoms.Shape.Invertor

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Simplicial
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Order

universe u

namespace Atoms.Diagrammatic

open MarkedSSet.modelCategoryCartesian

section Cells

open Opposite

theorem isIso_forget_map_markedFaceNerve_map {X Y : MarkedDiagSet.{u}} (f : X ⟶ Y)
    [IsIso (MarkedPresheaf.forget.map f)] :
    IsIso (MarkedPresheaf.forget.map (markedFaceNerve.map f)) := by
  have : Mono f := (MarkedPresheaf.mono_iff f).2 inferInstance
  have : Epi f := MarkedPresheaf.forget.epi_of_epi_map inferInstance
  have : Mono (MarkedPresheaf.forget.map (markedFaceNerve.map f)) :=
    (MarkedPresheaf.mono_iff _).1 inferInstance
  exact isIso_of_mono_of_epi _

variable {X : MarkedDiagSet.{u}}

def siteCellHom {x : MarkedSite atomMarking} (s : X.obj.obj (op x)) :
    (MarkedPresheaf.yoneda atomMarking).obj x ⟶ X :=
  ObjectProperty.homMk (uliftYonedaEquiv.symm s)

noncomputable def markedFaceNerveCell {x : MarkedSite atomMarking} (s : X.obj.obj (op x)) :
    markedFaceNerveSite.obj x ⟶ markedFaceNerve.obj X :=
  (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).inv.app x ≫
    markedFaceNerve.map (siteCellHom s)

private theorem siteCellHom_map {x y : MarkedSite atomMarking} (g : x ⟶ y)
    (s : X.obj.obj (op y)) :
    siteCellHom (X.obj.map g.op s) =
      (MarkedPresheaf.yoneda atomMarking).map g ≫ siteCellHom s :=
  ObjectProperty.hom_ext _ ((uliftYonedaEquiv_symm_map g.op s).trans rfl)

theorem markedFaceNerveCell_map {x y : MarkedSite atomMarking} (g : x ⟶ y)
    (s : X.obj.obj (op y)) :
    markedFaceNerveCell (X.obj.map g.op s) =
      markedFaceNerveSite.map g ≫ markedFaceNerveCell s := by
  rw [markedFaceNerveCell, markedFaceNerveCell, siteCellHom_map, Functor.map_comp]
  have h := (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).inv.naturality g
  rw [Functor.comp_map] at h
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ markedFaceNerve.map (siteCellHom s)) h.symm).trans (Category.assoc _ _ _))

theorem markedFaceNerveCell_comp {Y : MarkedDiagSet.{u}} (f : X ⟶ Y) {x : MarkedSite atomMarking}
    (s : X.obj.obj (op x)) :
    markedFaceNerveCell (f.hom.app (op x) s) = markedFaceNerveCell s ≫ markedFaceNerve.map f := by
  have : siteCellHom (f.hom.app (op x) s) = siteCellHom s ≫ f :=
    ObjectProperty.hom_ext _ (uliftYonedaEquiv_symm_comp s f.hom).symm
  rw [markedFaceNerveCell, markedFaceNerveCell, this, Functor.map_comp]
  exact (Category.assoc _ _ _).symm

private theorem siteCellHom_yonedaEquiv {x : MarkedSite atomMarking}
    (φ : (MarkedPresheaf.yoneda atomMarking).obj x ⟶ X) :
    siteCellHom (uliftYonedaEquiv φ.hom) = φ :=
  ObjectProperty.hom_ext _ (uliftYonedaEquiv.symm_apply_apply φ.hom)

theorem mem_marked_markedFaceNerve {y : (markedFaceNerve.obj X).underlying _⦋1⦌}
    (hy : y ∈ (markedFaceNerve.obj X).marked ⦋1⦌) :
    (∃ (x : MarkedSite atomMarking) (s : X.obj.obj (op x)),
      ∃ e ∈ (markedFaceNerveSite.obj x).marked ⦋1⦌,
        (MarkedPresheaf.forget.map (markedFaceNerveCell s)).app _ e = y) ∨
      ∃ v, (markedFaceNerve.obj X).underlying.map (SimplexCategory.σ 0).op v = y := by
  have hc := isColimitOfPreserves markedFaceNerve ((MarkedPresheaf.yoneda atomMarking).denseAt X)
  rcases exists_mem_marked_of_isColimit hc hy with ⟨j, e, he, rfl⟩ | h
  · refine Or.inl ⟨j.left, uliftYonedaEquiv j.hom.hom, (MarkedPresheaf.forget.map
      ((MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.app j.left)).app _ e,
      MarkedPresheaf.map_mem_marked _ he, ?_⟩
    have h : MarkedPresheaf.forget.map
        ((MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).hom.app j.left) ≫
          MarkedPresheaf.forget.map (markedFaceNerveCell (uliftYonedaEquiv j.hom.hom)) =
        MarkedPresheaf.forget.map (markedFaceNerve.map j.hom) := by
      rw [markedFaceNerveCell, siteCellHom_yonedaEquiv, ← Functor.map_comp]
      exact congrArg MarkedPresheaf.forget.map (Iso.hom_inv_id_app_assoc
        (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite) j.left (markedFaceNerve.map j.hom))
    exact (congrArg (fun f => f.app _ e) h).trans rfl
  · exact Or.inr h

private theorem siteCellHom_unmarked {V : Shape.Atom} (c : X.underlying.obj (op V)) :
    siteCellHom (x := (MarkedSite.unmarked atomMarking).obj V) c =
      (MarkedPresheaf.yonedaCompFlatIso atomMarking).inv.app V ≫
        (MarkedPresheaf.flat atomMarking).map (uliftYonedaEquiv.symm c) ≫
          (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app X :=
  MarkedPresheaf.hom_ext (by
    ext ⟨W⟩ ⟨g⟩
    rfl)

private theorem yonedaCompFaceNerveIso_inv_app (V : Shape.Atom) :
    yonedaCompFaceNerveIso.{u}.inv.app V = unmarkedCompMarkedFaceNerveSiteIso.inv.app V ≫
      (MarkedPresheaf.yonedaCompExtendIso markedFaceNerveSite).inv.app
        ((MarkedSite.unmarked atomMarking).obj V) ≫
        markedFaceNerve.map ((MarkedPresheaf.yonedaCompFlatIso atomMarking).inv.app V) :=
  rfl

theorem markedFaceNerveCell_unmarked {V : Shape.Atom} (c : X.underlying.obj (op V)) :
    markedFaceNerveCell (x := (MarkedSite.unmarked atomMarking).obj V) c =
      unmarkedCompMarkedFaceNerveSiteIso.hom.app V ≫ yonedaCompFaceNerveIso.inv.app V ≫
        faceNerve.map (uliftYonedaEquiv.symm c) ≫
          markedFaceNerve.map ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app X) := by
  rw [markedFaceNerveCell, siteCellHom_unmarked, yonedaCompFaceNerveIso_inv_app,
    Functor.map_comp]
  refine (congrArg (fun k => _ ≫ _ ≫ k) (markedFaceNerve.map_comp _ _)).trans ?_
  exact MarkedPresheaf.hom_ext rfl

end Cells

section ClosedSubset

open Opposite

def outputRel (P : OGP.{0}) (a b : P) : Prop :=
  P.boundary (.Iic a) 0 true = P.boundary (.Iic b) 0 true

variable (P : RDCpx.{0}) (S : LowerSet P.obj.toOGP)

private theorem outputRel_restrict_iff (a b : P.obj.toOGP.restrict S) :
    outputRel (P.obj.toOGP.restrict S) a b ↔ outputRel P.obj.toOGP a.1 b.1 := by
  rw [outputRel, outputRel, ← (map_injective (incl S)).eq_iff, map_boundary, map_boundary,
    map_Iic, map_Iic]
  rfl

noncomputable def rdcFaceNerveRestrictIso :
    rdcFaceNerve.obj (P.restrict S) ≅ markedSubcomplex (edgeSet.{u} (outputRel P.obj.toOGP))
      (chainSubcomplex (S : Set P.obj.toOGP)) where
  hom := edgeHomMk
    { app _ := ↾fun σ => ⟨Monotone.functor (f := fun i => ULift.up (σ.obj i).down.1)
        fun _ _ h => (leOfHom (σ.map (homOfLE h)) :), fun i => (σ.obj i).down.2⟩
      naturality _ _ _ := by
        ext σ
        exact Subtype.ext (nerve.ext_of_isThin rfl) }
    fun e he => by
      obtain ⟨-, h | ⟨h, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 he
      · exact (mem_marked_markedSubcomplex_iff _ _).2
          (Or.inl ((outputRel_restrict_iff P S _ _).1 h))
      · exact absurd h (Set.notMem_empty _)
  inv := edgeHomMk
    { app _ := ↾fun σ => Monotone.functor
        (f := fun i => ULift.up (⟨(σ.1.obj i).down, σ.2 i⟩ : P.obj.toOGP.restrict S))
        fun _ _ h => (leOfHom (σ.1.map (homOfLE h)) :)
      naturality _ _ _ := by
        ext σ
        exact nerve.ext_of_isThin rfl }
    fun e he => by
      refine (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ⟨rfl, Or.inl ?_⟩
      rcases (mem_marked_markedSubcomplex_iff _ e).1 he with h | h
      · exact (outputRel_restrict_iff P S _ _).2 h
      · exact congrArg (fun a => (P.obj.toOGP.restrict S).boundary (.Iic a) 0 true)
          (Subtype.ext h)
  hom_inv_id := MarkedPresheaf.hom_ext (by
    ext n σ
    exact nerve.ext_of_isThin rfl)
  inv_hom_id := MarkedPresheaf.hom_ext (by
    ext n σ
    exact Subtype.ext (nerve.ext_of_isThin rfl))

private theorem rdcFaceNerve_map_inclusion_comp_hom {S' : LowerSet P.obj.toOGP} (h : S ≤ S') :
    rdcFaceNerve.{u}.map (RDCpx.inclusion P h) ≫ (rdcFaceNerveRestrictIso P S').hom =
      (rdcFaceNerveRestrictIso P S).hom ≫
        markedSubcomplexMap _ (chainSubcomplex_mono (LowerSet.coe_subset_coe.2 h)) :=
  MarkedPresheaf.hom_ext rfl

noncomputable def faceNerveClosedSubpresheafIso (U : Shape.Atom) (S : LowerSet U.ogp) :
    faceNerve.obj (closedSubpresheaf U S).toFunctor ≅
      markedSubcomplex (edgeSet.{u} (outputRel U.ogp)) (chainSubcomplex (S : Set U.ogp)) :=
  faceNerve.mapIso (closedSubpresheafRealizeIso U S).symm ≪≫
    realizeCompFaceNerveIso.app _ ≪≫ rdcFaceNerveRestrictIso U.rdc S

theorem faceNerve_map_comp_faceNerveClosedSubpresheafIso_hom (U : Shape.Atom)
    {S S' : LowerSet U.ogp} (h : S ≤ S') :
    faceNerve.{u}.map (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) ≫
        (faceNerveClosedSubpresheafIso U S').hom =
      (faceNerveClosedSubpresheafIso U S).hom ≫
        markedSubcomplexMap _ (chainSubcomplex_mono (LowerSet.coe_subset_coe.2 h)) := by
  have h₁ : Subfunctor.homOfLe (closedSubpresheaf_mono U h) ≫
      (closedSubpresheafRealizeIso U S').inv = (closedSubpresheafRealizeIso U S).inv ≫
        realize.map (RDCpx.inclusion U.rdc h) := by
    ext ⟨V⟩ f
    rfl
  have h₂ := realizeCompFaceNerveIso.hom.naturality (RDCpx.inclusion U.rdc h)
  rw [Functor.comp_map] at h₂
  have e (T : LowerSet U.ogp) :
      (faceNerveClosedSubpresheafIso U T).hom =
        faceNerve.map (closedSubpresheafRealizeIso U T).inv ≫
          realizeCompFaceNerveIso.hom.app _ ≫ (rdcFaceNerveRestrictIso U.rdc T).hom := rfl
  have h₃ := (faceNerve.map_comp _ _).symm.trans ((congrArg faceNerve.map h₁).trans
    (faceNerve.map_comp _ _))
  rw [e, e]
  calc _ = (faceNerve.map (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) ≫
        faceNerve.map (closedSubpresheafRealizeIso U S').inv) ≫
          realizeCompFaceNerveIso.hom.app _ ≫ (rdcFaceNerveRestrictIso U.rdc S').hom :=
        (Category.assoc _ _ _).symm
    _ = faceNerve.map (closedSubpresheafRealizeIso U S).inv ≫
        (faceNerve.map (realize.map (RDCpx.inclusion U.rdc h)) ≫
          realizeCompFaceNerveIso.hom.app _) ≫ (rdcFaceNerveRestrictIso U.rdc S').hom := by
        rw [h₃]
        simp only [Category.assoc]
    _ = _ := by
        rw [h₂]
        simp only [Category.assoc]
        exact congrArg (_ ≫ _ ≫ ·) (rdcFaceNerve_map_inclusion_comp_hom U.rdc S h)

theorem faceNerve_map_yonedaEquiv_symm_comp_faceNerveClosedSubpresheafIso_hom (U : Shape.Atom)
    {S : LowerSet U.ogp} {V : Shape.Atom} (c : (closedSubpresheaf.{u} U S).toFunctor.obj (op V)) :
    yonedaCompFaceNerveIso.inv.app V ≫ faceNerve.map (uliftYonedaEquiv.symm c) ≫
        (faceNerveClosedSubpresheafIso U S).hom =
      rdcFaceNerve.map (Shape.restrictLift U.rdc S (Shape.atomToRDCpx.map c.1.down) c.2) ≫
        (rdcFaceNerveRestrictIso U.rdc S).hom := by
  have h₁ : uliftYonedaEquiv.symm c ≫ (closedSubpresheafRealizeIso U S).inv =
      (uliftYonedaEquiv (F := realize.obj (U.toMoleculeShape.rdc.restrict S))).symm
        ⟨Shape.restrictLift U.rdc S (Shape.atomToRDCpx.map c.1.down) c.2⟩ :=
    (uliftYonedaEquiv_symm_comp c _).trans rfl
  have h₂ := faceNerve_map_comp_realizeCompFaceNerveIso_hom_app
    (Shape.restrictLift U.rdc S (Shape.atomToRDCpx.map c.1.down) c.2)
  have e : (faceNerveClosedSubpresheafIso U S).hom =
      faceNerve.map (closedSubpresheafRealizeIso U S).inv ≫
        realizeCompFaceNerveIso.hom.app _ ≫ (rdcFaceNerveRestrictIso U.rdc S).hom := rfl
  rw [e, ← h₂, ← h₁, faceNerve.map_comp]
  simp only [Category.assoc]

end ClosedSubset

section MarkedClosedSubset

open Opposite

variable (U : Shape.Atom) {S : LowerSet U.ogp} {A : Set U.ogp}
  (hA : ∀ a ∈ A, a ∈ S ∧ 0 < grade ℕ a)

private noncomputable def markedClosedSubsetCounit :
    faceNerve.{u}.obj (closedSubpresheaf U S).toFunctor ⟶
      markedFaceNerve.obj (markedClosedSubset U S A hA) :=
  markedFaceNerve.map ((MarkedPresheaf.flatForgetAdjunction atomMarking).counit.app
    (markedClosedSubset U S A hA))

private instance isIso_forget_map_markedClosedSubsetCounit :
    CategoryTheory.IsIso (MarkedPresheaf.forget.map (markedClosedSubsetCounit.{u} U hA)) := by
  have : CategoryTheory.IsIso (MarkedPresheaf.forget.map ((MarkedPresheaf.flatForgetAdjunction
      atomMarking).counit.app (markedClosedSubset U S A hA))) :=
    inferInstanceAs (CategoryTheory.IsIso (𝟙 _))
  exact @isIso_forget_map_markedFaceNerve_map _ _ _ this

private noncomputable def markedClosedSubsetIso :
    MarkedPresheaf.forget.obj (markedSubcomplex (edgeSet.{u} (outputRel U.ogp))
        (chainSubcomplex (S : Set U.ogp))) ≅
      MarkedPresheaf.forget.obj (markedFaceNerve.obj (markedClosedSubset U S A hA)) :=
  MarkedPresheaf.forget.mapIso (faceNerveClosedSubpresheafIso U S).symm ≪≫
    @asIso _ _ _ _ (MarkedPresheaf.forget.map (markedClosedSubsetCounit U hA))
      (isIso_forget_map_markedClosedSubsetCounit U hA)

private theorem forget_map_markedFaceNerveCell_comp_inv {V : Shape.Atom}
    (c : (markedClosedSubset.{u} U S A hA).underlying.obj (op V)) :
    MarkedPresheaf.forget.map
        (markedFaceNerveCell (x := (MarkedSite.unmarked atomMarking).obj V) c) ≫
        (markedClosedSubsetIso U hA).inv =
      MarkedPresheaf.forget.map (rdcFaceNerve.map (Shape.restrictLift
          U.rdc S (Shape.atomToRDCpx.map c.1.down) c.2) ≫
        (rdcFaceNerveRestrictIso U.rdc S).hom) := by
  have h := faceNerve_map_yonedaEquiv_symm_comp_faceNerveClosedSubpresheafIso_hom U c
  have h' : rdcFaceNerve.map (Shape.restrictLift U.rdc S (Shape.atomToRDCpx.map c.1.down) c.2) ≫
        (rdcFaceNerveRestrictIso U.rdc S).hom ≫ (faceNerveClosedSubpresheafIso U S).inv =
      yonedaCompFaceNerveIso.inv.app V ≫ faceNerve.map (uliftYonedaEquiv.symm c) := by
    exact (Category.assoc _ _ _).symm.trans
      ((Iso.comp_inv_eq _).2 (h.symm.trans (Category.assoc _ _ _).symm))
  refine (Iso.comp_inv_eq _).2 ?_
  have e : MarkedPresheaf.forget.map (markedFaceNerveCell
      (x := (MarkedSite.unmarked atomMarking).obj V) c) =
      MarkedPresheaf.forget.map (yonedaCompFaceNerveIso.inv.app V ≫
        faceNerve.map (uliftYonedaEquiv.symm c) ≫ markedClosedSubsetCounit U hA) := by
    rw [markedFaceNerveCell_unmarked, Functor.map_comp,
      forget_map_unmarkedCompMarkedFaceNerveSiteIso_hom_app]
    rfl
  exact e.trans ((congrArg MarkedPresheaf.forget.map ((Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ markedClosedSubsetCounit U hA) h'.symm))).trans rfl)

private theorem chain_edge_ext {T : Set U.ogp} {e e' : (chainSubcomplex.{u} T).toSSet _⦋1⦌}
    (h₀ : (e.1.obj 0).down = (e'.1.obj 0).down) (h₁ : (e.1.obj 1).down = (e'.1.obj 1).down) :
    e = e' := by
  refine Subtype.ext (nerve.ext_of_isThin (funext fun i => ULift.ext _ _ ?_))
  fin_cases i
  · exact h₀
  · exact h₁

theorem forget_map_markedFaceNerveCell_toSelf {X : MarkedDiagSet.{u}}
    {x : MarkedSite atomMarking} (s : X.obj.obj (op x)) :
    MarkedPresheaf.forget.map (markedFaceNerveCell (X.obj.map (MarkedSite.toSelf x).op s)) =
      MarkedPresheaf.forget.map (markedFaceNerveCell s) := by
  rw [markedFaceNerveCell_map, Functor.map_comp]
  rfl

private theorem obj_markedClosedSubsetIso_inv_app {V : Shape.Atom}
    (c : (markedClosedSubset.{u} U S A hA).underlying.obj (op V))
    (e : (MarkedPresheaf.forget.obj (markedFaceNerveSite.obj
      ((MarkedSite.unmarked atomMarking).obj V))) _⦋1⦌) (i : Fin 2) :
    (((markedClosedSubsetIso U hA).inv.app _ ((MarkedPresheaf.forget.map
      (markedFaceNerveCell (x := (MarkedSite.unmarked atomMarking).obj V) c)).app _ e)).1.obj
        i).down =
      ConcreteCategory.hom c.1.down (e.obj i).down := by
  have h := congrArg (fun φ => φ.app _ e) (forget_map_markedFaceNerveCell_comp_inv U hA c)
  have h2 := congrArg (fun σ : (chainSubcomplex (S : Set U.ogp)).toSSet _⦋1⦌ => (σ.1.obj i).down)
    h
  exact h2.trans (by rfl)

private theorem obj_markedClosedSubsetIso_inv_app' {x : MarkedSite atomMarking}
    (s : (markedClosedSubset.{u} U S A hA).obj.obj (op x))
    (e : (MarkedPresheaf.forget.obj (markedFaceNerveSite.obj x)) _⦋1⦌) (i : Fin 2) :
    (((markedClosedSubsetIso U hA).inv.app _
      ((MarkedPresheaf.forget.map (markedFaceNerveCell s)).app _ e)).1.obj i).down =
      ConcreteCategory.hom
        ((markedClosedSubset U S A hA).obj.map (MarkedSite.toSelf x).op s).1.down
        (e.obj i).down := by
  rw [← forget_map_markedFaceNerveCell_toSelf]
  exact obj_markedClosedSubsetIso_inv_app U hA _ e i

variable {U hA} in
private theorem markedClosedSubsetIso_hom_mem_marked {R : U.ogp → U.ogp → Prop}
    (hR : ∀ a b, R a b ↔ outputRel U.ogp a b ∨ b ∈ A ∧ grade ℕ b = 1)
    (e : (markedSubcomplex (edgeSet.{u} R) (chainSubcomplex (S : Set U.ogp))).underlying _⦋1⦌)
    (he : e ∈ (markedSubcomplex (edgeSet.{u} R) (chainSubcomplex (S : Set U.ogp))).marked ⦋1⦌) :
    (markedClosedSubsetIso U hA).hom.app _ e ∈
      (markedFaceNerve.obj (markedClosedSubset U S A hA)).marked ⦋1⦌ := by
  have hout : outputRel U.ogp (e.1.obj 0).down (e.1.obj 1).down ∨
      (e.1.obj 0).down = (e.1.obj 1).down →
      (markedClosedSubsetIso U hA).hom.app _ e ∈
        (markedFaceNerve.obj (markedClosedSubset U S A hA)).marked ⦋1⦌ := fun h =>
    MarkedPresheaf.map_mem_marked ((faceNerveClosedSubpresheafIso U S).inv ≫
      markedClosedSubsetCounit U hA) ((mem_marked_markedSubcomplex_iff _ e).2 h)
  rcases (mem_marked_markedSubcomplex_iff R e).1 he with h | h
  · rcases (hR _ _).1 h with h | ⟨hb, hd⟩
    · exact hout (Or.inl h)
    · set b := (e.1.obj 1).down
      let c : (markedClosedSubset U S A hA).underlying.obj (op (Shape.Atom.ofClosure U b)) :=
        ⟨⟨Shape.Atom.closureIncl U b⟩,
          fun t => S.lower (Shape.closureIncl_mem_closure U b t) (hA b hb).1⟩
      have hc : c ∈ (markedClosedSubset U S A hA).marked (Shape.Atom.ofClosure U b) :=
        (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr ⟨b, hb,
          Shape.Atom.map_closureInclOGP_top U b, Shape.Atom.dimension_ofClosure U b⟩)
      obtain ⟨hm, s, hs⟩ := hc
      obtain ⟨w, hw⟩ := (Shape.Atom.exists_closureIncl_eq_iff U b (e.1.obj 0).down).2
        (obj_zero_le_obj_one e.1)
      let e' : (MarkedPresheaf.forget.obj (markedFaceNerveSite.obj
          (MarkedSite.marked (Shape.Atom.ofClosure U b) hm))) _⦋1⦌ :=
        ComposableArrows.mk₁ (homOfLE (ULift.up_le.2 ((Shape.Atom.ofClosure U b).le_top w)))
      have he' : e' ∈ (markedFaceNerveSite.obj
          (MarkedSite.marked (Shape.Atom.ofClosure U b) hm)).marked ⦋1⦌ := by
        refine (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 ⟨rfl, Or.inr ⟨⟨rfl,
          fun y _ => (Shape.Atom.ofClosure U b).le_top y⟩, ?_⟩⟩
        change grade ℕ (Shape.Atom.ofClosure U b).top = 1
        rw [← (Shape.Atom.ofClosure U b).dimension_eq, Shape.Atom.dimension_ofClosure, hd]
      have hm' := MarkedPresheaf.map_mem_marked (markedFaceNerveCell s) he'
      rw [← forget_map_markedFaceNerveCell_toSelf, hs] at hm'
      have hrt := (Iso.inv_hom_id_app_apply (markedClosedSubsetIso U hA) _
        ((MarkedPresheaf.forget.map (markedFaceNerveCell
          (x := (MarkedSite.unmarked atomMarking).obj (Shape.Atom.ofClosure U b)) c)).app _ e'))
      have heq : (markedClosedSubsetIso U hA).inv.app _ ((MarkedPresheaf.forget.map
          (markedFaceNerveCell (x := (MarkedSite.unmarked atomMarking).obj
            (Shape.Atom.ofClosure U b)) c)).app _ e') = e := by
        refine chain_edge_ext U ?_ ?_
        · exact (obj_markedClosedSubsetIso_inv_app U hA c e' 0).trans hw
        · exact (obj_markedClosedSubsetIso_inv_app U hA c e' 1).trans
            (Shape.Atom.closureIncl_top U b)
      rw [heq] at hrt
      exact hrt ▸ hm'
  · exact hout (Or.inr h)

variable {U hA} in
private theorem markedClosedSubsetIso_inv_mem_marked {R : U.ogp → U.ogp → Prop}
    (hR : ∀ a b, R a b ↔ outputRel U.ogp a b ∨ b ∈ A ∧ grade ℕ b = 1)
    (y : (markedFaceNerve.obj (markedClosedSubset U S A hA)).underlying _⦋1⦌)
    (hy : y ∈ (markedFaceNerve.obj (markedClosedSubset U S A hA)).marked ⦋1⦌) :
    (markedClosedSubsetIso U hA).inv.app _ y ∈
      (markedSubcomplex (edgeSet.{u} R) (chainSubcomplex (S : Set U.ogp))).marked ⦋1⦌ := by
  refine (mem_marked_markedSubcomplex_iff R _).2 ?_
  rcases mem_marked_markedFaceNerve hy with ⟨x, s, e, he, rfl⟩ | ⟨v, rfl⟩
  · rw [obj_markedClosedSubsetIso_inv_app' U hA s e 0,
      obj_markedClosedSubsetIso_inv_app' U hA s e 1]
    obtain ⟨V, _ | _, hV⟩ := x
    · obtain ⟨-, h | ⟨h, -⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 he
      · exact Or.inl ((hR _ _).2 (Or.inl (boundary_closure_apply_eq (Shape.Atom.isMap
          ((markedClosedSubset U S A hA).obj.map (MarkedSite.toSelf _).op s).1.down) h)))
      · exact absurd h.1 Bool.false_ne_true
    · obtain ⟨-, h | ⟨⟨-, hM⟩, hd⟩⟩ := (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 he
      · exact Or.inl ((hR _ _).2 (Or.inl (boundary_closure_apply_eq (Shape.Atom.isMap
          ((markedClosedSubset U S A hA).obj.map (MarkedSite.toSelf _).op s).1.down) h)))
      have htop : (e.obj 1).down = V.top := eq_top_of_isMax hM
      have hV1 : V.dimension = 1 :=
        V.dimension_eq.trans ((congrArg (grade ℕ) htop).symm.trans hd)
      have hc : (markedClosedSubset U S A hA).obj.map (MarkedSite.toSelf _).op s ∈
          (markedClosedSubset U S A hA).marked V := ⟨hV rfl, s, rfl⟩
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hc with
        ⟨W, p, y, hp₁, hp₂, hpy⟩ | ⟨a, ha, him, hda⟩
      · refine Or.inr ?_
        rw [← hpy]
        exact congrArg (ConcreteCategory.hom y.1.down)
          (apply_eq_of_degeneracy ⟨hp₁, hp₂⟩ hV1 _ _)
      · refine Or.inl ((hR _ _).2 (Or.inr ⟨?_, ?_⟩))
        · rw [htop, apply_top_eq_of_map_eq _ him]
          exact ha
        · rw [htop, apply_top_eq_of_map_eq _ him, ← hda, hV1]
  · have h := NatTrans.naturality_apply (markedClosedSubsetIso U hA).inv
      (SimplexCategory.σ 0).op v
    refine Or.inr ((congrArg (fun σ : (chainSubcomplex (S : Set U.ogp)).toSSet _⦋1⦌ =>
      (σ.1.obj 0).down) h).trans (Eq.trans ?_ (congrArg (fun σ : (chainSubcomplex
        (S : Set U.ogp)).toSSet _⦋1⦌ => (σ.1.obj 1).down) h).symm))
    exact congrArg (fun i => (((markedClosedSubsetIso U hA).inv.app _ v).1.obj i).down)
      (Subsingleton.elim (α := Fin 1) _ _)

variable {U hA} in
noncomputable def markedFaceNerveMarkedClosedSubsetIso {R : U.ogp → U.ogp → Prop}
    (hR : ∀ a b, R a b ↔ outputRel U.ogp a b ∨ b ∈ A ∧ grade ℕ b = 1) :
    markedSubcomplex (edgeSet.{u} R) (chainSubcomplex (S : Set U.ogp)) ≅
      markedFaceNerve.obj (markedClosedSubset U S A hA) where
  hom := edgeHomMk (markedClosedSubsetIso U hA).hom (markedClosedSubsetIso_hom_mem_marked hR)
  inv := edgeHomMk (markedClosedSubsetIso U hA).inv (markedClosedSubsetIso_inv_mem_marked hR)
  hom_inv_id := MarkedPresheaf.hom_ext (markedClosedSubsetIso U hA).hom_inv_id
  inv_hom_id := MarkedPresheaf.hom_ext (markedClosedSubsetIso U hA).inv_hom_id

variable {U hA} in
private theorem forget_map_markedFaceNerveMarkedClosedSubsetIso_hom {R : U.ogp → U.ogp → Prop}
    (hR : ∀ a b, R a b ↔ outputRel U.ogp a b ∨ b ∈ A ∧ grade ℕ b = 1) :
    MarkedPresheaf.forget.map (markedFaceNerveMarkedClosedSubsetIso (hA := hA) hR).hom =
      MarkedPresheaf.forget.map ((faceNerveClosedSubpresheafIso U S).inv ≫
        markedClosedSubsetCounit U hA) := by
  rw [Functor.map_comp]
  rfl

theorem markedFaceNerveMarkedClosedSubsetIso_hom_comp {S' : LowerSet U.ogp} {A' : Set U.ogp}
    (hA' : ∀ a ∈ A', a ∈ S' ∧ 0 < grade ℕ a) (h : S ≤ S') {R : U.ogp → U.ogp → Prop}
    (hR : ∀ a b, R a b ↔ outputRel U.ogp a b ∨ b ∈ A ∧ grade ℕ b = 1)
    (hR' : ∀ a b, R a b ↔ outputRel U.ogp a b ∨ b ∈ A' ∧ grade ℕ b = 1)
    (ι : markedClosedSubset U S A hA ⟶ markedClosedSubset U S' A' hA')
    (hι : MarkedPresheaf.forget.map ι = Subfunctor.homOfLe (closedSubpresheaf_mono U h)) :
    (markedFaceNerveMarkedClosedSubsetIso (hA := hA) hR).hom ≫ markedFaceNerve.map ι =
      markedSubcomplexMap (edgeSet.{u} R) (chainSubcomplex_mono (LowerSet.coe_subset_coe.2 h)) ≫
        (markedFaceNerveMarkedClosedSubsetIso (hA := hA') hR').hom := by
  have hc := (MarkedPresheaf.flatForgetAdjunction atomMarking).counit.naturality ι
  rw [Functor.id_map, Functor.comp_map, hι] at hc
  have hf := faceNerve_map_comp_faceNerveClosedSubpresheafIso_hom U h
  have hf' : (faceNerveClosedSubpresheafIso U S).inv ≫
      faceNerve.map (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) =
      markedSubcomplexMap (edgeSet.{u} (outputRel U.ogp))
          (chainSubcomplex_mono (LowerSet.coe_subset_coe.2 h)) ≫
        (faceNerveClosedSubpresheafIso U S').inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← hf, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  have hm : markedClosedSubsetCounit U hA ≫ markedFaceNerve.map ι =
      faceNerve.map (Subfunctor.homOfLe (closedSubpresheaf_mono U h)) ≫
        markedClosedSubsetCounit U hA' := by
    exact (markedFaceNerve.map_comp _ _).symm.trans ((congrArg markedFaceNerve.map hc.symm).trans
      (markedFaceNerve.map_comp _ _))
  have hk : ((faceNerveClosedSubpresheafIso U S).inv ≫ markedClosedSubsetCounit U hA) ≫
      markedFaceNerve.map ι = markedSubcomplexMap (edgeSet (outputRel U.ogp))
        (chainSubcomplex_mono (LowerSet.coe_subset_coe.2 h)) ≫
          (faceNerveClosedSubpresheafIso U S').inv ≫ markedClosedSubsetCounit U hA' := by
    rw [Category.assoc, hm, ← Category.assoc, hf', Category.assoc]
  have hk' := congrArg MarkedPresheaf.forget.map hk
  simp only [Functor.map_comp, forget_map_markedSubcomplexMap, Category.assoc] at hk'
  refine MarkedPresheaf.hom_ext ?_
  simp only [Functor.map_comp, forget_map_markedFaceNerveMarkedClosedSubsetIso_hom,
    forget_map_markedSubcomplexMap]
  exact hk'

end MarkedClosedSubset

section MarkedHorn

open Opposite

variable (m : Shape.MarkedHornData)

theorem weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_rel
    {R : m.atom.ogp → m.atom.ogp → Prop}
    (hRs : ∀ a b, R a b ↔ outputRel m.atom.ogp a b ∨ b ∈ m.marking ∧ grade ℕ b = 1)
    (hRt : ∀ a b, R a b ↔ outputRel m.atom.ogp a b ∨ b ∈ m.targetMarking ∧ grade ℕ b = 1)
    (hW : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R)
      (chainSubcomplex_mono (Set.subset_univ (m.hornSet : Set m.atom.ogp))))) :
    WeakEquivalence (markedFaceNerve.{u}.map (markedHornInclusion m)) := by
  have e : Arrow.mk (markedSubcomplexMap (edgeSet.{u} R) (chainSubcomplex_mono
      (LowerSet.coe_subset_coe.2 (le_top : m.hornSet ≤ ⊤)))) ≅
      Arrow.mk (markedFaceNerve.map (markedHornInclusion m)) :=
    Arrow.isoMk (markedFaceNerveMarkedClosedSubsetIso (hA := m.marking_mem) hRs)
      (markedFaceNerveMarkedClosedSubsetIso (hA := m.targetMarking_mem) hRt)
      (markedFaceNerveMarkedClosedSubsetIso_hom_comp m.atom m.marking_mem m.targetMarking_mem
        le_top hRs hRt (markedHornInclusion m) rfl)
  have huniv : chainSubcomplex.{u} (Set.univ : Set m.atom.ogp) =
      chainSubcomplex ((⊤ : LowerSet m.atom.ogp) : Set m.atom.ogp) := by
    rw [LowerSet.coe_top]
  have : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} R) (chainSubcomplex_mono
      (LowerSet.coe_subset_coe.2 (le_top : m.hornSet ≤ ⊤)))) := by
    have := weakEquivalence_markedSubcomplexMap_of_eq (edgeSet R) huniv
    rw [← markedSubcomplexMap_comp (edgeSet R) (chainSubcomplex_mono (Set.subset_univ _))
      huniv.le]
    infer_instance
  rw [weakEquivalence_iff] at this ⊢
  exact ((weakEquivalences MarkedSSet).arrow_mk_iso_iff e).1 this

theorem weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_dim_ne_one
    (hA₁ : ∀ a ∈ m.targetMarking, grade ℕ a ≠ 1)
    (hW : WeakEquivalence (markedSubcomplexMap (edgeSet.{u} (outputRel m.atom.ogp))
      (chainSubcomplex_mono (Set.subset_univ (m.hornSet : Set m.atom.ogp))))) :
    WeakEquivalence (markedFaceNerve.{u}.map (markedHornInclusion m)) :=
  weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_rel m
    (fun _ b => ⟨Or.inl, fun h => h.resolve_right fun h' =>
      hA₁ b (m.mem_targetMarking_iff.2 (Or.inr (Or.inr h'.1))) h'.2⟩)
    (fun _ b => ⟨Or.inl, fun h => h.resolve_right fun h' => hA₁ b h'.1 h'.2⟩) hW

theorem mem_hornSet_iff_ne_and_ne {a : m.atom.ogp} :
    a ∈ m.hornSet ↔ a ≠ m.face ∧ a ≠ m.atom.top := by
  rw [m.mem_hornSet_iff, ← SetLike.mem_coe, m.atom.coe_bdryFull_top, Set.mem_Iio,
    lt_iff_le_and_ne]
  exact ⟨fun ⟨⟨_, h₁⟩, h₂⟩ => ⟨h₂, h₁⟩, fun ⟨h₁, h₂⟩ => ⟨⟨m.atom.le_top a, h₂⟩, h₁⟩⟩

theorem eq_or_eq_top_of_face_le {b : m.atom.ogp} (h : m.face ≤ b) :
    b = m.face ∨ b = m.atom.top := by
  rcases eq_or_lt_of_le h with h | h
  · exact Or.inl h.symm
  · refine Or.inr (GradeOrder.eq_of_le_of_grade_le (m.atom.le_top b) ?_)
    have h₁ : grade ℕ m.face < grade ℕ b := grade_strictMono h
    have h₂ := m.dim_face_add_one
    rw [← m.atom.dimension_eq]
    omega

theorem weakEquivalence_markedFaceNerve_map_markedHornInclusion
    (hA₁ : ∀ a ∈ m.targetMarking, grade ℕ a ≠ 1)
    (hout : outputRel m.atom.ogp m.face m.atom.top) {t : m.atom.ogp}
    (ht : m.atom.ogp.boundary ⊤ 0 true = .Iic t)
    (htQ : t ∈ (m.hornSet : Set m.atom.ogp))
    [WeakEquivalence (markedSubcomplexMap
      (edgeSet.{u} fun a b => outputRel m.atom.ogp a b ∧ b ≠ m.atom.top)
      (coneBase_le (Λ := (m.hornSet : Set m.atom.ogp)) (w := m.atom.top) htQ))] :
    WeakEquivalence (markedFaceNerve.{u}.map (markedHornInclusion m)) := by
  have htd : grade ℕ t = 0 := Nat.le_zero.1 (grade_le_of_mem_boundary
    (ht ▸ LowerSet.mem_Iic_iff.2 le_rfl : t ∈ m.atom.ogp.boundary ⊤ 0 true))
  have hTt : m.atom.ogp.boundary (.Iic t) 0 true = .Iic t :=
    boundary_Iic_of_isMin (grade_eq_zero_iff.1 htd) 0 true
  have hTtop : m.atom.ogp.boundary (.Iic m.atom.top) 0 true = .Iic t := by
    rw [m.atom.Iic_top, ht]
  refine weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_dim_ne_one m hA₁ ?_
  refine weakEquivalence_markedSubcomplexMap_chainSubcomplex_horn (outputRel m.atom.ogp)
    (x := m.face) m.atom.le_top (fun a => mem_hornSet_iff_ne_and_ne m)
    (fun b hb => eq_or_eq_top_of_face_le m hb) ?_ htQ (hTt.trans hTtop.symm)
    (fun a haQ ha => ?_) hout (fun a _ ha => ha.trans hout)
  · intro h
    have := m.dim_face_add_one
    rw [h, ← m.atom.dimension_eq] at this
    omega
  · have hta : t ∈ m.atom.ogp.boundary (.Iic a) 0 true := by
      rw [ha, hTtop]
      exact LowerSet.mem_Iic_iff.2 le_rfl
    exact ⟨a, haQ, LowerSet.mem_Iic_iff.1 (boundary_le _ 0 true hta),
      Or.inl (hTt.trans (ha.trans hTtop).symm), ha, le_refl a, Or.inr rfl⟩

end MarkedHorn

section Atom

variable (W : Shape.Atom)

theorem boundary_bdry_zero (hW : 2 ≤ W.dimension) (α γ : Bool) :
    W.ogp.boundary (W.ogp.bdry ⊤ α) 0 γ = W.ogp.boundary ⊤ 0 γ := by
  rw [W.bdry_top_eq_boundary (by omega) α]
  exact IsMoleculeIn.isGlobular W.isMolecule _ _ (by omega) γ α

end Atom

section TwoPieces

variable {W : Shape.Atom} {β : Bool} {a b : W.ogp}

private theorem bdry_inf_bdry_not (hd : 2 ≤ W.dimension) (β : Bool) :
    W.ogp.bdry ⊤ β ⊓ W.ogp.bdry ⊤ (!β) = W.ogp.boundaryFull ⊤ (W.dimension - 2) := by
  have h := W.isAtom.isRound.inf_boundary_succ (W.dimension - 2) (by
    rw [LowerSet.krullDim_top, W.krullDim_eq_dimension]
    exact_mod_cast (by omega : W.dimension - 2 + 1 < W.dimension))
  rw [show W.dimension - 2 + 1 = W.dimension - 1 by omega] at h
  rw [W.bdry_top_eq_boundary (by omega), W.bdry_top_eq_boundary (by omega)]
  cases β
  exacts [h, (inf_comm _ _).trans h]

private theorem boundary_bdry_sub_two (hd : 2 ≤ W.dimension) (α γ : Bool) :
    W.ogp.boundary (W.ogp.bdry ⊤ α) (W.dimension - 2) γ =
      W.ogp.boundary ⊤ (W.dimension - 2) γ := by
  rw [W.bdry_top_eq_boundary (by omega) α]
  exact IsMoleculeIn.isGlobular W.isMolecule _ _ (by omega) γ α

private theorem inf_bdry_eq_boundary_of_forall (hd : 2 ≤ W.dimension) (γ : Bool)
    (hp : W.ogp.IsPastingIn (W.dimension - 2) (cond γ (.Iic a) (.Iic b)) (cond γ (.Iic b) (.Iic a))
      (W.ogp.bdry ⊤ β))
    (h : ∀ y, (∀ δ, y ∈ W.ogp.boundary (.Iic a) (W.dimension - 2) δ) →
      y ∈ W.ogp.boundary (.Iic b) (W.dimension - 2) γ) :
    .Iic b ⊓ W.ogp.bdry ⊤ (!β) = W.ogp.boundary (.Iic b) (W.dimension - 2) γ := by
  have hMN := bdry_inf_bdry_not (W := W) hd β
  obtain ⟨-, -, hFG⟩ := (isPastingIn_cond_iff γ).1 hp
  apply le_antisymm
  · intro y hy
    obtain ⟨hyF, hyN⟩ := LowerSet.mem_inf_iff.1 hy
    have hyMN : y ∈ W.ogp.bdry ⊤ β ⊓ W.ogp.bdry ⊤ (!β) :=
      LowerSet.mem_inf_iff.2 ⟨hp.le_cond γ hyF, hyN⟩
    rw [hMN] at hyMN
    obtain ⟨δ, hδ⟩ := mem_boundaryFull.1 hyMN
    rw [← boundary_bdry_sub_two hd β δ] at hδ
    by_cases hδγ : δ = γ
    · rwa [hδγ, hp.boundary_cond γ] at hδ
    · rw [Bool.eq_not.2 hδγ, ((isPastingIn_cond_comm γ).1 hp).boundary_cond (!γ)] at hδ
      exact h y ((Bool.forall_bool' γ).2
        ⟨hFG ▸ LowerSet.mem_inf_iff.2 ⟨boundary_le _ _ _ hδ, hyF⟩, hδ⟩)
  · intro y hy
    refine LowerSet.mem_inf_iff.2 ⟨boundary_le _ _ _ hy, ?_⟩
    rw [← hp.boundary_cond γ, boundary_bdry_sub_two hd β γ,
      ← boundary_bdry_sub_two hd (!β) γ] at hy
    exact boundary_le _ _ _ hy

private theorem inter_bdry_eq_boundary (hd : 3 ≤ W.dimension) (γ : Bool)
    (ha : grade ℕ a = W.dimension - 1)
    (hp : W.ogp.IsPastingIn (W.dimension - 2) (cond γ (.Iic a) (.Iic b)) (cond γ (.Iic b) (.Iic a))
      (W.ogp.bdry ⊤ β)) :
    .Iic b ⊓ W.ogp.bdry ⊤ (!β) = W.ogp.boundary (.Iic b) (W.dimension - 2) γ := by
  have hgA := IsMoleculeIn.isGlobular (W.isRDC a)
  have hgB := IsMoleculeIn.isGlobular (W.isRDC b)
  refine inf_bdry_eq_boundary_of_forall (by omega) γ hp fun y hy => ?_
  have hfull := (W.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := a))).isRound.inf_boundary_succ
    (W.dimension - 2 - 1) (by
      rw [LowerSet.krullDim_Iic, ha]
      exact_mod_cast (by omega : W.dimension - 2 - 1 + 1 < W.dimension - 1))
  rw [show W.dimension - 2 - 1 + 1 = W.dimension - 2 by omega] at hfull
  obtain ⟨δ, hδ⟩ := mem_boundaryFull.1 (hfull ▸ LowerSet.mem_inf_iff.2 ⟨hy false, hy true⟩)
  rw [hp.boundary_eq_boundary_of_lt_cond γ hgA hgB (by omega) δ] at hδ
  exact hgB.boundary_le_boundary (by omega : W.dimension - 2 - 1 < W.dimension - 2) δ γ hδ

theorem inter_bdry_eq_boundary_of_dimension_eq_two (hd : W.dimension = 2) (γ : Bool)
    (ha : grade ℕ a = W.dimension - 1)
    (hp : W.ogp.IsPastingIn (W.dimension - 2) (cond γ (.Iic a) (.Iic b)) (cond γ (.Iic b) (.Iic a))
      (W.ogp.bdry ⊤ β)) :
    .Iic b ⊓ W.ogp.bdry ⊤ (!β) = W.ogp.boundary (.Iic b) 0 γ := by
  have hk : W.dimension - 2 = 0 := by omega
  have hbot := (W.isMolecule.isAtomIn_Iic (LowerSet.mem_top (a := a))).isRound.inf_boundary_zero
    (by rw [LowerSet.krullDim_Iic, ha, hd]; exact_mod_cast (show 0 < 2 - 1 by omega))
  have h := inf_bdry_eq_boundary_of_forall (by omega) γ hp fun y hy => by
    rw [hk] at hy
    exact absurd (hbot ▸ LowerSet.mem_inf_iff.2 ⟨hy false, hy true⟩) (by simp)
  rwa [hk] at h

private theorem mem_hornSet_closure_iff {x y : W.ogp} :
    y ∈ (W.ogp.bdryFull ⊤ : Set W.ogp) \ W.ogp.interior (.Iic x) ↔ y ≠ W.top ∧ y ≠ x := by
  rw [W.coe_bdryFull_top, W.interior_Iic, Set.mem_sdiff, Set.mem_Iio, Set.mem_singleton_iff,
    lt_iff_le_and_ne]
  exact and_congr_left' (and_iff_right (W.le_top y))

theorem hornSet_closure_eq_union (hd : 2 ≤ W.dimension) (γ : Bool)
    (ha : grade ℕ a = W.dimension - 1) (hb : grade ℕ b = W.dimension - 1)
    (hp : W.ogp.IsPastingIn (W.dimension - 2) (cond γ (.Iic a) (.Iic b)) (cond γ (.Iic b) (.Iic a))
      (W.ogp.bdry ⊤ β)) :
    (W.ogp.bdryFull ⊤ : Set W.ogp) \ W.ogp.interior (.Iic a) =
      ((.Iic b ⊔ W.ogp.bdry ⊤ (!β) : LowerSet W.ogp) : Set W.ogp) := by
  have hMN := bdry_inf_bdry_not (W := W) hd β
  obtain ⟨hAB, -, hFG⟩ := (isPastingIn_cond_iff γ).1 hp
  have hab : a ≠ b := by
    rintro rfl
    rw [inf_idem] at hFG
    have := grade_le_of_mem_boundary (hFG.le (LowerSet.mem_Iic_iff.2 le_rfl))
    omega
  have hlt (α : Bool) {z : W.ogp} (hz : z ∈ W.ogp.bdry ⊤ α) : z ≠ W.top := by
    have hz' : z ∈ (W.ogp.bdryFull ⊤ : Set W.ogp) := bdry_le_bdryFull ⊤ α hz
    rw [W.coe_bdryFull_top] at hz'
    exact ne_of_lt hz'
  have key : ∀ δ {y : W.ogp}, y ∈ W.ogp.boundary (.Iic a) (W.dimension - 2) δ →
      y ∈ LowerSet.Iic b ∨ y ∈ W.ogp.bdry ⊤ (!β) := by
    intro δ y hδ
    by_cases hδγ : δ = γ
    · rw [hδγ, ← hFG] at hδ
      exact Or.inl (LowerSet.mem_inf_iff.1 hδ).2
    · rw [Bool.eq_not.2 hδγ, ← ((isPastingIn_cond_comm γ).1 hp).boundary_cond (!γ),
        boundary_bdry_sub_two hd β (!γ)] at hδ
      have hyMN : y ∈ W.ogp.boundaryFull ⊤ (W.dimension - 2) := mem_boundaryFull.2 ⟨_, hδ⟩
      rw [← hMN] at hyMN
      exact Or.inr (LowerSet.mem_inf_iff.1 hyMN).2
  have hdG : krullDim (LowerSet.Iic a) = ((W.dimension - 2 : ℕ) : WithBot ℕ∞) + 1 := by
    rw [LowerSet.krullDim_Iic, ha]
    exact_mod_cast (by omega : W.dimension - 1 = W.dimension - 2 + 1)
  ext y
  rw [mem_hornSet_closure_iff, SetLike.mem_coe, LowerSet.mem_sup_iff]
  constructor
  · rintro ⟨hyt, hyx⟩
    have hy : y ∈ W.ogp.bdry ⊤ false ⊔ W.ogp.bdry ⊤ true := by
      change y ∈ (W.ogp.bdryFull ⊤ : Set W.ogp)
      rw [W.coe_bdryFull_top]
      exact lt_of_le_of_ne (W.le_top y) hyt
    obtain ⟨α, hα⟩ : ∃ α, y ∈ W.ogp.bdry ⊤ α := by
      rcases LowerSet.mem_sup_iff.1 hy with h | h
      · exact ⟨false, h⟩
      · exact ⟨true, h⟩
    by_cases hαβ : α = β
    · rw [hαβ, ← hAB] at hα
      rcases LowerSet.mem_sup_iff.1 hα with hyG | hyF
      · have hyfull : y ∈ ((W.ogp.bdry (.Iic a) false ⊔ W.ogp.bdry (.Iic a) true :
            LowerSet W.ogp) : Set W.ogp) := by
          rw [coe_bdry_Iic_sup]
          exact lt_of_le_of_ne (LowerSet.mem_Iic_iff.1 hyG) hyx
        rw [SetLike.mem_coe, LowerSet.mem_sup_iff, bdry_eq_boundary hdG,
          bdry_eq_boundary hdG] at hyfull
        rcases hyfull with hy' | hy'
        · exact key false hy'
        · exact key true hy'
      · exact Or.inl hyF
    · rw [Bool.eq_not.2 hαβ] at hα
      exact Or.inr hα
  · rintro (hy | hy)
    · refine ⟨hlt β (hp.le_cond γ hy), fun h => hab ?_⟩
      rw [h] at hy
      exact GradeOrder.eq_of_le_of_grade_le (LowerSet.mem_Iic_iff.1 hy) (by rw [ha, hb])
    · refine ⟨hlt (!β) hy, fun h => ?_⟩
      rw [h] at hy
      have hxMN : a ∈ W.ogp.bdry ⊤ β ⊓ W.ogp.bdry ⊤ (!β) := LowerSet.mem_inf_iff.2
        ⟨hAB ▸ LowerSet.mem_sup_iff.2 (Or.inl (LowerSet.mem_Iic_iff.2 le_rfl)), hy⟩
      rw [hMN] at hxMN
      obtain ⟨δ, hδ⟩ := mem_boundaryFull.1 hxMN
      have := grade_le_of_mem_boundary hδ
      omega

private theorem weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_isPastingIn
    (m : Shape.MarkedHornData) (hd : 3 ≤ m.atom.dimension) {a b : m.atom.ogp} (γ : Bool)
    (ha : grade ℕ a = m.atom.dimension - 1)
    (hb : grade ℕ b = m.atom.dimension - 1) {β : Bool}
    (hp : m.atom.ogp.IsPastingIn (m.atom.dimension - 2) (cond γ (.Iic a) (.Iic b))
      (cond γ (.Iic b) (.Iic a)) (m.atom.ogp.bdry ⊤ β))
    (hface : m.face = a) (hA₁ : ∀ a ∈ m.targetMarking, grade ℕ a ≠ 1) :
    WeakEquivalence (markedFaceNerve.{u}.map (markedHornInclusion m)) := by
  obtain ⟨t, -, ht⟩ := exists_boundary_zero_eq_Iic m.atom.isMolecule true
  have hgA := IsMoleculeIn.isGlobular (m.atom.isRDC a)
  have hgB := IsMoleculeIn.isGlobular (m.atom.isRDC b)
  have hk : 0 < m.atom.dimension - 2 := by omega
  let F := LowerSet.Iic b
  let N := m.atom.ogp.bdry ⊤ (!β)
  have hQ : (m.hornSet : Set m.atom.ogp) = ((F ⊔ N : LowerSet m.atom.ogp) : Set m.atom.ogp) := by
    change (m.atom.ogp.bdryFull ⊤ : Set m.atom.ogp) \ m.atom.ogp.interior (.Iic m.face) = _
    rw [hface]
    exact hornSet_closure_eq_union (by omega) γ ha hb hp
  have hI : m.atom.ogp.boundary F (m.atom.dimension - 2) γ = F ⊓ N :=
    (inter_bdry_eq_boundary hd γ ha hp).symm
  have hF0 : m.atom.ogp.boundary F 0 true = .Iic t := by
    rw [← hp.boundary_eq_of_lt_cond γ hgA hgB hk true, boundary_bdry_zero m.atom (by omega), ht]
  have htF : t ∈ m.atom.ogp.boundary F 0 true := by
    rw [hF0]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have htN : t ∈ m.atom.ogp.boundary N 0 true := by
    rw [boundary_bdry_zero m.atom (by omega), ht]
    exact LowerSet.mem_Iic_iff.2 le_rfl
  have htI : t ∈ m.atom.ogp.boundary (m.atom.ogp.boundary F (m.atom.dimension - 2) γ)
      0 true := by
    rw [hgB 0 _ hk true γ]
    exact htF
  have hQw : ∀ y ∈ (m.hornSet : Set m.atom.ogp), y < m.atom.top := fun y hy =>
    lt_of_le_of_ne (m.atom.le_top y) ((mem_hornSet_iff_ne_and_ne m).1 hy).2
  have hFw : ∀ y ∈ F, y < m.atom.top := fun y hy =>
    hQw y (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inl hy))
  have hNw : ∀ y ∈ N, y < m.atom.top := fun y hy =>
    hQw y (by rw [hQ]; exact LowerSet.mem_sup_iff.2 (Or.inr hy))
  let R : m.atom.ogp → m.atom.ogp → Prop :=
    fun a b => outputRel m.atom.ogp a b ∧ b ≠ m.atom.top
  have hR₁ : ∀ a b, a ≤ b → b < m.atom.top → outputRel m.atom.ogp a b → R a b :=
    fun _ _ _ hb h => ⟨h, hb.ne⟩
  have hR₂ : ∀ a, R a m.atom.top → a = m.atom.top := fun _ h => absurd rfl h.2
  have := weakEquivalence_coneBase_of_isMoleculeIn.{u} R hR₁ hR₂ (m.atom.isRDC b) hFw htF
  have := weakEquivalence_coneBase_of_isMoleculeIn.{u} R hR₁ hR₂
    (m.isMoleculeIn_bdry (!β)) hNw htN
  have := weakEquivalence_coneBase_of_isMoleculeIn.{u} R hR₁ hR₂
    ((m.atom.isRDC b).boundary _ γ) (fun y hy => hFw y (boundary_le _ _ _ hy)) htI
  have := weakEquivalence_coneBase_congr.{u} R (w := m.atom.top)
    ((congrArg (fun S : LowerSet m.atom.ogp => (S : Set m.atom.ogp)) hI).trans
      (LowerSet.coe_inf F N))
    (boundary_le _ 0 true htI)
  have := weakEquivalence_coneBase_union.{u} R (w := m.atom.top)
    (boundary_le F 0 true htF) (boundary_le N 0 true htN)
    (fun h => lt_irrefl _ (hFw _ h)) (fun h => lt_irrefl _ (hNw _ h)) mem_or_mem_of_le_or_le
  have hQ' : ((F : Set m.atom.ogp) ∪ N) = (m.hornSet : Set m.atom.ogp) := by
    rw [hQ, LowerSet.coe_sup]
  have := weakEquivalence_coneBase_congr.{u} R (w := m.atom.top) hQ'
    (Or.inl (boundary_le F 0 true htF))
  refine weakEquivalence_markedFaceNerve_map_markedHornInclusion m hA₁ ?_ ht
    (hQ' ▸ Or.inl (boundary_le F 0 true htF))
  change m.atom.ogp.boundary (.Iic m.face) 0 true =
    m.atom.ogp.boundary (.Iic m.atom.top) 0 true
  rw [hface, ← ((isPastingIn_cond_comm γ).1 hp).boundary_eq_of_lt_cond (!γ) hgB hgA hk true,
    boundary_bdry_zero m.atom (by omega), m.atom.Iic_top]

end TwoPieces

section Invertor

variable (V : Shape.Atom) (ε : Bool) (hV : 0 < V.dimension)

theorem weakEquivalence_markedFaceNerve_map_invertorMarkedHorn_of_two_le
    (h2 : 2 ≤ V.dimension) :
    WeakEquivalence (markedFaceNerve.{u}.map
      (markedHornInclusion (Shape.invertorMarkedHorn V ε hV))) := by
  have hd : (Shape.invertorAtom V ε hV).dimension = V.dimension + 1 :=
    Shape.dimension_invertorAtom V ε hV
  have hd3 : 3 ≤ (Shape.invertorAtom V ε hV).dimension := by omega
  have hdim (β : Bool) : grade ℕ (Shape.invertorTopElt V ε hV (some β)) =
      (Shape.invertorAtom V ε hV).dimension - 1 := by
    rw [Shape.dim_invertorTopElt_some, hd]
    omega
  have hdim1 (β : Bool) : grade ℕ (Shape.invertorTopElt V ε hV (some β)) ≠ 1 := by
    rw [hdim]
    omega
  have htop : grade ℕ (Shape.invertorAtom V ε hV).top ≠ 1 := by
    rw [← (Shape.invertorAtom V ε hV).dimension_eq]
    omega
  refine weakEquivalence_markedFaceNerve_map_markedHornInclusion_of_isPastingIn
    (Shape.invertorMarkedHorn V ε hV) hd3 (!ε) (hdim ε) (hdim (!ε))
    (Shape.isPastingIn_closure_invertorTopElt V ε hV) rfl fun a ha => ?_
  rcases (Shape.invertorMarkedHorn V ε hV).mem_targetMarking_iff.1 ha with rfl | ⟨-, rfl⟩ | ha
  · exact htop
  · exact hdim1 ε
  · obtain rfl := Set.mem_singleton_iff.1 ha
    exact hdim1 (!ε)

end Invertor

end Atoms.Diagrammatic

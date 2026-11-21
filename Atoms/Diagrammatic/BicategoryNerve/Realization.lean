import Atoms.Diagrammatic.BicategoryNerve.PathInterp
import Atoms.Diagrammatic.Rewriting.InftyCategory

open CategoryTheory Opposite Order Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape
open CategoryTheory.Bicategory (PathCell pathComp pathComp_mapPath)
open CategoryTheory.FreeBicategory (lift IsStructural)
open scoped CategoryTheory.Bicategory

universe w v u v'

namespace Atoms.Diagrammatic

attribute [local instance high] instFintypeRdc

namespace Layered.Signature.Interp

variable {B : Type u} [Bicategory.{w, v} B] {S : Signature.{v'}} [DecidableEq S.Pt]
  (I : S.Interp (bicategoryNerve.{w, v, u} B)) (hS : S.WellFormed)

include hS

theorem isPath_cellSource (c : S.Ce) : S.IsPath (S.cellSource c) := (hS c).1

theorem isPath_cellTarget (c : S.Ce) : S.IsPath (S.cellTarget c) := by
  rw [IsPath, ← (hS c).2]
  exact (hS c).1

theorem dim_cell (c : S.Ce) : (PastingDiagram.ofCell (I.cell c).2).dim = 2 :=
  (I.hasRoundType_cell c (isPath_cellSource hS c) (isPath_cellTarget hS c)).dim_eq.trans
    (congrArg (· + 1) (I.dim_path (isPath_cellSource hS c)))

theorem exists_nerveComposite_cell (c : S.Ce)
    (hd : (PastingDiagram.ofCell (I.cell c).2).dim ≤ 2) :
    ∃ φ, (PastingDiagram.ofCell (I.cell c).2).nerveComposite hd =
      ⟨I.pointObj (S.cellEnds hS c).1, I.pointObj (S.cellEnds hS c).2,
        I.label.mapPath (S.toPath _ (S.walk_cellSource hS c)),
        I.label.mapPath (S.toPath _ (S.walk_cellTarget hS c)), φ⟩ := by
  have hT := I.hasRoundType_cell c (isPath_cellSource hS c) (isPath_cellTarget hS c)
  have hs : S.pathEnds (S.cellSource c) = some (S.cellEnds hS c) := (Option.some_get _).symm
  have ht : S.pathEnds (S.cellTarget c) = some (S.cellEnds hS c) := (hS c).2.symm.trans hs
  have hb (α : Bool) : ((PastingDiagram.ofCell (I.cell c).2).boundary 1 α).dim ≤ 2 :=
    (PastingDiagram.ofCell (I.cell c).2).shape.dimension_boundary_le 1 α |>.trans one_le_two
  have e₀ : ((PastingDiagram.ofCell (I.cell c).2).boundary 1 false).Equiv
      (I.path _ (isPath_cellSource hS c).ne_nil) :=
    hT.equiv_boundary_cond (I.dim_path (isPath_cellSource hS c)) false
  have e₁ : ((PastingDiagram.ofCell (I.cell c).2).boundary 1 true).Equiv
      (I.path _ (isPath_cellTarget hS c).ne_nil) :=
    hT.equiv_boundary_cond (I.dim_path (isPath_cellSource hS c)) true
  have h₀ := (PastingDiagram.nerveComposite_boundary_one _ hd false (hb false)).symm.trans
    ((PastingDiagram.nerveComposite_congr e₀ (hb false)
      ((I.dim_path (isPath_cellSource hS c)).trans_le one_le_two)).trans
      (I.nerveComposite_path _ hs _))
  have h₁ := (PastingDiagram.nerveComposite_boundary_one _ hd true (hb true)).symm.trans
    ((PastingDiagram.nerveComposite_congr e₁ (hb true)
      ((I.dim_path (isPath_cellTarget hS c)).trans_le one_le_two)).trans
      (I.nerveComposite_path _ ht _))
  obtain ⟨ha₀, hb₀, hP₀, -, -⟩ := Bicategory.PathCell.mk.inj h₀
  obtain ⟨-, -, hQ₁, -, -⟩ := Bicategory.PathCell.mk.inj h₁
  exact PastingDiagram.pathCell_exists_eq_mk _ ha₀ hb₀ hP₀ hQ₁

noncomputable def cellComposite (c : S.Ce) :
    pathComp (𝟭q B) (I.label.mapPath (S.toPath _ (S.walk_cellSource hS c))) ⟶
      pathComp (𝟭q B) (I.label.mapPath (S.toPath _ (S.walk_cellTarget hS c))) :=
  (I.exists_nerveComposite_cell hS c (I.dim_cell hS c).le).choose

noncomputable def reading : S.BicatInterp hS B where
  toPrefunctor := I.toGenPrefunctor
  cell c := eqToHom (pathComp_mapPath I.label _).symm ≫ I.cellComposite hS c ≫
    eqToHom (pathComp_mapPath I.label _)

theorem reading_cell (c : S.Ce) :
    (I.reading hS).cell c = eqToHom (pathComp_mapPath I.label _).symm ≫ I.cellComposite hS c ≫
      eqToHom (pathComp_mapPath I.label _) :=
  rfl

theorem nerveComposite_cell (c : S.Ce) (hd : (PastingDiagram.ofCell (I.cell c).2).dim ≤ 2) :
    (PastingDiagram.ofCell (I.cell c).2).nerveComposite hd =
      ⟨I.pointObj (S.cellEnds hS c).1, I.pointObj (S.cellEnds hS c).2,
        (I.reading hS).label.mapPath (S.toPath _ (S.walk_cellSource hS c)),
        (I.reading hS).label.mapPath (S.toPath _ (S.walk_cellTarget hS c)),
        eqToHom (pathComp_mapPath (I.reading hS).label _) ≫ (I.reading hS).cell c ≫
          eqToHom (pathComp_mapPath (I.reading hS).label _).symm⟩ := by
  refine (I.exists_nerveComposite_cell hS c (I.dim_cell hS c).le).choose_spec.trans ?_
  refine congrArg (PathCell.mk _ _ _ _) ?_
  rw [reading_cell]
  exact eq_eqToHom_conj_conj _ _ _ _ _

private theorem unitorReading_heq_of_eq (F : S.BicatInterp hS B) (k : UnitorKind)
    (e : Edge S.Pt S.Ed) {x y x' y' : S.Pt} (hx : x = x') (hy : y = y')
    (hs : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some y)
    (ht : S.walk x (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some y)
    (hs' : S.walk x' (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).1 = some y')
    (ht' : S.walk x' (S.cellType (.unitor k e : Cell S.Pt S.Ed S.Ce)).2 = some y') :
    F.unitorReading k e hs ht ≍ F.unitorReading k e hs' ht' := by
  subst hx hy
  rfl

theorem nerveComposite_unitorDiagram_gen (g : S.Ed) (k : UnitorKind)
    (hc : (S.pathEnds (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1).isSome)
    (hs : S.walk ((S.pathEnds (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1).get hc).1
      (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1 =
      some ((S.pathEnds (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1).get hc).2)
    (ht : S.walk ((S.pathEnds (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1).get hc).1
      (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).2 =
      some ((S.pathEnds (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1).get hc).2)
    (hd : (I.unitorDiagram k (.gen g)).dim ≤ 2) :
    (I.unitorDiagram k (.gen g)).nerveComposite hd = PathCell.ofHom (I.reading hS).label
      (S.toPath _ hs) (S.toPath _ ht) ((I.reading hS).unitorReading k (.gen g) hs ht) := by
  obtain ⟨θ, hθ⟩ := I.toPathInterp.exists_nerveComposite_unitorDiagram k (.gen g) hc hs ht hd
  have hc₁ := edgeSig.isPath_cellType_unitor_fst k (.gen ())
  have hs₁ := edgeSig.walk_of_pathEnds (Option.some_get hc₁).symm
  have ht₁ := edgeSig.walk_of_pathEnds ((edgeSig.pathEnds_cellType_snd wellFormed_edgeSig
    (.unitor k (.gen ()) : Cell edgeSig.Pt edgeSig.Ed edgeSig.Ce)).trans (Option.some_get hc₁).symm)
  have hDom : (I.toPathInterp.freeEdge g).unitorDomain k (.gen ()) =
      I.toPathInterp.unitorDomain k (.gen g) := by
    cases k <;> rfl
  have hMap : (I.toPathInterp.freeEdge g).unitorMap k (.gen ()) ≍
      I.toPathInterp.unitorMap k (.gen g) := by
    cases k <;> rfl
  have hF : ((I.toPathInterp.freeEdge g).unitorDiagram k (.gen ())).Equiv
      ⟨I.toPathInterp.unitorDomain k (.gen g), realize.map (I.toPathInterp.unitorMap k (.gen g)) ≫
        ((I.toPathInterp.freeEdge g).ofEdge (.gen ())).map⟩ := by
    exact ((I.toPathInterp.freeEdge g).equiv_unitorDiagram k (.gen ())).trans
      (PastingDiagram.equiv_of_eq (PastingDiagram.mk_realize_eq hDom hMap _))
  have hdJ : ((I.toPathInterp.freeEdge g).unitorDiagram k (.gen ())).dim ≤ 2 :=
    (PastingDiagram.dim_eq_of_equiv hF).trans_le
      ((PastingDiagram.dim_eq_of_equiv (I.toPathInterp.equiv_unitorDiagram k _)).symm.trans_le hd)
  obtain ⟨θ', hθ'⟩ := (I.toPathInterp.freeEdge g).exists_nerveComposite_unitorDiagram k
    (.gen ()) hc₁ hs₁ ht₁ hdJ
  have h : (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.edge g).2).shape.rdc
      (PastingDiagram.ofCell (I.edge g).2).map).1.toPrefunctor =
      (bicategoryNerveHomEquiv _ (PastingDiagram.ofCell (tautCell (I.edge g).1
        (I.toPathInterp.dimension_edge g).le)).shape.rdc (PastingDiagram.ofCell (tautCell
          (I.edge g).1 (I.toPathInterp.dimension_edge g).le)).map).1.toPrefunctor ⋙q
        (lift (bicategoryNerveHomEquiv B (PastingDiagram.ofCell (I.edge g).2).shape.rdc
          (PastingDiagram.ofCell (I.edge g).2).map).1.toPrefunctor).toPrefunctor := by
    rw [toPrefunctor_ofCell (tautCell _ _)]
    exact Eq.symm (Labelling.free_comp_lift _ _ (bicategoryNerveHomEquiv B
      (PastingDiagram.ofCell (I.edge g).2).shape.rdc
        (PastingDiagram.ofCell (I.edge g).2).map).1.obj_eq_of_boundary_Iic)
  obtain ⟨ψ, hψ, hθψ⟩ := PastingDiagram.exists_isStructural_of_equiv_freeImage _
    (I.toPathInterp.unitorMap k (.gen g)) _ _ h (I.toPathInterp.dim_ofEdge (.gen g)).le
    (I.toPathInterp.equiv_unitorDiagram k (.gen g)) hF hd hdJ hθ hθ'
  have hc' := cellType_unitor_mapEdge (S' := edgeSig) (S := S) (edgePt g) (fun _ => g)
    (fun _ => rfl) (fun _ => rfl) k (.gen ())
  have hc₀ : (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1 =
      (edgeSig.cellType (.unitor k (.gen ()) : Cell edgeSig.Pt edgeSig.Ed edgeSig.Ce)).1.map
        (mapEdge (edgePt g) fun _ => g) := congrArg Prod.fst hc'
  have hc₁' : (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).2 =
      (edgeSig.cellType (.unitor k (.gen ()) : Cell edgeSig.Pt edgeSig.Ed edgeSig.Ce)).2.map
        (mapEdge (edgePt g) fun _ => g) := congrArg Prod.snd hc'
  have hs' := walk_map (edgePt g) (fun _ => g) (fun _ => rfl) (fun _ => rfl) hs₁
  have ht' := walk_map (edgePt g) (fun _ => g) (fun _ => rfl) (fun _ => rfl) ht₁
  rw [← hc₀] at hs'
  rw [← hc₁'] at ht'
  have hb := heq_unitorReading_of_isStructural (edgePt g) (fun _ => g) (fun _ => rfl)
    (fun _ => rfl) (I.toPathInterp.freeEdge g) _ (I.reading hS)
    (I.toPathInterp.toGenPrefunctor_freeEdge g) k (.gen ()) hs₁ ht₁ rfl hs' ht' hψ hθψ
  have hpts : (S.pathEnds (S.cellType (.unitor k (.gen g) : Cell S.Pt S.Ed S.Ce)).1).get hc =
      (edgePt g ((edgeSig.pathEnds (edgeSig.cellType
        (.unitor k (.gen ()) : Cell edgeSig.Pt edgeSig.Ed edgeSig.Ce)).1).get hc₁).1,
        edgePt g ((edgeSig.pathEnds (edgeSig.cellType
          (.unitor k (.gen ()) : Cell edgeSig.Pt edgeSig.Ed edgeSig.Ce)).1).get hc₁).2) :=
    Option.some.inj ((Option.some_get hc).trans (S.pathEnds_eq_some_iff.2
      ⟨(S.isPath_cellType_unitor_fst k (.gen g)).ne_nil, hs'⟩))
  have hr := unitorReading_heq_of_eq hS (I.reading hS) k (.gen g)
    (congrArg Prod.fst hpts).symm (congrArg Prod.snd hpts).symm hs' ht' hs ht
  have hθR := hb.trans hr
  rw [hθ]
  exact Bicategory.PathCell.ext rfl rfl HEq.rfl HEq.rfl
    (hθR.trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

theorem nerveComposite_unitorDiagram_unit (z : S.Pt) (k : UnitorKind)
    (hc : (S.pathEnds (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1).isSome)
    (hs : S.walk ((S.pathEnds (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1).get hc).1
      (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1 =
      some ((S.pathEnds (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1).get hc).2)
    (ht : S.walk ((S.pathEnds (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1).get hc).1
      (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).2 =
      some ((S.pathEnds (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1).get hc).2)
    (hd : (I.unitorDiagram k (.unit z)).dim ≤ 2) :
    (I.unitorDiagram k (.unit z)).nerveComposite hd = PathCell.ofHom (I.reading hS).label
      (S.toPath _ hs) (S.toPath _ ht) ((I.reading hS).unitorReading k (.unit z) hs ht) := by
  obtain ⟨θ, hθ⟩ := I.toPathInterp.exists_nerveComposite_unitorDiagram k (.unit z) hc hs ht hd
  have hc₁ := pointSig.isPath_cellType_unitor_fst k (.unit ())
  have hs₁ := pointSig.walk_of_pathEnds (Option.some_get hc₁).symm
  have ht₁ := pointSig.walk_of_pathEnds ((pointSig.pathEnds_cellType_snd wellFormed_pointSig
    (.unitor k (.unit ()) : Cell pointSig.Pt pointSig.Ed pointSig.Ce)).trans
      (Option.some_get hc₁).symm)
  have hDom : freePointInterp.unitorDomain k (.unit ()) =
      I.toPathInterp.unitorDomain k (.unit z) := by
    cases k <;> rfl
  have hMap : freePointInterp.unitorMap k (.unit ()) ≍
      I.toPathInterp.unitorMap k (.unit z) := by
    cases k <;> rfl
  have hF : (freePointInterp.unitorDiagram k (.unit ())).Equiv
      ⟨I.toPathInterp.unitorDomain k (.unit z), realize.map (I.toPathInterp.unitorMap k (.unit z)) ≫
        (freePointInterp.ofEdge (.unit ())).map⟩ := by
    exact (freePointInterp.equiv_unitorDiagram k (.unit ())).trans
      (PastingDiagram.equiv_of_eq (PastingDiagram.mk_realize_eq hDom hMap _))
  have hdJ : (freePointInterp.unitorDiagram k (.unit ())).dim ≤ 2 :=
    (PastingDiagram.dim_eq_of_equiv hF).trans_le
      ((PastingDiagram.dim_eq_of_equiv (I.toPathInterp.equiv_unitorDiagram k _)).symm.trans_le hd)
  obtain ⟨θ', hθ'⟩ := freePointInterp.exists_nerveComposite_unitorDiagram k
    (.unit ()) hc₁ hs₁ ht₁ hdJ
  have h := I.toPathInterp.toPrefunctor_unit_point z
  obtain ⟨ψ, hψ, hθψ⟩ := PastingDiagram.exists_isStructural_of_equiv_freeImage _
    (I.toPathInterp.unitorMap k (.unit z)) _ _ h (I.toPathInterp.dim_ofEdge (.unit z)).le
    (I.toPathInterp.equiv_unitorDiagram k (.unit z)) hF hd hdJ hθ hθ'
  have hc' := cellType_unitor_mapEdge (S' := pointSig) (S := S) (fun _ => z)
    (fun e => Empty.elim e) (fun e => Empty.elim e) (fun e => Empty.elim e) k (.unit ())
  have hc₀ : (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1 =
      (pointSig.cellType (.unitor k (.unit ()) : Cell pointSig.Pt pointSig.Ed pointSig.Ce)).1.map
        (mapEdge (fun _ => z) fun e => Empty.elim e) := congrArg Prod.fst hc'
  have hc₁' : (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).2 =
      (pointSig.cellType (.unitor k (.unit ()) : Cell pointSig.Pt pointSig.Ed pointSig.Ce)).2.map
        (mapEdge (fun _ => z) fun e => Empty.elim e) := congrArg Prod.snd hc'
  have hs' := walk_map (fun _ => z) (fun e => Empty.elim e) (fun e => Empty.elim e)
    (fun e => Empty.elim e) hs₁
  have ht' := walk_map (fun _ => z) (fun e => Empty.elim e) (fun e => Empty.elim e)
    (fun e => Empty.elim e) ht₁
  rw [← hc₀] at hs'
  rw [← hc₁'] at ht'
  have hb := heq_unitorReading_of_isStructural (fun _ => z) (fun e => Empty.elim e)
    (fun e => Empty.elim e) (fun e => Empty.elim e) freePointInterp _ (I.reading hS)
    (I.toPathInterp.toGenPrefunctor_freePoint z) k (.unit ()) hs₁ ht₁ rfl hs' ht' hψ hθψ
  have hpts : (S.pathEnds (S.cellType (.unitor k (.unit z) : Cell S.Pt S.Ed S.Ce)).1).get hc =
      ((fun _ => z) ((pointSig.pathEnds (pointSig.cellType
        (.unitor k (.unit ()) : Cell pointSig.Pt pointSig.Ed pointSig.Ce)).1).get hc₁).1,
        (fun _ => z) ((pointSig.pathEnds (pointSig.cellType
          (.unitor k (.unit ()) : Cell pointSig.Pt pointSig.Ed pointSig.Ce)).1).get hc₁).2) :=
    Option.some.inj ((Option.some_get hc).trans (S.pathEnds_eq_some_iff.2
      ⟨(S.isPath_cellType_unitor_fst k (.unit z)).ne_nil, hs'⟩))
  have hr := unitorReading_heq_of_eq hS (I.reading hS) k (.unit z)
    (congrArg Prod.fst hpts).symm (congrArg Prod.snd hpts).symm hs' ht' hs ht
  have hθR := hb.trans hr
  rw [hθ]
  exact Bicategory.PathCell.ext rfl rfl HEq.rfl HEq.rfl
    (hθR.trans ((eqToHom_comp_heq _ _).trans (comp_eqToHom_heq _ _)).symm)

theorem nerveComposite_cellDiagram (x : PastingDiagram (bicategoryNerve.{w, v, u} B))
    (c : Cell S.Pt S.Ed S.Ce) (hc : (S.pathEnds (S.cellType c).1).isSome)
    (hs : S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).1 =
      some ((S.pathEnds (S.cellType c).1).get hc).2)
    (ht : S.walk ((S.pathEnds (S.cellType c).1).get hc).1 (S.cellType c).2 =
      some ((S.pathEnds (S.cellType c).1).get hc).2) (hd : (I.cellDiagram x c).dim ≤ 2) :
    (I.cellDiagram x c).nerveComposite hd = PathCell.ofHom (I.reading hS).label
      (S.toPath _ hs) (S.toPath _ ht) ((I.reading hS).cellReading c hc hs ht) := by
  cases c with
  | gen g => exact I.nerveComposite_cell hS g hd
  | unitor k e =>
    cases e with
    | gen g => exact I.nerveComposite_unitorDiagram_gen hS g k hc hs ht hd
    | unit z => exact I.nerveComposite_unitorDiagram_unit hS z k hc hs ht hd
  | unit p =>
    obtain _ | ⟨e, p⟩ := p
    · exact (Bool.false_ne_true hc).elim
    have hp : (I.pathCons e p).dim = 1 :=
      I.dim_pathCons (S.walk_cons_eq_some.1 hs).2
    exact (PastingDiagram.nerveComposite_unit_of_dim_eq_one _ hp hd
      (I.nerveComposite_pathCons hs _)).trans
      (PathCell.ofHom_id (G := (I.reading hS).label) (S.toPath (e :: p) hs)).symm

variable [DecidableEq S.Ed]

theorem nerveComposite_layer {e : Edge S.Pt S.Ed} {q p' : List (Edge S.Pt S.Ed)}
    {l : Cell S.Pt S.Ed S.Ce × ℕ} (hl : S.applyLayer (e :: q) l.1 l.2 = some p') {x y : S.Pt}
    (hp : S.walk x (e :: q) = some y) (hp' : S.walk x p' = some y)
    (hd : (I.layer e q l).dim ≤ 2) :
    (I.layer e q l).nerveComposite hd = PathCell.ofHom (I.reading hS).label
      (S.toPath _ hp) (S.toPath _ hp') ((I.reading hS).layerReading l.1 l.2 hl hp hp') := by
  have hw := S.walk_of_applyLayer hl hp
  have hc := S.isSome_pathEnds_of_applyLayer hl hp
  have hE : S.pathEnds (S.cellType l.1).1 = some ((S.pathEnds (S.cellType l.1).1).get hc) :=
    (Option.some_get hc).symm
  have hT := I.hasRoundType_cellDiagram hS (I.pathCons e q).unit (S.isPath_of_pathEnds hE)
  have hsp : I.Spans (I.cellDiagram (I.pathCons e q).unit l.1)
      ((S.pathEnds (S.cellType l.1).1).get hc).1 ((S.pathEnds (S.cellType l.1).1).get hc).2 :=
    (I.spans_of_hasRoundType (I.hasRoundType_path _ hE)).of_hasRoundType hT
  have hd₀ : (I.cellDiagram (I.pathCons e q).unit l.1).dim = 2 :=
    hT.dim_eq.trans (congrArg (· + 1) (I.dim_path (S.isPath_of_pathEnds hE)))
  have hsp₁ := hsp.whisker true (c := y) hw.2.2
  have hd₁ : (I.whisker true ((e :: q).drop (l.2 + (S.cellType l.1).1.length))
      (I.cellDiagram (I.pathCons e q).unit l.1)).dim = 2 :=
    (I.dim_whisker true hsp (by omega) hw.2.2).trans hd₀
  have h₁ := I.nerveComposite_whisker_true hsp hd₀.le
    (I.nerveComposite_cellDiagram hS _ l.1 hc hw.2.1 (S.walk_cellType_snd hS hc) hd₀.le) hw.2.2
    hd₁.le
  refine (I.nerveComposite_whisker_false hsp₁ hd₁.le h₁ hw.1 hd).trans ?_
  exact (PathCell.ofHom_eqToHom (S.toPath_append₃ (S.eq_of_applyLayer_eq_some hl).2.1 hp hw.1
    hw.2.1 hw.2.2) (S.toPath_append₃ (S.eq_of_applyLayer_eq_some hl).2.2.symm hp' hw.1
      (S.walk_cellType_snd hS _) hw.2.2).symm _).symm

private theorem layerReading_comp_evalFrom_congr (F : S.BicatInterp hS B) {c : Cell S.Pt S.Ed S.Ce}
    {o : ℕ} {p p₁ p₂ r : List (Edge S.Pt S.Ed)} (e : p₁ = p₂)
    {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)} (hl₁ : S.applyLayer p c o = some p₁)
    (hl₂ : S.applyLayer p c o = some p₂) {x y : S.Pt} (hp : S.walk x p = some y)
    (hp₁ : S.walk x p₁ = some y) (hp₂ : S.walk x p₂ = some y) (h₁ : S.targetFrom p₁ ls = some r)
    (h₂ : S.targetFrom p₂ ls = some r) (hr : S.walk x r = some y) :
    F.layerReading c o hl₁ hp hp₁ ≫ F.evalFrom ls p₁ hp₁ h₁ hr =
      F.layerReading c o hl₂ hp hp₂ ≫ F.evalFrom ls p₂ hp₂ h₂ hr := by
  subst e
  rfl

theorem nerveComposite_layers {e : Edge S.Pt S.Ed} {q : List (Edge S.Pt S.Ed)} {x z : S.Pt}
    (hp : S.walk x (e :: q) = some z) : ∀ {ls : List (Cell S.Pt S.Ed S.Ce × ℕ)}
    {r : List (Edge S.Pt S.Ed)} (h : S.targetFrom (e :: q) ls = some r)
    (hr : S.walk x r = some z) (hd : (I.layers e q ls).dim ≤ 2),
    (I.layers e q ls).nerveComposite hd = PathCell.ofHom (I.reading hS).label
      (S.toPath _ hp) (S.toPath _ hr) ((I.reading hS).evalFrom ls (e :: q) hp h hr)
  | [], r, h, hr, hd => by
    obtain rfl := Option.some.inj h
    have hq : (I.pathCons e q).dim = 1 := I.dim_pathCons (S.walk_cons_eq_some.1 hp).2
    refine (PastingDiagram.nerveComposite_unit_of_dim_eq_one _ hq hd
      (I.nerveComposite_pathCons hp _)).trans ?_
    refine (PathCell.ofHom_id (G := (I.reading hS).label) (S.toPath (e :: q) hp)).symm.trans ?_
    rw [Signature.BicatInterp.evalFrom_nil, eqToHom_refl]
  | [l], r, h, hr, hd => by
    obtain ⟨h₁, h₂⟩ := S.targetFrom_cons_eq_some h
    obtain rfl := Option.some.inj h₂
    refine (I.nerveComposite_layer hS h₁ hp hr hd).trans ?_
    rw [Signature.BicatInterp.evalFrom_cons, Signature.BicatInterp.evalFrom_nil, eqToHom_refl,
      Category.comp_id]
  | l :: l' :: ls, r, h, hr, hd => by
    obtain ⟨h₁, h₂⟩ := S.targetFrom_cons_eq_some h
    have hr₁ := S.walk_applyLayer hS h₁ hp
    have hpE : S.pathEnds (e :: q) = some (x, z) :=
      S.pathEnds_eq_some_iff.2 ⟨List.cons_ne_nil _ _, hp⟩
    obtain ⟨e', q', he⟩ := List.exists_cons_of_ne_nil
      (S.isPath_of_pathEnds (S.pathEnds_applyLayer hS h₁ hpE)).ne_nil
    have h₁' : S.applyLayer (e :: q) l.1 l.2 = some (e' :: q') := he ▸ h₁
    have hr₁' : S.walk x (e' :: q') = some z := he ▸ hr₁
    have h₂' : S.targetFrom (e' :: q') (l' :: ls) = some r := he ▸ h₂
    rw [Signature.BicatInterp.evalFrom_cons,
      layerReading_comp_evalFrom_congr hS (I.reading hS) he _ h₁' hp _ hr₁' _ h₂']
    have hL := I.hasRoundType_layer hS hpE h₁'
    have hR := I.hasRoundType_layers hS (S.pathEnds_applyLayer hS h₁' hpE) h₂'
    have hc := hL.pastable hR (.refl _) (I.dim_path (S.isPath_of_pathEnds hpE))
    have heq : I.layers e q (l :: l' :: ls) =
        (I.layer e q l).paste (I.layers e' q' (l' :: ls)) 1 hc := by
      simp only [layers, h₁']
      exact PastingDiagram.pasteOr_of hc
    have hdL : (I.layer e q l).dim ≤ 2 := (hL.dim_eq.trans (congrArg (· + 1)
      (I.dim_path (S.isPath_of_pathEnds hpE)))).le
    have hdR : (I.layers e' q' (l' :: ls)).dim ≤ 2 := (hR.dim_eq.trans (congrArg (· + 1)
      (I.dim_path (S.isPath_of_pathEnds (S.pathEnds_applyLayer hS h₁' hpE))))).le
    have hdP : ((I.layer e q l).paste (I.layers e' q' (l' :: ls)) 1 hc).dim ≤ 2 := heq ▸ hd
    refine (PastingDiagram.nerveComposite_congr (PastingDiagram.equiv_of_eq heq) hd hdP).trans
      ((PastingDiagram.nerveComposite_pasteAlong_one _ _ _ _ hdL hdR hdP
        (I.nerveComposite_layer hS h₁' hp hr₁' hdL)
        (nerveComposite_layers hr₁' h₂' hr hdR)).trans ?_)
    exact PathCell.ofHom_comp _ _

theorem nerveComposite_diagram {d : Diagram S.Pt S.Ed S.Ce} {x y : S.Pt}
    (hx : S.pathEnds d.source = some (x, y)) {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hd : (I.diagram d hsrc).dim ≤ 2) :
    (I.diagram d hsrc).nerveComposite hd = PathCell.ofHom (I.reading hS).label
      (S.toPath d.source (S.walk_of_pathEnds hx))
      (S.toPath q (S.walk_of_pathEnds (S.pathEnds_target hS hq hx)))
      ((I.reading hS).evalB d hx hq) := by
  obtain ⟨_ | ⟨e, p⟩, ls⟩ := d
  · exact absurd rfl hsrc
  exact I.nerveComposite_layers hS _ _ _ hd

end Layered.Signature.Interp

namespace Layered.RelSignature

variable {S : RelSignature.{v'}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

theorem target_completeSide_of_relationApply (hS : S.WellFormed) {d d' : Diagram S.Pt S.Ed S.Ce}
    {r : S.Rel} {h o : ℕ} (hd : S.relationApply d r h o = some d') (α : Bool)
    {q : List (Edge S.Pt S.Ed)} (hq : S.target (cond α d' d) = some q) :
    S.target (S.completeSide (cond α d' d) r α h o) = some q := by
  unfold completeSide
  split_ifs with hr
  · rw [relationApply] at hd
    split at hd
    · exact absurd hd (by simp only [reduceCtorEq, not_false_eq_true])
    rename_i p hp
    split_ifs at hd with hc₁
    dsimp only at hd
    split_ifs at hd with hc₂
    obtain ⟨-, hlen, -, hsseg⟩ := hc₁
    obtain rfl := (Option.some.inj hd).symm
    have htake : (cond α ⟨d.source, d.layers.take h ++
        (S.relTarget r).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ d).layers.take h =
        d.layers.take h := by
      cases α
      · rfl
      · dsimp only [cond_true]
        rw [List.append_assoc, List.take_append_of_le_length (by simp; omega),
          List.take_take, min_self]
    have hp' : S.targetFrom (cond α ⟨d.source, d.layers.take h ++
        (S.relTarget r).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ d).source
        ((cond α ⟨d.source, d.layers.take h ++
        (S.relTarget r).layers.map (fun l => (l.1, l.2 + o)) ++
          d.layers.drop (h + (S.relSource r).layers.length)⟩ d).layers.take h) = some p := by
      rw [htake]
      cases α <;> exact hp
    have hu : (S.applyLayer p (.unit (S.side r α).source : Cell S.Pt S.Ed S.Ce) o).isSome := by
      rw [source_side hS r α, Signature.applyLayer,
        if_pos ⟨(isPath_source_side hS r).ne_nil, hsseg⟩]
      rfl
    have hpath := S.isPath_source_of_target hq
    rw [Signature.target, if_pos hpath, ← List.take_append_drop h (cond α _ d).layers] at hq
    rw [Signature.target, if_pos hpath]
    exact (S.targetFrom_append_cons_unit hp' hu).trans hq
  · exact hq

variable {B : Type u} [Bicategory.{w, v} B] {hS : S.WellFormed}
  (I : S.Interp hS (bicategoryNerve.{w, v, u} B))

omit [DecidableEq S.Ce] in
theorem nerveComposite_completeSide {d : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {α : Bool} {h o : ℕ}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target (S.completeSide d r α h o) = some q)
    (hc : (S.completeSide d r α h o).source ≠ []) (hsrc : d.source ≠ [])
    (hd : (I.diagram (S.completeSide d r α h o) hc).dim ≤ 2) (hd' : (I.diagram d hsrc).dim ≤ 2) :
    (I.diagram (S.completeSide d r α h o) hc).nerveComposite hd =
      (I.diagram d hsrc).nerveComposite hd' := by
  obtain ⟨x, y, hx⟩ := S.exists_pathEnds_of_isPath (S.isPath_source_of_target hq)
  have hx' : S.pathEnds d.source = some (x, y) :=
    (congrArg S.pathEnds (S.source_completeSide d r α h o)).symm.trans hx
  rw [I.toInterp.nerveComposite_diagram hS.1 hx hq, I.toInterp.nerveComposite_diagram hS.1 hx'
    (S.target_of_target_completeSide hq), evalB_completeSide]
  exact PathCell.ofHom_eqToHom_comp (S.toPath_congr (S.source_completeSide d r α h o) _ _) _

theorem nerveComposite_eq_of_relationApply {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ [])
    (hdd : (I.diagram d hsrc).dim ≤ 2) (hdd' : (I.diagram d' hsrc').dim ≤ 2) :
    (I.diagram d hsrc).nerveComposite hdd = (I.diagram d' hsrc').nerveComposite hdd' := by
  obtain ⟨hq, hq', -⟩ := isSome_target_and_source_of_relationApply hd
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hq
  obtain ⟨q', hq'⟩ := Option.isSome_iff_exists.1 hq'
  have hc (α : Bool) : (S.completeSide (cond α d' d) r α h o).source ≠ [] := by
    rw [source_completeSide]
    cases α
    exacts [hsrc, hsrc']
  have ht₀ := target_completeSide_of_relationApply hS hd false hq
  have ht₁ := target_completeSide_of_relationApply hS hd true hq'
  have hb₀ := (I.toInterp.dim_diagram hS.1 ht₀ (hc false)).le
  have hb₁ := (I.toInterp.dim_diagram hS.1 ht₁ (hc true)).le
  have hB₀ := PastingDiagram.nerveComposite_congr
    (I.equiv_boundary_relationStep hd false (hc false))
    ((I.relationStep d r h o).shape.dimension_boundary_le 2 false) hb₀
  have hB₁ := PastingDiagram.nerveComposite_congr (I.equiv_boundary_relationStep hd true (hc true))
    ((I.relationStep d r h o).shape.dimension_boundary_le 2 true) hb₁
  exact ((nerveComposite_completeSide I ht₀ (hc false) hsrc hb₀ hdd).symm.trans hB₀.symm).trans
    ((PastingDiagram.nerveComposite_boundary_eq _).trans (hB₁.trans
      (nerveComposite_completeSide I ht₁ (hc true) hsrc' hb₁ hdd')))

omit [DecidableEq S.Ce] in
theorem nerveComposite_eq_of_unitApply (m : UnitMove) {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ}
    (hd : S.unitApply m d h = some d') {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ []) (hdd : (I.diagram d hsrc).dim ≤ 2)
    (hdd' : (I.diagram d' hsrc').dim ≤ 2) :
    (I.diagram d hsrc).nerveComposite hdd = (I.diagram d' hsrc').nerveComposite hdd' := by
  obtain ⟨x, y, hx⟩ := S.exists_pathEnds_of_isPath (S.isPath_source_of_target hq)
  rw [I.toInterp.nerveComposite_diagram hS.1 hx hq, I.toInterp.nerveComposite_diagram hS.1
    (S.pathEnds_source_unitApply hd hx) ((S.target_unitApply hS.1 hd).trans hq),
    Signature.BicatInterp.evalB_eq_of_unitApply _ m hd]
  exact PathCell.ofHom_eqToHom_comp (S.toPath_congr (S.source_unitApply hd).symm _ _) _

theorem Link.nerveComposite_eq {d d' : Diagram S.Pt S.Ed S.Ce} (l : S.Link d d')
    (hq : (S.target d).isSome) (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ [])
    (hdd : (I.diagram d hsrc).dim ≤ 2) (hdd' : (I.diagram d' hsrc').dim ≤ 2) :
    (I.diagram d hsrc).nerveComposite hdd = (I.diagram d' hsrc').nerveComposite hdd' := by
  obtain ⟨q, hq⟩ := Option.isSome_iff_exists.1 hq
  cases l with
  | relation r h o hd => exact nerveComposite_eq_of_relationApply I hd hsrc hsrc' hdd hdd'
  | relationBackward r h o _ hd =>
    exact (nerveComposite_eq_of_relationApply I hd hsrc' hsrc hdd' hdd).symm
  | identification h hd =>
    exact PastingDiagram.nerveComposite_congr
      (I.toInterp.equiv_diagram_swap hS.1 hd hq hsrc hsrc') hdd hdd'
  | unit m forward h hd =>
    cases forward
    · have hq' : S.target d' = some q := (S.target_unitApply hS.1 hd).symm.trans hq
      exact (nerveComposite_eq_of_unitApply I m hd hq' hsrc' hsrc hdd' hdd).symm
    · exact nerveComposite_eq_of_unitApply I m hd hq hsrc hsrc' hdd hdd'

theorem RewriteChain.nerveComposite_eq {d d' : Diagram S.Pt S.Ed S.Ce} (p : S.RewriteChain d d')
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hsrc' : d'.source ≠ []) (hdd : (I.diagram d hsrc).dim ≤ 2)
    (hdd' : (I.diagram d' hsrc').dim ≤ 2) :
    (I.diagram d hsrc).nerveComposite hdd = (I.diagram d' hsrc').nerveComposite hdd' := by
  have key : ∀ {d d' : Diagram S.Pt S.Ed S.Ce}, S.RewriteChain d d' → (S.target d).isSome →
      ∀ (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ []) (hdd : (I.diagram d hsrc).dim ≤ 2)
        (hdd' : (I.diagram d' hsrc').dim ≤ 2),
        (I.diagram d hsrc).nerveComposite hdd = (I.diagram d' hsrc').nerveComposite hdd' := by
    intro d d' p
    induction p with
    | refl d => intro _ _ _ _ _; rfl
    | cons l p ih =>
      intro hq hsrc hsrc' hdd hdd'
      have hq₁ := l.isSome_target_of_isSome hS.1 hq
      obtain ⟨q₁, hq₁'⟩ := Option.isSome_iff_exists.1 hq₁
      have hsrc₁ := (S.isPath_source_of_target hq₁').ne_nil
      have hdd₁ := (I.toInterp.dim_diagram hS.1 hq₁' hsrc₁).le
      exact (l.nerveComposite_eq I hq hsrc hsrc₁ hdd hdd₁).trans (ih hq₁ hsrc₁ hsrc' hdd₁ hdd')
  exact key p (by rw [hq]; rfl) hsrc hsrc' hdd hdd'

end Layered.RelSignature

end Atoms.Diagrammatic

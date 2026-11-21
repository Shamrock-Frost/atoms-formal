import Atoms.Diagrammatic.Rewriting.LayeredLocation

open CategoryTheory Atoms.Shape Atoms.Diagrammatic.PastingDiagram

universe u v

namespace Atoms.Diagrammatic.Layered

namespace RelSignature

variable {S : RelSignature.{v}} [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce]

namespace Interp

variable {hS : S.WellFormed} {X : DiagSet.{u}} (I : S.Interp hS X)

omit [DecidableEq S.Ce] in
private theorem pos_dim_roundDiagram {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) :
    0 < (I.toInterp.roundDiagram hS.1 hq hsrc).dim := by
  have hdx : (I.toInterp.roundDiagram hS.1 hq hsrc).dim = 2 :=
    I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc
  rw [hdx]
  exact Nat.two_pos

omit [DecidableEq S.Ce] in
private theorem isRewritableSubmolecule_roundDiagram {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ []) :
    (((I.toInterp.roundDiagram hS.1 hq hsrc).boundary
      ((I.toInterp.roundDiagram hS.1 hq hsrc).dim - 1) true).shape.ogp).IsRewritableSubmolecule
      (Within.refl _).image ⊤ :=
  isRewritableSubmolecule_image_refl (isRound_boundary_of_isRound
    (I.toInterp.roundDiagram hS.1 hq hsrc).isRound _ _)

noncomputable def targetUnitor {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) : RoundPastingDiagram X :=
  unitorRound (I.toInterp.roundDiagram hS.1 hq hsrc) (I.pos_dim_roundDiagram hq hsrc) true
    (Within.refl _) (I.isRewritableSubmolecule_roundDiagram hq hsrc)

noncomputable def targetUnitorReverse {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) : RoundPastingDiagram X :=
  unitorReverseRound (I.toInterp.roundDiagram hS.1 hq hsrc) (I.pos_dim_roundDiagram hq hsrc) true
    (Within.refl _) (I.isRewritableSubmolecule_roundDiagram hq hsrc)

omit [DecidableEq S.Pt] [DecidableEq S.Ed] [DecidableEq S.Ce] in
private theorem equiv_unitData_refl (x : RoundPastingDiagram X) (hd : 0 < x.dim)
    (hj : ((x.boundary (x.dim - 1) true).shape.ogp).IsRewritableSubmolecule (Within.refl _).image ⊤)
    {k : ℕ} (hk : x.dim - 1 = k) (hp : x.toPastingDiagram.Pastable (x.boundary k true).unit k) :
    (unitData x hd true (Within.refl _) hj).pasting.Equiv
      (x.toPastingDiagram.paste (x.boundary k true).unit k hp) := by
  subst hk
  exact (equiv_paste_pasteAtBoundary _ x.toPastingDiagram (x.dim - 1) true (Within.refl _)
    hj.isSubmoleculeOf (Within.image_refl _) (boundary_unit (dim_boundary _ (by omega) true) false)
    hp).symm

omit [DecidableEq S.Ce] in
private theorem equiv_unitData_roundDiagram {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q) :
    (unitData (I.toInterp.roundDiagram hS.1 hq hsrc) (I.pos_dim_roundDiagram hq hsrc) true
      (Within.refl _) (I.isRewritableSubmolecule_roundDiagram hq hsrc)).pasting.Equiv
      (I.toInterp.roundDiagram hS.1 hq₁ hsrc).toPastingDiagram := by
  have hqp := S.isPath_target hS.1 hq
  have hdx : (I.toInterp.roundDiagram hS.1 hq hsrc).dim = 2 :=
    I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc
  have hxb : ((I.toInterp.roundDiagram hS.1 hq hsrc).boundary 1 true).Equiv
      (I.toInterp.path q hqp.ne_nil) :=
    (I.toInterp.hasRoundType_roundDiagram hS.1 hq hsrc).equiv_boundary_cond
      (I.toInterp.dim_path (S.isPath_source_of_target hq)) true
  have hqu : S.target ⟨q, [(Cell.unit q, 0)]⟩ = some q :=
    S.target_singleton (l := (.unit q, 0)) hqp (S.applyLayer_unit_self hqp.ne_nil)
  obtain ⟨h₁, e₁⟩ := I.toInterp.equiv_diagram_append hS.1 (d := d.unitFirst)
    (d' := ⟨q, [(.unit q, 0)]⟩) ((S.target_unitFirst _).trans hq) rfl hsrc hqp.ne_nil
    (List.cons_ne_nil _ _) (List.cons_ne_nil _ _) (by rw [hqu]; rfl)
  have eu := PastingDiagram.equiv_of_eq (I.toInterp.diagram_unit_singleton hqp.ne_nil)
  have hp : (I.toInterp.roundDiagram hS.1 hq hsrc).toPastingDiagram.Pastable
      ((I.toInterp.roundDiagram hS.1 hq hsrc).boundary 1 true).unit 1 :=
    pastable_unit_boundary (by omega)
  refine (equiv_unitData_refl _ _ _ (by omega) hp).trans
    ((Equiv.paste (.refl _) (hxb.unit.trans eu.symm) hp h₁).trans
      (e₁.symm.trans (PastingDiagram.equiv_of_eq (I.toInterp.diagram_congr ?_ _ _))))
  exact congrArg (Diagram.mk d.source) (by simp [Diagram.unitFirst])

omit [DecidableEq S.Ce] in
theorem hasRoundType_targetUnitor {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q) :
    HasRoundType (I.targetUnitor hq hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq₁ hsrc) (I.toInterp.roundDiagram hS.1 hq hsrc) := by
  have hb := hasBdry_unitorRound (I.toInterp.roundDiagram hS.1 hq hsrc)
    (I.pos_dim_roundDiagram hq hsrc) true (Within.refl _)
    (I.isRewritableSubmolecule_roundDiagram hq hsrc)
  have hdx : (I.toInterp.roundDiagram hS.1 hq hsrc).dim = 2 :=
    I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc
  have hn : (I.toInterp.roundDiagram hS.1 hq hsrc).dim - 1 + 1 = 2 := by rw [hdx]
  rw [hn] at hb
  have e := I.equiv_unitData_roundDiagram hq hsrc hq₁
  exact .of_equiv_boundary
    (I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq₁) hsrc) hdx hb.dim_h
    fun β => by cases β; exacts [hb.side.trans e, hb.other]

omit [DecidableEq S.Ce] in
theorem hasRoundType_targetUnitorReverse {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q) :
    HasRoundType (I.targetUnitorReverse hq hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq₁ hsrc) := by
  have hb := hasBdry_unitorReverseRound (I.toInterp.roundDiagram hS.1 hq hsrc)
    (I.pos_dim_roundDiagram hq hsrc) true (Within.refl _)
    (I.isRewritableSubmolecule_roundDiagram hq hsrc)
  have hdx : (I.toInterp.roundDiagram hS.1 hq hsrc).dim = 2 :=
    I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc
  have hn : (I.toInterp.roundDiagram hS.1 hq hsrc).dim - 1 + 1 = 2 := by rw [hdx]
  rw [hn] at hb
  have e := I.equiv_unitData_roundDiagram hq hsrc hq₁
  exact .of_equiv_boundary hdx
    (I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq₁) hsrc) hb.dim_h
    fun β => by cases β; exacts [hb.other, hb.side.trans e]

omit [DecidableEq S.Ce] in
private theorem targetUnitor_mem_equivalences {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ []) :
    I.targetUnitor hq hsrc ∈ equivalences X ∧ I.targetUnitorReverse hq hsrc ∈ equivalences X :=
  ⟨mem_equivalences_of_isDegenerate _ (isDegenerate_unitorRound _ _ _ _ _),
    mem_equivalences_of_isDegenerate _ (isDegenerate_unitorReverseRound _ _ _ _ _)⟩

omit [DecidableEq S.Ce] in
private theorem sideLayers_spec {r : S.Rel} {o : ℕ} {L R t : List (Edge S.Pt S.Ed)}
    {a x y b : S.Pt} (hL : L.length = o) (ht : S.target (S.relSource r) = some t)
    (hLw : S.walk a L = some x) (hs : S.pathEnds (S.relSource r).source = some (x, y))
    (hRw : S.walk y R = some b) (β : Bool) (hM : L ++ (S.relSource r).source ++ R ≠ []) :
    (I.toInterp.diagram ⟨L ++ (S.relSource r).source ++ R, sideLayers r o β⟩ hM).Equiv
      (I.whisker false L (I.whisker true R (sideRound I.toInterp hS r β).toPastingDiagram)) := by
  set J := I.toInterp
  have hpsrc := isPath_source_side hS r
  have hsrcβ := source_side hS r β
  have heta : S.side r β = ⟨(S.relSource r).source, (S.side r β).layers⟩ := by
    have : S.side r β = ⟨(S.side r β).source, (S.side r β).layers⟩ := rfl
    rw [hsrcβ] at this
    exact this
  have hside : S.targetFrom (S.relSource r).source (S.side r β).layers = some t := by
    have := (target_side hS r β).trans ht
    rw [Signature.target, if_pos (by rw [hsrcβ]; exact hpsrc), hsrcβ] at this
    exact this
  unfold sideLayers
  split_ifs with hl
  · have hts : t = (S.relSource r).source := by
      rw [hl] at hside
      exact (Option.some.inj hside).symm
    subst hts
    rw [hsrcβ]
    have hap : S.applyLayer (L ++ (S.relSource r).source ++ R) (.unit (S.relSource r).source) o =
        some (L ++ (S.relSource r).source ++ R) :=
      S.applyLayer_eq_some_iff.2 ⟨hpsrc.ne_nil, L, R, rfl, hL, rfl⟩
    rw [J.diagram_singleton hM rfl hL (by exact hpsrc.ne_nil) (J.pathCons (.unit a) []).unit]
    obtain ⟨e, q', he⟩ := List.exists_cons_of_ne_nil hpsrc.ne_nil
    have h₁ : J.cellDiagram (J.pathCons (.unit a) []).unit (.unit (S.relSource r).source) =
        (J.pathCons e q').unit := by
      rw [he]
      rfl
    have h₂ : (sideRound J hS r β).toPastingDiagram = (J.pathCons e q').unit :=
      (J.diagram_congr (d' := ⟨e :: q', []⟩) (heta.trans (by rw [hl, he])) _
        (List.cons_ne_nil e q')).trans rfl
    rw [h₁, h₂]
  · have hw : (⟨L ++ (S.relSource r).source ++ R, (S.side r β).layers.map
        (fun l => (l.1, l.2 + o))⟩ : Diagram S.Pt S.Ed S.Ce) = Diagram.whisker false L
          (Diagram.whisker true R ⟨(S.relSource r).source, (S.side r β).layers⟩) := by
      subst hL
      simp [Diagram.whisker]
    have hne : (Diagram.whisker false L (Diagram.whisker true R
        ⟨(S.relSource r).source, (S.side r β).layers⟩)).source ≠ [] := by
      rw [← hw]; exact hM
    refine (PastingDiagram.equiv_of_eq (J.diagram_congr hw _ hne)).trans
      ((J.equiv_diagram_whisker_whisker hS.1 hs hLw hRw hl hside hne).trans ?_)
    exact PastingDiagram.equiv_of_eq (congrArg (fun z => J.whisker false L (J.whisker true R z))
      (J.diagram_congr heta.symm _ _))

omit [DecidableEq S.Ce] in
private theorem inHom_sideRound {r : S.Rel} {t : List (Edge S.Pt S.Ed)}
    (ht : S.target (S.relSource r) = some t) (β : Bool) :
    InHom ⟨1, I.toInterp.path _ (isPath_source_side hS r).ne_nil,
      I.toInterp.path t (S.isPath_target hS.1 ht).ne_nil⟩
      (sideRound I.toInterp hS r β).toPastingDiagram := by
  have hu := hasRoundType_side I.toInterp hS r ht β
  have hd1 : (I.toInterp.pathRound _ (isPath_source_side hS r)).dim = 1 :=
    I.dim_path (isPath_source_side hS r)
  exact ⟨by rw [hu.dim_eq, hd1]; exact Nat.lt_succ_self 1, hu.equiv_boundary_cond hd1 false,
    hu.equiv_boundary_cond hd1 true⟩

private noncomputable abbrev stepBelow (d : Diagram S.Pt S.Ed S.Ce) (h : ℕ)
    (hsrc : d.source ≠ []) : PastingDiagram X :=
  I.toInterp.diagram ⟨d.source, (.unit d.source, 0) :: d.layers.take h⟩ hsrc

private noncomputable abbrev stepAbove (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (h o : ℕ)
    (q : List (Edge S.Pt S.Ed)) : PastingDiagram X :=
  I.toInterp.diagram
    ⟨pathBefore d h o ++ (S.target (S.relSource r)).getD [] ++ pathAfter d r h o,
      d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩
    (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_right_ne_nil _
      (getD_target_relSource_ne_nil hS r)) _)

private noncomputable def stepCtx (d : Diagram S.Pt S.Ed S.Ce) (r : S.Rel) (h o : ℕ)
    (q : List (Edge S.Pt S.Ed)) (hsrc : d.source ≠ []) : CtxExpr X :=
  .comp (CtxExpr.paste true (I.stepAbove d r h o q) 1)
    (I.toPathInterp.segmentCtx (I.stepBelow d h hsrc) (pathBefore d h o) (pathAfter d r h o))

private theorem stepBelow_spec {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) {a m n b : S.Pt}
    (hs : S.pathEnds (S.relSource r).source = some (m, n))
    (hLw : S.walk a (pathBefore d h o) = some m) (hRw : S.walk n (pathAfter d r h o) = some b) :
    (I.stepBelow d h hsrc).IsRound ∧ (I.stepBelow d h hsrc).dim = 2 ∧
      ((I.stepBelow d h hsrc).boundary 1 true).Equiv (I.toInterp.path
        (pathBefore d h o ++ (S.relSource r).source ++ pathAfter d r h o)
        (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_right_ne_nil _
          (isPath_source_side hS r).ne_nil) _)) ∧
      ((I.stepBelow d h hsrc).boundary 1 true).Equiv (I.toInterp.whisker false (pathBefore d h o)
        (I.toInterp.whisker true (pathAfter d r h o)
          (I.toInterp.path _ (isPath_source_side hS r).ne_nil))) ∧
      S.target ⟨d.source, (.unit d.source, 0) :: d.layers.take h⟩ =
        some (pathBefore d h o ++ (S.relSource r).source ++ pathAfter d r h o) := by
  set J := I.toInterp
  obtain ⟨hA, -, -⟩ := relationApply_occurrence hS hd
  have hpsrc := isPath_source_side hS r
  have hpath := S.isPath_source_of_target hq
  have htc := (S.target_unitFirst ⟨d.source, d.layers.take h⟩).trans
    (S.target_mk_of_targetFrom hpath hA)
  have hcb' := (J.hasRoundType_diagram hS.1 htc hsrc).equiv_boundary_cond (J.dim_path hpath) true
  refine ⟨J.isRound_diagram_of_first hS.1 htc hsrc rfl rfl, J.dim_diagram hS.1 htc hsrc, hcb',
    hcb'.trans ?_, htc⟩
  have e₁ := J.whisker_path true hpsrc.ne_nil hs (c := b) hRw (by simp [hpsrc.ne_nil])
  have hsp := J.spans_of_hasRoundType (J.hasRoundType_path hpsrc.ne_nil hs)
  have e₂ := J.whisker_path false (q := (S.relSource r).source ++ pathAfter d r h o)
    (by simp [hpsrc.ne_nil]) (S.pathEnds_whisker true hs hRw) (c := a) hLw (by simp [hpsrc.ne_nil])
  exact (PastingDiagram.equiv_of_eq (J.path_congr (by simp) _ _)).trans
    ((J.whisker_equiv false (hsp.whisker true hRw) e₁ hLw).trans e₂).symm

private theorem stepAbove_spec {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q t : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (ht : S.target (S.relSource r) = some t) :
    (I.stepAbove d r h o q).IsRound ∧ (I.stepAbove d r h o q).dim = 2 ∧
      ((I.stepAbove d r h o q).boundary 1 false).Equiv (I.toInterp.path
        (pathBefore d h o ++ t ++ pathAfter d r h o)
        (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_right_ne_nil _
          (S.isPath_target hS.1 ht).ne_nil) _)) ∧
      S.target ⟨pathBefore d h o ++ t ++ pathAfter d r h o,
        d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩ = some q ∧
      I.stepAbove d r h o q = I.toInterp.diagram ⟨pathBefore d h o ++ t ++ pathAfter d r h o,
        d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩
        (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_right_ne_nil _
          (S.isPath_target hS.1 ht).ne_nil) _) := by
  set J := I.toInterp
  obtain ⟨hA, hL, -⟩ := relationApply_occurrence hS hd
  obtain ⟨a, b, hab⟩ := S.exists_pathEnds_of_isPath (S.isPath_source_of_target hq)
  have hpt := S.isPath_of_pathEnds (S.pathEnds_targetFrom hS.1
    (by rw [S.targetFrom_append, hA, Option.bind_some]; exact (targetFrom_side hS hL ht false))
    hab)
  have hty : S.target ⟨pathBefore d h o ++ t ++ pathAfter d r h o,
      d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩ = some q := by
    refine S.target_mk_of_targetFrom hpt ?_
    rw [S.targetFrom_append, targetFrom_above hS hd hq ht, Option.bind_some, Signature.targetFrom,
      S.applyLayer_unit_self (S.isPath_target hS.1 hq).ne_nil, Option.bind_some]
    rfl
  have he : I.stepAbove d r h o q = J.diagram ⟨pathBefore d h o ++ t ++ pathAfter d r h o,
      d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩ hpt.ne_nil :=
    J.diagram_congr (by rw [ht, Option.getD_some]) _ _
  rw [he]
  exact ⟨J.isRound_diagram_of_last hS.1 hty hpt.ne_nil (l := (.unit q, 0)) rfl rfl,
    J.dim_diagram hS.1 hty hpt.ne_nil,
    (J.hasRoundType_diagram hS.1 hty hpt.ne_nil).equiv_boundary_cond (J.dim_path hpt) false, hty,
    rfl⟩

private theorem stepCtx_side {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q t : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (ht : S.target (S.relSource r) = some t)
    {a m n b : S.Pt} (hab : S.pathEnds d.source = some (a, b))
    (hs : S.pathEnds (S.relSource r).source = some (m, n))
    (hLw : S.walk a (pathBefore d h o) = some m) (hRw : S.walk n (pathAfter d r h o) = some b)
    (β : Bool) :
    ∃ hp : (I.stepBelow d h hsrc).Pastable (I.toInterp.whisker false (pathBefore d h o)
      (I.toInterp.whisker true (pathAfter d r h o)
        (sideRound I.toInterp hS r β).toPastingDiagram)) 1,
      ((I.toPathInterp.segmentCtx (I.stepBelow d h hsrc) (pathBefore d h o)
        (pathAfter d r h o)).app (sideRound I.toInterp hS r β).toPastingDiagram).Equiv
        ((I.stepBelow d h hsrc).paste _ 1 hp) ∧
      (((I.stepBelow d h hsrc).paste _ 1 hp).boundary 1 true).Equiv (I.toInterp.path
        (pathBefore d h o ++ t ++ pathAfter d r h o)
        (List.append_ne_nil_of_left_ne_nil (List.append_ne_nil_of_right_ne_nil _
          (S.isPath_target hS.1 ht).ne_nil) _)) ∧
      ∃ hy : ((I.stepBelow d h hsrc).paste _ 1 hp).Pastable (I.stepAbove d r h o q) 1,
        (((I.stepBelow d h hsrc).paste _ 1 hp).paste _ 1 hy).Equiv
          (I.toInterp.diagram ⟨d.source, (.unit d.source, 0) :: (d.layers.take h ++
            sideLayers r o β ++ d.layers.drop (h + (S.relSource r).layers.length) ++
              [(.unit q, 0)])⟩ hsrc) := by
  set J := I.toInterp
  obtain ⟨hA, hL, -⟩ := relationApply_occurrence hS hd
  have hpsrc := isPath_source_side hS r
  have hpath := S.isPath_source_of_target hq
  have hs' : S.pathEnds t = some (m, n) := S.pathEnds_target hS.1 ht hs
  obtain ⟨hc, hdc, hcb', hcb, htc⟩ := I.stepBelow_spec hd hq hsrc hs hLw hRw
  obtain ⟨-, -, -, hty, hye⟩ := I.stepAbove_spec hd hq ht
  obtain ⟨_, -, -, happ₁⟩ := J.toPathInterp.typed_segmentCtx hc hdc hs hs' hLw hRw hcb
  have hLsR := S.isPath_of_pathEnds (S.pathEnds_targetFrom hS.1 hA hab)
  have htM : S.target ⟨d.source, (.unit d.source, 0) :: d.layers.take h ++ sideLayers r o β⟩ =
      some (pathBefore d h o ++ t ++ pathAfter d r h o) :=
    (S.target_unitFirst ⟨d.source, d.layers.take h ++ sideLayers r o β⟩).trans
      (S.target_mk_of_targetFrom hpath (by
        rw [S.targetFrom_append, hA, Option.bind_some, targetFrom_sideLayers hS hL ht β]))
  have hu := hasRoundType_side J hS r ht β
  have hp := J.toPathInterp.pastable_whisker hdc hs hs' hLw hRw hu hcb'
  have hspu := (J.spans_of_hasRoundType (J.hasRoundType_path hpsrc.ne_nil hs)).of_hasRoundType hu
  obtain ⟨h₁, e₁⟩ := J.equiv_diagram_append hS.1 (d := ⟨d.source, (.unit d.source, 0) ::
      d.layers.take h⟩) (d' := ⟨_, sideLayers r o β⟩) htc rfl hsrc hLsR.ne_nil
    (List.cons_ne_nil _ _) (sideLayers_ne_nil r o β)
    (by rw [S.target_mk_of_targetFrom hLsR (targetFrom_sideLayers hS hL ht β)]; rfl)
  have E₁ := (Equiv.paste (.refl _) (I.sideLayers_spec hL ht hLw hs hRw β hLsR.ne_nil) h₁
    hp).symm.trans e₁.symm
  obtain ⟨h₂, e₂⟩ := J.equiv_diagram_append hS.1 (d := ⟨d.source, (.unit d.source, 0) ::
      d.layers.take h ++ sideLayers r o β⟩)
    (d' := ⟨pathBefore d h o ++ t ++ pathAfter d r h o,
      d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩) htM rfl hsrc
    (S.isPath_target hS.1 htM).ne_nil (List.cons_ne_nil _ _) (by simp) (by rw [hty]; rfl)
  rw [hye]
  refine ⟨hp, (happ₁ _ hspu).trans (CtxExpr.paste_app false hp),
    (E₁.boundary 1 true).trans ((J.hasRoundType_diagram hS.1 htM hsrc).equiv_boundary_cond
      (J.dim_path hpath) true), h₂.of_equiv E₁.symm (.refl _), ?_⟩
  refine (Equiv.paste E₁ (.refl _) _ h₂).trans (e₂.symm.trans ?_)
  exact PastingDiagram.equiv_of_eq (J.diagram_congr (congrArg (Diagram.mk d.source) (by simp)) _ _)

private theorem stepCtx_spec {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q t : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (ht : S.target (S.relSource r) = some t) :
    ∃ H' : PdHom X, (I.stepCtx d r h o q hsrc).Typed Set.univ True
      ⟨1, I.toInterp.path _ (isPath_source_side hS r).ne_nil,
        I.toInterp.path t (S.isPath_target hS.1 ht).ne_nil⟩ H' ∧
      IsRoundCtx ⟨1, I.toInterp.path _ (isPath_source_side hS r).ne_nil,
        I.toInterp.path t (S.isPath_target hS.1 ht).ne_nil⟩ (I.stepCtx d r h o q hsrc) ∧
      ∀ β, ((I.stepCtx d r h o q hsrc).app (sideRound I.toInterp hS r β).toPastingDiagram).Equiv
        (I.toInterp.diagram ⟨d.source, (.unit d.source, 0) ::
          (d.layers.take h ++ sideLayers r o β ++
            d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)])⟩ hsrc) := by
  have hab := (Option.some_get (S.isPath_source_of_target hq)).symm
  have hs := (Option.some_get (isPath_source_side hS r)).symm
  have hw := walk_beside hS hd (S.isPath_source_of_target hq)
  obtain ⟨hc, hdc, -, hcb, -⟩ := I.stepBelow_spec hd hq hsrc hs hw.1 hw.2
  obtain ⟨⟨k₁, v₁, w₁⟩, ht₁, hr₁, -⟩ := I.toPathInterp.typed_segmentCtx hc hdc hs
    (S.pathEnds_target hS.1 ht hs) hw.1 hw.2 hcb
  obtain rfl : k₁ = 1 := ht₁.k_eq
  obtain ⟨hy, hdy, hyb, -⟩ := I.stepAbove_spec hd hq ht
  have hb : (PdHom.side ⟨1, v₁, w₁⟩ true).Equiv ((I.stepAbove d r h o q).boundary 1 (!true)) := by
    obtain ⟨_, e₀, E₁, -⟩ := I.stepCtx_side hd hq hsrc ht hab hs hw.1 hw.2 false
    exact (ht₁.mapsInto _ (I.inHom_sideRound ht false)).target.symm.trans
      ((e₀.boundary 1 true).trans (E₁.trans hyb.symm))
  refine ⟨_, .comp ht₁ (CtxExpr.typed_paste true (u := ⟨_, hy⟩) (Set.mem_univ _) hdy hb),
    IsRoundCtx.comp_paste true ht₁ hy hdy hb, fun β => ?_⟩
  obtain ⟨_, e₀, -, _, E₂⟩ := I.stepCtx_side hd hq hsrc ht hab hs hw.1 hw.2 β
  exact (CtxExpr.app_equiv _ e₀).trans ((CtxExpr.paste_app true _).trans E₂)

omit [DecidableEq S.Ce] in
private theorem inHom_rel {r : S.Rel} {t : List (Edge S.Pt S.Ed)}
    (ht : S.target (S.relSource r) = some t) :
    InHom ⟨1, I.toInterp.path _ (isPath_source_side hS r).ne_nil,
        I.toInterp.path t (S.isPath_target hS.1 ht).ne_nil⟩ (PastingDiagram.ofCell (I.rel r).2) ∧
      (PastingDiagram.ofCell (I.rel r).2).dim = 3 ∧ ∀ β,
        ((PastingDiagram.ofCell (I.rel r).2).boundary 2 β).Equiv
          (sideRound I.toInterp hS r β).toPastingDiagram := by
  have hρ := I.hasRoundType_rel r
  have hin := I.inHom_sideRound ht
  have hd2 : (sideRound I.toInterp hS r false).dim = 2 :=
    (hasRoundType_side I.toInterp hS r ht false).dim_eq.trans
      (congrArg (· + 1) (I.toInterp.dim_path (isPath_source_side hS r)))
  have hdρ : (PastingDiagram.ofCell (I.rel r).2).dim = 3 :=
    hρ.dim_eq.trans (congrArg (· + 1) hd2)
  have eρ : ∀ β, ((PastingDiagram.ofCell (I.rel r).2).boundary 2 β).Equiv
      (sideRound I.toInterp hS r β).toPastingDiagram := fun β => by
    have := hρ.equiv_boundary_cond hd2 β
    cases β <;> exact this
  exact ⟨⟨by rw [hdρ]; exact Nat.one_lt_succ_succ 1,
    (equiv_boundary_boundary _ (Nat.lt_succ_self 1) false false).symm.trans
      (((eρ false).boundary 1 false).trans (hin false).source),
    (equiv_boundary_boundary _ (Nat.lt_succ_self 1) false true).symm.trans
      (((eρ false).boundary 1 true).trans (hin false).target)⟩, hdρ, eρ⟩

omit [DecidableEq S.Ce] in
private theorem sideRound_eq_unit {r : S.Rel} {β : Bool} (hl : (S.side r β).layers = []) :
    (sideRound I.toInterp hS r β).toPastingDiagram =
      (I.toInterp.path _ (isPath_source_side hS r).ne_nil).unit := by
  obtain ⟨e, q', he⟩ := List.exists_cons_of_ne_nil (isPath_source_side hS r).ne_nil
  have heta : S.side r β = ⟨(S.relSource r).source, (S.side r β).layers⟩ := by
    have : S.side r β = ⟨(S.side r β).source, (S.side r β).layers⟩ := rfl
    rw [source_side hS] at this
    exact this
  refine (I.toInterp.diagram_congr (d' := ⟨e :: q', []⟩) (heta.trans (by rw [hl, he])) _
    (List.cons_ne_nil e q')).trans ?_
  rw [I.toInterp.path_congr he _ (List.cons_ne_nil e q')]
  rfl

private noncomputable def stepUnitor {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) : PastingDiagram X :=
  (I.toPathInterp.segmentSpec (Option.some_get (isPath_source_side hS r)).symm
    (walk_beside hS hd (S.isPath_source_of_target hq)).1
    (walk_beside hS hd (S.isPath_source_of_target hq)).2).fam (I.stepBelow d h hsrc)

private theorem stepUnitor_spec {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) :
    ∃ hp : (I.stepBelow d h hsrc).Pastable (I.toPathInterp.unitWhisker (pathBefore d h o)
      (pathAfter d r h o) (isPath_source_side hS r).ne_nil) 1,
      ∃ hr : (I.stepUnitor hd hq hsrc).IsRound,
        (⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ∧
        (I.stepUnitor hd hq hsrc).IsDegenerate ∧ HasBdry false 2 (I.stepUnitor hd hq hsrc)
          ((I.stepBelow d h hsrc).paste _ 1 hp) (I.stepBelow d h hsrc) := by
  have hw := walk_beside hS hd (S.isPath_source_of_target hq)
  have hs := (Option.some_get (isPath_source_side hS r)).symm
  obtain ⟨hc, hdc, hcb', -⟩ := I.stepBelow_spec hd hq hsrc hs hw.1 hw.2
  have hp := I.toPathInterp.pastable_whisker hdc hs hs hw.1 hw.2
    (hasRoundType_unit (I.toInterp.pathRound _ (isPath_source_side hS r))) hcb'
  exact ⟨hp, I.toPathInterp.segmentUnitor_spec hc hdc hs hw.1 hw.2 hp⟩

private noncomputable def stepUnitorReverse {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) : PastingDiagram X :=
  (I.stepUnitor hd hq hsrc).reverse (by
    obtain ⟨-, -, -, h, -⟩ := I.stepUnitor_spec hd hq hsrc
    exact h)

private noncomputable def relationPieceSource {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) : PastingDiagram X :=
  if (S.side r false).layers = [] then
    ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app (I.stepUnitorReverse hd hq hsrc)).pasteOr
      ((I.stepCtx d r h o q hsrc).app (.ofCell (I.rel r).2)) 2
  else (I.stepCtx d r h o q hsrc).app (.ofCell (I.rel r).2)

noncomputable def relationPiece {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) : PastingDiagram X :=
  if (S.side r true).layers = [] then
    (I.relationPieceSource hd hq hsrc).pasteOr
      ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app (I.stepUnitor hd hq hsrc)) 2
  else I.relationPieceSource hd hq hsrc

private theorem isPiece_stepUnitor {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hts : (S.target (S.relSource r)).getD [] = (S.relSource r).source) (p : Prop) :
    IsPiece 1 p ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app (I.stepUnitor hd hq hsrc))
        ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app ((I.stepBelow d h hsrc).pasteOr
          (I.toPathInterp.unitWhisker (pathBefore d h o) (pathAfter d r h o)
            (isPath_source_side hS r).ne_nil) 1))
        (I.toInterp.diagram ⟨d.source, (.unit d.source, 0) :: (d.layers.take h ++
          d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)])⟩ hsrc) ∧
      IsPiece 1 p
        ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app (I.stepUnitorReverse hd hq hsrc))
        (I.toInterp.diagram ⟨d.source, (.unit d.source, 0) :: (d.layers.take h ++
          d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)])⟩ hsrc)
        ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app ((I.stepBelow d h hsrc).pasteOr
          (I.toPathInterp.unitWhisker (pathBefore d h o) (pathAfter d r h o)
            (isPath_source_side hS r).ne_nil) 1)) := by
  obtain ⟨hp, hr, hm, hdeg, hB⟩ := I.stepUnitor_spec hd hq hsrc
  have hw := walk_beside hS hd (S.isPath_source_of_target hq)
  obtain ⟨-, hdc, hcb', -, htc⟩ :=
    I.stepBelow_spec hd hq hsrc (Option.some_get (isPath_source_side hS r)).symm hw.1 hw.2
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  rw [ht, Option.getD_some] at hts
  subst hts
  obtain ⟨hy, hdy, hyb, hty, hye⟩ := I.stepAbove_spec hd hq ht
  have hb : (PdHom.side ⟨1, (I.stepBelow d h hsrc).boundary 1 false,
      (I.stepBelow d h hsrc).boundary 1 true⟩ true).Equiv
      ((I.stepAbove d r h o q).boundary 1 (!true)) := hcb'.trans hyb.symm
  obtain ⟨hT, hR⟩ := isRoundCtxOn_paste true _ hy hdy hb
  have hinH : ∀ {e a : PastingDiagram X} (β : Bool), HasBdry β 2 e (I.stepBelow d h hsrc) a →
      InHom ⟨1, (I.stepBelow d h hsrc).boundary 1 false,
        (I.stepBelow d h hsrc).boundary 1 true⟩ e :=
    fun β hB => ⟨by rw [hB.dim_h]; exact Nat.lt_succ_of_lt (Nat.lt_succ_self 1),
      (equiv_boundary_boundary _ (Nat.lt_succ_self 1) β false).symm.trans
        (hB.side.boundary 1 false),
      (equiv_boundary_boundary _ (Nat.lt_succ_self 1) β true).symm.trans
        (hB.side.boundary 1 true)⟩
  have hrev : ∀ α, (((I.stepUnitor hd hq hsrc).reverse hdeg).boundary 2 α).Equiv
      ((I.stepUnitor hd hq hsrc).boundary 2 (!α)) := fun α => by
    have e := boundary_reverse _ hdeg α
    rw [hB.dim_h] at e
    exact e
  have hB' : HasBdry false 2 ((I.stepUnitor hd hq hsrc).reverse hdeg) (I.stepBelow d h hsrc)
      ((I.stepBelow d h hsrc).paste _ 1 hp) :=
    ⟨by rw [dim_reverse, hB.dim_h], hB.dim_b, hB.dim_a, (hrev false).trans hB.other,
      (hrev true).trans hB.side⟩
  have hcy : (I.stepBelow d h hsrc).Pastable (I.stepAbove d r h o q) 1 :=
    ⟨hb, by rw [hdc, hdy]; omega⟩
  obtain ⟨h₂, e₂⟩ := I.toInterp.equiv_diagram_append hS.1 (d := ⟨d.source, (.unit d.source, 0) ::
      d.layers.take h⟩) (d' := ⟨pathBefore d h o ++ (S.relSource r).source ++ pathAfter d r h o,
      d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)]⟩) htc rfl hsrc
    (S.isPath_target hS.1 htc).ne_nil (List.cons_ne_nil _ _) (by simp) (by rw [hty]; rfl)
  have eC : ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app (I.stepBelow d h hsrc)).Equiv
      (I.toInterp.diagram ⟨d.source, (.unit d.source, 0) :: (d.layers.take h ++
        d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)])⟩ hsrc) :=
    (CtxExpr.paste_app true hcy).trans ((Equiv.paste (.refl _)
    (PastingDiagram.equiv_of_eq hye) hcy h₂).trans (e₂.symm.trans (PastingDiagram.equiv_of_eq
      (I.toInterp.diagram_congr (congrArg (Diagram.mk d.source) (by simp)) _ _))))
  have eW := PastingDiagram.equiv_of_eq (PastingDiagram.pasteOr_of hp).symm
  exact ⟨(isPiece_app hT hR (e := ⟨_, hr⟩) (fun _ => hm) (hinH true hB.symm) hB.dim_h).of_equiv
      (CtxExpr.app_equiv _ (hB.side.trans eW)) ((CtxExpr.app_equiv _ hB.other).trans eC),
    (isPiece_app hT hR (e := ⟨_, isRound_reverse hdeg hr⟩)
      (fun _ => mem_equivalences_of_isDegenerate _ (isDegenerate_reverse _ _)) (hinH false hB')
      hB'.dim_h).of_equiv ((CtxExpr.app_equiv _ hB'.side).trans eC)
      (CtxExpr.app_equiv _ (hB'.other.trans eW))⟩

private theorem isPiece_relationPiece {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q)
    (hq₁' : S.target ⟨d'.source, d'.layers ++ [(.unit q, 0)]⟩ = some q) :
    IsPiece 1 (IsEquivalence X (I.rel r).2) (I.relationPiece hd hq hsrc)
      (I.toInterp.roundDiagram hS.1 hq₁ hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq₁' hsrc').toPastingDiagram := by
  obtain ⟨-, -, hcd⟩ := relationApply_occurrence hS hd
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.1 (hS.2 r).isSome_target
  obtain ⟨_, hT, hR, happ⟩ := I.stepCtx_spec hd hq hsrc ht
  obtain ⟨hinρ, hdρ, eρ⟩ := I.inHom_rel ht
  have hP := isPiece_app hT hR (e := cellRound (I.rel r).2) (p := IsEquivalence X (I.rel r).2)
    id hinρ hdρ
  have hw := walk_beside hS hd (S.isPath_source_of_target hq)
  have hX : ∀ β (hs : (cond β d' d).source ≠ []) (hqβ : S.target ⟨(cond β d' d).source,
      (cond β d' d).layers ++ [(.unit q, 0)]⟩ = some q), (S.side r β).layers ≠ [] →
      ((I.stepCtx d r h o q hsrc).app ((PastingDiagram.ofCell (I.rel r).2).boundary 2 β)).Equiv
        (I.toInterp.roundDiagram hS.1 hqβ hs).toPastingDiagram := fun β hs hqβ hl =>
    (CtxExpr.app_equiv _ (eρ β)).trans ((happ β).trans (PastingDiagram.equiv_of_eq
      (I.toInterp.diagram_congr (by rw [hcd β]; simp [Diagram.unitFirst, sideLayers, hl]) _ _)))
  have hY : ∀ β, (S.side r β).layers = [] →
      ((I.stepCtx d r h o q hsrc).app ((PastingDiagram.ofCell (I.rel r).2).boundary 2 β)).Equiv
        ((CtxExpr.paste true (I.stepAbove d r h o q) 1).app ((I.stepBelow d h hsrc).pasteOr
          (I.toPathInterp.unitWhisker (pathBefore d h o) (pathAfter d r h o)
            (isPath_source_side hS r).ne_nil) 1)) := fun β hl => by
    obtain ⟨hp, e₀, -⟩ := I.stepCtx_side hd hq hsrc ht (Option.some_get _).symm
      (Option.some_get _).symm hw.1 hw.2 β
    refine (CtxExpr.app_equiv _ (eρ β)).trans
      (CtxExpr.app_equiv (CtxExpr.paste true _ 1) (e₀.trans (PastingDiagram.equiv_of_eq ?_)))
    rw [← PastingDiagram.pasteOr_of hp, I.sideRound_eq_unit hl]
  have hZ : ∀ β (hs : (cond β d' d).source ≠ []) (hqβ : S.target ⟨(cond β d' d).source,
      (cond β d' d).layers ++ [(.unit q, 0)]⟩ = some q), (S.side r β).layers = [] →
      (I.toInterp.diagram ⟨d.source, (.unit d.source, 0) :: (d.layers.take h ++
        d.layers.drop (h + (S.relSource r).layers.length) ++ [(.unit q, 0)])⟩ hsrc).Equiv
        (I.toInterp.roundDiagram hS.1 hqβ hs).toPastingDiagram := fun β hs hqβ hl =>
    PastingDiagram.equiv_of_eq
      (I.toInterp.diagram_congr (by rw [hcd β]; simp [Diagram.unitFirst, hl]) _ _)
  have hU : ∀ β, (S.side r β).layers = [] → _ := fun β hl =>
    I.isPiece_stepUnitor hd hq hsrc ((congrArg (·.getD []) ht).trans
      (target_eq_of_layers_eq_nil hS hl ht)) (IsEquivalence X (I.rel r).2)
  unfold relationPiece relationPieceSource
  by_cases h₁ : (S.side r true).layers = [] <;> by_cases h₀ : (S.side r false).layers = [] <;>
    simp only [h₀, h₁, ↓reduceIte]
  · exact (((hU false h₀).2.of_equiv (hZ false hsrc hq₁ h₀) (.refl _)).pasteOr hP
      (hY false h₀).symm).pasteOr ((hU true h₁).1.of_equiv (.refl _) (hZ true hsrc' hq₁' h₁))
      (hY true h₁)
  · exact (hP.of_equiv (hX false hsrc hq₁ h₀) (.refl _)).pasteOr
      ((hU true h₁).1.of_equiv (.refl _) (hZ true hsrc' hq₁' h₁)) (hY true h₁)
  · exact ((hU false h₀).2.of_equiv (hZ false hsrc hq₁ h₀) (.refl _)).pasteOr
      (hP.of_equiv (.refl _) (hX true hsrc' hq₁' h₁)) (hY false h₀).symm
  · exact hP.of_equiv (hX false hsrc hq₁ h₀) (hX true hsrc' hq₁' h₁)

theorem hasBdry_relationPiece {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q)
    (hq₁' : S.target ⟨d'.source, d'.layers ++ [(.unit q, 0)]⟩ = some q) :
    HasBdry false 2 (I.relationPiece hd hq hsrc)
      (I.toInterp.roundDiagram hS.1 hq₁ hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq₁' hsrc').toPastingDiagram :=
  (I.isPiece_relationPiece hd hq hsrc hsrc' hq₁ hq₁').1

theorem relationPiece_paste_mem_equivalences_iff {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hρ : IsEquivalence X (I.rel r).2) (hd : S.relationApply d r h o = some d')
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    {w : RoundPastingDiagram X} (hp : (I.relationPiece hd hq hsrc).Pastable w.toPastingDiagram 2)
    (hdw : w.dim = 3) :
    ∃ hr : ((I.relationPiece hd hq hsrc).paste w.toPastingDiagram 2 hp).IsRound,
      ((⟨_, hr⟩ : RoundPastingDiagram X) ∈ equivalences X ↔ w ∈ equivalences X) := by
  obtain ⟨hr, h⟩ := (I.isPiece_relationPiece hd hq hsrc
    ((isSome_target_and_source_of_relationApply hd).2.2 ▸ hsrc) (target_append_unit hS hq)
    (target_append_unit hS (target_ends hS hd hq true).1)).2 w hp hdw
  exact ⟨hr, h hρ⟩

omit [DecidableEq S.Ce] in
include I in
private theorem target_swap {d d' : Diagram S.Pt S.Ed S.Ce} {h : ℕ} (hsw : S.swap d h = some d')
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) : S.target d' = some q := by
  obtain ⟨l₁, l₂, rest, n, hdrop, hn, rfl⟩ := S.eq_of_swap_eq_some hsw
  have hls : d.layers = d.layers.take h ++ [l₁, l₂] ++ rest := by
    rw [List.append_assoc]
    exact (List.take_append_drop h d.layers).symm.trans (congrArg _ hdrop)
  have hpath := S.isPath_source_of_target hq
  rw [Signature.target, if_pos hpath, hls, S.targetFrom_append, S.targetFrom_append] at hq
  obtain ⟨p₂, h₁, h₃⟩ := Option.bind_eq_some_iff.1 hq
  obtain ⟨p, hA, h₂⟩ := Option.bind_eq_some_iff.1 h₁
  obtain ⟨x, z, hs⟩ := S.exists_pathEnds_of_isPath hpath
  refine S.target_mk_of_targetFrom hpath ?_
  rw [S.targetFrom_append, S.targetFrom_append, hA, Option.bind_some,
    (I.toInterp.equiv_diagram_swapLayers hS.1 (S.pathEnds_targetFrom hS.1 hA hs) h₂ hn).1,
    Option.bind_some, h₃]

include I in
private theorem target_of_isLayered : ∀ {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d'),
    c.IsLayered → ∀ {q : List (Edge S.Pt S.Ed)}, S.target d = some q → S.target d' = some q
  | _, _, .refl _, _, _, hq => hq
  | _, _, .cons (.relation _ _ _ hd) c, hc, _, hq =>
    target_of_isLayered c hc (target_ends hS hd hq true).1
  | _, _, .cons (.identification _ hd) c, hc, _, hq =>
    target_of_isLayered c hc (I.target_swap hd hq)
  | _, _, .cons (.relationBackward ..) _, hc, _, _ => hc.elim
  | _, _, .cons (.unit ..) _, hc, _, _ => hc.elim

private noncomputable def pasteRoundOr (u : PastingDiagram X) (v : RoundPastingDiagram X)
    (n : ℕ) : RoundPastingDiagram X := by
  classical
  exact if hp : u.Pastable v.toPastingDiagram n then
    if hr : (u.paste v.toPastingDiagram n hp).IsRound then pasteRound hp hr else v else v

private theorem pasteRoundOr_eq {u : PastingDiagram X} {v : RoundPastingDiagram X} {n : ℕ}
    (hp : u.Pastable v.toPastingDiagram n) (hr : (u.paste v.toPastingDiagram n hp).IsRound) :
    pasteRoundOr u v n = pasteRound hp hr := by
  rw [pasteRoundOr, dif_pos hp, dif_pos hr]

private theorem roundAfter {u a b : RoundPastingDiagram X} {n : ℕ}
    (hu : HasRoundType u.toPastingDiagram a b) (hn : a.dim = n) (x : RoundPastingDiagram X)
    (hp : u.Pastable x.toPastingDiagram n) (hx : x.dim = n + 1) :
    (u.paste x.toPastingDiagram n hp).IsRound :=
  isRound_paste_of_dim u x (hu.dim_eq.trans (congrArg (· + 1) hn)) hx hp

private theorem pasteRoundOr_spec {u : PastingDiagram X} {v a b c : RoundPastingDiagram X}
    {n : ℕ} (hu : HasRoundType u a b) (hv : HasRoundType v.toPastingDiagram b c) (hn : a.dim = n)
    (hround : ∀ (x : RoundPastingDiagram X) (hp : u.Pastable x.toPastingDiagram n),
      x.dim = n + 1 → (u.paste x.toPastingDiagram n hp).IsRound) :
    ∃ (hp : u.Pastable v.toPastingDiagram n) (hr : (u.paste v.toPastingDiagram n hp).IsRound),
      pasteRoundOr u v n = pasteRound hp hr ∧
        HasRoundType (pasteRoundOr u v n).toPastingDiagram a c := by
  have hp := hu.pastable hv (.refl _) hn
  have hr := hround v hp (hv.dim_eq.trans (by rw [← hu.dim_eq_dim, hn]))
  rw [pasteRoundOr_eq hp hr]
  exact ⟨hp, hr, rfl, hu.paste hv (.refl _) hn hp⟩

private theorem hasRoundType_pasteRoundOr {u v a b c : RoundPastingDiagram X} {n : ℕ}
    (hu : HasRoundType u.toPastingDiagram a b) (hv : HasRoundType v.toPastingDiagram b c)
    (hn : a.dim = n) : HasRoundType (pasteRoundOr u.toPastingDiagram v n).toPastingDiagram a c :=
  have ⟨_, _, _, h⟩ := pasteRoundOr_spec hu hv hn (roundAfter hu hn)
  h

private theorem pasteRoundOr_mem {u v a b c : RoundPastingDiagram X} {n : ℕ}
    (hu : HasRoundType u.toPastingDiagram a b) (hv : HasRoundType v.toPastingDiagram b c)
    (hn : a.dim = n) (hu' : u ∈ equivalences X) (hv' : v ∈ equivalences X) :
    pasteRoundOr u.toPastingDiagram v n ∈ equivalences X := by
  obtain ⟨hp, hr, e, -⟩ := pasteRoundOr_spec hu hv hn (roundAfter hu hn)
  rw [e]
  exact (paste_mem_equivalences_iff_right hu' (hu.dim_eq.trans (congrArg (· + 1) hn))
    (hv.dim_eq.trans (by rw [← hu.dim_eq_dim, hn])) hp).2 hv'

private theorem pasteRoundOr_piece {k : ℕ} {p : Prop} {P : PastingDiagram X}
    {v a b c : RoundPastingDiagram X} (hP : IsPiece k p P a.toPastingDiagram b.toPastingDiagram)
    (hv : HasRoundType v.toPastingDiagram b c) :
    HasRoundType P a b ∧ HasRoundType (pasteRoundOr P v (k + 1)).toPastingDiagram a c ∧
      (p → v ∈ equivalences X → pasteRoundOr P v (k + 1) ∈ equivalences X) := by
  have tP : HasRoundType P a b := .of_equiv_boundary hP.1.dim_a hP.1.dim_b hP.1.dim_h fun β => by
    cases β
    exacts [hP.1.side, hP.1.other]
  obtain ⟨hp, hr, e, t⟩ := pasteRoundOr_spec tP hv hP.1.dim_a fun x hp hx => (hP.2 x hp hx).1
  obtain ⟨_, hm⟩ := hP.2 v hp (hv.dim_eq.trans (congrArg (· + 1) hP.1.dim_b))
  refine ⟨tP, t, fun h hv' => ?_⟩
  rw [e]
  exact (hm h).2 hv'

private theorem equivalent_pasteRoundOr_assoc {u : PastingDiagram X}
    {v w a b c e : RoundPastingDiagram X} {n : ℕ} (hu : HasRoundType u a b)
    (hv : HasRoundType v.toPastingDiagram b c) (hw : HasRoundType w.toPastingDiagram c e)
    (hn : a.dim = n) (hround : ∀ (x : RoundPastingDiagram X)
      (hp : u.Pastable x.toPastingDiagram n), x.dim = n + 1 →
        (u.paste x.toPastingDiagram n hp).IsRound) :
    Equivalent (pasteRoundOr (pasteRoundOr u v n).toPastingDiagram w n)
      (pasteRoundOr u (pasteRoundOr v.toPastingDiagram w n) n) := by
  have hb : b.dim = n := hu.dim_eq_dim.symm.trans hn
  obtain ⟨hp₁, hr₁, e₁, t₁⟩ := pasteRoundOr_spec hu hv hn hround
  obtain ⟨hp₃, hr₃, e₃, t₃⟩ := pasteRoundOr_spec hv hw hb (roundAfter hv hb)
  obtain ⟨hp₄, hr₄, e₄, -⟩ := pasteRoundOr_spec hu t₃ hn hround
  rw [e₁] at t₁ ⊢
  obtain ⟨hp₂, hr₂, e₂, -⟩ := pasteRoundOr_spec t₁ hw hn (roundAfter t₁ hn)
  rw [e₂, e₄]
  obtain ⟨_, _, ea⟩ := equiv_paste_assoc hp₁ hp₂
  exact equivalent_of_equiv (ea.trans (Equiv.paste (.refl _) (PastingDiagram.equiv_of_eq
    (congrArg RoundPastingDiagram.toPastingDiagram e₃).symm) _ hp₄))

private theorem equivalent_pasteRoundOr_right {u : PastingDiagram X}
    {v v' a b c : RoundPastingDiagram X} {n : ℕ} (hu : HasRoundType u a b)
    (hv : HasRoundType v.toPastingDiagram b c) (hv' : HasRoundType v'.toPastingDiagram b c)
    (hn : a.dim = n) (hround : ∀ (x : RoundPastingDiagram X)
      (hp : u.Pastable x.toPastingDiagram n), x.dim = n + 1 →
        (u.paste x.toPastingDiagram n hp).IsRound) (h : Equivalent v v') :
    Equivalent (pasteRoundOr u v n) (pasteRoundOr u v' n) := by
  obtain ⟨hp, hr, e, -⟩ := pasteRoundOr_spec hu hv hn hround
  obtain ⟨hp', hr', e', -⟩ := pasteRoundOr_spec hu hv' hn hround
  rw [e, e']
  exact equivalent_paste_side true h
    (hu.dim_eq.trans ((congrArg (· + 1) hu.dim_eq_dim).trans hv.dim_eq.symm)) hp hp' hr hr'

private theorem equivalent_pasteRoundOr_left {u u' v a b c : RoundPastingDiagram X} {n : ℕ}
    (hu : HasRoundType u.toPastingDiagram a b) (hu' : HasRoundType u'.toPastingDiagram a b)
    (hv : HasRoundType v.toPastingDiagram b c) (hn : a.dim = n) (h : Equivalent u u') :
    Equivalent (pasteRoundOr u.toPastingDiagram v n) (pasteRoundOr u'.toPastingDiagram v n) := by
  obtain ⟨hp, hr, e, -⟩ := pasteRoundOr_spec hu hv hn (roundAfter hu hn)
  obtain ⟨hp', hr', e', -⟩ := pasteRoundOr_spec hu' hv hn (roundAfter hu' hn)
  rw [e, e']
  exact equivalent_paste_left h
    (hu.dim_eq.trans ((congrArg (· + 1) hu.dim_eq_dim).trans hv.dim_eq.symm)) hp hp' hr hr'

private theorem equivalent_pasteRoundOr_unit {v b c : RoundPastingDiagram X} {n : ℕ}
    (hv : HasRoundType v.toPastingDiagram b c) (hn : b.dim = n) :
    Equivalent (pasteRoundOr b.toPastingDiagram.unit v n) v := by
  obtain ⟨hp, hr, e, -⟩ := pasteRoundOr_spec (hasRoundType_unit b) hv hn
    (roundAfter (u := b.isRound.unit) (hasRoundType_unit b) hn)
  rw [e]
  exact equivalent_symm (equivalent_paste_unit_of_equiv false v
    (hv.dim_eq.trans (congrArg (· + 1) hn)) (hv.equiv_boundary_cond hn false) hp hr)

noncomputable def chainCore {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d')
    (hc : c.IsLayered) {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) : RoundPastingDiagram X :=
  match d, d', c, hc, q, hq, hsrc with
  | _, _, .refl _, _, _, hq, hsrc =>
    (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq) hsrc).isRound.unit
  | _, _, .cons (.relation _ _ _ hd) c, hc, _, hq, hsrc =>
    pasteRoundOr (I.relationPiece hd hq hsrc) (chainCore c hc (target_ends hS hd hq true).1
      ((isSome_target_and_source_of_relationApply hd).2.2 ▸ hsrc)) 2
  | _, _, .cons (.identification _ hd) c, hc, _, hq, hsrc =>
    chainCore c hc (I.target_swap hd hq) ((isSome_target_and_source_of_swap hd).2 ▸ hsrc)
  | _, _, .cons (.relationBackward ..) _, hc, _, _, _ => hc.elim
  | _, _, .cons (.unit ..) _, hc, _, _, _ => hc.elim

private theorem chainCore_spec : ∀ {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d')
    (hc : c.IsLayered) {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q)
    (hq₁' : S.target ⟨d'.source, d'.layers ++ [(.unit q, 0)]⟩ = some q),
    HasRoundType (I.chainCore c hc hq hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq₁ hsrc) (I.toInterp.roundDiagram hS.1 hq₁' hsrc') ∧
      ((∀ r, IsEquivalence X (I.rel r).2) → I.chainCore c hc hq hsrc ∈ equivalences X)
  | _, _, .refl _, _, _, _, _, _, _, _ => ⟨hasRoundType_unit _, fun _ => unit_mem_equivalences _⟩
  | _, _, .cons (.relation r _ _ hd) c, hc, _, hq, hsrc, hsrc', hq₁, hq₁' => by
    have hq₂ := (target_ends hS hd hq true).1
    have hsrc₂ : _ ≠ [] := (isSome_target_and_source_of_relationApply hd).2.2 ▸ hsrc
    have ih := chainCore_spec c hc hq₂ hsrc₂ hsrc' (target_append_unit hS hq₂) hq₁'
    obtain ⟨-, t, m⟩ := pasteRoundOr_piece (I.isPiece_relationPiece hd hq hsrc hsrc₂ hq₁
      (target_append_unit hS hq₂)) ih.1
    exact ⟨t, fun hρ => m (hρ r) (ih.2 hρ)⟩
  | _, _, .cons (.identification _ hd) c, hc, _, hq, hsrc, hsrc', hq₁, hq₁' => by
    have hq₂ := I.target_swap hd hq
    have ih := chainCore_spec c hc hq₂ ((isSome_target_and_source_of_swap hd).2 ▸ hsrc) hsrc'
      (target_append_unit hS hq₂) hq₁'
    exact ⟨ih.1.of_equiv (I.toInterp.equiv_diagram_swap hS.1
      (S.swap_unitFirst (swap_append_unit hS hd hq₂)) ((S.target_unitFirst _).trans hq₁) hsrc
      _).symm (.refl _), ih.2⟩
  | _, _, .cons (.relationBackward ..) _, hc, _, _, _, _, _, _ => hc.elim
  | _, _, .cons (.unit ..) _, hc, _, _, _, _, _, _ => hc.elim

theorem hasRoundType_chainCore {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d')
    (hc : c.IsLayered) {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hsrc' : d'.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q)
    (hq₁' : S.target ⟨d'.source, d'.layers ++ [(.unit q, 0)]⟩ = some q) :
    HasRoundType (I.chainCore c hc hq hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq₁ hsrc) (I.toInterp.roundDiagram hS.1 hq₁' hsrc') :=
  (I.chainCore_spec c hc hq hsrc hsrc' hq₁ hq₁').1

noncomputable def diagram3 {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d')
    (hc : c.IsLayered) {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) : RoundPastingDiagram X :=
  pasteRoundOr (pasteRoundOr (I.targetUnitorReverse hq hsrc).toPastingDiagram
      (I.chainCore c hc hq hsrc) 2).toPastingDiagram
    (I.targetUnitor (I.target_of_isLayered c hc hq)
      ((RewriteChain.isSome_target_and_source hS.1 c (Option.isSome_iff_exists.2 ⟨q, hq⟩)).2 ▸
        hsrc)) 2

omit [DecidableEq S.Ce] in
private theorem pasteRoundOr_ends {d d' : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q)
    (hsrc' : d'.source ≠ []) {K : RoundPastingDiagram X}
    (hK : HasRoundType K.toPastingDiagram
      (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq) hsrc)
      (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq') hsrc')) :
    (∃ (hp₁ : (I.targetUnitorReverse hq hsrc).toPastingDiagram.Pastable K.toPastingDiagram 2)
      (hr₁ : ((I.targetUnitorReverse hq hsrc).toPastingDiagram.paste
        K.toPastingDiagram 2 hp₁).IsRound)
      (hp₂ : (pasteRound hp₁ hr₁).toPastingDiagram.Pastable
        (I.targetUnitor hq' hsrc').toPastingDiagram 2)
      (hr₂ : ((pasteRound hp₁ hr₁).toPastingDiagram.paste
        (I.targetUnitor hq' hsrc').toPastingDiagram 2 hp₂).IsRound),
      pasteRoundOr (pasteRoundOr (I.targetUnitorReverse hq hsrc).toPastingDiagram K
        2).toPastingDiagram (I.targetUnitor hq' hsrc') 2 = pasteRound hp₂ hr₂) ∧
    HasRoundType (pasteRoundOr (pasteRoundOr (I.targetUnitorReverse hq hsrc).toPastingDiagram K
        2).toPastingDiagram (I.targetUnitor hq' hsrc') 2).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc') ∧
    (K ∈ equivalences X → pasteRoundOr (pasteRoundOr
        (I.targetUnitorReverse hq hsrc).toPastingDiagram K 2).toPastingDiagram
        (I.targetUnitor hq' hsrc') 2 ∈ equivalences X) := by
  have hn := I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc
  have tA := I.hasRoundType_targetUnitorReverse hq hsrc (target_append_unit hS hq)
  have tB := I.hasRoundType_targetUnitor hq' hsrc' (target_append_unit hS hq')
  obtain ⟨hp₁, hr₁, e₁, t₁⟩ := pasteRoundOr_spec tA hK hn (roundAfter tA hn)
  have m₁ := pasteRoundOr_mem tA hK hn (I.targetUnitor_mem_equivalences hq hsrc).2
  rw [e₁] at t₁ m₁ ⊢
  obtain ⟨hp₂, hr₂, e₂, t₂⟩ := pasteRoundOr_spec t₁ tB hn (roundAfter t₁ hn)
  exact ⟨⟨hp₁, hr₁, hp₂, hr₂, e₂⟩, t₂, fun h =>
    pasteRoundOr_mem t₁ tB hn (m₁ h) (I.targetUnitor_mem_equivalences hq' hsrc').1⟩

theorem diagram3_eq_paste {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d')
    (hc : c.IsLayered) {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q) (hsrc' : d'.source ≠ []) :
    ∃ (hp₁ : (I.targetUnitorReverse hq hsrc).toPastingDiagram.Pastable
        (I.chainCore c hc hq hsrc).toPastingDiagram 2)
      (hr₁ : ((I.targetUnitorReverse hq hsrc).toPastingDiagram.paste
        (I.chainCore c hc hq hsrc).toPastingDiagram 2 hp₁).IsRound)
      (hp₂ : (pasteRound hp₁ hr₁).toPastingDiagram.Pastable
        (I.targetUnitor hq' hsrc').toPastingDiagram 2)
      (hr₂ : ((pasteRound hp₁ hr₁).toPastingDiagram.paste
        (I.targetUnitor hq' hsrc').toPastingDiagram 2 hp₂).IsRound),
      I.diagram3 c hc hq hsrc = pasteRound hp₂ hr₂ :=
  (I.pasteRoundOr_ends hq hsrc hq' hsrc' (I.hasRoundType_chainCore c hc hq hsrc hsrc' _ _)).1

theorem hasRoundType_diagram3 {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d')
    (hc : c.IsLayered) {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q') (hsrc' : d'.source ≠ []) :
    HasRoundType (I.diagram3 c hc hq hsrc).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc') := by
  obtain rfl : q = q' := Option.some.inj ((I.target_of_isLayered c hc hq).symm.trans hq')
  exact (I.pasteRoundOr_ends hq hsrc hq' hsrc'
    (I.hasRoundType_chainCore c hc hq hsrc hsrc' _ _)).2.1

theorem diagram3_mem_equivalences (hρ : ∀ r, IsEquivalence X (I.rel r).2)
    {d d' : Diagram S.Pt S.Ed S.Ce} (c : S.RewriteChain d d') (hc : c.IsLayered)
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ []) :
    I.diagram3 c hc hq hsrc ∈ equivalences X := by
  have hsrc' : d'.source ≠ [] :=
    (RewriteChain.isSome_target_and_source hS.1 c (Option.isSome_iff_exists.2 ⟨q, hq⟩)).2 ▸ hsrc
  have h := I.chainCore_spec c hc hq hsrc hsrc' (target_append_unit hS hq)
    (target_append_unit hS (I.target_of_isLayered c hc hq))
  exact (I.pasteRoundOr_ends hq hsrc (I.target_of_isLayered c hc hq) hsrc' h.1).2.2 (h.2 hρ)

noncomputable def relationStepRound {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) : RoundPastingDiagram X :=
  pasteRoundOr (pasteRoundOr (I.targetUnitorReverse hq hsrc).toPastingDiagram
      (pasteRoundOr (I.relationPiece hd hq hsrc)
        (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq') hsrc').isRound.unit 2)
      2).toPastingDiagram (I.targetUnitor hq' hsrc') 2

theorem equiv_relationStepRound_diagram3 {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) :
    (I.relationStepRound hd hq hsrc hq' hsrc').toPastingDiagram.Equiv
      (I.diagram3 (.cons (.relation r h o hd) (.refl d')) trivial hq hsrc).toPastingDiagram := by
  obtain rfl : q = q' := Option.some.inj ((target_ends hS hd hq true).1.symm.trans hq')
  exact .refl _

private theorem relationPiece_unit {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel} {h o : ℕ}
    (hd : S.relationApply d r h o = some d') {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q)
    (hsrc' : d'.source ≠ []) :
    HasRoundType (pasteRoundOr (I.relationPiece hd hq hsrc)
        (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq') hsrc').isRound.unit
        2).toPastingDiagram
      (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq) hsrc)
      (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq') hsrc') ∧
    (IsEquivalence X (I.rel r).2 → pasteRoundOr (I.relationPiece hd hq hsrc)
        (I.toInterp.roundDiagram hS.1 (target_append_unit hS hq') hsrc').isRound.unit 2 ∈
      equivalences X) :=
  have h := pasteRoundOr_piece (I.isPiece_relationPiece hd hq hsrc hsrc' (target_append_unit hS hq)
    (target_append_unit hS hq')) (hasRoundType_unit _)
  ⟨h.2.1, fun hρ => h.2.2 hρ (unit_mem_equivalences _)⟩

theorem hasRoundType_relationStepRound {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hd : S.relationApply d r h o = some d') {q q' : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) (hq' : S.target d' = some q')
    (hsrc' : d'.source ≠ []) :
    HasRoundType (I.relationStepRound hd hq hsrc hq' hsrc').toPastingDiagram
      (I.toInterp.roundDiagram hS.1 hq hsrc) (I.toInterp.roundDiagram hS.1 hq' hsrc') := by
  obtain rfl : q = q' := Option.some.inj ((target_ends hS hd hq true).1.symm.trans hq')
  exact (I.pasteRoundOr_ends hq hsrc hq' hsrc' (I.relationPiece_unit hd hq hsrc hq' hsrc').1).2.1

theorem relationStepRound_mem_equivalences {d d' : Diagram S.Pt S.Ed S.Ce} {r : S.Rel}
    {h o : ℕ} (hρ : IsEquivalence X (I.rel r).2) (hd : S.relationApply d r h o = some d')
    {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hq' : S.target d' = some q') (hsrc' : d'.source ≠ []) :
    I.relationStepRound hd hq hsrc hq' hsrc' ∈ equivalences X := by
  obtain rfl : q = q' := Option.some.inj ((target_ends hS hd hq true).1.symm.trans hq')
  exact (I.pasteRoundOr_ends hq hsrc hq' hsrc' (I.relationPiece_unit hd hq hsrc hq' hsrc').1).2.2
    ((I.relationPiece_unit hd hq hsrc hq' hsrc').2 hρ)

omit [DecidableEq S.Ce] in
private theorem dim_roundDiagram {d : Diagram S.Pt S.Ed S.Ce} {q : List (Edge S.Pt S.Ed)}
    (hq : S.target d = some q) (hsrc : d.source ≠ []) :
    (I.toInterp.roundDiagram hS.1 hq hsrc).dim = 2 :=
  I.toInterp.dim_diagram hS.1 ((S.target_unitFirst _).trans hq) hsrc

omit [DecidableEq S.Ce] in
theorem equivalent_targetUnitor_paste_reverse {d : Diagram S.Pt S.Ed S.Ce}
    {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q) (hsrc : d.source ≠ [])
    (hq₁ : S.target ⟨d.source, d.layers ++ [(.unit q, 0)]⟩ = some q)
    (hp : (I.targetUnitor hq hsrc).toPastingDiagram.Pastable
      (I.targetUnitorReverse hq hsrc).toPastingDiagram 2)
    (hr : ((I.targetUnitor hq hsrc).toPastingDiagram.paste
      (I.targetUnitorReverse hq hsrc).toPastingDiagram 2 hp).IsRound) :
    Equivalent ⟨_, hr⟩ (I.toInterp.roundDiagram hS.1 hq₁ hsrc).isRound.unit := by
  have he : (I.targetUnitor hq hsrc).IsDegenerate := isDegenerate_unitorRound _ _ _ _ _
  have t := I.hasRoundType_targetUnitor hq hsrc hq₁
  have hn := I.dim_roundDiagram hq₁ hsrc
  have hde : (I.targetUnitor hq hsrc).dim = 3 := t.dim_eq.trans (congrArg (· + 1) hn)
  have hde' : (I.targetUnitorReverse hq hsrc).dim = 3 :=
    (I.hasRoundType_targetUnitorReverse hq hsrc hq₁).dim_eq.trans
      (congrArg (· + 1) (I.dim_roundDiagram hq hsrc))
  obtain ⟨hpz, ez⟩ := (I.targetUnitor hq hsrc).boundary_invertor_composite he false
  have hk : ∀ m (_ : (I.targetUnitor hq hsrc).dim - 1 = m) (hpm :
      (I.targetUnitor hq hsrc).toPastingDiagram.Pastable
        (I.targetUnitorReverse hq hsrc).toPastingDiagram m),
      ((I.targetUnitor hq hsrc).toPastingDiagram.paste
        (I.targetUnitorReverse hq hsrc).toPastingDiagram
        ((I.targetUnitor hq hsrc).dim - 1) hpz).Equiv
        ((I.targetUnitor hq hsrc).toPastingDiagram.paste
          (I.targetUnitorReverse hq hsrc).toPastingDiagram m hpm) := by
    rintro _ rfl _
    exact .refl _
  exact equivalent_of_mem_equivalences_cond false (z := ⟨_, isRound_invertor he
    (I.targetUnitor hq hsrc).isRound false⟩)
    (mem_equivalences_of_isDegenerate _ (isDegenerate_invertor _ he false))
    (by rw [dim_paste, hde, hde', max_self]) ((dim_unit _).trans (by rw [hn, hde]))
    (dim_invertor _ he false) (ez.trans (hk 2 (by rw [hde]) hp))
    ((boundary_invertor_unit _ he (I.targetUnitor hq hsrc).isRound false).trans
      (t.equiv_boundary_cond (by rw [hn, hde]) false).unit)

theorem equivalent_chainCore_append {d d' d'' : Diagram S.Pt S.Ed S.Ce}
    (c : S.RewriteChain d d') (c' : S.RewriteChain d' d'') (hc : c.IsLayered)
    (hc' : c'.IsLayered) {q : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q) (hsrc' : d'.source ≠ [])
    (hp : (I.chainCore c hc hq hsrc).toPastingDiagram.Pastable
      (I.chainCore c' hc' hq' hsrc').toPastingDiagram 2)
    (hr : ((I.chainCore c hc hq hsrc).toPastingDiagram.paste
      (I.chainCore c' hc' hq' hsrc').toPastingDiagram 2 hp).IsRound) :
    Equivalent (I.chainCore (c.append c') (hc.append hc') hq hsrc) ⟨_, hr⟩ :=
  have hsrc'' : d''.source ≠ [] := (RewriteChain.isSome_target_and_source hS.1 c'
    (Option.isSome_iff_exists.2 ⟨q, hq'⟩)).2 ▸ hsrc'
  have tC' := I.hasRoundType_chainCore c' hc' hq' hsrc' hsrc'' (target_append_unit hS hq')
    (target_append_unit hS (I.target_of_isLayered c' hc' hq'))
  match d, d', c, hc, c', hc', hq, hsrc, hq', hsrc', hp, hr, tC' with
  | _, _, .refl _, _, c', hc', hq, hsrc, _, _, hp, hr, tC' => by
    have hn := I.dim_roundDiagram (target_append_unit hS hq) hsrc
    exact equivalent_paste_unit_of_equiv false _ (tC'.dim_eq.trans (congrArg (· + 1) hn))
      (tC'.equiv_boundary_cond hn false) hp hr
  | _, _, .cons (.relation _ _ _ hd) c, hc, c', hc', hq, hsrc, hq', hsrc', hp, hr, tC' => by
    have hq₂ := (target_ends hS hd hq true).1
    have hsrc₂ : _ ≠ [] := (isSome_target_and_source_of_relationApply hd).2.2 ▸ hsrc
    have hP := I.isPiece_relationPiece hd hq hsrc hsrc₂ (target_append_unit hS hq)
      (target_append_unit hS hq₂)
    have tK := I.hasRoundType_chainCore c hc hq₂ hsrc₂ hsrc' (target_append_unit hS hq₂)
      (target_append_unit hS hq')
    have tKK := I.hasRoundType_chainCore (c.append c') (hc.append hc') hq₂ hsrc₂ hsrc''
      (target_append_unit hS hq₂) (target_append_unit hS (I.target_of_isLayered c' hc' hq'))
    have tP := (pasteRoundOr_piece hP tK).1
    have hn := I.dim_roundDiagram (target_append_unit hS hq) hsrc
    have hn₂ := I.dim_roundDiagram (target_append_unit hS hq₂) hsrc₂
    obtain ⟨hp₁, hr₁, e₁, -⟩ := pasteRoundOr_spec tK tC' hn₂ (roundAfter tK hn₂)
    have ih := equivalent_chainCore_append c c' hc hc' hq₂ hsrc₂ hq' hsrc' hp₁ hr₁
    exact equivalent_trans (equivalent_pasteRoundOr_right tP tKK
      (hasRoundType_pasteRoundOr tK tC' hn₂) hn (fun x hp hx => (hP.2 x hp hx).1)
      (equivalent_trans ih (equivalent_of_equiv (PastingDiagram.equiv_of_eq
        (congrArg RoundPastingDiagram.toPastingDiagram e₁).symm))))
      (equivalent_trans (equivalent_symm (equivalent_pasteRoundOr_assoc tP tK tC' hn
        (fun x hp hx => (hP.2 x hp hx).1))) (equivalent_of_equiv (PastingDiagram.equiv_of_eq
          (congrArg RoundPastingDiagram.toPastingDiagram (pasteRoundOr_eq hp hr)))))
  | _, _, .cons (.identification _ hd) c, hc, c', hc', hq, hsrc, hq', hsrc', hp, hr, _ =>
    equivalent_chainCore_append c c' hc hc' (I.target_swap hd hq)
      ((isSome_target_and_source_of_swap hd).2 ▸ hsrc) hq' hsrc' hp hr
  | _, _, .cons (.relationBackward ..) _, hc, _, _, _, _, _, _, _, _, _ => hc.elim
  | _, _, .cons (.unit ..) _, hc, _, _, _, _, _, _, _, _, _ => hc.elim

theorem equivalent_diagram3_append {d d' d'' : Diagram S.Pt S.Ed S.Ce}
    (c : S.RewriteChain d d') (c' : S.RewriteChain d' d'') (hc : c.IsLayered)
    (hc' : c'.IsLayered) {q q' : List (Edge S.Pt S.Ed)} (hq : S.target d = some q)
    (hsrc : d.source ≠ []) (hq' : S.target d' = some q') (hsrc' : d'.source ≠ [])
    (hp : (I.diagram3 c hc hq hsrc).toPastingDiagram.Pastable
      (I.diagram3 c' hc' hq' hsrc').toPastingDiagram 2)
    (hr : ((I.diagram3 c hc hq hsrc).toPastingDiagram.paste
      (I.diagram3 c' hc' hq' hsrc').toPastingDiagram 2 hp).IsRound) :
    Equivalent (I.diagram3 (c.append c') (hc.append hc') hq hsrc) ⟨_, hr⟩ := by
  obtain rfl : q = q' := Option.some.inj ((I.target_of_isLayered c hc hq).symm.trans hq')
  have hq'' := I.target_of_isLayered c' hc' hq'
  have hsrc'' : _ ≠ [] := (RewriteChain.isSome_target_and_source hS.1 c'
    (Option.isSome_iff_exists.2 ⟨q, hq'⟩)).2 ▸ hsrc'
  have n₀ := I.dim_roundDiagram hq hsrc
  have n₁ := I.dim_roundDiagram (target_append_unit hS hq) hsrc
  have n₂ := I.dim_roundDiagram hq' hsrc'
  have n₃ := I.dim_roundDiagram (target_append_unit hS hq') hsrc'
  have tA := I.hasRoundType_targetUnitorReverse hq hsrc (target_append_unit hS hq)
  have tK := I.hasRoundType_chainCore c hc hq hsrc hsrc' (target_append_unit hS hq)
    (target_append_unit hS hq')
  have tB := I.hasRoundType_targetUnitor hq' hsrc' (target_append_unit hS hq')
  have tA' := I.hasRoundType_targetUnitorReverse hq' hsrc' (target_append_unit hS hq')
  have tK' := I.hasRoundType_chainCore c' hc' hq' hsrc' hsrc'' (target_append_unit hS hq')
    (target_append_unit hS hq'')
  have tB' := I.hasRoundType_targetUnitor hq'' hsrc'' (target_append_unit hS hq'')
  have tKK := I.hasRoundType_chainCore (c.append c') (hc.append hc') hq hsrc hsrc''
    (target_append_unit hS hq) (target_append_unit hS hq'')
  have tAK := hasRoundType_pasteRoundOr tA tK n₀
  have tA'K' := hasRoundType_pasteRoundOr tA' tK' n₂
  have tBA' := hasRoundType_pasteRoundOr tB tA' n₃
  have tKK' := hasRoundType_pasteRoundOr tK tK' n₁
  obtain ⟨hp₀, hr₀, e₀, -⟩ := pasteRoundOr_spec tB tA' n₃ (roundAfter tB n₃)
  obtain ⟨hp₁, hr₁, e₁, -⟩ := pasteRoundOr_spec tK tK' n₁ (roundAfter tK n₁)
  have E₁ := equivalent_trans (equivalent_symm (equivalent_pasteRoundOr_assoc tB tA' tK' n₃
    (roundAfter tB n₃))) (equivalent_trans (equivalent_pasteRoundOr_left tBA'
      (hasRoundType_unit _) tK' n₃ (equivalent_trans (equivalent_of_equiv
        (PastingDiagram.equiv_of_eq (congrArg RoundPastingDiagram.toPastingDiagram e₀)))
        (I.equivalent_targetUnitor_paste_reverse hq' hsrc' _ hp₀ hr₀)))
      (equivalent_pasteRoundOr_unit tK' n₃))
  have E₂ := equivalent_trans (equivalent_symm (equivalent_pasteRoundOr_assoc tB tA'K' tB' n₃
    (roundAfter tB n₃))) (equivalent_pasteRoundOr_left (hasRoundType_pasteRoundOr tB tA'K' n₃)
      tK' tB' n₃ E₁)
  have E₃ := equivalent_trans (equivalent_pasteRoundOr_assoc tA tK tK' n₀ (roundAfter tA n₀))
    (equivalent_pasteRoundOr_right tA tKK' tKK n₀ (roundAfter tA n₀) (equivalent_symm
      (equivalent_trans (I.equivalent_chainCore_append c c' hc hc' hq hsrc hq' hsrc' hp₁ hr₁)
        (equivalent_of_equiv (PastingDiagram.equiv_of_eq
          (congrArg RoundPastingDiagram.toPastingDiagram e₁).symm)))))
  refine equivalent_trans (equivalent_symm (equivalent_pasteRoundOr_left
    (hasRoundType_pasteRoundOr tAK tK' n₀) (hasRoundType_pasteRoundOr tA tKK n₀) tB' n₀ E₃))
    (equivalent_trans (equivalent_pasteRoundOr_assoc tAK tK' tB' n₀ (roundAfter tAK n₀))
      (equivalent_trans (equivalent_symm (equivalent_pasteRoundOr_right tAK
        (hasRoundType_pasteRoundOr tB (hasRoundType_pasteRoundOr tA'K' tB' n₂) n₃)
        (hasRoundType_pasteRoundOr tK' tB' n₃) n₀ (roundAfter tAK n₀) E₂))
      (equivalent_trans (equivalent_symm (equivalent_pasteRoundOr_assoc tAK tB
        (hasRoundType_pasteRoundOr tA'K' tB' n₂) n₀ (roundAfter tAK n₀)))
        (equivalent_of_equiv (PastingDiagram.equiv_of_eq
          (congrArg RoundPastingDiagram.toPastingDiagram (pasteRoundOr_eq hp hr)))))))

end Interp

end RelSignature

end Atoms.Diagrammatic.Layered

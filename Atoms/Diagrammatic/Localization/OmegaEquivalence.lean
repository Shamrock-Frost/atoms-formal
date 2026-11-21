import Atoms.Diagrammatic.Localization.ModelStructure

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Shape

universe u

namespace Atoms.Diagrammatic

structure IsOmegaEquivalence {X Y : DiagSet.{u}} (f : X ⟶ Y) : Prop where
  exists_equivalent_of_dimension_eq_zero (V : Atom) (hV : V.dimension = 0)
    (y : diagram Y V) : ∃ x : diagram X V, Equivalent (cellRound y) (cellRound (f.app (op V) x))
  exists_equivalent_of_hasRoundType (a b : RoundPastingDiagram X) (hab : Parallel a b)
    (V : Atom) (y : diagram Y V)
    (hy : HasRoundType (PastingDiagram.ofCell y) (a.mapTo f) (b.mapTo f)) :
    ∃ x : diagram X V, HasRoundType (PastingDiagram.ofCell x) a b ∧
      Equivalent (cellRound y) (cellRound (f.app (op V) x))

private theorem equivalent_cellRound_app {X Y : DiagSet.{u}} (f : X ⟶ Y) {U V : Atom}
    {x : diagram X U} {x' : diagram X V} (h : Equivalent (cellRound x) (cellRound x')) :
    Equivalent (cellRound (f.app (op U) x)) (cellRound (f.app (op V) x')) := by
  rw [cellRound_app, cellRound_app]
  exact h.map f

private theorem roundPastingDiagram_mapTo_comp {X Y Z : DiagSet.{u}} (a : RoundPastingDiagram X)
    (f : X ⟶ Y) (g : Y ⟶ Z) : a.mapTo (f ≫ g) = (a.mapTo f).mapTo g :=
  RoundPastingDiagram.ext (PastingDiagram.mapTo_comp _ f g)

theorem IsOmegaEquivalence.comp {X Y Z : DiagSet.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : IsOmegaEquivalence f) (hg : IsOmegaEquivalence g) : IsOmegaEquivalence (f ≫ g) where
  exists_equivalent_of_dimension_eq_zero V hV z := by
    obtain ⟨y, hy⟩ := hg.exists_equivalent_of_dimension_eq_zero V hV z
    obtain ⟨x, hx⟩ := hf.exists_equivalent_of_dimension_eq_zero V hV y
    exact ⟨x, equivalent_trans hy (equivalent_cellRound_app g hx)⟩
  exists_equivalent_of_hasRoundType a b hab V z hz := by
    rw [roundPastingDiagram_mapTo_comp, roundPastingDiagram_mapTo_comp] at hz
    obtain ⟨y, hy, hzy⟩ :=
      hg.exists_equivalent_of_hasRoundType (a.mapTo f) (b.mapTo f) (hab.mapTo f) V z hz
    obtain ⟨x, hx, hyx⟩ := hf.exists_equivalent_of_hasRoundType a b hab V y hy
    exact ⟨x, hx, equivalent_trans hzy (equivalent_cellRound_app g hyx)⟩

private theorem hasRoundType_ofCell_map_iso {X : DiagSet.{u}} {U V : Atom} (e : U ≅ V)
    {x : diagram X V} {a b : RoundPastingDiagram X}
    (h : HasRoundType (PastingDiagram.ofCell x) a b) :
    HasRoundType (PastingDiagram.ofCell (X.map e.hom.op x)) a b where
  dim_eq :=
    (PastingDiagram.dim_eq_of_equiv (PastingDiagram.equiv_ofCell_map_iso e x)).trans h.dim_eq
  dim_eq_dim := h.dim_eq_dim
  source := ((PastingDiagram.equiv_ofCell_map_iso e x).boundary a.dim false).trans h.source
  target := ((PastingDiagram.equiv_ofCell_map_iso e x).boundary a.dim true).trans h.target

private theorem ofCell_uliftYonedaEquiv_map {X : DiagSet.{u}} {U : Atom} (φ : ball.{u} U ⟶ X) :
    (PastingDiagram.ofCell (uliftYonedaEquiv φ)).map = (realizeAtomIso U).hom ≫ φ := by
  change (realizeAtomIso U).hom ≫ uliftYonedaEquiv.symm (uliftYonedaEquiv φ) = _
  rw [Equiv.symm_apply_apply]

private theorem hasRoundType_ofCell_of_comp_eq_sphere {X : DiagSet.{u}}
    {a b : RoundPastingDiagram X}
    (hab : Parallel a b) (x : diagram X hab.cellShape)
    (hx : realize.map (hab.cellShape.rdc.restrictIncl (hab.cellShape.ogp.bdryFull ⊤)) ≫
      (PastingDiagram.ofCell x).map = hab.sphere) :
    HasRoundType (PastingDiagram.ofCell x) a b := by
  have h := (hab.hasRoundType_ofCell_iff (𝟙 X) x).2 (hx.trans (Category.comp_id _).symm)
  rwa [RoundPastingDiagram.mapTo_id, RoundPastingDiagram.mapTo_id] at h

theorem exists_hasRoundType_app_eq {X Y : DiagSet.{u}} {f : X ⟶ Y}
    (hf : (monomorphisms DiagSet.{u}).rlp f) {a b : RoundPastingDiagram X} (hab : Parallel a b)
    {V : Atom} (y : diagram Y V)
    (hy : HasRoundType (PastingDiagram.ofCell y) (a.mapTo f) (b.mapTo f)) :
    ∃ x : diagram X V, HasRoundType (PastingDiagram.ofCell x) a b ∧ f.app (op V) x = y := by
  obtain ⟨e, he⟩ := hab.exists_iso_hasRoundType f y hy
  let A := hab.cellShape
  have hsq := (hab.hasRoundType_ofCell_iff f _).1 he
  have hm : monomorphisms DiagSet.{u} (realize.map (A.rdc.restrictIncl (A.ogp.bdryFull ⊤))) :=
    mono_realize_map _ Subtype.val_injective
  have sq : CommSq hab.sphere (realize.map (A.rdc.restrictIncl (A.ogp.bdryFull ⊤))) f
      (PastingDiagram.ofCell (Y.map e.hom.op y)).map := ⟨hsq.symm⟩
  have := (hf _ hm).sq_hasLift sq
  let x' : diagram X A := uliftYonedaEquiv ((realizeAtomIso A).inv ≫ sq.lift)
  have hx' : (PastingDiagram.ofCell x').map = sq.lift :=
    (ofCell_uliftYonedaEquiv_map _).trans (Iso.hom_inv_id_assoc _ _)
  have hfx' : f.app (op A) x' = Y.map e.hom.op y :=
    PastingDiagram.ofCell_map_injective ((ofCell_app_map f x').trans
      ((congrArg (· ≫ f) hx').trans sq.fac_right))
  have htx' : HasRoundType (PastingDiagram.ofCell x') a b :=
    hasRoundType_ofCell_of_comp_eq_sphere hab x' ((congrArg (_ ≫ ·) hx').trans sq.fac_left)
  refine ⟨X.map e.symm.hom.op x', hasRoundType_ofCell_map_iso e.symm htx', ?_⟩
  rw [NatTrans.naturality_apply, hfx', ← Functor.map_comp_apply]
  change Y.map (e.inv ≫ e.hom).op y = y
  rw [e.inv_hom_id, op_id, Functor.map_id_apply]

private theorem isOmegaEquivalence_of_rlp_monomorphisms {X Y : DiagSet.{u}} {f : X ⟶ Y}
    (hf : (monomorphisms DiagSet.{u}).rlp f) : IsOmegaEquivalence f where
  exists_equivalent_of_dimension_eq_zero V _ y := by
    have sq : CommSq (initial.to X) (initial.to (ball.{u} V)) f (uliftYonedaEquiv.symm y) :=
      ⟨initial.hom_ext _ _⟩
    have := (hf _ (monomorphisms.infer_property (initial.to (ball.{u} V)))).sq_hasLift sq
    refine ⟨uliftYonedaEquiv sq.lift, ?_⟩
    have h : f.app (op V) (uliftYonedaEquiv sq.lift) = y :=
      (uliftYonedaEquiv_comp sq.lift f).symm.trans
        ((congrArg uliftYonedaEquiv sq.fac_right).trans (uliftYonedaEquiv.apply_symm_apply y))
    rw [h]
    exact equivalent_refl _
  exists_equivalent_of_hasRoundType a b hab V y hy := by
    obtain ⟨x, hx, hfx⟩ := exists_hasRoundType_app_eq hf hab y hy
    refine ⟨x, hx, ?_⟩
    rw [hfx]
    exact equivalent_refl _

theorem equivalent_of_rlp_monomorphisms {X Y : DiagSet.{u}} {q : X ⟶ Y}
    (hq : (monomorphisms DiagSet.{u}).rlp q) (hY : HasWeakComposites Y)
    {a b : RoundPastingDiagram X} (hab : Parallel a b)
    (h : Equivalent (a.mapTo q) (b.mapTo q)) : Equivalent a b := by
  obtain ⟨U, c, hc, hdU, hs, ht⟩ := exists_equivalence_cell_side hY false _ _ h
  have hcT : HasRoundType (PastingDiagram.ofCell c) ⟨a.toPastingDiagram.mapTo q, a.isRound⟩
      ⟨b.toPastingDiagram.mapTo q, b.isRound⟩ :=
    { dim_eq := hdU
      dim_eq_dim := hab.1
      source := hs
      target := ht }
  let A := hab.cellShape
  have hA : 0 < A.dimension := by
    rw [hab.dimension_cellShape]
    exact Nat.succ_pos _
  let c' : diagram Y A := hab.reindexCell q c hcT
  have hc' : IsEquivalence Y c' := by
    obtain ⟨e, -⟩ := hab.exists_iso_hasRoundType q c hcT
    have he : c' = Y.map e.hom.op c := hab.reindexCell_eq q c hcT e
    rw [he]
    exact (isEquivalence_map_iso_iff e c).2 hc
  have hsq : realize.map (A.rdc.restrictIncl (A.ogp.bdryFull ⊤)) ≫
      (PastingDiagram.ofCell c').map = hab.sphere ≫ q :=
    (hab.hasRoundType_ofCell_iff q c').1 (hab.hasRoundType_reindexCell q c hcT)
  obtain ⟨g, hg⟩ := (exists_toWalkingEquivalence_comp_eq_iff A hA hY c').2 hc'
  let j := realize.map (A.rdc.restrictIncl (A.ogp.bdryFull ⊤)) ≫ (realizeAtomIso A).hom ≫
    toWalkingEquivalence A hA
  have hj : monomorphisms DiagSet.{u} j := by
    have : Mono (realize.{u}.map (A.rdc.restrictIncl (A.ogp.bdryFull ⊤))) :=
      mono_realize_map _ Subtype.val_injective
    have : Mono (toWalkingEquivalence A hA) := (topInversionData A hA).mono_toLocalization
    exact monomorphisms.infer_property j
  have sq : CommSq hab.sphere j q g := ⟨by
    rw [← hsq, Category.assoc, Category.assoc, hg]
    rfl⟩
  have := (hq j hj).sq_hasLift sq
  let t : diagram X A := sq.lift.app (op A) ((toWalkingEquivalence A hA).app (op A) ⟨𝟙 A⟩)
  have ht : IsEquivalence X t :=
    ((topInversionData A hA).isEquivalence_toLocalization ⟨⟩).map sq.lift
  have hmap : (PastingDiagram.ofCell t).map =
      (realizeAtomIso A).hom ≫ toWalkingEquivalence A hA ≫ sq.lift :=
    ofCell_uliftYonedaEquiv_map (toWalkingEquivalence A hA ≫ sq.lift)
  have htT : HasRoundType (PastingDiagram.ofCell t) a b :=
    hasRoundType_ofCell_of_comp_eq_sphere hab t
      (by simpa only [hmap, j, Category.assoc] using sq.fac_left)
  exact EquivalenceData.equivalent
    { dim_eq := hab.1
      equivalence := cellRound t
      mem := ht
      dim_equivalence := htT.dim_eq
      source := htT.source
      target := htT.target }

theorem isOmegaEquivalence_of_trivialFibration (n : ℕ∞) {X Y : DiagSet.Infty.{u} n} (f : X ⟶ Y)
    [Fibration f] [WeakEquivalence f] : IsOmegaEquivalence f :=
  isOmegaEquivalence_of_rlp_monomorphisms
    (@rlp_monomorphisms_of_trivialFibration_toInfty_map n _ _ f ‹_› ‹_›)

theorem equivalent_of_trivialFibration (n : ℕ∞) {X Y : DiagSet.Infty.{u} n} (q : X ⟶ Y)
    [Fibration q] [WeakEquivalence q] (hY : HasWeakComposites Y)
    {a b : RoundPastingDiagram X} (hab : Parallel a b)
    (h : Equivalent (a.mapTo q) (b.mapTo q)) : Equivalent a b :=
  equivalent_of_rlp_monomorphisms
    (@rlp_monomorphisms_of_trivialFibration_toInfty_map n _ _ q ‹_› ‹_›) hY hab h

end Atoms.Diagrammatic

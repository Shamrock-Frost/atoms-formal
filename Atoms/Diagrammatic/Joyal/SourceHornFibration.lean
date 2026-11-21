import Atoms.Diagrammatic.Joyal.GrayCylinderModel
import Atoms.Diagrammatic.GrayTensor.HornModel
import Atoms.Diagrammatic.Localization.InversionHorn

open CategoryTheory Limits MorphismProperty HomotopicalAlgebra Atoms.Shape Atoms.Molecule
  Atoms.Molecule.OGP

universe u

namespace Atoms.Diagrammatic

private noncomputable abbrev arrowIso : globe.{0} 1 ≅ (atomGlobe 1).ogp :=
  FiniteOGP.ofOGPIso (globe 1)

private theorem arrowIso_hom_top : arrowIso.hom ⊤ = (atomGlobe 1).top := by
  have h := map_Iic arrowIso.hom ⊤
  rw [LowerSet.Iic_top, map_top_of_isIso, ← (atomGlobe 1).Iic_top] at h
  exact (LowerSet.Iic_inj.1 h).symm

private noncomputable abbrev arrowInput : (atomGlobe 1).ogp :=
  arrowIso.hom (SuspCarrier.pole false)

private theorem isMin_arrowInput : IsMin arrowInput :=
  (OrderIso.isMin_apply (orderIsoOfIso arrowIso)).2 (SuspCarrier.isMin_pole false)

private theorem arrowInput_covBy : arrowInput ⋖ (atomGlobe 1).top := by
  rw [← arrowIso_hom_top]
  exact (isMorphism arrowIso.hom).covBy_apply (SuspCarrier.pole_covBy_susp.2 (isMin_point _))

private theorem boundary_arrowInput :
    (atomGlobe 1).ogp.boundary (LowerSet.Iic arrowInput) 0 false =
      (atomGlobe 1).ogp.boundary ⊤ 0 false := by
  have hd : (atomGlobe 1).dimension = 1 := dimension_atomGlobe 1
  have h := (atomGlobe 1).bdry_top_eq_boundary (by omega) false
  rw [hd] at h
  rw [boundary_Iic_of_isMin isMin_arrowInput, ← h, ← map_top_of_isIso arrowIso.hom, ← map_bdry,
    bdry_globe_one, map_Iic]

private theorem atomicHornDataOfCovBy_eq_mk (U : Atom) (hU : 0 < U.dimension) (side : Bool)
    (removed : LowerSet U.ogp) (hr : U.ogp.IsRewritableSubmolecule removed (U.ogp.bdry ⊤ side))
    {x : U.ogp} (hc : x ⋖ U.top) (ho : U.ogp.orient hc = side)
    (hx : removed = LowerSet.Iic x) :
    (atomicHornDataOfCovBy U x hc).toHornData = ⟨U, hU, side, removed, hr⟩ := by
  subst hx ho
  rfl

private theorem HornData.exists_eq_atomicHornDataOfCovBy (h : HornData) {x : h.atom.ogp}
    (hx : h.removed = LowerSet.Iic x) :
    ∃ hc : x ⋖ h.atom.top, (atomicHornDataOfCovBy h.atom x hc).toHornData = h := by
  obtain ⟨hc, ho⟩ := mem_faceSet_top_of_isRewritableSubmolecule h hx
  refine ⟨hc, ?_⟩
  revert x
  obtain ⟨atom, positive, side, removed, rewritable⟩ := h
  intro x hx hc ho
  exact atomicHornDataOfCovBy_eq_mk atom positive side removed rewritable hc ho hx

private noncomputable def arrowSourceHorn : AtomicHornData :=
  atomicHornDataOfCovBy (atomGlobe 1) arrowInput arrowInput_covBy

private theorem sourceHorns_hornInclusion_grayTensorRight_arrowSourceHorn (V : Atom) :
    sourceHorns.{u} (hornInclusion (arrowSourceHorn.toHornData.grayTensorRight V)) := by
  let e := Atom.grayTensorIso (atomGlobe 1) V
  let x : (Atom.grayTensor (atomGlobe 1) V).ogp := e.hom (arrowInput, V.top)
  have hx : (arrowSourceHorn.toHornData.grayTensorRight V).removed = LowerSet.Iic x := by
    change map e.hom (LowerSet.Iic arrowInput ×ˢ (⊤ : LowerSet V.ogp)) = _
    rw [← V.Iic_top, ← LowerSet.Iic_prod (arrowInput, V.top), map_Iic]
  obtain ⟨hc, hh⟩ := HornData.exists_eq_atomicHornDataOfCovBy _ hx
  have hg (W : Atom) (y : W.ogp) : W.ogp.IsGlobular (LowerSet.Iic y) := (W.isRDC y).isGlobular
  have hs : (Atom.grayTensor (atomGlobe 1) V).ogp.boundary (LowerSet.Iic x) 0 false =
      (Atom.grayTensor (atomGlobe 1) V).ogp.boundary ⊤ 0 false := by
    have ht : (⊤ : LowerSet (Atom.grayTensor (atomGlobe 1) V).ogp) =
        map e.hom (LowerSet.Iic ((atomGlobe 1).top, V.top)) := by
      rw [LowerSet.Iic_prod, (atomGlobe 1).Iic_top, V.Iic_top, LowerSet.top_prod_top]
      exact (map_top_of_isIso e.hom).symm
    rw [ht, ← map_Iic, ← map_boundary, ← map_boundary, boundary_Iic_grayProduct_zero
      (hg _ _) (hg _ _), boundary_Iic_grayProduct_zero (hg _ _) (hg _ _), boundary_arrowInput,
      (atomGlobe 1).Iic_top]
  rw [← hh]
  exact ofHoms.mk (f := fun p : {p : Σ U : Atom, U.ogp // ∃ _ : p.2 ⋖ p.1.top,
      p.1.ogp.boundary (LowerSet.Iic p.2) 0 false = p.1.ogp.boundary ⊤ 0 false} =>
    hornInclusion.{u} (atomicHornDataOfCovBy p.1.1 p.1.2 p.2.fst).toHornData)
    ⟨⟨Atom.grayTensor (atomGlobe 1) V, x⟩, hc, hs⟩

private theorem eq_of_mem_hornSubset_arrowSourceHorn {z : (atomGlobe 1).ogp}
    (hz : z ∈ hornSubset arrowSourceHorn.toHornData) : z = atomGlobeVertex true default := by
  replace hz : z ≠ (atomGlobe 1).top ∧ z ≠ arrowInput :=
    (mem_hornSet_closure_singleton_iff arrowSourceHorn.toHornData (x := arrowInput) rfl).1 hz
  obtain ⟨w, rfl⟩ : ∃ w, arrowIso.hom w = z := ⟨arrowIso.inv z, by simp⟩
  rw [atomGlobeVertex_apply]
  rcases w with (_ | _) | _
  · exact absurd rfl hz.2
  · rfl
  · exact absurd arrowIso_hom_top hz.1

private theorem hornInclusion_arrowSourceHorn :
    hornInclusion.{u} arrowSourceHorn.toHornData =
      isTerminalBallAtomPoint.from _ ≫ uliftYoneda.map (atomGlobeVertex true) := by
  ext V c
  refine ULift.ext _ _ (Atom.hom_ext fun y => ?_)
  exact eq_of_mem_hornSubset_arrowSourceHorn (c.2 y)

private theorem saturation_sourceHorns_pushoutProduct_arrowSourceHorn {A B : DiagSet.{u}}
    (m : A ⟶ B) [Mono m] :
    saturation.{u} sourceHorns.{u} (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj grayTensorBifunctor.{u}) (hornInclusion arrowSourceHorn.toHornData)
      m).ι := by
  have := NatTrans.isSaturated_leibnizPreimage.{u}
    ((Functor.curry.obj grayTensorBifunctor.{u}).map (hornInclusion arrowSourceHorn.toHornData))
    (saturation.{u} sourceHorns.{u})
  have h : monomorphisms DiagSet.{u} ≤ NatTrans.leibnizPreimage
      ((Functor.curry.obj grayTensorBifunctor.{u}).map (hornInclusion arrowSourceHorn.toHornData))
      (saturation.{u} sourceHorns.{u}) := by
    rw [monomorphisms_eq_saturation_sphereInclusions]
    refine saturation_le _ _ ?_
    rintro _ _ _ ⟨V⟩
    obtain ⟨e⟩ := nonempty_arrowIso_pushoutProduct_hornInclusion_sphereInclusion.{u}
      arrowSourceHorn.toHornData V
    exact ((saturation sourceHorns).arrow_mk_iso_iff e).2
      (le_saturation _ _ (sourceHorns_hornInclusion_grayTensorRight_arrowSourceHorn V))
  exact h m (monomorphisms.infer_property m)

private noncomputable def arrowSourceInclusion :
    horn.{u} arrowSourceHorn.toHornData ⟶ ball.{u} (atomGlobe 1) :=
  hornInclusion arrowSourceHorn.toHornData

private noncomputable abbrev arrowVertex (ε : Bool) : ball.{u} atomPoint ⟶ ball.{u} (atomGlobe 1) :=
  uliftYoneda.map (atomGlobeVertex ε)

private instance mono_coprodDesc_arrowVertex :
    Mono (coprod.desc (arrowVertex.{u} false) (arrowVertex.{u} true)) := by
  have h : coprod.desc (arrowVertex.{u} false) (arrowVertex.{u} true) ≫
      toWalkingEquivalence (atomGlobe 1) ((dimension_atomGlobe 1).symm ▸ Nat.one_pos) =
      coprod.desc (reversibleArrowVertex.{u} false) (reversibleArrowVertex.{u} true) := by
    ext1 <;> simp [reversibleArrowVertex] <;> rfl
  have : Mono (coprod.desc (arrowVertex.{u} false) (arrowVertex.{u} true) ≫
      toWalkingEquivalence (atomGlobe 1) ((dimension_atomGlobe 1).symm ▸ Nat.one_pos)) := by
    rw [h]
    exact mono_coprodDesc_reversibleArrowVertex
  exact mono_of_mono _ (toWalkingEquivalence (atomGlobe 1) _)

private theorem grayTensorSnd_ball_atomPoint (X : DiagSet.{u}) :
    grayTensorSnd (ball.{u} atomPoint) X = (GrayDiagSet.leftUnitor X).hom := by
  rw [grayTensorSnd, isTerminalBallAtomPoint.hom_ext (isTerminalBallAtomPoint.from _) (𝟙 _)]
  exact (congrArg (· ≫ _) (grayTensorBifunctor.map_id (ball.{u} atomPoint, X))).trans
    (Category.id_comp _)

private theorem curry_grayTensorBifunctor_map_app {A B : DiagSet.{u}} (f : A ⟶ B)
    (W : DiagSet.{u}) :
    ((Functor.curry.obj grayTensorBifunctor.{u}).map f).app W = (grayTensorRight W).map f :=
  rfl

private theorem curry_grayTensorBifunctor_obj_map (W : DiagSet.{u}) {A B : DiagSet.{u}}
    (f : A ⟶ B) :
    ((Functor.curry.obj grayTensorBifunctor.{u}).obj W).map f = (grayTensorLeft W).map f :=
  rfl

private theorem grayTensorRight_coprod_hom_ext {A B X Y : DiagSet.{u}}
    {f g : grayTensor (A ⨿ B) X ⟶ Y}
    (hl : (grayTensorRight X).map coprod.inl ≫ f = (grayTensorRight X).map coprod.inl ≫ g)
    (hr : (grayTensorRight X).map coprod.inr ≫ f = (grayTensorRight X).map coprod.inr ≫ g) :
    f = g := by
  refine ((grayTensorRightAdjunction X).homEquiv _ _).injective (coprod.hom_ext ?_ ?_)
  · rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, hl]
  · rw [← Adjunction.homEquiv_naturality_left, ← Adjunction.homEquiv_naturality_left, hr]

private theorem exists_relative_gray_homotopy {X Y Z : DiagSet.{u}} (p : X ⟶ Y)
    (k : X ⟶ Z) (q : Z ⟶ Y) (r : Z ⟶ X) [Mono k]
    (hkq : k ≫ q = p) (hkr : k ≫ r = 𝟙 X)
    [hY : IsFibrant ((DiagSet.toInfty 1).obj Y)]
    (hkw : WeakEquivalence ((DiagSet.toInfty 1).map k)) :
    ∃ H : grayTensor (ball (atomGlobe 1)) Z ⟶ Y,
      (grayTensorLeft (ball (atomGlobe 1))).map k ≫ H =
        grayTensorSnd (ball (atomGlobe 1)) X ≫ p ∧
      (grayTensorRight Z).map (arrowVertex false) ≫ H =
        grayTensorSnd (ball atomPoint) Z ≫ q ∧
      (grayTensorRight Z).map (arrowVertex true) ≫ H =
        grayTensorSnd (ball atomPoint) Z ≫ r ≫ p := by
  let I := ball.{u} (atomGlobe 1)
  let pt := ball.{u} atomPoint
  let adj := grayTensorRightAdjunction Z
  let δ : grayTensor (pt ⨿ pt) Z ⟶ Y := (adj.homEquiv _ _).symm
    (coprod.desc (adj.homEquiv _ _ (grayTensorSnd pt Z ≫ q))
      (adj.homEquiv _ _ (grayTensorSnd pt Z ≫ r ≫ p)))
  have hδl : (grayTensorRight Z).map coprod.inl ≫ δ = grayTensorSnd pt Z ≫ q := by
    rw [← Adjunction.homEquiv_naturality_left_symm, coprod.inl_desc, Equiv.symm_apply_apply]
  have hδr : (grayTensorRight Z).map coprod.inr ≫ δ = grayTensorSnd pt Z ≫ r ≫ p := by
    rw [← Adjunction.homEquiv_naturality_left_symm, coprod.inr_desc, Equiv.symm_apply_apply]
  let sqb := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
    (coprod.desc (arrowVertex.{u} false) (arrowVertex.{u} true)) k
  let topb : sqb.pt ⟶ Y := pushout.desc (grayTensorSnd I X ≫ p) δ
    (grayTensorRight_coprod_hom_ext (by
      rw [curry_grayTensorBifunctor_map_app, curry_grayTensorBifunctor_obj_map, ← Category.assoc,
        ← Functor.map_comp, coprod.inl_desc, ← Category.assoc ((grayTensorRight X).map _),
        grayTensorRight_map_grayTensorSnd, ← Category.assoc ((grayTensorRight X).map coprod.inl),
        ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, hδl, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, hkq]) (by
      rw [curry_grayTensorBifunctor_map_app, curry_grayTensorBifunctor_obj_map, ← Category.assoc,
        ← Functor.map_comp, coprod.inr_desc, ← Category.assoc ((grayTensorRight X).map _),
        grayTensorRight_map_grayTensorSnd, ← Category.assoc ((grayTensorRight X).map coprod.inr),
        ← grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, hδr, ← Category.assoc,
        grayTensorLeft_map_grayTensorSnd, Category.assoc, reassoc_of% hkr]))
  have : Mono sqb.ι := mono_pushoutProduct _ _
  have : Cofibration ((DiagSet.toInfty 1).map sqb.ι) := (cofibration_iff _).2 ‹Mono sqb.ι›
  have : WeakEquivalence ((DiagSet.toInfty 1).map sqb.ι) :=
    DiagSet.Infty.weakEquivalence_toInfty_one_pushoutProduct _ _ (Or.inr hkw)
  have : Fibration (terminal.from ((DiagSet.toInfty 1).obj Y)) := hY
  let topb' : (DiagSet.toInfty 1).obj sqb.pt ⟶ (DiagSet.toInfty 1).obj Y := topb
  let sqH : CommSq topb' ((DiagSet.toInfty 1).map sqb.ι) (terminal.from _) (terminal.from _) :=
    ⟨terminal.hom_ext _ _⟩
  let H : grayTensor I Z ⟶ Y := sqH.lift
  have hH : sqb.ι ≫ H = topb := sqH.fac_left
  have hHk : (grayTensorLeft I).map k ≫ H = grayTensorSnd I X ≫ p := by
    rw [← curry_grayTensorBifunctor_obj_map, ← sqb.inl_ι, Category.assoc, hH]
    exact pushout.inl_desc _ _ _
  have hHv (ε : Bool) : (grayTensorRight Z).map (arrowVertex ε) ≫ H =
      (grayTensorRight Z).map (cond ε coprod.inr coprod.inl) ≫ δ := by
    have e : arrowVertex ε = cond ε coprod.inr coprod.inl ≫
        coprod.desc (arrowVertex.{u} false) (arrowVertex.{u} true) := by
      cases ε
      · exact (coprod.inl_desc _ _).symm
      · exact (coprod.inr_desc _ _).symm
    rw [e, Functor.map_comp, Category.assoc,
      ← curry_grayTensorBifunctor_map_app.{u} (coprod.desc _ _) Z, ← sqb.inr_ι,
      Category.assoc, hH]
    exact congrArg (_ ≫ ·) (pushout.inr_desc _ _ _)
  have hH0 : (grayTensorRight Z).map (arrowVertex false) ≫ H = grayTensorSnd pt Z ≫ q :=
    (hHv false).trans hδl
  have hH1 : (grayTensorRight Z).map (arrowVertex true) ≫ H = grayTensorSnd pt Z ≫ r ≫ p :=
    (hHv true).trans hδr
  exact ⟨H, hHk, hH0, hH1⟩

private theorem exists_retractArrow_of_relative_gray_homotopy {X Y Z : DiagSet.{u}} (p : X ⟶ Y)
    (k : X ⟶ Z) (q : Z ⟶ Y) (r : Z ⟶ X) [Mono k]
    (hkq : k ≫ q = p) (hkr : k ≫ r = 𝟙 X)
    (hp : sourceHorns.{u}.rlp p)
    (H : grayTensor (ball (atomGlobe 1)) Z ⟶ Y)
    (hHk : (grayTensorLeft (ball (atomGlobe 1))).map k ≫ H =
      grayTensorSnd (ball (atomGlobe 1)) X ≫ p)
    (hH0 : (grayTensorRight Z).map (arrowVertex false) ≫ H =
      grayTensorSnd (ball atomPoint) Z ≫ q)
    (hH1 : (grayTensorRight Z).map (arrowVertex true) ≫ H =
      grayTensorSnd (ball atomPoint) Z ≫ r ≫ p) :
    Nonempty (RetractArrow ((DiagSet.toInfty 1).map p) ((DiagSet.toInfty 1).map q)) := by
  let I := ball.{u} (atomGlobe 1)
  let pt := ball.{u} atomPoint
  let sqL := Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u})
    arrowSourceInclusion.{u} k
  let topL : sqL.pt ⟶ X := pushout.desc (grayTensorSnd I X) (grayTensorSnd _ Z ≫ r) (by
    rw [curry_grayTensorBifunctor_map_app, curry_grayTensorBifunctor_obj_map,
      grayTensorRight_map_grayTensorSnd, ← Category.assoc, grayTensorLeft_map_grayTensorSnd,
      Category.assoc, hkr, Category.comp_id])
  have hsat : sourceHorns.{u}.rlp.llp sqL.ι :=
    saturation_le _ _ (le_llp_rlp _) _ (saturation_sourceHorns_pushoutProduct_arrowSourceHorn k)
  have : HasLiftingProperty sqL.ι p := hsat p hp
  have sqL' : CommSq topL sqL.ι p H := ⟨by
    refine sqL.hom_ext ?_ ?_
    · calc sqL.inl ≫ topL ≫ p = grayTensorSnd I X ≫ p := pushout.inl_desc_assoc _ _ _ _
        _ = (grayTensorLeft I).map k ≫ H := hHk.symm
        _ = sqL.inl ≫ sqL.ι ≫ H := by rw [← Category.assoc, sqL.inl_ι]
    · calc sqL.inr ≫ topL ≫ p = grayTensorSnd _ Z ≫ r ≫ p := pushout.inr_desc_assoc _ _ _ _
        _ = (grayTensorRight Z).map arrowSourceInclusion.{u} ≫ H := by
          rw [arrowSourceInclusion, hornInclusion_arrowSourceHorn, Functor.map_comp,
            Category.assoc, hH1, ← Category.assoc ((grayTensorRight Z).map _),
            grayTensorRight_map_grayTensorSnd]
        _ = sqL.inr ≫ sqL.ι ≫ H := by rw [← Category.assoc, sqL.inr_ι]; rfl⟩
  let L : grayTensor I Z ⟶ X := sqL'.lift
  have hL₁ : sqL.ι ≫ L = topL := sqL'.fac_left
  have hL₂ : L ≫ p = H := sqL'.fac_right
  have hLk : (grayTensorLeft I).map k ≫ L = grayTensorSnd I X := by
    rw [← curry_grayTensorBifunctor_obj_map, ← sqL.inl_ι, Category.assoc, hL₁]
    exact pushout.inl_desc _ _ _
  have hn : k ≫ (GrayDiagSet.leftUnitor Z).inv =
      (GrayDiagSet.leftUnitor X).inv ≫ (grayTensorLeft pt).map k := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq, ← grayTensorSnd_ball_atomPoint,
      ← grayTensorSnd_ball_atomPoint]
    exact (grayTensorLeft_map_grayTensorSnd _ _).symm
  have hkρ : k ≫ (GrayDiagSet.leftUnitor Z).inv ≫ (grayTensorRight Z).map (arrowVertex false) ≫ L =
      𝟙 X := by
    rw [← Category.assoc, hn, Category.assoc, ← Category.assoc ((grayTensorLeft _).map k),
      grayTensorLeft_map_comp_grayTensorRight_map, Category.assoc, hLk,
      grayTensorRight_map_grayTensorSnd, grayTensorSnd_ball_atomPoint, Iso.inv_hom_id]
  have hρp : ((GrayDiagSet.leftUnitor Z).inv ≫ (grayTensorRight Z).map (arrowVertex false) ≫ L) ≫
      p = q := by
    rw [Category.assoc, Category.assoc, hL₂, hH0, grayTensorSnd_ball_atomPoint,
      Iso.inv_hom_id_assoc]
  let hret : RetractArrow ((DiagSet.toInfty 1).map p) ((DiagSet.toInfty 1).map q) :=
    { i := Arrow.homMk k (𝟙 _) (by rw [Category.comp_id]; exact hkq)
      r := Arrow.homMk ((GrayDiagSet.leftUnitor Z).inv ≫
        (grayTensorRight Z).map (arrowVertex false) ≫ L) (𝟙 _)
        (by rw [Category.comp_id]; exact hρp)
      retract := Arrow.hom_ext _ _ hkρ (Category.id_comp _) }
  exact ⟨hret⟩

theorem fibration_toInfty_one_of_rlp_sourceHorns {X Y : DiagSet.{u}} (p : X ⟶ Y)
    [hX : IsFibrant ((DiagSet.toInfty 1).obj X)] [hY : IsFibrant ((DiagSet.toInfty 1).obj Y)]
    (hp : sourceHorns.{u}.rlp p) : Fibration ((DiagSet.toInfty 1).map p) := by
  let F := MorphismProperty.factorizationData (trivialCofibrations (DiagSet.Infty.{u} 1))
    (fibrations (DiagSet.Infty.{u} 1)) ((DiagSet.toInfty 1).map p)
  let Z : DiagSet.{u} := F.Z
  let k : X ⟶ Z := F.i
  let q : Z ⟶ Y := F.p
  have hkq : k ≫ q = p := F.fac
  have : Mono k := F.hi.1
  have : Cofibration ((DiagSet.toInfty 1).map k) := (cofibration_iff _).2 F.hi.1
  have hkw : WeakEquivalence ((DiagSet.toInfty 1).map k) := (weakEquivalence_iff _).2 F.hi.2
  let sqr : CommSq (𝟙 ((DiagSet.toInfty 1).obj X)) ((DiagSet.toInfty 1).map k)
      (terminal.from _) (terminal.from _) := ⟨terminal.hom_ext _ _⟩
  let r : Z ⟶ X := sqr.lift
  have hkr : k ≫ r = 𝟙 X := sqr.fac_left
  obtain ⟨H, hHk, hH0, hH1⟩ := exists_relative_gray_homotopy p k q r hkq hkr hkw
  obtain ⟨hret⟩ := exists_retractArrow_of_relative_gray_homotopy p k q r hkq hkr hp
    H hHk hH0 hH1
  exact (fibration_iff _).2 ((fibrations _).of_retract hret F.hp)
end Atoms.Diagrammatic

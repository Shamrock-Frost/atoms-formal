import Atoms.Diagrammatic.Marked.GrayTensorHorn
import Atoms.Diagrammatic.Joyal.MarkedGrayTensorModel
import Atoms.Shape.MarkedHornGrayTensorLeft

open Atoms.Molecule Atoms.Molecule.OGP
open CategoryTheory Limits Opposite Atoms.Shape

universe u

namespace Atoms.Diagrammatic

open Homotopical (MarkedPresheaf)

private theorem isDegenerate_iso_hom_app_iff {X Y : DiagSet.{u}} (e : X ≅ Y) {V : Atom}
    (x : X.obj (op V)) : IsDegenerate Y (e.hom.app (op V) x) ↔ IsDegenerate X x :=
  ⟨fun hx => Iso.hom_inv_id_app_apply e (op V) x ▸ isDegenerate_app e.inv hx,
    isDegenerate_app e.hom⟩

section GrayTensorRight

variable (h : MarkedHornData) (V : Atom) (marked : Bool) (hV : marked = true → 0 < V.dimension)
  (L R S : ℕ → LowerSet (Atom.grayTensor h.atom V).ogp)
  (hs : (Atom.grayTensor h.atom V).ogp.IsStagedPasting
    ((Atom.grayTensor h.atom V).dimension - 1) (.Iic (h.grayTensorFace V)) L R S)
  (hS : S ((Atom.grayTensor h.atom V).dimension - 1) = (Atom.grayTensor h.atom V).ogp.bdry ⊤ h.side)
  (ht : ∀ i < (Atom.grayTensor h.atom V).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
    grade ℕ y = i + 1 → y ∈ h.grayTensorMarking V false)
  {M : Set V.ogp} {hM : ∀ z ∈ M, 0 < grade ℕ z}

private theorem nonempty_arrowIso_pushoutProduct (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    (f₂ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM)
    (hf₂ : MarkedPresheaf.forget.map f₂ = sphereInclusion V) :
    Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h) f₂).ι ≅
      Arrow.mk (markedHornInclusion.{u} (h.grayTensorRight V marked hV L R S hs hS ht))) := by
  obtain ⟨E⟩ := nonempty_forget_arrowIso false h (h.grayTensorRight V marked hV L R S hs hS ht) V
    (h.toHornData_grayTensorRight V) f₂ hf₂
  have hR : E.hom.right ≫ (closedSubpresheafUnivIso _).hom = (tensorBallIso h V).hom :=
    congrArg Iso.hom (iso_ball_ext (Arrow.rightFunc.mapIso E ≪≫ closedSubpresheafUnivIso _)
      (tensorBallIso h V))
  have hRapp {T A B : Atom} (f : T ⟶ Atom.grayTensor A B) (c : h.target.underlying.obj (op A))
      (d : (ball.{u} V).obj (op B)) :
      (E.hom.right.app (op T) ((grayTensor _ _).map f.op (grayTensorCell c d))).1 =
        ULift.up (f ≫ Atom.grayTensorMap c.1.down d.down) :=
    (congrFun (congrArg (fun φ => (NatTrans.app φ (op T) : _ → _)) hR) _).trans
      (tensorBallIso_hom_app h V f c d)
  have htopv {T A B : Atom} (e : T ≅ Atom.grayTensor A B) (c : h.target.underlying.obj (op A))
      (d : (ball.{u} V).obj (op B)) :
      (Atom.grayTensorIso h.atom V).inv (ConcreteCategory.hom (E.hom.right.app (op T)
        ((grayTensor _ _).map e.hom.op (grayTensorCell c d))).1.down T.top) =
          (ConcreteCategory.hom c.1.down A.top, ConcreteCategory.hom d.down B.top) := by
    rw [hRapp]
    change (Atom.grayTensorIso h.atom V).inv (Atom.grayTensorMap c.1.down d.down (e.hom T.top)) = _
    rw [iso_hom_apply_top, Atom.grayTensorIso_inv_grayTensorMap_top]
  have hEd {W : Atom} (y : (grayTensor h.target.underlying (ball.{u} V)).obj (op W)) :
      IsDegenerate (ball.{u} _) (E.hom.right.app (op W) y).1 ↔
        IsDegenerate (grayTensor h.target.underlying (ball.{u} V)) y :=
    isDegenerate_iso_hom_app_iff (Arrow.rightFunc.mapIso E ≪≫ closedSubpresheafUnivIso _) y
  have hEinj (W : Atom) : Function.Injective (E.hom.right.app (op W)) :=
    Function.LeftInverse.injective fun y => Iso.hom_inv_id_app_apply (Arrow.rightFunc.mapIso E) _ y
  have hE (W : Atom) (y : (grayTensor h.target.underlying (ball.{u} V)).obj (op W)) :
      y ∈ (markedTensor false h.target (markedBall.{u} V M hM)).marked W ↔
        E.hom.right.app (op W) y ∈
          (h.grayTensorRight V marked hV L R S hs hS ht).target.marked W := by
    refine (mem_marked_markedTensor _ _ _ _ _).trans
      (Iff.trans ?_ (mem_marked_markedClosedSubset_univ_iff _ _ _ _).symm)
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · rcases hy with hy | ⟨A, B, c, d, e, hm, rfl⟩
      · exact Or.inl ((hEd y).2 hy)
      rcases hm with hc | hd | ⟨hf, -⟩
      · rcases (mem_marked_markedClosedSubset_univ_iff _ _ _ _).1 hc with hc | hc
        · exact Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell
            (Or.inl (isDegenerate_app (closedSubpresheafUnivIso h.atom).inv hc)))))
        · exact Or.inr ((h.mem_targetMarking_grayTensorRight_iff V).2
            (Or.inl ((congrArg (fun z => z.1 ∈ h.targetMarking) (htopv e c d)).mpr hc)))
      · rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hd with hd | hd
        · exact Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2
            (isDegenerate_grayTensorCell (Or.inr hd))))
        · exact Or.inr ((h.mem_targetMarking_grayTensorRight_iff V).2
            (Or.inr ((congrArg (fun z => marked = true ∧ z.2 = V.top) (htopv e c d)).mpr
              ((hMm _).1 hd))))
      · exact absurd hf Bool.false_ne_true
    rcases hy with hy | hy
    · exact Or.inl ((hEd y).1 hy)
    by_cases hdeg : IsDegenerate (grayTensor h.target.underlying (ball.{u} V)) y
    · exact Or.inl hdeg
    refine Or.inr ?_
    set g : W ⟶ Atom.grayTensor h.atom V := (E.hom.right.app (op W) y).1.down with hg
    obtain ⟨W₀, p, i, hp, hi, hpi⟩ := exists_collapse_inclusion_factorization g
    have hpiso : IsIso p := by
      by_contra hni
      exact hdeg ((hEd y).1 ⟨W₀, p, ULift.up i, hp, hni, congrArg ULift.up hpi⟩)
    have : Mono g := by
      have := mono_of_isInclusionHom i hi
      exact hpi ▸ mono_comp p i
    obtain ⟨A, B, i', j', e, -, -, he⟩ :=
      Atom.exists_iso_comp_grayTensorMap_of_isInclusionHom g (isInclusionHom_of_mono g)
    let c : h.target.underlying.obj (op A) := ⟨ULift.up i', fun _ => LowerSet.mem_top⟩
    have hy' : y = (grayTensor _ _).map e.hom.op (grayTensorCell c (ULift.up j')) := by
      exact hEinj W (Subtype.ext ((congrArg ULift.up he.symm).trans
        (hRapp e.hom c (ULift.up j')).symm))
    have h1 := (h.mem_targetMarking_grayTensorRight_iff V).1 hy
    rw [← he] at h1
    change ((Atom.grayTensorIso h.atom V).inv (Atom.grayTensorMap i' j' (e.hom W.top))).1 ∈ _ ∨
      (_ ∧ ((Atom.grayTensorIso h.atom V).inv (Atom.grayTensorMap i' j' (e.hom W.top))).2 = _) at h1
    rw [iso_hom_apply_top, Atom.grayTensorIso_inv_grayTensorMap_top] at h1
    refine ⟨A, B, c, ULift.up j', e, ?_, hy'⟩
    rcases h1 with h1 | ⟨hm, h2⟩
    · exact Or.inl ((mem_marked_markedClosedSubset_univ_iff _ _ _ _).2 (Or.inr h1))
    · exact Or.inr (Or.inl ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
        (Or.inr ((hMm _).2 ⟨hm, h2⟩))))
  have hmono : Mono (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h) f₂).ι) :=
    ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff E).2 ((MarkedPresheaf.mono_iff _).1
      (markedHorns_le_monomorphisms _ (MorphismProperty.ofHoms.mk _)))
  have hinj (W : Atom) := (mono_iff_injective ((MarkedPresheaf.forget.map
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false))
      (markedHornInclusion.{u} h) f₂).ι).app (op W))).1 inferInstance
  refine nonempty_arrowIso_of_forget _ _ (fun W x hx => ?_)
    (fun _ x hx => mem_marked_source_of_markedHornInclusion _ x hx) E hE
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hx with hd | ⟨A, B, c, d, e, hm, hx'⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _
      (@isDegenerate_of_isDegenerate_app _ _ _ hmono _ _ hd)
  have hw : E.hom.right.app (op W) ((MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h) f₂).ι).app
        (op W) x) = (MarkedPresheaf.forget.map (markedHornInclusion.{u}
          (h.grayTensorRight V marked hV L R S hs hS ht))).app (op W) (E.hom.left.app (op W) x) :=
    (congrFun (congrArg (fun φ => (NatTrans.app φ (op W) : _ → _)) E.hom.w) x).symm
  have h2 := (h.mem_hornSet_grayTensorRight_iff V).1
    ((congrArg (fun z : (closedSubpresheaf.{u} (Atom.grayTensor h.atom V) ⊤).toFunctor.obj (op W) =>
      ConcreteCategory.hom (z.1.down : W ⟶ _) W.top ∈
        (h.grayTensorRight V marked hV L R S hs hS ht).hornSet) hw).mpr
      ((E.hom.left.app (op W) x).2 W.top))
  rw [hx'] at h2
  rcases (congrArg (fun z => z.1 ∈ h.hornSet ∨ z.2 ∈ V.ogp.bdryFull ⊤) (htopv e c d)).mp h2 with
    h2 | h2
  · let c₀ : h.source.underlying.obj (op A) :=
      ⟨c.1, fun t => h.hornSet.lower ((Atom.isMap c.1.down).monotone (A.le_top t)) h2⟩
    have hy : (grayTensor _ _).map e.hom.op (grayTensorCell c₀ d) ∈
        (markedTensor false h.source (markedBall.{u} V M hM)).marked W :=
      (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨A, B, c₀, d, e,
        hm.imp_left (mem_marked_source_of_markedHornInclusion h c₀), rfl⟩)
    have heq : (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h)
          f₂).inr).app (op W) ((grayTensor _ _).map e.hom.op (grayTensorCell c₀ d)) = x := by
      refine hinj W ((congrFun (congrArg (fun φ => ((MarkedPresheaf.forget.map φ).app (op W) :
        _ → _)) (Functor.PushoutObjObj.inr_ι _)) _).trans ?_)
      rw [hx']
      exact forget_map_markedTensorMap_app false (markedHornInclusion.{u} h) (𝟙 _) e.hom c₀ d
    exact heq ▸ MarkedPresheaf.map_mem_marked _ hy
  · have hd₀ : d ∈ (Homotopical.EZCategory.uliftBoundary.{u} V).obj (op B) := by
      rw [← closedSubpresheaf_univ_erase_top]
      exact fun t => (V.ogp.bdryFull ⊤).lower ((Atom.isMap d.down).monotone (B.le_top t)) h2
    let d₀ : (sphere.{u} V).obj (op B) := ⟨d, hd₀⟩
    have hm₀ : tensorMask false h.target ((MarkedPresheaf.flat atomMarking).obj (sphere.{u} V)) A B
        c d₀ := by
      rcases hm with hc | hd | hf
      · exact Or.inl hc
      · refine Or.inr (Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ _).2 ?_))
        rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hd with hd | hd
        · exact isDegenerate_of_isDegenerate_app (sphereInclusion V) hd
        · exact absurd ((hMm _).1 hd).2 ((V.mem_bdryFull_top_iff _).1 h2)
      · exact Or.inr (Or.inr hf)
    have hy : (grayTensor _ _).map e.hom.op (grayTensorCell c d₀) ∈
        (markedTensor false h.target ((MarkedPresheaf.flat atomMarking).obj (sphere.{u} V))).marked
          W :=
      (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨A, B, c, d₀, e, hm₀, rfl⟩)
    have heq : (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h)
          f₂).inl).app (op W) ((grayTensor _ _).map e.hom.op (grayTensorCell c d₀)) = x := by
      refine hinj W ((congrFun (congrArg (fun φ => ((MarkedPresheaf.forget.map φ).app (op W) :
        _ → _)) (Functor.PushoutObjObj.inl_ι _)) _).trans ?_)
      rw [hx']
      refine (forget_map_markedTensorMap_app false (𝟙 _) f₂ e.hom c d₀).trans ?_
      rw [hf₂]
      rfl
    exact heq ▸ MarkedPresheaf.map_mem_marked _ hy

end GrayTensorRight

theorem exists_arrowIso_pushoutProduct_markedHornInclusion_sphere (h : MarkedHornData)
    (V : Atom) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor h.atom V ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h)
        (sphereToMarkedBall V)).ι ≅ Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorRight V
  exact ⟨h.grayTensorRight V false (fun h => absurd h Bool.false_ne_true) L R S hs hS ht, rfl,
    nonempty_arrowIso_pushoutProduct h V false _ L R S hs hS ht
      (fun b => ⟨fun hb => absurd hb (Set.notMem_empty b),
        fun hb => absurd hb.1 Bool.false_ne_true⟩)
      (sphereToMarkedBall V) rfl⟩

theorem exists_arrowIso_pushoutProduct_markedHornInclusion_markedSphere (h : MarkedHornData)
    (V : Atom) (hV : 0 < V.dimension) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor h.atom V ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h)
        (sphereToMarkedBall V ≫ markingToMarkedBall V hV)).ι ≅
          Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorRight V
  refine ⟨h.grayTensorRight V true (fun _ => hV) L R S hs hS ht, rfl,
    nonempty_arrowIso_pushoutProduct h V true _ L R S hs hS ht
      (fun b => ⟨fun hb => ⟨rfl, hb⟩, fun hb => hb.2⟩) _
      ((Functor.map_comp _ _ _).trans (Category.comp_id (sphereInclusion V)))⟩

private theorem mono_markingToMarkedBall (V : Atom) (hV : 0 < V.dimension) :
    Mono (markingToMarkedBall.{u} V hV) :=
  (MarkedPresheaf.mono_iff _).2 (inferInstanceAs (Mono (𝟙 _)))

open MorphismProperty HomotopicalAlgebra in
theorem MarkedDiagSet.Coinductive.weakEquivalence_pushoutProduct_markedHornInclusion (n : ℕ∞)
    (h : MarkedHornData) {X Y : MarkedDiagSet.{u}} (i : X ⟶ Y) [Mono i] :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) (markedHornInclusion.{u} h) i).ι) := by
  let G := Functor.curry.obj (markedTensorBifunctor.{u} false)
  let α := G.map (markedHornInclusion.{u} h)
  let T := (trivialCofibrations (MarkedDiagSet.Coinductive.{u} n)).inverseImage
    (MarkedDiagSet.toCoinductive n)
  have : IsSaturated.{u} (trivialCofibrations (MarkedDiagSet.Coinductive.{u} n)) := by
    rw [← fibrations_llp]; infer_instance
  have : PreservesColimitsOfSize.{u, u} (MarkedDiagSet.toCoinductive.{u} n) :=
    inferInstanceAs (PreservesColimitsOfSize (𝟭 MarkedDiagSet.{u}))
  have : ∀ W, PreservesColimitsOfSize.{u, u} (G.obj W) := fun W =>
    inferInstanceAs (PreservesColimitsOfSize (tensorLeft false W))
  have : ∀ W, PreservesColimitsOfShape WalkingSpan (G.obj W) := fun W =>
    inferInstanceAs (PreservesColimitsOfShape WalkingSpan (tensorLeft false W))
  have := NatTrans.isSaturated_leibnizPreimage.{u} α T
  have hhorn : ∀ h' : MarkedHornData, T (markedHornInclusion.{u} h') := fun h' =>
    coinductiveGenerators_le_trivialCofibrations n _ (Or.inl (Or.inl (.mk h')))
  have hsphere : ∀ V : Atom, NatTrans.leibnizPreimage α T (sphereToMarkedBall.{u} V) := fun V => by
    obtain ⟨h', -, ⟨e⟩⟩ := exists_arrowIso_pushoutProduct_markedHornInclusion_sphere.{u} h V
    exact (T.arrow_mk_iso_iff e).2 (hhorn h')
  have hmarked : ∀ (V : Atom) (hV : 0 < V.dimension),
      NatTrans.leibnizPreimage α T (markingToMarkedBall.{u} V hV) := fun V hV => by
    obtain ⟨h', -, ⟨e⟩⟩ :=
      exists_arrowIso_pushoutProduct_markedHornInclusion_markedSphere.{u} h V hV
    have hks : T (NatTrans.leibnizBox α (sphereToMarkedBall V ≫ markingToMarkedBall V hV)) :=
      (T.arrow_mk_iso_iff e).2 (hhorn h')
    have hpo := NatTrans.isPushout_leibnizSourceMap_of_comp α (sphereToMarkedBall V)
      (sphereToMarkedBall V ≫ markingToMarkedBall V hV) (markingToMarkedBall V hV) (by simp)
    have hc := T.of_isPushout hpo (hsphere V)
    have hfac := NatTrans.leibnizSourceMap_leibnizBox α (sphereToMarkedBall V) (𝟙 _)
      (i := sphereToMarkedBall V ≫ markingToMarkedBall V hV) (i' := markingToMarkedBall V hV)
      (by simp)
    rw [CategoryTheory.Functor.map_id, Category.comp_id (NatTrans.leibnizBox α _)] at hfac
    have := mono_markingToMarkedBall.{u} V hV
    have : Mono (markedHornInclusion.{u} h) := markedHorns_le_monomorphisms _ (.mk h)
    refine ⟨mono_markedPushoutProduct (markedHornInclusion h) (markingToMarkedBall V hV), ?_⟩
    exact (weakEquivalences _).of_precomp _ _ hc.2 (hfac ▸ hks.2)
  have hmono : MorphismProperty.monomorphisms MarkedDiagSet.{u} =
      saturation.{u} (functorImage (MarkedPresheaf.flat atomMarking) sphereInclusions ⊔
        MarkedPresheaf.markingMaps atomMarking) :=
    (MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps atomMarking
      monomorphisms_eq_saturation_sphereInclusions.symm).symm
  refine (weakEquivalence_iff _).2 (saturation_le.{u} _ (NatTrans.leibnizPreimage α T) ?_ i
    ((congrArg (fun P : MorphismProperty MarkedDiagSet.{u} => P i) hmono).mp
      (MorphismProperty.monomorphisms.infer_property i))).2
  rintro _ _ g (⟨K, Y, t, ht, e⟩ | ⟨a, ha⟩)
  · cases ht with
    | mk U =>
      exact ((NatTrans.leibnizPreimage α T).arrow_mk_iso_iff
        ((eqToIso e).symm ≪≫ flatSphereInclusionArrowIso U)).2 (hsphere U)
  · exact ((NatTrans.leibnizPreimage α T).arrow_mk_iso_iff (markingMapArrowIso a ha)).2
      (hmarked a ha)

private theorem nonempty_forget_arrowIso_left (V : Atom) (h h' : MarkedHornData)
    (hh' : h'.toHornData = HornData.grayTensorLeft V h.toHornData) {M : Set V.ogp}
    {hM : ∀ z ∈ M, 0 < grade ℕ z}
    (f₁ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM)
    (hf₁ : MarkedPresheaf.forget.map f₁ = sphereInclusion V) :
    Nonempty (Arrow.mk (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ (markedHornInclusion.{u} h)).ι) ≅
      Arrow.mk (MarkedPresheaf.forget.map (markedHornInclusion.{u} h'))) := by
  have e₁ := Functor.PushoutObjObj.mapArrowIso (G₁ := MarkedPresheaf.forget)
    (G₂ := MarkedPresheaf.forget) (G₃ := MarkedPresheaf.forget)
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false))
      f₁ (markedHornInclusion.{u} h))
    (Functor.PushoutObjObj.ofHasPushout _ _ _)
    (F' := Functor.curry.obj grayTensorBifunctor.{u}) (Iso.refl _)
  rw [hf₁] at e₁
  have e₂ := Functor.PushoutObjObj.ι_iso_of_iso_right (f₁ := Arrow.mk (sphereInclusion.{u} V))
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj grayTensorBifunctor.{u}) _ _)
    (Functor.PushoutObjObj.ofHasPushout _ _ _) h.forgetArrowIso
  obtain ⟨e₃⟩ := nonempty_arrowIso_pushoutProduct_sphereInclusion_hornInclusion.{u} V h.toHornData
  rw [← hh'] at e₃
  exact ⟨e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ h'.forgetArrowIso.symm⟩

private noncomputable def tensorBallIsoLeft (V : Atom) (h : MarkedHornData) :
    grayTensor (ball.{u} V) h.target.underlying ≅ ball.{u} (Atom.grayTensor V h.atom) :=
  ((Functor.curry.obj grayTensorBifunctor.{u}).obj (ball V)).mapIso
    (closedSubpresheafUnivIso h.atom) ≪≫ grayTensorBallIso V h.atom

private theorem tensorBallIsoLeft_hom_app (V : Atom) (h : MarkedHornData) {T A B : Atom}
    (f : T ⟶ Atom.grayTensor A B) (d : (ball.{u} V).obj (op A))
    (c : h.target.underlying.obj (op B)) :
    (tensorBallIsoLeft V h).hom.app (op T) ((grayTensor _ _).map f.op (grayTensorCell d c)) =
      ULift.up (f ≫ Atom.grayTensorMap d.down c.1.down) := by
  rw [NatTrans.naturality_apply]
  change (ball _).map f.op ((grayTensorBallIso V h.atom).hom.app _
    ((grayTensorBifunctor.map (𝟙 (ball V), (closedSubpresheafUnivIso h.atom).hom)).app _
      (grayTensorCell d c))) = _
  have h1 := grayTensorCell_naturality (X := ball.{u} V) (X' := ball.{u} V)
    (Y := h.target.underlying) (Y' := ball.{u} h.atom) (𝟙 _) (closedSubpresheafUnivIso h.atom).hom
    d c
  exact (congrArg (fun z => (ball _).map f.op ((grayTensorBallIso V h.atom).hom.app _ z)) h1).trans
    (congrArg ((ball _).map f.op) (grayTensorBallIso_hom_app_grayTensorCell d.down c.1.down))

section GrayTensorLeft

variable (V : Atom) (h : MarkedHornData) (marked : Bool) (hV : marked = true → 0 < V.dimension)
  (L R S : ℕ → LowerSet (Atom.grayTensor V h.atom).ogp)
  (hs : (Atom.grayTensor V h.atom).ogp.IsStagedPasting
    ((Atom.grayTensor V h.atom).dimension - 1) (.Iic (h.grayTensorLeftFace V)) L R S)
  (hS : S ((Atom.grayTensor V h.atom).dimension - 1) =
    (Atom.grayTensor V h.atom).ogp.bdry ⊤ (xor V.dimension.bodd h.side))
  (ht : ∀ i < (Atom.grayTensor V h.atom).dimension - 1, ∀ y ∈ L (i + 1) ⊔ R (i + 1),
    grade ℕ y = i + 1 → y ∈ h.grayTensorLeftMarking V false)
  {M : Set V.ogp} {hM : ∀ z ∈ M, 0 < grade ℕ z}

private theorem nonempty_arrowIso_pushoutProduct_left
    (hMm : ∀ b, b ∈ M ↔ marked = true ∧ b = V.top)
    (f₁ : (MarkedPresheaf.flat atomMarking).obj (sphere.{u} V) ⟶ markedBall.{u} V M hM)
    (hf₁ : MarkedPresheaf.forget.map f₁ = sphereInclusion V) :
    Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ (markedHornInclusion.{u} h)).ι ≅
      Arrow.mk (markedHornInclusion.{u} (h.grayTensorLeft V marked hV L R S hs hS ht))) := by
  obtain ⟨E⟩ := nonempty_forget_arrowIso_left V h (h.grayTensorLeft V marked hV L R S hs hS ht)
    (h.toHornData_grayTensorLeft V) f₁ hf₁
  have hR : E.hom.right ≫ (closedSubpresheafUnivIso _).hom = (tensorBallIsoLeft V h).hom :=
    congrArg Iso.hom (iso_ball_ext (Arrow.rightFunc.mapIso E ≪≫ closedSubpresheafUnivIso _)
      (tensorBallIsoLeft V h))
  have hRapp {T A B : Atom} (f : T ⟶ Atom.grayTensor A B) (d : (ball.{u} V).obj (op A))
      (c : h.target.underlying.obj (op B)) :
      (E.hom.right.app (op T) ((grayTensor _ _).map f.op (grayTensorCell d c))).1 =
        ULift.up (f ≫ Atom.grayTensorMap d.down c.1.down) :=
    (congrFun (congrArg (fun φ => (NatTrans.app φ (op T) : _ → _)) hR) _).trans
      (tensorBallIsoLeft_hom_app V h f d c)
  have htopv {T A B : Atom} (e : T ≅ Atom.grayTensor A B) (d : (ball.{u} V).obj (op A))
      (c : h.target.underlying.obj (op B)) :
      (Atom.grayTensorIso V h.atom).inv (ConcreteCategory.hom (E.hom.right.app (op T)
        ((grayTensor _ _).map e.hom.op (grayTensorCell d c))).1.down T.top) =
          (ConcreteCategory.hom d.down A.top, ConcreteCategory.hom c.1.down B.top) := by
    rw [hRapp]
    change (Atom.grayTensorIso V h.atom).inv (Atom.grayTensorMap d.down c.1.down (e.hom T.top)) = _
    rw [iso_hom_apply_top, Atom.grayTensorIso_inv_grayTensorMap_top]
  have hEd {W : Atom} (y : (grayTensor (ball.{u} V) h.target.underlying).obj (op W)) :
      IsDegenerate (ball.{u} _) (E.hom.right.app (op W) y).1 ↔
        IsDegenerate (grayTensor (ball.{u} V) h.target.underlying) y :=
    isDegenerate_iso_hom_app_iff (Arrow.rightFunc.mapIso E ≪≫ closedSubpresheafUnivIso _) y
  have hEinj (W : Atom) : Function.Injective (E.hom.right.app (op W)) :=
    Function.LeftInverse.injective fun y => Iso.hom_inv_id_app_apply (Arrow.rightFunc.mapIso E) _ y
  have hE (W : Atom) (y : (grayTensor (ball.{u} V) h.target.underlying).obj (op W)) :
      y ∈ (markedTensor false (markedBall.{u} V M hM) h.target).marked W ↔
        E.hom.right.app (op W) y ∈
          (h.grayTensorLeft V marked hV L R S hs hS ht).target.marked W := by
    refine (mem_marked_markedTensor _ _ _ _ _).trans
      (Iff.trans ?_ (mem_marked_markedClosedSubset_univ_iff _ _ _ _).symm)
    refine ⟨fun hy => ?_, fun hy => ?_⟩
    · rcases hy with hy | ⟨A, B, d, c, e, hm, rfl⟩
      · exact Or.inl ((hEd y).2 hy)
      rcases hm with hd | hc | ⟨hf, -⟩
      · rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hd with hd | hd
        · exact Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2
            (isDegenerate_grayTensorCell (Or.inl hd))))
        · exact Or.inr ((h.mem_targetMarking_grayTensorLeft_iff V).2
            (Or.inr ((congrArg (fun z => marked = true ∧ z.1 = V.top) (htopv e d c)).mpr
              ((hMm _).1 hd))))
      · rcases (mem_marked_markedClosedSubset_univ_iff _ _ _ _).1 hc with hc | hc
        · exact Or.inl ((hEd _).2 ((isDegenerate_map_iso_iff e _).2 (isDegenerate_grayTensorCell
            (Or.inr (isDegenerate_app (closedSubpresheafUnivIso h.atom).inv hc)))))
        · exact Or.inr ((h.mem_targetMarking_grayTensorLeft_iff V).2
            (Or.inl ((congrArg (fun z => z.2 ∈ h.targetMarking) (htopv e d c)).mpr hc)))
      · exact absurd hf Bool.false_ne_true
    rcases hy with hy | hy
    · exact Or.inl ((hEd y).1 hy)
    by_cases hdeg : IsDegenerate (grayTensor (ball.{u} V) h.target.underlying) y
    · exact Or.inl hdeg
    refine Or.inr ?_
    set g : W ⟶ Atom.grayTensor V h.atom := (E.hom.right.app (op W) y).1.down with hg
    obtain ⟨W₀, p, i, hp, hi, hpi⟩ := exists_collapse_inclusion_factorization g
    have hpiso : IsIso p := by
      by_contra hni
      exact hdeg ((hEd y).1 ⟨W₀, p, ULift.up i, hp, hni, congrArg ULift.up hpi⟩)
    have : Mono g := by
      have := mono_of_isInclusionHom i hi
      exact hpi ▸ mono_comp p i
    obtain ⟨A, B, i', j', e, -, -, he⟩ :=
      Atom.exists_iso_comp_grayTensorMap_of_isInclusionHom g (isInclusionHom_of_mono g)
    let c : h.target.underlying.obj (op B) := ⟨ULift.up j', fun _ => LowerSet.mem_top⟩
    have hy' : y = (grayTensor _ _).map e.hom.op (grayTensorCell (ULift.up i') c) := by
      exact hEinj W (Subtype.ext ((congrArg ULift.up he.symm).trans
        (hRapp e.hom (ULift.up i') c).symm))
    have h1 := (h.mem_targetMarking_grayTensorLeft_iff V).1 hy
    rw [← he] at h1
    change ((Atom.grayTensorIso V h.atom).inv (Atom.grayTensorMap i' j' (e.hom W.top))).2 ∈ _ ∨
      (_ ∧ ((Atom.grayTensorIso V h.atom).inv (Atom.grayTensorMap i' j' (e.hom W.top))).1 = _) at h1
    rw [iso_hom_apply_top, Atom.grayTensorIso_inv_grayTensorMap_top] at h1
    refine ⟨A, B, ULift.up i', c, e, ?_, hy'⟩
    rcases h1 with h1 | ⟨hm, h2⟩
    · exact Or.inr (Or.inl ((mem_marked_markedClosedSubset_univ_iff _ _ _ _).2 (Or.inr h1)))
    · exact Or.inl ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
        (Or.inr ((hMm _).2 ⟨hm, h2⟩)))
  have hmono : Mono (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ (markedHornInclusion.{u} h)).ι) :=
    ((MorphismProperty.monomorphisms _).arrow_mk_iso_iff E).2 ((MarkedPresheaf.mono_iff _).1
      (markedHorns_le_monomorphisms _ (MorphismProperty.ofHoms.mk _)))
  have hinj (W : Atom) := (mono_iff_injective ((MarkedPresheaf.forget.map
    (Functor.PushoutObjObj.ofHasPushout (Functor.curry.obj (markedTensorBifunctor.{u} false))
      f₁ (markedHornInclusion.{u} h)).ι).app (op W))).1 inferInstance
  refine nonempty_arrowIso_of_forget _ _ (fun W x hx => ?_)
    (fun _ x hx => mem_marked_source_of_markedHornInclusion _ x hx) E hE
  rcases (mem_marked_markedTensor _ _ _ _ _).1 hx with hd | ⟨A, B, d, c, e, hm, hx'⟩
  · exact MarkedDiagSet.mem_marked_of_isDegenerate _
      (@isDegenerate_of_isDegenerate_app _ _ _ hmono _ _ hd)
  have hw : E.hom.right.app (op W) ((MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁ (markedHornInclusion.{u} h)).ι).app
        (op W) x) = (MarkedPresheaf.forget.map (markedHornInclusion.{u}
          (h.grayTensorLeft V marked hV L R S hs hS ht))).app (op W) (E.hom.left.app (op W) x) :=
    (congrFun (congrArg (fun φ => (NatTrans.app φ (op W) : _ → _)) E.hom.w) x).symm
  have h2 := (h.mem_hornSet_grayTensorLeft_iff V).1
    ((congrArg (fun z : (closedSubpresheaf.{u} (Atom.grayTensor V h.atom) ⊤).toFunctor.obj (op W) =>
      ConcreteCategory.hom (z.1.down : W ⟶ _) W.top ∈
        (h.grayTensorLeft V marked hV L R S hs hS ht).hornSet) hw).mpr
      ((E.hom.left.app (op W) x).2 W.top))
  rw [hx'] at h2
  rcases (congrArg (fun z => z.1 ∈ V.ogp.bdryFull ⊤ ∨ z.2 ∈ h.hornSet) (htopv e d c)).mp h2 with
    h2 | h2
  · have hd₀ : d ∈ (Homotopical.EZCategory.uliftBoundary.{u} V).obj (op A) := by
      rw [← closedSubpresheaf_univ_erase_top]
      exact fun t => (V.ogp.bdryFull ⊤).lower ((Atom.isMap d.down).monotone (A.le_top t)) h2
    let d₀ : (sphere.{u} V).obj (op A) := ⟨d, hd₀⟩
    have hm₀ : tensorMask false ((MarkedPresheaf.flat atomMarking).obj (sphere.{u} V)) h.target A B
        d₀ c := by
      rcases hm with hd | hc | hf
      · refine Or.inl ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ _ _).2 ?_)
        rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hd with hd | hd
        · exact isDegenerate_of_isDegenerate_app (sphereInclusion V) hd
        · exact absurd ((hMm _).1 hd).2 ((V.mem_bdryFull_top_iff _).1 h2)
      · exact Or.inr (Or.inl hc)
      · exact Or.inr (Or.inr hf)
    have hy : (grayTensor _ _).map e.hom.op (grayTensorCell d₀ c) ∈
        (markedTensor false ((MarkedPresheaf.flat atomMarking).obj (sphere.{u} V)) h.target).marked
          W :=
      (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨A, B, d₀, c, e, hm₀, rfl⟩)
    have heq : (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁
          (markedHornInclusion.{u} h)).inr).app (op W)
            ((grayTensor _ _).map e.hom.op (grayTensorCell d₀ c)) = x := by
      refine hinj W ((congrFun (congrArg (fun φ => ((MarkedPresheaf.forget.map φ).app (op W) :
        _ → _)) (Functor.PushoutObjObj.inr_ι _)) _).trans ?_)
      rw [hx']
      refine (forget_map_markedTensorMap_app false f₁ (𝟙 _) e.hom d₀ c).trans ?_
      rw [hf₁]
      rfl
    exact heq ▸ MarkedPresheaf.map_mem_marked _ hy
  · let c₀ : h.source.underlying.obj (op B) :=
      ⟨c.1, fun t => h.hornSet.lower ((Atom.isMap c.1.down).monotone (B.le_top t)) h2⟩
    have hy : (grayTensor _ _).map e.hom.op (grayTensorCell d c₀) ∈
        (markedTensor false (markedBall.{u} V M hM) h.source).marked W :=
      (mem_marked_markedTensor _ _ _ _ _).2 (Or.inr ⟨A, B, d, c₀, e,
        hm.imp_right (Or.imp_left (mem_marked_source_of_markedHornInclusion h c₀)), rfl⟩)
    have heq : (MarkedPresheaf.forget.map (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) f₁
          (markedHornInclusion.{u} h)).inl).app (op W)
            ((grayTensor _ _).map e.hom.op (grayTensorCell d c₀)) = x := by
      refine hinj W ((congrFun (congrArg (fun φ => ((MarkedPresheaf.forget.map φ).app (op W) :
        _ → _)) (Functor.PushoutObjObj.inl_ι _)) _).trans ?_)
      rw [hx']
      exact forget_map_markedTensorMap_app false (𝟙 _) (markedHornInclusion.{u} h) e.hom d c₀
    exact heq ▸ MarkedPresheaf.map_mem_marked _ hy

end GrayTensorLeft

theorem exists_arrowIso_pushoutProduct_sphere_markedHornInclusion_with_data (V : Atom)
    (h : MarkedHornData) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor V h.atom ∧
      h'.toHornData = HornData.grayTensorLeft V h.toHornData ∧
      HEq h'.targetMarking {w : (Atom.grayTensor V h.atom).ogp |
        ((Atom.grayTensorIso V h.atom).inv w).2 ∈ h.targetMarking} ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) (sphereToMarkedBall V)
        (markedHornInclusion.{u} h)).ι ≅ Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorLeft V
  refine ⟨h.grayTensorLeft V false (fun h => absurd h Bool.false_ne_true) L R S hs hS ht,
    rfl, h.toHornData_grayTensorLeft V, ?_,
    nonempty_arrowIso_pushoutProduct_left V h false _ L R S hs hS ht
      (fun b => ⟨fun hb => absurd hb (Set.notMem_empty b),
        fun hb => absurd hb.1 Bool.false_ne_true⟩) (sphereToMarkedBall V) rfl⟩
  apply heq_of_eq
  ext w
  exact (h.mem_targetMarking_grayTensorLeft_iff V).trans
    (or_iff_left_of_imp (fun h => absurd h.1 Bool.false_ne_true))

theorem exists_arrowIso_pushoutProduct_sphere_markedHornInclusion (V : Atom)
    (h : MarkedHornData) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor V h.atom ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false)) (sphereToMarkedBall V)
        (markedHornInclusion.{u} h)).ι ≅ Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorLeft V
  exact ⟨h.grayTensorLeft V false (fun h => absurd h Bool.false_ne_true) L R S hs hS ht, rfl,
    nonempty_arrowIso_pushoutProduct_left V h false _ L R S hs hS ht
      (fun b => ⟨fun hb => absurd hb (Set.notMem_empty b),
        fun hb => absurd hb.1 Bool.false_ne_true⟩)
      (sphereToMarkedBall V) rfl⟩

theorem exists_arrowIso_pushoutProduct_markedSphere_markedHornInclusion (V : Atom)
    (hV : 0 < V.dimension) (h : MarkedHornData) :
    ∃ h' : MarkedHornData, h'.atom = Atom.grayTensor V h.atom ∧
      Nonempty (Arrow.mk (Functor.PushoutObjObj.ofHasPushout
        (Functor.curry.obj (markedTensorBifunctor.{u} false))
        (sphereToMarkedBall V ≫ markingToMarkedBall V hV) (markedHornInclusion.{u} h)).ι ≅
          Arrow.mk (markedHornInclusion.{u} h')) := by
  obtain ⟨L, R, S, hs, hS, ht⟩ := h.exists_isStagedPasting_grayTensorLeft V
  refine ⟨h.grayTensorLeft V true (fun _ => hV) L R S hs hS ht, rfl,
    nonempty_arrowIso_pushoutProduct_left V h true _ L R S hs hS ht
      (fun b => ⟨fun hb => ⟨rfl, hb⟩, fun hb => hb.2⟩) _
      ((Functor.map_comp _ _ _).trans (Category.comp_id (sphereInclusion V)))⟩

open MorphismProperty HomotopicalAlgebra in
theorem MarkedDiagSet.Coinductive.weakEquivalence_pushoutProduct_mono_markedHornInclusion
    (n : ℕ∞) {X Y : MarkedDiagSet.{u}} (i : X ⟶ Y) [Mono i] (h : MarkedHornData) :
    WeakEquivalence ((MarkedDiagSet.toCoinductive n).map (Functor.PushoutObjObj.ofHasPushout
      (Functor.curry.obj (markedTensorBifunctor.{u} false)) i (markedHornInclusion.{u} h)).ι) := by
  let G := Functor.curry.obj (markedTensorBifunctor.{u} false)
  let α := G.flip.map (markedHornInclusion.{u} h)
  let T := (trivialCofibrations (MarkedDiagSet.Coinductive.{u} n)).inverseImage
    (MarkedDiagSet.toCoinductive n)
  have : IsSaturated.{u} (trivialCofibrations (MarkedDiagSet.Coinductive.{u} n)) := by
    rw [← fibrations_llp]; infer_instance
  have : PreservesColimitsOfSize.{u, u} (MarkedDiagSet.toCoinductive.{u} n) :=
    inferInstanceAs (PreservesColimitsOfSize (𝟭 MarkedDiagSet.{u}))
  have : ∀ W, PreservesColimitsOfSize.{u, u} (G.flip.obj W) := fun W =>
    inferInstanceAs (PreservesColimitsOfSize (tensorRight false W))
  have : ∀ W, PreservesColimitsOfShape WalkingSpan (G.flip.obj W) := fun W =>
    inferInstanceAs (PreservesColimitsOfShape WalkingSpan (tensorRight false W))
  have := NatTrans.isSaturated_leibnizPreimage.{u} α T
  have hbox {K Z : MarkedDiagSet.{u}} (j : K ⟶ Z) : NatTrans.leibnizPreimage α T j ↔
      T (Functor.PushoutObjObj.ofHasPushout G j (markedHornInclusion.{u} h)).ι :=
    T.arrow_mk_iso_iff (arrowIsoPushoutDescSymm _ _ _ _ _)
  have hhorn : ∀ h' : MarkedHornData, T (markedHornInclusion.{u} h') := fun h' =>
    coinductiveGenerators_le_trivialCofibrations n _ (Or.inl (Or.inl (.mk h')))
  have hsphere : ∀ V : Atom, NatTrans.leibnizPreimage α T (sphereToMarkedBall.{u} V) := fun V => by
    obtain ⟨h', -, ⟨e⟩⟩ := exists_arrowIso_pushoutProduct_sphere_markedHornInclusion.{u} V h
    exact (hbox _).2 ((T.arrow_mk_iso_iff e).2 (hhorn h'))
  have hmarked : ∀ (V : Atom) (hV : 0 < V.dimension),
      NatTrans.leibnizPreimage α T (markingToMarkedBall.{u} V hV) := fun V hV => by
    obtain ⟨h', -, ⟨e⟩⟩ :=
      exists_arrowIso_pushoutProduct_markedSphere_markedHornInclusion.{u} V hV h
    have hks : T (NatTrans.leibnizBox α (sphereToMarkedBall V ≫ markingToMarkedBall V hV)) :=
      (hbox _).2 ((T.arrow_mk_iso_iff e).2 (hhorn h'))
    have hpo := NatTrans.isPushout_leibnizSourceMap_of_comp α (sphereToMarkedBall V)
      (sphereToMarkedBall V ≫ markingToMarkedBall V hV) (markingToMarkedBall V hV) (by simp)
    have hc := T.of_isPushout hpo (hsphere V)
    have hfac := NatTrans.leibnizSourceMap_leibnizBox α (sphereToMarkedBall V) (𝟙 _)
      (i := sphereToMarkedBall V ≫ markingToMarkedBall V hV) (i' := markingToMarkedBall V hV)
      (by simp)
    rw [CategoryTheory.Functor.map_id, Category.comp_id (NatTrans.leibnizBox α _)] at hfac
    have := mono_markingToMarkedBall.{u} V hV
    have : Mono (markedHornInclusion.{u} h) := markedHorns_le_monomorphisms _ (.mk h)
    refine ⟨((monomorphisms _).arrow_mk_iso_iff (arrowIsoPushoutDescSymm _ _ _ _ _)).2
      (mono_markedPushoutProduct (markingToMarkedBall V hV) (markedHornInclusion h)), ?_⟩
    exact (weakEquivalences _).of_precomp _ _ hc.2 (hfac ▸ hks.2)
  have hmono : MorphismProperty.monomorphisms MarkedDiagSet.{u} =
      saturation.{u} (functorImage (MarkedPresheaf.flat atomMarking) sphereInclusions ⊔
        MarkedPresheaf.markingMaps atomMarking) :=
    (MarkedPresheaf.saturation_functorImage_flat_sup_markingMaps atomMarking
      monomorphisms_eq_saturation_sphereInclusions.symm).symm
  refine (weakEquivalence_iff _).2 ((hbox i).1 (saturation_le.{u} _ (NatTrans.leibnizPreimage α T)
    ?_ i ((congrArg (fun P : MorphismProperty MarkedDiagSet.{u} => P i) hmono).mp
      (MorphismProperty.monomorphisms.infer_property i)))).2
  rintro _ _ g (⟨K, Y, t, ht, e⟩ | ⟨a, ha⟩)
  · cases ht with
    | mk U =>
      exact ((NatTrans.leibnizPreimage α T).arrow_mk_iso_iff
        ((eqToIso e).symm ≪≫ flatSphereInclusionArrowIso U)).2 (hsphere U)
  · exact ((NatTrans.leibnizPreimage α T).arrow_mk_iso_iff (markingMapArrowIso a ha)).2
      (hmarked a ha)

end Atoms.Diagrammatic

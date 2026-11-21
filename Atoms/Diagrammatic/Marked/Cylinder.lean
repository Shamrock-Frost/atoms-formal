import Atoms.Diagrammatic.GrayCylinder.Exact
import Atoms.Diagrammatic.Marked.Basic
import Atoms.Homotopical.Marked.Extension

open CategoryTheory Limits Opposite MorphismProperty HomotopicalAlgebra
open Atoms.Homotopical Atoms.Molecule Atoms.Molecule.OGP Atoms.Shape

universe w w' u

namespace Atoms.Diagrammatic

theorem iso_hom_apply_top {U V : Atom} (e : U ≅ V) : e.hom U.top = V.top :=
  (isCollapseHom_of_iso e).apply_top

theorem grade_apply_top_le {V U : Atom} (c : V ⟶ U) : grade ℕ (c V.top) ≤ V.dimension := by
  rw [V.dimension_eq]
  exact (Atom.isMap c).grade_le _

theorem degenerate_of_grade_lt {V U : Atom} (c : V ⟶ U)
    (h : grade ℕ (c V.top) < V.dimension) : atomMarking.Degenerate c := by
  obtain ⟨W, p, i, hp, hi, rfl⟩ := exists_collapse_inclusion_factorization c
  refine ⟨W, p, i, ⟨hp, fun hpi => ?_⟩, rfl⟩
  have htop : p V.top = W.top :=
    hp.apply_top
  have hd := Atom.dimension_eq_of_iso (asIso p)
  change grade ℕ (i (p V.top)) < V.dimension at h
  rw [grade_eq_of_isInclusionHom i hi, htop, ← W.dimension_eq] at h
  exact absurd hd (Nat.ne_of_gt h)

theorem isDegenerate_ball_of_degenerate {V U : Atom} {c : V ⟶ U}
    (h : atomMarking.Degenerate c) : IsDegenerate (ball.{u} U) (ULift.up c) := by
  obtain ⟨W, p, q, ⟨hp, hni⟩, rfl⟩ := h
  exact ⟨W, p, ⟨q⟩, hp, hni, rfl⟩

theorem grade_grayCylinder_obj (U : Atom) (z : (grayCylinder.obj U).ogp) :
    grade ℕ z = grade ℕ ((cylAtomIso U).inv z).1 + grade ℕ ((cylAtomIso U).inv z).2 :=
  ((isMorphism (cylAtomIso U).inv).grade_eq z).symm

theorem symm_cylAtomIso_top (U : Atom) :
    (cylAtomIso U).inv (grayCylinder.obj U).top = ((⊤ : globe.{0} 1), U.top) := by
  have h (z : (grayCylinder.obj U).ogp) : z ≤ (cylAtomIso U).hom ((⊤ : globe.{0} 1), U.top) := by
    have hz : (cylAtomIso U).inv z ≤ ((⊤ : globe.{0} 1), U.top) := ⟨le_top, U.le_top _⟩
    have := (isMorphism (cylAtomIso U).hom).monotone hz
    rwa [Iso.inv_hom_id_apply] at this
  have htop : (grayCylinder.obj U).top = (cylAtomIso U).hom ((⊤ : globe.{0} 1), U.top) :=
    le_antisymm (h _) ((grayCylinder.obj U).le_top _)
  rw [htop]
  exact Iso.hom_inv_id_apply _ _

theorem fst_symm_cylAtomIso_le {U : Atom} {w z : (grayCylinder.obj U).ogp}
    (h : w ≤ z) : ((cylAtomIso U).inv w).1 ≤ ((cylAtomIso U).inv z).1 :=
  ((orderIsoOfIso (cylAtomIso U)).symm.monotone h).1

theorem eq_comp_grayContraction_comp_grayEndpoint {V U : Atom}
    (c : V ⟶ grayCylinder.obj U) (ε : Bool)
    (h : ((cylAtomIso U).inv (c V.top)).1 = SuspCarrier.pole ε) :
    c = (c ≫ grayContraction.app U) ≫ (grayEndpoint ε).app U := by
  refine Atom.hom_ext fun v => ?_
  have hv : ((cylAtomIso U).inv (c v)).1 = SuspCarrier.pole ε :=
    (SuspCarrier.isMin_pole ε).eq_of_le
      (h ▸ fst_symm_cylAtomIso_le ((Atom.isMap c).monotone (V.le_top v)))
  calc c v = (cylAtomIso U).hom ((cylAtomIso U).inv (c v)) := (Iso.inv_hom_id_apply _ _).symm
    _ = (cylAtomIso U).hom (SuspCarrier.pole ε, ((cylAtomIso U).inv (c v)).2) := by rw [← hv]
    _ = ((c ≫ grayContraction.app U) ≫ (grayEndpoint ε).app U) v := rfl

theorem exists_isCollapseHom_comp_grayCylinder_map_closureIncl {V U : Atom}
    (c : V ⟶ grayCylinder.obj U) (h : ((cylAtomIso U).inv (c V.top)).1 = ⊤) :
    ∃ p : V ⟶ grayCylinder.obj (Atom.ofClosure U ((cylAtomIso U).inv (c V.top)).2),
      IsCollapseHom p ∧
        p ≫ grayCylinder.map (Atom.closureIncl U ((cylAtomIso U).inv (c V.top)).2) = c := by
  set y := ((cylAtomIso U).inv (c V.top)).2 with hy
  set i := grayCylinder.map (Atom.closureIncl U y) with hi
  have hincl : IsInclusionHom i :=
    isInclusionHom_grayCylinder_map _ (Atom.isInclusionHom_closureIncl U y)
  have hex : ∀ t, ∃ a, i a = c t :=
    exists_grayCylinder_map_closureIncl_eq U y c fun t => snd_symm_le_snd_symm_top c t
  have := isIso_principalLift_of_isInclusionHom i hincl
  let q := principalLift (grayCylinder.obj U) (i (grayCylinder.obj (Atom.ofClosure U y)).top) i
    (apply_mem_closure_apply_top i)
  let r := principalLift (grayCylinder.obj U) (i (grayCylinder.obj (Atom.ofClosure U y)).top) c
    (mem_closure_apply_top_of_exists_eq i hex)
  have hq : inv q ≫ i = Atom.closureIncl _ _ := by
    rw [IsIso.inv_comp_eq]
    exact (principalLift_comp_closureIncl _ _ _ _).symm
  have hpi : (r ≫ inv q) ≫ i = c := by
    rw [Category.assoc, hq]
    exact principalLift_comp_closureIncl _ _ _ _
  refine ⟨r ≫ inv q, isCollapseHom_of_apply_eq_top _ (t := V.top) (hincl ?_), hpi⟩
  rw [← ConcreteCategory.comp_apply, hpi]
  apply IsInclusion.injective (f := (cylAtomIso U).inv)
  rw [hi, symm_grayCylinder_map_apply, symm_cylAtomIso_top, Atom.closureIncl_top]
  exact Prod.ext h rfl

def ballMarking (U : Atom) (M : Set U.ogp) (hM : ∀ z ∈ M, 0 < grade ℕ z) :
    MarkedPresheaf.Marking atomMarking (ball.{u} U) where
  marked V := {c : ULift (V ⟶ U) | IsDegenerate (ball U) c ∨ c.down V.top ∈ M}
  markable V c h := h.elim dimension_pos_of_isDegenerate fun h =>
    lt_of_lt_of_le (hM _ h) (grade_apply_top_le c.down)
  degenerate _ b p hp y := Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport V W e (c : ULift (W ⟶ U)) :=
    or_congr (isDegenerate_map_iso_iff (X := ball U) e c).symm (by
      change c.down W.top ∈ M ↔ c.down (e.hom V.top) ∈ M
      rw [iso_hom_apply_top])

def cylinderMarked (x : MarkedSite atomMarking) : Set (grayCylinder.obj x.obj).ogp :=
  {z | ((cylAtomIso x.obj).inv z).1 = ⊤ ∨
    (x.isMarked = true ∧ ((cylAtomIso x.obj).inv z).2 = x.obj.top)}

theorem pos_grade_of_mem_cylinderMarked (x : MarkedSite atomMarking) :
    ∀ z ∈ cylinderMarked x, 0 < grade ℕ z := by
  intro z hz
  rw [grade_grayCylinder_obj]
  rcases hz with h | ⟨hx, h⟩
  · rw [h, grade_top_globe]
    omega
  · rw [h, ← x.obj.dimension_eq]
    exact Nat.lt_add_left _ (x.markable hx)

private theorem comp_grayCylinder_map_mem {x y : MarkedSite atomMarking} (g : x ⟶ y) {V : Atom}
    (c : V ⟶ grayCylinder.obj x.obj)
    (hc : ULift.up c ∈
      (ballMarking.{u} _ (cylinderMarked x) (pos_grade_of_mem_cylinderMarked x)).marked V) :
    ULift.up (c ≫ grayCylinder.map g.1) ∈
      (ballMarking.{u} _ (cylinderMarked y) (pos_grade_of_mem_cylinderMarked y)).marked V := by
  rcases hc with hd | hz
  · exact Or.inl (isDegenerate_app (uliftYoneda.{u}.map (grayCylinder.map g.1)) hd)
  · have hs := symm_grayCylinder_map_apply g.1 (c V.top)
    rcases hz with h1 | ⟨hx, htop⟩
    · refine Or.inr (Or.inl ?_)
      change ((cylAtomIso y.obj).inv (grayCylinder.map g.1 (c V.top))).1 = ⊤
      rw [hs]
      exact h1
    · rcases g.2 hx with ⟨hy, hg⟩ | hg
      · refine Or.inr (Or.inr ⟨hy, ?_⟩)
        change ((cylAtomIso y.obj).inv (grayCylinder.map g.1 (c V.top))).2 = y.obj.top
        rw [hs, htop]
        exact iso_hom_apply_top (asIso g.1)
      · refine Or.inl (isDegenerate_ball_of_degenerate (degenerate_of_grade_lt _ ?_))
        change grade ℕ (grayCylinder.map g.1 (c V.top)) < _
        rw [grade_grayCylinder_obj, hs, htop]
        have h₁ : grade ℕ (g.1 x.obj.top) < x.obj.dimension := by
          obtain ⟨d, p, q, ⟨hp, hni⟩, hpq⟩ := hg
          have h₃ := dimension_le_of_isCollapseHom p hp
          have h₄ : d.dimension ≠ x.obj.dimension := fun h =>
            hni (isIso_of_isCollapseHom_of_dimension_eq p hp h.symm)
          have h₅ : grade ℕ ((p ≫ q) x.obj.top) < x.obj.dimension :=
            lt_of_le_of_lt (((Atom.isMap q).grade_le _).trans
              ((grade_mono (d.le_top _)).trans d.dimension_eq.ge)) (lt_of_le_of_ne h₃ h₄)
          rwa [hpq] at h₅
        have h₂ := grade_apply_top_le c
        rw [grade_grayCylinder_obj, htop, ← x.obj.dimension_eq] at h₂
        dsimp only
        omega

noncomputable def markedCylinderSite : MarkedSite atomMarking ⥤ MarkedDiagSet.{u} where
  obj x := MarkedPresheaf.ofMarking (ball (grayCylinder.obj x.obj))
    (ballMarking _ (cylinderMarked x) (pos_grade_of_mem_cylinderMarked x))
  map g := MarkedPresheaf.homMk (uliftYoneda.{u}.map (grayCylinder.map g.1)) fun V c hc =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (comp_grayCylinder_map_mem g c.down ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hc))
  map_id x := MarkedPresheaf.hom_ext (by
    change uliftYoneda.{u}.map (grayCylinder.map (𝟙 x.obj)) = 𝟙 _
    rw [grayCylinder.map_id, uliftYoneda.{u}.map_id])
  map_comp f g := MarkedPresheaf.hom_ext (by
    change uliftYoneda.{u}.map (grayCylinder.map (f.1 ≫ g.1)) =
      uliftYoneda.{u}.map (grayCylinder.map f.1) ≫ uliftYoneda.{u}.map (grayCylinder.map g.1)
    rw [grayCylinder.map_comp, uliftYoneda.{u}.map_comp])

theorem mem_marked_yoneda_obj_iff (x : MarkedSite atomMarking) (V : Atom)
    (g : ((MarkedPresheaf.yoneda.{u} atomMarking).obj x).underlying.obj (op V)) :
    g ∈ ((MarkedPresheaf.yoneda atomMarking).obj x).marked V ↔
      0 < V.dimension ∧
        ((x.isMarked = true ∧ IsIso g.down.1) ∨ atomMarking.Degenerate g.down.1) := by
  constructor
  · rintro ⟨hV, ⟨h⟩, rfl⟩
    exact ⟨hV, h.2 rfl⟩
  · rintro ⟨hV, hg⟩
    exact ⟨hV, ⟨⟨g.down.1, fun _ => hg⟩⟩, ULift.ext _ _ (MarkedSite.hom_ext (Category.id_comp _))⟩

noncomputable def markedCylinderSiteEndpoint (ε : Bool) :
    MarkedPresheaf.yoneda atomMarking ⟶ markedCylinderSite.{u} where
  app x := MarkedPresheaf.homMk (Y := markedCylinderSite.obj x)
    { app V := ↾fun g => ULift.up (g.down.1 ≫ (grayEndpoint ε).app x.obj :
        V.unop ⟶ grayCylinder.obj x.obj)
      naturality _ _ _ := rfl }
    fun V g hg => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (by
      obtain ⟨-, ⟨hx, hi⟩ | ⟨W, p, q, hp, hpq⟩⟩ := (mem_marked_yoneda_obj_iff x V g).1 hg
      · refine Or.inr (Or.inr ⟨hx, ?_⟩)
        change ((cylAtomIso x.obj).inv ((grayEndpoint ε).app x.obj (g.down.1 V.top))).2 = _
        rw [symm_grayEndpoint_apply]
        exact iso_hom_apply_top (asIso g.down.1)
      · refine Or.inl ⟨W, p, ⟨q ≫ (grayEndpoint ε).app x.obj⟩, hp.1, hp.2, ?_⟩
        change ULift.up (p ≫ q ≫ _) = ULift.up (g.down.1 ≫ _)
        rw [← Category.assoc, hpq])
  naturality x y f := MarkedPresheaf.hom_ext (by
    ext V ⟨g⟩
    exact congrArg (fun k => ULift.up (g.1 ≫ k)) ((grayEndpoint ε).naturality f.1))

theorem forget_map_markedCylinderSiteEndpoint_app_app (ε : Bool) (x : MarkedSite atomMarking)
    (V : Atom) (g : (MarkedSite.unmarked atomMarking).obj V ⟶ x) :
    (MarkedPresheaf.forget.map ((markedCylinderSiteEndpoint.{u} ε).app x)).app (op V) ⟨g⟩ =
      ULift.up (g.1 ≫ (grayEndpoint ε).app x.obj) :=
  rfl

private theorem comp_grayContraction_mem {x : MarkedSite atomMarking} {V : Atom}
    (c : V ⟶ grayCylinder.obj x.obj)
    (hc : ULift.up c ∈
      (ballMarking.{u} _ (cylinderMarked x) (pos_grade_of_mem_cylinderMarked x)).marked V) :
    (x.isMarked = true ∧ IsIso (c ≫ grayContraction.app x.obj)) ∨
      atomMarking.Degenerate (c ≫ grayContraction.app x.obj) := by
  rcases hc with ⟨W, p, ⟨y⟩, hp, hni, hy⟩ | h1 | ⟨hx, htop⟩
  · obtain rfl : p ≫ y = c := congrArg ULift.down hy
    exact Or.inr ⟨W, p, y ≫ grayContraction.app x.obj, ⟨hp, hni⟩, rfl⟩
  · refine Or.inr (degenerate_of_grade_lt _ ?_)
    have h₂ := grade_apply_top_le c
    rw [grade_grayCylinder_obj, h1, grade_top_globe] at h₂
    change grade ℕ ((cylAtomIso x.obj).inv (c V.top)).2 < _
    omega
  · have hcol := isCollapseHom_of_apply_eq_top (c ≫ grayContraction.app x.obj) htop
    by_cases hi : IsIso (c ≫ grayContraction.app x.obj)
    · exact Or.inl ⟨hx, hi⟩
    · exact Or.inr (.of_degeneracy ⟨hcol, hi⟩)

noncomputable def markedCylinderSiteContraction :
    markedCylinderSite.{u} ⟶ MarkedPresheaf.yoneda atomMarking where
  app x := MarkedPresheaf.homMk (X := markedCylinderSite.obj x)
    { app V := ↾fun c => ULift.up (⟨(c.down : V.unop ⟶ grayCylinder.obj x.obj) ≫
        grayContraction.app x.obj, fun h => absurd h Bool.false_ne_true⟩ :
          (MarkedSite.unmarked atomMarking).obj V.unop ⟶ x)
      naturality _ _ _ := rfl }
    fun V c hc => by
      have hc' := (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hc
      exact (mem_marked_yoneda_obj_iff x V _).2
        ⟨(ballMarking _ _ (pos_grade_of_mem_cylinderMarked x)).markable V c hc',
          comp_grayContraction_mem c.down hc'⟩
  naturality x y f := MarkedPresheaf.hom_ext (by
    ext V c
    exact ULift.ext _ _
      (MarkedSite.hom_ext (congrArg (c.down ≫ ·) (grayContraction.naturality f.1))))

theorem forget_map_markedCylinderSiteContraction_app_app (x : MarkedSite atomMarking)
    (V : Atom) (c : V ⟶ grayCylinder.obj x.obj) :
    ((MarkedPresheaf.forget.map (markedCylinderSiteContraction.{u}.app x)).app (op V) ⟨c⟩).down.1 =
      c ≫ grayContraction.app x.obj :=
  rfl

theorem grayCylinderFunctor_map_app_grayCylinderUnit_app {P Q : DiagSet.{u}} (φ : P ⟶ Q) (U : Atom)
    (a : P.obj (op U)) :
    (grayCylinderFunctor.map φ).app (op (grayCylinder.obj U)) ((grayCylinderUnit P).app (op U) a) =
      (grayCylinderUnit Q).app (op U) (φ.app (op U) a) :=
  (ConcreteCategory.congr_hom (NatTrans.congr_app (grayCylinderUnit_naturality φ) (op U)) a).symm

theorem grayCylinderContraction_app_app_grayCylinderUnit_app (P : DiagSet.{u}) (U : Atom)
    (a : P.obj (op U)) :
    (grayCylinderContraction.app P).app (op (grayCylinder.obj U))
        ((grayCylinderUnit P).app (op U) a) =
      P.map (grayContraction.app U).op a :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (grayCylinderUnit_comp_grayCylinderContractionApp P) (op U)) a

private theorem grayCylinderFunctorBallIso_inv_app_id (U : Atom) :
    (grayCylinderFunctorBallIso.{u} U).inv.app (op (grayCylinder.obj U)) ⟨𝟙 (grayCylinder.obj U)⟩ =
      (grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩ := by
  have h : (grayCylinderFunctorBallIso U).hom.app (op (grayCylinder.obj U))
      ((grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩) = ⟨𝟙 (grayCylinder.obj U)⟩ :=
    (ConcreteCategory.congr_hom (NatTrans.congr_app
      (grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom U) (op U)) ⟨𝟙 U⟩).trans
        (congrArg ULift.up (grayCylinder.map_id U))
  exact (congrArg ((grayCylinderFunctorBallIso U).inv.app (op (grayCylinder.obj U))) h).symm.trans
    (Iso.hom_inv_id_app_apply _ _ _)

private theorem grayCylinderFunctorBallIso_inv_app (U V : Atom) (f : V ⟶ grayCylinder.obj U) :
    (grayCylinderFunctorBallIso.{u} U).inv.app (op V) ⟨f⟩ =
      (grayCylinderFunctor.obj (ball U)).map f.op ((grayCylinderUnit (ball U)).app (op U) ⟨𝟙 U⟩) :=
  (NatTrans.naturality_apply (grayCylinderFunctorBallIso U).inv f.op
    ⟨𝟙 (grayCylinder.obj U)⟩).trans
    (congrArg ((grayCylinderFunctor.obj (ball U)).map f.op)
      (grayCylinderFunctorBallIso_inv_app_id U))

noncomputable abbrev markedCylinder : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} :=
  MarkedPresheaf.extend markedCylinderSite

private theorem epi_markedCylinderSite_map_toSelf (x : MarkedSite atomMarking) :
    Epi (markedCylinderSite.{u}.map (MarkedSite.toSelf x)) :=
  have : Epi (uliftYoneda.{u}.map (grayCylinder.map (𝟙 x.obj))) := by
    rw [grayCylinder.map_id, uliftYoneda.{u}.map_id]
    infer_instance
  MarkedPresheaf.forget.epi_of_epi_map this

private noncomputable def markedCylinderAdjunction :
    markedCylinder.{u} ⊣
      MarkedPresheaf.nerve markedCylinderSite epi_markedCylinderSite_map_toSelf :=
  MarkedPresheaf.extendAdjunction _ _

instance preservesColimitsOfSize_markedCylinder :
    PreservesColimitsOfSize.{w, w'} markedCylinder.{u} :=
  markedCylinderAdjunction.leftAdjoint_preservesColimits

instance preservesColimitsOfSize_forget :
    PreservesColimitsOfSize.{w, w'} (MarkedPresheaf.forget.{u, 0} (D := atomMarking)) :=
  (MarkedPresheaf.forgetSharpAdjunction atomMarking).leftAdjoint_preservesColimits

def ballIsoForgetYoneda (x : MarkedSite atomMarking) :
    ball x.obj ≅ MarkedPresheaf.forget.obj ((MarkedPresheaf.yoneda.{u} atomMarking).obj x) where
  hom := { app V := ↾fun g => ULift.up (⟨g.down, fun h => absurd h Bool.false_ne_true⟩ :
      (MarkedSite.unmarked atomMarking).obj V.unop ⟶ x), naturality _ _ _ := rfl }
  inv := { app V := ↾fun g => ULift.up (g.down.1 : V.unop ⟶ x.obj), naturality _ _ _ := rfl }

private noncomputable def markedCylinderSiteForgetIso :
    markedCylinderSite.{u} ⋙ MarkedPresheaf.forget ≅
      MarkedPresheaf.yoneda atomMarking ⋙ MarkedPresheaf.forget ⋙ grayCylinderFunctor :=
  NatIso.ofComponents (fun x => (grayCylinderFunctorBallIso x.obj).symm ≪≫
      grayCylinderFunctor.mapIso (ballIsoForgetYoneda x)) fun {x y} g => by
    obtain ⟨g, hg⟩ := g
    have h₁ : uliftYoneda.{u}.map (grayCylinder.map g) ≫ (grayCylinderFunctorBallIso y.obj).inv =
        (grayCylinderFunctorBallIso x.obj).inv ≫ grayCylinderFunctor.map (uliftYoneda.{u}.map g) :=
      grayCylinderFunctorYonedaIso.inv.naturality g
    have h₂ : uliftYoneda.{u}.map g ≫ (ballIsoForgetYoneda y).hom = (ballIsoForgetYoneda x).hom ≫
        MarkedPresheaf.forget.map ((MarkedPresheaf.yoneda atomMarking).map ⟨g, hg⟩) := rfl
    change uliftYoneda.{u}.map (grayCylinder.map g) ≫ (grayCylinderFunctorBallIso y.obj).inv ≫
        grayCylinderFunctor.map (ballIsoForgetYoneda y).hom =
      ((grayCylinderFunctorBallIso x.obj).inv ≫
        grayCylinderFunctor.map (ballIsoForgetYoneda x).hom) ≫
          grayCylinderFunctor.map (MarkedPresheaf.forget.map
            ((MarkedPresheaf.yoneda atomMarking).map ⟨g, hg⟩))
    rw [← Category.assoc, h₁, Category.assoc, Category.assoc]
    exact congrArg ((grayCylinderFunctorBallIso x.obj).inv ≫ ·)
      ((grayCylinderFunctor.map_comp _ _).symm.trans ((congrArg grayCylinderFunctor.map h₂).trans
        (grayCylinderFunctor.map_comp _ _)))

noncomputable def markedCylinderForgetIso :
    markedCylinder.{u} ⋙ MarkedPresheaf.forget ≅ MarkedPresheaf.forget ⋙ grayCylinderFunctor :=
  MarkedPresheaf.isoOfPreservesColimits (G := markedCylinder ⋙ MarkedPresheaf.forget)
    (H := MarkedPresheaf.forget ⋙ grayCylinderFunctor) ((Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (MarkedPresheaf.yonedaCompExtendIso markedCylinderSite) _ ≪≫
      markedCylinderSiteForgetIso)

private theorem markedCylinderForgetIso_hom_app_yoneda_obj (x : MarkedSite atomMarking) :
    markedCylinderForgetIso.hom.app ((MarkedPresheaf.yoneda atomMarking).obj x) =
      MarkedPresheaf.forget.map
          ((MarkedPresheaf.yonedaCompExtendIso markedCylinderSite.{u}).hom.app x) ≫
        markedCylinderSiteForgetIso.hom.app x := by
  have h := NatTrans.congr_app (MarkedPresheaf.whiskerLeft_yoneda_isoOfPreservesColimits_hom
    (G := markedCylinder ⋙ MarkedPresheaf.forget)
    (H := MarkedPresheaf.forget ⋙ grayCylinderFunctor) ((Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (MarkedPresheaf.yonedaCompExtendIso markedCylinderSite)
        MarkedPresheaf.forget ≪≫ markedCylinderSiteForgetIso)) x
  refine h.trans ?_
  simp

private theorem forget_map_markedCylinderSiteEndpoint_app_comp (ε : Bool)
    (x : MarkedSite atomMarking) :
    MarkedPresheaf.forget.map ((markedCylinderSiteEndpoint.{u} ε).app x) ≫
        markedCylinderSiteForgetIso.hom.app x =
      (grayCylinderEndpoint ε).app
        (MarkedPresheaf.forget.obj ((MarkedPresheaf.yoneda atomMarking).obj x)) := by
  rw [← cancel_epi (ballIsoForgetYoneda x).hom]
  refine uliftYonedaEquiv.injective ?_
  change (grayCylinderFunctor.map (ballIsoForgetYoneda x).hom).app (op x.obj)
      ((grayCylinderFunctorBallIso x.obj).inv.app (op x.obj) ⟨(grayEndpoint ε).app x.obj⟩) =
    (grayCylinderFunctor.obj (MarkedPresheaf.forget.obj
      ((MarkedPresheaf.yoneda atomMarking).obj x))).map ((grayEndpoint ε).app x.obj).op
        ((grayCylinderUnit _).app (op x.obj) ((ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩))
  exact (congrArg _ (grayCylinderFunctorBallIso_inv_app _ _ _)).trans
    ((NatTrans.naturality_apply _ _ _).trans
      (congrArg _ (grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _)))

private theorem markedCylinderSiteForgetIso_hom_app_comp_grayCylinderContraction
    (x : MarkedSite atomMarking) :
    markedCylinderSiteForgetIso.{u}.hom.app x ≫ grayCylinderContraction.app
        (MarkedPresheaf.forget.obj ((MarkedPresheaf.yoneda atomMarking).obj x)) =
      MarkedPresheaf.forget.map (markedCylinderSiteContraction.app x) := by
  refine uliftYonedaEquiv.injective ?_
  change (grayCylinderContraction.app _).app _ ((grayCylinderFunctor.map
      (ballIsoForgetYoneda x).hom).app _ ((grayCylinderFunctorBallIso x.obj).inv.app _
        ⟨𝟙 (grayCylinder.obj x.obj)⟩)) =
    (MarkedPresheaf.forget.obj ((MarkedPresheaf.yoneda atomMarking).obj x)).map
      (grayContraction.app x.obj).op ((ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩)
  exact (congrArg _ ((congrArg _ (grayCylinderFunctorBallIso_inv_app_id _)).trans
    (grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _))).trans
      (grayCylinderContraction_app_app_grayCylinderUnit_app _ _ _)

private theorem whiskerRight_endpoint_forget_comp_aux (ε : Bool) :
    Functor.whiskerRight ((MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
        MarkedPresheaf.extendMap (markedCylinderSiteEndpoint.{u} ε)) MarkedPresheaf.forget ≫
        markedCylinderForgetIso.hom =
      Functor.whiskerLeft MarkedPresheaf.forget (grayCylinderEndpoint ε) := by
  refine MarkedPresheaf.hom_ext_of_preservesColimits (NatTrans.ext (funext fun x => ?_))
  change MarkedPresheaf.forget.map (((MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
      MarkedPresheaf.extendMap (markedCylinderSiteEndpoint ε)).app
        ((MarkedPresheaf.yoneda atomMarking).obj x)) ≫
      markedCylinderForgetIso.hom.app ((MarkedPresheaf.yoneda atomMarking).obj x) = _
  rw [NatTrans.comp_app, MarkedPresheaf.extendYonedaIso_inv_app_yoneda_obj,
    MarkedPresheaf.extendMap_app_yoneda_obj, Iso.inv_hom_id_app_assoc,
    markedCylinderForgetIso_hom_app_yoneda_obj, Functor.map_comp, Category.assoc,
    ← Functor.map_comp_assoc MarkedPresheaf.forget
      ((MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).inv.app x),
    Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp,
    forget_map_markedCylinderSiteEndpoint_app_comp]
  rfl

private theorem markedCylinderForgetIso_hom_comp_aux :
    markedCylinderForgetIso.hom ≫
        Functor.whiskerLeft MarkedPresheaf.forget grayCylinderContraction =
      Functor.whiskerRight (MarkedPresheaf.extendMap markedCylinderSiteContraction.{u} ≫
        (MarkedPresheaf.extendYonedaIso atomMarking).hom) MarkedPresheaf.forget := by
  refine MarkedPresheaf.hom_ext_of_preservesColimits (NatTrans.ext (funext fun x => ?_))
  change markedCylinderForgetIso.hom.app ((MarkedPresheaf.yoneda atomMarking).obj x) ≫
      grayCylinderContraction.app _ = MarkedPresheaf.forget.map
        ((MarkedPresheaf.extendMap markedCylinderSiteContraction ≫
          (MarkedPresheaf.extendYonedaIso atomMarking).hom).app
            ((MarkedPresheaf.yoneda atomMarking).obj x))
  have h := NatTrans.congr_app (MarkedPresheaf.whiskerLeft_yoneda_extendYonedaIso_hom atomMarking) x
  rw [Functor.whiskerLeft_app] at h
  rw [NatTrans.comp_app, h, MarkedPresheaf.extendMap_app_yoneda_obj, Category.assoc,
    Category.assoc, Iso.inv_hom_id_app, markedCylinderForgetIso_hom_app_yoneda_obj,
    Category.assoc, markedCylinderSiteForgetIso_hom_app_comp_grayCylinderContraction,
    ← Functor.map_comp]
  rfl

noncomputable def markedExactCylinder : ExactCylinder.{u} MarkedDiagSet.{u} where
  I := markedCylinder
  endpoint ε := (MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
    MarkedPresheaf.extendMap (markedCylinderSiteEndpoint ε)
  contraction := MarkedPresheaf.extendMap markedCylinderSiteContraction ≫
    (MarkedPresheaf.extendYonedaIso atomMarking).hom
  endpoint_contraction ε := by
    have h : markedCylinderSiteEndpoint ε ≫ markedCylinderSiteContraction = 𝟙 _ :=
      NatTrans.ext (funext fun x => MarkedPresheaf.hom_ext (by
        ext V ⟨g⟩
        exact ULift.ext _ _
          (MarkedSite.hom_ext (congrArg (g.1 ≫ ·) (grayEndpoint_grayContraction ε x.obj)))))
    rw [Category.assoc, ← Category.assoc (MarkedPresheaf.extendMap _),
      ← MarkedPresheaf.extendMap_comp, h, MarkedPresheaf.extendMap_id, Category.id_comp,
      Iso.inv_hom_id]
  mono_endpoints X := by
    rw [MarkedPresheaf.mono_iff]
    have he (ε : Bool) := NatTrans.congr_app (whiskerRight_endpoint_forget_comp_aux ε) X
    have hc : coprodComparison MarkedPresheaf.forget X X ≫ MarkedPresheaf.forget.map
        (coprod.desc (((MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
          MarkedPresheaf.extendMap (markedCylinderSiteEndpoint false)).app X)
          (((MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
            MarkedPresheaf.extendMap (markedCylinderSiteEndpoint true)).app X)) ≫
          markedCylinderForgetIso.hom.app X =
        coprod.desc ((grayCylinderEndpoint false).app (MarkedPresheaf.forget.obj X))
          ((grayCylinderEndpoint true).app (MarkedPresheaf.forget.obj X)) := by
      ext1
      · rw [coprodComparison_inl_assoc, ← Functor.map_comp_assoc, coprod.inl_desc,
          coprod.inl_desc]
        exact he false
      · rw [coprodComparison_inr_assoc, ← Functor.map_comp_assoc, coprod.inr_desc,
          coprod.inr_desc]
        exact he true
    have hm : Mono (coprodComparison MarkedPresheaf.forget X X ≫ MarkedPresheaf.forget.map
        (coprod.desc (((MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
          MarkedPresheaf.extendMap (markedCylinderSiteEndpoint false)).app X)
          (((MarkedPresheaf.extendYonedaIso atomMarking).inv ≫
            MarkedPresheaf.extendMap (markedCylinderSiteEndpoint true)).app X)) ≫
          markedCylinderForgetIso.hom.app X) := by
      rw [hc]
      infer_instance
    have hm' := ((MorphismProperty.monomorphisms _).cancel_left_of_respectsIso _ _).1 hm
    exact @mono_of_mono _ _ _ _ _ _ (markedCylinderForgetIso.hom.app X) hm'
  preservesMonomorphisms := ⟨fun {X Y} f hf => by
    rw [MarkedPresheaf.mono_iff] at hf ⊢
    have := mono_grayCylinderFunctor_map (MarkedPresheaf.forget.map f)
    have e : MarkedPresheaf.forget.map (markedCylinder.map f) =
        markedCylinderForgetIso.hom.app X ≫
          grayCylinderFunctor.map (MarkedPresheaf.forget.map f) ≫
            markedCylinderForgetIso.inv.app Y :=
      (NatIso.naturality_2 markedCylinderForgetIso f).symm
    rw [e]
    infer_instance⟩

theorem whiskerRight_endpoint_forget_comp_markedCylinderForgetIso_hom (ε : Bool) :
    Functor.whiskerRight (markedExactCylinder.{u}.endpoint ε) MarkedPresheaf.forget ≫
        markedCylinderForgetIso.hom =
      Functor.whiskerLeft MarkedPresheaf.forget (grayCylinderEndpoint ε) :=
  whiskerRight_endpoint_forget_comp_aux ε

theorem markedCylinderForgetIso_hom_comp_whiskerLeft_contraction :
    markedCylinderForgetIso.{u}.hom ≫
        Functor.whiskerLeft MarkedPresheaf.forget grayCylinderContraction =
      Functor.whiskerRight markedExactCylinder.contraction MarkedPresheaf.forget :=
  markedCylinderForgetIso_hom_comp_aux

private theorem exists_iso_map_eq_iff {P : DiagSet.{u}} {V V' W : Atom} (e' : V' ≅ V)
    (c : P.obj (op V)) (d : P.obj (op W)) :
    (∃ e : V ≅ W, c = P.map e.hom.op d) ↔ ∃ e : V' ≅ W, P.map e'.hom.op c = P.map e.hom.op d := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e' ≪≫ e, (Functor.map_comp_apply P _ _ d).symm⟩
  · rintro ⟨e, he⟩
    refine ⟨e'.symm ≪≫ e, ?_⟩
    rw [Iso.trans_hom, Iso.symm_hom, op_comp, Functor.map_comp_apply, ← he,
      ← Functor.map_comp_apply, ← op_comp, e'.inv_hom_id, op_id, Functor.map_id_apply]

private def cylinderMarking (Y : MarkedDiagSet.{u}) :
    MarkedPresheaf.Marking atomMarking (grayCylinderFunctor.obj (MarkedPresheaf.forget.obj Y)) where
  marked V := {c | IsDegenerate _ c ∨
    (∃ (U : Atom) (y : (MarkedPresheaf.forget.obj Y).obj (op U)) (e : V ≅ grayCylinder.obj U),
      c = (grayCylinderFunctor.obj (MarkedPresheaf.forget.obj Y)).map e.hom.op
        ((grayCylinderUnit (MarkedPresheaf.forget.obj Y)).app (op U) y)) ∨
    ∃ (ε : Bool) (U : Atom) (m : (MarkedPresheaf.forget.obj Y).obj (op U)), m ∈ Y.marked U ∧
      ∃ e : V ≅ U, c = (grayCylinderFunctor.obj (MarkedPresheaf.forget.obj Y)).map e.hom.op
        (((grayCylinderEndpoint ε).app (MarkedPresheaf.forget.obj Y)).app (op U) m)}
  markable V c h := by
    change 0 < V.dimension
    rcases h with h | ⟨U, y, e, -⟩ | ⟨ε, U, m, hm, e, -⟩
    · exact dimension_pos_of_isDegenerate h
    · rw [Atom.dimension_eq_of_iso e, dimension_grayCylinder_obj]
      exact Nat.succ_pos _
    · rw [Atom.dimension_eq_of_iso e]
      exact Y.markable U m hm
  degenerate _ b p hp y := Or.inl ⟨b, p, y, hp.1, hp.2, rfl⟩
  transport V W e c := or_congr (isDegenerate_map_iso_iff e c).symm (or_congr
    (exists_congr fun U => exists_congr fun y => exists_iso_map_eq_iff e c _)
    (exists_congr fun ε => exists_congr fun U => exists_congr fun m =>
      and_congr_right fun _ => exists_iso_map_eq_iff e c _))

private theorem grayCylinderFunctor_map_mem_cylinderMarking {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y')
    {V : Atom} {c : (grayCylinderFunctor.obj (MarkedPresheaf.forget.obj Y)).obj (op V)}
    (hc : c ∈ (cylinderMarking Y).marked V) :
    (grayCylinderFunctor.map (MarkedPresheaf.forget.map f)).app (op V) c ∈
      (cylinderMarking Y').marked V := by
  rcases hc with h | ⟨U, y, e, rfl⟩ | ⟨ε, U, m, hm, e, rfl⟩
  · exact Or.inl (isDegenerate_app _ h)
  · exact Or.inr (Or.inl ⟨U, (MarkedPresheaf.forget.map f).app (op U) y, e,
      (NatTrans.naturality_apply _ _ _).trans
        (congrArg _ (grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _))⟩)
  · exact Or.inr (Or.inr ⟨ε, U, (MarkedPresheaf.forget.map f).app (op U) m,
      MarkedPresheaf.map_mem_marked f hm, e, (NatTrans.naturality_apply _ _ _).trans
        (congrArg _ (ConcreteCategory.congr_hom (NatTrans.congr_app
          ((grayCylinderEndpoint ε).naturality (MarkedPresheaf.forget.map f)) (op U)) m).symm)⟩)

private noncomputable def markedCylinderModel : MarkedDiagSet.{u} ⥤ MarkedDiagSet.{u} where
  obj Y := MarkedPresheaf.ofMarking _ (cylinderMarking Y)
  map {Y Y'} f := MarkedPresheaf.homMk (grayCylinderFunctor.map (MarkedPresheaf.forget.map f))
    fun V c hc => (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2
      (grayCylinderFunctor_map_mem_cylinderMarking f
        ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hc))
  map_id Y := MarkedPresheaf.hom_ext (by
    change grayCylinderFunctor.map (MarkedPresheaf.forget.map (𝟙 Y)) = 𝟙 _
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id])
  map_comp f g := MarkedPresheaf.hom_ext (by
    change grayCylinderFunctor.map (MarkedPresheaf.forget.map (f ≫ g)) =
      grayCylinderFunctor.map (MarkedPresheaf.forget.map f) ≫
        grayCylinderFunctor.map (MarkedPresheaf.forget.map g)
    rw [Functor.map_comp, Functor.map_comp])

private theorem markedCylinderSiteForgetIso_hom_app_app (x : MarkedSite atomMarking) (V : Atom)
    (c : V ⟶ grayCylinder.obj x.obj) :
    (markedCylinderSiteForgetIso.hom.app x).app (op V) ⟨c⟩ =
      (grayCylinderFunctor.obj (MarkedPresheaf.forget.obj
        ((MarkedPresheaf.yoneda atomMarking).obj x))).map c.op
          ((grayCylinderUnit _).app (op x.obj) ((ballIsoForgetYoneda.{u} x).hom.app (op x.obj)
            ⟨𝟙 x.obj⟩)) :=
  (congrArg _ (grayCylinderFunctorBallIso_inv_app _ _ _)).trans
    ((NatTrans.naturality_apply _ _ _).trans
      (congrArg _ (grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _)))

private theorem markedCylinderSiteForgetIso_hom_app_app_mem_of_fst_eq_top
    (x : MarkedSite atomMarking) (V : Atom) (c : V ⟶ grayCylinder.obj x.obj)
    (h1 : ((cylAtomIso x.obj).inv (c V.top)).1 = ⊤) :
    (markedCylinderSiteForgetIso.{u}.hom.app x).app (op V) ⟨c⟩ ∈
      (cylinderMarking ((MarkedPresheaf.yoneda atomMarking).obj x)).marked V := by
  obtain ⟨p, hp, hpc⟩ := exists_isCollapseHom_comp_grayCylinder_map_closureIncl c h1
  by_cases hi : IsIso p
  · refine Or.inr (Or.inl ⟨_, (MarkedPresheaf.forget.obj
      ((MarkedPresheaf.yoneda atomMarking).obj x)).map (Atom.closureIncl _ _).op
        ((ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩), asIso p,
      (markedCylinderSiteForgetIso_hom_app_app x V c).trans ?_⟩)
    exact (congrArg (fun t : V ⟶ grayCylinder.obj x.obj =>
      (grayCylinderFunctor.obj _).map t.op ((grayCylinderUnit _).app (op x.obj)
        ((ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩))) hpc.symm).trans
      ((Functor.map_comp_apply _ _ _ _).trans
        (congrArg _ (NatTrans.naturality_apply (grayCylinderUnit (MarkedPresheaf.forget.obj
          ((MarkedPresheaf.yoneda atomMarking).obj x))) (Atom.closureIncl _ _).op
            ((ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩)).symm))
  · exact Or.inl (isDegenerate_app _ ⟨_, p, ⟨_⟩, hp, hi, congrArg ULift.up hpc⟩)

private theorem markedCylinderSiteForgetIso_hom_app_app_mem (x : MarkedSite atomMarking)
    (V : Atom) (c : V ⟶ grayCylinder.obj x.obj)
    (hc : ULift.up c ∈
      (ballMarking.{u} _ (cylinderMarked x) (pos_grade_of_mem_cylinderMarked x)).marked V) :
    (markedCylinderSiteForgetIso.{u}.hom.app x).app (op V) ⟨c⟩ ∈
      (cylinderMarking ((MarkedPresheaf.yoneda atomMarking).obj x)).marked V := by
  rcases hc with hd | h1 | ⟨hx, htop⟩
  · exact Or.inl (isDegenerate_app _ hd)
  · exact markedCylinderSiteForgetIso_hom_app_app_mem_of_fst_eq_top x V c h1
  · rcases hw : ((cylAtomIso x.obj).inv (c V.top)).1 with ε | ⟨⟨⟩⟩
    · have hca := eq_comp_grayContraction_comp_grayEndpoint c ε hw
      have hcol : IsCollapseHom (c ≫ grayContraction.app x.obj) :=
        isCollapseHom_of_apply_eq_top _ htop
      by_cases hi : IsIso (c ≫ grayContraction.app x.obj)
      · have hm : (ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩ ∈
            ((MarkedPresheaf.yoneda atomMarking).obj x).marked x.obj :=
          (mem_marked_yoneda_obj_iff x _ _).2
            ⟨x.markable hx, Or.inl ⟨hx, inferInstanceAs (IsIso (𝟙 x.obj))⟩⟩
        refine Or.inr (Or.inr ⟨ε, x.obj, _, hm, asIso (c ≫ grayContraction.app x.obj),
          (markedCylinderSiteForgetIso_hom_app_app x V c).trans ?_⟩)
        exact (congrArg (fun t : V ⟶ grayCylinder.obj x.obj =>
          (grayCylinderFunctor.obj _).map t.op ((grayCylinderUnit _).app (op x.obj)
            ((ballIsoForgetYoneda x).hom.app (op x.obj) ⟨𝟙 x.obj⟩))) hca).trans
          (Functor.map_comp_apply _ _ _ _)
      · exact Or.inl (isDegenerate_app _ ⟨_, _, ⟨(grayEndpoint ε).app x.obj⟩, hcol, hi,
          congrArg ULift.up hca.symm⟩)
    · exact markedCylinderSiteForgetIso_hom_app_app_mem_of_fst_eq_top x V c (by rw [hw]; rfl)

private noncomputable def markedCylinderSiteToModel :
    markedCylinderSite.{u} ⟶ MarkedPresheaf.yoneda atomMarking ⋙ markedCylinderModel where
  app x := MarkedPresheaf.homMk (markedCylinderSiteForgetIso.hom.app x) fun V c hc =>
    (MarkedPresheaf.mem_marked_ofMarking _ _ V _).2 (markedCylinderSiteForgetIso_hom_app_app_mem
      x V c.down ((MarkedPresheaf.mem_marked_ofMarking _ _ V _).1 hc))
  naturality _ _ g := MarkedPresheaf.hom_ext (markedCylinderSiteForgetIso.hom.naturality g)

private noncomputable def markedCylinderToModel : markedCylinder.{u} ⟶ markedCylinderModel :=
  (MarkedPresheaf.extend markedCylinderSite).descOfIsLeftKanExtension
    (MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).inv _ markedCylinderSiteToModel

private theorem whiskerRight_markedCylinderToModel_forget :
    Functor.whiskerRight markedCylinderToModel.{u} MarkedPresheaf.forget =
      markedCylinderForgetIso.hom := by
  refine MarkedPresheaf.hom_ext_of_preservesColimits (NatTrans.ext (funext fun x => ?_))
  have h := NatTrans.congr_app
    ((MarkedPresheaf.extend markedCylinderSite).descOfIsLeftKanExtension_fac
      (MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).inv _ markedCylinderSiteToModel) x
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, ← Iso.app_inv, Iso.inv_comp_eq] at h
  change MarkedPresheaf.forget.map (markedCylinderToModel.app
    ((MarkedPresheaf.yoneda atomMarking).obj x)) =
      markedCylinderForgetIso.hom.app ((MarkedPresheaf.yoneda atomMarking).obj x)
  rw [markedCylinderForgetIso_hom_app_yoneda_obj]
  exact (congrArg MarkedPresheaf.forget.map h).trans (MarkedPresheaf.forget.map_comp _ _)

private theorem markedCylinderForgetIso_hom_app_app_mem (Y : MarkedDiagSet.{u}) (V : Atom)
    (c : (markedCylinder.obj Y).underlying.obj (op V)) (hc : c ∈ (markedCylinder.obj Y).marked V) :
    (markedCylinderForgetIso.hom.app Y).app (op V) c ∈ (cylinderMarking Y).marked V := by
  have h := (MarkedPresheaf.mem_marked_ofMarking _ _ V _).1
    (MarkedPresheaf.map_mem_marked (markedCylinderToModel.app Y) hc)
  have e : (MarkedPresheaf.forget.map (markedCylinderToModel.app Y)).app (op V) c =
      (markedCylinderForgetIso.hom.app Y).app (op V) c :=
    ConcreteCategory.congr_hom (NatTrans.congr_app
      (NatTrans.congr_app whiskerRight_markedCylinderToModel_forget Y) (op V)) c
  exact e ▸ h

private theorem markedCylinderForgetIso_hom_app_app_inv (x : MarkedSite atomMarking) (V : Atom)
    (c : V ⟶ grayCylinder.obj x.obj) :
    (markedCylinderForgetIso.hom.app ((MarkedPresheaf.yoneda atomMarking).obj x)).app (op V)
        ((MarkedPresheaf.forget.map
          ((MarkedPresheaf.yonedaCompExtendIso markedCylinderSite.{u}).inv.app x)).app (op V) ⟨c⟩) =
      (markedCylinderSiteForgetIso.hom.app x).app (op V) ⟨c⟩ := by
  have h : MarkedPresheaf.forget.map
      ((MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).inv.app x) ≫
        markedCylinderForgetIso.hom.app ((MarkedPresheaf.yoneda atomMarking).obj x) =
      markedCylinderSiteForgetIso.hom.app x := by
    rw [markedCylinderForgetIso_hom_app_yoneda_obj, ← Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h (op V)) ⟨c⟩

private noncomputable def yonedaToFlat (X : DiagSet.{u}) (U : Atom) (x : X.obj (op U)) :
    (MarkedPresheaf.yoneda atomMarking).obj ((MarkedSite.unmarked atomMarking).obj U) ⟶
      (MarkedPresheaf.flat atomMarking).obj X :=
  MarkedPresheaf.homMk (Y := (MarkedPresheaf.flat atomMarking).obj X)
    { app V := ↾fun g => X.map g.down.1.op x
      naturality _ _ f := by
        ext ⟨g⟩
        exact Functor.map_comp_apply X g.1.op f x }
    fun V g hg => by
      obtain ⟨-, ⟨h, -⟩ | ⟨W, p, q, hp, hpq⟩⟩ := (mem_marked_yoneda_obj_iff _ V g).1 hg
      · exact absurd h Bool.false_ne_true
      · exact (MarkedDiagSet.mem_marked_flat_iff_isDegenerate X V _).2
          ⟨W, p, X.map q.op x, hp.1, hp.2, (Functor.map_comp_apply X q.op p.op x).symm.trans
            (congrArg (fun t : V ⟶ U => X.map t.op x) hpq)⟩

theorem mem_marked_markedCylinder_obj_flat (X : DiagSet.{u}) (V : Atom)
    (c : (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).underlying.obj (op V)) :
    c ∈ (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).marked V ↔
      IsDegenerate _ c ∨ ∃ (U : Atom) (x : X.obj (op U)) (e : V ≅ grayCylinder.obj U),
        (markedCylinderForgetIso.hom.app ((MarkedPresheaf.flat atomMarking).obj X)).app (op V) c =
          (grayCylinderFunctor.obj X).map e.hom.op ((grayCylinderUnit X).app (op U) x) := by
  have hinv : ∀ {W : Atom}
      (d : (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).underlying.obj (op W)),
      (markedCylinderForgetIso.inv.app ((MarkedPresheaf.flat atomMarking).obj X)).app (op W)
        ((markedCylinderForgetIso.hom.app ((MarkedPresheaf.flat atomMarking).obj X)).app
          (op W) d) = d := fun d =>
    Iso.hom_inv_id_app_apply
      (markedCylinderForgetIso.app ((MarkedPresheaf.flat atomMarking).obj X)) _ d
  constructor
  · intro hc
    have hdeg : IsDegenerate _ ((markedCylinderForgetIso.hom.app
        ((MarkedPresheaf.flat atomMarking).obj X)).app (op V) c) → IsDegenerate _ c := fun h =>
      hinv c ▸ isDegenerate_app _ h
    rcases markedCylinderForgetIso_hom_app_app_mem _ V c hc with hd | hu | ⟨ε, U, m, hm, e, he⟩
    · exact Or.inl (hdeg hd)
    · exact Or.inr hu
    · refine Or.inl (hdeg ?_)
      rw [he]
      exact (isDegenerate_map_iso_iff e _).2 (isDegenerate_app _
        ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate X U m).1 hm))
  · rintro (hd | ⟨U, x, e, he⟩)
    · exact MarkedDiagSet.mem_marked_of_isDegenerate _ hd
    · let u := (MarkedSite.unmarked atomMarking).obj U
      let w₀ := (MarkedPresheaf.forget.map
        ((MarkedPresheaf.yonedaCompExtendIso markedCylinderSite).inv.app u)).app
          (op (grayCylinder.obj U)) ⟨𝟙 (grayCylinder.obj U)⟩
      have hw₀ : w₀ ∈ (markedCylinder.obj ((MarkedPresheaf.yoneda atomMarking).obj u)).marked
          (grayCylinder.obj U) :=
        MarkedPresheaf.map_mem_marked _ ((MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2
          (Or.inr (Or.inl (by
            change ((cylAtomIso U).inv (grayCylinder.obj U).top).1 = ⊤
            rw [symm_cylAtomIso_top]))))
      let c' := (MarkedPresheaf.forget.map (markedCylinder.map (yonedaToFlat X U x))).app _ w₀
      have hc' : c' ∈ (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).marked
          (grayCylinder.obj U) :=
        MarkedPresheaf.map_mem_marked _ hw₀
      have himg : (markedCylinderForgetIso.hom.app ((MarkedPresheaf.flat atomMarking).obj X)).app
          (op (grayCylinder.obj U)) c' = (grayCylinderUnit X).app (op U) x := by
        refine (ConcreteCategory.congr_hom (NatTrans.congr_app
          (markedCylinderForgetIso.hom.naturality (yonedaToFlat X U x)) _) w₀).trans ?_
        exact (congrArg ((grayCylinderFunctor.map (MarkedPresheaf.forget.map
          (yonedaToFlat X U x))).app _) ((markedCylinderForgetIso_hom_app_app_inv u _ (𝟙 _)).trans
            ((markedCylinderSiteForgetIso_hom_app_app u _ (𝟙 _)).trans
              (Functor.map_id_apply _ _ _)))).trans
          ((grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _).trans
            (congrArg _ (Functor.map_id_apply X _ x)))
      have hc : c = (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).underlying.map
          e.hom.op c' := by
        refine (hinv c).symm.trans (Eq.trans ?_ (hinv _))
        refine congrArg _ (he.trans ?_)
        rw [← himg]
        exact (NatTrans.naturality_apply (markedCylinderForgetIso.hom.app
          ((MarkedPresheaf.flat atomMarking).obj X)) e.hom.op c').symm
      rw [hc]
      exact ((markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj X)).transport e c').1 hc'

noncomputable def markedCylinderUnitCell (Y : MarkedDiagSet.{u}) {U : Atom}
    (y : Y.underlying.obj (op U)) :
    (markedCylinder.obj Y).underlying.obj (op (grayCylinder.obj U)) :=
  (markedCylinderForgetIso.inv.app Y).app _ ((grayCylinderUnit _).app (op U) y)

theorem markedCylinderForgetIso_hom_app_unitCell (Y : MarkedDiagSet.{u}) {U : Atom}
    (y : Y.underlying.obj (op U)) :
    (markedCylinderForgetIso.hom.app Y).app _ (markedCylinderUnitCell Y y) =
      (grayCylinderUnit _).app (op U) y :=
  Iso.inv_hom_id_app_apply (markedCylinderForgetIso.app Y) _ _

theorem forget_map_markedCylinder_map_unitCell {Y Y' : MarkedDiagSet.{u}} (f : Y ⟶ Y') {U : Atom}
    (y : Y.underlying.obj (op U)) :
    (MarkedPresheaf.forget.map (markedCylinder.map f)).app _ (markedCylinderUnitCell Y y) =
      markedCylinderUnitCell Y' ((MarkedPresheaf.forget.map f).app (op U) y) := by
  have e := ConcreteCategory.congr_hom (NatTrans.congr_app
    (markedCylinderForgetIso.hom.naturality f) (op (grayCylinder.obj U)))
    (markedCylinderUnitCell Y y)
  have key : (markedCylinderForgetIso.hom.app Y').app _
      ((MarkedPresheaf.forget.map (markedCylinder.map f)).app _ (markedCylinderUnitCell Y y)) =
      (markedCylinderForgetIso.hom.app Y').app _
        (markedCylinderUnitCell Y' ((MarkedPresheaf.forget.map f).app (op U) y)) := by
    refine e.trans ?_
    refine Eq.trans ?_ (markedCylinderForgetIso_hom_app_unitCell Y' _).symm
    refine (congrArg ((grayCylinderFunctor.map (MarkedPresheaf.forget.map f)).app _)
      (markedCylinderForgetIso_hom_app_unitCell Y y)).trans ?_
    exact grayCylinderFunctor_map_app_grayCylinderUnit_app _ _ _
  exact (Iso.hom_inv_id_app_apply (markedCylinderForgetIso.app Y') _ _).symm.trans
    ((congrArg ((markedCylinderForgetIso.inv.app Y').app _) key).trans
      (Iso.hom_inv_id_app_apply (markedCylinderForgetIso.app Y') _ _))

theorem mem_marked_markedCylinderUnitCell (Y : MarkedDiagSet.{u}) {U : Atom}
    (y : Y.underlying.obj (op U)) :
    markedCylinderUnitCell Y y ∈ (markedCylinder.obj Y).marked (grayCylinder.obj U) := by
  let φ : (MarkedPresheaf.flat atomMarking).obj Y.underlying ⟶ Y :=
    MarkedPresheaf.homMk (𝟙 Y.underlying) fun V x hx =>
      MarkedDiagSet.mem_marked_of_isDegenerate Y
        ((MarkedDiagSet.mem_marked_flat_iff_isDegenerate _ V x).1 hx)
  have hflat : markedCylinderUnitCell ((MarkedPresheaf.flat atomMarking).obj Y.underlying) y ∈
      (markedCylinder.obj ((MarkedPresheaf.flat atomMarking).obj Y.underlying)).marked _ :=
    (mem_marked_markedCylinder_obj_flat _ _ _).2 (Or.inr ⟨U, y, Iso.refl _,
      (markedCylinderForgetIso_hom_app_unitCell _ _).trans
        (Functor.map_id_apply (grayCylinderFunctor.obj Y.underlying) _ _).symm⟩)
  have h := MarkedPresheaf.map_mem_marked (markedCylinder.map φ) hflat
  exact (forget_map_markedCylinder_map_unitCell φ y) ▸ h

theorem markedCylinderForgetIso_hom_app_endpoint (ε : Bool) (Y : MarkedDiagSet.{u}) {V : Atom}
    (m : Y.underlying.obj (op V)) :
    (markedCylinderForgetIso.hom.app Y).app (op V)
        ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app Y)).app (op V) m) =
      ((grayCylinderEndpoint ε).app Y.underlying).app (op V) m :=
  ConcreteCategory.congr_hom (NatTrans.congr_app
    (NatTrans.congr_app (whiskerRight_endpoint_forget_comp_markedCylinderForgetIso_hom ε) Y)
      (op V)) m

theorem mem_marked_markedCylinder_obj_cases (Y : MarkedDiagSet.{u}) {V : Atom}
    {c : (markedCylinder.obj Y).underlying.obj (op V)}
    (hc : c ∈ (markedCylinder.obj Y).marked V) :
    IsDegenerate _ c ∨
      (∃ (U : Atom) (y : Y.underlying.obj (op U)) (e : V ≅ grayCylinder.obj U),
        c = (markedCylinder.obj Y).underlying.map e.hom.op (markedCylinderUnitCell Y y)) ∨
      ∃ (ε : Bool) (U : Atom) (m : Y.underlying.obj (op U)), m ∈ Y.marked U ∧
        ∃ e : V ≅ U, c = (markedCylinder.obj Y).underlying.map e.hom.op
          ((MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app Y)).app (op U) m) := by
  have hinv : ∀ {W : Atom} (d : (markedCylinder.obj Y).underlying.obj (op W)),
      (markedCylinderForgetIso.inv.app Y).app (op W)
        ((markedCylinderForgetIso.hom.app Y).app (op W) d) = d :=
    fun d => Iso.hom_inv_id_app_apply (markedCylinderForgetIso.app Y) _ d
  have hnat : ∀ {W W' : Atom} (e : W ⟶ W') (d : (grayCylinderFunctor.obj Y.underlying).obj
      (op W')), (markedCylinderForgetIso.inv.app Y).app (op W)
        ((grayCylinderFunctor.obj Y.underlying).map e.op d) =
      (markedCylinder.obj Y).underlying.map e.op ((markedCylinderForgetIso.inv.app Y).app _ d) :=
    fun e d => NatTrans.naturality_apply (markedCylinderForgetIso.inv.app Y) e.op d
  rcases markedCylinderForgetIso_hom_app_app_mem Y V c hc with hd | ⟨U, y, e, he⟩ |
    ⟨ε, U, m, hm, e, he⟩
  · exact Or.inl (hinv c ▸ isDegenerate_app _ hd)
  · refine Or.inr (Or.inl ⟨U, y, e, ?_⟩)
    rw [← hinv c, he]
    exact hnat e.hom _
  · refine Or.inr (Or.inr ⟨ε, U, m, hm, e, ?_⟩)
    rw [← hinv c, he]
    refine (hnat e.hom _).trans (congrArg _ ?_)
    exact (congrArg ((markedCylinderForgetIso.inv.app Y).app _)
      (markedCylinderForgetIso_hom_app_endpoint ε Y m)).symm.trans (hinv _)

def markedBall (U : Atom) (M : Set U.ogp) (hM : ∀ z ∈ M, 0 < grade ℕ z) :
    MarkedDiagSet.{u} :=
  MarkedPresheaf.ofMarking (ball U) (ballMarking U M hM)

def cylinderBallMarking (U : Atom) (M : Set U.ogp) : Set (grayCylinder.obj U).ogp :=
  {z | ((cylAtomIso U).inv z).1 = ⊤ ∨ ((cylAtomIso U).inv z).2 ∈ M}

theorem pos_grade_of_mem_cylinderBallMarking (U : Atom) {M : Set U.ogp}
    (hM : ∀ z ∈ M, 0 < grade ℕ z) :
    ∀ z ∈ cylinderBallMarking U M, 0 < grade ℕ z := by
  intro z hz
  rw [grade_grayCylinder_obj]
  rcases hz with h | h
  · rw [h, grade_top_globe]
    omega
  · have := hM _ h
    omega

noncomputable def markedCylinderBallForgetIso (U : Atom) (M : Set U.ogp)
    (hM : ∀ z ∈ M, 0 < grade ℕ z) :
    (markedCylinder.obj (markedBall.{u} U M hM)).underlying ≅ ball (grayCylinder.obj U) :=
  markedCylinderForgetIso.app (markedBall U M hM) ≪≫ grayCylinderFunctorYonedaIso.app U

variable {U : Atom} {M : Set U.ogp} {hM : ∀ z ∈ M, 0 < grade ℕ z}

theorem markedCylinderBallForgetIso_unitCell {V : Atom} (y : V ⟶ U) :
    (markedCylinderBallForgetIso U M hM).hom.app _
        (markedCylinderUnitCell (markedBall.{u} U M hM) ⟨y⟩) = ⟨grayCylinder.map y⟩ := by
  refine (congrArg ((grayCylinderFunctorBallIso U).hom.app _)
    (markedCylinderForgetIso_hom_app_unitCell (markedBall U M hM) ⟨y⟩)).trans ?_
  exact ConcreteCategory.congr_hom (NatTrans.congr_app
    (grayCylinderUnit_comp_grayCylinderFunctorBallIso_hom U) (op V)) ⟨y⟩

theorem markedCylinderBallForgetIso_endpoint (ε : Bool) {V : Atom} (m : V ⟶ U) :
    (markedCylinderBallForgetIso U M hM).hom.app _
        ((MarkedPresheaf.forget.map
          ((markedExactCylinder.endpoint ε).app (markedBall.{u} U M hM))).app (op V) ⟨m⟩) =
      ⟨m ≫ (grayEndpoint ε).app U⟩ := by
  refine (congrArg ((grayCylinderFunctorYonedaIso.hom.app U).app _)
    (markedCylinderForgetIso_hom_app_endpoint ε (markedBall U M hM) ⟨m⟩)).trans ?_
  exact ConcreteCategory.congr_hom (NatTrans.congr_app (grayCylinderEndpoint_app_ball ε U)
    (op V)) ⟨m⟩

theorem markedCylinderBallForgetIso_map_unitCell {V U' : Atom} (e : V ⟶ grayCylinder.obj U')
    (y : U' ⟶ U) :
    (markedCylinderBallForgetIso U M hM).hom.app (op V)
        ((markedCylinder.obj (markedBall.{u} U M hM)).underlying.map e.op
          (markedCylinderUnitCell (markedBall U M hM) ⟨y⟩)) =
      ⟨e ≫ grayCylinder.map y⟩ :=
  (NatTrans.naturality_apply (markedCylinderBallForgetIso U M hM).hom e.op _).trans
    (congrArg ((ball (grayCylinder.obj U)).map e.op) (markedCylinderBallForgetIso_unitCell y))

theorem markedCylinderBallForgetIso_map_endpoint (ε : Bool) {V U' : Atom} (e : V ⟶ U')
    (m : U' ⟶ U) :
    (markedCylinderBallForgetIso U M hM).hom.app (op V)
        ((markedCylinder.obj (markedBall.{u} U M hM)).underlying.map e.op
          ((MarkedPresheaf.forget.map
            ((markedExactCylinder.endpoint ε).app (markedBall U M hM))).app (op U') ⟨m⟩)) =
      ⟨e ≫ m ≫ (grayEndpoint ε).app U⟩ :=
  (NatTrans.naturality_apply (markedCylinderBallForgetIso U M hM).hom e.op _).trans
    (congrArg ((ball (grayCylinder.obj U)).map e.op) (markedCylinderBallForgetIso_endpoint ε m))

theorem mem_marked_markedCylinder_markedBall_iff {V : Atom}
    (c : (markedCylinder.obj (markedBall.{u} U M hM)).underlying.obj (op V)) :
    c ∈ (markedCylinder.obj (markedBall U M hM)).marked V ↔
      (markedCylinderBallForgetIso U M hM).hom.app _ c ∈
        (ballMarking (grayCylinder.obj U) (cylinderBallMarking U M)
          (pos_grade_of_mem_cylinderBallMarking U hM)).marked V := by
  have hinv' : ∀ {W : Atom} (d : (markedCylinder.obj (markedBall U M hM)).underlying.obj (op W)),
      (markedCylinderBallForgetIso U M hM).inv.app _
        ((markedCylinderBallForgetIso U M hM).hom.app _ d) = d :=
    fun d => Iso.hom_inv_id_app_apply (markedCylinderBallForgetIso U M hM) _ d
  have hhom : ∀ {W : Atom} (d : (ball (grayCylinder.obj U)).obj (op W)),
      (markedCylinderBallForgetIso U M hM).hom.app _
        ((markedCylinderBallForgetIso U M hM).inv.app _ d) = d :=
    fun d => Iso.inv_hom_id_app_apply (markedCylinderBallForgetIso U M hM) _ d
  obtain ⟨d₀, rfl⟩ : ∃ d₀ : V ⟶ grayCylinder.obj U,
      (markedCylinderBallForgetIso U M hM).inv.app _ ⟨d₀⟩ = c :=
    ⟨((markedCylinderBallForgetIso U M hM).hom.app _ c).down, hinv' c⟩
  rw [hhom ⟨d₀⟩]
  have hunit : ∀ {U' : Atom} (p : V ⟶ grayCylinder.obj U') (y : U' ⟶ U), IsIso p →
      p ≫ grayCylinder.map y = d₀ →
        (markedCylinderBallForgetIso U M hM).inv.app _ ⟨d₀⟩ ∈
          (markedCylinder.obj (markedBall U M hM)).marked V := by
    intro U' p y hp hpc
    rw [← hpc, ← markedCylinderBallForgetIso_map_unitCell p y, hinv']
    exact ((markedCylinder.obj _).transport (asIso p) _).1 (mem_marked_markedCylinderUnitCell _ _)
  have hright : ((cylAtomIso U).inv (d₀ V.top)).1 = ⊤ →
      (markedCylinderBallForgetIso U M hM).inv.app _ ⟨d₀⟩ ∈
        (markedCylinder.obj (markedBall U M hM)).marked V := by
    intro h1
    obtain ⟨p, hp, hpc⟩ := exists_isCollapseHom_comp_grayCylinder_map_closureIncl d₀ h1
    by_cases hi : IsIso p
    · exact hunit p _ hi hpc
    · exact MarkedDiagSet.mem_marked_of_isDegenerate _
        (isDegenerate_app (markedCylinderBallForgetIso U M hM).inv
          ⟨_, p, ⟨_⟩, hp, hi, congrArg ULift.up hpc⟩)
  constructor
  · intro hc
    rcases mem_marked_markedCylinder_obj_cases _ hc with hd | ⟨U', ⟨y⟩, e, he⟩ |
      ⟨ε, U', ⟨m⟩, hm, e, he⟩
    · exact Or.inl (hhom ⟨d₀⟩ ▸ isDegenerate_app (markedCylinderBallForgetIso U M hM).hom hd)
    · have hd₀ := (hhom ⟨d₀⟩).symm.trans
        (congrArg ((markedCylinderBallForgetIso U M hM).hom.app _) he)
      rw [hd₀, markedCylinderBallForgetIso_map_unitCell e.hom y]
      refine Or.inr (Or.inl ?_)
      change ((cylAtomIso U).inv ((e.hom ≫ grayCylinder.map y) V.top)).1 = ⊤
      have h₁ : (e.hom ≫ grayCylinder.map y) V.top =
          grayCylinder.map y (grayCylinder.obj U').top := by
        rw [ConcreteCategory.comp_apply, iso_hom_apply_top]
      rw [h₁, symm_grayCylinder_map_apply y (grayCylinder.obj U').top, symm_cylAtomIso_top]
    · have hd₀ := (hhom ⟨d₀⟩).symm.trans
        (congrArg ((markedCylinderBallForgetIso U M hM).hom.app _) he)
      rw [hd₀, markedCylinderBallForgetIso_map_endpoint ε e.hom m]
      rcases (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).1 hm with hmd | hmt
      · obtain ⟨W, p, ⟨q⟩, hp, hni, hpq⟩ := hmd
        refine Or.inl ⟨W, e.hom ≫ p, ⟨q ≫ (grayEndpoint ε).app U⟩,
          collapses.comp_mem _ _ (isCollapseHom_of_iso e) hp, fun h => hni ?_, ?_⟩
        · have : p = e.inv ≫ (e.hom ≫ p) := by simp
          rw [this]
          infer_instance
        · change ULift.up ((e.hom ≫ p) ≫ q ≫ (grayEndpoint ε).app U) =
            ULift.up (e.hom ≫ m ≫ (grayEndpoint ε).app U)
          have hpq' : p ≫ q = m := congrArg ULift.down hpq
          rw [← hpq']
          rfl
      · refine Or.inr (Or.inr ?_)
        have key : ∀ f : U' ⟶ U, f U'.top ∈ M →
            ((cylAtomIso U).inv ((e.hom ≫ f ≫ (grayEndpoint ε).app U) V.top)).2 ∈ M := by
          intro f hf
          have h₁ : (e.hom ≫ f ≫ (grayEndpoint ε).app U) V.top =
              (grayEndpoint ε).app U (f U'.top) := by
            rw [ConcreteCategory.comp_apply, iso_hom_apply_top]
            rfl
          rw [h₁, symm_grayEndpoint_apply]
          exact hf
        exact key m hmt
  · intro hc
    rcases hc with hd | h1 | h2
    · exact MarkedDiagSet.mem_marked_of_isDegenerate _
        (isDegenerate_app (markedCylinderBallForgetIso U M hM).inv hd)
    · exact hright h1
    · rcases hw : ((cylAtomIso U).inv (d₀ V.top)).1 with ε | ⟨⟨⟩⟩
      · have hca := eq_comp_grayContraction_comp_grayEndpoint d₀ ε hw
        have hd : ULift.up (d₀ ≫ grayContraction.app U) ∈ (markedBall U M hM).marked V :=
          (MarkedPresheaf.mem_marked_ofMarking _ _ _ _).2 (Or.inr h2)
        have hc : (markedCylinderBallForgetIso U M hM).inv.app _ ⟨d₀⟩ =
            (MarkedPresheaf.forget.map ((markedExactCylinder.endpoint ε).app
              (markedBall U M hM))).app (op V) ⟨d₀ ≫ grayContraction.app U⟩ :=
          (congrArg ((markedCylinderBallForgetIso U M hM).inv.app _)
            ((congrArg ULift.up hca).trans (markedCylinderBallForgetIso_endpoint ε _).symm)).trans
              (hinv' _)
        rw [hc]
        exact MarkedPresheaf.map_mem_marked _ hd
      · exact hright (by rw [hw]; rfl)

end Atoms.Diagrammatic
